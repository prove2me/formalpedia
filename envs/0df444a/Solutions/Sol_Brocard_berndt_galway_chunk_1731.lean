-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1731
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:27:52.520411+00:00
-- url     : https://prove2.me/submissions/9e4ea1c7-548d-4294-8f6e-6aef6d770cc6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 311151079 ≤ n < 311330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 311152329 1250 311151079 311151101
    0x42d061a0a050703120e0d0f03182315012903160e01091206020a030b09040f02091e130203210712030b15090406061d21120309010e01 59
    0x545000c2c40b1340d03000e40d420580340507060340041d80c0d004039180c045000c0000d900b00d4001500c0b03510b100c0108000040540d0b08203000030300101e582c540c0000025034540c240c21032480d201140c026803034890711a1549401d44080ba00403100c815140001a100e5641e100030740348041d0060607070951945c41c4401c044600c01500c5403148017051462440c1da6030b102d205c009a62103014500b020405654004030001413441c0c000549581c0d5000400d840120341501c15048581c00c140c542c1c048518040d01c540c4100c003540030010b40901c108100007540040e80c6103c0c00005103200b0345c41c040e1814090341100c400a00100300b24041d10030240c0c8202c0340c00f0075200050910708503072061868220683d40e18087c821026140b4020b05485210040a0382d4170002031f00e62150003404200d840d1841f001c10401036070407551146c024010051244072541d14513866000b070700f08051703404080443c10420021500d10038441416154020709500c1154242c180004501402d040c44c001d1001d8200500703010b01301d88001242d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 311153579 1250 311152329 311152337
    0x14060a14040f03050d09081c0b1003020a03090803010e09280201051309110d0c08060105030c13030204020d02070c0f080303010522050a09020306071409042d061a0a 72
    0x40018442ca8010300206100e0700d003440c14204050320785020b681a5180447d824000464102500794024980708054900d40400384040300204001c20400d510a40c8244105a0001402c1d81014060b0b008100c800307501150003030fa2982c0d140540d1004600c00d0b10b40420700d0141c01c18895040403000310100442c03000036010310140080e6401950940e010f0a102500b403000c40d180040e80c2c282510445907001c0c0c0e0230295a07552030b00e076490781d02101c0d6090306110520007280c0600065036070040035603a0041e191801e403540ca00d4500b1610102c0030050740020344c043d00000310200c03058080d4018040d0319100e0945030503041c0d02d61071585c0b05603203d0b0260030401e071b105200402c41c5280180340681d540e4280181250409800381996003a50812030b1401c1080d52110102d20841c00c1c104070141c0e10031054902050b00541c0b131a1050614441c50061901c10b54070782d540100b48c00002081e1100f900c20410050651036422014a0040c0211f4440e0f0b07020000c030038103d1040c501e002011105000c90319030b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 311154829 1250 311153579 311153581
    0x1a04050f041a010c0312180203060a0203090c13020d05010b13080f250f03050307300518030106031b0501140304120e280b0a14031f0314060a14 63
    0x1101c13030002d01c2d28140e00304100520b034a01a10580d214200e034a8940351035403081c000b1103005051a140020f0b24411541c3d00c1082001a40480031584c40e9243c2021551070125000685003400a4001c4020038401035213010700000c1c0c034503400c60040c111015101c00008c000c954940d0210344a0810550000c41078120550380c050046070181d0400495000c03514286000361681c4a098003021281c004031580d034000501e6006100c0910036107a00c1d6040511400c482d85c926062001e0525120302c2d020003031003030100f00d900720300401e8044400c9044000d0020071160703599082401c04040b21400801d8a0001064003003440c0d4456581d0b40003105080381c1076442c5803507582d030f003264040c0e08440d2203003000310000300d1207490369505103154544512045402d400d800240d0782d00c1d15646490f8802c0352a51410052104202d070040c0341c0c65001c10f4603c00458807503640b0f43d0b146000c107800020741129031b0140c6901000b04142c01d85040d10500c1d9510840741d80e50340302da07444811140c0b03680c1d1008107002800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 311156079 1250 311154829 311154881
    0xe07091805101d030d1e02160b060328020f0402090d0f020a031707050d0e13150504060807060906080415050403020a1502040e0f040803010e101a04050f04 68
    0x203040f0721180500c8416000105000120081c259003002c214400425120904101d04411400240700c01c051071030030861a000a4041a04205420034030080c40d582c6d8410014038584d40a001c2d59041c0186032400300802c10384080001120f0841040403842080d10a010102c90300f0688280c81880d0740c05040c040c240c131890707100c1409220202900303c0e8007121100380440000c0340384400080114001013104e0312040c031494154241008843c0e0402040041808846180d07107e0201d2000e440180e42c0c0064100d1040900c0c0740c508040d42c01c2160018202000060306903c001a02c4048661a99510b004540c03100c030100e501c81002c0da0091700454441d45040c103408031983c0101c2d000352290040300e40030051a681c241130000102a68a980c40d03000c1010031210318208251644640c040d5001c18a5103096901d542842c00180900401400303500c0c0080c4041240500c00d00182c01c0102058609001442c0d0011343c2d5481380c0601400f07044040710b2070700d050405014840308000401000702ca904012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 311157329 1250 311156079 311156081
    0xa2004060509011b050a06020a120902030709020a0905040c0f0909050c0901110c090709050301141b03130f05010219110a030e060702060c0607230307031508010e0709180510 76
    0x1110300e40c1d2038003e6040444000403800c1001c40e01c0c2d148078002c0583c0b9002524400b501082b8541c50300f504c1d40b4107103004100160340100e03401058580c1d040b001130702c0f91074180044501031440e07000150003a283c9108003e186800c1510300d00b0440d541e51311506d0040d00d5840c1482a03840035121aa1010700611074032140b507000b00107103214069100704440000c0d081d031000400280d4207650040c0424080c10060100381000c1c0108501c01d0f00c209a6030302a0f003050700030704821112100061015400100201d644000051503a0180382d800600c3c0c405c000c225410068000c0d030110104031140303095080072411883c000c2e5803a0783c24501c9a00a4541c102482e2400d8400c11042002c02da07100c801006242c0041c0d0702c0300080d0089042c1d5000400b424502014041c2500b54030a4065058840741a40314580d032440c00100c1e0390241e001c0c075010681c07404200c07510b143c0b00c80c1030700030851950901c040c2180729500043c0c9030f01240c00d440303418022200c8212616003443c0400c02c01a050390427007a56a4004092 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 311158579 1250 311157329 311157347
    0x30c06130608061201020a0e03010e15040204020912120c06130b2e0303050903190c151209080a08011509140616050a06110f0a0e040b04050a200406050901 68
    0x141c007400c08030728448515402c80c3d1020700c40c1c0c00070550044540588d070030b0901c208003541e40d0348d0004106c6840d2030a0509403002c1d00034402481650001100c510a403a071410515402c0070200c2101c0f00c007040740750b40c11556003215108a40601c600300025416582c0145803030390164009001d02c00e6601d600e1240492900e0150300c0032042c0e00d00840c0b42c1038980380182068020740c02941c0306915840044201420b0540c0c1d0603a2217640c0700f0341c144000c0812188000741c412901095500d482030011000103980c01406030b064210329a107800004414010030390002c082c1070400d503841c0c803003903038960306071407000520400c164000601c400024440f10943c941d01091768200140803d052941800176008600b14801d0115200e404c644074100c03c10406e4054041c95101000c51682010b0340305244800500555504108000b66811009460784480c1e000302002000500300f800603140100602010b400310318102440601044040d50f60881441d058605850b019521280340646c4a030045400c119 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 311159829 1250 311158579 311158591
    0x8151e040f0902190e0c040e01060c03030e03070804080f01050708220503190807020d0e090a0f0f0e070605070503070f021c05010c031d070501050d0b0402070b0105030c06130608 78
    0x540c2e40144409a5510301444024400600c00114458207081062111101c0946180000c02081c4002c0c08401411003502e419070707130a440d1495007401c29040803000303820001842e10490000003200001d00005100070400c0d00d4419048450303101c04104003908a841c11111100001c40c44d20100b10741c0c95005510601100030f50458607030b2450355459590850b03211010540580000641d1542c0e559081a28142e01c905e941c0068038a000341048060840602e8a4441c0d200e403c002c03000030031080d200d62040070500e060070020031102c07a8100500008219580c00c40490344641000007030b00503c585c04886499074403078040c0d428140e656440d254400070b03001c000ca0f030002c0c2c0e01124100c0440c4a80d07003a01414041c400200781201641000f8086500c00200d040388070030883c040031000100011000c086035400c0c40c1407980c589940300100300030f201340d0444030fa00a00008500040c4902425580e0588400320140d95489003003408100c80c030310940103009030308554030108110703543c0115882a0320034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 311161079 1250 311159829 311159831
    0x402010e031e030c01060806010b0f0a090b03040f060609090c1203050702100302070c05100225090c09050f010503040203150603010906050103120e03070f0504020c0312010608151e040f 81
    0x40b484081181c00380041282e040c182c0c00895040c0d10704109014400041c01858050001541003801441c3e05100303d8001569850f000103406808520400c0302c54001c0080300140c541328201031625808000a0700c1d03003601c01700e052030004212441c0c00d00c00e00001c60360240c2070546451500c1d440b8561141e07805001c0d130900c2004d0000d900542c5038a821076800000c1542d0041e40e81c4914a0900d00c406040d411180c01890005169174040340c001a5104d99284901079803580c07140740c10102400d502c02a0070425a081c02c0c12200388085401111800984800311a54001c41100c81f004503594002180d02940c95405178115001e400d12003004182c01c0721010307001040c0c3d900c16858890541d0000e03070084400c11801c1c110ba1041c550300107030440c11b80314101c02601d82c0d1840c1080d40c8108005500034244602e0707000400742c0004c2010004c41d1150b040c0784130309929a6949840107031420070222503d10711014002c0c9031041600c3c0001c60f0003075681c15128040821074401c0c0a010003018070310222020310f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 311162329 1250 311161079 311161093
    0x304151103090402071a161d031f020c070803031b03040503040306051003030f0e030309012105040c050111070b0403060f15090203060f0102010e0607050f040e0c070210170402010e03 80
    0x79407200d0006040301c6000d2101c2c0b10928620311000c3e00310300f0006244100303007147c280480d00c4980d03120400310500c0c9030301d6000c40c030402c004100080c00c114418054403603107100300c00300700c40790042034000c0c1820742900000d41d0400c03684c1d21011a202d2200715401c042c1c900c409101d60560052000c081d54006008100700c1e41040e840360f0710001111810740301c2c1c078480c1000020400c00c169200340d0541600781070b8500540039044c1c400c0400c0e524003c41001f241803051300ca4800d4454104002042d10031000102d0501290819081c903521120711802801e000070b02543c1262548880000e00404a41c4075140b454a0585152208801460b07000d0685003003688550740b81c99140c4202d8528009444220401640c0b41029410888021601d01480f81564108680c600703200c1400320b500c41c1e02c44402d040ca0b40c3e81d0400246a10f425214581141c0201a0f44106101c00f0103a51805040450b00c280c0e190030301107400ca00141c8081542d40441d0045021150000340154490b41101c082c01601074100c03158 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 311163579 1250 311162329 311162347
    0x4020a0317121015020c0d11040e030d15060504030c030b0a02070f0c091a0a0e0705090a0e150603040510090512041202090105040510031b150203090901080304151103 73
    0x8501015603030b010308981d0f288400e100560000f1054004418070b40002c1c0099960a4046000340550a00241c080c51180d08400000d0700c96400c0a240c1c0c0d074100081c0c0759118825480780300140b901c807044901c1e048103036002149480c0210211000c1c0c030742005038040341030710759503600d10052801031801d036485809010400000304122070003101e20340f2074a1804800d41c01d06900c0802c441d0800b5940e00303c90500040000c10351640701410090302d8403150707121510b0b41d075010113841c18440d5051603170b000603204100061300c0d0046007480d40254010a1394546d095004010815a80400d541c0900300e074005203d41c000541c1681d104807141485481951107040301e200ca03010711608039030f0020710b032403000c2c250810461400a15203030240c001114200458101441c1024502d112804020101580320250a0701e0440001c0030000034040d0300d4042c0d582c4100100025101c0c1c00a00c2d24900680a0740000301d42000040140e906513511250154041c0343c0340e400403291b1810401a0003040e000400500b00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 311164829 1250 311163579 311163607
    0x7020a08030a0f0c1d0d05030412150f0504200f040203011401030e0d020616030e070b1b0c100f03020c06090304180b0f220906050a0f0504020a0317 65
    0x302c01c00b15400c000801d01c84903c40981070f19804903903038081124421081e1080c0c0206036840c5040f460568085410f1000e44c5085882c5200310780044201000c82080701040024260740c0ba5141d403490101800750700250910384041d0380342903c00414504024010050402c0c03c0805011142001001110700001a4011504030383c000c1c0c101021020480611090658150007021070180714140104030704049180e0084d100c1c4005000601c03101000c0b2000c203a1148241c101e0850040c07280300b40d0b40519600c0b10409280e5005410809072215400712603101c810b0080b50728440c1d0783c00608054140302016400700d4801c4400341d0079606061b42849140900c0004214041c85955180d004640d540d05245412405184003800d58404030b081003004070103621080c9a0300c4481d00103484114171110340d10000195040321002c010082c40c604011007062140700c2e004240a200050001c1140302d01c0680c0e44400c1e0342c400c035001703500b04140400400c0010340a01500c16817041c1d00320040e08083d95080625 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 311166079 1250 311164829 311164831
    0x10e0f21030c0f03090d11011e02010b0112020304021e031009060b0307050901061d121506011b0c0b07050c0901120507090b0d0221100e1b010203070b07020a0803 71
    0x1609907480400c604012850802a0480c0244040c1c0154107260224002500302c8640030001010b00038105050020350340034031a0b050440c2528940c00180e0120741c00000c1c000c000c2c010000380058045000c01040100500c201d038001c5401405ca65641020702c1c0308060900000c80220790544205a03980904011074404c0302c1d00248260004518460044201071403c003140d0070891091000c000100000354000f15042c81122031020181501c06091700000d401d0900700c0b211286034010600720100039a560741c0c40500c00d900981715500c9001100c070341c4002e6000503000041001010f66070502c0003010314400342c54a2803151040342c8010510398003050703201c142a44003103038155070840f07001c0c20490203204803000707004804001c00c101c113400c60003d42c040e60311283c06030050300c40c8501d0300000585200100346d049000000c031182c0849000003c0300512110201c0d111a001c2c040c4000c7c1d20100f085400f803501d40c1d059008504140315520703801e26000001e41194298403e8682240c009000a0091 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 311167329 1250 311166079 311166139
    0xa06051012060501090c0302191805060406080a06090c0504090504111807141e130801021305011e02070605180a03030c0302100b01080721060f180209010e0f 69
    0xc00c40e13516152030801a2150107400391b00b85401032066501d009000d811441e0303500340f00d180440400500507901c1605003c3c0390071030781c0c00080c0094045049a04030100500600c42803a08000d800e40d1250f01c041124007048020b40025010482041880e50907040b403500700b4040c81088554100000000b1091244040c41c1c005a800c55001c000c0410b42000441244551500d03440b8901a503c8603002c213110143d9038194400c660200d11085058003000041c1e014101c240021035540e042c0d003a2030038040b40705114503070009030301d0a8101e0038150848240380c0e0b0b20f04160010300c081c074142001036905400142c03828030144c11058120314280e59941542c0b0065000f80c91b64040b0b009207040090802484603c00303401e6605140250f00540d038000000c907400a003a02c2c04007000070721108031034144405140340020307150800b40089170181c00c0e079200c641160340e10311488000f17800000300d40090b030040b03440143c00704081d040700c1c0a040c103112803840302c4100001c1030300403101d40c0c1c004215007140320b110607 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 311168579 1250 311167329 311167331
    0xf02040905040c14100f020a0c060206150109080304050d020312130e010b070302071806030501090803090f1915060305011a040c0302180d0615080a0c06080106020a0605101206 77
    0x380300501100240010140c26044910361444e50700350003040c14005040500020420600c045040e25842408030a603125404000d25a240341d4401c402591a2025148000c2d0074400c00c8124655602880d25003045800c0329020314180352905003017000d079815110050741c140c00b0b020000584070190a0081100d01000c64020b98241d0410400c1c030a90801601f02c41c0200104129810219030001803000c01c45951416000d030743c640d003900301000b810031588020259802c2811800802c6804000340d445030170940100c3d60000311301884d1560f40c0b007844801516420300ca910f0305011a80034014119003c401c000c01181300b95981e074880e421110b40c6100744c0502480070318100c0c610314041c0551541e8840f0341c0b4080d400d21240b649880c0310500800c3c0d1007031050151411100400c5001d801240e6a080b0f03403108038a6a40d515840c403a2140c00c07d2508496025118002055943c064400507041c0d80155006111030f0701159902801400d0241404035103c59101001462204191540a0052050340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 311169829 1250 311168579 311168581
    0x5030304060e061006021908090a03030203090414060d030807020102070b0903030a06050f01090e04111f0305010503150705031e010602010e10090b0402090a020405090717100312050d0f02040905 85
    0x8246007090301c09400c00f481c400e28180100540c560020ba6404039442d4407a254032803400fa131402c8c01c4c0324861200025008100c458000040c5600403000d04840401610103011041d52022400319070f0030f00711801940452000c00f180086031055803803a0b03203c0d44074000103142582907128040e504c00d044804080641c000020012880c00030301500e00101002d030780f48808051b030310b0000f07000002c440c0101d030b240041c3c0500240c203015140f40c445401080c06440098642050281401075144000c40303040803c1c1400c00026141c1000a0300550140d07244200403410b445107001200c840e0b0025018418002c0c400012099400d44980418000c0c9825000000e074003242c00e0816061a0170a04c002c282a031918956001050814a41603400350381165201500d540d910500c90090003190816508500d03904100b1042c1074000500d80c810710005006803009039200c1d0070000f017800660000030300b04246452000c01706806440a00380195100c00045030b20074078024103d04a0f04546e00481050f07803220 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 311171079 1250 311169829 311169851
    0x2160b0402030c0109031502090f0909060717010503100e0f0105071e0201021303060b01050c0102030c0403020405010b27040e030d020706060602031e03100513050a0c020102070201090515070503030406 88
    0x9803e0362200038201034082c145151140091020703100101c4a41d142c00240c0c40f40180d0701d421074154111001010344102d410140d003c9070762400300300c9140b80407401c1e9854a485520b203a199007412107000400400603109403002c2c4030083c0042c014504694442c0d86000c1000390340a005052007504607540d2040388200f840810001103040c0811141564410004028808001c0040c1025030b03410130404a80c900b01d81004982c40c0c402c0f00d0750321000394804400d11808440300703001401186d008540074442c03645c840c513401c003440c450b81081c01d424204004042c0121030b08941c1300001400001c000180149502c8485420b40c1d02000b1a1250694005081001c01c0350300e202c2e40d00a00103a10095003804141c01e83c2901103154130320440500c0f00c0c04000200700d07100454000c0090a00a0483d240481c40c0818107000b50000b0707111801102d00f03241c04043c8051052003603400036a01699140c542514000c240864603020803c00440603000b00021004210100000c600652288600040d55070145c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 311172329 1250 311171079 311171083
    0xd08120a0b0103020a0c33060617011d060a0902040824091522050f12030606121003050102070f05070806060d0602090f030106140f040213060c0602160b040203 70
    0x181d0160381c18035105020700480d40758080e0340c0010b100c1c1d1011060005460315550b50440f802508442100b0000d442101d4030f01c0707810b40d00301c101260f00648071481b60b080001c151a08d13042d42401410000c50516911280145a40052642000001d00051031054a801401d0141d9019400c044c0e80b03503005c8076501d5140039040703408520a208040610145050042c00e482c6c40e01c824604881d003520541d03001c699a240304c6181d42c540f41500881d5083c8109041c0fa05a403203030100301300900e07103029044a440402402c0b07400c40344610030040c80203103040c2c1c60715500104540301800c50404188046000b20000340d0034070041503c14051400c3c04d180d610a40b41c4640342c080990406002e0ba00803100788a0903480c0c0240c122801580204c015032120300841c01300d00c00d10100c6500550544c20880001044115030810311040d84c41903440d23801e10040f01d028007040e403088580131005115604010010700f13109a52252107144901c0c009844c0908c503070fa210f0320720710b09200c2c16140d080000d02803000714541 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 311173579 1250 311172329 311172341
    0x606080603060423010e0a110112050118110c0d030e060c0909071b0210090815060f040b0a03080d0203010f060f08010e1005031b09070912020f0d08120a 67
    0x850042c081c902e401c0c0d580c4402035100d0320007410150344290055113a06000e4006070300c0740c002c00f01250440d0b0041c6c141303081d07604010b4807283c1c00f040c0480300041500c1081c0c0074081c1600c0b400902420400f10003603c8100901100c80c00641e0701d00c05000452101d4810702000c54003441c0756401180c090030150009090220107085c5141f88078041000c1d510603119515000d40c09070107420300e52070b00d02d612611a09407004814000354000913018030003003d160401c08003000d8400760821106440c45104154a002005903045a03003c1c04840f004103603481c25400032020948041c2003034130300b81d0756036496103155044000404100c0380c0120040c0017561880e20b440300181101e260071350316152800c0000c0c00ca0f202c180503a2085a80000c001a1003015a1200d10014000581190420011800a50b124a0001c50014800c84805000ca201d01344a00c00c4e603000e072200340b00c112030120a1a42044040340d541007000390040c5200c0c09030408514804041d18000880180707840d00c030302d0914400c10844107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 311174829 1250 311173579 311173591
    0x161a0c1002031806090c040f14040b04260d0213080f070302041802090414030903100504060b0a050603150307240f090b04090504020303070804170c060f12100f09060608 74
    0x800f0130200b20400e040001c26804000066078000b4541d1035114448001d0f205400d081c02c6242811401d000c01c010300d910243d840780340036107039401207a01c146103941340682c1815a50040720b0300a224696813146035a00a000c400e03e0001d0944100d65108849800d15407001c5000034181c01040303041040d4141409204036171900000c0d082c0c101001075000550460000c0c00242855000c0e40000013104410011104014001401c60380464124407160010304000c503070454a10b8108142d00c40d61341005d04800b0b007990802000e0a08560b00c0030f40036104158140402985442840000506e0b0002e121904005400002c0400010f181142c000751001d04947c0851707040104020b403c000300b5440c641034400b42c8d911050081500d031101d00000c0e180d405080b03030142c0904800680018010f00c1c0c000396150b40c62081040da0140f000200070013280c2e00540d940010005020460b02e14500c10080c056540039012814040e4240d0316541d105104400541150320b403203940c0c6109101480d081540194000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 311176079 1250 311174829 311174833
    0x1170309060a0c06140a0b0a1d041401060e0f1f1a0c032101150807120b01120f0c140c07140a090c0f030e161a0c10020318 54
    0x44102004500503119401c00d0404002954600c001000041c0e00804500494417000c41038a00305150903000030300c0180006845000c204200241c0400d414040171806030700c01155510039911500d581c031800c0085840c5c05100c0d58ac882c03020031032040e42c040c4180902e032a9408103480789040700c0100c1110402c800100011090034070108106130b4680420492038032039440d51074460003811099451800307402c072015002c40051154107425041861142e048418111000c0210b072400801900c140405441c84400520b500b01824804130842e004036100c2d03c010301d40895400c544400e82d504649045002c61201600c6006c0c400003654000001c49988614400080c58481c901003da940e40040b0b01c900d00207880703642c14090142c0d481480c00070051a0030541440492400079005000d044a0b07002e40c00440d2801903a0646460b00048108100408086030f5070710034100280002462006003900003c40380c108114441700c0010f101c1302014200400d80981ca03401c1c5111885940b05140900c03901c03175 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 311177329 1250 311176079 311176087
    0x3050702130e101a0a0909020427020f01120f050601030501140102150702030f0d02090301060b0c1f11130e090303071713020402211b09190f080303011703 68
    0x2c04000b003034011503414203040c0010303507a494400015602d03822840c0795622800396100000c200076982c10411039981300311800c1000100c810303603000410850002c0070340311459007010706005051403801d04018050506020346446a4215407900361511401052202602d80c3c007441203a5805024072405051107143c010313100f03848200001d595400071703c441002290307101c01041040d8005d00440302241d401203034503940d0b0040c036102031000e98004020540290319000d000100c0030780d20b405551403401c0e010040c0c851038040940300340c85003902001d06102c84d42e590100050f80c0c2128001011000d00503406a4100392410100210845008100381c115401c1001040310455001c081c011790b003d8245034a0105071106124141c0300c2c0290040250018800503941103030080d05004910302c401c00d1a60004690303500000407150b1400e8200c5044a180c00b4421000c1c546064844200c0c00c00315004904495541c0782110000f9503820f82c0103040c5600b0020051042505200a40c51201140c030011850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 311178579 1250 311177329 311177351
    0x80d0507030e190c0510020303160801050a17070e0117070b090f010c1a1e0603010c080106232d0405010c0b06060706050a060504060801050402060306090415090305070213 75
    0x1a03541940f01456158042c01d190010005900d8150000c0c01c005004c40c854812181c0010303603640c1c001c0d98030401003402a1440703a5018403800c02c650503078034060f00424035286080c0303005401501c0c0b140c47e40745a0190900103d0001084444503001b061074004071180c2640032481241440d0103a041114142420460112652030740d2001c04201c0c01d00f880c0c091002011814004106588100e80c140c502030448248042e84003002c0d1201c005000b005004103003038403402c0815003200c9c4e8035010b4802248440f001004000d0090b04a510b011030100c0c1c0500f0400c80c0ca001c0c50210385d100341b01804c00d0b40c5281d85a804001c10b9001c1841c1c1a1070f40303070401f91405e810900060650350400c1070040505202500140300780e264441540e0100e90301070418001420029a800050012402030b1070041e4607000c0e0014400c10140078017401550050021b51071600c4102c1841121140140309071b410280030b10b545000000c0da1320036020b00347d00070707640c0985810507841008240d00b0388400300c3c009981041c0c14004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 311179829 1250 311178579 311178583
    0x3021f060b07020607030c0605040f031d011d0301180f030e1503010302060f0706020705061504200c0a0203071e0b091f1209140f0102030f04080a1b080d0507030e 71
    0x2402c039404440994888181d032600b00d0f40c2c40c0c07c80800404190500050000700445d517020b1083e060300c03035250107500c4941001512003130800309141e5400202c9004941e01030488d140010f003082c4c240640081600c107074081d224101e06203584400c5a18100003c2c4a5040c0342c1e00118071340c45400103c8a02d01a220007208070641c40c0010700001c5c0c45180d00107507004103d00138074100ea40b0203512120541d259040e43c00c0458894504480c1e10060001500c3c01c02d590b4542803042c8254000040b498a0006044202184603504042c03005051849910159000f69074100140d400400080c0e071954005003000049541526050348500c050403002d0140102581c1c03041c1316000c1088001c21049440d14501008076040d081c04007a1880c040c2c60508880180040ea91812100c0c1500c1402c84030003003080381d04217080344005c46c1d004216000c003101040000c0c80b0300c001001c110010740360400340c4c8018000c1822558651950803122113000142482c081e070715500559500032400e0400700410581691059 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 311181079 1250 311179829 311179837
    0x603030906040e0709030606080307020906120a03080c070b09062d0103020d1121060c0435030d05010311011722080a02012f04090207050f0a03021f060b 67
    0x8030f45501c100b400a00e285118003d004011500010288210356032040c3e5143c40354050a420707406401018006526810301116000180032000000c0c1143e40090b20125003411010342907105440c010045500425402400e4a000d289640094201802d00000c41f0070b00304070010480d0349880d6208018a4024929401581126010340d24954050b8144c5001c3c22a0b035190400c0d5a0b200c08110a401c10703d03034a0080c141c0c4100c14100484100f500c031210701050382e010750320810050040c001c0e9042109107086800e00000826003401c3c4c42820030390004076042d50441c581d01c83c0700c240d4400040060110359091000e185600b0300f800b1036070014990000310181c4000f0150346030342ca040c0c1c00300120105d00d40e00003840a03070031a41c4142c541c0c0060074000d010700901c040c500c0c4024551801e1501c8480340c14500407201022045040c6080d1400c084440690003040c401e48440c05a0450480c8050044c0081c4480380c0c441c2c0c3c05450001078508203803c002c0b0105080215140c03a0420030310140d003040c8221 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 311182329 1250 311181079 311181089
    0x10206010b0a020f0f0607022103010923010305210307080a0507020c150406080603030f03040f08040509100501120c12090503071e060c03111603030b060703050d05060303090604 78
    0x9940d42c01c44030026454500e000c83c3c0a405407249001e8004804030110342a40a010039038291498008944080d8144040e9110803c00c4c1030402c00040041010030b6000348840c00340010740c900c05800c0c0f1035040d0144c030004d9000b0342e83c1c0d800c640480320058651007403105146c400c4036000303411400c00c41401408031070300802c10304060b65101c3c003056015000f04025a40202e006000800300c08600c0454a0103411910038000401d2030b81000c1030203860b011040d034406d400ba803030030241150f80d40c0d140c5921602c0040340640d44110104030124281d215420b0f004e104912484c01e0110700d40c40d081c001020200c0120040e448a458205d501000643c40b001d100c91008418801003a02e51071814914107501c81c0c400010701c0e609580e0041084521078800020340b503070083d0010482070900500c01d4050b59066142280d900c03e00700510155403140441c101d00d0300e8000d28000403040c0c101000324040340e00105055011030b001185c150024000d60290706e9001d1404d4018505140300351010810b0b5000324014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 311183579 1250 311182329 311182349
    0x6180f02040915020403030e0301050c07031d270610050301080a0b0a0f0524010e01090e1e270f0d0f1e110c0103050705180d0506040507060f020c01020601 68
    0x2202080c0110000c041d43c8407101100308542d1541d5900d0f0180803400400e200340c0c025400d2800180d6049410026907049a80544848030b490845456181c825403400c010350390b1101d8800d04a2410403040962507490301d8111501803003e007841130400a100c21001041000c010041006105540d03012903001d1381e855204801465903104c5204040282104003480e9002074a00170420042952050032940680e005900741200525008011030f012030700c00c90001e01103030340c030101005500c0003002c00f950712280400000400190b0401800c01500003940e080305008503150401750891643c0c041c007540d508140380200b84850a500905803a04d050308550b00030303c0b4003600940041d60051146450030841c2ca02007180f81008014090b040204101e40001a4803800901020070350191140901600080d1202400c1880c42c51050502011004003507030815400111500000d90410440f80510310840103400c01c181402c000828500b04800e24104640c0898100d40090f40c0108101741940c3d82c01403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 311184829 1250 311183579 311183591
    0x2040303031529221508040b010608040302010b041e0b06031620060f01170607120b01020106030f08030a050603030f0a030c1103031305070501020d170714031306180f0204 75
    0x70f1000381c050b132000d1009180c45142c03c002201314030715680b0140e410004902d07641ca40c0c3c4400c21210b00c0c4080f5001800300e21604014001140610592644580700b440080b81c40084140400c003542d16003003059182c0410207100c20444562070080c038444540a40302c0b94114a0b11081820802d0001344041d003d000c555514030400d184a801108a15070b41034007211004e04001040f003500000910035031501c2a45822600746103840490000e000c1c42907aa20740883c155410b04200090003815842030542d942c3c0d00c400000909598400040d46000c0c5860300d03260b24100c0908001d94100915a910035081042001000d072805c0c1c040d20b10740c511514002030108403607402500e2080c050031a0015911001c41000b0311141e00c0b41e44d13039071081c2c410300c15585480d55410059a4403104241060003003410420450346082003903804961103c0c0711718104c0c1003402110003c00381a8800d4801a4920070310100000600c41c1d00d0240c26400c4600900909044441e511950024240510003e2285807110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 311186079 1250 311184829 311184899
    0x306010e071b0305030702100207030f121e0b0a09060b0d05060d080d0209040617030a23130314030f0306040207050f060a0c140f0426010f020403030315 67
    0x18070810600b000c0380496000305045420007400c41c0e0412a4440014440e21190020752000b900070f40301d010b0b51544401c08001c01c00802501c1d08080043c4c4030040e6030b0b490b6644442d1941e040c104c51907940d00700e140000e002900d0340602c5107000b415040b04050034240001000f000403510102c441e1805460f00c0004e45071595800504058103c1c0b0014200d8000480d1841c91212160300420716200704840400013030b41d5901c0301000307450500d02c912815400902c82007194501890640c030f12400f05e200b12184114200180e080709800070b15400c60304000c1000f0509c20007440400c860050700b8200025030400e4410300c00404180701c0201041c0c061900410f44400b0414100306c5c401410503207400381d98152030802e410200a104440c0302c000060003030724621034402400011034411515100c0068505410819010aa98124a01c44d10451181c0d4a426003840080c45441e822031191100543c1d241d107103040040c161044003005034800c0350405800c000800d184e414010b052800c5000c1e1860215980c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 311187329 1250 311186079 311186087
    0x307030209040c030507030b0a050a23101806140d0902060c060c091309020d0201050c120c030301030b061002070e07090e1029030f04080c010e01060806150306010e07 73
    0x201c00380c10500b8042d00300320b1150142c120300c0c07207503809503030404c4403080c11001c01c440070072903100307494208444240500000a0010711201800300d009a115500c1c0f14501c003041d05140b0059101c80007070001d500351a040c9201d41da5507030043c1403610700b0311410081051f081000c0d10600044210042d074404060303007103445103400d80b03240011110a41382c480c03401403d441515804144424450b5409441c8040c1910242c495004890b40251141c0160100c0b89e0041d1820352050a01c8801c610030700918a104000b0f8000a084040c8658003850b100c4d40756150444510001422441c0301d58484070a4048095000079030a04030740c98000c049055807224842501c0340d40300303034210102e4030403c6010003951031503031400b56044070340060b4642c074542040f03c1c003060038050540f00102d580c1c4040010403055076014480707a822a01801404d464981541c150380d0860b804040e9200f042e0751150420441100d042c09a00c0d84072491103014040c109034132000944540c014001c035070b202041079000c5a090351003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 311188579 1250 311187329 311187337
    0xa0e0609010c0516260a111c030e030c1e04050c0408101508070501121a060a030c030b0621090f0d0c050d050f09010818060112020108060901060e0603070302 69
    0xb00065130b80a14503003240841c506120b0280301e403200411061030440400c05900088030346603a1015001841d41aa2a01e02c02c031500c1d03a100307030301214801d010700d0502c0c1000544181140309440b5003070f40c0e003805005c0c103061440d40740c03d15110384c0b0000c00b42c0907a041003440f4ac25012a089500060a40c3c034107000b03103000d024680004841e440b51b030300074015500c10b5034000c40c03504d04031310b144099859884841c80d41d6542e8130f01170700303001484000114130010071940100361440d0291049084640b080004566103421681411000035102d58100c0c00141c0c02d4498000d102d08140e60340380c40d102c1b00d1034042c0c012840e06126900701100880c0002e12018061005218044040090742d00070403c03203100400481e0440d1040d5564041d0b80f0100000a00810840e80e2803017034512580c1c24044020019101e404000703219000b11445041c500c0000c180501c2124007070198004e6403000400d10f030000620b034400c01800369000c1c601c00d000502043c0c0d0041c0c0303600c5076082c0803514540c2d2541c0d003143c120040c0c09 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 311189829 1250 311188579 311188583
    0x20907030213030b13021f211803090905071e0e030f0a121701060c0228030804140126070507080a050d0509150a0507091703070b0702030a0e0609010c 66
    0x484034248142d81c1780404040035014001c440c510b8044440c410040d10601d9003a000c1c00210740a01102c1c08013141c200102c040d110644040062043c800c144124120081003208500185001005010095181c8a1942c11109501d0035080800702001603600b840c14190900c024040082142c00240d6000c1100c00100804641610b100c0c43c0b0920701012440d00310340d030b12000b0030a075203825500300c507842d04040d048804c156a100c420203030365000c0c0b000019482940c2221a1100140000d0311014181c0c000c001f117100f002040e90320b902d41241ca0012800c0a0019410444050700c240390340c0300b01c45540501c5464030191403c1c561140c080a503854412201d00424407800843c1c05050180c203e00908000c0720300b4503052000d0354820440540321070755009241c00c4024110003041e903403c0c440e80480d038802c80308d0624540c05500c81e103244040d41c000c80303282c44080c2d00000e115000c0040707100c106a00300d00302d40010341c02d218684c10041c1c800d00c4c6050905000315004141f09007640e101d0760300745080035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 311191079 1250 311189829 311189843
    0xc0c0402040b0d0c0f0c0807080c0a0f0507090216020402090307081207060b0907170606130b0304120e10030504020d0b0a0504020307081204050f03012003040c0801060302090703021303 81
    0x9680d8110b0410682040f540e8580c1185849402564030b4080c9610114800d0a96180300308200b1036607820300c054001e070000352516602480782240160080020146c8180030f0b464401495059140541c5882400c6d000642c03090300610104050824054820469a07030407a805a21102c00705e010030300d028010b90006a0300d01c00c05001071807081d0048000d00f0014006d5000748082c1d040e620034000020002d49144000804055090104520186001344c000c90003d115505d010510b066001400f0780641041107240701c00070610042182406580425103254240260410081400a0324510840011704207051311600050700b1551b90810040c0320390b81c40031110309141002003201d0010401214124060300c00c040c008500c03800c000070354418446404840c186014202014045a00d0890b0b615641540d00ca1080004010342e554039612030041c01000c407074a030301e02400c0c07034006403080c0c0d440800c941c1d01d002030a20140c4c444412842e40140241009a6500e021702d00308455541c1d0b645c0040c00c05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 311192329 1250 311191079 311191087
    0x809060d05131203050112030e0a080607030204170607051b030d050f010302010f0e10030c0e0d03180f060504030f0206120103030f120b0f09040201020a1a1801020a0906050c0c0402 79
    0x5052280c2011034014020004003156054105050f0211742e002c0c0107d03030322281100311000004c0d1144245980001b401f4003000d09a40c1d071135024515000c81681d4810201b50017150a02c12072807401101207001c1c0e0910010450341c1007248014102740700300c4046280701034810048071400f020410469002a140704410002403030300b42207180110100380812400110284000b900e0b1510030b0310800d0040320024500b0791600340c0c9a20a50050518800c1d50701030104c000b904640c15590381400001143c02922238891034170030106032085021a40d0071082c0c401560307902c04e121055102003614140da5000c0250781c1d211a1900009025000754a0082610b802000000c001c040e807201569000c02c00903204c050100b0701c81c0c0101000c6d5a866114a0340203c1c60320000941440e16000c8203030000d0040c010b803184d0110a481e0108212599201205003007030000a0211030040031401d6554030180c00021070a01034845c01c01414400d192280d0410040007040c0b070100000d00b0300c0801c4003003d00a00840d030b6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 311193579 1250 311192329 311192341
    0x803040206031b041e1421010b040e0606040612080307050a140703030c0216140d230d201f0204182408060f0718031b080c0303070809060d05 62
    0x110785c03d418a61085000740d080009045c07404c03031402c0c0c000500c01880151000107200c9050301c50b2848414110b2035649890f00000d840d11544030708100703000c40c3c0006e0038440c900b42e4144416500c03e40e124140b00321100070100301082c81101642e8000d0300c9454455030b5483e0720070040700c0c046030303010b010740c010103002903aa0109a0580d0200814141c0e6800303880c10b0a04004415007031601d20301c101b1b29411103000e683c40e114504210780e050014824040c1e003071801c00342241c0d049a0782e130f0031142100d0341d408005081040d0760020411003000380240b100c3c1c0c400a03030780441e142d11841102840340100c0c1401c1900010149540c042c0c03000750200e28075a88519122401400c081c00041000300c0c04d0706401c40a07126205107400080d01035400c0d43c1e005040544414100e40b00849004000c00100503944898001000d0f403070950704025401080019099020166000c000104581c041c503002d6108030580304c443e44001c015144202e030040302d0b1036103d140140100d91a44241112010864913000401407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 311194829 1250 311193579 311193599
    0x2070e180c100f0c1a040c09050108160603051510021509030909190b03010f0509010b030a03200f01140915060f0d0203010b09180c01020a0803040206031b04 69
    0x202011036800310340c069051a03003405aa0351181e9004000a0610009031000600a40e0081101d07407041c120720290288018801e0302c000d40a4408031401c1410480401444940d40240e50240c220342e005000b6041c00b00b1004040300031144100000d01d81c03100001001c05880e140202c04a602c094480440364800c1d81001b500c4007000315a40145a04000c007061700d1940010549101036400380210503161910ba5486080c119005103040a0b1900c0e070503240c200c1d03102030280c854940e0792040d0100366400d0500303280342542c24911145000f640a45101404203a010030340201c0340d280b050220254400d060812410301c038500030445180d600b0b11040e917401d07600c0030301c1e110301c200c0c00c120680c1c196109103c8221480c0748180c1e2120f5000004200c031482d1440c0046050500f5440240001841c6c1c0002020a00518003160841c0c010305001c2d05601000c08140a000303440f174000d1000c1c1c0308440c1c0390380e1160f1040c04041d0019005190110000f0300d502018000d43c110160304e101800e0300c0316038070800a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 311196079 1250 311194829 311194861
    0x2100e06071404150e0607051b0109060509030604020111010b041503111012051003120e090c040b0d2415020714010804030e150d050609010b070b0a02090102070e 71
    0x440040e0400d80791844001019003903074242c90b40700845000d1300800c008100c034030481180b042c60380301c0c0007004035200144081204440d452104240420302c80e9100b4005414540b0340e0340640d0910008000008440d80c000c1403240e4072940c2420011201414180b120f40104003141106402500e040d103142d1410300800c1d001d20889100d1306903c4410b40b4404148950140e401d5031600204070303070610b48840c410203900480e03401800103658110f00d69494842c4114400b40880c104081030545081e0300c000e00703106080c50b40c00b06121801a00d000e00d0720141c4a024400c00c070024034500d0756070840e10b58440325040c0848044404210004841d500e824800b0404007180d200f0340050300c140400025400100c0104824041d416101c3ca0215595601c7c00e0f52007401c01d03003602d64041d90f108440703408151110080c0901034645180084c941c44c080081c03010404040c0c10282407141b00340300380c00000e00c803d0348c03442d8840603800002d40c4813020040141c0c078120782908042c0325004180f0402200324052030f00c00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 311197329 1250 311196079 311196091
    0x91009081803010219031112040615092007020a0302060c15061c030806150f2a070302060c01150b180a08101e05090a030f020c0a1502100e06 62
    0xc40c0401c0564007094201d201c0c2d00514003a000d80c8402000c2c4440c000e074040d000d01c01104001501d00f00741c40401e1440c0d100222821074800b9600c10000310025815441100941400f8030308100c5c001d108000c04608030000000c445a8180026842c030864a50310050001980d014240c1e9440b40c00c160011901c070f5800d42d410f070282d90601400918240703070000b046a510032411811182007001514202c2d809034005100c140c2142403030340e04150030f207640c1005000e11030324181c02d41d86a000301147c0c800d5503100d8086803560f40340410a2703500c9171a80462002c0440380d049600c15542c1140c40d0803e400340001340c4540040b40c00455000951340010300c020444580852020030300c03410f10400f006000c041d14001c40301c031030340f00c441108040c1e5a240d00c803541c4003040411100303400c2c0d04441050107480003102c00761a42d82013503491400b0117400c210341021145060014040840344040031400741045841401c84110044840212035802442000800305880e5820700070140101703000d80e070b06e0b0400e03218 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 311198579 1250 311197329 311197357
    0x1103040311031009020a030f03110618070b130b30010504111305120312090f0114070507030f112508010204060206040803090f0604050703030305060108070f0809100908 74
    0x100303c855019205004034141c0c000c1009074424295100c031401034051400032018800420591101c000007080390500c81c108560032040b0114190b80c500741400340d5544400c1c008441445490b110703419808184060751f000009180e201c8030381c11100440d15000c4e0f822114045c0700312001464141c040070449040e82c405a9051005144049480c84144030f800b044082c22a40703201c09100500e04403c180204501d900e084a003021020000d22101040964030f05031168001101c10503210030038010f5031103110640704807003402c0c5010030004d0020310841c1d800404204110b110b560340c8500500f11562001c50803801c5403100ca00c0740c41c2642001c0c016084a5100302c1c8540400a070641050003120141c5103d035018100903119641c07005200d41000d415040c0c01d0140c0c504009841104000303840c803440c054401841140c0c40e5081c06400c0304c00c042d191a04220720182007200040c1c0106400c0d5080c8c1c1e2500c2c003914150b80e140e0310982801c00180300469624140350091090080d950701424050b409100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 311199829 1250 311198579 311198593
    0x72001090e06010c0c05030d02060402090f01030317041b0b07020a0e1506161202060f0109060e13030201062102010206010b0909011208040e040804081e060c0a110304031103 76
    0x100564003030010707100e480180c5400c500022800d521611841e00c090f446840b44840c0d207510703000003d00f44403415101d2001030b0700c208101700542c0341c42c06c5840d0b00400d0741c003d041450750440e1401000c4900003c0d14000700800d91001c1010050b00a45085000f03009502e02c2c03d14030717110b641100070f55104400591254522820105844100c0e80106000b228540c40951400450702e0500c5020f810180700105420600ba20600100e4080111b886980304964042e00992070844141828008107030070682400b4035240061221070072100b4080e81103003403001e5245148821746070032405800503800004000c11000c004a0717100c801900c2c40d191031340c403d80a03030765070380c0c4c84000e10b043c18001c0441d4150f10001040c01004080601d109400c40c2501a02c4418982501c5050300300708600700303550488940b03000003010010100148400c3c0c008030690700080d100c0004600a041d55600042c240c0900a400012a9003c45000f09010265500203a0680f5141c550764100340810303001c00d01c105402030042c05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 311201079 1250 311199829 311199893
    0x70f15030510090b0a030812010e01080a0b070516212307230d05040906050907020a0605060103140126061006050d142502030c0a0b040f0807 62
    0x7000d914465002d50b191104024078140450000d40320840442d030f0007841040c000710104403240000c06080054498510711940346c51049540c020059103e103415800c040700100c0010020300c0c5140c2c0160a501c0c0840d107030300f00315121030101010320200070054800055131007007061000c5446940c805490311200c80111a86081030359010315a945c2c0810032604004c0c0354009041c01a900324404c103414040c0300e038004980c441c0c0b80742c081801380342400b044010a082104c5c100b140580d00180c9410b8500050a080401020350b1f60858100000d110545400009205074465403081b4400c0002c0030200142e03507541d81914034800814460000c1110044018050b03074080003a03014040c081000301041c1c0c0c2464003504a40c103130419140c8035501d0791612090805104880c0b903660080e012140b141d0007060f003051805000c42e995081d0f401c2035400902c00300b80300300c0e00820295402c60300440d0030f09165a441c50015084507074060f00034040c1c2c40c042040b03414040000a0a0a040004000c51601003922 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 311202329 1250 311201079 311201081
    0x30a0c0506070216120f1e15020a20010b04060b0d050702011e0c09170c0a0602071409180f0a03090b0702220f020408010212010519060f0e03070f1503 66
    0x2001c0e42d01340c120804010740c50340305400310b41c80b500441c5103481e150b0403030351841b00c40c0c091908000341100340b400d401014041903006030201ca42c01c1ea13104600d052082c150281100c649003290841c80320100340c18140c3e0341c400390814080104020070800140c1d40703d20700c280d0250019581c56104510307145c0015196801480f400300c04030950041c0c104900a14464803010f41031641d981d00c00c00000c00800556541a0300c0c00201545090003c3d20200c04980700b4001841c145038451405c651280d4001c2110f030100c02264000318100380caa01140d139071100c03000d40500600501c3d507603c0e84101e26401e00c803000b0100b030348810f00744291b0712403040503661030081040c0e001d0300d04040d42c418859130005400d0fa40d4100000b41c0e0100030071000c1101200300d80080c04a820a602510259400051450b902c0780340100749030242400300c800646180403c50102854002c60164500340500003e40080d402c2c064030221060000080840d0403491320303098810004c500500c60001f0030f06500c03201101450203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 311203579 1250 311202329 311202343
    0x122007062007030618060b0a0e0c13080105040803040510050609060d08090d08120a0b010f0f0c0b010f0f050108250c1401060e090f0a11060405091e0108030f03040201030b0111030a0c05060702 84
    0x40508002031982b11000098003c0d80705219401da41d950380c1200044c494001e0180d1485940100c4a00340c8a1030242450703800c1c03c10034000100d80f81c0c42c02e0104407d55a80004258100710709844080c2d290300707545000c1c406407140c003461a60010b2096001c604020455000300b030b49100c00200c202e010380380c00310050292182441c0700c0b404036510043c40600180319100200f070901c42840c1000100e48075854069440303400ba00002203421050005020020f08040010000c01c02844c2259103854524840080b00c22149804a900202c3c0300050030590f02c40d01c0700d2410141c22406c1407425101d101c5105000307000c5489603101e42e03c3c0b440c0002d000e1001c0407810500409000c1e001d00040c103c987d4a54400c201d044640710b510050511011409881d5100740500c114940490088034050b0340e071107107400010503171041d209944204540010344d240310042e03a030050742c20300340072585920f2030300142e410390202200300d01e99200c00b040075000c3e82da00400a544447c00344041e602e00d0b40b00c030798040780c072154 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 311204829 1250 311203579 311203589
    0x302070608010806280516030506010f0c1401060f0906050f103c02060609061207140409020d05370b060d122007062007030618060b0a 59
    0x102c0001401c81c824410120b0017000a20b03265502600d84c0b80150044444c00c0d5000198001c00c0d002c02e804490301841346503004402406d0022258805120051120841410007007103858048507a0f0710b5003000b500500090700c0101941c541c0b0b00d071107a464200624071407044610880d242c0180300228109440301241955441d41c40c100b400450352078200c902c1003c07020418240286030b012241d1508180206400d1007819809041141042000c00010010180405110b9031582e16a182d02030300c0012007500700c0b45545144a41440800c1c0054000d04040001039084184005a003080000c04a0002140d491003072121322034250795031000391591203d0203d20079011413104610046074900003140e5200400900c05204115541d1710100c0d01e1044040300301c0480c0384540c5194165203285980d01c00055484000c0980b54903181000344a440c0611903021141c14440f02040310141c14803400001d990060000d111051106e01a890544400d032820b5655520303015840c3c0c481d0ad4404020012a1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 311206079 1250 311204829 311204833
    0xb03033a061406090d1205070c05040513030c210f1205060303090105090a090908090901120c05010815040509060106090f0f0b16050708010507080606070b04110303070614010303020706080108 84
    0x180902080c0f260aa104d43c2d1440da01c20342100041001070450300e00f00e0a0f80d009583c4180d01c600c039500d00368800c0012500200e00c40c80c00c020230030040442d80e681c00c68140f909407602c80c9101c0ca032400d10a20301540768500b68035440c000c2000384041030f00050000e05062940da203408407030940d50140c9044840694100358581c1003000600c095600c18000380400300707001042c8943c0c042e1b40d5800e05044440c2e40c00103c0c0c03c18400314200c0501c0c0b0b80f00941034014030945030108544a034583c1d8100b07a05055005880c18403001030040303a00603900c032400001e9020080c1041000b800c05900951340e0b00024400c2a000544049000c20210320454010045940200f05000c441d42031608101d031039008207120751071701c0040b80800f90100306c040002c90014181c90300001200d040c00c1500808818000300200c0c02000100480d8000840c0360801c0c03940550456402d10400c03029500080c01c511076040c01401160400072481c2544040a2699040324401e80031039001c1035550109890096091044410035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 311207329 1250 311206079 311206109
    0x7020d0f080906061318060e070b0a081603020c01050a0504020a060905090f150303040b09031605090604090213150f0501020111030703020901030209040e010203071706130b03033a06 80
    0x7900300400d800307a02e00c205d03100100b00c0000020070365501c113103c120b007910880d17140c5440c0c280050007400000c000c1c0008429440c40e12120b80d6024003580000390201c094900244803100846220380c4c1514580400f840090041c0d0420032489006001d054609910920741350600040b81c034050b43c850030403104d02030200106a5100348101c802e8000040c4121256000c60b5040394265400340010f0000c5c040c1e07508882e4840350705009141c030300707090980c4400003440080340500056640001c0154408030445002c688400c80d440461800c5019480041c8817900788180c41484a007031140500c1074900800c0321448440c4e80b03200480c241d500d900900800842d0800101e03a013207210740c00501c08120181009440c10242c0004103088805441d003807110f03a54080213006c0c40590084811400494007030b1101c0301424014002000b03601100f815640c041d07610800b1000e50740b000d1040c0c480c0e070b00e0b0001e4516429604200c11542005280c200d040b04d00000280d5140311004610424081c1d8100003200e4400c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 311208579 1250 311207329 311207341
    0xe090c160206090409020d1a06013f150302010e03060f0403080c130312021911010e12030d0207150e06011203030e100618051e04140607020d0f080906 66
    0x441d440300c0100c3d038201d034807000311001503121031515035030305403043c0258548c407400d81d0800e044900000d0300e9241000080c0c01e04c0d04030074a04800c14500c1e00c1e48650015908080744404904103500c099a1400143c24212407840b10701040d0540d2084a000303880d01e685c0c2c84401030816450740d404440841c40b284104001c0f03004640f14a01041d840040040e01901d072072020000d0400d450416481141d2803040814004110ba034180300c50440c3c05d80d6070b06c201800c02807036694001b0006d5411900ca0401040200150051ba50b04546081610010065940e92403000d110fa07000303540030050039200341350380040d01d000000417840366200703805462001e4001c513400c2002260180e100010140c01309611540c89403c618414441e40245265044e000241d0307601d4a2020308220b424a00c54070700709c51400742000604040e070b503407141c025884140c4d201103981e20b40c07400c03801312001400240c40c548103540c1006100c6400082c50600c008054442e150355120040040302c030200b04499056841d0840d03004103030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 311209829 1250 311208579 311208589
    0x10c0206041424090f010e0307090e1f0c09050105030f070e0411030f0103030801080a05150c12040b060f0f180c0417070f060f0c080a05070c03030e090c1602 69
    0x603032110020520004460030020200120f030f81141c116140390000101e81e01c0a10302010b11a03803121003805c1400d58843d000002a444249511400e130200ea00c8000310184040d05001c9403000710110385c040c1440058210f0140020300701c001e0004081055032002048542c041ea040e40d1103441c80c400c5c10307004e41e52000001c42d8206444410290095164400780040c1c080f982c01442c440c814079285010782d5855410b00070030700c94040c1c0c012000750300008c1c030642c0400e0010038000740c0d408001c14032000d1030710b03102e104003182d00c262184900280b81384c1003800b0800140c0300c078135030003007034101c41520701d10320280d080101e50302e8001100e03540f08100041c0150032038071816603254031515010341c044c2000c5c1c1d5003080d21103c0071003000100c002d40148209110640c44a200540940618540303a00b210045400223064100364040c06042c02c3c1c80440c61522151040c411208842e034031245490000f5520304c3c014040d81d204a0380e09202e004040d001800d00303071481c804e0341c0e0342e030403894602040e83c4402e4080c0300e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 311211079 1250 311209829 311209859
    0x2030c0709090f081c0203010e060108010626130807200a05011215090c0e121507181d041202060408090402090411070b10080c0307090c0302091518010c020604 70
    0x412900058003060802400306d2014500030f00c1401c80c0c40304a031424070001440004143c110606000c2c00c2512102c0c0c2d41040f07046004103080d41742000c404d50311112080e02006600c0940140681000074001d01089100070040240d40c0d0390340014410150702e102040000e04c07181c01076600064060001d595851840c2c0c01000c2c090740350045001a803600c4180c2c070016152144071a42c0410040700c800e00d0a800c000829a500010100290042400c40e4402c03041456019200500308a4034074241c040c40d81e10107240314001c21403001442403c080000707007815000d0040790290b61510034100f0754280d00d030003ca4094031030799102010034907006524040200035001108240c1d00309a441e100040910003c100a10300c645c001d00f02c017070303c51401803d1100d10a0207900b200364076400000d03940513207840014001042e248402e0700030032146415a4110700034021048096400307504030342070249299454000340080107000421801c0c121503000150354440f902a4001c1d08210104800c0000001071510f0ac = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 311212329 1250 311211079 311211097
    0x603051b010f03180c0e01050f090f010509040302030f070c061403040c06050a021005010e0114060a05030f04060b0904030807030c050c0709020d06030503030705190e1804031b0302030c0709090f08 86
    0x488000c561511100084030f030700441b44a401d08001444503240c0f084641805950403240c01c016444d0500320126802c1040c40703840c1c080c20781301c00841d04140c0248142ea944044019090f03480b0710302402c082c9001000d5104100100d0740c00c442080c3e2034030494044a1060380c000c4000f4400c10325008088a80c1d600182800045004603541c2e52041403050260034002c140501c2e1261081d410318003405070030b0071050301081c81141d007040310b040840e41260660340c0c40060001c80d4402c503965070400134060178041d50070a07807101c400e1003084101a040b8003880c0c0107144a580c00c003d091188401514548112000b206903580880c108020b03100e4642c0050121340b00028001c14640d69039074869143d50001d0f10080c002c1480841d6208040d05001d2400c0c3d0343e60083e1601203848010f900c0481c00c0803024480d2a24617116260019003030600650001e4810442503541c44080c4242d414002d44a8201030b001c154107000c1d80c407001403c2030103801029030302500200d0342c4410508a69511080740e20038112 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 311213579 1250 311212329 311212361
    0xa050f030322090c02150c0702032a0603092103130224030702030d0e03190e18090c0406090506181005041d0d030c05041a0405060307030603051b010f03 67
    0x81400e290714090b01a0001c2a500101864a02600c5e64814610007c081c020201c0781801540050381d000550b4400c0d02c200030a0f0b58008009840c208207105200004007a0890b43c0003007844400b440c00240b07241100e100701e03c1c401d012940202d102e41541300582d0108162000081d1080140ca04800460380003143c9800825109640c27121004450304121461005a0000b00e90f0b183e07440400e0042140c51002c0c440510304d0810b40c041d9114804800003004002c07c19603103008902c0da04d404580d008074003100c60f140b400e646801a20030ba6542078090a550041d41094000161071900340030b5240034503402011a07460003d02541402200d100500f40c6040714400c078000180d036151480740040c21007034404803503405000c001d43c44d0303d004510003000042625241100c0c402960050544003520080c1c4000705003040483c0310548a4015038010941c85400041484080c40e01980300d582100d106030203a400e040100030342e40c0b129400b89120103020405010003400c00310301c250701c806117082003298 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 311214829 1250 311213579 311213647
    0x19080f0a051c090b010e010b0307030c050c070905180c090f10030b0403020303101d1b09090a02030405191a070908060702100609062904180b0a050f0303 67
    0x1440100c40801c1c080300300a69035a18000c0e010301c4a00004c1c5805051991003101203540350000d5403580d440018811020181c2d01c160055132144208221034860500e141100e95103501c40e1280002814103443e41d810403060303480c480268820110f111844900010002d42c030719554004040b03a018002084c601501004800c0400000c80ea20417541c000c0703000368001c6842e843c1c58082e500080e046900802040d407a400e60701468040c00114071079100c900c08501c07104040360034400d00d03414001d80c19043d51066804042280c10101759000c0c500c924064002c440b03203001c55111a400c0c108140c0310250240d10604e00c20f440d03002e0308442c4550040d06515000e00d0700c0c1e59507402d607400d2507004e803072502c010303001038000444840c0035008100280002403400c11800f031810759210102c40013420400075400a1031042c120301d05514040c1d400a007040284203440d02a0226108010b104a0107080c3c03081103400804a032600301103e146d50341403030180084d0701c0e00c495044204280010100001c0c8911a006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 311216079 1250 311214829 311214847
    0x40209060307030501030b0f0108060411241e09010503280c183816050a0302010e0115050d0f060c0207140f2b1a010819080f0a05 57
    0x100441c4030701c6440d90f00064650440c5031020301104054110503903c141013005200b03a041c042407503508281e00aa003070418a1240c0b0119081383e001082030740030a4034620b000201148034000503c0798003181444103000001c400e0314016039000301c00c0c2d502e0001d4400d02c005164844131440224a10629414205072180d50500308020380342400c03c0e00c000a80041d0080b03c400d410322a142014041c42441c101ca010b07002010b440344072004000d02e041040100d0707580c03080d009190089410350400c03017001c101000018285507a680c51907903001c600540c84c14242410f211810b1242403100e0b5016540041100c2c80e14041042c3c610001c3c00550303070303032110002c4000050703c42e218042100700160080c01703d01d0b18040c2d518541c000802150743c02041040080c1050384da80032107420302e03107085001408109070020440f1000b95005200100341c80405640b100c5c0060365415414100c4038607c080700c100d4244074030703282d4065407200303c02403860b1000e0040c2c900380401c00d4082c2ca01c01c492460400d082103018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 311217329 1250 311216079 311216089
    0x4060b04050c0702120a020303090d030c050d090806091506040b060d0c1808120912070308030106021f0c0c08090d080301030f050d0f02031e0705010f0b01030c020a03020c090402040209 81
    0x645031248074a100045060450031710510501c2c09448600141052142c1a00440d13120f2040d542c0541c400d1085c169640e040501451241200c0c9411400700c6601c9903050b000509a251503010301c3c8060300c00c1c10b00040180344000384429a080f0504252115a1520307002d010141110300b0b10300341c3c01001441392a100002c103209884107180260303503869034007058621100c169440d90300915010b0b00709007507002841300f4440880c0d1503002c0c1641c8800d038a50901c1c0010342000540e800c000c081c06c50020001400d40e5000071a0100c040c04c200e9002d503903074190959041110703403180350314020610070700030a404901002d01828a91001500d083d42c011182d540d5030f500e0798401d8004503411000003010340d0a1010401c03840c405001d090611840c455030460010303549004621202e01d09844403ca02c0f44c1c480710345402d65520710780c400028841d0458028001010f04095803c060000c4d01c0c01301c00c44c42e540e00c0007480b05202d58054014007031901d960018011810401007059170410b408010154481d212 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 311218579 1250 311217329 311217331
    0x906040801050f060127141507110a0e1303030515030f030d1503080412021f02010b01030c050405010c2010091815090509010e010c0926030a0804060b0405 68
    0x506100281c4625020b40090703c14005121015420380d0707512100030040d86c082d85c0c007006882800f070316100404880000126280043c03082182d02a201194800812a05004059100d0380448100c04183c3e29611807007805003045a8021000351303000e026601090103580304030781203c954121880484030210109240880c800c4030800103a0001403280c10001c0b03d481441c01d403030703012002c43c081540703191101803542c042d90040c040c680d84062003407000c66440c90801e56280c1c21b0100051b90208030844041d00800800c000107002c40d040c201000d81103071160089505840058443c050086801c5c0c40f004a0310042519440c091500c8030120740e2607684544101d4030144640d511600b4450810400c07910500c45040080312a504008031140020b480542200940758038450009007070351034994143c00b60415841c01000e030b51030640787c9002288e004101d002520302070400e044000e01d6050781c0c046926102d044c0d58140750801c0c80500040c502c20000182c1050183c10042002e881c158001421071754 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 311219829 1250 311218579 311218591
    0x6091401110904140c09061c1a0301050711060703180803090303011809031d061b0303071b0f0b1f0f0510110a082104060501030201022a0105090604080105 68
    0x300400c8100c40ba00d024041c140340d100c00504c02050504001c00042158003c0900c218440c02c40401c0102200c02c00c1c081c061140c034001c010a00201e8201c4140c0312400c1b103028031042c041d50070000010800c034004c0d5501c0c404051a80003d01b0b0319511804200c0050024803419107100030b40c40781d0715000c600c0d034801940c001d4581e98042c40c4d903945000001da040c8034200c1e220900150501000e400401d070815074445210705040140c080310011000005d50b580704074181000d0462944465600304800000554464a5541c8030b0300506007600700d2564280c40b0301c1400405280140000100041140c0e89154001340c40c6000c80c03000c50010881e00d40803507041e0708460b0090000540c10000782c6020601c04603201c9a0b420000d424040c181084c3e500d551590300040e00e644000280701d2410041078a0f8168082c054000185d404c0c1407900c3c0420185c1420b2209a00501c42e404410b40705400181c2c0b40c15003140000021640070707620100541c2d464002c40c00190b0f02903014880043d00c0da8013070040520402c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 311221079 1250 311219829 311219861
    0x14070510110c06010305060702010b0a03050a0201080c220936050111030a02030702011821090b070c031109190c0201140a09051c02030a0503180d0207062a06091401 72
    0x488c244074000d00715010040000d01c1110003110800c089038001c901001d6003602841c2181145c0c0c0d41f19000303d114440c400c603000019505a08421300d07254541d407580c003a60100b180070300001c0403200c10550150400f1030600b0382140c1d8040d80c0803448584900380c54041e44a100046036202282c3d8120a054200b01c07071004c2142d03000002c0204455081c410401e054000c640a4196203d19440f000e83c040d41f02d0000c0d02680c8900c070071560340326004041c2d0b00700900408020960b519624500156100d11511044a5076244040d25400a00e800c160b01da20420404001d03d0b058070010070502c0240c0402a1918255548d9490203017540c00d400d04424032503081d8500c041110001361070194648881810511200c4c1b00441e2040601540403044415070b0066103801901ca0f2911064a00702401800583d00745101e2441d110307030b020381c0224402003180e00d10348401d00000580c07e0000041c2400001032010703440503c0f0400c00099842c0e00c20708219000f4400310103890541452039003125087e089440b00c079 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 311222329 1250 311221079 311221081
    0x72705090403125c12010909032c0a03110f0108040c050409020109080312010e0901090816140a030519020f0a0209040f06150614070510110c0601030506 67
    0x2d24000e0140715078094202d103aa0f40780721100043c02d0048541e41c02d60600341005110329103041301c841401e208984543d10200b60000d40d20100c101896808034641c01d40c1d42d00c40030000560310b07901e4030030028007641644500c01c0f00c0e04e981e108a428109000c8500703802007030040142c3e2140e103440c528a0081c1d8420381030700c01e0a010000800802c5015015082d0400c00300504100000720310707001390340c1250070645010a102c0400c1c030040c0c1d10b000558000c80c040b84808141090030400820600d03040320240c29049a10703440d801c0700e103400d90f944200d001d40598000c01c800c20800440c441340752505801469203481440d070001c09203041c80c0203640f0503400260040b51b2900d07034440c120300100034032109000030301a00c1d03101142c680e03d603002c10030041c2c132485020001a041c415207a40f02c001c800e601c0341040016200203038405140b25200d0041000207100c003808405031015500482d0b0307400360028020041c4090342490403000d040098034040440c00e040c06a00d181000402c902030203948038401504003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 311223579 1250 311222329 311222357
    0x4030903020f0f13020a050708030408071b0305210c0102121021020402031b030f070215040b1f0b0403052b09031106090d03020303040209070305072705090403 70
    0xd02c844902c01c9201d00251501a2115507681000c215002050000541c40f44080c071810350b0b00c0d010b00b64000e0003010000042008021040000b00300103442045510340c024030040050ba4448154000144107600c17140140d0010317800040320300c5504800300080c620b05040d0340b5000b400d9070060404002d0b01c01c881c2c0240a00820401403000c09021031555081d603924610a00c407078208540c1c0740183c000d0741d00001007010006554015452500480801035890600b0040102419412116070006006100e4845148210220795a0081c0d400070307403d07040c5484581030710440c11280040b4007419051140f00055526803000600000c5000304090010910b004043e0742c0f1010031541d400c83d4a5800307650040000d0b0700040c00c0010b90390800030243c044000b10010807082d12a078540d4680c000d030000d01490405600000440c42544295034404058071404070a034203442050303ca82000c1242c040c407000c080610114400c40700c0340181143d0040e02d503180040703010b40406603401d40005402c1058484c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 311224829 1250 311223579 311223589
    0xa080607020d0f210b0a170f01050f071107030203060a1508030903030a121e2a0e1507060e01230c0304171b03090a0806091002030702150403090302 65
    0x420038a150800c0000c0100c00c3d00300a010741d0b11843c5448041c6a800d07081c1c00d152034a40d005c000d0144002c0d00c2a21110348407684001503460720038081c1654810721f4940044518103000d928007a07204040440e005454929040c0d8090354041011442031140110000c0560b0702041141d0041f030800c60000741ca4032070480300c0d008401e055007044000d58001c00802c40d00c0d0300e0010807100b403070718140750801010010f8400c203800391030002c036008400084129407203543c0201d0f520010f0711901504203000f2000c04400400f01d15001c3d03142c400d000c81d10780e115444483c202400f40f81508409604071503d00b6420380d8450b802c46101100e2079900340e41d00d0407545040f94481480300c5856212a20840903440c042e5005411b41c40014001048004c1404072030312a45103407000c1e00c1702405208284040208064140c2e6078a4107c114101d12485581e103000403401c00106950307000c2e0401501511400003c51fa42001940c0b0142200c400c41c8207082d044010714841000c118020f81c400e0b982d0042691441c01040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 311226079 1250 311224829 311224843
    0x1104060201111201092a0203120a0b090402010e1c1a010509090706030b0d0203030a0c110402040e040f080702180105040c0806061b0c060a1101060e0105031504060603020a08060702 79
    0x40c02146040000103c4802a0310100781102c3c0c003e04003080c0d10b00080400e0b4082c0b03010801c11460700d205d14082c018183c0c0c011010302a2051140b2034040c0c00d99406040344280d401400035150860408008600554480c1001c40a040d101501c0d6401c07540b2422600d05c3d800740e134034200b074a0b0f580c200110420492804070289005000441e01e041c00f074141402c01a03150f00d245d20500c0705155903001c40a0ba582c031000c603250020b540040549458044800015101e826810b00480c0ca500f4a02220815494180b00340c609803101140700803103030341c1d0303e030f0b1590480480c6c004140d13000c0d081070154a0041e660500d0054900c0201c030f09001d81549004144010f44005882501c03c0c80301c000100980c544508050315490711105980c42005500d546009041c440581030751350f00100e000403003030f83c5a40c201e4501492a07500000801031990744102072005031100380502ca9240d0001002078992821610241c0c1d00980140000184030740d599001506182080d400554903400c10300c204920300d03405022070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 311227329 1250 311226079 311226101
    0x3200103020903030d0e07050d0b090601081c1202040801060b190201020712051c0501140f0a05030705131b082508070309030e03010906022d030a0b030f011104060201 73
    0x1076081000040020b91a805140854804955a00f0040c0c8851404010341c2d401081c028109001480d9641445012070340111210200752240c04000102848000781000e10451000c0c0045101c0a05540454140c1c02c801c1c00c0d0340c401038003030002190549080c41400020040c0000095540003000e24840c4c0741403080c0c41120559105100e00c1021400c2c40007065281c0c9194a021544d130700d058030082e00c0d0104099551a0300510f00750000caa01c040340304903001500b01c115645031403480040e02f00010800c66006858040d001342400308510305010820410001d5508008901101041c00310700d0f880d601c950048000650050501080c0300c1c880d00c409400e003407050310701c041ea034081550280070b80002400c03100802d0f580750703001ea0500d84201080d541010004000307004d02070840c20000b000e908114171000c940c119003e0220810a15200c0c0313880e4580e98510b44038210b42c0c3d4050301400a03c903080019405029072102141030003400e1140442c104513140c1c0c1e250b00e84d402c000c0003e085030000000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 311228579 1250 311227329 311227331
    0x15280f0f0c050a0b040f0c06020105090f0609030406050a11030a08040209090a0b1810050c0d0c09080601051504051c0501060504140a0c03093c1a0408040b0403200103 73
    0x4601145000c149495015000009032101c5e441d24604543e18001d1810080c0550200a4001c2a201d6064010034010500d082c1181c0c94004442022515140159a40711481d4401c00040140fa80541c010742019207060a00c03000c20001d40071b189085901c500075000006e400c2c0c0c01084114900b03c848250003646150040c803c680282d914000300010203130603904075058010800c1140300d020421118416170200042c025428011b404550f180c204813200c80659050011080c500c51180080c1e10032109588010040d591904040c0125034a4803180400300c8102008007003402c0d00c908081c0b0658141e01a10130144e041c160800301c1c210f581d2a00007034401e6080c2440100344d145a00085a00010f92090028000d03105400c25001001404401004002c921001c402e20003a00320400303020556440480f084000040e421002c40307484140002d00b1b2058040038070804034900c1c031400e03034054070801d00b1a00c1c180e250b802901064109620884000d1640f2101300742503100701e2180b5800d40000e080c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 311229829 1250 311228579 311228597
    0xb0603060f06090a1409071b0605040c0f0305030304140303040309030f02131107020307050a0f060e06070b0103050d17010b0412050c060f07050709060302240d0f06050102010509070515280f0f 84
    0x8c0303481c820304001c01905003a15100464144400d2120b08002007c0003910b25500b00d41c1e07840c1c01e80d200d40046506482c2030a40a080303c105a1000c070031648260b6045d40c40510710b81c296516080200e603d504e099802080718031028000d910244985d24078070058841d440d44070758061041600d016950340049010b0b015400d01002940342c415041000e44000741810070705900804042605401241005411403880c50000000e1007804144803950b040b01e542e420b0484446c400100410100a01c21040003d0b0f04010070030200c4101d1078204081440340c001d6461140c07001c000200b4a4001059103000d500c0002485020440c04100e06402081c0303100d018042d00d8503580004041540011900c04507a9460001c200340c03c03056001c407081c00d0500281007050420140c55a0300601a03401014007641c40c10300485c1084400080759000c81b8401401c8954404005800700190340110300e600350750110741410030325a00000c041900c814500c0c0ea44510480c42015001850a28a00c1d41070302400041d031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 311231079 1250 311229829 311229857
    0xf0106030b01060e030102070b10030c1a04030b07050909010e0106030e15131a0c030a0f05060f300115152c060d0c0306090b0603060f06090a140907 65
    0x905040c1150f0160400c014030000c2c9801107406803040d400e0003050030400360308000341c1d00303031425403181540e000c0c4030801c554540b0382c0c07801c8125030044000e90200e00d01c14003042001520118000d5070201162414a080008000124007220b10a8002c4041420b00c080180301c210380c10300c1070325007189040c8010040b00088410070601c1d150064908100106217030001c1c010b0103210881281005001000c1000c5460100c41c407a0503504291224003045080292030703803e12041e40a558044e40700140f000440030816010098105124049000d0440303142c00001004c000044689128005040022805110030480e40d41c0d00c441d9500b01c00190085107098902e6184d11a06004a40ca60a4007114401522040240c0c1c4520f10b4130350f107039000100081038121305140c2d03040039040401700d840a00460340c45205040c2564038204025030003450500004520f131a002c84001d104442c0584003525121008011030360713841540d00a0710703022416604292040c140483c0c082c2e40712504d85840001d1309055 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 311232329 1250 311231079 311231093
    0x30912140307150f2c1501060804060f0c050904051f0305061f0b0a0302070c09091401060503030315040207060e0102032a03071d030726060f04020307030b04050c040c030e0f010603 79
    0x1011343c1c0404c1c0c01e901d80e03110361281003008001c485588500d06c1040c0d0f80d20030707005060400454003141c00c1800d064080c44600c1407070091003a1000d45403205800c0c080c0480c14000180300061800d1264011800781000d12021641158080c6001c0ca02401c600e103015040100c141043c0640e030310f031a00b0ad000f01002404c3c80c1c5400e0341e96401880c54003590f58102401c0007082200d880d00410301203454403020b0003c11110040001c01c232100e1030024811103650f4405c041d240c0c0011900202840e013511003600c92441c003a401440c00d11b1181d100040d040042c7c88005003282c0080355860a00302c2e03100d003a00d003d42140e107041c555240a10307407100e1440c0381c0401c0080041686142c207511640361090060030aa0f014032030140544149901040c0810b01d07502080711305c041a00c4a440c25003d030070041071410014a0005c0e114035005401030070818038555800b41e078504024401d80302c0d4061444100b405559901a04840d0203880d43d0104101c0c190880c1a0b003810b146000700306413a0300d040300410001c0d103c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 311233579 1250 311232329 311232371
    0x40609061a12010b070f02100f230405010e030a05151f06051213020904030807030c020c101107030c080607110c0d030f12050130030912140307150f 65
    0x16003543c494549405143c1130003142c082e1b490007503000616210540281c0d6100790300c10040c4000742e03224030104c1003c4890542c4007a01e41c0350000001c40800c414841540100070701e9a065402904450b0903451a1716074500b00041c0b20020140d50446800b4420001040e0142350346170031199400c01c11181c5807080241261045d0b19001a01510322800164030407200c0c080e4209054014042d109145818540245800720888540000c22b203030800340d0410510010f200010307184003401c001c10312090848281c0369599500b0040384039101d981400710018000b008400020715090b001003c2c00c1c00c2c5013101501d10314181c2c81d052060f84c0301e0310007441550344031882d501c02075800d81800310004601400031140c120049107005a81c41c01c2c0400000d18428045030300301111010002c0b0100381514a180702500040d407100500000e440540030701100c000407000000c1d50f88130780c410704a0b900600400d981103800c440d034195070b09007401545411031178081c040c0d00800c40c10808100181d00c21528100b101600d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 311234829 1250 311233579 311233589
    0x7170d0f090618080307030c020405090a111306050a0305010c0909110d051005060c0c1507050a03080a061d06040501090608120c1005090a03020c012c010e040609061a1201 75
    0x800090020549000c1c500c0e4031001e130031340100741c0e99030b400d0604005d410144942e80403400390345881c00155407490040381404804c2c0c3d001d0501c2180c1c1c5002c1c401c01100488030614126620707980d90300090650740e10411a0004e500c074030000f141c0d0302d00a400c09042c034905644080c000d54100720480390b81e52194411626041900040001d0941702c0c501d02c1810341055806c6644c200ba03001404200b000c03400542d2031141901121140c0b4404420f01e04040a4028800000c001307a21907103882002034000c00310660b1140306207800181140e03a810070b0409140c100403400d000444400c09028060405005250141940c8070b005d000d468039102c8011341e00d0851064021800002140385144c5079820320800c180d1500b15201409a400e000640c251030750000341088016104003080600a54003801ca0041d25241031020a1602c0714440300c2080021150012181000000c514504490740c562158001402a00c20b001076007604158400d50174141220740c80c1d05500040c0642055004100c0c0310505542c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 311236079 1250 311234829 311234837
    0x5150a050d03030b04060b270d0f03031103042f010914210313150228060c020c0301060b0403050604110a09090b06010f0305070c020f011107170d0f0906 67
    0x207a05050032001802c0c0362a9069101d070038014001014100c02c4060619641507100180819005041c2d02c10703202401d000d555000b1640000e1407020400001103018110300900303002c500d003d0b08481d8001d01c2d90040310101e9502084c01d050001c050480d901c3c0e83c0c5611316054403503a8030000400040d140e0140d41c840c08400b241d441c03071030180c02d80350300142c0b0305149642c0a014005501207013203140c032070b005408041c00141100f140090401c07580d01d840120424660050404469021090880340c14505c000010f6656a5001040080c1c03040c440c00c0312000065000d007408101d54001c041c20360720b59a11014442c98240b2090000c201d0228001d074106910400702d08910b0144000302d6201c0781c16501ca2646a40b85c100410248407640c04102d1007040c00340e032459003e13104c0d0003040e000c0303c0c015910034001600c0c815805006090502c858003100d01d05040058001c4170070b040540c941540c3d03800c6008440c030401500c140540c001c001c0500c8140b1b9a0400e4884c5180c0b904000342003402a00c9080100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 311237329 1250 311236079 311236099
    0x3309100b030c010c140c0a090c30050c040503100609060f082505030f01020c060f0405100e10020c01060f15320a0201050402120105010501090501050309010608070e0a05150a05 77
    0x620400400c1101c0c80090030030b081c01d230356a41302e4600801058095002041080040000000d8940f09403c0200f420058882444482d503000c5402444c00030080e502944003000041f40340c1c3e0b000c000ca11000300c104000460824205028030054821540c010807166a9114044c00415404211418186c0072001c0703040032400e00c44900309201540c0d50010784c06003c0c42d10a050000d07419001428440c000c58220340460704c0307604c0305d4000c6c00070456018200c0e41001d084101200c060341c00c0b07201100c20100441c2e4414488001200403644100b0400301181e546203400c200700081c11002400a09481c0c03c003e89203410f01d400a00800071046603055509c0c2c8103504c840301103040b200f0400001007031415942d101c03c1508030182c0240000e440c1a4850382d0b0700745280e456500c0500556050345c0301070b520200c011340781c20019520b035000900b01c44002e540b900c0d80880c084500300002001083c001d50104c01509003055940d0807288050401540c101c25401d120340301d82c840741607030800c641007030702d540e140c1d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 311238579 1250 311237329 311237363
    0x91501030f060e01084207090504020d060509090606061209070b0403150f0b0312070606030b04050a020139050a06060f0f080601083309100b030c010c 66
    0x41c009034100403902c0c3d4104002143c1c10300300081c030710151405903803440710900300d00d83c42c1504d0705900d5050320a1902896944c081d03498249400701d401100d03506040307403111748030310004059811011460f40170301d07aa404100818500b181c42030790040c005402904090601c00d000c00e400380f04018491601d02e5202e40070420040e01001440000d0030301c51030340c40e00d0b55140d15104105981d404102c1e0707061410040f40780e803a0121031041c061740380001002024410340b0040f5030146604540720079110346507141c40000c0858446d00342c283c881d5100e0000b401e01c1104901c0090442c1850703520030000b0320064008840c0900c618015a99400e203100c581c80c1f5610540c0c070785075280c81ca103001c00400841c01c0280000d16594450441c1c2c0a840300707848903101c400e031100103140c4e981c44244601d04195028070010403801980e009505964541d1511400f500d0b60018031070071402d0810b40302c8007495070041c820b11103050014402c048801c00210050081508107600003020881d48241c041c145821f40801440307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 311239829 1250 311238579 311238581
    0x402150a020715180e100311010903020d0b0a0c1106040b0402150a0c12050c1f06030c0618050607030f11030c0123011a07030311040e0420091501030f 66
    0x4003d183c50495003986402d0798000404504660000715100320340001c1c0070541e00c03c40044584503104000216101074515125510052800003806040c80081d080220150700c03102012100c95000351885134079400e00003284021501c0e2008602c4c10030907084000304607158041021600183c01c0b07a1428210f84480c00040c0c1188065580c180341010700284255511750000441d9100901450103c050306161050542c0e5038030641440b01703031075044400d4150340001844004001101c40c03030070005209841c0d540340803440038550000d0011036003007501c440b0140004000100580416030b00c1d04d0810005030782c00340c1200c00c0c2c0c504000910001e000d03100710900d0300300151400300350702e00000c2c4040751919040042e0040004444070302480407034001b088234010501c0390700d004450040402e1030a0b03400e407012001049a1001c040b060071081100040c43c0c2081d2507078a02842c003500444501202c03081c0405000c02d41c41c40e956005917101010030400404200e180319042202f030030041100c001c4000d081c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 311241079 1250 311239829 311239843
    0x403060905071805060427170705121206030c0f0d0201030902060f0c061003110108070521150a27020706020a02060403122d0f05090f070e0402150a02 66
    0xa21409062040c5180f000c00700c0e0446401100d05075002c00c03064900014807400850503040e40701c2d100302031010500010304003065640304088160052800e011181d0740e060700700049950354107100d200200e03500c0c00510680500c1604124210010301c3c0305032401000c502a40031900000b40301d0392101c1c4000c415039000e5000001e007268014241c030740d0b80c00c20390b0006107030341c214002c1040640301301000900d04080014003001507a4000b221011000244001190319850003008078007084401c0c04801104c10351051a0f5100c503401d0031041440c0d1038407804280c00c00c501000d078180700d030485d5002002100207aa05524840e11201d1000f00e500e60800c022102a20941e980149402d02c00074100102d940e000c10f0031030142d0f12a66911b41c010190306d40000c255408604c840c46a1488614000310060a00d400c6820249644501007080c051880650007280c0c41212060050341207000174920f000014851480a00314854114056040940200d80c60040e030403e4000f04032400a031840740703d03000304100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 311242329 1250 311241079 311241089
    0x3060a0f09050f21030103110f060f040806180114070810030b0405010c08010f24090e07170108031303060209061909030b0f07081519030c1703040803040306090507 72
    0x4950011490f80c0440d55030501070181c203541c0b0034042c01d840b1500610030884c3c0c100c070f0f00700c140b442c0940041000c1080038681c680042d54001420400b0740c0310317102081701403c0100100350280c40945454004240da030b07184030322010066490480408600c3c821202c103e5080700951a0070045607a500200001d0110141c201a1042840c58200400c00a054020085c00031b00ea5845200d40c0e640c5a0700c080b500f01140c090116200581c00100500b1031500c04401901d0102c1d18000384a25500e00906030b01c000c05445410002d454180258500d800030800c40c1e0041100c40c0c001c510380080044040c041e007006010051040c1e80024042c0d490b50f90f407000340c45040840380c0101c11095400d200c0540f0030540c5110440e8030301e405500003034581c1490042e40b807241e40148c51300c071306a54030902c20009110000c50841ea104a035600800c114014822592025512403181640050b00780060001c0301280700907450000d07802000103200080c130210549044950140002c140c0380c1c407501c0d040e4100000c907001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 311243579 1250 311242329 311242333
    0xc06050622021c09020a0317070618050114011208070221031309090f0209060a0b0301060f020715022e0908041415030c0a0e0306102303060a0f0905 65
    0x10300451015564014142141c0d8445071901a00e0b03c400303000d0603903440050196103d0304200c0d0404c0428148e00c451a02404542d039240d1030085247c2e034110840d40707440f048407120701040b0800800c104003449100f00ca1018212889a01d615190190114000d411001070101390049071000454680000524042d81c84070480f001c2d51908038a040c0c3c1e00e40165205a449052018000880c50158070504c0900c2d9042040d10014031a50f40a01001c14070151046030000c1d03d5000000c1c40700201000346010f41401d0703803214440e90203e200285030440c107401c4100001d220203071200071141c0001d030300c003001c04202c42c500101c1c0d0030303480c04c072090001343d00c059104007400d21600300c0401c060f80009005450044400200d01805041402480500004030507002c00781000401c00421441001c6d0000c0c030020300d82020480c0300080807a04219064602c00d05a0154540038403204401d052036080c114102c2ca482c0d190b0a40d42e1000998400000e06140484c03a5540718034104101d9542021001ca904201 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 311244829 1250 311243579 311243629
    0xb090109050402010807030c0509061812030405040e060114010e0310050f01170303070905130e0106120209130803040602160b040309090b0a06140306060405092503020a0c060506 78
    0x416000360504032000c07130000304003000044019000c1c0c424180d40300c0260351080e050801c82c1d0700740040c40e4051a51040c200e2400307004510300d949d4000c0d801d941c814480d80515101c51505007440140c51900a06906a402c076a0040c003503c8903075811461903c1003407800d01c85014880c0003007400d24070800300e0107a00340c0c20071040184583d2035001c0c0714102d48080c070444070030f08840e15150340c0b83d0205407000c2c400245034820821581c90130a00c11480801d01303141c00644440c4a1130130508680c041c1e842000c0d91400c1207402829454180b1440d6070003092072426070b09805140d40c8180c42840010705c010105a4041103114289a140e103003110003030f501c88908c66480c241800c016004840307034407030701d46107070b0516100c1107890500076110343c121403181d1a02600c0050001810800340c00091055401410078040042c10340c1c0c6030311040d402014550100c040280c0d011025140d001d00d9042888103050042051520565200d64034034001038000758001364585403180011007a541c0c0485a1062400c080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 311246079 1250 311244829 311244839
    0x3070c0510020a031b060e120301150c050c01121e091209120311030d0204080f06181504080903060c040303020f19060507020a05061005040506030601080618031306090303021009051903030b0901 85
    0x200441c10385400a014400480b0201c200f1510711241741001841a0000b503c2e12881d03502034a004005212090000f03e8000c2800d804103803000c002074784005215171260044414011140042040018980303000300d44070741800403c28424003030180c014100104040c1d540c4c514402401903441b8011103000a40d41c2d182d6075080c071aa01ca02d86400202c07503000c0c0a01188003800840c045d100c0701e81055016080f0b20100301140d541c517010040c4103590501d0700300301d49d0040342d41c1402001d10882e101e0094a4a41e821070030b00174a403004010340300d019a1300c00302c600c0140c81e01405a416140381d02c100045050341e1a9101281000c2400c0001801d51160406101d000500b020b283c4040d0f07030042c0c0742000355513540c1e41055543c407428403803a0141d42100c400f1038008648600d05422000064040324074000603000100c028030340030383c40700300012860315040c81095410b0102d003c0300e60040c0410710640c42d1580781c00b0380b200044040da202c0300c5007101e1082c0c01c050080c0c220100320800103280501a613950 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 311247329 1250 311246079 311246113
    0x270c04030f0b1f03020f1504080d050c0d0207081f150314010b0f180402030a0f15050a05390c0109060c1107050d1403070c0510020a031b060e 62
    0xb80c0b1080792500704445003421808640f90f0034412030703070014514280101d040c001e002c02030b4454010039007864820000407030001c03810000821406280d5a80c50394651182100c20305000000d40804115040140c040010450009011340403403880d9103ca51180680c03004440200341180034024070301c109007800818020550403035080c01d10150028412800e0341010403500d202e40600c01d580c06007400011010100a4500140e403043c030150840e045960651180c002d40380551100311980c80749240c503400802d520f4080c07a50410640c150500c403a0509000340003901c8400b02c070805040642306131803811028421171010042c21240308031a601c81070300311014080e000c3d942023510f07010b06101a1203680e500c14800070414281c1600903161481c1000200484400d0402042d44c09544607003c101c00c0f00800d00060400074804e60007001440d141005002010541d0801071042d50040c1c1c190801290b080310104030049020225842c45100c1803030101c00402d128050400d480c41444881d0100c1921 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 311248579 1250 311247329 311247331
    0xc0b0702100605100206040b0912030f04020307123903050c040509150408030415021204110604060f0e032409010b15040312120e0c0906270c04030f0b 66
    0x8911001d02c5907580764014021504030494900300180d1122000401017609000c0d442e4002142c0c00075100c00c40041c031140740b46034009464600070f81c13003540240001c42c902003109200030524407a107503112001780d484040d0700221900c800703c03485441d521442070307110303543c4030766100e0300c0ca204801890b00f522401c000d075030350310100e400c2802240b401c4081003035070000041800749a5a800f03182c584070b6171181d48000e4240c00181c01115202e075844001d00c010041d5002412400c10144001105444c0600303110250181d0384510b580124000c010900085070300c01d40641001080342001d400000d02c820100303181152548281004c840d9201c00e004d440b00454043d00e00030341c0321000a0103881e058404200e90a481010421041c2d0410002000081c42250400320500480d080c0700603600c5545914001740e5201c00c0141400d40c00050701c088040c079103080d030369400200541d0006400c0541003982a185040c0d05240700c03680e0403140c00115208192003c8901840c0e124889590900661400e80c401c000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 311249829 1250 311248579 311248603
    0x1e0e040e03210c04060c0606030605010b09100f0e01110c03030433021b0d0b0c040f0b0f070308180d090e090102072d080315030c010807020d0f0c0b0702 67
    0x1c042d14a20103101a6030501d5000307140d006401c9141a1400c80305031009940d4090441e900781e11400000086140c81c4a064002d042d42d140741543c030b01d052410461075102c40b042601c00d0018050140c407030f003980685a143c1c0e0070801e08028050042c0214003e00e0701510044440e40b40c800003c01041c102040120a01d20b80c050212480c550503400c0c640000b011411801040140d0018800c1758103250110b81140c016070002d85101101145516541c200c0301c811188002c0680000404000e411402c42c80c0c0c500034031500700000d0420903a0208901c0b184a81300001c3c040044400210742c0344084c5480140e50b0411300000c03540003e41c0e8800c0500f80b5421031041d0b05602d40c00100052913810180220389240e5408200300d86c86101c82002205e010b5180e60521903000183c0c4c160b1000108808011409100310300030082480107201c00b0549021240100a0f04000003d0248a54107400042420b00c10b43c1c81e06000010008415088031015401440a4410035103201170007465034020803400c2d4096 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 311251079 1250 311249829 311249857
    0xb06041814061008041511030406090302060109090317090f15040524190e0313030501050c0712030f1e0506130606050f090a080102190912031e0e040e03 67
    0x1d942c03202041001207a654044011903101c00000300022a00c410308540d5034913103080029402c0d12884281140e800880341203032070365500c80303140e028103404001e0b840c014005c0440501000c862664003c01c8044420010740005640c2c1c40070481424062001c1041f01c0f280100702c4400c2483e0442410040e0001c1c0c07015103140c00303001c1500d510300c0924888200c082c5240c1e8040c920756110271581000700a07421071441600307691584400354180d030500041151444446403080c61604604009084860180055181400410541c1d00180c000f00540c0da480c03100b0b040020311039801c07454080143c4a68110704c0740070f10301585203c03540e898075844180501d04c181c84101401c075407401901c044031b074a80203038004200180308940a10380000020003a500c009000e40d003030103544090f41400e90f0000c5680c3c00d17041c8030002880300c0c815804888103005100302512070007448116280034000800908080084509403004003405500a03180740138481c0c0044d0040203609040a00591aa04001880001d00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 311252329 1250 311251079 311251081
    0x2130912200106061d0121060306050a0209030a33060305150601120b01090e01081c0f080f130f0503210123130e0606040b030303190b06041814 63
    0x900d070144100810384502e40c07500000c0000c001100ca002005c408a0a8100140125030110031201c1d03094841e41c1d640700d81d401060680c158038110b82500e60052000b070050b413050003145c2c140e64001031000c1e003058110200105031150300e9526240d940118100125050362003201420f81c3c1040d81c00641283e00031401d44501c0c0010186522100c3e80a03070b400e07800111182590920349820b40c0c49011210130504000441e25a00c0c07800001c040b0090f030080c00250002d020014100c200d2001200c0260f215181034080e01c0401100584100c1001c0d009441c2c0c040c190001402203030b0041182c3c100e032074124244141c0082546000396480d4010480500d200c110910000c9118030b103030f080c2ca416140003140e9400b4030700c801c400034041d00c071010000c6940202101e03d0240359004074829503820b40490400303041d0300d02d802e0040c0016903560441d0303103029510802c2001355030347ea000d120b041d0754601c0d1480403500f09844030000d00c040c01141c002d180c0304038030548550051405a8002450240180d81c45021 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 311253579 1250 311252329 311252387
    0x20a030e01180b0f07051c110f030d050a180c05010905060408060f040f0c0306051f03050c040b060c191109040201050a0c0f0b040302061017030702130912 68
    0xb4070410700c01c9940c014800c142d060007030b0826000942080c03050506104d04081107901d41601e03012042d1490000a0700ea14510001198441860491111b03082d00500b100a41090340d6556031191503020100b03140e58902041809080d90405025103180c00409220200903081a030481c41c02841a1070114401d0840003d441c1440c0b800d0303c0441d0110b201a1800e0343d102480c0a1100f070000300100e50300204070748072100141c842c40098001d103015100010360303858183d050180c030080c21030344001d210b08886030401c00540c00086000000901391800b242c070700c4c014004100c031380c001c95078500301da401010f6494100c4400b050590f02490b000795140b1400d09012014420f480c4800c1d03c0c003a0019a0030042d090100740160b22051186104001c1588652819203410300b600a060346d04074016080345080c084500d0740011030f2400b501004048000c1c0319200080e0555078130030b07020000e0203800307040300200403900d080d44041301064028006c0d032035080114200600d04000c00440f20790403a20040b00b030311 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 311254829 1250 311253579 311253587
    0x10606020d02070317091c060f05060d02011805130b0102100905030f160c0f08150105030705011101021308030306030d0c0803010902030a0e0703110109140f060a090b0703020a030e01 80
    0x103040714107900a0900305045403141000e840c00c410314801c07031130700402c9010f400741c603030445100118040c0034410024041c40d181c100141d40030403c41c00d0383d5504110074031816541f29140120700f5a4242045440c000c2128020000d0300b8903a480280d1000d0b0030b1140d0003e80c043da41140b00d11490990a4800043c030526100c130894960420203000c650003841521b0b100c90420006050041c0d00403001d082401d00c43c2d8801c5c80a251030b4109804110600c041082140340c208200c0c807020100b108024030960603c8042a5139001a00c40d0074104052440000c058070000e41c1100c2004404580b00551542c0303400c0007070381d0380d4810344849000f403241a8451418a208031008514564420701e207034656441e0501c2d04010390030140c030600c2c2460b03403990840441c940800440d030046200b15500c100c001c03280e40002d000c15115030300c4142c4440c840c0e1003000300303a030303580280d011052000c65403107895800b100e00c115480300301a00300c440d5101001884c0c0c002d03d5000035900b50038a1007a55141408402d51004403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 311256079 1250 311254829 311254843
    0x1518022d180403050306060705010c0507060522030516050f06060a0501050a021914031c050c0403030e041d0f071a0901020c040b04151d010902040e150102010b0604061101060602 78
    0x780d0121100408074000a104000540d040640100346a04244050b100c20b0b00315060801118045103001031410b0403c895401102e178850560354040e102c1d01d204021501140a034440024100240054201400c0180c01c10b00505242c02904445001c1c0c1c942c03045a580d05419213510f0322400756540300107841e612960440300404000d90181c4240d4420b00c0e190000b200760380b10212000c494010440002d80410005040c00300c1c1d00704225120481c0d124615800c80d080a001c0701c01d00d60f0304100c03d1000ca50000e94031070211806507000100c00d0a00c2100d81d481d05613070140c0d581c0f2401119000944d840c4001800c43c107640056281424010314814407501a02ca40d125103801758200746000b042c9460103a0145500c0c0402500221f100031500340301d04e282403070030327082040f0710303898520f003064840c0c0390756922409040502000c6240c142424400615584020164074041d95803542004280c0d200790445140c02d00d014181070703183c03a01d03a003016100e0010084860025880c003000041e841d840003d00d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 311257329 1250 311256079 311256109
    0x70c05130b030d1b06090605070e030102090d0f0c0b0a02030301082b051c110a09080604051e010204050d060b09060a0e0106050f09060c0106211518022d 67
    0xe20f10040d055100751352902d003d2080c5920040c0104183c1c012500b0350081017102032241c0c50008003890032030805050789001c0b80d4201c0c081d070b20601c03022a681c0c4401814a5419402c60481d2007480098074101c1c2900a0580149421441c0456401d000940020103941690041400e482651302c404c55103100e20381c0d8000c061080b203011001c030303110018000e000810311821080c1041111422064061f029504140540079102d14006541030003d5400a11603016014a802800c442d003410384070031369201d010b4201500f05170f2254030503100044096040b5001408080c280d003204810a042c504010002030201900a12160300055100d103082c21100b4292106600110041d03401e010b412a0503810032403e0005c10041000f50350030640d80c6a0180070084034810011401504040e031080c1010f4030340c044503004a0a0310010b0b000a40308038244940c60b4005000000c1005042c6121441030310360000183d0440421091103101c00130700e03441d0005985d201c52924480d510044184020164a8204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 311258579 1250 311257329 311257333
    0x30d27020d0303020d0209030d020c010e090f07141c090201120507120209180903030103062910030204030f2f090402060919060c0b0a0209060d0b0411070c05130b03 72
    0x8910010f80240e0140041c460128001410100c03110b010070702d05052000c061015901c0704042d05c0503580e009010f15100402a2114042c0d410100014003140502610650074400c0052042c1007060f40d8006580314031200c4a24800310300c0204040c0001006000382c264001074500007040e20641c46030240d140179039010790f980c0e8032965180f100744000350403001050341c6c07060320310008020700c60820f18080c1c00f4503c0304000c0d6a072940f4501c1d100d0200e502d464007042005500c020351451003c3c280030040b84101c41035860221140c08148101c1c000d20894000400000800e44298107000d500f0702c8403140000b109403514004c0343c1045001154443e01c40031a030f44503810311300150042c240503010740350622000c0e0043d800304110070b40d4400200000d130070010001d6400e071b0302002845105984240c01180c07000c2c0842c94801080041440761040c2c00c040142c1c00c2d1a45480011619154815883c042e107800e203294442056240c420b0001859200b141c1c480c5007070a18180c011856446403200308440140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 311259829 1250 311258579 311258599
    0x14011202060a120209040f050a240b0703090b0316120203220507030c060c11010e010801030b1f06170c0301060e0d05120708091206100b090d05030d2702 67
    0x400f1a2a402c48546502c01c2940910a01c0c03082d4403180140241c81040083c003041c01d10704000070204031100745040405104121101c240c1b4100b417016941c0680341c503102c01d950f450710503080c00c2d15102810342c480c425402d0000200007007083c10901401495400d41c0d2024500544e41c421070081c1d010036101d50508500e800c038080d0b41c05041a41a80c6450f2041d820745544507620b807030781041103640e41d106c900800d1a0001400400c441003520403070f40c480074200601e00c1100307280020038003101408002c25010840011401402076144c200d0b81445001031451031442d280d05c801819008a0034104240f0b15000001c600340000b42d80c19a8160f9010f903503030303000c0040d0160030032043d02c0000f00c05840c60b000e03210001c0110b41c2c51038000c14055001e44900c5a99001d0501440b80204112400000c9a0030000030302c0300c0905140c04117411140105103441c2c927024900c00142400003100c0009100e44000980000703c4505e0b40c000001c0740c41003440811010031000b141d642d1802543c03030300030b5101644c14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 311261079 1250 311259829 311259847
    0xb1b0a050717030a0b1c050307020616171b07050f04150902070c050a06020f120c15040b01031103030f090910050d0c1a0a0206011202010e0307091401120206 69
    0xd0140155034040c07040810382c28003a4600a03240c1c0c0c03051340d49500540e00d03010114050305010581910030030305810071600a0b116a1100703070303c0b8003d05500030301c100000901132810400e001d25002510390000e80340b040d0301001d11001c1440b64815080014505101c11078500b6048000c5041c1c0d0841c0c0c400b0b0451f51321a10301c1e508000003090241c0391b4045a850302c0c100800c89850503c0034180c00d0b1711403c6403030342ca142414208008100a58041800c540c40300001d0340b074407400858400b403c8640100c0c0c064484446503035180c18a2107001411501404030010403040c0880103d0440c103ea002c0c4901c0060528403800b4141c032445840345c400d4050900300401030782d5040c0020500d41c04052150503030f003a540c0b134a0028440c468800e600395034180740d210041c08070200c03030104402c100380300c0b441c0c5507d0300c613000c0c0c0040c2d2141c4051044034500f5607103448100969004075408030b80400c004080e40d1403035442e10710031401000c4003c0c450380328250700c4001152800743c0e11034843e00c40b60024aa80d0a12200d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 311262329 1250 311261079 311261087
    0x10b0d0507030b040611032d01051c151404060513030906111614030111030121020402070819020d1b0b060a080d050405010216030804030b151305040b1b0a 68
    0x2c1d000b100d0046d910f0191b204080d01070000741d4000c00d42c2a01500c40c2e031008022910746800c44440303411240741c0311300041015a03200b20302ca00c40100d1400c0803058000480c24403450307a0040002480c109402c0101c003c1070390301852030113489948a401300704100e4803144125000051321860043c00f290388200140716203802030800d16200e0400364101e4006101c26104041040c1060780440f0000d00c14600060181c5000e0042201e140d043c18901400e540c503242120b0400038101409a840c0703c1c08041100a54543e501142c1c98142c0090116a482d1403c80d848814442d03420788000050254142d0300049a104410340c003014007610400f000900d0454940102d8660003a1480703500600e040c1d400a03200e8414020f1025a9206448082e241c030314180c0061305011509000302003403541c3d03000c11300c0005c03480c809480c20f994221084042503a10120403010030301803000b02c1544066120642c0900c004160006d6104a111740e01c10000c41d1950f088404d0b8110850400024205c400d0001808040c41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 311263579 1250 311262329 311262331
    0x319061d010b160215030708070e01020c10121d0607020105090604060b03011b030213240f090e0112060e150412140706020a02060603160501050d02091809010b0d0507030b 75
    0x20380b9000c8841041e144e80007a41c4c4080801689030030080200c200000b06400885550f03118a25040803800070881c0300001b034881070380083c07051080702d1001307011201d40c3c422101c0306983d0682c03400800c8540e024070660000c2d1000341ca4186550702c502c200281e1010702c180680c500695001006080507196a0754800240900740700e40d54040d9640c08402c0030394020060801d11020550b2401a50392480d4292044408515041400852207400032018070043c0d04103030800c1a921450704c0441e610780e09008450b011065804460510350310000401e10003180c00c005480ea51154404020410b40b070b141880d1110881c001002001c0642030014000c07501d08140d080e502080713840c00d220603c002050202c2d80750031140342524090750210b07001e030483e6010046160800001c80c02015010748490f804000e02d003103409218108000403510489001c0c1d80d805444844100030490040c200f03a9004800351944125041140c9600740703200b400d2036040140700203032401d4125000e0425107045d9100d500e12800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 311264829 1250 311263579 311263597
    0x170a050408090913021906080f1506030702031c0c0e0d0c08030d05100501020303130602090d0c0303080910230903091c05060105100f1101060b0319061d010b 69
    0x441009403100c10fa907400d2502e0b11400c002e0207010000d9207680107100d0303003da10784081c1c070702c0d00d84100d0107000c0c21b82c02c159415800103c0c2c09114a40da44c4440020354550004010340d0b41064021042c003a03060340120180c40305008065a541000d0a01c2d600e40d0217039081074001401040f10b020710b1045c00d0610840b090314460090725600c00c655640c0c2485407031a48825581c0090716581d9040c407403450320340e40304480240713000d200440c114200302c405040d01c80c0660f1401400700d0390019001006440d0354803030141140e08003800f00642da40d40c0c180908942c0d011201d54460f0f001e0702d0960241143c007442008040d01c05044101c10085103903101501c9081e01801d541c68502c030500c000480c03a03a500078000444016080c2c1040c000b001d5282007407a001060300100e1080301384001500855502260b21000c0301030616040382c0b010401070a65004104503000000340d00000002c22075071801c2c14500e0030b40454444400c2043c6548d400f2685525400410520010440b110040001070044409000e0100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 311266079 1250 311264829 311264843
    0x102010b0303030c0c071205060c07051603030305040614150409051009060b010f020d0516021305010b0901200706030506130c020606100e030a12050c03040807080706170a0504 77
    0x9150300c40028a10b401c2120400d4101c800010b11403000881803145100622911424100e410101e656054903810018400030390302d240400e164090000c10015156a02e130301c3c10705296030035102e003401005000120b8041e516241050700704440c02d04100c1070148251448080c00c140d42131408200b1001e442115400c0ea5140305101c003020004444d4403d101480388036400c0050f01c0300c41e9900140911245060082c29500300c08a808d40c140d410008898540c038860b030454440c03a6052000481942d0005074004500303150000105240004900034210303103409032104080c030182c504d810340c60401c02130202c25468000107410070203d4080c3e000aa000303000100821008036034000c60300111000ca54501005a000c00188080c9041c041c10301000c3e03010f02c1c985144840120408070b03070b4451010400405450f8401060100d80f8450000d0700c800c62040b00549503641d50b074001503541c4405034040c00440d0b0040843c0040c0e41360103504405406030a100d20100d00780c1d5107000034002000000d000340c403a8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 311267329 1250 311266079 311266091
    0x50c091b13090e0d0507170705030d05071b02011e0309080f0a030b06030105060a1d0a060306030c05040c0801180209090406050403090b09030c061b0a0b0403030e070b04060e010201 79
    0x34000050251125003044006442442d181003280000c0d10340a140401c0a0342050b880c20181550010807a800a40c0003081108481c1d1030180c024198840c1d8400900030f800301087c86800701449030090ba000d07260503512010360081d0100010480722108400902160309110b1117050541d510885500c450881c1c1000035004150b41c85600e0a036000e1007105c0c800510003d080090181c142c8126502043c0540d069402d43d1f0400000c5080b42c07281040080510036040c0c288810f01d001e4030070a00385c110b0082c0c40120803658543c0064060440350204a0b141418801d001c1000e00389481401d282c4c4c202d90740d03440d03010b034a806200711110084070010210b0308d0b002c20072200c5039250025102c1c0105d1213030300001418906407c0080180d06560041c9203007010401041381d0395580001c242a8100d0304880c403030703604c519410494000d202030501c0c405040c040c85082e4030520119189480c4903a0182c0c030140100c03000d482c030071521768441c0d00502d19988400d00040c81258440c00c2e07182c10702070060000041c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 311268579 1250 311267329 311267371
    0x12230d0e0d081315020d0917070506131412152e090f060b03070e0f040e060f070504060c081c0509010c1206050604050402031e0708041a04050c09 64
    0x40358010444202069000102040f104c1c1200b952441c0312000e62014002810200100811002c0c46105082804005107001e408a4005107c20001000010320544c0c2e0f4501990b800e002142d1076208100c5441c1c0e0003800264281002402410a0003001c40604032000303054100a050034009041074112940341070f1412100801c3c03100c2038012a400c1c804000c0d800b86880402130540e241000103110644c1040c008102074034607002541c0e008401801c0c41c1d206051180045540070720003048585e442424648284041c00c004604603008030b104541d004880e6690280030b4a417449944950fa000580002c258400301340c200c4042e0480864a034640951850b030115188145d4009952044003655558006c59080d82c100b203403000e0404040d03030280700b03013454000000c00600480c41a140515000000100c680c500c0170b074038851070090380b65010201d0801c1314008160301c1c8100c800f1a00c40d07044030302020b00b03003c044010600c2594490003c05074583c0c1c800500490350307405042900c0c1040c0169030382d01c1e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 311269829 1250 311268579 311268593
    0x9090c1c05040f210903030e04020903030f04080c09041101121805070e0108010c081b0c07060302040303140f1902030408070803030402040c030209030304030303020c031312230d0e0d 80
    0x3004901036100d00c41d110140d801d0030124074400752845213404ca00c0e2208401da4603009140101100c3d0107042a444040d802c0317000c500607106100c001d5616001c00551a40301d0b0f40480040c1043d100400122072881504206026500c002580c001d0052515144810550343c032842c08000001c0004001103041100b82101070b168007000401141c07103411005040c0035080d408050b2500510301340340280b0600211030f00103802810003030b280250750190700c1080340c41d840f4400102da40050a18080300c9c54076075030b039000400a40090004800107210a82c60644030b0501c41c0c141c1d040301d04040e410301c3c0390186903250344c0380c21218143c110707083d80401d010003d071014040c0b0030080106030b518042d5550349450f00c100011501c40000990505105011030a11910f00200f51400e60764181001640c0768806011640395004015803000c41c000e0410700030515410740c500209040e80304107000b01740d0100808140c40140c5001c0000221030340400490800c8900c50101203c8111024001040c41ca4994959075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 311271079 1250 311269829 311269831
    0x2103020409020414040e01051603050c0403170a0806010e0603070e0d06050108010f140f18101a010e0d020312070f0602160c08010507120207032007050109090209090c1c05 75
    0x50301c1c0c42c0e641c00051301c0c182081c1c003d14031403100c1d02c0300070040351900d284030482e401c1c420030800c8101556100000c1c4000210307c100d40145800242041564540096416040e442107a150b00080e080c00d01107000381d4000c0b40f0455104034003c110504603a42d509040794011071000402d80c0c00318201c200c40300840c40c5841380f180601510300010030456071151640d425078a0100a150010520b8003c110401c15039080d07294101740e008c51414081da0b0b80b003500e01d140102440c03855000e60b01c0d010081d003000c02d141d003d01c407203400c0a0b04d40e440288008010094200401c0310040d4041c0c00c4080f44003c08100350004141d101e101e000d86419101103034403000704a8020920880d0000e01c2d01046c00300b40105140c946000b044004000e00c400e10303000e10010003000841e00001800c68002c81d50340d0405004200e0045085001810300041c59003030700c021987d0340d40c0d6118103408141400d9010030800458000c41c0d5010340d000d400d480e80c903250f21070b4031501c96224801c51141e40b011800e42d5600044d01d4003901d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 311272329 1250 311271079 311271089
    0x1508040b0415020d060f0f0b07080f09010203070c090506100c120f050c0102030a0213050d080d0b0105070615051f050414010c1e0203060703021804051b07082521030204090204 77
    0x15802c040c1400e040c0005807c2130b030400740e03000800388641c074000781c0f000701100c10f203c00c0d486071103444a030a030b00141d166004041000f03111400d40d0802282130781099110f11b100d0300b03049a580000c1d0791620006d8407560b4642802a022807000444003030340301d000c1e95203040c0074812403034058900703007c081031942241c00a4440c0440785400244021401c00101c020318007074503003103c003d400044250f0300d10806204080720038141039280c0101451301c0c1e000e101910903094000d1014460a609440112922030f0280680f030302c00d0b03491f0703a903561a4284608020000c1221525002e14141c100420310300d048441d085001c1c10031000c104d108001980340005c6070302d0b400e5000c00b48010501248101801c0140090a01041520601400b4960400d40c0101070b40c90100ba1000141d03519032205058440005464101102074000307005410005440018104d00005212006001c2c5152a100c1240786003004044c043e100e0a6811106200c01501803524009060600601d8a030340d88061800f0b0780c01c03642c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 311273579 1250 311272329 311272349
    0x4050307090b0901051225050402030c0918010518040501110f0a0318150504050f060c090a0f050a0308030a020405040606090501180303081b07150203011508040b0415020d06 76
    0x8001c0d903e0408080160240000721018116095074151a82c1da030b4580790000c075854030420920306144600352850703c02500303001d40255603174a8400040c01c0300d50300440e44035000e5070703412003030100721a007041e180750595400400910450101c04541442000064810b680139580c42c00790810906180c03000300700b04003811030020744420300c500c6d0280c1200d09450382915030300e541707455a6000035151000d01d00042c5801c0300001e041d071640c4c01d1561408a00500c100018400c1078144000c090845000c3d140f00d10b000c4501c1c428076501d80d003c4006202181c030403c0e41049035035070148006034240c0c000d154030441156005041c0350707840001505452071030344028042241550b052005507800340603246090000c003507060f0003601e165001401c07100b0003042d5004040100d1410031021008108441000c0d0304140300c01d1303501c421441240002e500a100381101c1d1060401d803004064019814a8851900b06520b0042a03841e03841e0601400000d0941070304e41c036401c2200000e803081382d1159001404001e10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 311274829 1250 311273579 311273591
    0x190c050d180c09020408030d090f0f0b0a0b04020c030702060901021908030a06450501090f0c08010806060103090606080f160602010e10020c031c0b010311030c03040b04020102030405030709 83
    0x3049800300390b0a42042c8102ca004100602c40b4400006c11254644801d00e000648803040b420034102d51800d14100808032680a4030400a010620001c10700400000c04200101030f40031040008900c1402d0a5151940050220001515000024005d1414180181d4841d02c1128041880560003a0320031145000c0c08820300c8582413083c030070030018000c1104140c1e02c80b4042c5040361036441d540080365410420011250401006e403445c1076181100582c414082540c550304d41c140581540001c01040c2c608c0c1a41c100021449510751904840c0c252001d041d2507202e160044018104101003981e8040c2c86000025482100708070481c12206000041d0080c0c0c4030160b400b81c4411565031101c01160305080802c0443ca101084030340d100c0c002c4d02c4d0010780d0350410010703442c11401500e580304070200c200c2880f040040c0803a04500803001d405da0301004648500702da0f0003c50300007a03074040341c694014000200002c001d002a2900a801401120300b06540e41c000a40340c48216000042c0407a10b0788 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 311276079 1250 311274829 311274833
    0x305060709052101110d02030108010e07050114090a170a050f060601051614190c0b03071209060f05070905030f0705060715060f031a0a05190c050d18 66
    0x20061540025007454645641894100042c250580032403c0807101140342540505150096204080d15208910616101e21541c0000342c001d42003403040041c42e50915100f0901c020380424040c090310016100c045241001d508001c445821001d00d00b504103030302c00c1010800c10000200034400c004400000c041c01c04050ad08141085010381c1e00b000c01c0d41c084010301c0681d83c0c101c410f0340d01181c1d103958200780c068014101811100382d5004c24801c03e0080c1c4036950360803400c4104440b400390049810f051110b513a802c401d403035840200d50040000d10b07078543d241b6120034560040780d0340c280601c8011445080003201042201c805443c15008295034400c00c000300e00302400307829240e0b4a081d01800c0c2252404d80850024811840300903d504003883e000c40000b08641d00102c00b500b900c0801210f17154491801c865003404603014488561181c9000402690b401d010f5a803107401d0400e540c0414100d40c14541d4003a0842e8418602480340c140807003aa000500d00c00c0201c11103040c1080c1646028074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 311277329 1250 311276079 311276083
    0x40501030b04060f060e030307120f08180303011703120a051005060c0d030914030a08012115020c010209040e07091b05030112081c0e060106090609140f090405070305 73
    0x9114040c00b0700e041c41010480b42c040150443c0845503681010090580e468000a04501c06e00c80020680a41f0a0b80c410b82181d00800380d400360300b140d4585500c80c1c0c6580c0302c400103015258140760001d0780100b00601552491030204c0303da114022048034100181c8552600c81d80d8421501d03007155a42d00c03030030000f801d013190075408020a000e86d05c11f8039240c1009489034443c05005803040038144c556100808204451003e507880d6444402500d80310820404000c0094100b0311408490703112003003034641e60745034100c000c610095006100c41c10880c14802480041d4010b403560005a550034010903009403640d01032001580c03810000360094a0900c0c581d441110604450842c051405401c0582040d4101e01102c2c1500c80d110181400d003021841c0c01d606501c40d0701d110780120f0004103210505182c06030459041405a00c042c2d940c1e580e20340104807503021031845400700140d40b0500c104909074800c4060f68142c0006410006640c00d80c40c081504c086081d10101ca01d5030100304200140300003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 311278579 1250 311277329 311277341
    0x34020c010e120613140f01020306040614011710080d0c050d1b0f080715021b1204090e030405041107060501050108040b15010c0b09010e100e0d051b01020f04050103 72
    0xc220364444030400500b0245030303a036100512040f00c100c02013130100244482d0080c040c03000141c0c9012a10701880c007001813030203500155445c501640c1081004602c0c020134801c2e82c240030106a50340c4000d5992841420800703030000c0c1012100912048001c01d900d0780501c03100c440c41c0ca4989824241016510b4034600e40b1043c1c20054040040071500350744c060004800c0074003510780012200000b00d0660501004070f10926900030061885500003181090711500540070b0100c00c8292243e0008205100e40c0d00da00e031b17192092054241c108018481c0e04026800340c841242800212030400e0780b00c40108040390700000c0130076148440400c180003002268081d06015010070718003101d80703080c03e0340c603240c0700c80c80074001e0100b0119985108201741d00c200360980c0055042000c4028504203258074a00905600100c04460f02500c43c1070304040741240210b000c04103401004003034003d041e044c21035a40c3c10070650311114a440c00940c940c4107800340082c2222a901011040c0d555203030000140440718 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 311279829 1250 311278579 311278607
    0x1e0302060f01060804140c090a0605040b01030507021f0b060a050c0601090603200d06050f010f0801140a0c09080307211701050402030601050c0a060b041103010e34020c01 75
    0x500000140030f1113034802c5155070040c3d400360703a103541d6503c140b040508000c14920340036040001134081001045c859040002200d80540b0100816400f1100460599404031900300240e0310810714001040b00b06c418060034102160700c0061143c0c84040010f04642c400005000005c0001c42c0c10241074806021107030040500500c1049a41e00d50381d141715154400b2079a441c0800031844140d005034444803021313160981d00900c01c00092a0040c034503c004da000303000e0381d0340f05c08a18002040702c040c144a072151050b480b5942d00c0540eaa602e9145000c1c2060645101c100656404000b0b00d614007003000e000c406101d8490000d8003003d241d0000150001150f040042240356082101c441d031030b0000150568009403030150341e030341e10350005075034030303c20004803407003038407800f01c0238402d021455124038101c43e0b003203800703210f03403c910150b0100c2404280115000c00850340c011030311050800c0741140c104180d14030320721882640300400e40007445441e804900540c012442001c1d49603840103c500d0036032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 311281079 1250 311279829 311279851
    0x7022e08040f080a050f03070314010602031314040603050d0906030c0f1e03150603050109050709030c060c0203100612120203040f0b0918100e0f040222091e030206 72
    0x1c40c050b00d6040d11101c44420141c118580000c284884038801d9044460f00c2c03840b103007042d0340e0f41801c9400070002e05e1180300801c1035030018000402c410784044215070152000109102c2c045050025600c8129034441d446c90b07106907104000000030340184441c4001003059101c04521500d0610701805032081c10000400700119880d0340c12005410114802d050041007030711520142c0c0c0040103400030440411413400e204401400020300c25030503040b25069424260f0180079076151705000342c5111410340002000198180c1c814800d0300d100301041080140001d04442c0700c44c80302c50f50741e0200c03002034100c6602c0a10410000d400c2c08110402c0c0025000c8a10041d4602441c0c105542511017050043e640c1c6480001241842c6036241400011125180316500240e0304013440800308042d17075440b0319005542c001002852103143c011156200c0c070f4020b00301448440c100c00c0551038021031903403072400903a51034103004080740041c01da4900c50f0011902c40324040c916400e01038941503000b01400c141c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 311282329 1250 311281079 311281081
    0x60e0106110f0604120f0c051c12090c05090406090209191b0203190903051e101406040504020409050f0c0111061026010507181410120207022e08 64
    0x14003041c805c4260a500d17240c240004d0071001000c0b00c9002034580098107500c50444091000402c50340c0002d00c440c030a807a4181200800000c0000341c81c2c60410251070640107402c204900d0030113030600c95100c0e00c43d8400046104003540041c900010560311041490300101d1100300e070542f1071003001e12140041c411216129042c2000950b13a00c640900c1041c51441c4440d2000c240d4060075019001d035074400c0940d0300380d050040030340e00d1950004040107114410300e814400d5010a0b48900d62545035607000807103440d60761000748006010060f0040b41c10980e5680c08001241c418010520344d04400e02c058100d28000e03200040640a00c401d00350283d40100d01407202c2039000c001d480c412108500015102d2030074035034455101c15942421103040b9401c1c10104001264000141400c01d208800b11196880c3c0340c403d00040e4007050039015070000410b102e460b0009024030b2002c0d8001d0410000949021203076404210090b040c004c1452400300030520340712030980c0c440d650001500c001d02e02001d003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 311283579 1250 311282329 311282333
    0x1603020a020117060a0b09010903170315090709090b2d0108060418060908071a0601091715180109030801141f0309020d0204060803090a091a01050904060e0106110f0604 74
    0x1545034511821b0b000800c00a56810140d0044c52810001c6030441c41032001840115180b08880d8411200701241c0000104108032528200500600405090340c5011006082c020b80030300501c01c1e00710305c5034400c07110400c004110781c1c01c81c1c0d20166800b8507240180304240e40d00014240c6100900007601c114200260b00c42840d0420000c59681d13908880d01180c2d0003640c0c03e2041c0103208409010b0280f600b0740d69104941079682014034000c900c282c0e40d42050329524020003141e40700307290401610350011082c0382c007002000300c14103402001810300100c41000c9581e40c6421201c078180708802052000d001000f4040744d00740855680c01041d6008581074081400d8080042c2d101142d550905030345980c1d440035900c03100c5440341c07142e034090304c10409d643c0c40f010130131354a8002e407614520031404510701142810860040c00701d28040ea00c842c0154402e08001034640b074001001880c2c100e9070711500000c2d02da2003480150700921403030316258410540203000da403c010560a041c4503941c0040300f8080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 311284829 1250 311283579 311283589
    0xc03020705090108030702010c2303030405060f060603070305090717070609052403041403030103030309050607030c0e01110f0303010905090f19030c0212060a0e0c0108151002031603020a02011706 86
    0x7540c61f41c24640660b060780c0d2807814401c001074816002c9483c0d08080785445080e000040158080c5015808541c4280e403040c3c900394500c074040712a2030300464244086a460350107500116001154641592800c980f541d041620b00c0d641c00d41c499805078000c8000308611908132840c034016020545d903a0103142c90725a01100742107410310041e0219280000042c0a200c5510340c525030640341d05007038a6880d603590070000d016114101003600c06001710030228003000c0c000e2050078070103641a29110b03520740000005403000314400e0030042c3c050041d55068814650248000c6000e4050602d00140c0750405540c02e5183c01250702d0442c003590320070301c41143d9000c500c0448900e810380c1031820301500c0c1020720100310000d41d035006034101d602c624810b0050041e842c0c1c21243c104030b40c00c0119210010088011640707010241d5205e541009501e4100c00142080b2540c604101021700440b45456950f5000c0060013007401016001a00304a1131413003150392103c014030104486402641c281c0c20800d00280c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 311286079 1250 311284829 311284837
    0x9140402090408030603031e0a030c050c060f060d1505090d020a03080f040206040909050d111501120606050a0b0c0d0f0f030b1311040f08070303020d050d0603120c0302070509010803 80
    0x908070283c04800240141c0d8108102c450b460b42205070b502408031161681c404607003000031444086401c02080c1450144102b0680d11005251801441e444c2c94040c01e020404c03a0180c5050b070020300c6d024101010920928454809844e11f0000065070700d008080342c0d00b025007208900342107402007030342203003c40c0d8804139060700001030700f90250140c2c65900c00507205218683c0310f47c51042c01c2000c02c01c144100030800c4070a16005481d410b80800b060401b03592144a505010300000c0e40300740040c803020030507800303114007039100d00d1000441c151504005901007905501110400f400040d180111001c00d214101458000d400d2918400403410406004060300100d404c081554481072890301d0b503980301011a4208440784100a060322550b02c0101030390040c0100402e000c3c7d9480c00080202c400681901240e41544c060702e00c0d4031612000300e52540c4170300180c0000b2078171244040045880c0d07950440d590f88080d140c4104802407440c019052a00651046108018410040007115030200442e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 311287329 1250 311286079 311286083
    0x907050307081b07060e1e01060f031b091b02010c021603020d020a090c0507140a021c0f0c060305180705091602030f0c0a1e150209010302190207091404020904 70
    0xc2100d040a550307101d40c0da0081001c00f900103030421265003501c070030216460b0150071074550040130b0307e54100380d19030a807003040c45003055000c9049410004240701c4205080400080800c1240c050784d2001500159000c840012500030140704500c0301e41a0244158041050326002504031000481000c180c04901440003a009076030800b442d00440d82c07101a07000c0900103103a000c10907a4401e8600034441c0c8c00032801110b03d4256074081c0c419050780090700740780e03455004047c2083c00711070381d2112606440000d01242c0081a81c1d0081c00080c4484c08894060000d070394001503203203041c80f0700060044104840ca075098100784414003050f140d04842e10341c030240e4001e10244600300400c0482c61403140005c0d064051001065202103030070042162882140500d01c52419203000f100801c00016810b00c000700408600c004404200b105600a00030074901410014204680a0520b48610901332120001601302250501489000c1d101d02c1140c881218100030721858a070303010841541d805000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 311288579 1250 311287329 311287351
    0x140310020d140702060106090e101a0d02030c0d11070f030e0f0406080d02120415032d09050f030a0c0602031803040905010815130b151806090705030708 67
    0x2600203980c4a0b8002c09401c0790000c001001c0741c508500029110802806030500103400740c5000580800c0340c0504a0041c00b4080200615524054009903080c006c0155451001e100380081c801e00041ca00c0551310880d2440d084507541d8814003c100200c0d0501d444041240c0c45c14048200405e020480100101d5417500306091044203040000701d06c4008022000d0f4081e007407100c0898660008250102001044e0f000c503003030040300c140c00341002c3c01903000c1e03070b0845010000320310b134100c2c4030b50405002d614444e050841440103400700140c0700c042c428408080c0d01d8440c06074a01300302040140c0c4201080d003901540c02c040300c1040061000080da60050002a0040081174100307803018074520008070900101d07981d841e41c901d5514041e200910500050707000c3c19100300c3d003001021080c244501500c0c1c10031020540030382d482c1c806070400980310384140030084215100780d44910303140e008009104c02c00d2244a01e0042d0800402c04401040c07141044018402d00000c41d410084494200c4030140c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 311289829 1250 311288579 311288587
    0x350d021206040c0522091e11030106140f19030e1b0d1103010b0402030117010b0a060504030221070609031e030e12030c03031003021e13150801020408010b0a14031002 73
    0x10009180c86801103607070b2500d0304001204c0300070b00e241c80c02c0305207c1c0c4d90014413101507540a04e5405000c248103540100f80700802c60340b01c0840810040841c0c108074280030303003041f0700007410800c807240004c280808280c0e54104110110400c1009403040800034540c62152081500451110341540100030110744620340c0d4041256000e40048080e41c001410840d12903039551038150f144003501c0703500c0d411175103040e07050405030808241403c1602c05684982349450f07d56400c0c49040c4603002c4040c41140d00c42e1a020303d0141003032101000a0401c1d64800255504600740701c0b02c1e1018210b5460504d190503091403000940200001c03881c1e9030202c43c1519107008440080303095105000d000052800004104510012450004001e0f81d000751040701e040091486882d00c00e01d40045420361203c0120b031202617542d40d07500b01400050750018062186640c030b909150982e01300740c00c000c074580d45416a100c03040c20300b140c1d034400402901508554900c001400310383c86491549100c0110b0350005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 311291079 1250 311289829 311289877
    0x1031e0606050d050705120604030c080705030706050c040f1e0b070c08070b031b0703120c0905150a0e030d090e0c04030f050c040f09350d021206040c05 67
    0x1500c103500810003d000204a20100e140098803900c0d64060a4801c1c1031429001024580000f05d95100b80d6054940c1080010640c40c0d5000540201d03004480500c42000b1100000f0081e0049038002d1201009581c0c40300c1c10400342d0034040d902e640003542d45802c2c400d42c4000300300e50300c05c14100726419256000d680b0411400d201c04c50010079006041244100b00380001c05c00304000040d40700b120718a280b5204115100501591841443c60241c0028614803014280400750751044000d140039003041c440c00b5030b895012075042505140080b401c041c1c045464031980307821107101c88010f01c0807005000c5001c460700700a0400901c9009480e8124007110004048240c80002c44006d990000031400da600307103a28015a4a4070600001030003141450520000802d0a00640140310742c41052440d5044808048800d180400c40300800152052800b5030114848040181190f003c46100581e480c907804070782c0303000d07003002a140a01032440d00c401500400e40c014107035030070420010f800582040205e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 311292329 1250 311291079 311291081
    0x405040e0a05100c0c0f1a1003120507020f120f0f0109050c03151305030405091801061e090f02040509162604060e072c06040203060a05060d1b09031a01031e06 70
    0x94011f16030700e10039000d001c4d6103034a01050100b26031091031901000d5200007021140c40c003c81000a41016001648680e2487d1460301880c400740190203c407590b184c68020704c2c0c50b00304035942107651030350f440704d0100a11809111003260104290010010200104800324034408014840c42c6c0f40440307081c01a0400c1811300848000f458000c20100444c1444415041c008210745000a040d41c40c02e407000a4803100382010b0380c1010440f85e0400e07406031a000c0014050411406c44041a0b5030801000c9110f5880d86240c40c01703000e0b00c00c0780480d00c01140307030040d02c18005120700959503441c6500030038030b90b070358a0056580680d0000f00410302007d4411410310740040703900a8202118243e43e0020701e203010141c4e4084080120740381c070090b510b40c402440100e00c429110307141c0094400c0d0b0240854148000142503c540903507000821401509078402d0344030105022a000484003941001408940505000003030304402c8d00080a502d55a104803c90081c1c0400840c0c074003000a40744144201 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 311293579 1250 311292329 311292353
    0x150f05091806070801170105060901140607050304030f120e060a2a0303050a0f150b071b0e07030b0105030633030a0b1f08070804080405040e0a05100c0c0f 68
    0x5042102c420741403e6002402d14a42402045e000c0c61421052041c50340c014050540a00c50140140c506a42018001d9903141218644990000c004100d0b10000840800c01007000b14010500d40802d1007081c03a088542c942d0301c5161404000203c4400c00f900d070343e510100c130700070305031420800340c030f00150282c0001620040854007640418201c48000345501070f044148610410002003003581d00c2d05076100100c0d00300502400107083d10000601041d06060000d042490050711503018005e4003959a60802000e03402c454031103000c580c10320100f10f40500030751a050b402402d010303003140f4209000c01e00840d0700d00540718140c0c040203220100300100441500221601007005079032407420484440203015000502402038008072501c0d050101c124942d0100c441c141d580e1045030740c95a200844040c000600151703034060f81080005025500c0c0d20601c1154130704130014043c40b0086090207030404090f02d23403100300702d4106017640610560110345645001ea00400c4010802618180050f010207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 311294829 1250 311293579 311293621
    0x20c010c1505040b160f05040312050f0301030f0c0e0106120f0e1501050a1a040e2d0709090203090c1e04051003050f0714040b240d150f0509 62
    0x80740006000501404000451103248030028440d1005ca084008031210403180640800090b8144000d00006610351850078403008c0b0791030690f060031000108041c1c02d52086e40100c0328080d0580c100001c100c9121301c00001009200a4031902c2d40c507158019007200ca07401840d40485990b2a110040300e0a144c2c800c0b010900c8140c119010f202c004010801c21a90a010b1039200b84110700000803c210700300200092414840c0b04581420f1610050030b101d210050403c0c3c408545c074801c902018048140280a4a05040105d100c10704250202400ba10116081000007600400c00c10180348400212101083c9003550340b0440410703000c80b10a4102140036840ea4420f00309818050b988802c402c401c0e00f602c0c001c0d030030386240038840780b001d942c1d1382c929208806450305812100122443e00303520408508402a010407600002c40c01800300c24003220070010760404000c90020701448203446110201f41582181c042c4450402c0201c092604183c400c40d482201400001400308105c90303040741c10b0031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 311296079 1250 311294829 311294831
    0x280e01030c020f011d010b091335041508011a07020f131e0b010e010c03120c050c0c010306080303040b0c0c0a0c060f0f090e09010627140403020c010c15 67
    0x21004000d1502c00644561048071190300341f00e43c81d100b41c5002075a0721b006500030000c04921990742d40d13850072501c5c0f685405030400c503890920a00708580d901d00d8403a1503040303902c22a58403401c0c20300c2643d00340351404c0c0c0d01c0c1c1005444401406600e000700001112000c0140056490f0314513480024403100300400000d8019001c180440f450794065040001d00c000c3d60700e40001c40c0500320200c1d104640350742d512240094404020342d1415405003400400c820b009140c00f5012000640f00c16064940390038040e070015100160309044401c0c01d22003144050001d1130140542458441c1c0720345c0c1c03404060400b078000c0305400e01081080540c00100c2e90381141900c26625040c8140c100711041c061241300b40d20104d0900e1000c80b005503c40c0201e20b03030340c080b540c5aa2481a0500c0822210000000d00e0101c0c1d40d135a402c0c001c42d1440820031610066400c00e0481c201c05982c2c902950140d44500800b40400001d0078244030000760041401c500742070081c070300a10900c26074281084236070011240b040002e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 311297329 1250 311296079 311296091
    0x1050c0304052107060216090b01030f020c06180c031203091903030504061104050d0605040318090605030715051204060b0a06080609100b0f03040c1a280e01030c020f01 74
    0x10030408851140c80c0c81031041d14a181d9650b10181c0c0c6076107d04c028107400c03c0c0100000e00c410b44450340482c134109018500003902c0a005c807140c5c412a8892401018242e005404020008810b207001f205c103c84488040d140c031000310008039a445000209410741140040300040e0b1f01c0e003040080c40407a500210703128281300d01c1420040c0c01024159420350310a8203080301c2c1b40d0541200021201140c00103030565441825949603c801003401034412010404070030420a801e01038020480f01401e1320321030000d1024500420941752a03405e40c4000c5c0c0002c01d02e04200500d03500402501c1040300e0754001400c0f0b40c1d0f101e00e0304200030040d9401701c59200f101c0042c00f080c281d90125503180301d04015030780d4900030744500080d1081007000c0d11810199800800107003002100d04405160424440c01c0d11841c0da648404c1c480425901491103901000004100c00841e130402480406021459403c88400001e0072840248120025019541815151004c020401e0b10070400038404001c81d000070009 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 311298579 1250 311297329 311297359
    0xe13021b03031305010b061305130f02031005010818070509041b03060c020d0c02030c0d0303021e070b1509010608060111010e010b03070b040e13021801080c12010b0f01050c030405 79
    0x8689010b54296031562030600e1160960a081f411102c0c02d10040d8198014185800100469100114408001180c8960941800c014140080d50040d0307000c1c000b1030134281c2400d00042c03080d20020408920031f0f422086100f60003c001c1414000ea40302030f40c410711555918103041c014005a08601200f11007070060020600600d507101500c9001c55500303540244012050460b804e641c1190b02a6058208114920076441c002d15804502c41c403d08015051408401054007452000548107040d0180000c01004002031404c50660211401002c1185000c145012440d0040140185001d00c0810008642d46038014642d2200380c90301c0f10024084080001c1d0014083c00d040d103000d034040d01c00e0000101d0300210b42000e480682d24030304000c070030940d80d42c0341565000301c0302c890a0342c0011044103070400da548071041e0b060180c0f1010004000450040381409104103001001c0da03456494941500441d030344114010040000c00d1078a0ac0c0c680818400250945c03141e940304a40c40038149440ca00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 311299829 1250 311298579 311298601
    0x50106060f0203070b0118090804150906093503031e0c0406120c111c080c04030506040609080d0923010b03060406090f060518010c0e13021b0303 64
    0x940d512581d41048801020000766a80c0c06016802018071003c900180081d500b09a0007d080d83d03014080400d04a030700b5151040903504c12f8010403040c0901e03014903031000790840031010050005140a40841d0f20300003803000d014030142d18000110300c00d00101550500141089011030101805036580d82c02e011081d0843c8001c00c071141c3e41c1012030500043c1c40040c4050540d81142e105484500c1d4030b203001ca08a0300101903c410704424442807840140c00c6140030052480071498803002c980c0c1255008601804040c001400c68044540400080c00002c8001c10110f810541c81400862040c210740f174500b03420f000301d0080507041441c1240210a0011400041d02c2000040e03011583c0c501d140000d00f400d8540c4078540740c0d05a4040701c04100001d4032540642e100c140110030740c051742c2d401e565548050350fa09555a800070031140b05081040c0b41c003846000c02c90103032030518410340380001c800300b90041401c1030301c80d0030103602140b00000b61110303522200301d00b034407071003602da50b450b01d0b83c1c80320 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 311301079 1250 311299829 311299841
    0x10803070201030c0305060f0d0503040e010303020d020609010b3f07170a050c010f0309060c0903120903030806060702040908070303150603060305070b0315030709240b030c0717070501 81
    0x1a0003c1c0c00e02401011a0703020f403098030b0040e60040c085414800e8518107204010a500c5804c6595100c100000135883e80e04000247c0603505c641d000c0c180907025104000d1409034090071500041c0d01d081c903900e02c144c0da249660214140b10b190410303407144002a419604445100c4138880307410a41c4980c01004401040b204241c0308004400c000344840d00071002d564041c06880249154001d4164002560080600701540b50051401196001403a910b1000b03590510302000041010f4036004d008010b0300310b48206645c3e86501c3c010014620310340740100303105805032556004200001304801592503c0d0407100c28140c10074007480d070364402c6143c010014000c8034080301c0c1616030000c001c00d03950311034001c580440307401000500000d8101164454103030300c040c2903061f402103413040c0c45066403030900c41880281100781c00002d00c0100b844100700044500140c1c0c41c403540701c140040c07001040da1401c0e03c0e0082d40407603405456082070b20384510002c07008184c1e4400300c00701140000c20040150401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 311302329 1250 311301079 311301083
    0xb0609030d03020927041e1203050105091e06090703060b071101082406180d120809030a1d01140f07110f06092b0602040e0108031c050c0702040501080307 68
    0x101056083e001200c00089100c1e170840c00e07080d80300020a0104040b0450640c0c4000190340b141c406900c256900070340d030080c10740c0110200c2c2d1910010442407900ca0b00d41a4810003a4505215041031139203800a9458020a1036101e450200d0224034064826845240a010582c69156403070015041685c440210009814009904075000402c4207a061002109814035040c840040d4941401000744e1034108030f00c074040c0d1050820307900310b403130355008010035a0601504030f808c148680c0010041124000505052081d841004842880e607441444640040c6000a81c1c203e641c4140004891610200ea080442c0d402d0100f22414030195040040840300c3c820704443c0010042035042c00301380c51403403100303527070100091094045505042d5a9014101c0403880403041c01d25885c485e0710400c15000900f0380b0125800314043c000703068542d21190140107030500450800b450560400da1103214840b00141e41c503110702c0890b01c01c0001d0306c103a45405600600900031582c451201c0743e034a030041101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 311303579 1250 311302329 311302339
    0x302010b0a05040b090c07020103090204020f07030f03020a0207052e0f09090501120803100906080c0108090105090d0f0e060406050705010b0906130902031203270309060301090b0609030d030209 85
    0x40042d0328645071251042c041c40c00b030705120080d60703036040612280c2c004c98800ea0501d034681e20320310016502da00c0144851115040301c15101e000c50300300200138925090000c0107042c4100b0070400360680000d0308504030386c000c842c1603041c002c0024400240c2e040c91008030349914011141c444820740c01c141030ba032501213555039058503269118507050030b42c1ca00b841202409400f4080400214813076500a546c04000564442e1645940c3c9036070000b2107265920458158128051342e0b2840e6a02c1040e82c2e0700001100d009009501b409201241c0709e0020002003014054a0b29200c154103014070302c89a41048000d201c1c54170355a481d800034045500c1b030801150701e5480d244104940d0301c0d01c03500c01c9000e407101402c503030a1043d21402400c01400064403d0341d1511500e415882c58100b00001544110006240751505442c104105c92103800c46002011080e0020300c92250704c0c0d102c0d10262070445c0c001000c003180d03000811010440b01d124940c40c00b0f03094020030f410000c0e8581c05400411800400340c81d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 311304829 1250 311303579 311303599
    0xa0f1b0f021908040506030402030f060a06180908030a0b0d1406160f0818030c011104050306070903050a06020a110a0606080d0c110910050a1706130b0414070504090302010b 76
    0x410700102c0d00c40105012028003041c0705a042c82c40184d80e015102400701c0d0500c0000d0b0034403928210341180e0071107500f52038100c10700c94483c1c585411001f41443c85000d2000c00020340d5204401e000003880c1d04416a69020040040d54405000c0800d0f15000715110300b0701049515804e8460b241241c1c181c035048081034102140b1889450340c88100801660362700b4003a200d8045e07468040c102c10709096164801072202540304003007840358902e11885201026900d6203414181070408100a0840301484150301c02000410408284241d009034454401030380c0c3c5605160640380c1700f81c2d001c448074441c030555519004002c3c5e00d501c01c0d010355429400b00c8094607603000381101d00100e8a180202824592a03200c4001d0800c025195003001b12402c4800c00a91948c02141111701301c2e030300c440000d2044020010344130303c0500086800460201c07581c0b0b411341c13050b2120000710f64080e1006012042c0440ba0703d0361b000c1d003408028040c190051080c0910440c03070030008c0c003a0000b05807135403044880300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 311306079 1250 311304829 311304853
    0x106080d1704020d23011a01030e0d08040206070c0303030902121b0402030a020d023103020f090912130305060f0105031e0307050307031d180a0f1b0f02 67
    0x100da91880c00c64500241c8690320303070f803e0103800c004804003154920f4031244c00306000009280c665a5a220140000641c4111903000d40c4844101c1050981130514042103042e10b5880450b040f080001203007441c04503900c8038070109003544035040019140601d85000401055810307001010003d008079810b8a4900181c5647d54442940f59610050412002104010350809802440d4440ea81410060501024000c02ea0a84e070082250500044ea400d004615058065047c900b00302400510280c10f90b0031540802c488400ca4044640300e02412000145065000c100c518803500e9248007060300c441c2c60388036040401001d4041110b1600942000a44c0d00c80001c540f030b1304a80c4000d006200f0015001800d0681c407000035142d0450340401c00140010640420040401038440d035910307424001d5000e4402951422820b825220340060000b80c00720200f040d01c0303d600203482d640001240c0711101c102100030508825400e00c41c1d4070803102018160340010710f05913405025000e42c0d00c0c4031380355 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 311307329 1250 311306079 311306087
    0x12040603051014012006130b090606031002090609031006180b03191a100905070318080903070f030b2203020703032102190f03020a050301181103090106080d 69
    0x25001c3d100c2d0144400c1020200340d8401c550340100032441c0300140d601d40c3d030031007009410003604484200070102145a40e604011454581c0c0741d01000600141c0740605040d000a9102c3c440c00306e601d074121f900030948540d10341d51f07c421250f030070078000c040300e402c112140d8241000e0305035031040421001d580441c101c00540c2174010070140e1003000f005040b0b00100300f03612554807800001d0a40740744428907100780390609000b102034011520061721010803860074040509540c00248420209400c280081e0749018a080355085e10540c03242220b0b0f15518401c0204e4502402640041038041c07680c0800800c0c8403030340041a01403401e48110300c144050124039005ca980b02d031741c00140107034001841000403030b2180c0310282150710035078480000c0914407504442a80c01c03030300040b00100d100210201115030021411b41d41644107040941c10060344510107881030005200e0030480c400751541002c00c8070110380c45040048240d144098a030f05000101398020160750007030200911580040034015801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 311308579 1250 311307329 311307361
    0x7020106090c142503050c0705010309050c120c102307030504210f030e091b12090a0503130e0709050a03062a0c020a05270403090302031204060305 65
    0xe40c0b80d070b6846070030100d1501d0541d03204c042001050070440c586151240050441d0805140c020b80d1099100c10201319841d007440f403140d00c014141440c0c400b0580000d43c010400c1000c5020843c3c1e4034210544903541d15007040c0602c403043da0310039030400d444018550041c024801000303080e46495030700010704507205a94419408064007241007440200f00000b107200c00030f441d0304006640c0f103102d0b88041d51085117420940200b20007042c00481044801d05184098651050a4003002d0f0003030041001802014815400d80c00402900300340001d502074070400c139001100e1760040807070307680e041c2c2400c00079164000d501840c0d9107c841800424902446640200155440141503484440ca0b554a10700102401c0020000c607802c842d030760348102d40106820700c20043c126120071107102414810400340c0481038024601c541201d11054141c1d030002c5240707000d50350301240803203055141c504060f1401d160030341c4000d616205900e00400401e680740080c10071609603440c24481600c40b0f61a40d0402c2c3d203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 311309829 1250 311308579 311308601
    0x200d050f100f020f1b0f10023606180d030306060207080d050409390e031912050d02030703020d0506040911040f021204050a0209060102150105060f0c0d0201050702010609 75
    0x1030a00c1035840f10017840e29644a15000b00041301d0b602c2080251490030400360424440e02640d020408003001440f42d50401c044010300d204d2010760104aa002c02c1b45d01c241088820b016620201d2040c0d900d942c0d10680c06c001e410010030849031020307a850003c0c080c011a0140c04014000e00e000016400000a40d14010f010151149418a420076006000400096a004d11600107503401c2d8001c054070600343e02d0b240000c82c0a0032038054011000540b213a90100720b00750003a8080d105400d0000810285400880c0e400300c4104502c20b03081500315010700030b00340d500905920000902810a825500419a20342c3d442400c2c04190703980b80c10072044400d14603000c1d1000340b656489411528145d07000324009008203900500700f10000700b003d09a04001c450850702c41e03020901013030a508d4414140b0360301600901c0105194013250018080c50704040c400c1c5402040007140c5a55482c0403402034031340c401f0b2098120b506803c5554030080c0608815662500554078000c00894408403c1c040c0341c0340c1d98 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 311311079 1250 311309829 311309857
    0x3130f03030504180b0d03030b010f0f080408070c0305032107080408030411060f040612110403080f07080d0504050d0905090c0f160c0b0a03140103200d050f100f02 72
    0x58039120380e054803100300d904c0c2c05041c0d55030b40030354880b40d40d9640640e0580c00e010360740020384907244030b0001d4030f000d91004200c01030001c203480f03011030580d0000b000c6911907442050551036920500e0426002145600010928003001c64100d4070300e400c05c1100400d11440d005400302c1e68481c41d40690713288105541c042c01c41c0301c0400000707001c41c030200d4a1800c400005042c051038a60240c2030001c4c50381054016030005074508200e440c0b0040303103010310307070400c078420303002c0340c641440c41e61514a103114660105840c243c020a0060500c05008261510150206400e000c02e01e0300d45040741d103c0e0f0b200026033002c106448008252810008816440340f4090800c01c0c1c078044003400b418101e03030050700c0110702080d2000f94500000d40b0910003280180380801c134141e11550a400c0c098103031a40c410815a850800070010004180e5041a0103400c2c052607000301c0c0104d200b40b003c56020fa01c1090050254800d02069015584000980701d0000178140400c00007a2140c1985005038400c401c20400700b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 311312329 1250 311311079 311311087
    0xe03100f061d040c121110021609020c010e01230a0b04061d0a1109150d060e160f08010b0d020d0924020c1b0a0e0c030402011b020108010b032703130f030305 69
    0xc2c04e100c18007c06820b02c0d8011200860540f07070100d0825052500305121340e580118440580c104240610094002100004c0c0400d01001e002500e18100381d075030074140d4100e8000817840042d0180d00ca20304541e0082d200340460b41e181c1409c2c0756030445810990111446450010701000b00611654088152050702c0500e82a2500108044520b00800d4009258010808840410203a205050040241413a07030b8000e881c00e02d002d0050008030f0b800040a100a0160320001c0700d9001c40418151030b91076248984810760b40c0401ca00901400100b85061450301e5180c4091000703440030959a9000365031000404001102c04100742d01601841070000c0d030100d4040403060300302101740e820300e410240401c0d940c00d075101d0703012001c5a819642071869250000034007080d540e210145152032109446080f507a0461640024409141403288180041c004008284001000c1c401040c070004d0103400320050070f0710351400c551668810032026541c0c00100c1000101e100300c84980c542141e4140d1211428 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 311313579 1250 311312329 311312363
    0x5010e0108011703120a05041e030207180b060705070e1e1306021201030c050a0501140a0f021e1b040509070e07120c0806040c0e03100f061d040c12 65
    0x3c3e424140405080c0740000d208442d4030b088402d100e03600c6019001008078507030030541809064540107a00800c61148001c950002081d00098804110380c5030024a8100304c0d054214a002400a04185c40e807114000a2087c1400000100c81058a14003943c0380b0864880c80d202c0c4e4110086440100e81d0000e006e400035035070180301c6084d801018002c6501629140000003101c410301c40c2600111041c1248090912060070018282c0000c0c11003800c00c21100203c001040c00d1a0103454424007c106015075026000c520a000c05d0a00141402042c1452604140720319241c3c140b0080d0860302c0d0114005103081c5291034055076010b84014805468010300b4050104c6142200801c00d1041c0b02c044e018800000c003052140b40c1d1054201d54070080740f81480c8081000360360a1400c040100000321041a000340d81c003103080301c500359081d18002082d0f904079403500d0150095074032086101f520341003116014009215800d220340c2c880c040c60107485844184218500300c11410140000c400c40c0e0b41d00072 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 311314829 1250 311313579 311313599
    0x1050307030312270606060c0309031101020c0402181c03050301062601030609060c0806031c0c05010501060503370e0c04050c0d0c11030a030c181e05010e010801 71
    0x5009000e0110201e4800c6210007240d502c1d5118800b84c580d80c1a0f5140c00209000e40c40c0304a102510280c0383c401e04412246c0c80c01424480907000141c1131801414518010382e00030081e881c9001005001991200f00c2103281e00024122811030b540120a2506165103900040c080f0030001c131f5240d1a001d00b541d0070301d1011140d8014580d811a940c81c10351114402040043c200603000718400c1c0700c04100303a003151a16400b80c1d0140700d03111047c0b086200a111880c0d0380881c00c0004401030880c0c03847c2e1244003002c1201c03404000d00019003254038000001c1080759018004611406011928681d401c4598030921444003105000c8010151103640c09042900c00c0c3d0401c40141100900301c440329034000340090200c5205803504c41920000090b4940140b11318002c1c02c00700d00050810b400b130740c0c0990b0f00454036031154a5031001096510708000414038065018808079281c1c10341115060340c0c42d0403081380488038001e03803501101c80d00d41c1c00085640c8107100c1d180b0747e2203060b507440c10340740d18000c4000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 311316079 1250 311314829 311314847
    0xa0206040b0307051308212b1d0708150106050406120209030d020703020a1d01030b040507170a06110307052209090308010f2903090111040603020c060a05010503070303 74
    0x140c00c029003000a805c00d08444100700001c2c0091001814030100080aa06694018002e00c0707451408103100344031014440c80200345d03e01c042030807071520510302d000304200100b0415068181c075807190461010031140004425080e900030000311003e0b030410380020700e0f100800b481254009403082100b8003002c0d21402e6400b81f00031034144054103100b000300009041024018080006a201600c20015807801601c1c100003095101c402e9031080050b200000f4480703c050002070006580d5001060030000100305410003420031341d85d04000300707800700d84c4c46448824103d0309603151400d01c0884071800440c001101d015010a0301c03414508024590030340c00c000100c6a090060400303251001864600314000c00310083e12a80d00e102d6190304000303a012150060342c0007500c07204038881001602c0c8101103151802d4400842007991a6134444a401d4054070a01100301001c180129001070310540640103040c0108001003506c00b150354030b20001086920034843c2c640d25901003001040441e01410501c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 311317329 1250 311316079 311316091
    0x402030906070e130e01020d061e03030e0d0501050106080f0609010e0f18060c0417060903070201110a15020c0c0121090602120403021606140306060d020c0a03200a0206040b03 77
    0x2d40301020200840216105d03500b030080b15940015880c0040782c0640f0440010340312140d000b036203c3d0400700b0030b50000b581034000201803061080e00100d0035655a0900f40c0c0c4d880d80300d0001c0c4000c2d0784940300209800003e0701e404144002c11310110b5103600d03262090b00d0680300303446100c001a0f540c031461182072010140c200080d9020403406960b41000a11030310740b00c0c11108000d00c4c1c0c0c4514181c10050020304940fa1030681c0d4014506201070403501204940d050741e024078000c00103c41800c44107041c810708440080c1a20051030b65041d244500e50040c00a00b04020709607200840c0c032100655070600300c0307100e110f0f100e140060310145035482a401400c409000e08001810407204503091041c0110a8031f05802584c408001031240c04841240cbc1c0c1c000d440c8a1410030810300d02c3d03100c0402c450001410031882004041110503000440d6415140000850000c50700c6406250401070304080f00110780607900241c07a840c60b4a8080e000540c2ca8081358090182e51900b031038996170038001d1f0405409 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 311318579 1250 311317329 311317339
    0x6151311070c06090f05040e030a0f02030c030319050a0b032a04060b0409060b04080303060d15020d14010501050717070c030f0501020d0609060605091201110708090f0402030906070e 80
    0x19907001ca80d0458040c1e010740195140c0c002d2440c01c01c0c0f184401c80400d40d00c100e204505092160217008004015100e801c071403401c00301011000050183c0c00c60013421450341662001004004000414408150040d181140d0400c40d40c0c8940c0440300c10389a0b5001c2058050740821100340b0100400e1589200842c10300d054203030440e03a4a000a02560807560107400410004035045c07103c44030900c52100240302a01d0914a003529100f06541c9074000289000c0c490807212000700305018100000c42603502a00100b10f55a010310140607005000744185504c100e00d0580000c1400d5008104907980e41d900a68004035020111800c0c82c45580442d10413200408500800400115800013200388079101e04005a00c42c01c1c101d1140d0304036825580100e00650401c0701c10003409400c5021542240300c2a40c1c45201c80d004100c001d03001d0400c0c0e040019018074006030040c184007070a0041c02c0f0b000400c469280d403260814007000242d0100f42c4c2d0404e4541c201d240465000da019201180742c140300500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 311319829 1250 311318579 311318587
    0x30209010507021909060b0d050709030c0b0c070b04080625120e010b04090803090616050f0a110f0d08090a2d06090602031501021c030f270506151311 66
    0x485d040c01d0320b415900074980c0c04c001240c802c94403415801403540c40041842c108850b203180d901c500d13003400d8a40c801c640102c2c0d400951086402424007410000c2c200d600b001c203a84591b81d042c02c40c0e40b03030412201008201000c40340c0b911600303d1889810412180d9036103a00701c080415034032a005140040410f04c180d076a5407000070450300c4502030352007058002c201d140c1d124075040c15910305250001f005405820182e01270340c001641c2044c19200c61804401c12651903c12241054a85182440c0360851912803c1084c0591160000d1800707070050003650745902d03545842202548e0f031503201100070061504487c81120030100b59090b45801d0444035080b003142016234554800310f440441c016144590000200102208a0002103071004000e20080100090a0700000442030010007000c01b01620b03420000b228030001e40007519580301d0700c0b401035101c042031229600c0c0070300000401c0391603001c1c0d40001140b034200300c850380100e494040c0c02c00c80007920201c1d50300001c1c089042c80840941041c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 311321079 1250 311319829 311319839
    0x309121d031c080a020307050304060f021215101106130201090902040f090605030c0108040b0603070e0c120702070305030403321501051c0b0915040302100c0302090105070219 77
    0x2c201812004010300321100c80503550001032104030000c140350307081c0740100103212045e58008112607010340c004000280c2240303107168035000fa110b00480128952904024410322030070200703a0507a001001c84020000c600c1c000e8054800c122000d03207500903900080c00086000380e103010452040b910524010790300e9911141070b4800c0340c000d5045010401d068a01c10b01480c0035a00c40c410150104030014540b0300d5001000038491440100002c205588400101b200c0b070310108911000f40500450030720080c80d0805928209420001903c1000c40104002c100d0703160010810206132030f0024055494603048d0b407603644811014040f40460450668101c045041940c1c49142c281c02205014102c1d0726000c4c01d03c8181c0800c1a00802d114100e13105d290400800c07161004c18805034802c01c00700440c3c0e1018426410300c1c1841d80200c0075441080c1c10802010b5010500f070360201c00b0ba550420681c00030200850490140c217420780e001c101c04001d86405442c01e2201083e0580d8504544050144c0f10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 311322329 1250 311321079 311321083
    0x109030f0c1d06100c080d0f021b0c0310090312200d0b03010507050f040e043014090607080306040b1002010b01080a02090d0b0a02090d0c0302010f0309121d03 70
    0x1254081c401d4810500601c0010f141030384c0b100c041d0800034030b0900881c0180351035040071441070780b0808000c65920301071144001e00c560142d0b02c02c024210800400c0c005421149611500c0e141c0640c1d100f800340410380301c20740656200c0c1d01031154140e40ca248a40c11100c5200e001408411184007084607696000c000117003c85006040c0001c94a078041010500103060500f566806441c60040c8641030000040a1010805840c2240d000956808a81e21a8180a0204690200d420780d04c550320111030311042c080c4803074596030540c6656401c41e01600d0101c0203601409010300403a4029010425140804c5900f800785800c601d0091000070b180b440080058074102814036058003603516501040c90b190380114400b580a82008401c0d4604880c20000401c0f00e005c0b82c100400801c40400881c41c8002c40f6411303901d00180152005204c1302071401c218545507110700c400c90008813115410783d4690300c640611109650b0000f800348880c40c0049007641c0d01d20340c0c040c010603a0724030213081d55040e680c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 311323579 1250 311322329 311322359
    0xc0b040e010b0a1133070509010302090f042d09030203161a0906100803180409050a0f0b010504060503150105010815130203010918050304060305070c020d06140a0b0109030f0c 77
    0x12080000041d41c1121080031746186040c2c40c4800000d4030401c2000540e0043c0403146c01c014246001a6038040b9207001403035000020700840d8100b885d0601d845e500d03034506106184103040c004001c609580200301c107541500c0d4400341c01001a0000d00c501d12813504c40b2540143c2091040346512428001c1c111400d240c048103d5070030100760310900c09e10504c41c80c003101d048050030182001d50b260101d03251401c2900340a00f1000c5000ea0350340c020384070504c1400c0c4000a903299010341e15900c004142c2c00d000c621201c0030b000d6644a50318103000061285800140340e120001d400b03558100f40c1c0e280c0001500ca006004012819008000c0715010b4240d6665603220800003003202d0050302c80d4103000701801185c122a01c2c0494800110400001042c1c002007550226110341c6004502599446001c5a5907001c2e0b100082d0001400000b9200300900c03508203451000c0c2c003000c00c18050b5036004108003611055240c550102e0a01c1d141400403610030304840003002d0144075900007265403001084d200001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 311324829 1250 311323579 311323603
    0x60a09060e0a03090e1305031903180503160c05030304060908070905060f0f0406210c05060705030711031c051903050112061d0303070c05150f0c0904060302030115030c0b040e010b0a11 81
    0x1078040c02440c6c121303018810f05018152f00e511040e4038030301c3c1d503588650320300c1009945c0c60103542c00c019200c20850407840040103040c014003902c1e102d540d101400341070b00c0300b1801100c03024043e502d00410313030b5281c6210703582c801d00c40208a4130129104400b8040241030340c9410a4110341c03601e00c0071520200c210313000d443d03036000d040a442d90260b003818000d05852142d088207114000070003221010030400020b07940000d8000103d803000601a80005e03142480d1410a19038400080401810b4260030034084e044507001c80c00703920000f03042aa001c4003202e000b409446d0410580030412008030b24a075101801120281071200c0604c562542241d1540d08115803c030001070100c5441400c11030107225000c070940c2c40307035080842403c101c43d50511000b002000c014200e800801c1c00501030f81c1d01c0c1c000d68000c5802a00800490041d11580e031407201d8140401e481c003031059a000190806034000712000c0f02c905c910090820b0342000c010303000541c04044040200014071014114403181800302ca10000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 311326079 1250 311324829 311324857
    0x7120902130c20010203270c0d0b0403030f09050d0f0302160506102309040f0209010e01080c010e090c2805090405090c030705120f060a09060e0a03090e130503 70
    0xb803202c01c2c18114030000b040c42e41380d006105000e4103594115010314450440360520701006484030500745080501c10106510a821149010901038407070f260600a41c0240d4060280b42d03448a5808150f03042d419005049500c89400081414811441100c0308075003440c02501d0a41403020410700078022410960b85078020006020310030b590f10321132500401039021403403022341c03403120341c001441e009600b5140a0105034000600308a1102c04040f00140c0c001d00529003541c5400301000150000d000b00d100d244100f80031580315600a00c001045a82c0041c66030304280d9807071029030296040724152400c141140c1c06d403d81d00e04d203200080d0042d240d5541c2d941c0d413140c45550402095502c05844411780e50040043e0f4400741d140451404151207098078103500700707010103505074a81030b048014240070b40074120500603100401e8004180c2180958414000018054141034a418100300d009003c51912a400c0000648806c1083e030312984005001203006419100c41c0c3c06e40d400114485810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 311327329 1250 311326079 311326097
    0xf05040606050405060109240c05060906070201050603150a0c0908151605090f090402060906040603050f090f0706031a100f09080d051812010c0903120807120902130c 73
    0x90b00300b42c81303481d0703000c2030901c0c0c686162032820301c80e01c182c0e1919003001c0d030660500e5036007442c0580c020b1117080b009542c0305040350342c2407070507980054403a641966040015402c07c2c001c02c416280010300b525055055600c0020541c40741e155110003801f100000c40c0c20301c51101400a50502c050140c1604d1b180a80d1441d812071900001c054184690324500b0401e01130184100e00c507a44400200b50104101982c440320070380c80e1400020801d0003228840c80d4400030000700484d60580c186c000c0fa01031403424065800300e4030340101050f01ea00044c1c0c00200700ea031250b05d0401019100c0e400c031603058001312131320801180000000c10006040034040c000401c140e40d144500181e8454441c0000b04008009405002d0b03240e04020030911420a0060310f61360800c074000d201d42e803140e04207e0040050b000030004400303140c3c1c5c064000c5150348402d035242885242d071800076501440c4040c0c441c141d95564121200c0380f80403000300402d0091000c1e41c02c030610b40c1000410406610600710300c403006031164480c1d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 311328579 1250 311327329 311327339
    0x90d02090c0703080f190510170f0f010c08060d0f0524060411390717010516050d0905060c0c010606050702030a0f080c0307030e01030c0e09040201120f05040606 71
    0x105100c080d020201080d401030406c280d50400c03a0203d5418412483c0125a68407a041488020861600803440f038843c03000200c1d94104000951424060340346050b506803000480e6040c0c220341d0320b500c0c6100031074210000281245001c0b08420030051050301852031000b6a521880d1904140c460300030440b03520850948941001c04035142d170300080449003030040030703120102d8056034000e8001c3d40000700341604030500c2d4090110540111303800403e4541d511106003c49466441c00148510ba4440c0522840c075003180c90180101882050a800035090b14071a441c41103507160300c85485040c0c06071340c0b1210900080c0e0305108541c02040720208a6071034290500c80c10703007114017a500c0f041c140300c030030019040180c4003c10007010254000d44090347c00070311801c103184140700780352034484140070004c0c00004050f040854601002c500703a90400450700356042c2594022150070000d07900c0540c0034005801507102c2c0ca4040f244458103540400d440100c00f80480030340390f0035582194a55101c1c801801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 311329829 1250 311328579 311328587
    0xa0b040209012c070203041a090f090f04031b0602070507080c0a1406090415060f090f080604020d03050904091a1b0406050c16180f050912090d02090c0703 68
    0x4007500b0407400e40d446100e6079980b9290450f05240301c190300c01c802c0790002100300e0700038800c2d00c3c01083e1907510071500001400040a00b64003c1110f5842100c014100502a0610420702c1c1d10800212500b04600d8440c5e4500b590480c5a15903010300c0300724800400000241035002800b081403007840105060760a009140381055150228a80103402c004410000000f682140b1191140c094036600e64800204000c2005070550502c440410b43c01150000382140d0700c00c54840018001c1d9459039540e42d1245515007400040b4450340e856544140d000c01d0141c6003140114444610a0a00c9440c00280700046070075155042e0080d81c0702011442d40080c40d202c40703065581e101c214541d0391009107a120716000322500a5002d00000c218010030304e01201c110400000d50301200c44039910400540d02c10088240c018500d0414a9040c2440715003d411015409001d001d1600040034003d40e90140e80722403010f401000004e40c1c010003003500000586c94281066000e01e5405118603a41d0140d410094 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 311330935 1106 311329829 311329831
    0x15050418060204291303030e01270305010f0b030703030f050d0f020703110706050a110102120c0a09080d090e15030d02010605031501050a0b070c080a0b040209 70
    0x1191000486050728254850303007500864103124000c04a544d030198030a105c440a14000060001900502d02035444200c1072406400703442002d01c0c1c458100b00031a0214a603d10a00014004c0c0203081c000d4400d0240304203003e0003100301c4000401e40d500c805210141c2001421040450716a10031401c40f030075004218010b200e501020f900e40802948017003011000f00c1d40c0340303d0059108801154150403181d40d600c41c3c1d401c1c8901c13a10b0507205601143c0900002e558200843c0442d41d00c0c80070668001c2070300320b070b06545032440c1d21006820010386401c5001940d01c40c0d038008034010781c80400442610f060130100b00203501c820082c178a048a44030052031303042c0074102c0151f0410758154060001c0312422000c49400c028407600400010350b00380142a04441141c1e03081c0171030580340c401008014410105850903030341d07030f0404609281c40000103d0741ca8116000380403d524040c0001 = true := by decide +kernel

theorem cover : BRFrame.Cov 311151079 311330935 := by
  have h0 := BRFrame.cov_init 311151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 311151079 ≤ n) (h2 : n < 311330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
