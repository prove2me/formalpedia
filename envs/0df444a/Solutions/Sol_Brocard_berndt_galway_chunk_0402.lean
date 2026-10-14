-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0402
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:37:45.007993+00:00
-- url     : https://prove2.me/submissions/a5fbb5b7-0586-4e77-85e6-cad2ddf127f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 72122304 ≤ n < 72302160 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 72123554 1250 72122304 72122327
    0x130602010203070e19050613080105060108040f02090424020a0215010515030714030c0a020d0f1e0c050d0305010f06171504020c16050f0109140919060905150609090601 74
    0x180107005e41c02181c40d13100c4200400c00304c050900c0c170000180c070b07048030310b403c460303009c0c06d864100148007040c0b01c08035400980c41450f498041b282002c20b80c880b40b0313014807103202401784090040343d1102d5884418030340394003910a0044076001e0b180a07100035880503a14203030034011160300240c85d00c1c410b030640c80090095540441c240c14071303041c0054040806507058208503038000d80000005541d09040f80d06001c1c84e40212202d0620780c50741a40c1b2000070702042001d0399070381000108040080b0810703200e44100041e258204060300c4050000c20b03001400340a003406004008011850001244c030b10556040340e84144008611009480d180d18108014500c03618090b4000e80034056614a008103221012281a1700200d131002c140c6001d003030264441c08512064148540ca100401c4201054843d25240c080d0032130b00c0b8503069a81c50075441c503907404150000070071850031001013020a420340c416401111500d0300158240c0314142009480d10035078400c903411082d030354007003003095001e000e00c03488 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 72124804 1250 72123554 72123589
    0xb09131e0e0f060c04090f020304020904021203090402030a0605010801060503010e0c0d0b061c0f020c07210503040801050114090106020c012a03020a0605090102040602061b1b03130602010203070e 86
    0x1040b540400a80b07402d009480a000e84000000c00700000801d900c20304081e41901d210550441c41c15800007403400d50001c00280c000c1000340849401d00320240211707240024003c0c002c544900706119803000401290041c2404160b0200012840c98000c2094904882c801c00028126030707034805007028250899841440e203103131260003148065442d4804dc10348125442c000c1d055010008003001700341c03071054000310700d202d2040003c410031900118070b10003680c01c05c420500d01100c0d54400b00015840350722020341140070100340454a8007042d08554129840b030040c00100c8040740040103102802881204096444100150000e50003208585460a0241c00001c2a0311741c909100c00c6c11480d5507411001070b04041410401c1004034420a03410941e990021410907060103006507a846016148000042c2c1510b01c062220701c03500704403684c0c00011000c50020400100580e507403508035148030400e00460a002040a510510075248920307000e40e281050118080203000e004810b80d00104c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 72126054 1250 72124804 72124813
    0xb0108090d03020901170403080a1401060f0c021504080604050609010507090303210e0c090a0c0207050108040c050a0e010503010c020a0b0601140415050306032506080901020c06010b09131e0e 84
    0x7014448246c001d00c1c4501c1c0a03841d0700c11149003640030201219030040c00c102c0c83c00068030040c8084da038041014114203441e814100a42c01c1c140c000a500000c0b0034100c0305180c403001134003182404c4045900c40c01a0300c2101200e8050f00c54484031400c2c1c400403a81c50001030080c810400100344900c200300c0c024070171041c214070100060200842030b1480c0c2030040089a005010706900b500b84420700603401450355204015000b0300320b2000b5200d207038610070141040344074008203040c000c6a120007001030900802c0031110b15540d00c11104180300074400d5078400d520382190113168074004100c0c07008140d40b00c4050205950f031400192003c451440d0403803d07480040c070000c6079403440c400c100e1625920740e440712034030391410030304052074600104030704011700c0441c00036404000c5501002c0410384449041141d8666104008507009015138002c88406101da0bd000098800c00f000081c034400b001940ca01c1040031565215905640c45070158000c007000c2804481c01500241d030084500900b10016074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 72127304 1250 72126054 72126077
    0x403120f0206060f0f040e010905070f05090c0406030e100c0201050403120b0a061d12070302031204150c0311011b08010b040b040308031005030703050f0601060e100c030e040c0806040b0108090d03020901 89
    0xd42110700b15103084480364801075080c492624cc484d5180e000380402c8503c0703c075510b001140d000640c0614070031503080c140c0301c410f40c26a8100500450070010750012041200b11146107009002c0d000c01e8a050380031a00381041550150400c0c004c60b80c8990000e0715013100e1600d84102110300c50310810a0b0450b940c0c090654000710340d112600f090810306a02c0040c8982c1e0708600405040c400c00740c001041d1110201f00800401d480f00c10751410322056400c11030710740c0e00a428280da129103400c4194946500e00145400d603401810788542ca400159541c0040f80d0fa2942520b4049215a018001000134180701c00c0000400d1080116030050350398000305407642c0e544010030701c0d02c4800e030011181c9400c4400e012136050f90421440e0300401141ca03114040510b0715006c0b900700094550a20100f041706803403013080c540541d601d80111100544200f1240c2000580182a160140d8440340304034182120b0b03590541c8038450709800380c407104010300b5501c1e46020098000350b0001400c0d6040c042e840b20305 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 72128554 1250 72127304 72127331
    0x1505012c19020c0703020907021507080403020a08040308031005190308070c090507080108010c031b050304020307030c12050c090103030927181101080405120f0904020403120f0206060f0f04 83
    0x6040380e645a50000c00004d8114410400c010b04014000c0045500c14191503495042c010156a0404800c0c18482041d44460034201e0408000c2c1401402c039000004000003044030b114000d5118403061075004040a45030b400700141d081070381c0c0750a00d900000d10014004126282d008001061140e1083c107000c035074078400d410540b01e0444004001c41c0c0e0560041103841d0081c01003240c3c51080303190800409114496030114200c0c0c020081080140210001c0c01315202040b040c000b075078105026030b01082d6038250a640d040d10412044039240690502500355007040021641681d50544031200a41d060425500d610b0b210710038210384400d1061200014504ca41c031a0900d00007484813508010003d03401e001ca0040b1a110340181005241410080850000300310743c02450241c1c5101c0b5551000c1405c0741405000300c00080c1d5000780f000230b0000030040c4403181d12043c56041c0c0c843c400c2099034108207903101c1004540b0540c0001180141204910304044000b007041c000420001d003405c40d5282 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 72129804 1250 72128554 72128557
    0x16140415030305030906010603091203020901170f01061b050c060901020a06180308150906060c010209042a0f1d0a08150609060f010e0f04181505012c1902 68
    0x700340c0124000009120340520140803d90140140d070609000c0c002c103aa1346d110100f04c030b0010090425501088a1065a01c103900100d55540d12078650a014103064003482e0102c00b0a114500108ac20b0211510300f280111801000040d00607000d801e41d03400d030134280b14141e0700280300a41180256651080010f4540c0318020720b46441805102101845d1316024244d810098050040702a5486812100d1703038841c443d00d90b204805841240e10f03505030821141c0a4080e4407040e542c45810080310a189050340701c500c42d9102e003402e54001e40c0f8000c201c0242d0b81c0442d068008000100c184203070396007010340401c4d200d203e040040c2200d45d0060b503528640d41042e001e200c102c0001c0300448103008541c82c0100348140c01c20801c880900013121203200280c0142010b0300218083d00e100d04000821b5507407903002d0744a42e0b88100605000d0032081c50400d5000c0c0c440d15020030070342d01d0701e400071601d60314401344e0003150894034581d408840075011010039216402400740a004940a035080d414110900 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 72131054 1250 72129804 72129809
    0x1106040302100609020408190c05030f0309040c030203090706050901051b0a110604050a1202030123100909020904020405041b1502010605060307091502120316030e16140415 76
    0x24050b107586111440c0e650103903070890340710019030b50060000f4000401d020403450700300b0041e40e408541e824a5460b000c1000f048540c4556810300030243c0c00d000045010000f448070540c00c03142001003141d030342c205170224002640da10038990301400c005c1c8184c0340100000c0000c6101410040d04088040380c84a11680c02c2d1000e40c100d40e0451340400c4108031600c0070003040c1c0b40c0101c0300103082505190200349601c04070b100310590303117010f800c100007951000c0d8440d82d011312211a0f00c450601034107149001040c026116007180003038041e80080e6030a41803160401681e4010207407585501c1c1c030b40070080078240203081541e841c0c80c1d00c0d070681c45100e141c04044000b4940c0307080c107101d05142400040e08444055015501421040041101140e4010300690035503441840118207602940300403480d0203164224043c2010001040c005085c502e4508035406ca081550705001c54441058240d846000e07000341d4002c031b00e104540030b20400f07460565000c420b01028000041003612030020000c03000007603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 72132304 1250 72131054 72131057
    0x60b0909150604260f030307050f0418050f010905010e06010804150e07050301060e0c030402010c080c010504060212090a02030d080a14010306050912070503070f060b0d060f241511060403 82
    0x101c3c01100301c200c5070b01c2840480420700c003c3c00b96001c102503911b81703d100c0189400108400014034145652404040d5005403200c484005190075000360345100914064034802040405c0c00000101c00b0b00d18020346040e180740c02000307440c5484010054034001400b8000b11102c2c0340c40c1d40d10a400003c584594101070680000803d078440c42c0100385800c60b580c039003007110042c5108003008041510181100d800903030a1800b0304a0030014148494540a40c0070440d00d1355081c00248418010a0b4000d40520002c852115506448490000750342e6071203c100250182c015001b807055031406100300355844145844003050714428000090020079090b001204c03810754600034800e280b00100011030344503455411007407828280d030703e030550740f4010308400400a250740780b000d07410810540c1040e0b02c80c04000d041c0c026400341929040c0c000d000722104002d4524500760b081040703a5000b000c51044105003561007401141000c80340041c040c0c0e02e0348031805201c50920031014505040040500c664000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 72133554 1250 72132304 72132329
    0x80303090a03030e0d0c0b18060a061e05011d0609030703080c0606010c02010c06090302031303060c080f06061e090d030c03030e031903050601020a120507030e04060b0909150604 78
    0x1c0b80381c0a021980b10a52443d00c652000001d200c00350341000742001144e4201031350b0f948075600c40015602d01d013115022040280103160500040780741982005007501c140e408240340011114041844401e0320b8458140001d562240300344608040c104c0c40c40c04000b0240041740f03001031140c0800d03c0d208442c0d0007110250800034000102d1001489140d40144003403a1000c604035040d00000d2140440c04000f5003107568034041e0404141c02001182c002d1400d04160035480c1d9034074244103000300700301c1c200c5c580850b03c503800182166000b810100d00c00e40c002040a420b0040c90300e410315085c203520a00001020741000750000303541d00c80003c030340c40904c40c0c1e480e52840300d00b51a0080070354017500820310940e071042c002d42424004c00e1186d011500380c81d180c002a10343c3e890300100c0c038000128030054078103140c610078020050791080081819500179120707030b04080c0000c42071000303c0e8046c1c400d4680c0f034907040c0034403280c6203001c40710349810031848403240d48581484e500150196000782c0c0905141c808 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 72134804 1250 72133554 72133573
    0x9040f1202030a090e1e0a14040b07020105091f0c09030204021305100201090b07030f090218090c090402130c1211030402040b0904020f120709091401201804020408030309 75
    0x80c48282c0c0310240403019000ea041c3d05100b0308000d50010506d41213002c4910400000307001003c1039010107000005088020107508041c01e00001f040b00035241034005500b40000034100d0303e40040c1d0914680141072204c7c0100c0502000007000b81010b682100800400160000150f6100e00240c480c0743c68041029070103a14000401000c0045030078083c0540e4100024100442c11016150f079100d076650070045032501c1030b00d2101005001e90316009520a00c0a9a01035058920b82503a600c03400080f4221011103484104010782c2c500101d5000394019146d00c1c045480c6c18890304180528601410003090600f0124142000c0e01c0300743c51185040e20000c410003042d46411300030030501c0c038002e55100c0345504041e0003190855400e038941c0790154071149131001008800704072420041060240c2040f24082c2c2e403401d0a08403403581c072020300139070905944a2961428110308036842ca03014000d9450b084100090002c106018401c140d44242d0900002804031402d00042d032280b4031200181003440e2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 72136054 1250 72134804 72134807
    0x50609100c02120306060306130c170106170c0a090f0303180e0c0d05180a05060405010b01110a060506061308010212100b07140f0106031b08160509040f1202030a 71
    0x1c141c14400c00c00c6501c00880d68001c1c5041004a94201100ba2106585e0340d450700086510200489411a42a4030b854241c4822603400704107040000da03884190302440c1d0384c8103030444102001c020151080880708002c0b0340c40d07100c140001c1c40011160304080080c0c03540e840c00760100d1620360f84140c000c5003060340607080e80800c4076080d8014104003204120242402404d00400303000315038001c6c0000e665100032032400d040c0700348800440c1c00c000d401c68150502a18281d6140c1c03009440844066082c5029054603601503130052294510940042451400d591241c4014050240c1282c2e0001820001522401c42140030400a400c00600140e600e80c00c404582c41d00c4040102000045141540e0610038180400308651541350400c0381c8054801c0c00603480b50410106200010142d80f0781f44002041094103800402003404c2040e18061143d52614140d0301c440607070b0090700e80840340c0607040c8580c0c80d0008140390090300590214013130580c0c130b558114030124101a2800035a02c04900c0a8246 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 72137304 1250 72136054 72136061
    0x604200c060c0f0a030e010e07090f0b0f0906010c0303090b04061d0105060a09021305040207050a0201020d02150103030f0c0605071d04020712050f1611040b0603040b0606090d05060910 81
    0x2c0140500c03078a001d1074806074825030b001e03044205007010749a21240b5030f84182500f20050a00c0040b0135120b00c5645c4c2da00b600014864143d080c0c0030300342010034090403450403aa4045c0c103260003900c40411a642c020044480c1c3c007002e201241495079400801003c01d01c0300d1680c03881107114a40024600c02e010701e16a0b4440005a4202503d030704080800c03c4940b59400040700b1200c48100158039100c44007034916107015160022078002c4d2000c50072009000c1e000407064002d5000317070203a44240710b6001c401c0b0b071941e0001448030744108080c4010130000b4482d8003803007101131084c030f0882420181ca640788002d41344240c1e80c1400080010801c101d01c001c032400c5900c90f6042c106c40461030007441e030f981c404007118101c4060040c0903002c5802c203042d07050002103c3d114180210b00701843e940c9460612500800941268022481d085400026041a4040f00e0145030895081c066603520501005215407243c08001d42010140b05134200140c0f080023101d00508840c2c0c0504440020304510034200c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 72138554 1250 72137304 72137311
    0x1505070b0a0b03100f0605130c0f08010f0b070606271503030c060e03090316030b0a050108064510090c21021302070209090102130501080604200c06 65
    0x7a01d1400349140165640000c19114180c031507603012800d840e911000400a00c0303035a001c0780c0c002c080580c5034020410701c1c0e403059203021300c07589414155a04460040322524402d0040120114002d1803e00210883c0401f0b0803c031403290354049038168407681e00381500030310301c0c50034418500000c00115005040e070044811202c0b00300800801c4510f10f0f00c005200d8014650080c166542d50665484002000d10071203800e044083c048031960392440c0d4551007104114801515020102008100c0c0c20710b080c01b80c5412141400d0082c10680c8510800480c00340d92040703803100e28110200301c42510031107040540c02e90320300004102031081d00e40300f10a0910b00d0040d40108134614042c00240043c40c1c40a0307650684580402c0c06051403404050110004500103000e94811418515801039540540061507400d1096401c1c1d80e0a03121a00302c40e090340110140e02c490f04002010070f00031944640003265124100400200d403c11030360300d5035070f404007002c081400d8140300000c00612408007006055003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 72139804 1250 72138554 72138571
    0x40b1804020f0f0c0a050d02030309010b040207030f051804060801060e1f030b090708070f17070b0307120b04021305031e0606010806042d0609020c07031b1505070b 72
    0x2e0146441d82e00000b510034000403c02003200032540004a0b4402c00c81034252650100480d500d004821401079580c0e007040b00d07001555800d00a41c0342250a2600959a0760356241d1240c140d214006441950f41d60032080141446540c001d60800c05950307075000d80c00051910038000180d9504200809080c580c0007444032034000c4100a86400b550020a01001101c0d00294106c81c02d89170f1058941c10115580c3c0f00104920070350f00040f409503200060350003240c00420038014448803203182c0c15220b20540c45425010002400007440030b0f401411000040c91a9400000d402295040040d089806c1940041c3c000350b116170b02406542000c1100c08016280e034181809091024810307660b07100b0b80141752604004840c0c020501d1034542e0340100c06007818105080081c07105462401000d05028111940c2c454100704002a4000c0385108450040700d80300060a4074034295212a1f4000202d030721055007004000900241018184819103803000071a0b5030907690790001c1c1008491100068034458 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 72141054 1250 72139804 72139807
    0x70f0f020a080304020904030c0803040302031207080601080a0e03131203021e070504110c03070f0b0117030405100207080607080f010509090a0201030e01020c0f030c160e0a1a0402040b180402 84
    0x801152000b0160796000b541140c820503103644a02e0125800980745030003e04c04a808020f0104143d00032014040200c6c0b0701001043d260355610781280c61000542d0100d000c42d46400c0883c0b4600c801303400240050001c001124070b00a039601340110300b00095403003420000c11044003c010190b0500203501e8070910220358a0540501400d80d5448520702d108851042d9541c4e8101c03045406d2903019100e03e599070038181e0b9120035a1f81028840b41981c010111043d61002c40086140411110401242c440c9000150f040c241000144456441000b048409502c660480003a85010410030144582c034035940320902030901c0f8200043c0e01d001a041f69108485500c204001c0350b01c00186070000540900c2c000c01d260005040d450700900c514034081c0080e004021100340b10140000080800c0a041c40480c5c0703010b444e0580c1107040301c01a0003807510980d410f10100d101e601894015803221050f0031600c9400d241d80348005401c91388207a000926a150200310003856011401c2c08a407045010748065 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 72142304 1250 72141054 72141073
    0x90c030207031d04060b0d05090105060301020f04120c0b0f0a02010e0c151b0102040617090a030c08030703020c1f1a090601030917030a05090f0705011e0314070f0f02 73
    0xfa040c1028002500728407406405142070303a0340c690700840c004100c10482075a88806031011403003d0407080310702c59020b608010200b1511300b014400c544d00108504c444508050901a10b21160f080341e82040d202c074450301201081004100008000c40982651800d44c1c07406e81d90744c080c7c02d48144103280591500b207406955615258400640861400c05018696414102202c9112001031238081080c3d0340c40882c0200700103801c0141118500846089a9a00d42d030b541d052a940340c0d031080004000800c0b4000c004005180c032401f95070400c082d400d01504080b40e0404683c03420b414668010306a80749082540c812010324801d099540a6014074171034001e241e8008981000809044281003540e210744010074040c00e9100921020782d080c2c80720383c0d2803d1183d00312014103002e41d020045130054141c0300403211000a200801c48074107071107030041c083c64a828403112041c42980e606c14181c0300c160b6440000c20309252541f140000da180d82e107050b0821040144000c2c074422038642990700100c000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 72143554 1250 72142304 72142307
    0x91509010b041503020a0c0609030809011515030b061209070e060d0b011403070b030405060402011e0905040f1d0a050706030b03071e1203090503010507030203040b0f040309080703030207090c03020703 88
    0x800283c24880c100981d84241511044030740c088003601c080d100501e441d11080825a00514941c0035a260070001d002c1d50600c180c9100340e5482e0340c400c0c10001d2050200501d43e01c1d0181d00004100da000030030450425401c100341c0850081c040f60781c56210f400064040c418158a24502038020a05030b4240500d000c2c656034010148006001d2415220200904014207503010170000c0060031240e84415164101407a200d03a54090070384040717012415801c41208600c90400d03804074100c0c0d6982c0c40031101898034080c000200480c1038040e0350340b616041c40d200e504014400030801e0b00542c0c1d005104045d03941c10094107015407600250700701820624550740316900080d40d04180c2e5001304c071510054080d42d001401c5200765500843c5a103000c0215070090540044200d0102c59065009112780d41e01c0c3c500c01c502b00d10003160b0007085507003124007040c054074422894a034003622a0501c000c00c90703240da4005143c806954021401a8050b10040c8044c014501a00d001c150890900b5420701026640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 72144804 1250 72143554 72143579
    0x1a1c03092709020f04020c01060e06010e030d03050411041a0f01050301080a0b090a0507080a0611070c03150902060412030e040603020102031611040903030c0f02150c09030309091509010b04 83
    0x20400c940b1207000300251341c0e034140d51000701d0340c0007002190340310510f06400340a07040038402d2074140c1413000c000403040d502401c09544109402405401c0c104081601a0024030010b0816a51101c10300c2e606980ca48652240e0115803031502c1c80b40c4200340700801080f485400024400d41004818401001040400505940c403558400083c034540c0daa180307030013440c003d1009805010b0748a01710000620030300c00704040e500303030f40548024814911540035100c5ca034480e078440208060660303101007010035480e8403004003034540c030240420307850001d4000480b40d4210b50480c064050304003d0403002c040d00006100702c0e1440542d018000c0e40c0c03654002035240c1c011141c00113991010050382d881005041107119460100080c001c001c210700c2c9042c018001d1000304010008200320078814040c0741d00001d50141c1a0640c0c0c220641d240e540e81b503c00e0b0268100040c1c40303805110500c2481c0c03055840c002501d22460890f120005050940810000c0340481a03110b07910b051402c01c01441a80c15084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 72146054 1250 72144804 72144869
    0x20d0c0e1003060e22020406170f0703031e020c03010c05090406080a020303090603070c06060323030c06070f020106030204050f10120b0c03070c151b02010213091a1c0309 75
    0x1ca400701701000b02000c0c00e1121003c0030000707611070703d0000d0200b140007050154601d00d40d107178000c803490704252400082c7da4440c00d00000d004030380f400c1e061030781007041c83c5641d440c11040b501c11380780448103500101e0f00307440d0b11100c4030010a03408189803604ac100b51080500400c0d0480040a501030160046a180d11481c040503024100000c0014400c44c0940caa80440b60307400030040204959a042010041ca106101c1072011007121041078a960000016201d203091400060000d5071200c140590701c000040d443c3c2c00941d500e8000c000050b270b80703511480380311305040240b08859140001d460f0b1060341054010031016031903204080081921010240d5000826032840d95607500c40000c2070f52034103991003004088441903e2110840da13038030f07005001c0700c89021815180e000111035059090b40034641200800328050b0104105c140100c2d00f1008400e90740c412000190000640450030940e2501e11034040d00c01400d01e00c07010194468603000041030f10103203c08180800031800c600341417982 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 72147304 1250 72146054 72146071
    0x60604051815030303010306020a02062508181504021206190203061f0f0f030515190e010b0a09140105030105121c0e01080609010602070605030703020d0c0e1003060e 73
    0x420004079000508050360360341150040491751691781d02e00d800070280d400f41006000500810000c254042e500410318204a05100324120603440c08080c00c41d0844030060440138003454100e01041c080038103004400500781f01800018180c5441d0042c807001845001780c0790111703030044081003a00d0702200604011303641d01c0c1c80c015030b9070f83311400040c000c41a011145611400032131180d0101c4c5800464040548013552180c680208203043c0683c11070340c080740c40d528142280c050709020385c07070724044005c00720080f0005c5c00185600d031640c00d808d0950036000481607041c00200c445410750040c054100a0800c826200ea502290340002802804103200ba9402480ca0020881c107411007400b4480c02e0b010442001d08a16080e84d60042c49030301d01c01042030125803880007281050030104001c905070b46260700140010340c03611108450691005010008060342400009015221401000c0c4135645940d00d2142e9203c01c0401c014251030840a590140352a00c42c0030031035400d40d46099079100840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 72148554 1250 72147304 72147349
    0x60c0a0f030207080f04091a03030409090f0b09250503071701091502040f0e0c12040302161e050108101403010f0f06080106061103120606040803070c080606060405 72
    0x41e0060300079100000d090400c086071074060340086001400440320344500034801c3c1c1d10080c45c00e02c20403881508041c2c140d0000c00c01405550040c0d0011001c80d445403040c600b0145442d250599500801d440500958100a9043c0d06c581d0b815440d42c0c01d078100c4251010400c070714000c00250f907102c1a10a18000b60764a0760b65881c2c04000303501101c090f941040d1001c4000155000020081d8000c2c002c0403040c251010b00481d807404c00e012682c2c46050070001403464150005140c0c1e24482d80284100e0851049451182c5100b29240c2914020000c140d05141c501030340c1600c070001c3c40490381000e41001510400c000907190800c81c200100e803d0084003d425405000c0440c0c090910307440c03440d080d141451510b84161015902c050201c0d00345a000708210354840c2022102100304000209140c3d000b40308412141d20400729040e0060b000800980ca8190383e001d02c0e13421034000e0f1100340d488a10219003000b14500c00e0000b00d91005d02107890310b10703007030610002400750922076200a0380f6090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 72149804 1250 72148554 72148577
    0xf07060c020105120f01030501180f0204050402040207020307080105060307090c05070b04170403150e01090b0f250201020a09151403090304030203010615090504050f0402060711120703020f03060c0a 87
    0x743c08903448040c801c0001480d918040800c07900c650000c3c84100c503950f01c1c0c690510a03107081903125102c4650301182804064074503408000c043c3c1400381059034800da08004c0c900c0140c2d002c104520080c0109800455685883c07420136040c412164092000d40b800c01c065219416846000c80d00103a07400142c07041c00361030b05d0074841c220001107120040d1714607002501009200400021103d401d003050000d01410100505c00ca003038401d9404010104080c910114000c0d850114400ba0300c844504111070050041c0c1c1c0e148410045509a05d901503540090b4690380e4a6012040c20003900c802420341500c2c440444001f0704c61741c81c04c0c80c88a50a400800070800c1c8602c144111402550020b000707220403038841c070f907450000e0741050306140803c400c3c1900280a041c180140791194200004d9105245d54940034804941d0220501716480700610501103516078809640c040d04400c07410003070800900f144140500700d852201510700c81d500800400ca000c251920440e29803880c940703002d094091 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 72151054 1250 72149804 72149807
    0x105040603020d0b04110c1606090501050c0c0d0f060f050601080c07030201110c0303070f020a03050906180a0f050424030f020d060203070f030b040902030a0320010203010b0405120f07060c0201 85
    0x1391580d103482d40181042c00c0c40c03c0c202e1114001d0711451500e281610810000840c00b228100103510600c0040f5210a03070420542d03020700094180c10403e6400c1c0d840c4075900000150030074501c503404807036060390102180c0c1070201170f100e00ca0150001c00d01c104442d02f0800006081007030000e0907845144000034000e41014800e40140c0459020104d4a503119201c507000640c0b00d4104a5903031001505421800700780321b1001501405203a01a2912403405d84160184601580120307510304141c024140c620744652280c4c40001d00501c43c080d080c15200b41080d04100680380b072411850f104200001d085e031104e030f201510745000c40794005580b40a490546c408100720319019a80504041d02c04001c002009402841b440c0321320f01e81c1e580c00c2021420805c10001120400580603405034010f140c031340c0009014507101410051045008407410003d54217060a81e8000d0b000b4803e0b400d80880c0030803890030101600b40030300c500d0310b0140103c2e4510200103980c3e460390380305460070420924052030659 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 72152304 1250 72151054 72151061
    0x4030503030415200708070822090506010201111b07030209070e0f09010b071407050a030302070f0506030c070b06040b0909010902031c050901030207060b0612100f050105040603020d 80
    0x4661020549441e031034207042c04210314805050780300b00740d0b08001c8404008500280c041d00303d020f0751000305092004c691585080c40c0c20218046031214400c00c4049a80800404100134144c07076601c1052040c0c0c201007002c010f0701c2020b0074643c10741e810f10602828091011041d40c2c502c000c4800c410000c401e00c05142454580140c1c0041d401c050400d081c488400d130b029003c20400d4000391815042400c404043c04005c4c43c00344261607100c5410f0088000064101d06907000003071501c0e0840e21841d8841000408440c0aa8002c4000da800500108586034410070307080700070031080310501d0444c81e05013503038851072148040051184840c0000184259a1580550041070019080110320314214400e40c2c000d0510060a030700c00d2142032040311410501e120502000c40c06540c0301c90030091080d00640180d00546021298107480d0024800c0d203031100000780c807290341d02c042d030320a450901860484420311590003024090308c049909000741d98101c0e003100d040700c1c890310300140d0355400300c6d0094005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 72153554 1250 72152304 72152309
    0x609101e0f02160f1209030809090916180b0a0b0405010c030203070b01031101080a05101e090e06070f09050105040b0d0b03120a020f0c24070506010b030411030a0f1704 74
    0x70304459840c25001d01c90000c45420b102c601c0744031748840356400040c0a03071300c1181a120003001e0070f808100309815814841d1105800c810350301c0032600c210307042000724550003526401c0701040a2031404424166426170050750340b100000e035035110b001070801641448a110303e01400e0305100b5219841e40402d8030810450300500c0d00025554107e5840745002d101a40131826007600040c4902e000c1140601148501802054408c2e01041a24a00610202520304100342900c00715000200007895207541d000340d000800c82d9070054295864000c901078542d640c214480d504000403448107005590f0000308850503541d282d0300c1551181c40004080c0058503144a80540601800d00c40c07800ba00d9440d005070041082c40d03020b5501500c078107201e541c2e8600c1d01390390080c1d100c10103005480d85401e03030141043d036900b810720040e882c1075410b48410f031409000781d1012412002c00420001400310b030082c0280f80c84800c40107807450702c8282d00c0306c0ca409944c80901070060101d680c0800c46044040b000c5800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 72154804 1250 72153554 72153577
    0x308090709020f0901030606051c05090f032d070b0114040e0d081506070213020309010209030a03210603030206070e0f0409031d04090c0b070203070e090609101e0f02 73
    0x55414203c0ca8407042d07a00700e4078110340031a003000f001185060007401500c1b000424040b0803c2c3c0141151540c1c80541000740101040e03004207281180420414001444808908107410300641884c10b15516441c0117900c24040242062140d07900003469010264110f03a00e4600180c010f488040020b40208103e4554240b00d105034140c903180d55800c05002846103011000000980e6554000d002c00c1c0d104009000750b0100c0300d403503201d5481c00740e40d0195400c82006000103040c040740f003011a14003140080e042d00418925112600c1c1030107414002c050349207000350248540c510355903020b0750b03418002d0012028440010f07064840c0c5c1e01c400b99840d008040090040c4285052400e0280c0083d44904c0c0c04002c140200e5405085400c0901511030700c180d11505103440b03145002c05010980d0002d901c100d0345030150440028031100c00d0100300d40074031445c40192003681814980d851808440b25180189903042041000c01000050f83c0c48080c50f011940c045200c50074403001c08002d1040604010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 72156054 1250 72154804 72154807
    0xc0604150201140108030703030207150e0303040b06060a0905100c0203010c032703170a0e0a030917011a060c010207060f09230a030318021008090d1704030809070902 73
    0x506800490116600c50609070001c00c0405455060000d800c0c07030902881000340d004212003400039100f40c0c01059054021410504040943c4403c0c1098074886081000c0550001c018030084c8000480e40c1c0e1f40103003045900718039003481380c00c0140880fa0395200d901d101e224140c80010420b8001d0100c0014254010300802400c400ca41c0c000d4003c110741911404401c80510b50802c80d0708000159402068140d1030b074441700c0d59580c0214289880003031401d6141d07511403c445503040001c000790002c561090300d842c040d15003881e890b440384211410b4006510f0303042c2100b4400244d0300341c0d072140102d0f20940b050780d0354201c1422683c0c00ba10507118020040b5280c010b80440450240c2c0c4840003c41c800e91410000c00c1c091a21011000c0359441c40340c100da00251000c100086c0a503101c450500d02c80601e03000b235100d59400023008401c60880103c0896208001c1000c140c005106400c11b0b4138090070502214941810058810b8000500003010b0000503808100350500400c0103d0040108a8056 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 72157304 1250 72156054 72156059
    0x1804050a0203070324141306060305041203090b060f0111030403051c140a0e0a031b050109080304030b0f04050f06090a0218010e1303030209190f1202060d0504050c0604 74
    0x4030080d4400c64038079001034a04202401c00205034404028464900d05000304c02070b051104920340580125001c580c88031020024017041a01802004010021030310300282901e040c2c2011400300700803040740403c0514101c0c80d500007945d0100120381210081d14a0070140200300b0050700c01854001203c081884049400020041c0c0090360000c02c8143c2022a02804100041540d2036001d503c2c1c0800041e8091202640719440707800e002021a2004102c031040c903549449004552117200303000f00d960003020340244095600002100001c1403080300541c070381407542d01d40351420800076004009601e081c00100d0301744101000451b514010b4101034179030906001200030b66a400c0d10b83d049024001982054010807440460f442c102c03400b0f5091100d20381c4d84d000704180040f2030f1840031018540c3c284611011915103400c0001646154401e84c4011824030342240341131a01a40b1441c084403c055000340143c4940c0c080d91450380c4e0103000800c1544079407800a0410b841d071406580c02c020b021500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 72158554 1250 72157304 72157321
    0x5040f030b010f05030312040b0402060d02040b090a0b13030f0218010e15060703080403050c120408030d0e03040302010c03180b0d050406050708070f1404120f0b07020303010e010506180405 83
    0x88504a07015071140c690f0340c990391002d050710f9010720710f13025600321320306000280418807100c1c4c041d074000d100411192401e003c0702103c4007281c00541050f681d003440842c1903500782c10b041d1050b0014150380104141890a041420402c2c5183c2d808000c2c06111690054030464441c9440f100d40c140d074510a901440da143d407050b5245110880f03000d80b05000c0e50717440c40c0050400801b01c81c2555010307945d050341641c03283c4083d80c2952001c4600d202902c0760704001c4260204410181025200b0400034541e0b03400c10451000a0f9620101c00c1c801d603800c100700400050303800940c1d4170001c40d8107040499070011400441e01c104201070f448000c880c80300040f0044040c0c05580214800ca10640c41001291a142c004481c20101105e40340c001c6114002e040400e02d0044c060b02e940c0e8942000d2082c170f01500e4550004140000100c02ca0300e044043c85410100210b010240fa0303c030006100945c1550300d040ca941d200140b06100c0c25025aa0005104100c0b240042c1413901141000c0e00600207810900e12 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 72159804 1250 72158554 72158573
    0x15160c060e0c0a0e0c09010f021e0616140d15031a0402041a0a090e010209030f0303010e010605160204110d050f010305010f110315040b031603060c08060d030f05040f03 74
    0x115842619299004a130103500e0980722401058403c2d48582441c2d00303100103503800311032180c101d425403240c02c1c00c3e00c21801d14090554100d4281e0009040e96061110400070002402c5c2c03002000c7c4181c0c01c5030055100c101c60159103414800b00310100703804425020703050320807032580c1000d00049007020304a500440030024040c0900d1007a9410000407550207608920070740b01c8105280d20111601041101209581103005d860180744001443c01043c100041c0c50a805800d0003c2c0c00c0d003020004000105070001c05030b0042c5100e05009140405110f03d2400c1001c03030a0000b8495940c0d030b29180310104044040e80c1d03840d00d010804100e64100801d2940c5420024070040b1031640c200b80c051100180305002c1e0414800322400705504640721107072642d0b41d4205842000360030981d902c4011015903001c0003604946644052904040d60650601c10156003051070900706011541d030a100440d01c0309584a4070941c3c0600d0701c400b0503214640116594070541d80301c820705001c51000842400700c1d500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 72161054 1250 72159804 72159823
    0x3020a03050d0206060d0b0402090606091c0b06030c09010b1c02041202030d02011104260d180f0605370f081003020603060d051c081815160c060e 64
    0x1000c88104d40d841c201088484088004020b000c0c115103804100103081401441c0c3d0000c00c0142901d0801c0501c0021495080448440081482d1400840b00c207104c480040107802c81801d801070114180c400020640c441e8040c0b1480b9042c5400080707500100f0141003001403101c2e074181043d551240e460002c0c7c04140144403061f4401d024005c00032901900521800c1020100300e008141801c2c5080c22040403042102c0c800350110b03000300b8000100b480c09000c08140417130191903403160003003c140340b038070160003580001da003002849105110b401d070010169041c80c00d64800b02d071a80070307445040c04c0071142d42c510500800949130041034144c98008041d0200c028142e03640b4410f50395019581c0c942d001e42c0d07100c042c0d0040b40c1040404c480b030410842942c4418014000c982ea05241d144c0b040c140e6642180600c00003030907108c240800310041e100b82c803a94a070000d00520200d403545080340a10302000e00300280400200b80ca00040b14001c0c0c0b0312030182d9030010410426106141d07403481d11201d501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 72162304 1250 72161054 72161057
    0x6061401080f0106020d0311090d03090f090b0604090e0c03070e0a151206020f0f070b040c050d02222a170103120302030709030206181002030c06061903020a03050d 72
    0x1080059603203016100003d040301d9059000b40b41e1a909400242c000300242d0a440300f08141c200100b04507510f44a1400240c0b134883e45c0c2e0013452914209240c840c0c001c454115070b13046c0303041c8401c0380c0503030350f50708141c40984031000800254101c011501c81d01e00000c43d942141c060140141c00520000c050003030314030503401020240400409605030114140c540e000703040d900c4514810b0f100c00320322554060a90352490035402d901d0800841540d0b00300d500002012505034400d02d040204018808005100174041a18115840c4601d64001400303141441d4180da00600309082e00c1500144607001080b1a8103030304043d40b070483c19021210690003100e0100340c0402c000c1620580c2030820500610b041781c0e00556140030480c0b12007001c9000c0e44c4007801240801100060201c05643d46000418400c1005605618090801414000030700c903208592130a5400500424000c94400f1a80d283e104100b110008012171100014080349400c980010b0f400003103007c0c2c044100000010200c140c1d540c0c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 72163554 1250 72162304 72162317
    0x3030e060702010204240302040f080a0302011a01020303071409040204170105070e030d050c01150b0d06050a05010c1e0506131704030206040303030e0a171309090f02060705030706061401 82
    0x428606901303074440c2d07114008450f160020302c41003c091502d00344d05040140c0c580036140c45e0f07640e070710502c0d00da080e60017013410364100702202010550240b0a000c0c0d800f403003c0348003c1ca420041c0020b5260b002c0108803100b4070442d001e05c003100f52030b41c1c42102e6400c1d40c02001103480340d48441c6a001d8083c0c004514500641c0f034074000c2000306004145542c024000200240b00c1000c40c002c1c100c840c0e400030519040300759201e40300700001486610081c4083d00005160988a81e100843d070030070754069a0206004800c1c0450500043c1d1384080e5080d10300b038202c0701040c03441c0b011400081d04d061700c03d80090031314003404050140340008200b405403800d004815103040c9841c440c0042341540705c0c0b4400203602160401c01000081c1c000e41000c070b812100c030803c1d81c121602c40e1301d0340400c0842950ba0540c44031400604103100074000c1d16000094400800304015041140d603421b504401607440c040e10a40003c00c110040110030002c440342e6560240f001d216043e52075100741c0c01c400ba0b0082d1540880c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 72164804 1250 72163554 72163561
    0x30c2009010909050606060c070906060e030d1d0d02030a0b01120b0a0b0d12031404030203040807060804020d02061e0f03040c0504140411060409020f040501140c0705090612010903030e06 82
    0x4a80c090305043c2a040f00c0504140e480d62000c000b03407540041040d140c54021002c000980002c1442594010100c5440711401d0090324010581400d10120701030050110009144204e2907a464820018103c10b4403041c2515500740002840d042104e8402480c6808250000c2a8a506980340c035590b03d200746c094889a440b00303d44a01600c1d44070500540012100c0d1403400840c006284c144a03c0e011400c0c00160545003c5400b0255481220164056400044c0410040004000c0c41004042c03905d440401030606900050032045030460281c8078070f03800b140240e08980d00150700042d110074081440d9942002c800c00c0e09403500100d4043e500c8108881001070641031a0044602840c0100d440708250742d900e40c0c0307803007010f0403199046801610078000072419079010b20061029600c901401515a4503080006202d0700c007070203400d450740c0700a0007a00e000500c0028200280c0c2c1086038034003003e540b0701e40850507444040720220040e6003414101002d00d03815a1041034440c48107401c2d40d00658 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 72166054 1250 72164804 72164819
    0x5060c0d06050102061e130605150307050a06090b0f160c05040c03021c050403050c0d03020c06100303090623070b0a0b31020d060815010e0705030c07030c200901 71
    0x11003129001c90720300700e404180b5980c0f0b10600d2000d0788012140c02082507c03525407103500880c2c904840000064070035502c04d1405140c2000444002c1c03900711685000d1382e00740b08c00100f071010b152144510814001c00c04000b013a00b00e400b40d9444952000724090404624281846902c0051180c203001e0f900c0c10310700140d118464000c84003541002d940038260400c041440034020314004109a00300300c030912200c4041071050103440c00c5e1070956500940c4030300c01064141e0400102420100d902048520b0030000603030402c020324119015410301007040850086500050114140d61285940000804004200c42110280d024000350302003080014004802c0c400205210800ca66a280c58440d1501021720b811800f5000030061040141c103203102c3d09001c074141c070313001d030041031184e0015003119943e00801c446041c014007407402174001a04043c00050001e1101410062301d41a0004140f024035004011191403181d20941003800000f0003845070303e05240c2c54044902c80c01c020000000e001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 72167304 1250 72166054 72166063
    0xb1b0405010c120908060703090c050a080a02090406060308040e0a0e010e0705040c09050d0b04050613080702011103070b0420030708060c090109080f0106060e040c0c0b06010c05060c0d06050102 85
    0x681040e1101103101e40315490f1840902ca4900400c41000b0030100301141001051101d18081c4403103440208810600e071900184038810764010500900c1c02180400084c1030000e120485a501030f100c0d05a1b684032400d240e8003030849904040c1907407500040c0054452802c1c0c0f2074504c0b402840404010310052070312954241ca5860340d85074100c0c0c1c000501441140f034281d00103506548181031201405648401181c80301305c1005013613402c2c107252001c00007807140c280038881c0d001349850b20812045c2c66a80c2c4034803050094000182c104018103a00c03c2078403008204440a007038008640044034945454562a05038668148181ea00c1078521054200d04001581c00c098402c0c1d14044d16407595130101e603405542010845604001384070710009803400042c0300d444010a00e100000c0303040390400e0340242c03181c0064040c060003079180004080c1800e911080002c500c65002c002c0c40c4031521207000480b000026420080c04901034202440681c484240041980340d50106090101d0b69481c0b00682c0c1300c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 72168554 1250 72167304 72167309
    0x130815011e0302090702100f06060f0206040803010e070e1201060302010e180f0a0b100306030308060a080309040b1f0806030708010501080304060f03020f0304061e050c120604020c06040b1b04 84
    0x44001c580920040c60060049540541e1601c11170708100f108541c036000766100c890700085040c0ea2504207003d05c0768000e01d410380034203080c001016039003801e0761601c11078801441002000c051070380c0801d450381d2141e0311540501c1001002c2903403244824608500808882c1300481c0414a1100e203801d0604221080380305200303101006070155654402643d00741d400041c020785626682e042480d0190342d0700050402084250354000070100d04514014090a9010f0b123040d1054050076010420703414000704541a0180660b00407488502800214940040780440c010180c546083d00c030078071952006400c1e105100c110100c07528140c2da01c01240c220b172028027600b02c442d0020082031000301d0040308400c180280e1882c00514042541520a20301c0e0000d9400b26011a162407070761003031910094038400085101d0800700901d0402c5a40c0c81454410800b80903100b5000c64001071440d561075059030807088450341034684502d41403a0906c200e500484808903900f03c100002c00c0740c00c0c051000d50b4103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 72169804 1250 72168554 72168599
    0x240509090a1103010e0604120f020102070c15140c010e01110a050403030f0509061804051f090903260403020609010612031116061107080606090c090613081501 70
    0x40c809015211900e1801003000c0b4981c26640700d110b400080c000c208900e03840740c6e02515442d01800659407000340041441c0c0c45d4401160300600c030103008540307484001c0d4100c50795100e42d405028050f6600740c4250711829081c03640081c01064083c0c0b280303019005540308a1240d0005c00c0000410717840141603001d8031003a11b0005400303110500000c4c3c00707030b0300c0f1041170038060900c54102140c1900180c25036010a95408494038244000310550500e070042d650043c6c0c4900d9580452501e00b407078640c80191501c52035101a48815045090500401441e0801c21010400320045000340d0b411410310310042c0c07001ca0043c483c010000b5075603038041c4110400d0381e24094880b96032003c01c1d1421200c0c0c4080c0305450480d4001c1c1c00d92844200308110560000b06141c1e1070b90302c070740100000071078101080c0e684202c549812038020000300e5500c0c05034080e8403c0c4040c00c0691500500400b180d514090520f8426005800305004190207000042004140d05e040d01444116a215420b02036061000c415004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 72171054 1250 72169804 72169813
    0x80c0901030b0a02090102120d0c111504030f030b041103100f03150b01141602010906051227030a1d0a0e070807020c04111306080615180424050909 65
    0x50426003e40c005241a4605104640071100034001c0c061240e8010b40d20ba54000ea91340782d040c1d404076040f00300349034150701041c041c102186502510b040901c2008000904100712501c001308014029131203030641d0390014004000c420040c00c90040b5541c410740d0b00c0070220b50650800542c3d1503580107920240da03401384064a03480c4a60f002c00d406420702c2d044039818041c600c1d081d170021180075409403004603504860300810758804e0001602911540d04444108071080200c180c89941c01500f19030009034881d0710400803135407000c1c103540c80741c8034001607021400009240c0a4103944032203501b07a070318000c42c007003052a18440c0800680e900c46100d0b09280f5481e000000d0302242c0100822030340840c090054441607200140000e0884451070045425270344003180345182801c070003110002a0440d4100020315080c640d000803410044070000003406c14002405103024150040200c0648030058001d212054842d14620381401221020000804408800041030b01e0316044040c0201b14420192 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 72172304 1250 72171054 72171061
    0x30a0e06040c0b2d070303060e06060912070305010e060108010c090e0a05060a051c05010b03061302060706060918050d231605070305150901060305030301050402031504050709080c0901030b 83
    0x281c8154002018902a010070b024015100c00c01480b901051294038284e5103607181400d240181c105c41164004030f5098540d00d0400001f511000115000c00c00101c91700718004400f4002c02d40b9010320f03a00000d015500300b040454842c0400114203050301d00020003400001580c0d4011100b61403284551074402003148082130b02c02134281e011a4102c100a030640000646a201003440f00406607808035003207240e001307120140f00307007032041c1d24004000310042d21090400720804450f480700340030040e22600f80090b82c030040041580c46400188111001402902c480f0381c190140c585501c2000e81c0d4900902c000f41c007030980310b4049000d030030304402841c0c0603540f00d800031407100390461401c0110100010209401003002004580025071252004212051454003003920244020b031410303045030704201c82030002440100540b41590025100180c49507100303a95000e44c6154400c0041d0498904820300c00000e501c50011020f03286601c08031050f50b100c007028000e20103400d100c040d00030160303100070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 72173554 1250 72172304 72172319
    0x10b0c061605070203010e030c0115050609010e01120f05100503030c0d0810050901030f020f181b16030c020102060106020c01090b0c0703050304090902030c040c0c020d0201030e070605030a0e06040c 87
    0x1100740701105850083d00f001100d0380880e00b10380e016204155213a002003000c040c840d0090041600d400306130b10590080034681000700c0c03004c0c003910f080c041c10b000da40302c3e80308640d9125415548107024180070500c02d015000e180c0d040200026102012004840b56004c5650b09002017110111032030200101000c3c0070f2032354115104440034050384800c0d0040c1b00e0003d45540e401040d90f02840c0608140aa01000c0344100000b0406100b281c500031003e540901c052080030203082070f408000002d031103080076800c00c0380b400f561288580d1850903ca402c503042c6c0038554040410880c06100f83c08446103641c803000117076a10b4410840042c00141c00074020302c040401c0c403003d088032103d420101c800c41c94070383e42c2d0b417070554020303404c10071a0503500e03c02c88041d403074100039142001505441c100421400d400000301b02100201d40640159000382c0406e0031039109502001600150205a6284a850301c0c0c008026070b05c244e03044602a0304001b0f091543c02d40124456000d41c6e0b00c08035081065103413000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 72174804 1250 72173554 72173581
    0x12040302120703030b0a1203020712080d020f0a020f0610030212010908042409030b061903020307090906060e01060f0804081204030905040e010501051507170c010203060108010b0c06 80
    0x214118000c00000c0750307030752142401070710205100740c5002c40c0c20b010003800d0001c1d00e01540e03c4200c111340190380d001d0119801061180c20f40740040850284005036041c44201440380c58074405280d40b0000701d203201050300c0030103000c0144040c1d090322480d40560004a544600980310b000041c208650100018901030342a00b0f82502d850300041000c241685810100390465889501629000110182d00508042c00034401d0400da0a02400240c210380303c00e40e082500500e0103000f0341801d200c8131080d0500c480002c005640c0101165003d1b51150701c031034060f080c002001c994141c14500e01069505031012801e0603506969101110107001e00b41c101d4052002800030359103d601088171130945c1d0020308400c1c0c8a039000380c07500b070800e80ca0b12040c0021103507580558841c60f454800144000c0d5200c48001340d0940c1c40b03000341b585801d05828a2800300d00e00710014201d020b00020105130201040d006148246400d0722400f11580e40c4d40f80410092040315070035555138009800181d2071074244039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 72176054 1250 72174804 72174811
    0xb0103050103151d07060905191d040f0c030305040f08070b0901080601090306090b04120206130809060d090609020f03030304032a02060a0305041209030201020c1003140c040501200312 81
    0x10541c4ca003680b0385000d039506045660300000d00007441e841d0144880e081c9500d240070101d0a02c8401e00303010780352951401560ba0f6041c0441000c06480c0c001c07a0a02c0200701c6211789164002144124860b07032450080c145600600c0b603a110300d4010440010303900c00104400341203a00b000400c5190002c4400110b451550007000d50b07041c01140304002c00070405522030340030101d1140404100a00302400d0444480711240069011544645c04100c900b400707201600e07001c40e500100407038079035050100181240c003c03030180f510003030300d010040300601c01c10f81c0188230b00303034000d84010355001306800a246d1207100c1100c002d400316440103e0b2456118080c1e003000b24803203131074507082d00e41d02440e03002558540c40180c0c072400003502d400500013031200d4140c2e02c1c1d0038640c246c11300e40340c101e295a0001c0d4035120300003c0795120384200b00400d840d6600903003041030070508003118071800d46018104856107400074000e03a40000e00030005d8004040c05610a503a070302a0400085051494103c90f455032003100070b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 72177304 1250 72176054 72176081
    0x602030f0904060e09030a140a1b03091a180102030304081606020403020d0308040506070306050a05060315100207080601090b13050601021203090a0308150a15020106150c02040b010305010315 84
    0x114400103884c445004000d020b00c0c17210000d9565030304003640c014015140c074946a0b4844c00300304114065250024401542e00c1c203c101c088100c0f08080c03c042d101101c9aa00c19440103000850a0f80c800010070020400a00094000e83d54003550400490b541e000444005080c1c1c14200036040e503c40c0b181d4003e9218a100303800261900d51290b021510142c001c1108601240359075040c0b1041050600919512044500d020004c091a28002031f980254900c5040e01a1000001103a401c101240c2e00351805400544008400d01440000a40d103000c0d510500c819070117050004650380040d80a40304001100400c420701e802d40358000351006085c094280c90641c419035442140d181c50780c4000c0e621440c0500083c000842e60350a024200c1080103020700c1e0108191a900b28040d5200c0d038031082615031200c00540c8502800005034010141a00407044802408802940c0950321580c0b0028051003510b0900408000c0f0b00150240c0c0c9080c0001031080c0100c00661443c121141c3c040322001000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 72178554 1250 72177304 72177311
    0x40b040e1b0a0c0201080a0c020c0d02010c020a060e150a021b131e150819020316090203040312020702030a0206130b03010f03030207120503043c05010305010603060602030f0904 78
    0x11224107400da4403040b003107070210b400001e49909568101d0030150b80b00080440900c414090900029201c0c440c81d13070094440c0d0107401c2c00c103042d64820b12440400030b901900c12100103480d1800907183c54409034505104444007038000707450805035002e41e4040f44280d0000c1c0b2060b40140c041d0384080d0800d49039990002c3c07600d0041d0381551500d01070780030450940c0d00320069601c10816440c080d1500e94000b203044a840920402c8151000248484800c03c1050814090801d0f44000790425148401c04078406c50320030320125010060740c0c02140a00d20a44401004807007070041401031b4000d011020f54560000d14040c009800c052009041440a2380b41c004103598440141044030780082e0031040b4120f070201c2d414001c1580401050004d005070700c01a0803c03400c6a07452503507900c9a0b02070460b0340101c0c03407007107500004107a540700e80d40c5010034039500b13242c0d01d80c29583d6028007142c45210300080c20702000043c1e49003e8454001511010341c040c61410899801e8031003154041440740340c0240e038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 72179804 1250 72178554 72178591
    0xb150d0b0a0606020d020313030803040204020c0d0815011b03080a0e0a05010902030c0d0b010b0702030a140102030702150c0d020c0313080304140a0b0307111e0d14040b040e 76
    0x100d40e40603a20070580c403400020100d05115000b858a0f04c00041d0106541c0b0030402c0f20701d1903200252410842c1e9019001c2c6503a6034851001c00d01034060307445450b50071b201c0e12a910209036002070900b0321980c1e209040c050170316194801150755598842c9100312900800500d400403d200b9070301c282d48240905004580340c0810b1400310b01d40b03000d50000303a589075900ea092904500d0113100100581310120b820300c101c5030440d2034401038200c0611a86d21502400182c00e02151002d0044c60306890b082840b2646062181c002c0c0da01039032040394070758014090302d07121482c0e5030a02e01d54580946501000a401d015194010400039130140554098038401482003200040b21559500f0103440660099074895107000000c4850840050300d480c403555201400744580c0c04440d059a500144a250070701040680c0c90700e8030f0400c003078cc903c00c190000c1704d0809410050310000301881e2002d184d544600200440c0030040e041400340b802406061001084200800c02411110b69004504041031071328039030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 72181054 1250 72179804 72179813
    0xf04030905100f0809030a0f0f020f0102030f15100212160503030a0c0906030207030c0f020f1203041701150302010311120702101d0d0f0309051006210b150d 69
    0x188200700d00400143c408800940d600d5002c0c10f80c0341c00041540040d1308040d44940d01030a802c12400880b0200640000d00000c1e0303a1007081110345501c8072500855581c1000701c0e082c41c00c01e4003103d1507101c504d5000d9012406040941c02e441100a0b03030340c050400315040c4c16090000b1740c03000c0c10460302504030015034400f0400c00e000845c060700910300005141c011004002d403806060350b0000c1c0c00d052040c85407002184d0840310f0807003070781e0303100304107004088040c4000303442502c0c000121034000001c010300c903440100c0000180140c074141c9019400324510001e419007030350303150f81001005c5031000c0000c10065001c0d8228101000c8c1d622013040c01c20020030f0440302083c02c00c4030b08400584c401c4e075903400e8040252044040c045042d07103956040d04004001ca541d928100c141c480104503c9400000c8418420b0303200480195214095031030410281c45080c02070312540c010917004012405a501c514812081000d0546500504003c00e079526122507400380402d40b021150001e141c001c18a0005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 72182304 1250 72181054 72181069
    0xa060f06030602040e0601030b030d0210050c0408030d060807080a020a090506030a08070516050f010507030e030309041e050f04211205010303180608010b12220c0315140f04030905 79
    0x1441c00c2c5183c030081b46460341c001029036078103100c024000d4100100041050754042000403110040001c0424681c8800514142c1842140c0c45004117004c00301e0405050640c41c1c0000d011140880c1c00c96507066128801591030303c18544000398001004501040345103036942216502840080558102c0042c070307101d00d08107030700031001140d40e50080c0030340003201c610704807915020344025984032200101780000600240b040d5031000c3d062003c540074074541e0381d50070001c49103a194054800d01088203400c0032240301c03840c21500f16104a081c84001490a81e42540d00381c031541d041070800d038044c0c08001c0f540804600390001901007000e90742010460320034500900d4000c611a035070300060501d0f44001040b0780c1806030403100812100400401400002c28103a6082000142486505459010041d00480c0120510b5103101c144e014000003404051a0910200c1e030091151440401030204002c0c12178800c00030b518840f020390380c0480c0385000100e404982c418400c0c01c1c244115502c0d400000c045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 72183554 1250 72182304 72182309
    0x3030103151404030c020103020d06050604060c031e022e0501030807030305160206011406070203010c030204050a270209010e120705010e090f18070306060605030103140f0a060f0603060204 83
    0x1805050002442a541c40d2080e50718040403071040082c0c50034640c0c1c001303081155240001e41011f8010468480d10000e660000c0000d040040000e540c0d81d030741d2580075010740c01004083d4042010021248014462080d16110104841e8040c00c2c05440e404000220048a61040d107010005014580c26207122441950302031030280c08015180c10300f078034006050702d2000786078122a41940a60341d001503000201141501d01000c20040303400e00714408550207001d00080030b5410341c20028180d001039055030041050728025100416810707200c3e074407082240201000e03205404c80d802e0b080c0800240d01d45c041d04194605240030b04000c01030400203920154072841031300380b40c2c116513401c00c001d44e00702c1d4440d19190700039a4a038015140c40b00405d90154070003400b034402a0105441c05042c6101408404007441d40118104145a203500c0020055003013400121403030f01405011203446c50000414106465107880204448522a550b031005042d82860300d6440075243c1030040000740042c0060f201 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 72184804 1250 72183554 72183563
    0x703081801020307020112021b03072108011d060112090b0105190506030402040e01090803090109030206011a090d03030b060c030904051003150b060403140307210504030f020a0803030103 82
    0x8a410032404248a5411200c10090566004002c0280142d07080800841c80b8103c5103070058440020600302148020104110441408009015000c1217000002202c04003140100000d8144500350b05894000081c01195490003081189014511f10f02e10031603480f40061401c14a5540ca9101c014280c4da0814411100048401c0050040f81841c81e14000c21100101c19a85234520f0300010070310a00c805070001e4000d03500e540007580404000d4114040161b4041000340d0340b454182606802001c8e4200c04400600803400000354000032501c20300c0c2c4041614503004c0c5042104c0003041001e4401010807018140c443c644044159980b5000d4090419220003a59a03800004c08000823110018a01c01e0070903482c1400f0700100d00c0380d2019140041e002a4002071409508001444a001341c1e8001803135100010822070b20144040040e241c064450a4020f4803500840c01a032220480d074180d203000280240400c002050040782d10148280c00604030382d11041d1605c16840c1185d109810580d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 72186054 1250 72184804 72184807
    0x1704060c02010b100f030b0a1e06080108011401090b01020708030c010c021c08070507060b040c03091a240402070b090303010f09111b0f0a0b0a0c08040206031f08070308 74
    0xc1602070041c10300080f02101c0c81964110024400740044803900d507817604042e07907650341554035250303074180720007802d0700d10180c1c080240032107400e05076008180513400002e544203000240303141c014002d00c80b4800c0e044164446903828481800020700c58052054114800e448000803064401e1000308124091007001080e0010b0034030340070b494101071030b00f80d000e200184c47c80e03024000c3d407120318660010024a4829590042400c100001c0d00e581080d6690241c40c00c040d00a4694140d400204000c0c41103503600100d1018448406400302c2c1240c0503403007124081c1841c000910341c0508450045c4000740700508104803a11072036502c6804595400484d44000014400070000b04031000081c1641d500500071000d0012849032a40110000d45140c902503024050303800700240408900700e02c088d021500c50f1507a50401a005090942c0c4e000d40c03d40c50b14000340b200500c40c0740c0c202c1c8125000380c0203d1640d12072400302083ca1356403d050484440b4600c10104100c0d0080c040100250300883c0d806 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 72187304 1250 72186054 72186071
    0x60b0103020910031a0906090f1308041503060b0c0a0803070513090603050c0a06021506010306080322050a06090e0403020f070312021002092d040c08090c0d050a06020703170406 78
    0x300c000165042018071404403c82000410f544518230154003d403c1d0780d80711a1921b5882420380e0703031ba4010000803c600404203012507182c0c1484c25010041d0345a40d01401256540d0b81d00100500c505414100107400c50544640480d40c1d5000031a00b080307052404174502148082c01c4070b555821a04021010354440c2c0e820018003000b08021031280c1401c0f241401c5c0c107454400040d40d10131011844046542c92140000c01980c0a940103c0080c00704c0c8080d0380d0f035481d401200741010320091100b0010040051000305d5a8100003035071609803a040d4481444103400c2100440404600038021811171081544090078080148890001180b056202d60000362541030040e080000100141e401c6901c180045c100030754410690a5030400ca4540b1504040929110814059041000385412501300030924143c1548900b040d803142c001f003000d131141002801c08004421018400140455006444c07240220360107a0042c440704d48a03007403900e80c80180802d2258840e10072181a43d007141d81c3d41d142c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 72188554 1250 72187304 72187331
    0x234030510060b033903190608031c02030a020705070e0405060a020313020f0102070b030903130e010e0402060c03070605010e040308070906020d0c050c060d1b020601030c03060b010302091003 84
    0x2c2401810009600d50b040d80b40040c0744102a011100044100300c0700602c0d40783e030803961840c5481c604103107803600d42e17520f181618404c0383e0000c40010031115580381090009103441d02106549103100d064020302501c11003480f0a10107504090600310459500b0468040001d00030007000008120b0075100f19640d2038503052403802d00c40002c00d010700c0b50713004204100d242240c00d00e880b1a16a0b04903480302440d00c0010040b8605103998011100302140001400802c07100080a4003406c1c1d007107030500004c181c654600402c414400e204d0030071001e0908021500515241e0041e100c481c402c4000c503410445a62a070400395802a840310902c000007206000503d5409802103a000710b01781840100c1c03515190009580d010746030040b000700190500c03001c2c10000107200d080380404005004a0b2545841e01c0c1c080c004142010080343e0210845000038440d0b40081207079070499401882c0381881c5491a16510b003d4440440d20324101b41e802c204801c410f903900c11246815052947c0d00044409e0130019 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 72189804 1250 72188554 72188561
    0x30201020634020c0307030c150302070b0604020708070c03060209010311070201090501050a03091b060224010b09010504031e0501050106090e04110d0803011508070c030234030510 79
    0x3045020810b81c88944031050318004a118910381810410b081d40c190b8208074100032070380848903494041c80000105101003181050300340c401018141d1040111860140d00304c0c440c0c502c005000315554000210146801e9000d8801c050103040324900d044103e5455010901460b04125103841d8085406002564144035205220300c000010134600303040c5400280c500f100c0740c415141002070000307800850038443c2e0464290700c1d81c490b2441c00c03000e181c400c1c2c4d00410241802100018801d0100300002e00d1040e02c50104c1d9490790050307100c566400c11581c0380e440c1c0d0004000c58180541003100000050040201072000758003086190008403540c075000c2d0a549040e48040304200d00b2003800e0108241011085030082d03800450700801ca002d4070003003080803200315805000c41402000005180e40c18810350484400903541d814100c0d83c482409540036030001384041c0060b480007a40001c0c80d00340002041d4048000b483c103006c40c0f0308651946407202d619810032142e54001d0050368443c80c18602 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 72191054 1250 72189804 72189811
    0x50616140313020f0d05030d0b0f09010b03040606031a04150506030c010c020d05060403080a0b0108010303051902120a03241406030c0d15080c03070303050d11040801020c06010302010206 82
    0x40c21a040003449100c5000d18000504001c1c401c03584881680e00310340d240204140d40900103031540f420207909040581d240d810200443c0211410321010b12124548101ca440c8007013001040d60465908000420419810040044a103556a0807010000c2482d84502a2030241042d01d5090303246068513010458400e1240301b8000c49042000b8400c03140d4010888070341c1510b0a1a20b007040064600000f0081007142c040030b000e03070082c402071200b40769010f140d02d41301e910718801c24840035958000440380c4410901c40540011028407030504c4034008455481c1c1c008000e84111400c4092580101440c0e03030011580601003683c40d10040c000110417042910354640b20b44808004034036010300c400c5600811810544542030020024189809000c1030701c2d8070039207000c410080b001c0ca00b1101e032a18101c0e1f0040d08100c0c4a441d0f20b082151900003008820341c1d80c9565420305101000c516840500305000c5241c0d40068144804030710070b0401d00c050644010190000c0080c2d500d50300001e8200b00014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 72192304 1250 72191054 72191057
    0x91b0903070923040506060105180604060f08100b040909060905010c050a02070905011503090c0b0307050405120a120f090314060411091b0d0b06030a0f11281b050616 73
    0x1401c0002045c0c0100b038031540b14200307080007513a13921681030a071036000d00d101c00107074894400711300451143c4c1e1040b07880d0580034590319030074030544400340650f8000b0100d201c1c0d50a6041c0802090284080a03005001d00c60720070540880d051042c2e40d5054251092006008000380000c01c00a0202c1d07070400c00c14008040445040202c0e505001d0140b485c2c0402502d2801810b442e01542c83c100a0858021001000304094042e00c909081030002c00c030b40d00c28400c45118034020b110b0082000380110711440b003564494540e40040082010550720048904036440510003024800004280e250f004485804520000380400c0e141c94540000303070b002c80d0325440c1c0c0a20000c1007004203a044120000511091007110315480790040c40c40c0c0000340c42c480b07013003a070455004024003842d08650b0300700300c60003080000c0c00e000301e05d050321a007481c60054000c19880e580100c045140c1c13940424007900c41c200e005241c10a41d600942c02550580c0341d012104454a82c040c6e0f04216184443d41c8049600c001c0c0b0307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 72193554 1250 72192304 72192371
    0x21209010b090a021312020a03080a08060102072301030504020310090506040b070e103b040501060f090b090414070f091409040602180a090b040b0f091b09030709 71
    0x1405c41c89108603880c0c080c64107002409441c00c0203640d5880f043e10004d41e448229036684010700c1000901440c0142c0703415000d48500c0101083c0040301400a80580c080050603420098580c00110060319000c1d00580e01402422ba00320707624840da000b04c0300b130310f070280004003614105842c19035024070b4018846010410340c42d00d0850319507079140300c880d00b04040f442c0014004c491842c40f0b0a1345030002e0901410365020405206d00c03600000c1d40c005101400325001c0040c2e07a600d80060310b050b2581070341d000020f0700c106001d2001d48640700207002e0082c409000054000321018020900040541d40180440e500c41c2d400142d0603409068079015041b2108120803030611840412001a00904001d0007076401007030007031010140740c7d214030301e0410050140958540e28070b4044001c144042c1c400c0d0160b8100100c903007150401c0c030440200140003802514569546203140400c5c1807481d00800e5880d0010041202640c2e0200b2106024008c0d031040010b441984840450040310070441e40b8180f181c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 72194804 1250 72193554 72193567
    0xc05180415030201200a0309031203060803031f080a08120108010227010216030b011a0304210516060c1b03090608060f030708030904230c0706021209010b090a02 71
    0x80315541c00322542820710803070140400802c04040000994901c00714429244004181a070104078081124007130a003020900301c2841c0100c00361062401010350b00e030700400201300c4c900426040c0310303032003240c0d00001c4000c180c4030300d04079060004101040d0703500080400d50035918500c5a03101401002818002c62a100912448000c0b110064080e20688800404035a0042c0d000340304010030103a08282c4000a1500ca00c0d050072000c00c01e000340030140303a00e42c465180703d2514400700c0340180e800c41c9072441d4400d210030401e050403140d40d0b6248204017080c8041000c82401807038405400f403003441c0101d04c042442d20300a00e14107000d8200110140310300e03040c0c404a50001c1c0c0c81029110780b0302e000300340c0d940c038503000c00c0300390001e060100e030984202132000034801d01c00301c040e003590131045405200340391090a5500c01415001c441e03864010769007022a0b84038000310001d280d5580b02d0304d8094100310040c11032600c210780c00c68214215035124149500c05140c4030030a076030720080c442000c604045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 72196054 1250 72194804 72194831
    0x9021e0705070303080c04030b09011b0e010c02090a180302030a030b040908030411120f06060a0503030405010909180c080a0b0f09030703030e01022203030905031f1a03010c051804 79
    0x102c03d21010f02031103400c4011605079041c08003120099600541e802c15681820240341c2c1c008c0c075241d00c1a039091880c03143c0c00b0b581c80d0301c071351000d811101c0d0594a19041420607020448803a078041c1203521015030790b907008030035001040054200715000c1d80207191210b1001101030103030742400c043c0f1445a4a040c204c0e40c0028003480070f40b50040e40242a0b8103072195424089003c0440303d0f60002450300ca4001c400e04050000070b9114806c890035500c001c01c05139603405059681c00366000b41d60210303c0030b0400f880f882417507900610104074854820b500c840c803252542c00c7e913130f07036550050900c0e41c110030501000e01c801d151a040c1c010b102c41807000340f039251030601c8540f40d00494400038109a1110160303a5030356800d40603103600b00c00c80c449103c62805462918400c0d105948000c074085220508005010316001c6803009500c981000141e040e454012200c800600d83e00c01d10029480800c0d24000003501c0910810030405825104d840e84c4403c00c600d0704807104103c40c1036501c118141541108044e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 72197304 1250 72196054 72196063
    0x4050a03060f0b060d060f0b0a05120403030912080405060702120f07050304030204050f01080f1603030c1a0a0e07080304030c0306110f0f040509060103050f040305030c04030c09021e0705 82
    0x3a030700600005400c0b50542001d00282410500642d40b100d0086030303e01110f00746a0043e41140d0342c0b0440c1d0307050150b6512200d1954094038840da40450001d02c40030414142e243c0960398014441c0c540015007002941e0b490306000c0010f4075920008541608020800208100454000c4404d000600705201e511a80c2c0d10a0b00c54041d01207108100030480f80100a4100182c40203141e00500a000c0e51922000c10086070707030300744580d1410f0300c21060322000608010509030040040c4400c030000c030030f085445c00c0e203049100500c120ba6002030416003a1410385c45040144c000c901c007940104440300200740d010319001030b5401480c1c841d0810441040040c03074811000702142c0c0c2c00f10011030070300c4400d101045ca50003646280203018a000990001c07a6003c1c900600680e14100c580407440d4075020011011104121a01104a00e0344c40c04180030a0080024607800703000c10203064905902e0b42d99025854034103034003256025401003021492052081d040c0f9a41c0c0b0041c089050515030151a001e60743d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 72198554 1250 72197304 72197309
    0x506120c120102040806010b0703170403050d0504030509030102180102070506090a1a0f040f0f091107060509120c06040c0801200c03040b0a0c0209010503010506010c0209100f121704050a 82
    0x101c0c9960407071400c5030070039016a401402e104050b20385942c1c1d50340c2c1d58840da41c01036004a0004001500401aa00e03122026034011034041c0c0d6a1420504400c80d81c0e402810040e1054007400402d00030254a541c003400188069a0300f086546130320740000c00060b1402c0d00503045544918000d101c0c5902c0c0352200b034201d00032254484c4180c1e01c403803000b01240e07039148035103641e8244440001401107000d242d40c260f100200c1e101000300307904051392084014100c1d0300d07014812a03240c108202010116503a074002c15000024181500d003ca980c80380b561100d80e0140604c00d40e640c01850410050003013176030018000f003c1c0301c07009001c180d140300c001004803c4480000e0703034a480041641c1c00351003003c005580141c5201c04207141c2d608071941000d0001907055030103d10032000c200000c0790702c1c1810f0080c4c0b80140d80c1a128007aa0101550070440104070091210421420b061800160b8250a0281500521031380c18482c00504060600790784500c83c9111110004038100f00c200171a841d1012071804 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 72199804 1250 72198554 72198559
    0x150e070905090d0c02180108060906070c030903020108060102011d0106090e0615100c050a0311160f12060b03070b030115020307110616050601080c040b0f06090409051002030a0b040506120c 83
    0x189403804d4800a51130f1508400c44281350a040000850050b00009180f806900004220b0b006580c1d84a4102c558450030540100042d032910000c0006500817803d15421840500002c41c0c0c000e101802580c0520241155001c030703a460f80c80812070540c1602c500c81000301c140003d804946007502950281242c082059070040f05c0380071022440c14403540c44910072542c00f5050381c1c0c0000050070000d18082040325400da0500400c0502c00c44c48000d040c4a0089035010006100c040c0d29080f400707004540c0b4503805580e030540b9034007400000e9906014503006440c21385a183c1e240e505089021031200381c01c01203681035500170490340011a1150f80e85a151800840d2030355900c041c0d40c0300c40c000a00c40990020143c0c0f2464001050300d2502103030b0007007031000c140d400b080844011001c00c015185c00f501c07829003003c810060300107141403540080000b140104104c41c2c3c5070070441034003400c990003140ca080001e640d4150301703041d61815020711030f041303d07040324100f100f110311034055612901444a42407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 72201054 1250 72199804 72199817
    0xb03040201090e04030c0309050603060a0303050309010905030c0a030801120c0302040b0d02040905010903110706120b0111060a0506040b0603060102190606050a08030913110403060c0309150e070905090d 89
    0x5046a200b024034501410400b000c84209040a14004d00000040c034001c40104184440205513803c040f000d80784518402400404054030b03503102071b505030340050005001c1c0d540f180c00f46000300d00c00304001e00100f0400002440e0940701420000c140941c180c1005803506103102005002c158070249034801d8035012203001946e40c10b034800180b41038806540083d04141001c1c14002030003011760000380c1e000d002c0c0e241d80140e80300c5031804a0300c40500b4098600032070742c1000ca080c1c840c600c40d0700c550700303000042c1880031158411b5030300c0034035282007103c92071596a00e850801c01141810f01449031200c4083d92403606600300030001070744070780044640300d8841606008040030b011081d00311030000c1c0700240c01c9240c40d03511440e015459507c03000440e070061410700000340301150b061040c804a10b66503100181800d0840ea164400b030032008518404068465002c1d501084d503400c0c01300c051040404000076a085060724440c148085075000d0400540b030441000345180e004600c0b219400740c01d15052 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 72202304 1250 72201054 72201061
    0x1e08190b0102031e030a05070305070f0c020303041e0801200403110a030b1003020103140105030a15020c01020d020705010b12070b0706140103030201092a03150b03011b0f02010b0a0b03 81
    0x100d15600501d0407600b41c107204600d806060340e404e00000c602400781e001c02484a0341d15410180c090314000d841c1c0740c00080900c42d4131284244900000c0c00362a1009068900d03141e41d0b44425a442d00e400840b410b402200e904003000009802d11402c0244440302c4250419964000d0100f40d060045210180c0b030b1440030203501c0520382e107600701000074640c003240010060a0010207d404850300d40412400310340f038a8081900380e40d95500e564100e6500034001c101ca64981d42e202c4169000940051807000e40902c817601d8420402e0016040100c5e055400580f2410740d0b0424074259103590442d00d0003030300800900c03001340202013999001e90381d400110f50750740c90803442d04400a10310300210024282c2548000320415506401c0151024065560f50841d0402c000990b4041c170b800c94100c51100030000d00c01c1000403560316411f0307407803111034400162142c0c0d0300d0003081c291078000307644a00b480031241c04d07001c805070415405011241244000c01c00c0c11003001c00310713101280b1405040c41d14003012000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 72203554 1250 72202304 72202307
    0x20a030e1309030207080d0914060a17041a0609070e0603071704060510150207060c110301090f020103060605090325180f060b070206030a050916061e08190b01 70
    0x108140e0080d090000c0010602d5410300944072078190042003034a000d008185052244074450380c0b002d45650042041e03a44260604010f10365000c81c1d1107070248014000e014291015448045224034003480a82c4110f175184958601c118000a182e54812131500703091024030f036402050b01c18542019244180d0303a4481940503540c00d02e5000b043e035035862880007004104200c542040c2d00600242a1107190342c1e0300d0f041c00240780304681015100590202d00c040084500c00c2c50f41c1203a03030340585160200950700d01e0203c0e0075261004020b8950140c1a0700140441d40e161003004001d140340c0c0780290a010152001035145da00c8001c00c80c0d503003200b10001c84042c03210321403008020320316003013468504602030040c040641440c0404100389480c1000010341006a03604407040341d640145113a00c3c0d95a846036020003440082e100c14198454003604811900c80d0910410103404544c95143c0c5240000850050190b8005000d0702040780714020320800c1d0003043e116401c162014200420102c1c040c900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 72204804 1250 72203554 72203569
    0xb0102030c0106060908070f0302010f03090206091c03080f0105030d0e13020a21060605030c0d151403100e03030105091504110702010e030a0213090c0504050907150906020a030e 78
    0x1c815a6500e88400001c0d86504a8041000c0314050800e441513244e0b80c403c500d210084c0c0e8400a07001c190321030b0201c058503109521030728030303184010642810031400001240c01e54020341181c1c9010b2031990307010801e01d90840d895982c0106001d81b54003196052102107a11355072014142c0d03082c0001000c4400065072002d00724052402d882c1c100715200e8500f4500142020070840d04150f807004600300250f603564250180c00281c4070030b038403060f00c0c6442d06040300f003061340226420304d402542c440800c401801c1c40d100340c1c1c1c014600300884c039150f00858010141405a4a0b03800d041d0f661400a81400100000c030590303044540032a0b61090580d6103003c10f403d4200885007503680540750811204540c4421005010620b000b03990304810949000103241e5264010742c0040d600c5808085000324014598000d070f16824800c0041401056035080481c0c00c6c0c2e0802d5640500381e070020042400aa41d010000502d550090b00d4000206442c0c8000030f03407106030250002d41049032452040360340e51134400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 72206054 1250 72204804 72204817
    0x708181e01030e010b0d0c0302011e17070e030a05031c02030f04030c020a0f0e01090507110601091a13050f07090e07030504030e09041407050301020f0d020306031609150e0403050d0b010203 83
    0x1092652001b1080c54101c0790341ca10382c0802c138007040b18400720b07a07040500c180400744041c0d22500c85030f144400003018400b0070407005000c84100210119508102d86040c0000300005218400543e19105407140e15401400e91080460035688140104280392102c0554907030401e400d410040303000c00050000c1404101d030364100d103060012180001803603120000b070441c101c0d03203002003c220035210388404460500720b81d00a601e6a038818401404007811540c40210110491650340c40558030050210b000400f40e002c2d2280c48540d2030041003441c002c451010355114010b03140203614075050094900410402400d244209945c40c4000350406014200e0041a2140201541b919142a16103501149031140e240036240c0501030000030182814001d8500700e0b668500c0c45800c001d0700502950094100424035603042c400d00254184c443d03000700301d410180807510760115495400040d2500030030201d0b4045051542102c0411001c2580300c0d0075241140040c020101e004000900101d26501954 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 72207304 1250 72206054 72206059
    0x9050613030b01060f03050606070201020c12071527060c031b0c0e0a1a0109032d05070f0e010b03040807030c0b0c0705010b06070507030b07140708181e01030e010b 72
    0x70b00001c50000c0d04000c6504948120385d4007480326a44001c24030505020300031000340523a000b003000944616000c2c20108660780340d001110099a940c0c00720b0105013101416a0f40820000300300340c0311544009698200b02d481080b2480c0960303141c04c4004252491b80400a01040305540c1c540070860015482030006a405c0341180c0c801680301d0910f0906031209a480c01ca401d440d05d0b0300b42c002d0807030038028854808816160a1031191442d00e0310003642500b601100d00152100c000c01d40c2c0411410320307600300c2500070b400502c0c4c1c06060066854080c0c105400c0259204000401040600748000440368041d621002d1940c13117040c1894207032012011481d005144600c01030410981d05610406460301c240150000c0c00b8805402050005620403c0385c044c00d5600080d00c02d002041c0c9035010b094100c0f041e49002d40c842c400c0d112202005400c560011900d5000c00905010392032241309011280301c1044503c092040301e100d501100909200071103e062640352501010580000c0d4403121140a02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 72208554 1250 72207304 72207323
    0x10806010b0c0102070c03031d1009060f0309020301090305041502070b040510030212250c02030a0605090a05030c06040c080d200106050a0801060e07050c03040515040815180a030905061303 83
    0x40f880e000d03100000509e80b0b0707186020044100d0b0b00d28a0642d601d24041c0b2059101d0280c00b5090030f00c01c45404000c41248070500d5107406a40006031070920500c0010b5009544040c0c449040010350f0759030b4a42c0701c003443c1c219800060300707108a10360402240d044030000c503400540180900000e6029020340c10300400d240e594602005610448013000c41c0440c942081b02e40c00ca051032000645422205901c0a909640304a06003c0020540c0e400282c0194140040f11210345a6607034980c0f80d5842072504910680005091104100052545070007a003005405007100003884c00380200709a051601844045a0341c81080c1c400f08020f610040c050000600040c000d90f4a56482c02c0c040c1580e48940d4619111200c0051121072241e0b0588826242000c0034524240c40c00d0100b042c0d0002c042e01d03120250000b008001040c2c48200040811101000101a06440d0100c0030f4440802401c2007840c01d9008244007500007540940a4020784200312291610351680c6540c03d004082c16400082c2100207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 72209804 1250 72208554 72208559
    0x60509010605030c030a0b0c0c070f030302030705060601080f07030f060906080304031509080318030405120a0605010b040f090e010b0d0f0c050105090a05010e01020c030304060c02030c0603010806010b0c0102070c 93
    0x810342024050311030540866000f0110002416698180840c000e0044940a004605030f500e000300100712802c241c1d4110343c0d0007500c2d401c0170380c110300141d4011805603100080e00000c000041c000d095101d40d0900704003001d4507200c894400207040042014007055917511146d40c82c5001030b80201d010b445103a00c100003854aa07184d1560700d17803042c00141c0351011030503501d0031403207400d014a402030795000303d8050554035040300300e100b07c5444021656250005000104150300e03500310b9444030416010042815990600700001102c1040c2c00c05003000320100004d00948043c412848200d60138190001646d010020b00385004060540d54964081040283d44d010300a501511000040c000c00c5078440c001c0d514001503c59129101070b840c0c0007400407004210b950300888800140e0641801910000e038a500000f90941d80190040000718540001c80c0056040400001000010684541d4035650522440c04c3c3e48400510440003005400110150b1149080d01a910341350380c0a049080504d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 72211054 1250 72209804 72209821
    0x4170f0f0703030305090610050d06090b040c093801020106081207050607080601140306060706050c041a09030a0b040c0306020703021515011e030608120c010c020d1b030c0605 77
    0x2074103220660020703043ca004a10255000700703542d40a910881250f0401f146000c0501001200582c07040c0d401680e03545268011031001415a4402d0388110ba40100480c103043e01413044030080625580c102c295030641a41030129030703c5075a080031181d01ca0820040d16000101d01500903904032508500444002a501416240280240611400c15191984d45203103044130b507510202d403018002030707070b4591003c83c1240444c010f503004800600180e04d0100c4540f5030f042170f10415126448501800181041131120313807000e40f42c010480f2030480d840c2004403030000303a0350100d03898068180100035001c0b5082011024060000710344c4070405544598850501a40f5a2104151840121042c0700010790340301110306825034204d07050f101d18240411181e50500903051526181040c542d84480c080b40c094410020011580001b003440c0c0d0350741a9002e600d509462902651205650143c1c1003c010a030700080d028001074070f56038007447c080c006810f04560140b40c0d84e82c0545210b251000740321061 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 72212304 1250 72211054 72211063
    0x607030b041107050d092103080a2901260109020a02030c0d0903030f0813060b130623091003080a12060603050402030c03030a090b03090a08040609031103030301060504170f0f 77
    0x5071700e5030726581c0555984c0d580c00e070714070718104108001404a501030710000034001c4080135001468018001801030074a449440c0aa6040096540321a03941c41169060b69010b00a60f020500d41000504040d060400c12004010103000f100b10490700801c0c2e8450366442001505c41511039081203940d1032086580c05030114049010580010b80c40c3d560454006018003c543d0040602e00b001c0611f04105403075400052084a16103507020454502d0300d48882c0c100d0040c480540110000541d03d0042c59000040804901c01d00c503009401181c1040303e0307440d07100c1450048a42050005035664181c2108880092842c3c40300601e17289801c0d000320b0425450781c0400e1045109070f007100e409404d41310806a690080108200000303065001c01d00802c140d0358061030300040d804c0b00f2101407565271350b6012610b81294100c1400900c003041308005121017241c00c0340346000280d01452440d410f200d402050b612036030145901e102c0740c041451170201c00410002040da074983c0159003100d08960036180c3ca4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 72213554 1250 72212304 72212323
    0x170c0f1903081908042001030902060a05040f0e04020a0605030c0904020f030103060c14030601030902060c0a0b191a1c060507030204080f011a010e061215010f020604050607030b04110705 82
    0x42c074050203c5200786a00840850340200e0300150250708000b851340000104103070394508035040644582c940360050700c4403c082c1c188001c3c5500d1361911207040c1310703151520b140385a000825503000380c1d00b40009a1243c40180c0d00780c0e09940760450b640c0e43c5500c10700040d4821620101d4003d0310000d9412400141d04000e1410f9038407510b002d0000d908010800c4400c0f401240c15100405e9041012400942c0240e001c541c0c00c501c050f007424240641d0140b09410000d2801054440f00c2c0401d04000d02a1300648111003c0002c1c03240c10007649100944030006424024880b40c015004a00b411000c0000240b000b0007260788018140900d140944008029400c9442408220b22a048443c020184180103194805a01d44080c8040b075062900455003500d4012889810050811000c082c0100205955100d03500030424150440e84040005040300e010807840000c40d00104140720000d00045005038204840386808170f0b0b03c03500f90001600816200004044644000030031804101d40842d070f0410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 72214804 1250 72213554 72213577
    0x110706180803030708060405060a08010e070509070906050403241811010311121b040602010605130905060f06030c0a0e010306050a020c210909010305060907170c0f190308 75
    0xc0d0640e03140708103603a80c0030950700034000c140c8000000b111030600e84e21095101000400020240d580d495016007118501e10b407064644c0c00c4100103000300c0c00e010203e150406828070301101c20b0b61500c0c0c80100740f4012801f000303080c41780c40c6100310480c1c004460701d03a20340c911094040100200d200a540355940d0043c80458950035a4024418690700a1082c0c80c0752003251024145400f100e519400802d0742e0003402c244e6241900c03415441940d04490260000c0d107000c4e00001829418039080140c1c400201d110000d40c0e600f44282e03d80050004280b5a0b00a00060111081502c55100180c2004c10b842e4409800120070480000c0000c50142000d0480b80506000c2203152203030f4090105071f1003003005092a90384140d80c030304194034100b540c4003e2030000c408030a080c50480341c00100584020780c41901c203540a101030200038902440050b00803e044841000340740e000d000c00580b1102c0341e0b210140304583c1125480703503c0d03c60521380d455211500c000c00b0000e5841e442d01140d50b400060f84a503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 72216054 1250 72214804 72214847
    0xf0905120f010e010501080703030e03010212130302100c0c030c0c03120e150c0a02010503040309030206040b0409051f15110303010e071b020307030206030402030a0b0702100e070302090103030f110706 88
    0x44000c1171291a0584802001400c0e54a040d51825150469400b00c20b94143d9401c01800a18407101c0300301500480e1105004018500d803801c000f86881100c0c1c070080c1045150400b05070320759422803800315078240d06051880c1c6205031402c05403400e0986a001812107a028040c124802e03030700030010528801d08861a00c03c0e8041c0d141196924098200305404681c84502c4e1740700558010005940d200c1d100349070010080381c9950214045410561190300c1d4060301040c00c0c03142001c94000d550380f240408001c0c20942c8907900300a0760f00c48032445503000e00c101590b2500020b911030700c1d242070003102c0d9070b08a23a501c0d6552024500c20420841d00c4c1000104104c030320200c442002c44003ea20140c00400074400c2c282981c082010580c40a00101d900d03204116100d0005002d0140b064420b500d242c01a040c1100518469000c0d2130000c039103040ca5030030900c0103100603502c01e0201815650503141003019002c1222040d04d1004c0c0040000c40c040c80703481c10000e141c9a0000541070080c0306000b410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 72217304 1250 72216054 72216071
    0x90a0615090b1218070902070213020903120d021204140f0607050301060807051b0a02010806040905062d0907051906080712020f0a12050106080c0a0f0905120f01 71
    0x201c40022540c0900d042c04101000200c5400e0307121550a9040000c40041403528074010f0089031a103400341e032040640a801080350800d5150112010781c90b5078250f4019450310704128002521039103110901140c01102046140d18449a5819101c002e8a24012407009003064144503600740d980c0611029507101e2041145000d00700821000e02030401516050700316400c1c00e4094a4410004140e1000c004080c0702ea002000030254880d600e070080c0c0405080c43c1c0c180750000405001340100000d010f60b0070801d071800014800503c1a501c02c0860f41d4840d46801c21242d040e207101030076070402210388134000c2031091864012071918100e0302c0441d02072118010802000603902d449105540119072204006454a401440044158000300e500103140c0000410031600301d400924038840010203100f18944842414441e5501410450a20b2415464420010021842001d107071000b046130401070240f94a01514040000d0440104220349000304401e0782681c4501e0b4000088507582441041c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 72218554 1250 72217304 72217307
    0xc0402180a050f060304060b0607060c050a0908160b0912010e25050a030813090203010f061d0a03031407050a03030903081f06050a0207090507020114011401050304150b090a0615 78
    0x10343d512400989214251399880c2c940320020400480300c0d68000c5020080600040ca0b07501c51003440f6080c0e900d9554a80e1600403004002414503006051140e0004541600c00c070100b8104c041100c1d0207a908039590810200803d030b0780c0760301000032009903003000441d00b05008007160500d01003560700b41d500a80307a000031115030160400d106c0c040d0041044081071020a00e80c000800c41c464031039610450895803090000c0499109a1120540420814060140c07551051280104003425101321b180c140100d000a0030840380340c8401021f1150702030061a074003d180054031003194111080d14034895807070134054050b1101c4181100015002800a241550b60b01c007030414003069541c07820107441c1000001d40c0c40d54002d4030032501354030400340001007004280c0a510301c14102e82e03002103400c0320400c1e004242050b0607044a404503034800c0c9401385690b40401580c3c0c0c01508903401c0c0010310f0280c5000f0004016000300603070045240803c10840d03191540103071007161462038030080c418221480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 72219804 1250 72218554 72218569
    0x106061211030708042a05030f010207080301050d030c050703030210060b1611041410092706090201090b120f060604031109060a0e041b05060910030e0c0402180a05 72
    0x1455254024103001003100d4622911a042d4010b218058485506c440d130042607083c4803d071564000390002403981444a41418041030085150030790007542000716a0303650840c3750105000c2c541c0100c900c003030402c00703143c81217002c2070600d600001520b06c100c2e00c0303060094030395440d004a02000e900300000011990381c000102d071000000001070300704010346541c1b03815416681d4051a940151110400768103c036107080694020b2079205085400300749050030103401e4079084c40e600101110701c1d20400c3d20282c00c6400031840a54005000500301040d440180d03040d44c2c90b500210380d4201d002c109481d040d8104000107005660302c1d10101c90f2070751340904111f40c61107907020003000b01e01390514212160601d0000c0301e41105000304600c81454864403550842c2004807001d80d212120b50046104540740300ca284070240005641040c81d262141012540340f203513000b060780405a9070b01d081c040090091110b401700080060040d9503400c8661004800500c032002402d11034481038900042c203150100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 72221054 1250 72219804 72219821
    0x70903050309010f0e100806180103020d0b06011e020d09080304060504090203040809060307020a030e03010b18090f03130e010503010c2f0321060307030209180102040306060801060612 81
    0x2004516180b1180011190201c20200050038051076401e90300761940d0340c0021502039601d030354a10304986020003c002d40301c0206150301c0c1080c10041c00600240c0c58140c4a8a03050f0703044950140700d030702c6841c01203075071846455402009480d181c1c3c041c1240c650100d82040c050010b582d5188000d5100c2500070340b80d02c2036104800110b0380812007002002150340185501c01d00500c0180c2c00c141060002c00c5065208444140c01600115203840c10580c0003c3c01141b039140a40003002941c1d5800042940b48881d22403275080b8003a04000151010010080c00410410b03807002e03203494483c11406414040c2c1c0e28096841d0814004c0004a140c0c14140300f1501e0088466642049030f50f181c4141d042c1c2018480da440d0110701d0001d0f20300d040883d04100808051414030ac00b9003449071506800b4108c82c8018010520030307004140100007599444c1d0701a90000840300451400004c1e01c04001d009101d180d000402e0641062000900d2640650180f000c070780c42034a40fa6800429100d502d8100d41c01207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 72222304 1250 72221054 72221063
    0x114011701050d02030102091207050a090501060801030204050402030a02041d0f0102030c0712020a0606030b041106120c2b060305010c02030703021005060a1d07020d0c0206040515040b0705010b09070903 89
    0x2040100183c2c076140108005882c00a000186443c3d94540480c1d4509028600800240d0014200f00300d270b4105201d10138001d14031340000b04425410508000c18642c0c040c07202900c200d0301c900110382999024485100151345c01481005221040d00480300c10544007090017840d40124102c0e040c00c00018001c0380d20460f04510310f07518020150391421441d00079151498114072402988000081c0c240c401e0b54091030145503003d54902e054a080740902c2c80d0720a000d8000d403814040c0521000c844d490305038100407598112038071880502c01810030500c0030900070b0044440c1c100d60000c031528039403082c02580d0181000344440d000098090341d40703100b0400e00a005038022a014650300c2c089601c01c9070803042c0101840f9a0a9071002c64402414012040760865801c10042c091b510360100400d2041c0e03403180c00c0c28802c186658000806174001c03407040600500000200348030b102c44510866000e0701445001c0303900c460490901e83d0081145580705c074003541d8a100855030940c040c0c845c00040b01da10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 72223554 1250 72222304 72222347
    0x402030a050615130312030e030c060103060b0406060e091504021209210a080403030b06041509060e01050714010914060106020f06060904080a090503010c0e0901090e070611030c060f011401 83
    0x45644840300d01c21050b06d107008056039105002c140f0380091000304084c83c07042c80200340650640c146481155a44e19034107215138130700407040022a80042003040c05680c01c035403040d45981d44400030132120b007102c10042d501a2000802c3d03040d201090321040d000f440180201c60800f4100e80381d0404004000801e9510f4003001d00032100851311405425a00500c00d19010480842d00c0300801c1450b0016000554040e0400380e0b100d440b1680481710200070983d51a28202400d8004000380c0544600340f00509004805d07951005000c0e0250402c0e5034a980c0701e000b0f004a20020072049072148402e000c0d60005000f486840111a0b80014a036805180020420304003901d0ba980da40c009903001910400c140001180c0c0010716603020322560760a00d009469220054200b1400c000000030140c02c1030418a2a00300290684a800a0388505681c202d0a2070414041c4002009195015418050301148106002c10258010160b6040e0407a00b002c04110030340340c103000054800700c65111a0507440e114 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 72224804 1250 72223554 72223559
    0x5030a0201051e091005030910060f1406070510060e0a0b0907080a14010305011b21050c27040605030a02300102181908060c07110402030a05061513 65
    0x46200c8031110b46070021a40340380c001e003000031400d00c841718040c00c1c010800100400c0191501408104245140410100003040c201081d000b4680010300816940c035040400b115940c1c1c03a00c3c1c1c21110510f410104683e2948940c4810305c020780303c42e00595642c40300510114429100500501d1002c2d03400400210306a600c4860072500c18800030704010b0416140c0c0d421108060025030f030a4043d41c018030012070100801120703942c1d01000301ca4444204419030301070804140b42014190a12710068502188070784850001501c14000c05508084000040841d101100d4060800c0800304900350b4081c010580c1c1c80d001c050b02d03900d00b4040a03400c034032071070082c510039602030780000300c1850248501400145420221070881e0881480041c2c00f00100070f4050b00f03440c0000c007151300a00d408400514442c200305e4110348580001d4903400c40c0441c0410907504002e40c8403128454204050806c64980c45c00042c868040d120594199001c0c60310740d01001c3c429031201003180c810044414a0f5503942d031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 72226054 1250 72224804 72224827
    0x703061e09020d0212070c060506010e03100203071403010909030201051506030402150c030c06090f240720100c05130e040807060203040f0b160801140102010608010509011505030a020105 82
    0x50000100f1450340ea42044105400404083e8190143c19a503031449003001b450726201040340d5000d0500b07418040341c04030302015a9030000301d603c03070102403840150f00c1e42c80b010030039601c001c12800340c1d400c00306011002042c0d6060356840301c4c0505010364001d02482e03e80d202c84000b0015040f03501500701d44100005405800c01a002c1003522102d102c420f031030003400301c0349641150401c520075420340c1c0101c0d0900485031001c04c800d074080e01c0e810700a4041104a25019000b8032200320f00d00402c82142030001d02031a008222040c00c14130324550406603035a003040603035201c5113850703902c5010600c2c00c902544064402e20917142c0c014003040300d016486061540041c1c100200a001301c07180c40f020000080010005d00245006034443d24044001d0324051400810310b860041031401652a10004105010392000031641120398001280041069640040f405000c0700d400c00082503003818144026500154031004042d51418542d41080d5101d80403d0b4441500b2100a40090018400c2d03140d0603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 72227304 1250 72226054 72226057
    0x20f0709061404020912010f0902040e010501120212070308040603050a150303270b3006060403030c02030a06091202010c090803070303020f07050a03020d1d090c0a020304030c0e0703061e0902 84
    0x1740040c11a2050080030b101642961001745480701015256440c1f0004c60520740a00c40c050348002009000070340c100308003400802880310002e8441d011002c0301c0d80060905004460155401c144001c0d500c0d40c869a010f0090001501c0c1400010b24000418444910704082241500e078036517902c042c3d58030382d0b240f540854412440751030f00c0490143e40005103403101000400725507000200b0b0507802c14030b0780c0300d4040502c651404612810084010800d95a41301811541039a074035052190035444180086450460501b1000b480b40c1d26000d0b0a134107001c1540f5510701140620740c024041c0ca01100c9007262098502c1c86040140c0e401407100100190281d005403664080c02450305040ca0b08680700c603450020444400c1d4050380119aa01c55503e41c006594003441c032541054441c4400d103140410b07d1502c0080c1003018015012480007101032003030040303030b0055030000e6140c00341d02d85400700c54041034829281781c408207103081c80c00141c60070283c04c040e4403080b401c110751120034a000c407540040e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 72228554 1250 72227304 72227317
    0x80106141b010c0e010c03171506070b04020a0621052e0e070905030a110103110a020c0a06030603210509090106020d1101050c0405130f0c020f070906140402 69
    0x3040c1090001d5140e1400c981520a03084000303000204141c1c0510f200030301140b550500d000d0400030f40c28103040101b900706424422240e000c980100046d6245070012268800f070b03080d640e50006d0700181801c18804c00d0807000d8007030350080f5900014160b0b00d800c2543c135000d40c01f01c0340442d076121031450320350600145d0065a00c1000ca142c00f811503400604042d00340000042c0c078299442c0748400c240000030004400a0b4000c031241840620a0304160000c0e644003441d05000f00262043c51091195900c40d800600d11600c110701c1d61600c61082d0100607403141300c3c2c02034050140f2020040003401c2c40c482d0051170100c940041801c204800d010002d8220340300d19555401c20300c0800c10101e0364940300c07146042e0007002d40340d010348415940d0400060501403490f40241040e8144018020010a840c048070100c0b4012511002d8980d14556180c0142028840d007520a40ca003510540c841500441c2c0c8800510750f060a68021980b50f0000c1301c21070740300d8003400c0100f0000358241c003000e04040d4002e116 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 72229804 1250 72228554 72228587
    0x30c060501080c03100e0721030e09060d02060901020709050a0603140d0f0f0e03120318120306040c0e0301180201020d030c0206060609030f0607020f0d031a06090d0602030406150801090201080106 86
    0x1c540e904c1c0d00d44090180c845611b0b0321441e0140c0b0408c0400e2540c01400c8102c840000c80385140103040c9a4005440c911500d280a4440c45002544200c4d03a80200503c00082595541c1888103142c50070080c00100311622080e10f0980c5910392035030f585030021a00510081c2076803166081d10444600071610f0030f4840d4407400034410705527403c0510395000c00c9040401814440070580c1d80c80c211044000d03000c0160504951071384400e2002d90071090070300030399500000a035400a003503113056104035100340151900741c1d0154179008081100f60b80002ca140c0c4030300c1c000e030210750400f80c80c004110700702c680c4003840f000140c011102091507403404000a00b88084018200c4818580c4921075505160007901c40718056407001c524400c0c1d0100612041030742040d0fa0801f04507201c0a550003004111000b05614401c0c1c800040d19806075a820701543c2140e60840d074215180c3c40c180c034200d4001d20141881c1410803112080021300c200c014007506281d00d6040e540c24545900c0c0141c20b9500d2610360f08480c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 72231054 1250 72229804 72229813
    0xb0105120a021c021903060b03090a030f030b060706050103021005030f0402102007080c012d050c0a050a031403010302030c130209041e0509210f04050a03030c060501080c03100e 78
    0xf955107518006802c800700484403c1d02c80c131007182c801404a81c6582e00400030710b4400c1c01002156400490700010080d05424441594400010110010b00f018841e4039480000840c035102031007203651010307042c3d038800e07240b000140c0c20581c41981c60f408200e4002c07241984c1003000600505058514000005d1142407072043c0c0301580c04d1001c4680c000e6254500b1302c0e48042010043d41c0420014050035031b0302802d04a01500d014008281c8040a0100d4044030078170662040884500c2142216416043e81003502d0102005141254075010046010b80000b210000425040500d10007200d0403a03900600600c18000e80005112542540711070405050f40c0c00d1100c0c0105031102c1c040c2da840d1000600c0b0303840c0542032048188085890284c6100c0b035540c030851300f040a421540e0760310078208580071030040c0c9a401d0b000b44034410384a5500841e03000708140030008105500a072900300420b108200a00c45607132103081e550b684644c00b01405505070b10100200c0582c03846da03030182d4220202d01040c0d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 72232304 1250 72231054 72231097
    0x6180e1608030306011e0e040e070807030311060702011b030c0306080d170f22050703150b1008090714030a0b011205070e06060904020a050c0a05010c030b0105120a02 73
    0x3061500080d41c4038030a00d41000007040001d41c0d0100030042c0d41600a2150015040e860f50014084560320301054000d6642e810810540301c010818000207000b64021100c005480b8640105030740400551442c244c03140c840403880031401801039044500340a0b45640c509801008102c1c05071106034819400d2550302c00c000710324040d090040348108d0759503458038451803004901040c40e000c0024005501d01809405002210b100c005020444030520300b1520203040c1503003403181c10314045034001800f003040c140c0594030200d05034101c00803400080b262600f0b2260340c04e005980780303001100c0002c9203800c11482400200c1d403141c0000d084283c060110f4100c04980e0b81c607009142000c2e0081e14000000b503c140d410048200018005007500e0b1012005604046012031039602800b501a48665008600900614882c0c001c7d0b601c001d068400300d50f0041d0305424401d0003481c58201c030b03100080c204200042d0a5003d0800c6a45600c4054840c410035520001003500a4212800a010b1543c4d05240d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 72233554 1250 72232304 72232333
    0x105090307030b15010513030b04021201020a08010609090507140a0504090f1406060703170606070609150f062103020102040f030b01050f0a03050d0c050c031204080c0406180e 77
    0x206000c2e51103000501e199051610803100c01d00ba05541050401100f0008068500c045020b2001200d510445040c0300742c9452000814101c0180c03456140344d80301180145810b58000c480d50f041360000c0c0c4030121056100c265840c240d507011241500845c40c040e400c40d040302c1c821002022801501d2070007509054941c51203405170340d05071400d81c2d03906c0e444801c0c56105804014020f41c01902c12104d4a26001c059a400351800d00c20000e40303c0c4204081c000a81c00780c55503411250515401035007081030001d58030b0a40c04103440b1803144030307810307241c640e0030f01c0191818420301d000d50324101c0e031050300c440d201c0c0d031a11040083c0400883c110354090200049100302c221001c8099445650602750640c100405c1c424402102004c40b481004541c4040001c1400030070b03500b500503403619201c1040030203403c0543c80c06001c0314400e80c140c03240903020303c00c0d054110050b00c2a160110107507815140070380200030a9a5960098508005080a84070064821948a2540d465541090b2070500c0000c2a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 72234804 1250 72233554 72233563
    0x1d0f0118080c1314160309060c0206160e0f09040c080105190e0703020d020f03011e0e010e0c0307151e0509010809011e0e1005070512090f0a060b01050903 68
    0x745075881111030302c00c81d1600704410803151400041c10400002095808001d290f00a480c4201c070b42e640c0141c40c11000e11a40101c50001d4200506200741c40b03811000a603905c400311001904283d6070a11210030350705c5180c510b085084000c0c4054224200b04c420000003260140040f80e500c860035030001000b460a0040078403c074101c05400300340c0002070284100b80e40c50700b900043c0903008100c0030b10041e6075034001080c107190141c131031120303200c890004640107080d030f002c6018421000300b40d521360281194000e40d82d144880e40003409070f050040e0180d545c607101a200e141d4950011142804480d01e42d204040310b48200d071401c0ca00d1038844400300e03070380c40b40d0b0308126000280e000544640340c1c1d40c1281c91250040d50100007080014203913824149511070480c0489069600d5060b0807901c0c0c07200300300303011728070702101010015810301030005055940528010a4820342c2c01c0d0006500c2880402c0d01040784c0d1a10000e000c0481c5035540c2c5100924030120a10305005090007a541030b40c90820 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 72236054 1250 72234804 72234809
    0x11b02030f01140f09030d0905150a020a0306050a050d0b0709120308010e070206070c030e03070504060902040305010c080915270f120405011d0406030b04060f05071d0f0118 76
    0x90001a4010042a04071901d035401401c4079030301184203017880b415030400001c51364082141080041d00011910300181800420104100c0018100c01805001d400381d9000b003509000c5914100b020950f28010f104402003a481250b520800144001003c80e500030790301da40c4151a4a04401c019840715138100100c1c01c86001500000c419a0060180700d11551102d034200429000620040c07a000740010628801d54034006c0412604101e00070190710b0401075031001e4100100203008207a20703040100000e400603c02500c6a6007801a0706030903600565520340a0307900341000d08071007400454031065400000c1c0c048160b40c403410004040045220115910f4446444058400210310b030b02034500c0c064031050100c94400c1c007048200310907a001440b00084c090002810002485074100140061980d1b84c00135100041c001d0030841004500d6102400055a040b010490b070384504e002122303e88921104d140030201e1483c903119080c44d01b440342c1c0c49184414909140c00c84c0301000e03661f0f48100a41e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 72237304 1250 72236054 72236083
    0x7060c05102c01091a01051e030304170a022103030a0506270610030513030c050106080303010303022401060e130e01020d0609110a0c12051323010c0b0105011b0203 72
    0x803032500081120242c8a0030340d0031703d401c0e03118080f9410a4000b07020f0106405850361002d050200c41c1364561000d0080d64020000600e8403035801186a02080d21010b01c09800c910500d40800003440000900410801d2001513000450650fa06e00c845000203000c064500d643c440b6070924140c00c01c54101e10303010348045540c2d00340e40c4035090400610000603030204030401850b08000c100411240340841c01440c02da0185801141d420381400c0407030052190ba0081c0486010000021040c0f640014000e03400000c1005050003003400b402101c26801c4080c043d41000500c050304840350361425094503c4e15400c4440001403c1035403c525508a03800300364840280c0e03403a03c03001c02241c046807140c40030480c8500c0129182c1581c2d440010000002c0c0300d8010301c07000c6600d2681140611a10039500200c80d80c040e89001261126001801d00120003106044c0c001e420548881a5100d211010005507020011074200d0342841c005503020040964200020101480c00d000035039020030103d81d026044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 72238554 1250 72237304 72237311
    0x50301050406021c05010e06040c031401030c0303180b04090906020d140109060803030103112701120b16020a03110c0402031801050c0a08010501030902060904020310050307060c05102c01 82
    0x3130301490000c02c04402d4058a4403450074004218881c1386e95840c2e0ba000908450004060000c40e030190024050804101402d003030000022040280364030540741601d0203501c0d6103001009400b411203403100345000340e010000060204101e1425940c1014221900c655405410f08a01c20410000c80b44a800d002c3c01c040e00b44e10040050300003c2c031a041c040c01c5400d0145186604585030a04040000c041960107020681c0c8018844030240303104c0c000440c0c002c07c180c8403075691405409905400303484103440d91110a40402c0c1c00003081214038504545603005088600041d84064400d41841c01c2100c5032809060642c42d01e0b66903e03c011481968a56181084007000840b89821500b00401e01810181304000c0315140e0f903000015581140c500340b07004200114644040341c51801003041241d0000d00210034011002022a844c000b6901d00340c085640c01c6075a0a01295059075026004d8031980180e02180f01d103141a801005c21618a50340302e62800c154590700721840595144400b507030341d64 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 72239804 1250 72238554 72238567
    0xa080a06080f0c09100f090207030e040c020d111f0f0608120706020f07081215090105011710170604060b0a0f06030b0f040c02010c1808030f0304050705030105040602 73
    0x440c452000070309580303801080001503a16030309640d00103885260f841000000009003032a0440000c4501410844c00360106403599001850017a400044080300494a0b03040700210b07504152081c0411040700c1d900a0226003070407401601d808501444042d45030040f01d40c0c115007200e003944009001400e8100000d15580010f0303110040ba480e41d040039505400c40d820481c0a004d5650503216420740000d00160b85504246000310580f01c0c0a000400003030300840c00009560400400d5440b07409140e40001d080e0b54a00e041150080c0300740070b05408104100d0080c400420542c4045038043c1103840f40004440e22121034181c41c0c0183d11010b005988007004203c01c00003103003c1c05c440b64000740c440401c22410041282c40306403045c00b52b0f00800d0364071020340d1565a41c1d240f26103001d200140c0100110701c41c1102c000d01814900150101003000b444807259401501c403094000c0b0b440000165040480f440e112119642c00904241c4141c0714141d004509130740c0a20905024074440c02c401031740c1c3e45 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 72241054 1250 72239804 72239821
    0xf05160504050a0e0606100c120c050615010f0c050c090a0501240c08030606070b1005030f030c0c01230a03051b0703080606030a2003150306130201050f040b0a08 71
    0x2e40003080050010b0804c810103051000c00210190086c030f046410180824110b2403c0702c03003101010001c0d21000003105864045900300c008003100034020300660b81c1c40c0d641d022181180100003589140082c0701140080451881400d01d680c1c02d0b4401c03003d0302c1507440440c001600044054880506c40790f81c0d600104101c40800c040c0c100040c0034081c10106c400d2054401902c0700d031500070301400e11080000003542070740d142c80442c3c0e2140e600c00c40a02060130140009000107285001e0140a44584078120004101c0001071700c00020102005207101c056140c01140c0900200090541d4001c01d60b840c1000540c0220150805900e03543d070026040c502241801c0e01688407013450305034441c00300310303000c04640c0c07000407644d000409880c1d031036513070703c03400301c804001d02c5c501d00b20348254802100c00840004040c0015405500d41c400c00580e42c00c4007204040c0c843c0e0b01a51580c40508003031000c400154010409051141020003e91742056550007011025502040c001c80015072841c08100502 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 72242304 1250 72241054 72241061
    0x30f0f09030106080a0506010e0403090503011a0301060602031615110d0b01020715051e09030a1a0a020f07061e05011203123c060f060306080102070309120f05160504 73
    0x149200b00041041001716200c0a03210749042c068414002c510b07500240c14503001700c1e00e9a00912000e40200040554141d00600000711180e00d1440b075400c2007400504030380b0000c00c0c3d80c400d034244200e0a41d0716061340d540079812012900f00050043c1ca9401c05c500c0b500448018000e20703100c80c040400c002581d00002070512125801c444050111401003049059000068800b030725442041d030703031340f0740316280d4501028010440a60350500c5901c0344141004501080204440f400801c10801344e20345180220a0b400b40e40ca0342c901c3ca01e0305002840100d225078001c2c000c0300c81041420441e902034105a04260b4809070843e50490b000a00b0103410558440c1000104a40f980c0003007280d02400c514807013038201c1060944000902c0505294150501441c00d030f50300003007218080040030355490400c0e2501d052441100e0200c0d140441c001a192010300803904025410354411115a00b409a403034803180d03011109494280310301c07a407040080e004100e00340c1500702503c84118090f24003410403042c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 72243554 1250 72242304 72242309
    0x10308031909030c11040e030406020717010501030809010f0903061803020607030b030618070909050f060112020d03080c120702030306030c0a050f10210209040606050c0717030f0f09030106 83
    0x10070b14204007074022030760050030000003a81c0308a002c030281c40c00c000045d001d80b207424049801c0c1e020026002628030340005036201111805c411164121103004e038405c0c202e070400d00c400f52145204000b00c800315880380c540070462100904025012070345a444440845191b401e442c2e00b60b203903038002e40050540400c03c16500c041c4902c4c0a0101400e00e50109468810140404d0b2440e0100d11115500060a01c04080908072a40d0200405d030a20b0400c26a5000301c940003000502811f400072030804801d01b0101c41c020f401510f1460b03461041d0781c0c203c800000050114594480c24070100701c3c548200601980100d074664000c503120300303201c01014103090020b20b03a1b6100c0c46e4241340800182e2181d2000401da03200c100c4102042007268141520f011092551720200c04880103010a403d080c4e5a029101000054508119050b19140c0aa07030f00c0c8150106400303075a00c6401c0401c41d2108a9103d1140358104600307403414541d000512804a4102045000303404101180e44529400c091090000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 72244804 1250 72243554 72243601
    0x3020a030e1603021903021e0a0609080307030e060702030a030f03061d010e0a091514070c11090414030f1803010203060607060905031e0d06060806010e12100501030803 74
    0xc2c4124540b184980109031000a001c2c2d10080d040e0b0200500c02a020401160040c028440c0301540104840036150003808080c4a140484030229205120f443c10740d05845105005515003403541d02d040e21110f50000c1c2c0503034004020065480180c8050107050200e512a445801a00001c40340140c01d503000d9821000340d00c1034121065200300c03507203180241110032000f903000c00703900c80b0603995014107098540a00342e100080f030800303548415a8044402d511308040e002c03449486000044940c0f1030300c0030000c0d101c0749129480040b140b90400095070803a104000c001044502c039075001e42160046c06214801c1203000c182d0300101c000094003104940801c5000b1403451900000054044c082d8450181c040ca179985083c4040140800445040203140140d445000700307161740c0241285e008040002e80c2a0038120006802401410040d001d404140c580400030f406c1001440240307030450010700c515111343c0140e000d4501540c480d20b4041e600400e0080c0e500e1030200c1c091643c407180d0303902404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 72246054 1250 72244804 72244813
    0x3151e0203090703020d06200307110303040b27010e030901090b040503250e0a05010501020114061f1e050403031103090108060405090312010e100501030b0603070513080d03020a030e 80
    0x58001000700b00d01e800c0d00c1e41101e2042c20346c41340c1d06000c070040010324108040c80c50034080c80e106082c2c03154003862084249603100d0100c2410611079a03240d0005480c0288019010004203001c5140300074610b0445849400c0011041c00c003241880c252040c1070080011a040090025904d591111100003d0302248140300e140500d03140209a862402c1e04589400000e2031810b2090722664465101c02003c0502200c40c031400d03e20041e8000300340030700c2024090362800303040d5200510b948000b107101b910014100322421040e500d81e4902c00303000c44a608108521449071030146c004800c0c041e42040c0e50755803243e444c3d5080d850b02504040744400e040307030031b03600500c00c940c05aa40301c1c490f40e902c40c100361408030300c58440ca240e4914602035080c0c80f41d282040c003800807a900080080c2c440c031580b1450141c2d503d083e0340d0700054080368515680690400e10400c0040c0003240940024034128840c1d0a110303020603610900d046c10680740d03103094000643c000428005180d414010501c0c81c110b0301c001b82 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 72247304 1250 72246054 72246061
    0xf010203210720061909020d1713120308010509090304090c0903050a03030c030f1a040b0a0509042103060602060a0b28050a0801140c1303151e0203 65
    0x12000081c00d001494100c111030000100910b10481a0315410022903900300f80c41582c0b030490649030201200c58000003141000362280703c1865005451115401030100d03c456607142c0c40391203030034000e1031800c418040c00b001480d800c0914600c01f000100842e40c0800c0c08050980b90040c0141310607400103209427107110034030100c014084100e40807a0100440003c1c214103000e8152913a084960000d84a80900c404007030526425401c0b0440c0240d41d80d03402c11407403c42c600b004040710422281e5042c5402040c80c800e4650600d54405011000010080740c00c0c107640d41c0000e022510300b110304036081e480c1e49084c03114514203e0300c40000d40495050600140d410000000d50750300c1e00a28044900c1d07101d0b4150700107034441c0842c40511219082e4103203601e41c04040035004804183c49924000d0a44040000e4801c4040c8128160051300000c08003031a110f03500d140f48036800201c00c94031000a601c0e40040014031101c1d16460409420b003002c80c40c10321000e0580764020340c0c000c095206a0040042 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 72248554 1250 72247304 72247327
    0x5011503020c06070c0c17010f05010605040605070f080904020a050a030f0b09070c0606080304090204030201020f06090303071202040b0a1d030a0302060a020a020102040b031807081612030e030a030e0f010203 91
    0x404e0307004aa5141001c0300e01414101300410290780c0e40207000301114022108415a81900201c00784880702e00b00b800303180d80c1c81c85c049503075118622940740020303800d20a480000e034121031034030303c40c4e0300030041c40d03081140e0380c0c0001d41242d0003801014041900012442941505802104184d03201c242c801c0214417080801708201c0c520080580e010001d401c4030000070404186d000c0000f07060071208a83d12203850309100c0c0002e501902083e030152240c00f11200c1807120016a40c0e101c0c280d2100903509580710301700c3c203503100e0503040d512114081d003c4c8800b00d000502e64014180084155440d044200220801c40c4400c40741c0e03203107550003600702000d2030b0040303a0001001c6070002e655503001a6259801c1c03030102c1c020301440d04100b8565000206000c0114111461400045c02400070b44813102d83e50b82d98250340302c0c0040181c821584803480304010b040c80f00707942c0c0b03000a406400c00e11400d40b2074a000034200007110340b00324003050403400072b0750203410140d51482c07a003d420700045140c40891841d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 72249804 1250 72248554 72248563
    0x7090506090a05040212070303081b0c030d150801051006110f060c0901090306060b070b0f0f0613060e040c0f050a0b092707051809070e0d0303021303050105011503020c 74
    0x50a92580e443d403020a003151141c464001d03191071405d0603503041a46074600288102020340b0965007400c201411004a00c13088021160b0801110005601d045695042640541103c40401048a103100b2000036140f01c20b0107540c0c492509404035007541070800700041c0941c001140d150713a0ba03521981001c1030716080010381a030042a01001c05403070354801c500480b00b006d40c43c1c000030007841c105400061581d144c1c0000e011018803440c0c1d10340455543c405106400f2008881c48904203c4d1400410240e0070b25a905c1003c0c000b45060209004d030b155121514030034800e40e4101c0380e10a036144100324003402800c490001e000200c0e810300c412032511814000c1800381030503044c800d20310710b50740c81c10301c512100b8641c41c00f07a0000780785c105600d4005005010f40d0440c10788948049811503d441e40707031401c0803503584981610784610b80c0c0c201061060001d14294100100c0c14151708000544940e0582d049806c0150710807030000c5007175810044c01d1080014000d41140900d401405034880e40380d800300d0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 72251054 1250 72249804 72249811
    0xb07080f15010c0b0c040510020109060b0d0f030f0311030115030b03010b0f010516140303070e0a0605070b04151a12030304030503010e041509060e0606010e0310020a0207090c08010302030709050609 87
    0x48022130180c94000c04108544140c0d8886c0d60b20072010300740c00603440c0e019008080708600615007005503000350030500c260703104202d00040817812803070f000000007402a14a1902c0003001d10f0009a0441000402807656000303802203030003201000d8030781d5032184c0c1c10b006030030b0075100540007480000d407404d01044014852901c42414000042003c0040c1000d070004a050940c0000d01c103420202e00e010b060b600d81c0d000391001c0c40012088004504e080c00d1403000d00044810035a0f5051274000350b40c88803040301034050300460b0309500c01242058050301c1d5024120003070080712841d1a081c1c20900410480004000080c40306800034010132020903006010340b0304407005410311510641d5545041e001055000b07a140400c076150079154414030040e6401441e81f11448001c90f1040c0c0c4039880150780100801d0340b49079041d8482000c0300e9940480340c010b0b005980443c0119a810394440900b00180d510030074501c0c001540c000300400035880c4c00c0003408024030f0081c40400c4141040c0b00030640111004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 72252304 1250 72251054 72251063
    0x150309111002010207060504080304020a140a151806020303090d0207080706110f03030c0d0c02152406030c120609010b0406050a0e090f090c120703120c0b07080f15010c 74
    0x650941441c0d0007901210381e0180d202d1410401d503d86071030031041e1608161001d174040d803414000410449240320340c00d01c00d060010084600345191000c402c0f8801c24030086007040160760301c40c1510b8122031030340c01d1014009c03d802442d1a803421400c0c03140380c4070f0b994101320115405088100008032021403403c0c161100380c54441c406403a03810381a450902c3d01d02c5119158070002040260011400c80034056418900c3c90038000000008401ca03620b00140200ea40303401040000b0039a0406510018002c50307081c440d000c050410054001092038000b11003230100081c0005040c90303000c59144081e5881002254491100d5050100c42e000b140250f0164400340036000403240a801d0081c01e501840250003007078810750b483e110b205426030940a4860702c00610900c0d078140031900e4198540c3d003021040c070b0000d00946242d522181d00881220301c0780010301c46003030305260100c1c0d1540445480307101d61361101d9001e0700388030443c2c02400b00c1c002c002c480f00102c0000084100c0e0b83c01645e042400350031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 72253554 1250 72252304 72252319
    0x6030e03040f1403010e121903110909060a050301060e040b0a0e1908040b0c01020a090807061b11030105161b200112020a0903110f0603061c02040c0915030911 70
    0x42c01c0c0403134011b04086801005500c10070001c001d012076500020401c9800c010091f03100064068026019a0303141449501c1c0c4200600400c151400c180e920740303074442401080380008594a4011908452898200c1da41c2d0488490422041c02911022075030072404481c000c0000710390440c8281d0312a00340f43c09034a01c1049403203001040c0001d503070a6501621044080a65a400218016000b903001c0c102a8001c101004030001c0c00b0300d0041202c1d02125006c0c0c6940c40d080c040b50300300b00c417030440364441182c442c40b0b8000385000710713102481001d10a0010803000c0c500507446030b00140c0301d2031084030351032402c5010036800d100286a061144881e4100c2030071590146228000590310b0082e200c200f001c5c0c0e1072001c11f6204003181e003d152401203e0040e610b260b251740340d2409110190412403500d90300032100b000400e211741007802c04548140c40160000c11421032a60000382944c0d039030020200050034091007480000c0e21000b0b41000c18110b17003402c004890301d9179036000e800c20400004a1081b4034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 72254804 1250 72253554 72253589
    0x8040f0804081c020d030b03030a12060e040c03050714010e0409020d0f0b07090902040308090607150e0c18040f06050c040e010b0d05070f05030103061503150606030e03040f 76
    0x1105070703005008a1019920035105021480c1d05040b0861500c00051281d491018041c1c0d0092251859000c03018000c7c41c0382c480900b900f551040c0e00040340f0b4119681e1801c0000740040e0505a060085104460b81c07501c40345142882480e05c0c1c002d4005254213408202c54020980e00040310619011090340c1c040303283c1e00369000092003400340700700140111622000f090100038081852030312615064403004080b51701c84210070101d0145000c0100407081c00c0040001c245425030150500030311803041051010a2050b0311001d4030401041100706030b00ca003d8501540c5064600300704000c0d0701c00300c00c201d0b40c6440e0b151140340031014070014007407650310700c00301b00c040042400311409040400307070200442d65a0780242e4883c0d806054090641850715011500302482002680700c3d440d8241c1e0f0381806d603401d64031032100814000002c0c03401544008000030002d4070380e0041400710300c08040002030141c134248014043e100105548401074000f00400c1c001005100000e0080d80c80a0580c0710350300c0c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 72256054 1250 72254804 72254813
    0x607031b0f180806090d02060123040203090327010801050411091012020a050d0b010504030c060e03010b0d050102030a050a1808030612030c0d020d0305010e070305090a02060a180b070308040f 84
    0x21035088401e09005002c104a500318002810a031b00e808103600704c0e1802c1e0783e01c82d0640728800720b14050340d044144141c020811403810b0b801a40e0001140c00c29640740005840c40b880360715070785501c451b041401d003000c104500d60b003000d03900b40101000e03034092000758144030009040703104d061034592191180503d03035640d43d845030b01000c0c8040ea00f02000c41da1488010000361158001c80c1d80306801905041210b0305652050064a04603644420f000b050b0320f0405400356100d440000350f064040d076882c0044956507485a0503485040d009500050360390034204119803e541008228240181c20110f511841104941c0107015044d00400c80d0354994440b4000210404900e82010f0190310004c5000c004100011400c41401d00981c3c084a04405494a044e815510244505204035403d88002070486029070061644402030000b514900c042c2c0340e00259494200010500004081410048014042c0d581110207020710703c0380181071100315a0001d008050040004000c203091186030010031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 72257304 1250 72256054 72256097
    0x909090f0606171e0a021c0c1508060109080d050c070f0801022508070b06061b03130603060b04060c0f08040803091e0102151f080607031b0f 62
    0x381e801101803000e00e507909054009242d54860188041c0140ca503100c0070050582120500c00107600d000d00300c0d6000035000c21801400c840202140035414150000c005000c03440014048c15a4485820755401d1020b0300a05410000741712905000000c04184120300c4005014038035041903140c080c0d51610b5004045060070f0780d940c00b400c2900318541c004581c0d08010340150102044a00244060306a50740005110624051000d00890010040d82d03000c9080c0c840c040f0743c0910003401840c50701840140d0342045c04801c000d140c0f202d40012841c030043c40c10030110b60000b001c03203103003e010b900c1c244045c181c078600c580d07c075010600c828550018100483e980800d680e281d082090191180da03601485900d81c1e01044109100e400f140c40704000f042c451a040659900041c0d00405080401d22040b9122440c09400b0700700006211b21141c00d03440003501444090301407400544194282a800034054071026410101a9903603d03480340c103219807050321102d240003903280500c0031000401e682c5207070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 72258554 1250 72257304 72257333
    0x60a0e07051c02090c0a0905091e04110405010614040b0a03150b04050301060f0305060604050705131d06030a1203020315150a090b0a020706140c06040b0702010507050a090909 77
    0x40800200c02c40300e4900c1c000707001c1205034020b4481c40180e5072802003501c02840388440d00d0020959040c2c052106080042c14135500c005050400e59010714600c0300e10900300b0b4100d4040f0380c200340e04100180c5505041c0100c6004100c64101200c415640358203500c024000c601070342d01ca1301d60210b6141080381c460f40012803540f007541550b040554503108803004c0d66005024180c065820080c0c006040345000045208070b039001009802c454403404204805081d000c0e0622041240911160403043c0d000d034641da000b45541f88041c0320b1006030320b01d00a44040024501c52080c0c0201c841a004a410400000c80065092400503503d55814041c51265a0202003c3da00b103a400124a110b911040e001055070204039150020f41558528001c7c0651080005100041c0c0004100b002214007510000416802c100001820003c801a40c1803910408460980c3e1400c4a4010b02c03c41580a210340341c2c02c8951441c0403881d041c0c003920050400d0f010f0703101c0e00106590301c44014051201600c450b040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 72259804 1250 72258554 72258559
    0x306040b090709030303061202060f16081303020906090c0703210501030c091802030709020a030e0d03050106080a050103032a05010c051b060402030d030504050a0b0a09060606030b0102060a0e0705 86
    0x1450070039201c003c00960240c00101e020901e4032001180b000105000c0c407060660051030b062900c1c101207603602d01504103010981004ea510380c1c05500041c1303944013038161400c0071303105100510720310f004203c11010083c00c0b080c080c3c840c1400744103400c40c405080300e83c60764060401503030706020042080b1074010903070740704480309103080008803c0009841a0b103003100c410740e200b8400014482c103030164000fa048002581684445810032240d11a81c001c3d040307100043c18000b8264090b40a074500300302c02d050031000040d40d00d00041c0301c01500401c4103601301952100c100450b60450341c0c050910640c480c0a50200340502e110010000340e140300354002c161f0700030000d11504040d40c7c1d0140c503a0b0040480b0744a0140c40034403040d0701c0c000c002002841240c004004140c00780b55080250018003024005449500501300310350701142c02071281c64040d0030101000034070401c290404104451042d04210300705410404004035aa80c000361031900700741c10350303c0000c24842d000c0507940b071305589031701c9980c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 72261054 1250 72259804 72259819
    0x1020307061a28061409120606040c0516022202070b010e0108010e060606070c0f030f0c170a0209190903200303010605040b071106030406020309010c0809120306040b 73
    0x3500c14480800741109900c1c00c3d200241802c2900302041c21080c0220f46045100c03d44040030000a44039080c000c10194084041600e03040c5403801258045814200d011542d6205609000704c40c2458802c1d480505c44500c0c119003441c420284040c140c40e190080603108000c0500101181d8007503409401c0c2c0c111302100115542e0b642840e050301030360300912420402c3d400b05400010202d40c107001701c0c1000d980b0700010b0720659954600700b2819410441051701e0208160070b020440c88560080c01b005503006101c505503152a80c500000d4004d80383d080180030100810300305402460000d02d00306442e60445060704156a485030411080d550034151504082c10031181c2c109264024610802d0287d2407003a50011505030403483e0f0380c0e03100078412400012820001040070940032005017850920070108441c0950000f400900300e50001da40c20748880c0d50000a1083e00502445494600b15140c10034003020300c0c0241d200c40c0c60308040f48424a050b040040007905640e260384c0260b00910000b40110b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 72262304 1250 72261054 72261071
    0x40b100b0d150905130b0603030a0903060e070305030403031106060607020108070c030309050303130b1602070b0f040e010e091905070504110c0d02060702210a0f051e19170f060102030706 82
    0x9141460425000b030b00c084c141b0b1030110302c05081c04821100c1032710040e01c6240070785255a540100416030f44622804900030311601000140e014001840203500aa41e900704480f10380340d5039800e012001d440244154030800c403810060b41c04c440a82c1d400100f81c1051000d02e00703d403c05a01070600d45000810718000082081014803580c1581e00c07505004d040d60540d59603c40c0ac2034040300f006100702d20003591054004004103d160401001692502010325083c1a5242c0444034103520a8102100311103008003080850740c02000300303080d042c0785000c3c2102184c085880c0e0940700e9295000e131a029948584900c0c1d52604c042e412aa02c5035648011203003006a1800001c1d01c0c2c020580e000001400391003039655031182400c00174841134080c0f00c907403480c10b4a804c0c000c0d2480c000000740c00040c000706000c48000c4031110900d40000c4800889180e60342c3d40c224610010390345103000208140070f28006442d1000ea114403281e0383c440c4901c20310390349035199900141e1460180800c02841a41800c0380c0c07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 72263554 1250 72262304 72262321
    0x21504110d0c090c0306060323040201170f0115020303070f0302130503070305070302120f0309040c03091406040303060f0608060609040b090703091718010309020f030307050303040b100b0d150905 86
    0x3044c5505201d690030401d60b03403500002c60035038148600c440d1303180c2a000e54054411007d00c10141d00103105062070811038410595003500d09000b140e00d045050031100c01000190034031201d252101d04903201541c5949030600d005040d40303000307035955800c26501003013100c080d4812088420280400070103c8100964900e001542d550a070700040f030003410080402c40a2000c00140c60202c0441d030005981000c0140051000421140484c0740415440e14004004a503800142c5110b40d0001c5c0b010307002d545028203000d800d55410781d0000d003011a00140410155a000c0c0501d9000a022155140c0c0c9444082c0040c000d0f00841c09e41c998420729071b03010f003e000307074140c0d02050185100340003110b0f017502202e00c0e104440c004c92482c1001c203a040441c1d40302544c400c0c1c0c81a1a094401020200001c0310080402d02d0750308107240495a660000052000b805664142154404018a03a6807407450801c440c04031540941d080c90b81026440305480c40702c000004400d2809041c807040c0410261501504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 72264804 1250 72263554 72263561
    0x1017070e030a060b040c0201060b1206060702090108061506031506030405070e01080a030201180206030711120307031401050306010501050f0d06050904200f060301050d170a020607020d021504110d0c09 88
    0x8803217229600d03045070000403500600400f42141c03807030622641000000030701503260001c02402030f50310103c20000c0000590780c000d03c5030301074101c14008041c1490072108404980402d02d040700d100b40014420801c03141c7c40100603c1c0c0f076000686806441c1e8072a854075924141c015004030620b2000107001081030400000e8002d0100d000354000e01c4030341a02c20500c010740c0c5070058040d4101004000089015010351102c40d203491000c0b0450b5000c00940c500801540c00a8400100194031001403001004072088640c2c090802200941010b514010000c2e0140c03042500c8042c8581c40840e880e40c0d078405030f0740315a00400c40a441c04c4c03881d00e4146400a41580c1d030200c11414042005c020030114201802d201108620150000d851079080408012100c21003c00032034200981840f581c13041d84003480500425200c46d0000c2184e400d041e400030703050640d00d400c860115400003080042100300199815000354019024017000010400820031003c010f8201818041c001d10000991206550 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 72266054 1250 72264804 72264821
    0x1020d140106030203041a06010509220605120703060e0a1e0b15010905130e0114161427060705060106080c0403050a0605060d0c0b03010807051017070e030a06 70
    0x3203281d80e00c0d07000a40c100c1c04180c501034441d0184014985025001e05441a00b21405041040c188141400015402c102440790120f20415201d44190010164003c0c6005403d08460540c3d402c0c0e60142d55560750b06840c0700c0500950303100c1c942960f0b14001800716a2610b90815200c1d50003000003900045440da102d03070226140d00030800022110050703c1c9c5011042c0d4816902e86c0031307041c54502004506400c242c0f0201800d0740e160300d00d1700700405c244100d80b15800000f80340d0045203032200700000c801d2205031100e81804041c113074008084505108484810b143d0012202800c0c0310030303a42e083c4c0340c2c060500813600802c0c00038074030090050004016040350300640d0b030f9000325030b07070403032100d0480c0643d100050031a0b0000c128400000daa541090341c2c0a20f001d0035841c4112129211366407200c41540c0a0842e10f01c1c000018001c400050020764083c040c180c1c2d0400c1941031081d0300400c225920201030040240e8500400e042d80d107d505100000803004048401e42c034480c0c1000b600500b00003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 72267304 1250 72266054 72266081
    0x60a110d020c0306070507020d030f02121b0d08040c030f08090607050627030409091406070f0f020d120f0e030c030414090628030501020a05040815010b090409060e01020d 75
    0x400011700c1c4501c102c01300c512155016105400d49d0b0f1080c1c1d01074641d800d02d00e50758029400f41320005030a1134900741c05880c0c2c01000307007a281000307082e205c1c0c0c45090503488044c40e000c1045003c10080802e65102ca418216984402015202505414080c290707020358034480e6403040c000585241070107030004a207400b43c0000c0c01c80c0625032031404040114002c110312028200d810a11041103031908070f81c40203640354007031a48550440c400340368883c1042401c5880401007a003140c0c09242207a800466200c2424542c00185105080050050a000fa00b08808400b40d52189810400d00b00c1d00d410030120320000908032070300c81101442e00c1d601ca4029018903602d202c0c0381141070555140220303105010300c0000e0480d03404c1e01441608080f0209000f000e9000d00045444008001030091000f8510180203544154445041c8604141040d480418400c4407090100c018003030000e0800880384001421107000031452400e2411401402c02e03026108071652010996070071104050300501c0140404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 72268554 1250 72267304 72267313
    0x9050d0c0201080a050403301107030816020303040f03120f0b040e060114040207050a0807050303240a14010c0b0a02030114030a080d1802061b060106050a080402060a110d020c03 78
    0x44e081e40c00b04a0f00c0407180030b00004e0403121040c80c070003810301c081044e101c103a66038020707a082900120429501c9110101c00032017000035600042c1503000c0c80181d0419403800081903030a00c850707c003d40d6400050009444501a00341071401c040c0109416908039010360400c0c082c941c03001180000815510103180e00450521031056114200815864144e03016800110710040700a03082c00000e400046003282c007841820601c07804210158040c10301e00d4800c000541c2d503860903500f6440c882c5003500c2c0c0c40c840c06004034100d8280340d943d000e5907010303164401c00ca8146070782c180004075510442c1c0c07103001e0808000101071140e903c03c0c2da00118103172000c070a807562050000d4800e1540c0e680303561401500c03c03141130111036025007890300b013004003200d40c90319190070190a03000608a07600001042c0c445017502003090440003014060580140741d40d06049051041d50b460240c030030040200700034800d003400941000494011031502220b00ca04900b00d43d008000c244020750360310f941a000c2d5129114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 72269804 1250 72268554 72268561
    0x603060603020405010503011406040819020a05120307240606030f0b010206130809040b060c010e0f03030603070605090a0308130602160f060503060102011415090903040e071209050d0c020108 84
    0x30303000320f50403100c0c10781d2241e00e16032a00d403c00584000f1340c041c03645d00c44c0040000284d0b0b80410403a02c6040c62a01d03011000c00001841003152a9203190701240c0510084807500c40901e1020040d03440c42c9800c164041594548044949015180c40e030840780714500d0400c000c82c0365a03140c1d00912881c04440d0b4204020140180160b81d29501180d06071a00d02c085041140014070000162017800c0c400341001c00c00f2030742c0300005003031a040900c001055a40d14004251190310400491002c043c0031400303103103581098404691a41c0e1240140d00601400141c1c00003151a400c94110040d604400c180361502e044040c0c51000c441c25101c1c5030014403030760f000b4000381c070400c00f949021108640807010f002441c00a0650301d54000a1113203055558402c1251444d0743c00c910401d101d03203c0c4600c5150002c00c00c2003001402c05000e00043c032180d0043c0401d10a4030801ca400f00e800070002d0a010140c0d0200d01100400f81080c485c00608502940540114040d00002c0030b9180c68401d1305c0d4000681d6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 72271054 1250 72269804 72269807
    0x60e0114090c030f1b1c020c0d080c16020d0c06080417040602070324090b010501021027080409020c15160c02061608120609070216140a03051606030606 67
    0x800c1c0c4e586500c588840300801c4050901705000001c10503c8030302e06040079102d01c0c25900110030b1030f42d01622183c001551051014041c0502c1181e071041c0d0600c60074500b0020b0111900b0b010b2440c0b60741c80000d0b80d401000955550211014615900078800c0c0707400394403184018280c040030340382201c0c542805240418036800d50010755082d03d81ca03a005180781443d54660243c03900215890f2880298044100485500d490180600c0340c0d0045200035003039403602c80020724049a0134070303100c04140741c134010b01c410641c10b01203450803241301da10402000519040c012146c1c81a42e014841c2c551000402e41c2d10707410081021400c04582044429991791703590703108851104c11404950004500203000b000618101c000b6158030050501d0801d86140755a890001e41d41c0945911070b504441041000080d140111961703a0104440c4081c0442402400703200c08480721502958a00c180c43d02040c0381c10ba1641030300d080003990080e0841c0c042203003080004122010354080d940020b410300c000400c40a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 72272304 1250 72271054 72271057
    0x915060e040f0210110316021306030b0604020c0f0f06060102070b030c030f090c0a0906030209060111030d091b0306050702060901150e060a0807031a06150a030203060103060e0114090c 81
    0x450b042050250040030a03420810303042c881e03285040c180444c1000d4485c407080204003600610b0240e00c042c40880745c0c1401000090b039400040648003605100c8144001140154026004802a2005078517059040c4039039081c2040c0e070f5184544c84c0700f00182400070000024440340504402c3c0c00b9102c86988900700504030303200807200260511810400f003a8410b040c84030456024080b8815181502c0148000a04120959000600c0f071f0f44c403070300203005505e84821402e4205000342072038080d29004030f810341d88078010036203250121540c40405c102400007401e240020351420070744400b01d4a8481c50280000c19096803248018440c000c002078913500c051003201048501a14248041481c12154503c0c1c0d0f18010f01e443e030440f5040344001890b90040040b000918403505824003102c000765442071014100a01d924403800e620824084401501c008036040212149400340c1e0b0382e40c4890046c0d0280c01e11340d0090080c00d0120000041c0d00c1d800c070100c501400300031505049141c88406132503449 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 72273554 1250 72272304 72272311
    0x150315060302062a031b010b0301090f02010804110d06050115141912050405030901080c04051815090106030e010f022811100207120302031005040203060a08010915060e 74
    0x1040c03080014a164a4a51091030181c040c09452400e401c501c1005145c10354000f8019150401c02d41440c85016540038080e04282c00025402000104180d480301c0e80e010304604000784c18003060001103410310019042e1940c4410014008030f5a070007851424800070f05091144c02d280304010462080c52600c5580c0e41560040392480722424186071000b6610711209050030b51092000c5000c0c00d8140d1403803802001e200e50301607006076441c2d80c0120000b400882d0700820702102c9030710170041449156120f0703400080d400540050019559100485000e40c00c501c2014250f02414410000504a138141c001d2070425411074000d1000c81c1c903140480c016401100310781200349031842c0110f61400da01810102019402d880e2040c003501c500d800b41c03801e04440c92503c48541e500082c40c00300f80b00f02d2001ca60022946890b0862451800c040300a2149140d030040c28800c1c0d4002020802c44e035a00e01e45103014040c10002040f4a00e810301d800120244000e1990300c1031402e0040c005124410b03200171920 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 72274804 1250 72273554 72273559
    0x7060e010806150309030d05042604151d1305060406090b0306040f02010c0b01060206090601050105120a0c1206081f05040b070503040812040807050708030901050711060d150315060302 81
    0x140030f25800d8031003c0e82c0c0c10080c51000c8a110511203554040305074003620f0300690140c00100c0d4501c00d0040b0074000040140034403501244104400c000c8048414044060810b540ca007a240000c0ca2100a038100200d01148961205d48413420f80c00c5030484d607001d036000e030710100e070b041001c40c0d95034100c00140d8082050741c40d490741206d800a404501c0c2002c4c0c54441a00c1490030103080c0340c4581d03e0003407505082c0c002c01e00591014080140089041152601400090038542e0404a000c41610101720000b88070103a420703107541007407032854000c000542048403010000e0002d141c603003024030b0765100004060429003400c7d0a40c82c440701d94621407070b402103802c100015041e030303904181910254409030084802c1ea60401c420f5244040300c4a81a010301e00c0307010035990b510214100300d440d00700c40340c05c0341c0d41c150420082c1c14000c0e038019040300d00342c0d9406042d00344a100020300240450181030b1b00c0c100c0303040c241008814418001c60035801664400c146038000030070f4038442e400496415000094 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 72276054 1250 72274804 72274819
    0xc11010b06160501180f0507050105030609130201020a05010606030f0f060e040215190f020c03010501080606011b120503061003020412060203090a02040e0609210702121e07060e010806 81
    0x440c0328107414400c550641c0107400200d48005d11000c0720700013030000740c41620030721940c01000007003040030f1066000412003444d010b4114104840020803000c4007074011018149a001e0800031079000780110701440350800c0080005030340e2600084c01070019008241a00d520780781070580c140c20b4521910b019613040b43c40e80f40c07a9503555400d20182c000040354182085c03100b40041c500f00610b8a044440e45051a1b94480160702818000ba05d4100d0b46039003644070f039040c900140300c030500c0041d81c2c65004030240703030601100a65182c100c111001c2c1c4200a4200c2d035100b031002c802d1130703080700044d40500c400b61129584011340520842c02ca002e0b070301804c19214500c0e1030341d01c04562250065a0041c011301c066031201c012550000b804c85500e540003e401e034010b08200500c401c01403110303440c0440200a4003400310740d0000c00c0110340c0b0030480024414042960b901d62a0541088400180a81c150100f0705030203001c02e40d00d6491425100e402c0000e01361001500055205e05240ca00030140940b484 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 72277304 1250 72276054 72276067
    0x80f03070803070e0604090603110103141b0a2a0c05031501051504080d030504020a08010b0a0b030c130f0e01170316080903100905060a0b010c030809120403060c11010b06 75
    0x8803003c1c1c13210396100d03511000c14003001c50f894000f8400c0c080198411200498807805003400034040d160200c241d0000056070303400300451002d41c4e2058403660001518a9a80d81082e040706961840c5071011082480c51034100d000c0c0e448100000740c40020b070152030200f1661390307240101507039034132000c900c40060380a0b900104401d040083c204683c1030703e0360340d6807420705449901041c41c00c03c40c44035107400607813100f0921056003842c00150020708001d400920042800c0404554045001e214001c8202c00010019480c44c90b43c406440c1c2d01505070210024080d41c801225140400c00e0085141c1c120701d9800011b03001d540001d0b20302d4000c0c3c40c2130195007402c191044080d24090200c1080d80c40c100c04102c0240999400d21030248030113200100001d000c078160070314034605480201050300c030501e011b130522180ea07007080164145a81c5480d0002c0c0507600d0808440c2800c0c01050741c3e2000c00d0021070040f042010304e810003110900d8a54030904d000c006c01a00a090741c2c030865185070003501c1013014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 72278554 1250 72277304 72277307
    0x1050f060c030406110a0b070f0905100f050f0d0509030304050607030504030801120c03050f010c030e030301060e0607051005040303020a020606030106061b0c0509010b090112020301030c090c0e090f01080f0307080307 95
    0x3900c900c1c01c51009494105030309850703d15071f042080b80d611000401108035a0389440d0800b102401401c800e8650b141d80c04041c040241100c1d0b4075002c0a0140040400c00224484080e030842d010044c03103d03020b01c02030510b2244980e4a400980d0300301c2e21801039000251900c0c0c880c1c850305119a82564595480741d03c0d00281c140c81301040041a42c080102a2010010410400240421a50302000001c0040c4240002011510130014040a6800130401004225400070300f403e0031000071190503075901942c0c0350081c83e0450000d070b1800514144000c01040c1500341e40034080c01e99054094134072030b95a0b0800c0500301c40e83c6019000203d850a0142c0b0403404000c0300d280c040c144200700811a0540740c83c0000c44021003688804486240004c8070603003940d012055052801800609504550443c1d0310190b07014954060145160394030301000d0301e01c5200c2c1e950b07e42614800392046485040c0108062034000e400d0140314080c0c41589802c400028ac000120350056402c91200350864954000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 72279804 1250 72278554 72278567
    0x9030405010806010203090316170123060112050901151d040314070b09060103020325031506030f0c170304080a0b06011e1215030f02132301050f060c030406 69
    0x20f401d04611081c40342c8500d070f031420040146529007616034410014034142c150100b40036440907248d420390428003a030300901c1c0602c80180d03010f01c0b042929040790392060012100207180203001c0481c01d00740424004140c0d01036008101d03081e1080d0003071031440d0302c0701c0900e8641c40d00e8802d552600001c100004010a100b07100701100b044503000c080c1d04e80506031700d407d4502d4500761030081080d0020f000410461404100300d81102c140c20998003000d1195502054540286c1d11000e03002140303030004441542419481407010b95030001c0c05400080301810254251480c90003891421703902018406c0288a001040d02c04076144100101685030322a42c40d0041e03024090a03050600c8042400a040384030150054581c010496948035925181d422011050b21140c1c2407440c02194648400d001190114008201d060707010740314440341210000e0420002d2012032001c45185510012196601754226412412103608480c034004c0707008001b041000521440c251280d40f54810002048040c0c081e64 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 72281054 1250 72279804 72279811
    0x60103051012110906010908060c0f04180c0e06040b0a0c0c03050607110c010c0206090118090c03020c010b06040e130303021603260106020d1d03070f08060708090304050108 76
    0x34581980e035940c02620100d5014081c04aa1951810481c8101c50504000c4c2c142c0c05442440c00e49072162500c0111622170501804042410300e000800c172440b1103045044400030058281031548480b9542103c1e4000c00c402482100002d40d600c1040c40300d417600c4001d484c10340b080d400c0e1580c582061542c0036200060b04000c122105200040c001007c07403800d100c15403007464144c4a400756103404c039003250305102a51031518140020159030302c3c00360300c565085d00e1080c00d0030f01386160305141004040c04449900d5103c04042e600b045100c010840c2e00d50042c024501d160f400a01c0904040020000280524004c070740c03034a2102c40000300c46a1582080c500000c0c000e080043c07808040c94002c07901e4006242d025401f0481d0140d054000b45030600307041d6640120410821103a5040003002900c0700100402d8800b006134021440d61841d6550501200b0341c03c0c02030840c0c25107950349080c480640600d00c20392a040c01128001440c0900030546184995020b001562400342820015502100050f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 72282304 1250 72281054 72281071
    0xe06180111030906040c0f0803070b090a05010e0c0a0905011503020f070f0812060f01080a0b1206090d0201110a020304030213110705150603010b010905040c11030310082406010305 79
    0x7000d9401c00c0d4041e0100850090b030280014120529003401c0103482e001282d44024881701c04910100001100071040e500000c3d48a144c0741d109417542a041450034078440c801501075480c1c0f041068201400050101c0c108405030358044415036241408811602c0c24481c000402c2d8030110b0f01444544203a00401380c11032104006818015582c466a54802c0004422039200600084507030903240d400c42481c2d80650300b01c0d04001d1a05180000824035040984414070305500e80d0b030301d01010313500c07160403580c80e0700050200c4146140040300290f40302c0446000d6000f6500e02501d0316840c00413541160040381441e0029460306155509000c1050241d07000744c01450303a2408841c0d61016094010410140103000410701000d00102c0c0c15450b0303001900b103903c02c1c2e14005075030581780d821800300d1040710b500300e9001075031081401c1c0c1501c1c4d00309110b84034000d50000008100c4034101c040400c6083e11400c1d41120311890030665502c2c110840c0c1e0300e4078841c081c040701c005051503100742c000d1640011392 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 72283554 1250 72282304 72282311
    0x20c030a0f061b021018050a0f050709091a2505030702030f0c01090203010c050310030605060d050303100602060c030103020108150102100204090903320c0a1a0105130e061801 77
    0xc2100030074a03006408480c80145c20546070131220040d1401141003418120800540d01c2c0707020340e01d0990368011500000c0508810701e1103081848400c1c081c050050070544420701155003185400c07910340c41c51009640c90300c20010041107a0400d14051070114101418032610412030440042d21035406c024800004c41c0f00c200454043e0403100d202801c2d84181c1d8100104400d074246c4105401e4402000b21a000c000c001e008000440700039012940c04c9a40280c4006601c3c0c543d070011407030728102c1040c0a0700e28400001402656503000c01c00c0c0c8110f030070941c00d9800d01e46402c1c40310a820b20080c07001a000802042c04601ca29090b01c40b90320040300140100c400d10111207000e4001e0360001d03445000d011b547c420981040c1038003c0c0354000c0801452024802147e981e445260690340381000088070100040344a07021840c0c2040091015500004014140034864a00d192010400d000b018000c40d081502c54981d0020390041506240840000d8501d40d601e95501e5440501c0004030802150348 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 72284804 1250 72283554 72283571
    0x40e1902091e0102010e15070302130806070e09090705180a09050604150b01090b040303110322030c0602010902010e090903091207090e0f0c040504020604030b1302040c020c030a0f06 80
    0x240d0011441c05400c0070062207030b6280c0c1a03000039003124101142c080b090780100007180c0c00c40d00009a1a0350190683c240183c48039410b40c03004001c80c4a03030700104010f118020034000b80c2500100c114040c0c4504035003404140e900d050003161101043d02c5a41e0b044084007100400c104090405298404010003000440e03880e191102464108156000d44800184c10324503c009032040c0070380f04104800307003083c04c0c2e00c9203000901b1025208030700c00501041160915406459414411941c007a0071100000301d848115114640070348826205c220391100810000144040c0180514141150161200b00010180da001e100401d0402041c5520501040000f0003459032420030440710030015500901804d07062404441c2121982d0501441c01e600107a150307440312000003201e002d001019100492103844030b1011038031030b0140d40c00041508004600308983d542c442803006200364001c440602000701c107054143d0b1141030b8612201c0c0c042e0003800ca028007140a81e86034070300c41482020300144082 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 72286054 1250 72284804 72284809
    0x1050a05013b030109150506030106080a02060f0f07060f0c1b0b07090b0a0302030f01050a151d130e0c0405060609060708070812070f0302040b160201021203090120040e190209 77
    0x1801d140044446d50300c0800505206401031143d2030703202c41700f40d000f002083d050481a030b47e02e010000000b48217800c0011020041040c82003503a10300d465541d030300343d100c202c00d01d4950080d00b81d009007250041d1501212900e90f5104201e0342d20420a0200c032a0302300e6656490b02444480c0092001e000c2c04030928001071220003c000400384c0885a580c01612400c1c0b11a410f20b0100701a44054819103940c8000e008020384c00c12160000c500b14200f189245031259110820800010700305a4840c102d030002400d0b400f81a00034100000d100c070180c07400d02100008000450303100351186ca41000c824480c0d0941c2c4d040c00702c014900e081c002d078415402c007420347d81c1e855500e40c1324411014003d90080140132610341c01a00566982800c1c3c1019810a810645402610300480d641811840a4404100b0640e4001e04ca481c11460000013101c0c0c0d20704e44580090301800100508400c1903251004e80c0141c100d2800a4505540c1e03440aa40d142c0d45600e0184190380e01210f80140d1901d0b801c00c00c0c00180e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 72287304 1250 72286054 72286061
    0x10031b050a06050d05010509010501021c02070f060c060506040c0f0309080d02070f030206010b0a02030a0f12050406020306120c030a020607021305070e01030b0405040b19060305070b0301050a05013b0301 89
    0x8015a5075a60b6941091003804d90503114180c1c445806003580000502240e038005c1034103a0f01c1d404500070f090140c164031500f00e1038165a075009106159280c03c0204034158040000e01016001c3c0c001032200351103010a0004840020b032205000a9509180a40d910321a4012206060180c0002c90504000c00f51035812603000d5202142e0300c1c00568514410103805104160060000491050404911803c041d4882c0300d000c06010820104a0784a03c195002e2004015901c24000c0100414541413910390000c3d4001d4400c10b125000301c2d0940909003200141d0304050240c098094950226a50300b4014a5004640101c0e4022164800010281620b11a00380710740c2d080d40d19208902e08050000d03080310807003031080703000741c0c20502000b000c12541004190040610600a200c828480740441c0c0104000d030401403240c003038200002418508200a9030581d0700c1101c25941c0c00b651080159142e5000140703000081540780240203204119510281040c1c200080e012044c256074000039084 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 72288554 1250 72287304 72287309
    0xa0b04020c0a0c05030d0e09130807060c1e02100507020a050f030703090605071e0302030c0a0b1e012108040b0307031e0507170a060e070504060201110310031b050a 72
    0x1a68041a20b07501806441c01102009010650141c08401980c000c01040410307900010381c003588000b00801c100c640654401c90070290000b1845443c0c1c0307140c1c0341142c0035004641e030b40030000d138002000d820300144100388904002c00d01d0f00182802410882c980780500402071940007503006001000021030802d12001081c0701180c07001e16a40d02240c036003c0e19015081e0889410400c09100f01c000082c440848644418081c2c810401c03400308a140492440c450704100c1902030040d0003d00040006001c2c00754001c0c80412454207210b21581001048440b0034401c00d0360194a00c004241c03075900801c288044240584c0c00580340c180c65809429103503005030b074541c0010750b64141919034101030b03c1004030f0400d08039a0511490a0040008080c2e04000355414040c007510000324903445001c3d413200c4014080c4804941e01882c1021016001d900280b042a0240d404e010100300300402540c2141d00c01c1c441d901001e9801070450316184504480d001d0310605482c0e500750041a203694900b0903100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 72289804 1250 72288554 72288577
    0xe12070302030d0f090b0a0c0b060a0321080609090316080904050c030601020105060f0906010509011106100302180403080c030a0e010e1006050a0305030a0c0206040314420a0b0402 79
    0x3804d10312004042581a0740604c240d60340c1445941c0c00300354420b110300d604c10b82000d540d5a8a80b9a600000c0c4104c4050740000e02784040b0040d0119542601c4c1940905104280c90700e1107650b07282c4090055801c8110b0700881c50340c00c20003882a0074081d2445a00005000e44031403418100c01e440840c1c03c07200d00b92040700b00b00c1c034040200412076a0901519501540588911484e650b00001080e10000041c04283c14041c01244004103a482156040d40030b10317640003120100d0a150040081220142c00164020024040c2100000780502c0e500c6e0b01450740355407005101e40e00d9600c0d980700398001070070141d401c940b00e481d1001168824020814814400e1000e42a40501420580c003251910780c0100d014911986d030410100300d020040c0c40f00d0030751360305024028010a1000a0103803186410081c03040044110412101c480000c079400d510030f11038001420300c0700a49040c0072120188052140c00068000e403244422240d818441e003160004801041c40408030b400101a80c020014160 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 72291054 1250 72289804 72289817
    0x210605091806010303050318160303020601052209030e030313082104210503030a0203040b0a090f02040c0908070b070203070f05030601090c0e10050c0105090105070e12070302030d 79
    0x4103203022a15036412000c07528180c111500510321a6456490510015090000c04000202001d1820070440d14a05036003081c1d078007031000c80d2030120b42200540803e400501c01c0000110b21402c0c0700003100c0b25040c1c41e180e940b0b070301da107503601e410068045524110100040401d000b50f054804001030181c0300c2100c1840e01115041003040b920303080c0c0604e400360859881c020b545052000074400c441c00e0300c4400641002180321044004001c00b0780031380c01000791000104001070318041d03901460080e44652500d000540311145608140c5a45a8000e011a03101002c0c1000616081d400b0071641009070904495240c0d850000a05084403a8040c8647d800c0000d00300003145002d000c604003500c00f42003041102410200071079501c00050042000341540c40e81800706042c081d411021090314010150080d142816000400c40c1d013000090011075820003000c9040b500301800b1b00e41c82a51103980d040c221000e5042003052a078800c0c100c6030110b0098000210150b14244084108110180c035100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 72292304 1250 72291054 72291059
    0x108030910261b04030b07080c040e0a020d060e090706030f060e06010c080d06060e100804030203031f050406080c01091208030c0703030b03061008070e010b040509072106 75
    0xc1110032040e50000c0400904001240001e0180800c5140c0441070005078112a52000070303d41010300c1086000f00c02d80f101044c0081041001281035104944543d11401c99031900b41003007806001d03034021780c0040f1812000140b103114032039029181c001016503010601c15500e02c40e4080400c4155080c10203500648001d10426815010304e20b140200c1002c10491940b904210b2044030801802641c108580100501c007400405400d0340d8400c1e0b01c4800410174507940307d9018003040351600589005055003000b6502860081c940a4480d540513005589150b40d586928001c103140418121562040e01c540800e5a444034801d600c00390640100601008070324000240c65103805a014212032010580e80c940002e6400d41503d03040001000c5942e118120344c501540a0151715107080c1d0144280700c1000041181c2c1c0001c4030440310004191105507480324881c2c1d140000900403800e0001003000104000d08009010a80c0402c15280141034500341107490240c0850380e015401d440e5442d4a001e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 72293554 1250 72292304 72292309
    0x1021e0f010b060310090c120c020c0a0602011e05071b06020915030705040302011409191a040506030115020114040b04050c1c020409060b06040602030c0c0a06020a1704050901080309 80
    0x22501c051004580603804c0d460041030810032a000c034043c54480c40c2e26202040e450310300480306038100300d002c2c10082c0120380d40032400955503010a4202840307000740c41d00002c3e2207801032241c039617500310b601c0d14520703103844811050014200203407482c010419506000c001c0011800a0b9048103403242c8000360ba11482d00b0100100301d201e0900c05424060100140480142c015007240c08483c0d0a00340300540e51851099841c407070040e80f03152500300d54450004950440008061000d54441c1c0c2d8052140c449484940403250045010b6640c000804100522074075495900c4480c1c0b000e0300c2c0c40013107401c0c2d0580b42c01d01e42003001540c0c22901e1000c9241440708200e0240708220140c00c058818400010b858030391849682550f900190007141e90381c40b202c0078060700da08042548280608525601ca030381d001c000355241d00c88411070074a03020300c4498404502c5c2c0070500c00304441517036000746400c1002e511010803a1011070b1024101c4401000000385503140e0401c0790b0b008000c08006552600303103c3d0300317 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 72294804 1250 72293554 72293561
    0x415020102030f09030f0a08040f061406011101050912070c0305010c050c0705010f0903060b0a0b16020f09040b2403100204050108060103270201120207080406170105010f050901021e0f01 82
    0xd5482c079170014406411030392820000d454200c1150304c0c000d2030507101c030b0030700c101e50101d0104007400950501c84c6117840d00000074030180c00b441d42aa2048811007240b1074003400c0311070503070704412140c01040040011501078805405040d004e040020034003079596480e5804c40316803c40407000b14101190000c0154010b1091900034982801e041c80f460b107607217000810425180c00f00074003150f0340d1601c4a01c50313266005858081d182030810780c1d5850010121002400d624280120310514100c0c4c0303d0045801c0440c1c1c20b5015030350018044180c4d40b03c50010980000d1074000d4102c4d4509891105d040c82d41e81041404c0c8511400f81006030749905000004082100c002c01d030310f05050a06103003d402c83d05080c11120303882200c46414440900e00d00c0102c40740d84a22a241c2040e0340041050000e000143e0020011a100c50312910741c03407103140152420240b000d01c03c00d400700d0110280e804030540120010203074032405105481075080c95850031030b82d80220301202078a46e4051000500307607031804d20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 72296054 1250 72294804 72294811
    0x3021c031b030915091406071215050d0305090d050114040c0e0601020a061a040603151401060e0d0c0305030a110f030c0a020f040204030209010810180f1101050415020102030f 77
    0x15003840000710548a01d1518400025901903455440d8a1041031010543d60209441402425130b41d20781008c1d8001442204405600350502d850f044006038443c4018074030710210303180917210701c61a019a80302a100e03908032080c415000780780c2886c0710000500a00c28610025100c1c02210281d040038181000118541c1d000114403e03400f00c00d000c800da800080c02079400e540038802064429104025404410414400303036045800c01c0c5c0040108a0144141c4128100305c5004014203041540e034486c00104c01c2c0720301c07004100e0001103406141001c82004200f10700490000d0030b071540c0c903a030361461640018111b00000341450380482a0700030030b100e503001000d02600110308288910b01781c5604e403809000000e2042d0017a840c004480d0300c641d0160b800550b002170000ca42503a48400040d1038a4030011007441c07062412050711048c40c8424503200350180c1040c0300e1034104486940b101c0c031182020040364107004083c000000d0380018460700359070307050347c0d070b800540c99040407800100c5448018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 72297304 1250 72296054 72296057
    0x6080705070b04170d02040e0405010f0b010f050c07050604030b040510060f050402130e01170d02030a050306040905010603060c0c02030616051c0908040b071101080105060301050d03021c031b 84
    0x100090710106405a0000340c101c1d403c009180218001207110300102e110b51003004007558008103002401d1960900054030450040000740903030b40700d031241a07088031001c0c7c0400c0c0c0420446142404590701c2074001c1c1003c148520111101280c4601c00242c2541241d842156255851303c100010041c0c241f01d4160142d5503040309002046c00d00003862548049402110302407680820b42d0840341c003941c52560000d04c100c1540150a5071100148010b20680c401d00d44010311a1000691180384000308540b82c0c04650740d203003800c50319104100405030140346001c2d40e8541d03c0b00004400303e0039612801c40c0c4d441e1141c9450b8010b03002e51042c1401d10030b009102650310090101c100310316940100440d81034441800d0b450652895980d2060010415000050280100428080740540300c001c010681e85005840c81c500c069201d000465a880d03003405025000702d01840100071320700707001d40c00ca40c10500c640161101e45000340780ca10b1450424010700000613880d0801c20700c80f40070450006081e000603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 72298554 1250 72297304 72297307
    0x302220b031513020d0b0f040506070e0906120a0501151505040b0904150b0c01021209010219030e070506030f060108070c030804030e120d03050601020615011b030302041a0406080705 80
    0x900300c8104034000028910310322120307081c02c0c010855a4846540d1412540f14190040c9406c00382e0400344207d1049074211002d120724804198014010000d00a80c40c0c8000c1078241680c0e110003d2004800514405a04504c10207150f10f000910a015007610241441c160f016031030320b0000c00720028903008940805201c0108814811f0050220071610003010950340801c10100160000c82000740560204c2c241500c089504c0040d590306400814a00c600201d0000b81c545943c075405e800c0f0b2185092070385400007507000b0710fa41c29001c0d4200703003006d9801070240d550031a900c10106c2c160798001c43c1c0c5003144c942c5280401c0b42568201c28880d4001c9060306c1c014a081e44e8540e406815030364043c20240501007904070f004903a959039075140d00180700c143c050701c10390b05540202402402041da10203000d03010700740001c2c0714001511900401800f0580d01d40580818080070f010b00c0e62003129007503040580030080420b0103500340710700d2917842c0c00d1054050f9072145454001080c03568050866800c1000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 72299804 1250 72298554 72298573
    0x210a0c091e0509040206041d04150606050702010c06020904090804170604030507140a120503041103060606040b090402070203010207030c0501110721030b040e0d110a03050f0a0201060302220b03 85
    0x2450007070311003540d5081e11034003121348030750000402c9809071781d0011124036117481c1c101c08114585000c0303038060f51280c440c99030030300e81500c00d40095400b00d006003000940c1c240840c9026611911030340b83e5050180800500e440a108046000e0320110070043d102400005410401031070240d5424180001980190080d0700305035070000c2051003450b0000d021710341c0c618000070815909000bc0424594000381e8180c02c000039a2001e80150400c86082e1400301070b0f1003103110141004141181701d0a0018203c1d0300e45800d041c00c50751943c2000c1800c0e5002035080c403000d80140c80034402040114080e4486503c146400d00c0d282e0b00703407486c0c07a1050442480a002c4000040d41030505c034640200101200f0061501418003140204000c80c0c06039449800c1ca03034a0000903070302113140045860310795102503d40c40b00c1890281d50300c9801c10014000b402c100080c0c81c3c00c407001d82c007801d0f400341d0a20011038030760760f0f85d000500103101901daa0307500d5082d000010a500a0750f48190030590b00190007600c851032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 72301054 1250 72299804 72299849
    0x3050d1701082b030b040218040b01020c030d03020a17040303150b040303050403150b04140601020c01170103030c0503072001030b040b0a0501031a0402030103120e06070f0206210a0c09 81
    0x203900f2150a0f10901d0f01d5541d528001d41103d425048082c000315107440c078660210400480c5845041d0180c1e18001425406500c00320f0f69910070500603004240c03169071002c08400039808104800204000c1400c40c180c00014050214040d50195901061840030100e10420418840e8403c08150300304000410000c0d400400740e4080b2a0071070000414180007845180150443d03c41a5611915148200c050b50117440c2005000301c000b07074201c400c00107248005448020015a000440803003c1c00100700280c072403100c041c1a244201c094a04241c510396518409806002500c18a00c960115205013940e0500c40c40740414812502031005900d441e0102e4050010707801110704064449000c1030301462072010316a50f180c80074008566079030350390500c0d100c2c4085080c802000a41585444511490920280c9070055044000c4142c03403d010341c00c1043c81c1c4d1000b241c031607170b803030040c2d03130f10f8910f1210175031142e03c207000046000c0790f0001e01c3c01c7c00a00750b440300d03008034030344100e0036240c0190031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 72302160 1106 72301054 72301093
    0x50c01020c0a03092111010e12010c180e04061104180608010501091506050901021207030f090506040b04060c0203031b0703031202090f0105030a0603050d170108 71
    0x517520350001e00e141c1c81a0304140365002e108000e0000124100e07031081040c410701414100f00715402880850350440c054070303c0004076552102d000c51b8041d0045802021100d81c422000106800c0c0071058030160300242c07000c0d02040e80e07007843c603261020a01c110740241c03510b0402002036260302c8220401400e51809402029420240006201c50445c001e46200507450241945000e0901c80120b0380c0e50000340106045101d03003041340c6100903403880103000d0140240c0c0c076440048a0014080c002ea2000e6014030f0003510b04210411108007a6000d40e01910b19500c0d2441d04040d4900000e4514095902c01c801144401c0100e070b011004001800c40403a8030944808058101ea080b40d03a00302d01891585503084103061075a0b01d02507118400459000c0302611000600c15241d0300c0e900c0c81d24003032205640200e00c42c20f80100ca43c0080400080c010a6100c004100340001c0c500f220019 = true := by decide +kernel

theorem cover : BRFrame.Cov 72122304 72302160 := by
  have h0 := BRFrame.cov_init 72122304
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72122304 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 72122304 ≤ n) (h2 : n < 72302160) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
