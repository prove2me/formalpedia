-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0485
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:02:55.583162+00:00
-- url     : https://prove2.me/submissions/3be40b24-9649-4203-a427-23d8060a9fc8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 87050360 ≤ n < 87230216 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 87051610 1250 87050360 87050389
    0xb01050d080d05130b070e091503030405120a0b0403050d0c050c1b01110a0c0f0503010e0d0c03020c06040303020303040c05040e120f0f22061e0e0a0e07030b0406090e0309 75
    0x50401340d0030960750498074450648281c0d00090310600941362a107442414203800501e0707030400b200c0d4442d222003c2600ca01442c0703d0756219003190035442d440703c1c00502500100c04e500542030420b92400c1d140182075070304038036118021300340b410052444240c024022074824902d03040003440c94240308001014220080c40010741044449400e54100d9842000780a40241c4030322200e580d840c2c10403c3c4001051000c1d44050320a80c14070b0014640c088002c24540f91030540d504e0111007841003030400340d203012401c01290b50000c0c1c00007000814980d002c8061402345110700070712a180350b901c00402056500601403620030b81c010006010502c00701400405c2c020f0b882141003070801c0560b12254000781c102110904005480080810510711030300c4088010b072010f41070180c81c5c1c14124901048030341c14a0314410501001510400c559645c26919800900003240704c24a10b25055200270007900c101048c017800345003040f00100d02d0300058040c4c0780c9503038140380086082850303490800607445600390b407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 87052860 1250 87051610 87051631
    0xb0a03020f01020a0803070309050f0d0903140304050306190509011a010507060608010216120309082a0a0302010b0a0e0402030d080624090925050d0e01090f0b01050d080d05 76
    0x44c500e001440c04e401841c428130140c0ca0004200314981040d0b42851500d0340703100065000600394002854100b140401071329000986001100c4d01d01d6215455031066410460303040c804c4034100f020100300c001c8505d41025030842d0611250301c84c40304d07040c05d8618244000e00240014550096107521500117441910f01906000c2013880d42d81d5552030899020070300c01841001d0b1503c07841d0501448072a00800d41300e192074100100300c61500c81801c40d00860440f02882010311403101c192104502e8003004044010082d05c802e4100d5150181c02054028002ea00640c0e00d41c0000880c88000c01e2120310803600640980f08080c241642243e4010009040d10b52203c030048040a8084005010040c808540d40310302341c0d61001e20b010000c0e02d690041521090007000410050200c0c446262540e184100b0304040783c41e01e81c42c00c0345602034010310b02c0c0100d00358a030506c4c00c001e00c01c4484007003845a000e101d807a0503d03600c0384284102c1160780300c4081d00090f010810580070700030b9035000a80c00340000c0c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 87054110 1250 87052860 87052873
    0x3050309010f050405060a050907060c060b0a03062a0f0e1212040602070305070b030c0d05060f12060103061119230a020607030510050a03061104091506120b0a03020f0102 75
    0x310402c110f90080d1400d0720b15a220804002d40307464944078035234100140b00000e29580e4070b411001414241480c00082046803034881401c6e05440b00320700b00001c3c41d44407800740f00e03003a02d0703100b0b0904101142c5070045410b8000034000004602071240710182c59602d581e5011007208050a00c803d219903020009020301c52441041150541580640054000395018010061541c10401e14040c00754010303c0c00c0d51030410602400345026011503d103401d4406003c078403596a440001d228070b20f1a4800d6802904400c1c1c213000c00800482c1b0103059034454001001030050340020101c00340150603444d141e04801070000b034a00b600407105441d5a40b400e000024145a0080d10b840f1660011404c01c0c000d40e200000b4840d403a43c050042c070380e1001000340f0000c0000d00d0440081c8070062648005040142d484800d1505230400504640107425509014025606c2117002001d031003140c1c0c0301e0709000a08e080d00100312142540611240300e80c004140350341650542d000c0005d14084940140d05611900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 87055360 1250 87054110 87054131
    0x20108040c03020d1b05010f0e012001050901320c070602070f0602030103050c1212090a09060b03011508040203060402091e0114030d0305010b031302030708010e0102030a0f09030c0305030901 84
    0x84100000c003e1191780e403410010002c9100388401c2000340c001d5418050b00f40320308400e0581c014418618071509107012040c102140e24490f01d404988000400c0a50a00003081600c0e403054108003018004281904070400011000ea001c940c413500701803240c10b44440204440c1040100604071250250710018907000d031039522a81c980c0c0510300f0403a4072603004001041840350911800c24054016203640310380c103407903038074403500c03181c44ca060400840e101003074500d41c5032135152440014101120b810800d075510341441c8401034000340b10725407400b1640070510000ca4810000103001c0e41c0d014000b0410b0740c0310340c0d00b04220040010a4800782e400c0d5001111034124007604428000c01b07603c0c060040030f0390484141800e00815071800340038107040c90010048079055800710307903020740884070b901c01d64686803000900301002588040c1c075942c2400e0301e141250006500440c003c420803c020800f05803441d0040c0306942c5a0203010300413070100440701001c240110010355020440400020b030383c41c003c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 87056610 1250 87055360 87055369
    0x90213021602040f0b0f01180f030f060e1207060203070c08030a06050102072112050c030f0910030e10090201030612080904050705071e0f080a020604020f0406060507020108040c0302 80
    0x40358004003042424440c81d06606252051303e265684100c810b21500200d040407804030b240c01501d00e030401203101404107050800e01c22100141042d1210540340c00d0b0703641040f01c2c0b800d1161b80165401450f04441020b000b4001613039400804920070702c2c909010842d21240c009400c0101501c051011050031000003c000c0d80096100760700000c0c0001f00c580c00d1200091400b110380e0014001c429420b25550001600001442c41c0564061054041c106600300c0494180c01209c0d10210288008036503101c2010b1510060403101ca81585c0307403078a14070481000c03010b5506200c05819203070068100100112515041020424010704010030281d5960042c00040c041004040c1c2d0480c801041e41a80ca2406000b42608150149407050507e209500c0e0071014202440642c0c4803440301c0700c03420040164030a4401070340c1307400c4002e0710384a540c40c0d10043c4d00d40801319400c80c41003010309901d00c9285018402c1c80242c4a0540e281800c20301d10340d00540345400090300c142d4400710300540010060b42c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 87057860 1250 87056610 87056617
    0xf02040e0a020c010608070501090b090a051f022404060510051207060e0402030402030d11010f02120708060102010501081209011b05070609140d120509150a1205060303070609021302 80
    0xc05840060391001c503c00310508450302c2c1e03000541140c0054008000b20383c2d028520700161891000020359580b03100c3c00003508040a98422504041801c60024900c1948802011017210a809823200510021041c03c640300680800c0416401c0c81d0000c5004101300b5400b8940c4079009444840c030241d115800101d07802c2c03041e0340091240e80301070760502419030701c80c0e032044420009840960960071305500094613042d042035102c0030000c50000490400c1c00c2508031030a0444030300c03002c550303480941c1103400f450081154100c0118603d07002044407944140305a82c100c883d5100505410800c1e5400400f640d4098500c40d810441c101e4021100000310596108100b442440203080013442d068014003402c0c01d6034080c1c0070100040c0815001902c032414903410381c070303400194400c0d18414120203448501600351030581081d081c1c0320a60b000d0035020010000700490340c860300c466891641500d1b061300d00480340e06425070810b11406001484540184e010340d4801030110030b00c1d10b06005032804981 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 87059110 1250 87057860 87057871
    0x1101090f060203100806130602030424090303050108031903050c040305010e06310b0c0d02030f01180c0e060306030a0816020a170309120f01090b06040b010306030b07030f02040e 78
    0x5900006000c4c103034601c1456103000b4031458001d45a1464103480b800403114000802601c0e142d00040000c2c2009180c41c43c00d141d102980201d2204a000d0024020060484040480c0420325100010407a89000819200750041015000c400503001035012006070a0250280e05219000d11010000450a0007803001410980c0000c10b207a2074514001c40c2c02444041100c030032481c2c1c0c0c0440c0e0301c220521110740b840d19908445e2448058490b40060030542c0f00d1040030b5680700d88041b050ac01c0110340142403904072990703014807000343c81e90314941d0030448401d03030b09140225080f008040310900b030910107950320100c000d05840311880651944130040d03003c01e89054044241212190031450420100005005c681001001603240e802c4103030307039921450009030b00c81d18400c0300c4662100010040e101d825440d9074002d01c8980c00600d032102c41c00000b0f8445500c202e050070901d0909511074414003003181e81003542c01c0c0c003c2d142c00f0015030061142880a070502c035001c00c408603009103008003460150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 87060360 1250 87059110 87059123
    0x30d0c05030411010e10081506070303020703170921161406010801290307030507060c020a08060c0301050904030201060e040f020112060b0a200604111203030f071101090f 75
    0x340b80600d490364510b500c1118040c180320f00c0c1500701070306403660a02100c2240443c14502c481d5160b1f040b101600840c030b07901c00303a400403001807450308050b4542c0140403018480d803a1050f120087c0c10b0101e41c4502c1c1260701048540c8450103040000b0004200d203105000c1c4041024030b045847c4400c14194a40b00c5070580c0c602a200300030015a6404002540c0101014002040024030300304001704280003840c07002f0480301c0c6c1c00c085542c2d11395082c00b5840085038000c04490040c0da03144409031441c410410300380d200f40d001c00310000d0031141c003040c02c40c40b8100c2d80d00c04504e10307030800c000c0100103172025009404666881c2e0f408102e03a1100ea81880c0214040c0303162400d04035035440014000801112421a41130400e80100024043c070300c01e5500e0350465003080030650701c0101685845500d40041c101c04c904c01d100a100a22039850300c0581f80020649040c010743c00c181620300e95920090780c502840c40d030f01400041282d0301c11300c0384a2001019400100e600301154030b407085052420501520b20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 87061610 1250 87060360 87060367
    0x7030206090616080d05042a14120a03080a1a090106081306050103030804120c02010e060f0f0409020a0207060512010902070f0206121f0305060f090c1207050a0b16060e030d0c05 78
    0x3401031940300744a907042d8200d0023140c1000c10000c4050031020500c02c80142c4220001601010b40d125180d400355041c4540440d12aa0181c0c1030040503500c00303840d0611600d29281c104600c501c0c011030208000031015060034826440e00004a45400004020f4000c40000340c280100262042c01694001c60183d540c400e11401d1506148040140d0344040c2000e00082100c0c038001030b40c100100a680d460f04070ba066454010310800032034907115480800b00c05100c00203003c00d10f0a015400f414120001d9801c945025484210540d107620400201e80400b0355010010011450f0a80091046900c6000803000c64103040d40400c403160008030100381140c500340b04200c0c01d135025070300003112800e4185414400c6841c54a4103074030341c03101421000b0321003031980002e4442402000b80190152014220108481030010b10342d40703482d440d0280c81e1051281800020303026850000350b60020441c84040e90a64409903902c000030464625030103040c1c04180724858100c206881562908804c07901d8280ea0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 87062860 1250 87061610 87061613
    0x1a0c1b06060906011b02010e040e0d020609100c081602030403020a03110f0604060e1509090c0403060f02090f060c150a090615060503270601150806010207030206090616080d0504 78
    0x20080043c003140c10043e540c41010903000c80501d00100340b40c3c080c01d010f180715070180042400f425058100342c9840c03040c044460a000e5001828a1140e1501000d50b280e0020790030410b81501c0d047ca40d0040003c013100049410310203018880c0510404c540112450542d07650301007000c01001c3d0b4410758901c0344d00c0c000c100080c241040031003074010048803028a45414400c014090715040b50f1903500550030141180c042ca587e4004403203035090000c246007420304c0e00940c000e10b660310030301044a04904110030400508914005c0da811844020300ca04082c0a0013000e10513035402c40022101c280c400c00c09600403080c01e01c524503004150184d004100c1150600b050003e80d51902044400258803000802c241036011040d80d4100e440d0081d54801d18440359a841c40040000404500500031900009024060640c418100d0015901d64400c955500001a0380700e80e06403101a400080800046a8a2070418005c1ca81407020300d80d03411030f5502c10344401040c1c0d0060b14000e15017650310720a020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 87064110 1250 87062860 87062869
    0x905091e07031e09030e04110309120a0f110a061a0307060221031003060f09030f0219080309010216110a0b03130b060103021204060f0501121a0c1b0606 67
    0x140d0016039828144070702c401030042c403105140543c1450184035070304d0065030f0400d4800d07259144503e50080c014003003e50b00341d1001c0b8180c0d005640d00b08292090080c04464007441c00207403100b200032521014141d615140c000c2c2d504606010684540c2e000381a9800b00041c050320030341c09504c400d1031420000703000a400341813408030290091b00039544082100c000314551001000c60025034085407075201e0b262812400d1840800340c100030150740c1040340481c10160258000c80010740070380d403207960301c2558000c1661070b81c00040030840254907103800c0ea00418500c0e03000316000000000010302d000320044040030307001450301e030443e110000c4220900807440d0848040000e009201540c600d03505000d120321885010720340c0010249540c50300000c14583c02541610b101c54a440d0728480581381c1403802000400d12442e0b4090040d181000214100280b040000c02040e480f05101c4080c000408030444441c000503c1076a40322010403c0760141500d484c102114541200300502140c00e1000400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 87065360 1250 87064110 87064171
    0x601030309050a0803090f1906020a06060506091e030c12031b03040501020616020a020a06051c02030c12060a03050d02030403031b0201120207150e032503050910090509 74
    0x49206524100d41400100000b2044803100da80441f001e1480111000c080b61b000f062080b42104d4071000340700b00240c00e5802003480ca51803446000e01300701090b160800c111581c01202505904500f540600c000340f004054440308080c50000c04440881048100268010700e0629000609402c00b2a00071b00c14480c96002649100d440c0340610b061a08080c0001d5469400514140c65072100c0740c22103454074000c0c080d015100750041c01c03101d07042d03848901c05009079001e02d1520042140d00f4055440d800c200f442a04e019015041041d440c090700d41c1c0311000c4030740d00138110a9000d8011240040050750820941c0c2c0030f0986900615100c84c0745040140c0111140c06008060268070b1000500507a0700c280c5504d07034102d807800d0040c0c541d180c42c02c0101d0010f003050031179004149001028940c0b400b001000d825050009042509407200e0300c440701c00140524100103010600078000c41c45a4601080c02d9007048a0300d14044900c16915000100c5600e4161008482c000703000765080f02d00c400c0103400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 87066610 1250 87065360 87065369
    0x5060a1214162106090203070e1206060f0609030a14100501030201120c03020d09061a0103060308070f050f01050a02040608070507020a030303020d18060501290403150f0203090601030309 82
    0x2880c0305151962031800b0942c2ca80b8010307000c10058003020003180181e11542812155940010000940c941003240c000754000d5420f00d001c03501c181c0400150b0310b00306880c040619416800303000030392144824400c0314000840b9096000c4014000910240c0f810070815150034001c41d094a0380c0c0081c0c0802a0800d040382c046000384904040050016036040520b030f1144840c02c1c400051b40300d842c21002c60086c040d00d00380350b040d24280a490410b01400f86c104510300580150040d00180d5490010350844009100040c407182c2d0034440f803004601c00881001c200b501070015258080315820259003124821a580112540d02080910000b0b9000e00041e601004a00384140f8180c001d800042e150359491200400b0076030001401c9500054540140c0114072030402281407020080c6031200c0644400d016901c0e80c60f084050134040d074007800c41e880803402c18900301c00345400d00b50340b5a1042c0081c801d180e5481030707880705c0c1e4215084007a031000b1441881c2000240c1700c294190b140003007542110703501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 87067860 1250 87066610 87066641
    0x90c040305030f09010905041a04050703061404020901030212010e040c060c020102100902220603060c030b1c0302120408010f05010501080c2208060103120822030309060605060a12 79
    0x82030000410000450b0300b404032101500d6121800a00100d071480255007140d44c001d4141608105401040c1c03844941241d001c0b078040c4425920750034114101c03119071040c10555001e046454046081590050165400616003d8500920a10804011202a48650309861074442044248205104c2c008050210343c507011800007480c0e00000c0d075034100c5581c000d443c1980d80a440c1e0865035401100510082e0b0072454019440d440052034000305810302c016505035080080e07031214140701b0302c19001d000c00b0040040c6000d2000a502040d1081c00b844103d040d0710501080a503404001c4000c1c20003042d00000116030b040c10b5080e490103890040e40018140003441e001c3c801d038520200c00391807207055000040903004101c41c89a0b1007c0a030f17a842803201d405440000700c140700c142e0803114910300301520307079000c19112820610891045810800c0c07007403841d8165a00020311075048004402c3c011030001c1249030316030000a9040e400b541ea81c0002c1001d01540c032101c0e490500991403510700d1000b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 87069110 1250 87067860 87067867
    0x10f080706090b070233090f0306100b0c010204081b100e091b070807060c0908030405010207061d030106090c031409060a02030408070c0312091e060f0c0b0411090c 72
    0xc0c00f1240c54000d2070741c002d109003624582d50504c1c90546a00c440000a04c0d07134100c01010024902501d5580084809030044414a02d1030f110350500240f80303401564170842e100c18035840e00540f99400c0c1c00c1f000780c80321155000c100000d00940108102c1254503102d801d20080d4100140820546071200c04004052100c002d104407016510000074562000a059140d40c4071305812402028602c60585d000b040f201c000700309c0900b4004c0303a90100c0125811070b2a00c0c0561510b07480030564034000c42c451580142d205881c203015036441070311013040030700103860540c400408060000b425241d154001c0441d5550307404460704250b5050043c1904014541d01001039800e180080d2a00c40c0001003031307007206503000404181002100300440c6c00142d0081d400c8001d031900c03451700d03d44490818840e0400201040380c003040341310940300e111441441111080306c060340b4060b020f64a55143d147c8010071303c122200c8030310200358088000351040380700740f0002c5130340f8942d001080641c2c0c601400b058130f91503061 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 87070360 1250 87069110 87069119
    0x603051f05010e0102010902041802100504080a0204020901030617010c0318020d110117010801060f0e0f0703110415030501090c021504030513030f1101030b060307020a0b060d0b010f08070609 84
    0x20825009a81d8280b0301002048807200060b800742c601104001d400610301507142a29440c0301c44000e0086100b00d40b01c40e00003140280c00c988a018500075103846402c440d0326000180742950080c00c4400041c10b001c0380059460704c00074180e1403011203808840c0d45444420310a140d061080807400d841c1070f050391a5070300c400c0d000305001031017804005201c4043d0141000c01607004011481401b542c28000141d1580c41b004098081c10461098580441000c4000b0a80303030111030080c0c0c4114810603185505581c1c0c40400c83c0900030012104660031403c01003c0780c030074010b81048a0810749520041595450840254112030f80d800c551800c6401283d40601031100f1255010b400039014900700d40c580f036502d128501c0d0b41000ea03000a000001001c160380c104910034080d41e07843e20003600c0421032a12005c0034000d1a2204490450040c2c04c0104250700140c4030306c0c0c2c5640c2042026140c61620304042d900d03402c1c101c41c20380000801c1c0c040c401013044403100c04c01c06030700540301525203d04140d150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 87071610 1250 87070360 87070411
    0xd060c1e0509130605040603080a020c0301060311042c030702090c03091f0e010204230906060a0c03050c0a050601050909010908030105150c010c0e0406090605060a0c02180709060305 80
    0x1141c246a01c030340e0a90f20681d102e1503994002202405000b402000429039030300e080440e40c4c0c0710505032405402500303c64043c0e0316042c0b02d51411a0340203941c43c08590f4640b03003044010316840000788066400240f0450030220944146074518600d80000c2d035483d08540100200f14000400b01040075104008200d1008400b007902c510240e20300b9118001e40002e07080f10005440350315005141588082000502c101c0656056903010100e4040361003100400400d000306000104c40c041c1e04a1b00c01c02c42c0c0c2c1c000500c2140f80084660082c905181410300d103032146400d01807035540aa5040e40b00c0c100500507454000101500009010000c008030810395540040c0341c0014465548103110b08201c0f01030803d015002c80c2d4880103070200270448017104070009032400c440c03003911501951800c42c01156540b00303845008113454000340090708220200f50120b0b1600150306c02240c021002e401140540001c907038489008020303a0710340320100d506014004046500040c1202085015206003041c500071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 87072860 1250 87071610 87071617
    0x815160804020312030c04031110021b061b010501030506061c060c11030703080906060103021e070c05060c03090102010c0c02090601121e02090a050a03030801090504020f0d060c1e05 80
    0x50900c91000d03515800080d0130810084040034100300c0000410010b8041840103000380d0340329900c41c1ca50074038186d041c0181c1c02051720205000d40c0c8102c2c00c010001030a203004044818000301014609484040107480030104900b084003507079196401131003008002d120302c6070722250a41d0500c10806401d030f5140c0c08103e1559010b031085584407081c02d10700d841030190180f2403401404417640e030700072440c006000080494120342c4c0c502800300402d81c207611a0007150014034604031060740499100813003035900e0788076a83c00c03190040303042800146900c90340054216050000003450f00c940c2e4071070004e8290350f10301140004200d4908042c00059841d03e00d1941c0103e02840e200184080c80d02140c8002c0c540004180703d1a070b104900e43ca078060554000b0060a0401d85210619650301d40c18070001c5800341c00001d02140031640140020394150744001d40c403d0004240d428240c034200003107450300c1d0030b2074070039503449450b0f0030248121500001c00ea0070003010542c4240080c1c200c013000902602 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 87074110 1250 87072860 87072901
    0x1050c0f03060307050907120e030c070e150a0b0d0606080103020607150b1207050a050603010f0608090a020904030c0201081609050112060f08030705070e0f040f03050c0a0308010815 80
    0x2034011011403059101004020040c1c94007420b6808541008103018002a0b0800c4403603007482e0906c10f410351051404415110074640440040c0711041c244507600a40c1d4200511041003141a58107074000ca907100b1408000414168440780d035a14981d03d020b10036034903135401100a00520368010401615800304590b41c00b03410243e40010540c5131050100984180781400354450084020f1160201000c0b52510423100d048031510015a650420b010507800248580c55018074010001c00c01180203010040d03205071132000742e0320514065400600a0700d03003502e090700003072105c943c013004658200042d5070300150800c0d04000d040091060041c949455805194108941d025000340c00450070340040024111400342d2400c0c2d10b44ae008515940e400130201501d151080f410700250200c880b0042900030f800d0ba12a03c8040e80d0781d03484801c0c90003da5042101040303000c0100d18134040c014041500004d10a59a4054551502944d41d241c10500d00165030381c09840c00901581c441c08200010b02d0f503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 87075360 1250 87074110 87074137
    0xa05091c021f1820040e0705151605060105040c051602060d0603020303030f040201031104080d21051602010b1206040f0206070b15040510031a0907150201061701050c 73
    0x10386414000c034050003100c1e0304800c49140c00756100c8108004c0c6003400400302204130f59852542540c80030841542d000f19590016504281070511407400c2100410010301c6c40f401c201071400903001c440e0410005800c50503a0143c010800602c40740c5402d0190840c0ca21440c0703040c40c1401501031003415031b487d110800a204480010300d1140d035801c103401070741c004c50f001400e6a40f6490942030037400e00d10119003c80c000b070324082c445091440403105032801c3c3d40c3ca0400034881002c480764290340f030644282180f249400d4040400c02c0c09845805560321880904855540040c1c100d00041d0a51704000d082d40e106800c124001c810b003003c00100154013982000d01c1080e00410b40c00468200d2052103400307082c4046050411070a80142100182490340940b0104000d80d41c4181540b0841c01600005166000c0100101640d01444419a07000750300c00003a100c60780d940e1621003100c41c2c11402c0c4803015075102c4030100401c02056009003d42d07809c1c00300034852371418030282c1d00940300300405003018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 87076610 1250 87075360 87075403
    0x304080a031d10020c0115181a09070c030807020f030d0506040f06060207170601030b0a0510050a14090c09010f120209030d03021b0c1f0e06030a05091c02 68
    0x1001c0000d411002296a44010307145688181c0045902075030080380c4402080d1708001c1c107800e50987e90450701d01103d2101c4004450050340b00c5442000d4602c104003018000103940d041103041d0f40703207249140244070b00d4039644201203540c0b40c09841b00200034105010342d04200c6c80728840300740c080b040740c1c45100384c1c000025640e03842c0340000e4003d00040030482c944034541000030661075000142142038900a440310003c90f50010700140e545e0500f40070042120381d03103201040c40003c146d002907801070121440352500c41c1d2180003103000c00c11035902101e44091003281400352400d001d40344513080301d0030348000740c0752080c0d4000191107400780403c00020005002c0301c0346010903141c0e054030260304008003130b0391f440860000300401035040591030f441d0b062400180c039800c4241c00280c280302980c5c040c010600540c2c1c4291608a41d0400342020424042c0d008418030099541c88015480390f40611800210380c10074a691314a0301d00000e10f0500c0c011304c803c1150b03c0240d0006280050300c914003c1e0f2022 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 87077860 1250 87076610 87076631
    0xa0e0307030b01080313210f0201030b0d061e020903060c0a0909020a0c02040612030e0105130f1706010609080705041e022b090c09050603010207080a080105010f050304080a03 77
    0x1400200754000340c1424040340004c111008044001d15420b03a41b407201340b207420749589201c2c507081c244410502c946142c070080b800000e2820200d00c50034500505000856041d15408189861842d00003256a15903601d90940c43c000f410bc0c40006101c01d0700310450038408005c02081d91900702070402c6040c0c240100d80703501d0052044900c18041d010f65007040d515401c110340c005e4203c2642c480c0491180b818180702140080c150a4802c091035003559841e00720180e0700380103490540c01000301580b94000040081610000288800c0040010f445170701501499008028103009043c1c0100003000580c480c01c0064080008540e01900c904540014200701750040c007000d0840340b0421200850300108070390700c51900181000809040000b003004c02003504c21800000c031342d6002801041d041d1401000e2151070384640c440c5038400d5005d00018a1310300d440d25406042e801001d900c0000034102d00050150f9644a03402d40750452050401a00b5414590740f2001140180b00c00c480070559502c2d070141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 87079110 1250 87077860 87077863
    0x9010b0705071712121605030f0a09060b031609180210050d0b1c03020f010b03120d060f030b04110619050d140118051003080405010f02030f030a0501050906030606060a0e03 76
    0x3811507651020b895845600303c45e000314865040702c0c2092610031031010402e005004000301d03481020108210f590a503146412940100744c0d01c6005c2d14400d5a41a000f01551410420701c503041a1069054145c60b28000c3d9036000d50b000303801e00c1004d100403404144010b8072602000d0400d01c0e4142801904d8010340c0d0b0341c00e002015075040302a8804541840c001120f40c100c02d04203140d83c025800e2396042101c14207011b0903592248074441d059072218440500da506207201800c14480c00701c5c00411203568444a280410340c1640060302c604945100f44010001c29200107a00108180c51860601740065600c009404c010300e02e4005004001524802e911041d610503403510301e246405d80080c0d45c455508004030304010020f039107014689404512600c4021201108581e40075800a240c50b04280044501182402c132490035032000b03200194821031a10061445283d40703080c001601d6240c481040251617014121500079041039060150946594048601d1004075080001d07a00c8208008a03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 87080360 1250 87079110 87079123
    0x1091203030e0706090501030c030e06150d060f0c1101091707020d06060305060a0b010201060509010611070e1f05010806130e0a0605090105060a060f0503010e13060c090509010b07050717 82
    0x4840303c0c055800b0101d9490341001500d81035800a0340c08100c000b00c000e0056089030025100989182d1150340010540d00501ea410014030b04046c10048a1614594824050b039031090045c0d040251208503100c0b05a078024100240046600000d114010729031300c1e03480390300c8000000403029603400140d5000359190242002c01d087d0748010100142681c90900c41d443d05015200300742841d0810140c600c0543c030500550080e00c1d00103000040a92070300d007095540c0014142010b41500420600094003502c1090071803084100e9012050794481d4000c1030340010042c0d0b0481414460200284121070319800745074078013078000b5640080c00e002d10040e860701d07251004000415060400c000c000030210103411680c01180161058425203840320000d03540d440062a0364000141c2c184010401e0801c0c046145411140c031800c00d1402c003001340c8522007611100810b02010411300d40d41001a800c110f0803041c010320040c084141084955502c05866000030b11400307201200e141604409624180404c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 87081610 1250 87080360 87080381
    0x15080c0c03070f0201030f1505090403030b09040302030901030606031b11160617010801020c06040809190312091e060c0503090d0b070207060503040b0a1a0402030109021e090109120303 81
    0xc0342c0d00c4503101c1c50201019191050100d0005e401c02c4503410449807140580c12001003104d0305469894244001c0c0010220b0081c000e40826844030100c00854580c4000d4501482c002d90140d40d54482c203000140170f9903042c2e8802820117190010791460071a000c1c411001d0400ca40c60f00c5090798841c2c147c03c51a003211b0820f000359008000f03034006945900105181e4074107081d01c21060070b50380e80d03213101c42c203e0103144503181d402e400000000b0b000407082c80042c24001d50040c8143e400c07000414826082521541044548014840281da011a0003d0440e0000e00300051110091034074104038688041030f6109143c2070006c104440d808004e401e0040d5a406c6401505a0958642504018400c10029100b4070058040c02d400030640c00e2003036085a11131508064170782c41c1c0362120211080142511814442417424282200483d5601d0740021030003406200310240c0c40d042861406080b4651528510507814410002c50100c2c0e604200391604980156801c108035190700d090a901404d8100c41 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 87082860 1250 87081610 87081613
    0x206031003051b1801050a0b0304061b0e040506030601030809060f04150c12080f060d1406040c230d03050307020a050106030507180e06011422050711030415080c0c 72
    0x1114111443e100b628a81c030f240044581c1d890115080490941c0b5101c280201500711245c0b5105200c0c1c0407501d002540c11601c2404c001903180d20b50454503c0840030414071000181804052400c0742c60036006003900004100c0281000794510713a26600248074505400d0302a501c0880c2e010380782900ca00594005044000c44413400c0028000010045019414222441e9203450540840b0510480140e8030455240c01102155214070301003004519038110100ca00f07008000900d0390500007446110b00492050f08501456410408814100084036000d2100141e9034558086541e940c00181703241c250709030403e10f54a4486940881c20305814940103007081d13092010000400c84001900700c100c40b08510200b0300207240e013503144141c0e00030f0035074402580d1082c001808100d01c03124503064100300007005401c407074190202c0740c4c1c2c4ea0b40380340f0980c101c095540c2081045040d000304c0c462080c002ca440103140b51074184580c694a54112001503010465100001030ba030940010855824082050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 87084110 1250 87082860 87082873
    0x601141c0c031a010b030402130608011802030607030c02030906031f03030f0806010c02102a05060402090c0c03040324050c280e090c12040c1e03030903020603100305 73
    0x240003080c48242e02c01194500200500f81d9400408604070324141d0b41015240b17851511aa000c1080000d4031112246040c5c0c4d43c0c600016940c28240b04082d035240798a884907990001500416013030050040400091504180c410381c1040d40c00f0003180c07c2c48500310740d610f03201d4490000d50941d041c000c000c11031554001401c08014990085202c5800c03040716643c1c200765948d80801140c1c0c9002a4000a4205210310403090406028130f60494102071050b05002c810601d440422104560703446003540d0a800140601c07040d820710f25034681d44100c0d1000341500d0a0b0300d01c181c20ba940d11561001a003040c50100c0c10305040e450782e0180c0c61008115400c1808281000b591404460b031100b95015603c845108000e040d90380d41c6856130310005060380b10200000f010304103103c1c641030000c01d85e02002600700850000d00d00c3c5042c445014600400c03003146d8880c01d000c0c0a1079910501c921203000c140f00c0c1003041001a5000c042032040e217a0686400791251505443c1c004025140c0e00010210b000d8035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 87085360 1250 87084110 87084113
    0x233306070c0506120f1e06040c02010e1606020c0901050f060307050c01020a090e06100807030209120a03090312080412110309040f0e1207050309010507030504090903020a140d020601141c 82
    0x2004642d0250091641c0303408192102c1c6c0c1c02c0d600f00d8090030945044000344c000040c0b25450a94000480d066031030001061040910895501f0300c2411042e0400b10b0515043c240045030b410814034424050542d409011541018001003042761025401403143c8030000004141a1003282942d280a901400075920344500e040c0c0600801e0300b07401007084810881000481c645001002581c0c000c03d640c84004180e1039014088002c0e43c02019100c2d0481c10800101c23100da0420010100703198081d03561000b80a0546c5400007908020b6510f0504012030f150502c808a10060b4a0002840d071a040607403c035910148011b0450007080c442d558070a02e8041802c403880a0303500010300003555201a1241800000d035034280303a0103041c0003d0500d5100348441400b035405074004040030380c06400c040342880c0c3d858101034181c7d04490b1040340186c20800d0a2801c00021986080306641d0f50009040281410b8030000d5481da8140318181c40f50b503243d542ca8846449400d13590032401c2c60030004c2903140c04603 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 87086610 1250 87085360 87085387
    0x9020d0204050f0f0d08090a030c080d080106020f1507120504150c0f12050c090904050d02010b0a060203161403120f1003030f0e0301233306070c0506 66
    0xd0712907070780200e01a29215040349000c4d0030381d10326444000c040c0e80d0075402544880d0780c150040c0800e26000101a00c02201041c00c0085a40003060f160005003100c10440900410040060b4460000d41d8001002c02e40b90090121740790201d1410440300c000c003070b6140f1004442c2d001c030f00154420410f00d010288401d022155504504450041c103080c8804500b8520413564442038021600009003000200d22042009402950b00202155180d90908521900260043c8825101185c15510040c40910225028062082c900307008903003282040f0b1a0881c060348a1003a0154041030203a500070000c1002084281c034280d4110001c02c9a40b161a0301d5806e1b04a40030685140c1503c640c8000061b24130344440043d80182ca034150360340d290040c6424000e48102203115540c1e035240d500c5400105503003202504142c0b044505400710101801c0c408402607050400e802843c2e040e41e21074001d03d00f0704a00500070151100d0964843d40e0780c07406414111691034060300070b82d40c03000d40095070150020700e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 87087860 1250 87086610 87086617
    0x2010e0a17120a09110121110c011803020c091314100f0209030c0d050a020108090f0604030e0117090c010c05010b12010b090901090308010b2d0406020d0908070b09010909020d02 78
    0x800d40400024070145001075840101910030310302d1f032000c6405c03200c03128441608960f481407000c5149505100a40311111b003515889a079440300741e00048000c0e024103030b042107141e00000341030711a4021070801070151811030300704070005881022062501404048100400c05031010b041e07804029506005000c1c2c1c0203980440280346c824466039480140e40d24009a2050300c071030b4000020701140340d8990041d104044010207072600c1d805503030030814250900b4031009102e10702c01c1d940ea09008031404005003950307058401407015008402c3c20040c1d04ca000084580c010227090134000e4000305540741c4540500060002980c000d885440790980c00b0105400c100e055440481d241d503100d650314101c243c200da00407a40035001801b100700400c5030055000061141041d201d5030398550b5500500c1646054405616004520f180014208040e560602101d0b441000b40c0c83c024109a00d80103829030343d1078260041184500d0009182c6031030b0780c02200880000c0006d06070554940300000c402100a40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 87089110 1250 87087860 87087863
    0xc0a052a0109080a0620040f09050702010b010c030806030a0203030d060f06050f040306050403090509091e031204121808010902030106090c0f0c0c0b040e0a0c02010e0a17120a09 78
    0x2400c5550100190300805526050721020b00084c20111410740303400c0c010304481c1202080100852030000400280c1100910103841010380141006103030898040031528000c040104592500302080719585c0d000510703010541c2c0610f81510a5200c49001038107040d86031b00700944c944400110100080400d4200381c0840702141c01e82070543e41e568000380c82c1441080c50307000b005003040005100082081d4040354000d8042d00d0300c0480c141d101c0700070a40442c81a02d13840495440791600d41d42c0401030505d0862034104000182d410030012000400c101030020380000c00480c0d0600801a4462184400d298610354900782c40f44103540e1245480d009051003001640a54244280400e07100d60b28014401c00c0d0750103a84801c01100086e034100d41001807604110b071400a524000109004050007500c0039202403030b2069080d0800007860030841c0c031010000800e59042c0526a21124800714515944c9034110000003520748200c0c1518105104070711014804111000a100c0107480d05c1c1d11044d10b05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 87090360 1250 87089110 87089173
    0x1002240603070501090609030b0c0d02040b030405101112130605041412030103080406050309011103012c0709180b04060e0601030e010605030601120c05030d0e0a06050a02030703050c0a05 82
    0x40d03880c0c43c01115840098050780700815800350f81080040c250700c1c10340b5444041c26243e117003420740c52031254041e0ba100394040752001c08080140300512205003d03103400c850390040708202520b0500d8549606002e0040b08541e1b0710300b054001042c01d651508225817207540008208150328040c40e1054500101640a6480348035100340409080103040849050703a82102e1040d0900d80380c01006c41d003560000300b2115465480d140078207000032404c4e0207140a410026854441464000c5a902110940850086a1079010300a200310203400c500800c080d070781400c8500444200300070129019040c0002d000740c0051900600281121903540d0803070080500341d070140301300c44260540600b40c44240c0200b65060b003080300104000745031084045d440e24440c0b5070702c0d142d40c0d540c4d2001a0411800180002c04200080d6060842e450301003010b401a026908020742840c40e0004000e507203000302d45004003030002c0001d20741902d040401504c041180c0c040b007100d0b503202c49403054000400343c10002030001e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 87091610 1250 87090360 87090373
    0x1101020706050c070302060903070201090e04050c040c05032d04030c02120303041a0a09030e0906011215030c05090115050310030f03020a03030b0d05151f080d120b09061002240603 79
    0x8e04008011195000d405035a00e03007000e400d003c00070b501140c2c00703041242d0390320441c811211552900d000700c1076a9185510b0340c0703840c4c2c90003170b071403282842266252481d9400c42104d41c0381160740c04e0071030a422a41603c0c15480102003440841c140d40200610a80544000700400042000a4181c0c1080504403108a41c40381c50300740ca00c60940c0e513031500007004100c0c0200585402d0409281d0a5031150781403421140017600045028225001588269115000c0d50f01c107100340003400307078100300900064910308030540c034050824100d10b2091504908022000011981c00d0154410300d07000f86402824221044545140180d500d0704120022800b090070311440409501d008107502103080c3e00800a045402a0f017007050740c01c504010140411820000c4940c1c026050700840003004d04121001002c0001840d00094002d00008041d181c015080c42213004550f16010a280d41017007081e1040c03540c004006501b0303418a0016004943c00b100080702000240b1300c4c0c40c603503500031402035064968 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 87092860 1250 87091610 87091621
    0x30403050f1006061d010e0112020423010c0503030a0908130e040309091503060e0102210103030327030516060510030218060d0f0c0b070609110d030207061101020706050c07030206 79
    0x1d40d1420504210104d0305ea845103501254012003a00c0300ca00d50516001c5440c400ca600e4540c12604650820b00c2c84407200074a107a80f901c0c181080b00034200c4242041c0e2003600090392007540e01e00c00280013902554407800d03e0010001c041d82614960100740e4101140e860b00c42220400d480e41c102c40950004030060800110702007903108000c100740003520060921804c44d11a00301a0a8030300d00b808140d0760030410791745203102c40400200317056801d80102c48994550700300102a20701101d81c54902490392031040a070600320701040d4a1103035150501356241c000c481c00900748804071980c007a00050400041200c8030110076820380035248219502c0482d0b4419603000038044100311107154011103103112200104045c94540c1580b0392242407800b40482c2c80703d078003500a070401d138001c4910584850a2800b007100d04a44070003900704c140e0b0100b4403801c0540300203540e0f9030b0724444c1200340007040540c4440c072402074048039186900080c1c24171141c2020007160103182c0c0203140540050180901085 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 87094110 1250 87092860 87092867
    0x4060c0f0c180b12070b090607052b0206090d0e18010602070f0b0f03010b03041b06031d060f070f021e031914030a0506010c0519170405010801090509030403050f100606 74
    0xda0900200402d003031806d004510706a03a001000503a84400305001d59800104200800d00401000c1000d190440316100c07107100c0b41d6000e0599034801c0d50084400c01011820004902402402c13030314000c01c907805103902180340052014031400c040a1014008190b0b9500000c005086a0001021800c0030759070700d800008601480035442d0031080100010800078011001841c1c01c90302403404400c03c0d40c0d071390b10441c003c1c080d1a80104041b82d02c40300c003007680130300604404034402c5c40c01000c1d0040741341405064070f0f048070060401081c06880030121890620070485210100d140e1403441e030489050780c00300c41d503d4029046e441100340c68450b456031654440c54850302c006202222541c00c1d07444d000f054001911b402030900741000581c02e84c00011800400480e01408500c0e42c0200e4004100e0814201c030260541d4010003480b0100810441c0d40d9100d601c0307030304490307000000007180d4a03600c000d1030461003a607101815a02c900511403200d650080707075410f08000041404c00c60b00703030340e01c5095 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 87095360 1250 87094110 87094129
    0x606030f210c0304061701171504051e030306100e0306070f0302070209010914090102090d02010309061b09151d010804110a09020901031d0304060c0f0c180b 69
    0x2510398002501001840441003007011401420390441410501484212440c54006600c40c400090541c03c40c560071916004000d800744c810f4510f050b5a00700d2442010b6611180c010221003001c1080c0e000400348042804103405016520348000151400e040c1d8032581ca8005864030b62064240d030440c1040203006003074151030550041c002e8002c995480a060750b58500f10a60003060640070030400005a95030010180a000c0c0300e03038000703000040c07412140c0070144001c03c14881d50b0310401c030103100740d42ca4020b0b00102e507a091802042c40c0000d171905c0c0002d006000240313084000c0c200d54100c5420303001541c080c06d658181c04024140c42c03240c1411281c1c03030039140c5140714040070300702503060a5205403032480c0e10502483c113011003210032101154402070716910803040301d075010070508502c0da814040c00445062100398541d1000e03541d807000d9202e02c140d00c2a0003c0c440c089560310200b05c2e40c20742c101149600318652001c00c5070b6580003200f100c0c00030413064113140e1400c80e2041c02440c00c032494 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 87096610 1250 87095360 87095383
    0x60c0510020c0613050703060606110f0604052d0a06140f1303031109030729120a0b0a0b03090307020406060215010b030601050d0f1401050901180902010e0d05070503060603 76
    0x1049a03884801684c20440e066000039502c07030081c5c400102c0810000e005050060003d5074401d0641b404100300c80d8100100c0e0030301400c0a070030100600010440002c0c0041c00140743c5403c410780500d4012001c003202034890360780c1c1c03681d0040213054000e10100394401004850751416800341551107207120001c4e00d00440e40d114819800300440c0010910a0b40315900c00d07400030145034a44029a40024500b00c196882200c440b015401c02c040c1004020300700156400000460508140708000000b50401004000704034241d9182008800c655541508000402e188074155540c2c1c246041d00d90303280da00c141c1069002c3c0d41424800140d5502c0003a24003010013840e01124016420040c03001030b01e1380041e12260410005101c1812034480610540040d005100000101408800d14060900c40305a102e64420b9a4080c01042140b0408400c10010314604d107000540e0701e050303c01a1168030200b0031107030b04160485031810400000040031001d07500c007142250860360b15502016954031140a5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 87097860 1250 87096610 87096613
    0x30206010303030b06040905100312110303060f01090b0403030503090715022508030d02040801050105010f090608060301020d060b0c10020c03090913060221010f0501140901030b030601060c0510020c 87
    0x420200f48250300c96040071500510391850030307a407446030703005032003050741c05001c0740f01c801307008004100002c00030004d40c00306e0b414080603020f410100241c52707002c0104054040c3e1030920242c0c0082c4c2c498180302d000b81108a04aa031070702d40f01d0030010056081100d450b1074510580d440403651340d4031000fa010f101c0100e50b00912070354040c40280107080507403041c949004c10603c00b01280c0c2c0001400504034044c58031341c005841e07a24000d403160950742d060740258184940f03145070b1032543e640500790308280c403d03504010100e9100c3c080032900a01c41c4000e1b1400c40f0b03140072000310300568490020000070031003004440c00c103800f2100f044128426035603020916030081103401e101d41403007040b91b944102c011103071503c04041034481d403050b40d10241f08200c00c0f840111400c14088000c00581e4050151782c601c01c14418240300001e08103e900f0300740e02103203420203c0e8100d03050303120f030304003041403030b005400c2e01c845507541c01c00175044c2464000d0803a02800760380d10602081c640c034400e03a500a140c200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 87099110 1250 87097860 87097873
    0x31006270b1e04090507090b0a17070302010c140303010605120f010b0405040e120a0801170d080a0e011503060209150f040302061605010e0a0b01050d0302071a0408100b0411070302 79
    0x2801d00038070340c1280100ba045511202000c4c0401e0b8280100c1004051180700411003002401c204142591550071030848040f46200529480500060312000d480e82820100030260103420440c460388075400150026210001c00454101d600c80003600d50403101d1465444580c80303e00788001c480f2000d02404001c090103000c10071240c60503400a4240317007031440950354105000d942d4803075158880150354010420701801080460303104011104000c07140400b8041007041f160004020300400f9088004032070301c68030201c0f50024294050540304580c10a80c2c550b42e540c80c50b110740a500160740c440d1080b80b480c10540c140400c000119005003500113002458141542e0802203150002e0001c0c8100402501d515000984248100d0080301c1c1030b10001d061408040c41c101002480c16000940a02c200b520b140300000e4001802e28140e44039080302d01805215650202018011548400076600c00d106641221030100d5001204100e025039083c0a0441746085c0124a44a00800100140e0008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 87100360 1250 87099110 87099139
    0x1080406020a12050109020c0c010c03080f0411030a0f200607080c07030c08010501030606060c031d0105090a090203101a0a1d0907020f0c0f03070e06031006270b 71
    0x1540106412122401e0038a003c41020140740100c4000360007000d109940014040c810290030841c20640110901c0e000489000c01e0b80e00805884000c2e008803101e5100740085400c0200803e0781650781400a405c460a001c03140c109400d40041030340003600c1d10005031003075410500c03140180549502c00641000d14001c0310f90344100c03040c1d0187c41501c0301c44c0260f8101100294041c0040b1000f8800d900000c101c5505506003501201c08030b51080c020b01250612000c00203800c95200b10406180c40d03c0005e04d0b030030860060326184103c2e6142544607090080101d4081482d5000c0c40c083c0c2c041c161441c0c0c0032500c0d18081550600c00350401c4d55907600c203002c3d83d9581ca02c901e190b00721100f05540d06d0b1558441600104019010658580c1c015820440c0d49001068080000c502c01242c220f600c010581e203048082034482c9040c6c0100445102420b001803210380741000000c1003e80e0126040041d10754502084207000d20100080c1c0481c281c4006a110345c9855004100500b1002440c0119030440d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 87101610 1250 87100360 87100373
    0xf191205030d020c15090f0703030c110301090c0815071d0a1710050606040305120d0f1505030c010e060f070201031107051c080f010b0304060e100606110604120806010909051f14010804 81
    0xc3e00d00c1221330341005803078240c0d80d403000e0007000c24451065440c15080d0307040c03c07180c5043c01e101c001080b03841d944078020850415400520702da154400c85242800f84142000400c85c8900c407a000084d26031112031242601d0301c800a446400320700c1c9800104159282d5030100200d9125511019000d82d020b408403140740300b900741c024410601900000500e29a081550b6016166060250080003914036410050350400b40894041c1e41c0007407030246040852000050820f000d214000307500c524003c00c0107011a4040c2d801120400c00314980703640c6941e034910780301da40c410b249280030070092401d007400044140904482ca00440039898041120b07170810005c600540c1000704203560280d100c054407002440b0502441165080c600d0020a9160400001501720310410450700741c1c0ba0f00c9282048041900d40c81300b14404910f61500100c56143d10004039182e4509400c804030b007526001c18403642d00000b012074148114034003000c662590f13031484055a6845256121404201030b0030014001648 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 87102860 1250 87101610 87101627
    0x1409061011160906060305010503010203130b09010b0a090c020706020604031706011b0614070f090e1008070e0a14090c1002011b0801050f191205030d020c15090f070303 74
    0x4084040b100300e02046080c040c0ca07442198400c880080d540c0d0401e000c0658140a9103000d05026002949542416103400b20720b040b524001521180198001c80c0d000b4000390428080c5050007001c0101070340d02c4003101401403e8a410703090251241300170006100b400421900d11071078264680014a036246070710b0107c1d80c1401098a81000003001a15000240c2c18500c421003601590000528216040320085040303c00340000c02804109140300d010309600501480a642c015086100316440b10b107040304800d5149e411401050188400c0800d004110000c0a4412500d100c028842034200c6052070301980c2081d110a004d40d00144418486414031070300300b02428126100001d40c1c00f0780c00340c601c0e00505180040c0e00009050310010011807500800c2a501c943c07085605620a0780b5248028485c003103a4841d2000c038031940d020138400e1007003e0055030703030103600904c0039541c4103450b1155640326003103400c0c080e5140c2020b1000c00d0b10010005118000c10b41d212000b0132943d4210b440550b240390 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 87104110 1250 87102860 87102887
    0xf0908030129070813060203040f090218062212110904140601140108090105160c0503040b0d09021801050a090b131104030b0f16030e0109020301110414090610 70
    0x90100100c2c0364420800340041480700d00502c0b201c0d849103101d62000020030143d911000c119131052000b4040d40b202c030b800c2c0c0310403241f1041b00142d50b2090700541402104180000c5a07002c14041010036400808200c00480076403a2801041c829071030744038907114840b0009024141c07050900140d1042e0030444140c1e90400c0c0504001c1e2810005401403d10300b40c000d800011803d40350800201041d60011905138000c000c402c003c1c0704500c1c1000f0841c0580608505220030480040c94003000c0c810306004840140c02c0000d0060b41d551036001c0000054100074a0803030080c491003620800306440300390703918161030000f020441040d03c0c161400c405010300701c034240e6001c1c090050060500704c0d1482640d81458002e07000a844034a503080c07801d1680401400622403110303000420043e4240316a071040b00140c0303401c000440d203004102590060100342c20081d0550302e40a044243c482202010b04203d6090243e00b90740c1080b00024070400c50015503045401c460119400780481c0d0244e101d040581 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 87105360 1250 87104110 87104159
    0xe0f06011a0d2a1b0f020d0309170714010302090a052206030c06030c0215061012020d0504020a0f180209030f0a03120b0d050a021e030a060608010f09080301 69
    0x303607a030201d642d108036180550495110711402042035a900049580465420005000240c0c0502c0d01c4801703c0e0300702050002d01c10851744106804042c01440c900002d050801030310b82045e20034803081a40c50f01940245003000c58100c02c0401d281d071103030003245c0c40054050a03036182c1503d0306081c03180310242c01e101c1007400941420442503102140c41850010760142c0300400c00d40e0701d0450083d04940d40c01040303c04540118001100c0002000c0700a85c000d00140c0c3c001c41d40b034810003411606080350400000000b03000241000d00020190001030065008480080c0140e17942c800c6c0201080c00ba10074904103032451513046074040c10643c081c011030540034060754601e09040380764078181f029189048000c0350031084203039255811882280480603083d5280580300e25203440c1c1d150740f1801814000c6c407a1083d858095003220300a16691003403000601282c0e54803440d868408082c003d02d0060204030741c6042c042d440f0b06070700750103104d06448d04429010720316400c020200301542c061102205a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 87106610 1250 87105360 87105371
    0x20405040e010902180402060a08060d410d0e06040806090601032105071b0503010612050105092b0212040b07051506030606040903020a0b0403030e0f06011a0d 70
    0x4503229030040105404040c0c000141001143c810415824290012001d4140c0c0000070800141c440b0002c0351b600d0040c5082209541e0f80e00c5001851414482c00c1c010002c05600741c417004810300c030300003028469401c5c2d48003e10701c04040c111b102c0440c0000d121002180d20201203030212a001d1007070403e540c48003602031707440c154036030301d2a501e40a81901e07908401c4d0701c940e0040041c0200c00c04000e5070048814545001d0900c401c9004115024170000079119881c4000c42c0c00401406084800007072a001e0000d00c106561000d92111000f0407070f1081d1900d508080015450101c04140032107044031000c10341100d580000844e4801031407918101c000c2d03100d0785049154410803907010740300410600089a0ba5428603181c0141004001c4440e049400788182c1440030316500411210b40c41001a0340000d13280d603503030400b00e1030001040ca003d41142040400e010506a041e00003443c6403101d0001c4800e4403003420b0310300395200024407030310001c0c0c422003e00840400e00400181a02031418401061 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 87107860 1250 87106610 87106619
    0x2030903031902060c04062109050a030509011b0f3507020a0602011a01110a06020f070507050a0308030406050c280e0d030801091805060901050a0b12100c030204 71
    0x5580e000d00341c0030140b0480301100c1c0719010340c10420303154000d400415550400d41340c20700c05008107000d082c031200c00d440941080c0c08100c4880e1701c1b9141d86a0000f04403002142181009400d980c095504980001c1c1c0c00150075400e040074407018000c80354000c0800c0b01c5035260b0f85400b0601340d00400a01c02d407071b148940f003204003040c6000950b11030300124011691400c05204010900d80c4690120040d6410503010450300b5020a0703114015040a0801400c046000c1c1801030500d0142c0000400440c404a021420080110081d003500e5205d141221303041c035114420062102d0062100515400c4204002400100c1e96004075400c41c181000310390400350b0070307013920ba1180c031b1140f0805540c14445000824459100d50b02001c82101a1340507190920310741c0f0010007581050150250050700c0710b8042d111074040704040a0051b40050590b402400c0841c0e41d140a0701c0c050724504030440c1005030240c0a0b140512545040300036010013045c02c1e802002c0c0e104003400e51002002c06050303080c0720008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 87109110 1250 87107860 87107863
    0x9010e030304050706260a0f1503060209181306020715050421030501060f0c0807020a122d02010f030e0601080313090507020a020108100f0f05040c14030a0b0102030903 74
    0x18000c070300c03074001381c1051400c00304010301250205101640da0441003086543c42c0354004403042c0c2100c0341c08070102d660003000d002500a4076a1045c0181d021030100000401c2c00801c0c0d0140c060390504640707842194010b4201281c10320400d80d0180342c40114004908000b03411580140380103446805000856941000c4090864000321025110780c0ba00c90300c5811805c04001d040c0340308541d141810042941000c0000f00701d4000804c64605108000c640a81404804815a088182e0040105e410b00391250103032036024224480441c3d90200303d2054070074500c00503110052113a0501d4000c5501d441e0740e001161400b034042804401d041c3d03030b030403203804031142400058041e01c03101d030007990382d1030346031080065500082d0f05c8070888600c0c000600050340d5000c01d030704812075024a4012003c2d00c80010403218418a0382c400b41c98a0305607100010500340c000540011180704803800c2000d02410042550081045403507000c0540c17003040003030440100c1e54000460f424040c81202d0800800c1c00119 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 87110360 1250 87109110 87109117
    0x100903061104030b061f0f03142701061404020d090606081b0909030307052104030f090617011502030405060d060503012a031a1801050109050d02130509010e03 70
    0x4000718400002c09005200e0700d0403031340350094015103007a400310903451039480c4010f1469500004104000d840b4a074214485d4014a88490360048024254241200d5007a4070006195461461007511135407020780041c1031043c3c1d411078605080391541e12000f201000700a40c488401010100c0c0c6e5010610f0110304a03104000c0900a494018211a0560945010340b8000e6075610751251134488108071796007d01106480d0050b405040040c3c98880043c030b1301900042d030f80341076108100c4a504102c1030503840b1000c0081a0070549410805236121740048a0710100c3c03da0000c9049455001045040b40740c80d40c00003101046e1040e20b0516840c1ca000919991001907640081c5844910510543c54284100006040780c50544605003170000000f0282150034a8000103040c6d4030200050b400c520001c41004034040109810f03072000900c050464054402e00a00780010320724403010459062500c110130320b20360020300c5840511955108035000e41001400b00010b0754031880151510310703081015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 87111610 1250 87110360 87110381
    0x3070912030201200a05070605040618030e0a090204140d14010207030309021302162a0306020316050a0207090e01090b0c030114040506090402010c02010c0503040b04060e0d020102030910090306 85
    0x824584c0700b1190400440111002e01d01d40040c007001400001d5400c08102d03608240e120760b000c40d9a07541c1e0f0800c1c01c02083d102c08444a5048200d031385400b010751010701c400c6201c504554a0320b100382c483c071041c0228051402203003042044078003028003501c0d01c0c0e06c65401491044100f8504110041c4a041c04e9070480001203001c42e484140c402c00b14540707160800e945921a5404508120458540303801c1c442c1511806004810b0200c1c410644400110f4103032045000d8091402c0070a40c0c034508500254811102840825255180c20200303500ca501111481c81355903008058150401d06400d009029490303001d150381d0742e95640071b000900f00c03d4030b25100d1004440100e480358584140c00440d941407609a602c11803a001c104034040d59003941a54000b6020b103400b02244102d40f005039880ba03400c0d0800b415a20020500145a0114100410507a072165603000c1d82d10704c658003845003407005000002d002d60001e000160450510000101b1441443d140c0051b84681c2c07925482c00301c4045600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 87112860 1250 87111610 87111613
    0x507020a1a10091509140402030d121103130201020105091c0f050c01060603062108030103080901020c1306060f21021621090618031502071406070801080f0d05030709120302 76
    0x800c001444040c403d410104028004122546c50140c0c0045c0d1940d0360341c113080090249102f4585080402c95008090011610240b2692030070440041c4c0410107076103404900540c20400010540340d004641c840710010049081c4608604035581654186003d940d003404019040c4041641d00c5002d00494006161a460015100781802c003800038861200d84981e150301190007082000600300b03021641102c1c1c000e07110741e46035900440100d0510060b2400c0d6580314040b030b00c1c54007252030194044d80840784aa21054160180750340151581003c958079400c4880d058520140c0c55600f0350000c1814510040e082101e04489640d040100001c0000f00c080241c81c034401405003581003070f6040090069403e2040c880d10744500039583e90980e0f800000e01d4060003020241c2c24105030313010780d0302c00d960080400c0031041c2034502a80d61008206ea1500006000000002e160741d400b041442054000002900703200c8200e042c16a42c541c4040e01060402c0203000d00082d10090700c0660300c00031031080d030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 87114110 1250 87112860 87112901
    0x14031608072607020f0f040f0f0f0605031009060b060304151505030a06150504060902070c05090702030a0e0102070e18010b0f0604030b040f0506041202010507020a1a1009 75
    0x20b18022480d500300454181d0b5006540056803404080180e40480ba030454504058840490110300312203a50f08465411908202c8124001842ca400c031001ca126002c03810032500c0d403070140700c90a41d480d80c8185034054006074200343c00c400c0c264100b20134a500138800410030904020118290780e000b1641034958604502091312220788502030b01d600c0100c1500c2a1010509100000752070361181000100002c0d520b040390060f0090100c1c9000040900520401607a695040084041c0d84600421038900020321000700d074030b1078a4804d15024550302d034015810660b9002003518010a8084414107500c02c00d103000800070030313404056120b680e140c000100d9a05009002900f5200d10307858036072003480c8040e0740c2c000d1512000250b034126604011000080c2e00c80e424031a8242290140c0a03007a409184100f00c280100d174005828001c20550003042940e8520104988034580315000038500764212074107000c0044502802c035040000794400710180d5907111000320407106100590400b041c05103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 87115360 1250 87114110 87114113
    0x31903051201060c08040b0c0c1306080105061008010e0c0c01020d0219020c062a0a050d170c03010e07031508011d060f16020304030b0405030d1107030c1403160807 72
    0xc400c1d40d0300500c0e03d410011402031312645c4840309400b45008035110004041000310540c07008200c049098180507204031003a45244003000e029042c00e000f5000c0a600b0100440c1660514510205081890790f46200c0d40d41d00309200c40b996910068507092200d0002d00070304140721001e200610610820301001039071781d0400f0040e203103000c0920520348103641103544e010070b443c0c6a40c001c481c58100101c0140f84074081e00b00b00c58216000c0d038419410781d840307086007090801600280034410510f054840d10a103001003500f00507004001c03103060004071014801048580090041903800c055242004520590708030000c208044090b4400580350303443d15030200301a1064200c001c6013010401c06003840d454074941206002c28043c000c0009224bd514104070708510a2060ba409141d11402c80101030921f03050440d901e81185600d4400c00b46400d1007050090207400c1240c6101e941a1140d50410f406030700e50f02002c0705400e000d1025404100f01c2c01d40e0000745400c01d018000c0c880d000705078035084a07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 87116610 1250 87115360 87115387
    0xd060902090f01020f100c1403011205010518100b040212090d0801140901030209060a0510080105011803050c1e04060807180903093609020102010e0c1e03190305 71
    0xc2c1ea8141035401c080704260f003450300850b032009801003444020510002d01042165005544048448148408400441c00a14010706403051034060030090101d91144000856a8074070104000c5541d8088489815a0f200c01d41000d050b00200074030060a12841680c4d5605203982102c038a02e003500106508200f080c2c11408c0766000d0002030200e4408441e0350004100c5a800602010340728030000400180c46548800825000d0040a0004051101d2801001d0f040c0c00003805210f011030740d8900e09a084915080c414400c40350440d00818051b08144180404101c0100c00c1c001d044003c5100062641c0b2207000d11030041c5804030080c500c2c03a03d00007054081303443c519801043d00b4100405a004139510403481026119086240701c00c00d103403511040c1054404480401052180000b101c001a0141e400509006d00030380082c0400301000000c00c1d00c1c2c0340001c00195100404c006401c4108081c034100d18511074005e000c44d94000002040e001124006607003c400103040010242422001c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 87117860 1250 87116610 87116629
    0x319120e0a120503060f04020705030408010216030306080c0603041506050604150e06040e0708090a0f060e06060a0b030c0c0a0501150f1d010b030403182c090d030e030d06090209 78
    0xb103031401c54110306000000540d50541c0e840c083c0d110755008103041007840002d00c1100e00800301d21000315034800004c0200c581190703121605901080ca0000001511381011400c0e580e0007500510380382c51940d0741d0ba941200c80c0c2e0101010880103503a0310000c40d01e625010001d0010b0122a140c1c0d60b403088640358000c0114296040b41406200c00740001c10001c2104926030307400c00140d080a0125036180d0410340c0c40c0c14004803000e06280703048103004050043d998041401c1900c08820343d0010783d580d009000079918284502003030704070100002a04000b41c04050942f00e02d02c0410340b01d180a10383c940c182135581098107906007003030000c4100321a0342029012801444200c50310244202c0e4111501c105840503c254580b89200100203010944242152103040c8032007550310f0b0510703403502c94280140100300c8c10030302c00f00074020390040440c50703203400180b203100c40c40000c150061083c0000c401804a03443d14144600c030174002e118054016014800141c151603400580754103140041103450381 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 87119110 1250 87117860 87117893
    0xa020a23010c0c1401050d050c0405010f0e101d090108032a030a050d02090907030606032906070f080a020105090709020301080303060f1302071b0608090319120e0a 72
    0x260b510280004040c850031208480d681c80344180c2454801c0d0043c2e8040c4a9940702d8600545000e04210280010901a000307444003a40c8150180700b02c0c01098035240300201120b41e0100100001069240c030900388940c0f800d03400034450f1064120740011419000c030a810043d0607800c0400c24081c1c0034405a5010b8101c6010852040d00341090280c2c00d0716480307050b011004000b03002504401d40105030b0100c4025a07400740040d921440c007240000c005000301e02030140000e05012541c0307140802c9100100c06c0031f05400d000c1000c850001c0030454281d0001500710b804240400300d0502140c030b0b80000c0c003204001a0008115890f0240c0541d0900c041d40e00810751051040c001405401e03000000d82e50300410640c1c1d103412595000e00003543d042c2d00c5001c080f88040c00051442d040201c08006251000201c518482d40e964480e6001d503104001201d0801d455803040c4003160407062828401c6414a4035800d01005030030801c0000016100050f903150580ea1004015000300720740d42d890f02c200075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 87120360 1250 87119110 87119117
    0x601030b0f071d03160603020307030609020c03121f15020f070f060305060d0203070803180a0b19090f06360b0705030c01051005030d030501030317090a020a2301 71
    0x9182482d00549440000311025a145020000c00c010030b440401c500e0502401c0250f08500c0399644450090196200b1034403000000d09200001944180b14001d41d04440c000201950400003520b140609058000381007c100c81c0c10407905507404174081044401810100d0160b0704a0144c010010303140c2003020480c09015840701e5001c01040000071100415603a691402103210f844000000301c4413128000047d6160107500000184120f00000425074900e80620180800500300100b0940016900c1440090031003080f61107030b0910f01040b002184600c40c103022580e0340e00c592000c01c6c41802500000085a4000c801c2c08120000030f11704210800511403140001c040e2034407030070f0206114803407121181c902040c01400c03c0403e00c1502d1040294000030012031070003580f60411303100d043c071440303020b8002c40b8150b8140c03e1080c0610b80c10781e03405440740f000141042100303d05000d0b00038600300b028011010300c1001640c0300114880103003507009040402c00455803100203180261400241032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 87121610 1250 87120360 87120391
    0x90605161106040b0a090f050d08070e150901050a0c05060412140c120c0f01050903040603060509040b040b0606070807121b0213050c0f0301090c09090b061902030f07050601030b 78
    0x140710f040b140d03175006201c041d001c5254455440c00790700c0850500740061850040c100020100d40d84081228810030003540c480c4500700f104020b001034001c050541800008040208505550141d0700500203074080e45000c0c64181b60540b18a802c0407c01d0f02c00b11426032219200301035050b401202245a154401c540c14903040c2e950030020b0342d611441d00c8400b0301200108840178081c2045c0910401901e501e802070200c1c0c50107150180d00c85e4014020480401d113041008a035038142084043c1c42564444e40d10000c41c0c0f60f546506d000d03000300414695200f801000700c800025002c03809003202c0f03031040648074a000384840d00608180c03442e0020751080e5000510381005070341c4a208c035029103c050036001811303899a0844c140e00e0b1041c0c1190f64202c00001000040b0b0440315803100c0c140c03410781c2d0b542d07445e0b26840d6554030003540d004c03106941e404101446010316010a513000c044076449640110313403030920007141940c030356080b695007540c0300d81100d4010010b02c20306801c03150740302400c40d255145 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 87122860 1250 87121610 87121613
    0x40b01030b0d0f11062a0102040b1c091a060909010b060d051e01120c060315210c0b0d050901231b0d05041509050c0f0409060516110604 60
    0x1c540750508000c1d140d03100c9071861400b800958143d0605401000e04040d94131000015440d0445c403080c00340d000c462400c40c6d107415500b0810720031380f010f9850b40468686081d18900c2e4201405095011390401c042d51980740d140000c22280285d48034442a048010075460158100715aa050050201220340d0401401b02482d41d550f0044a028800814001815407500c11194444c02c0407140c0300b60007212540000300740d40c0c0520721510395962290004c420b41c180c0350407044043c0d580f82001d601c0206da00401c203004043c2030008110f440300103603a007804100002e46410164040a521a1225003000111900c4010080c010540d0010680f4024881041d00200c0000c0601c000303204018588403100202c1d06074000c0c040c1102d071030780c50034440d99165400725011200800d02581c007103401c038650b60206004510540106146a41c00002410401c002e6000380490b0103e07006685902994035084000050070038407500340140e8201f002c02d00030707488800026104001903690800309038080c001704070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 87124110 1250 87122860 87122869
    0x30a06080d1403010b130f030311061317030c0705150106030b04110f03040c09050702010b09150a18020909010902090102150c0706090804051e01020d05120a1d15010302040b01030b 79
    0x2411690440c2050769542a240c1b0032406e036200c1501704a0b80000d030140004180341d07114006070060b0a900d030644010f81c4581100626460113000000c014191041c000d280c0911034034007031a8022100c0c000a0314010a0b03584d51401c0591060b414500c9800c000014010540c2c180320b032400500d4180d404100c07072881598103000c2c500844400d400d02800010000d010800310361014002071000503018041030a2005010707000e0941e150455000d400f040e0002020654181e0051088940141048030090b00b030500c0b000c901400b042c01c2900140c0c08110010254071403041c203078024504003a0060b00c0f11030000c002400c0c0809446400b090301000c00500c060b00b00520b04031000181d020900080d840b8130f41c90030340b041d80255407103260f000c1c225124954141c1142426902e1803603003607003510414030440d4011348003400f43c01d681030410212140020b41c00c4443d82d20500d202c0e44403504182d031000b903900702545456010001c00c0300c44001c80e0010421818140600c0140440c242403d01c120050600801e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 87125360 1250 87124110 87124117
    0x3020c1516240b010e0402090117180a050a0b0c0405060d0209010e041e0f020a02120c0106030206040b040e07020706050703081b160201020c0405060a0515090402030a06080d14 77
    0x11400303080c11441d0803081014941c0c1c0e60440d2040292020000308528a81100070541524001e0205a00004c00440f40c9801d108032004850161075861004004003200300000b02c00600b00002403048032080819540304000700c884441c400c2d4028924050345240401d020b00d0050050360905006200500c4980d64030400c6c4c4c5c8445410141c010784911092380100c03070350060f0310101a00280b50a42c00c005110324105404d226044a50302888a600b000c0303c208120312404400c0d81c0140c21a236461110700410200521000c56034000100310140c89800051041d172003a84031925020f00050204030161a00351559071201e4240050300c1d1052804038060f00500ca0078600404025440300002c012500d40c81c503180e10240c50010710707900c40000f00004110380480301c1050340584504410117009151900034a881800e02074608684107241c0400c4c41645400c07082e512000203c2800021840e844910195106140c0f40c003020403030350728088101e410101001c0d00c04042043d0541e81485503203401045 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 87126610 1250 87125360 87125377
    0x70b04080c100f0f1a2107170d0908010c050301050909010e010905031803060c0f0306011403090616080603060c1309060f08010c090e010605090f03010e01050403020c15 74
    0x91598540780000814284010000c1c400d40b2103141158010b0107603201d90010a030b2840009013007210084410949150301c02000d00c0780e0780302101c03500074010407a0690b401e50010140c681207420b141e4458440c80c1944581c0c1030158425401066141c00c800e9100f0030020083c404407000b0423068200802c0109180300500486016282c808080f030300888095108040d070000250007000095440e00c5d00d252240c3c40100c8264030115841440c0e046d80c03802141c428041c450080c401403400488207c0d041e104d8000401c11814001500f80504542d031001000b1031041699034041d24040c50680444480300b031105000508000f80801007113400e840000d40b46c1e8101d444800596101c07404041c042503002e00310b03048000420704220000650348240c140c4081994104030007030000d9003001904a600741c1c11446150b0350b000d038000c0100a440c1c0264002c082818004c2d0007103e052403281c0100b420f503242161054074980d5240100400e00d075061000070840703441141e0600c8200d00e103407100f040d5405500700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 87127860 1250 87126610 87126623
    0x311030405100225050705150901022d060f04050105070f0c0303090c0f12050c04050702070e06180103080a0206010501050a020d08090f0d050a030605040912030f110d0917070b04 78
    0x5480c0c04000440e040d144e030008900400d05401a118681710741c4170012071094134001c0c619201d04180c005500310036203c1441042e801403820040c0b42c01c2c014116252084c20080e98000348101a03205402800b07481d1081c019110107180030f00f000d2500c0e41c2110b4008045a003005141c0c1d0070b20223160b80c0421100c0d40103415107070215040030107007000c980090040d4400810109140000140c3d030804403010070344c06010f03200391440d4100d00420700081c1ca90071242040140c00c1410180030f0501c10b00340d4541c001c10041d0100358039450303e60f00841c142c42e00303801c04d5561610104602c0701c429810020765004d00400c0c6429401e0129880c4080d581d80700c1d002d9040d051040c2e080c00a10681e6042140314003203e9254110380030a402000040c1480d846000da50300040d0410344049010304141c00750303074501903100c103489c00f0074003e04104800a0a0381000c201e807154681640401050404000e40b08240420a00044103100c61400c11500b40c191340f03d1181c1030106006050204010204840e4402e41244 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 87129110 1250 87127860 87127867
    0xa03080a050307090b030609010e040218070e031018080708090d140d0309210e03060c030915010308030a0e030c0a2f030d030902030f0601120b060301140105130204050607080a03110304051002 84
    0x2000561142e0f841003000300d0f444024040140d80b076483f103082c007100c0320143d06940c822031180702000207641d40c0c4490704030742c1c03c4840702d03c0001a030100c001780031150040000c241040034010009512403881da405444600591030f2560080e00e05000b0401445c00034203040104414079a11050765020b040408008107428030b80841130a401911444a0984001e084c1e4900e8078011444444641044d20122540c0c4520082d03094001c00061000341038070740146026040d9a03c16030b07078401074002141802194007090050319003150080101d40d114038880c800c0b440c0d0200c00c110301c0700008203028019401c3d0780500c0c028001d1503100031492043e903071760500d0081000382d100e0001c00d1030301c0200700329000c0511505000050016622101d800c08602c070381260155074441408250980380a802c070070312900540e00c0104401c2c07404070b44d140903542220002504042c0e481740003c840b500710100c1503440702c000040120851307505111345c00d02a1000720f82d072070550400d43c0703407203a4400d01c0410340107c07580c0c0003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 87130360 1250 87129110 87129113
    0xe15010e03010f06030b09070f12120912030206160203090f04020f0702120f0c0f090601030c021c110d020a081c020d060303020c040b010305090a110a03080a050307090b030609010e04 80
    0xf900500101c4500c50428000255240b400c00c010344012100500e880c0100b0002040d03d20196044804441070064069400b13100c6498130079810950400d6042072001a010000b19028a6a14250194042c1d000b5209502d01240e880c40c1c00d0300354882c50345c21074004120807000c646e6200c1858074031220603100142c8a40f080030740c0f4502440b41c440069400301030710800c0160120000b402c42a4078407140c0540c0c03504125134081c0a0003a010000d01644220200c0000d1200e520a510282448149104507007403030b121482c4640040070070034619400944807192001c0d140c5820400001c01990601c01416041300588400b078903130181301c4070a46460a459070003206440260151103020703050b480c1c1044566a64a0080d5681c59a5110a40200d080c81e16070440e5600910601d44120407260141071a0a020394841405500c03010131a680000000c07808000700e25044068210300905485181d90f178100a1409000022141d12001030319104108205a545500d85183d046076000b080680060b100e5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 87131610 1250 87130360 87130363
    0xa0b04062702090405090a11030102090f0405130b070c0203150c0307050c0a02100f080f39130303080a0501061202070819030203010f0803030103020f21060c03100e15010e03 76
    0x1007441031541301d41004103000500c800400c02d541e8180c401e01d18481c481740b0303483c01e0600340d000c1c10b0704190740004c05000365442400c054116039030101400350800c44002c069940c3c0303a6a10070039220480000c06090a04085080400c0140c084191907080314680b49022a4103030b01c2444001c2c400020848003240002e0260010000030340259801031003090b141c504414000c15220f401c04244000403d8080070541c0440c0601303101d40513030364a411070300c61341c4010f0032019a00042c00341c0c45a640b0f42c07050030a0900c407c5a00c0981180354000303da00c009245542002003c082d0050b01401c2410f2400c00101301087d00700050051903600032901588441003410029454000c00300c4494019a51004603154035600d40c0c0118103031118507203035035003194640d002141e881c0003d002c0250003811010415a19203400c01a20740070701d40b0000000840740c00201040d0500c607080d182d07070880d02008010302c8a1208610061005088050101c848900d07011990f807805062804c0035a0501c03043c2d41c0300c0300365900c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 87132860 1250 87131610 87131617
    0x50c030304230f062e0302010509031005040602030f01150813080d0f0606110706081306020c070f030201120207030806190803040b03040c120b0703020d0b0a0e0a0b04062702 76
    0x2940007a99000c50400e00c10039200c080c21561025a00c940a0852100c61003908011221038150345c1140c80c0581990700544040d841340d200ca5078140301c1d010b00c04004007400c1c01001d225900c290070150303d9080c9100c0e180d10380b40301a007100c0d08482c072964101d0016903100440700d50084813119460011002d82c00d040103240301c0e4403040c011203400c10b4840e0042d80c040d60024400c903200c40d610403402004200c035450311400c10f8003c4100043c420340105034603100c068140d1114a01418005251101c100c075510f161060030360144100f860220820401c7d0f41e0020b01005078044010025407900c66550740040500c80001d2002d8402d0351041c003014100325000304110040c3c660303d000c0ba540c582d00d9580e803a0464000b11801c841070820524041a0a440c00c0114070320142d00150b550b080d07480c0c82405070007030740011050b5513a072a0340703004008081d0340b44103a0741c000705980c810100c1c00b424040010b10640342010802da0155042103010003020010742d20390440407a503001d05494000103484020013a10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 87134110 1250 87132860 87132923
    0x601060819020714010e1524031c0f14030f04080a200f060c0406170910110414030d0e01030c0915020601060206010e13030e04090b071d01050c030304 66
    0x42c1150f0081c0076072101503000c4440c041801c4212128460071284094240c9000c4074255009038240e40701050031a2900000c8c3c6101600070151164644401225107100040d482d411002807402803000d108241c002c82014001d10081580d24654540f00381c48042d4464041d000500100c000540d0740b41851140d5003040c54080e095092620304003146402c80c1daa4a0041402c19103070045001107201d0f82102c1d8121000c44403245c0b1180c6d21460064240170841d03100401c03840c0709008802c1d40d41700c05030061154400004a18096607221414100d080d82080e10840200c2c0c06548107118081c1c80302e42040303c420546101b442d0210300d101004004559440040c1c0c80718070b0407290040b481c2c0100f80c001c16958107071100c680c2241c00c60380c4d0320545038043c900141c402d1621204d5108000000c40c0c82012041c001d000c0103400480c40030125a1a0191881e08403000c0c400508403000d109c00d0a60540c08040080f902460000d040a11003824980c5074400075100510301c0002c030100b5122a41d00046000140303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 87135360 1250 87134110 87134123
    0x10c0f020a0e090705030307050c220c1e0e0906040b01030f060305010603110303042d08060a0b010905030a0203030301051309170711090103080a0c05030d0204031407050306010608190207 82
    0x319a1000780e840001c42c1580c410209008050011400f0b040010a64814a41100041003140000d07014450203500711401000c00000c6401e605010381600d014031500000ba035507803407c810385403c00040c01e080040b031030314040040c2079060350f4440d52820040c64009100b201d000a03848014001030b8001e00007480c10481b12400c00b41c00005000c810342c03100086901940c0c0d000300250901c0105500c92060f401100c07942c444095214130510341665070043d801c15403000074840c4a031200c203894a02407046420017032450b01c0c1e2042020750350b80b140d038120040005a00816500c0125800a51030b4041400b50070700540c14100c10101a140642041d00300c00e4005c0c0851100c641c41c903001e85815801240b0581d1880c00c10002000e103800d02c03c000718126600a0055070400340070481c01c45440090420540d0544003e10082d1010b40e038520007040254414141940800d01042d40c0909124035680490311030340103c0c00410074980c12003002da40c804600500104540102c0410314001d024660018100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 87136610 1250 87135360 87135379
    0xb07140c10020705010c08060901120f06050108010c0909050702122a030304060e120409021b010501140a08060105150a030204030f0b060913020127170303180109030e010c0f02 77
    0x1080801c1d0b00a08a41d40200002d0024070341e507101c241c514031010341da4103401c48005c030010440b44401c030901e050040e104080d401c06640882d00c4603000e072142038201701d040340d54810384002e0190300031314038070b00600182d4014080d52400800207034881e1013440103595450000202c420800c0c040f0581c242c00c2c1482d407202d645030010b8410401da81e035001100d0440f655403070500e0041e0003030f0000402c101e0003a05440103038034150038660340d08040c1d00000415912210081d407078040c4404203016280c0a03110740b18030300c410342c01c1c0682080f50301c103010380c000080d582000740140804d0b181e03c000d114210109150007903840c0581c1e08128028403070703580042c0450304000401801c008000c0609030261504680368602602d502c140342d5030b1503c00e000000d0220745407904049076400040c045102c4034181c12503011a040e5280c2240d2000440c404c1d880619400000130424424003001d419040c40c29450001c00141c0b200c3e950180c445460b40c008581400700030003514007009111440b04144c40d5024001d0b40f003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 87137860 1250 87136610 87136633
    0x60903030304260408100c0c1a1e0f060108060102100e010204060f02010c0903032a0501090302060f0405150a110c0a02011e051206031c0801050a0608040b07140c 71
    0x100c41d1101a00d4200c1d8580d45501c0310301d01210801610300352280100a04082c40d05103086c01c0c000c220100704441441003044040d03021450a40d1607402c80316007060884170031b180011140a07040c46101080c040b80703514009000c005a900d0211680c452020f08000419441c0c0c8001030340743c100c1c0c602007038030b41c1c0c0d05243e84014541c1043d0003420840f400d03a160403000900d4400d0580c2640d07656507420000507060102040032911072f20317201414100078042c6000200b90320484290f210f002c1d030010395890391200489800c1650402c0b0b2507601c1441180c09400f981031903925035031142c500b605459035001010010071800440c5500080d080300740301045c01e030b031081c4c000740040d102c81d000e0310207034007040c2009d25003101c0456a240d2082d1200300d80d0f80c0e03180340051848a504440401421864140c890130381c1e006420070030325101c0264502152100d02080d032500080101d0409180c0041d010000124284000038200c610415000b160a041c59903040c4580140702042e4041c0c01d002e4880b6120300d100088 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 87139110 1250 87137860 87137873
    0x90503070507081c08070e010e0105091203030f090601030309030b04060b1806040c0206061003020f0c0d09030b0702011b08040303090c0f09060b07050c09070207030602130503010b030d09060e060903030304 90
    0x803005401341240300c40304001d1000e40c0c9648040b1804804500c202c6005031384c0750711410060f1040d03101410010b042c9000c0c1c8000c00c1d2080392481c01050664000010b104900291040080d4481451402007081d9030542d0750040034240c071840f0042c82d0b0030030400894208880f50300503550703044020b01402600d0092002e1100340203c165403203130143c0c0c9060203100030300b4404101103100b004080d0055003c01c9241008400035404840c420459000a11580b2000301c03041c4080c8040d00300e80c4e42c0c1c0074003403030070b5040c5510100070261528096a1420501c0301150610460745500c01440d0704200e07209548a040035400382a04007001040384c070700c640740440c0744604400840d013910740c900c2c010001d032a1100c803114402e20070900f002d0070b0b03684840d20b4280c85181480c00c10394042c0980c415103400d196650790b001c05a0700310f036038103481e201c075504428030a5080034450002c080350f080300180541c1103c500086c08a0681e070090400308a4520b51000103502c0d0441118a03400c00642102e40e81e18090070b00c807 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 87140360 1250 87139110 87139123
    0x1b030706090b060907201204060309150b091302060c06010612061409010e041a010305030703030c031427060f040c0501080c0301090218040c02060103110604140409050307050708 78
    0x321112504200800d0441c14142d4940784a00c2c01622521a00c00b40405070018000a50100035000e10400132007041f41602d0b240038100420702601c0110b0306406601e403c0e401c0360760044014131614508012982c03a591034000483d00405144400f24115139240089801c5106098400100d4480c1c100000742156001c0340300000f00c01c07242d8080101d04d0b1a5003200b942800d8200203c1d40c4a641480140b0001c83c1c6680c40720f4110f449130b0303058580441e00e918041042542640155070580010450005241c3c16004801d1032400314a030070010780103240c4180301c0007440542151181c800c0d04080c4c215a90b5112444c92001ea4600102d030410702d0500541900070000312801c0318981842440014554010040709018449400c45d01342568208114200290480c1041410140c510412440c2544030781c4603001c80440369902404566040d405c0820812a02941d0b031801440c08104c04c016400007180d0342501d10a080701c010030001c0d01400d0051039405800006003007070280d400c0008031103c001400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 87141610 1250 87140360 87140363
    0xb0402071a0903040501021c020c0a0e10150c0f03030f09060b130c050a05092103070506100b090613030615060e0f0f0405092b030f020405010507081b03070609 70
    0xd040e42a034610b60480d4480c0520300c00c040c0035034050b080703c00107020700001704500f4031554070450f00038507400700001d00d880c511790f8400b849002d0384c98288004928001c0e42c80d07020b0f002c0d50f140001010404a0000c04010b0031210103050b1400c08801070080620980201c0c120160155003840782c03410600f080c80c01883c2c26440944030b09200c1410341d4940b2024042c2ca00d2001346034551078141108040300790b407540e000d410095844004241269480813505985154a00c12000210385a030710900d010380c904540641003100001031440c080014011001c103c802c240780585505454100340c1d401501407110603080148868103220b4504031260540030311101f11541d907683c08000c200e080c0c080c0151204800842e6401c54882d41e0070703102c00c1c2010b401a5402081c0300c07080702d83e031f4464003a03801e480c4a00c0700141055105858420184981e00d4040d1a52007070103103030b0462400b031078100082c3c024410b450004103200008520341d20802e0300c41050850900001e0706072507442e05903150890051454000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 87142860 1250 87141610 87141653
    0x30f05070e0a0503211305060708070210020609060711011506020a05070f03032a02040908040501020f030f03011e09060306090b0f06030703060e0f0304080a170708040e0a0b040207 79
    0x700050f07900e80010000c424407070b85442c3c91203058942d0055825580020511640403a19401c0041c50352074400c028100c1c64041d002c9542c890315a44104110f4071201041a81194440c10a1220340c400214640f03400c00a1b5080070941d41010410117030140603143c07803100041003881c4c40010302c581c0104444003094882e1054950361901d6201c00d42d445500d9000140010f1314040c416020219142040103880108502c2c1e10b0035600d20307030b000030161000410100c4130b901c0701150810655804100d0454003100e540702a50500000238030307903240c40c001441000411100304035042030b14181a02210003509283c00b0070b0000780d440c1c0c28001e01400c40d0a80032508080044001076030b5507074103588107001d0b01e801000f52001e249992944009015440a65501400b40c60400b8006c884100300800090102070f002d00700420031b5040c90300d4091042051507000700d500300909400208030004650a4a601d441802030a40711283c41d90001d001125005400510001d040c2051007100244002c2c00c111504 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 87144110 1250 87142860 87142879
    0xc1701231812030109020a09030609031e0207060806040209041d06010f09060302010e01080402060d09051c0807050a08190e0c09100609140d02030319120c0801060f030f05070e 77
    0x542d07519410ba82030032a00d80c070244014001210550010503614209103050f0300c0c003075100c0d2500030886811f10300450125200c0603941c5c50800106801880c411102d001420040f842c106010f400400d00422561089500003258800c0d83d560740d011400b40411400404001241000c52070780e650303402c2c05400c1880c42c5648000a000c402806500140e81c0d06950f080c150701190070055030b440c10064401c80c0c0c090b205020342002c00303e841c450301c2005d030701070300003041840b094951208014072400b04c800304108809040040543e008000c071102e030092490800c40c150f0310300c014024000380c14522007800740c2c2882e024111010f4001000c0144580480b140a25600d4450b002006410076205680c0400c804a03030411650100d002001b824810181280900f11510343c00282998404108191a100c68110030b5682a9000c01c4801c81d8001d102802c00c46020b000030064503405051240784208062844000503032440f0b600000e011188200041c80b060a00030005440581000d50f030502880601 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 87145360 1250 87144110 87144151
    0x3070804140c100807021507030b04050609071e1106040305070311060103150c030207080d051b090f1002032101050f03060f0a020703051309020d0b030a0c170123 71
    0x858691258000108000f031148400c010565034090000c003d50154060600440301d20310300c6c100054400d5405507000a19007494104204c21600044c2055020714021010010f0164014420207a03145410440d2450444000d07412240c2181d000c640d04100d001e10340038402015003043c05042002e1280d114094110819015165124401d2002500080c44110818401c1c1c40d035910104051001c0d00d0b0151900c0c0054561032079551098160304252941e6008100880680c0000e1842070f41c80c0d40c0c2818131303020400d4001440e10000005041c4116000d81d16000171f0740c0208215000180c0490f03001e00004d910b0402c0d003441a40912070309005804880749a252440c010912610405507081c192000307032601c00006009404c51401201440030030801d80036900f4001aa450007404040c00140e520500b0080a80541c0d0002c00c4040c0250f0040c102c2c40006046000360740182d41900b140258502402030b4114050304981e01da00007444010350a41020340240300d0460b11445003031400d104010401d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 87146610 1250 87145360 87145363
    0x1e1e0606080f0c01030203090703080408160501140d050c0d0504060f050603120315030a0203060117010c050702031b040f0c020a02040506090405070b030604060b190207060806031b150307080414 85
    0x14068030b600c55410100c10032480e507009602850300014078034210740c080d5480342e07200b000981c415000484541c0c0580810400c044500900e071014100a1a0410640c0c80302045200c990140141044450340c0300e40000300c3d4001c1c4201642c494101101051003c2d0620303085c4000189040622a11854100000280c1c50b04000030100c44401c00c1480340d610759a240d0410b0a40f454214543c20b80c18028152084050f0b6810010103005e00010100784008030220b08480703084543c1042590113005003444035030050780d03010402001101c107920503095000201c5000034018450f604805501e80d03d0a4050b210091340080c400c060a442554200411340b0b0b20710401c854107608680c014a150310a4a040c05900203170310140d030f008040544041035070b03511076a03000c80300d80000d89001124400c403d8240c2d41c1c103904200440007040c2d5410001f041d03041c4800460740383c10060002c45078201c00e008450002c0e4480c211070694405000030240e440c1d05080e45c0080030300e08141c4068800d210b502280c145160700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 87147860 1250 87146610 87146623
    0x60c17180603040501141602010606090f09020a0903170a18211505010311090a050106050f0c030906030115110106080a030c02011106010303050901030f05131e1e060608 74
    0x315941422081800001000402e40c4020012101552038008801458281c0501c00e40141c51100c510f461705014004024215003603a4040401c21485800422214500d20036802c1550844400980c0c3c4025500c0260381400c0c081d0320003001c140d2881207030b035400c40c1d0f410701420804e0b0003a640c402024240c01c0030b1164414981c02884500c3d08540955070214805c4c1081100c480d00c1014034084c0071000041d20030850300c099005607030b600701044042615250400b000da912000c09442002194100500148a4000c001c43c240049100041c40e4038821020819526180d00081039559a90b8444000e00300c0f60007200c13007103004034092a000030740d100d42c107001d13090030f075100300c0c004040f450768a4038210f0310b00c584000140d040c00790300e1010340f25480d424017815000e5402900d0b8659111102d0f000181110040c04c0c484840c0b84c6400c050040a8103404026058180c000d01c0310200140001c1000d800b40303040c81c00007048442d00c07810341c2405402c188120300c011801031004001040e5210b825544864 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 87149110 1250 87147860 87147877
    0x60612060b040905130c0e0114011704060506010905061b2817040806130b0702030405152b05070207090b0904060e010209040c0302030603010c1107030b1f060c17 71
    0x801c0c8420b0050f0049a44415440580074503040080740f1a0703110812441c1184d0440c1e040030003100014044003040480743c1030210300a20744404883e045a2075548119030107040140055142d0012580583c45000c4401c00340c44000d03c919504d007904800c84c289141d103458103400b01d010b40d0351075181700c5585000c80902507280075182c0102e844603540780201c0000000054070b01c00d50510000c61480c1d4200825441000000c4a602e90107005042108001c00000d00c03450440d841000300340440d484441c06160600c0e014102c541d100d03e40d820b1815205060502c4c45543c00d52030144100a045880d0080c1c1d008402607000d4600071611041140141c0d0703554001c0d90381020900000c0f4000030196404042c860b10300720001403d01c511b41d40028143d031140308000d0002038010060203610319080c890702003400b0060500e00700c3d44007080091034451280f80310282c103c080840c00240d082e80c107000c0c1c00080700c24201040144503102d540140841403414810750741091119480c0400468560071a6480b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 87150360 1250 87149110 87149129
    0x61303050708091507060507021510060507080d0e06040c061d011116080d1403010302100f1211070605090c060d0911041109100305150409030c0b04050106061206 71
    0x1c40e100c0310b20551014440503041201d000800c01601007040161035100c1c407074000801e640c01c052000910b0042d01da240e01d03062030a080188042e035030703185000318100c42c41c84c00c1881d1521900d041c04c0c00c0034011200758002c06410503a20101e08103020820078071441c810103004804a4031102d013201c04141d0510313103000c1811941038001c200d6005095810307401030701904031400d020654001a0001005921050450740a1000284070325005100c60b130412004c8540e090075980345400040002441c440362105109410b40520305280c444c050402c040b0318014400d1215641d201410030302c1e80d2100105603405484c00c00462544000410b0010078560014001424182144041c40040400a03030448103d6510100c4e00041d1312a4015540c0700d50501c0368241c1c0b22202082840000c2d031345006148100b5103005c0810041004900084001745000c1e2000181d6586624042d1a11540d06202030040f86a0004000c02c1100c1500100b007940c3e655901d01903620941c180c1d203800c1c1c8a0502900024 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 87151610 1250 87150360 87150367
    0x70219080301170f0706031a0d080702010e0607080315130207050c151308010b0a0501140d0506060f07060902040617120c15010303020705010f050301030f12140a0507020306130305 79
    0x30080100d010b107800c450034034143c800134011015013514003a419070000001c640c89104005c03d20300808500e69001c07405881e582072407005540c440080d07204218000341032092050111010b5200c01d0f090316421640314064035a07a0402e8142d1480481540407d075220b86510401801e549003203000ba6065140c1c84002020800180b00800c15200c0e560400c01c44400010b01080f5a03040701880c018001f0b2814000000304103102c01c0a1140749582900100e040c890100c00c0d501e890700340c0104803014400f44000c009015140e100002d003403446020102070045901003105420f200d081e41c0443c1c1114800c460030444290307108440d00d1803e010340114110b41d0082c034107600c1070b08026002001c9500c9200261031800d14848101103843c40280c006400603807180c0302c14815960000050001404241045400d5614503603400684080e652001401c0401c01c29900d08440e0003100082c440007011090309444941881c0c0c000c00c83d810144060b0b22910680001c02c8840c41e144022400458040d07603020319 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 87152860 1250 87151610 87151619
    0x109030b1306180614070504080601090509010605060a030506010305060f06040603091a010e040506010806150103020703030b040204092304110603070c0b0f01030605150a1203020309041103070219080301 89
    0x200211507200503035400f500d80c250304140311241c04092000d07038801d00700004c6031301800c90040510701005040806102003040148002040001c40b241150a1080042900c1ea00d900d84240501929030121790015004201180c41c07942580003980f284030280d030100110340c0e42c00704202c1040e014100490b004078082009021241c407a8106c446401d0003210340340c907641180802408412001d9105440400b0303401c0500080000a0040300c1c010700841c0b009080ba0300300000c0d034180380046203d146060590018150b130415020f80c10408006900420854a40c1d40c1c80c40c0480207000c0c10041c1e80b82030900c0b00c2d1210004600f0301e9103e4011600042c00700c461449803030601246501c080c16450034416141150400901d43c0301c03070b513446424012a008400e51440c6400009c2e664007a2a02d02c50044c001204062a120800003800f207907907441a441d41c00f0240e02f811307401c43c40f07000490344d005070070006242a0090044011802061250b0840d502005080d01c00103203a0808000100002e504000401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 87154110 1250 87152860 87152881
    0x30f0c0311030112020a0f06030506150702031c0c061a04150f0b0c0f010513031715091f150e100905060702040e010c0201140709060203120702070b0a110c0109030b 72
    0x1130380b001d00701c1a1243d807666451011503145a104500080c1c0383c2040001170b04120b545d4039102c40700700b0112401c1c1136056002035110200e0700c02c5410744140c0e0740901032038103100e1030940c240c840d000f60041103581b4041d209215141401c07000503009500300003880700100d107051598400c0705d03e0310000001503400d2803426031599001085150351340c45995624000c4a03801e00c50140904400410600481e095240162854000d02500c075041d02c1d10780f003040009030700b12004402034881210840400e0340c50620b100b41680a80f142ca0300b00c08005c0d0f07000300e00014504441c03100c0140d5603c0c0c03000080c8046080080b521100c081180c00103181e50810085410420042c18003548010300102e003401c14031120500711042440b010005030b440b4a03500c0024240400040d42205a9182c510b10040c10200060743c0ca110f0001900198036103400041c00c898030910407407000e45090315086503120203030840140310300480d400000c0203005602060900350b018030400310407242d01c0204e2030700c0e5694004444 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 87155360 1250 87154110 87154139
    0xc05090604090203030c03210c0703030b03030c0109030207050405100602100f14040b040c08010e0c012d0206100f12020906030109020604090212010909050a02090c09060703030f0c03110301 83
    0x80c1c009481d041c80000580d020b1014103003200040c0001c644030640d8140d164100c182c49a1082c092035203210a0240000b1030400722096282c150502041ca84100000310b49940715682942c0003d51902d000308040540c0840d000301124401c490501854540d0300781d0400340f8440e4411a000340c1d1043e0b910220100c1640c010b03840e0f03041d01440c0010380c10760040d08004403090480302101c40e0701e4180c0c00c0008018402c0c10080141c840d00d0b00800601000d10441e964132003001c0e503842c0c14051001031950320343c85080c1a0040c0303117a0303040303807d101c4841418001e0742c2c40c4425586d8241c001c80162010510480c20006070044440c0c8400e90070220926400344010032034007811250705552560a02000350700c6d10b03030041c80101078920b00141d8400d58003c550790054010303044030031040e04000c0e0440c0071500002e0401d103001e404481c011b0040d04c84060070b0075030744940714610360890b001007050414107416500a40d0300000b078510074400700c290582e0440480d03a400c000782110100a1005018840066800b1f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 87156610 1250 87155360 87155371
    0x80405030408030d05041506030503030a090203101b170606030c0d1407111203100302041d0d050a09060503190b01020309150403020109050d11010302250b220c0509 72
    0x1581d00d0651911981815580910440c1c42072644450030f201c20080f080f04940290202d40800b00001411907485a4030f9100c05403030038803110f494415074020365400f800a44000714140d01e0800c68050540381001841d45903403407070004560203158655051108250181c82154001c100134074540d540241034100b0b8200c072641046040c0d03903450151400d0303000035040d8045c840c00e4555402e294a5010b005150031400c28656444480c10310038081c100c8281d08004058030341c112004900401c110080781c03501d0b0152445580540b040c50541036409412200805480d0407039902c401c54682c03111801d40d4a48802c0e43d61110084c0415080d0500101d29032100e4580c840510607245401d881c2c01c005440d4964010042d0b0401600043c2001190307040f00964000303207010ba55080c41c0e42116201c040f0703919200c40b10705051640008080e40754600c10800800000e44a8400e200074480701d00301000441004c8805031a0028201d40c01d00022001d0300c110b07a0400c1d0f2101d0210140b0341400140311041038041c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 87157860 1250 87156610 87156613
    0xa02060a050435070602030304140a0203030706050f060609090a0911191d07050a0f09090509030901080705090d03030e070803030c0316030207030804060c0915050c0c06160201080405 80
    0x80071420300c10107003c00f1030071122000a14080340c4101c10800748003084119000b43c0d41d0081400304640c603004400e0303a0340580c004504041c03803111042c05504008810700001d5140c000061102c040010b60b500660003000110081401580c0700e45c00e000007440b503c5501903000b4080000500340c45101d40113141c00310312031200f03402158001004641c03a2030018084401009121000344441c02442c2da4448000d200c0070005801804c00346000f800074821606483e082017040fa1001749801d00070b210f4800140314680782000b65290070b2400c0c5890b5003200700b2260008000c440070400e040d21650944d1440c500013031640c60031154640d410340003404542c154000e1405100000245128203001542c89408020002a941c0c03a1400c0b41c459030401c42503084007854410300000c07000c00d500030030a40c0d10a41c00103000980803c000b00c103940900c5680c0c481c0200e2038400242c0c10032036601001411405e0039038012613018182c0740b41040420700a10015180c5800040f002002542c40b450304140c116014a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 87159110 1250 87157860 87157867
    0x60702031606050903060f010e0f040503190c11040603080d2705010506010f11060a18020a0b0d0c030b13020f0d06060215131220030310030204060e0103050a02060a05 73
    0x10501d850a0441d80500046000401d082480d401c060000541c01a00408000d040398144a113011241c0030150021070030038805800602004404c100302e0300440682d81c607003503118582200042c0100d1302000700719080245442c81c0005800e042c0507600c00d4a40c050000d41c18444c03250303901c0e8000c20080444c0400103c81c48100d00c0d124008070600038500d400b81c000441c0500c0c05200161005024145030700410201140005103c4008904240c000c000c1140101d2030840090000c49071030303043c08000e58000b001d0f980000351403594800504100c1c841007001d000d40c100c1d00c0c2013076045900c003503031103038121039055403480c512040d0354000c00744205012030203400c19140200c04400c50f1050f0b0464009680007400303001d00c01d0041410765034480a00140b030b00c503160b525a6003158510403071040000384040c0d88408148420304d01110041d0b000c0c081c046036140d00d0101c0d09462004002d100980c003c92a020300800c211a201300c000341642c0c0c0081c000d080c0611141c1c01e100d41940320360f03484800c0180a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 87160360 1250 87159110 87159133
    0x907091107080f0414060304050d12140f090601060e0a05090403030204120f061413060506030304120605010f06020a0206040e06041401090911060301060f0507060608030f04061b0f0206070203 84
    0x103030180c8a19900764030540d440301d003017a00b046404e10a4844003440313000e0510400001400016003480c500125142c452410f9606081000152003060009020300130480100034085520080c01e512403480c15007201d400da6a0b4000c19180d0441004420344c000d440d0007003d2025007403e0080d01d41085c8a841c00500d410354900202101001102d4202e074121340c030350824006d1024500407410808440400180a418000c0250702c071900c4050f40108101c1d100c0002501a0b83d041c01a240103203103120b1480010591440c0c59001400b007401498100e05054601180c807601c0001d01e044100c2d0701a200501c0d10703003448217009560100800b40c590040d1154011180c450401100f14001c285105012400014629042c080340c41c42500c541e02402017840100f03e039036403251034003400c000d1504005543e844241001000fa00340d94000750050701c070009094038110ec06c83c0050086a81da50303035100d01e81d174880107483c0b00170b618035a02034600c45c0d085603400b01500c0c085001744020342c401011104000c407007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 87161610 1250 87160360 87160373
    0x5030c010c17060a050d061a03030c0f010e0c010903200d080a021e070b09010302070807030c021507080405040c030f1a040f0e210706060e0106030c05030907091107 72
    0x51200344002441d15811030a100c6074108090341002d411110040139504190119182034039200d405840c00d40c49146003200703100824001c3da0304081c00b41c1582d685060000a0701c0d500d018415502e08203610f02100030005d11b401142c1000c2e4288140e481390505891600c485d043ca102c490b07a4aa42024481c3d0880041d075a141c0e81180c201e44200f01a903140c886110005e0300700a20f00306103403c0b11001040000b02034001060b14016680300300b080c0f94480a0100c0100e00034018014001c000e480e000440200749500320080540e4140308035280b0b120094014294510380c010804000c1c214a0140000d00051600f900004036602092800081101c00001b155060740c80303080c03400e0300c9081c140c0005411414140189070980079000e40600c41e903070442e004141e85450445c0030480700c16412054017031240b0300034102c03070030907400203c280051511350b080c013501e558080c03180f10f003c245054404400d0900403001d80c2c2c130500359034014046882c58030801c1c402400d017600548040311010403841c00010072 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 87162860 1250 87161610 87161621
    0x30504021f030f141506030901091505010509310201121a0306010819020f1c0501020d050708130f02060f0c0109060c02010b060d020d09060e0a23150405030c01 70
    0x503658085554080101c180c0c0840f40d00c0c80ca030310304408801040102030986100c40c49688581606c0040c0c2da66104d0801d40d0040c2220311300205104654040e101711314809800c014160741c130445400246844200c0b0784181c0724140f900c070a9251040d01d0f04010b900541034400c00e4814010b05001d60410f00d411074040c115005140c3c01110b1110301c4849009505040119030702410a400c0100070b002500e400720001c0222200001744681c9043c240c0d034080d6100e4401c959412144400c0c06030741400c507490014007070340000316a4a142407400000800c2280302d4511903000d10b0ac0d540c169540c0b0411921b5240d43e0281401050360000710410204441e0700380840102110701c02c08000007140c050b5881c04509861500e0340040c1103a041101500c01c1d40d0f6010f04130fa051204901d00140c1d218040e0030f000025054108014020a19051a5688041c4045000144144a2607103810454400c25601281042422400c40b0300d6101841080d600800b071030707407690064050310845e41055075200c0c0c040d09460303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 87164110 1250 87162860 87162919
    0xc170903070b0106050c0a110409120f0212040b040e090a0b130309080a080a0804060b0405040f0201120c08070c03031d1f0c050913020d050c0c0f070b070303050402 72
    0x2480011030100b442010071565015000d20314000749014280c03840e19030f43d2060900080c1000d0368241c000303031442c2e0b03c0d588110b130800d40c061080c50356142d810001609170b9400a00c21030250080314504a40c4c0600402114144c414940e8140d081c01c0c106800c1d004c3c03100004015059522800b00e09070080b690b400c040510030740c50311813040c200308541d250013480c0d00034a5000c9a440c1d0b02c1300403000c00050500c800d80c2d041c0070441c5801c1501d65103c3c14684054881103100e10b8006151000b0b000601801100c80403003075000381c8503403140c484071071408030844e07503403500c003500040441c404186124440c48611900501038500032680e2800309152514a82c000c100d00c401c0c2e07501c21101d5041011030350101c072240007840e080400544144050141403072040780c01c451f02c21402800c50f4206690286c0c1520345010244030204170a00c3e01c81420754a903130141280d55958440c08600b810f5424000807450280c0705244062400d0914940c0c0139805443c003d40100d9201941c081480e03043c0070781c800310392043c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 87165360 1250 87164110 87164113
    0x6140c03070c230102010b0604031214030901050a1a010801060305270705040c08071d040e0d1805040902130510030f0602070201030b0d0228080d02031305060304150c1709 75
    0x842c3d401240e00d8908040d02840750640e410100c20700031710360350441a034085a4210b4040c541c140888541201c4003501021818046c000c0442400360340c0a0540c4000d104940c80401000501c805076001344d51481d0b81145540040c10b40b0005100e428825005140c1042c08824685040211441e800c0320031106881c04400c03036800341200b0442450903000f240c10000035414254420b0401100003001c00520030800c041d00750703058a145680761110381c04032901244101c19200c42e1010040c00900e50f414121a0783e40c034421404012a2501e0903102c1d110100b035001b00b28040e030703a11010407403021b081e008001a000c07203000c65000010070704800c01e00e0282842200010780e202c8051001508403500b0b0480c16014041300d0841c07030016119445801c1442c01000503a00320042001461215005a500000020300440c40200c0706960004040c0007008005488069002d89440510140f070108480150402007c4140c0c5000109030ba8061904072405241000400315003800708503c0074404d84080000707 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 87166610 1250 87165360 87165389
    0x14040b0d09050c040608120708090604060c1407180f0b0406060206040615060804020d050705100903020405090d090614090306100e060a08060c0c0106031506060206070906140c03070c 80
    0x700304040c040c3c1d509160080701c0420105040207803482c0d5a0700c5c12001c0c08041100014803105014040040e600d40900042020303944a8840c907008007514180d1900300c41c520070030f0020820011021480b0320070f0346d144088226400b950341d0102c001408007c0030540c00701f0740e50f000c0aa40c0e03496a01812003e003845400070802c82c00c15243c010100d50b61200904951230803020103000a0b0743c0807031010381083c0c0441d0301040c0300000d403c5c0641004015444280c0c401c0910340d15040094000340544c049a000700e82c100001c1c0e0314118155150000c03440e440c00040c50007201400410b001b8800f0031400e0140f21b4040e030074901450301292502109884001040c01074080402c0242108401a41e0003030060f00d07002c054a00e003454196448030003600c03404c154031002c980880c6102d4258000740c01580c0240384800106e4440b1030700c01c005c103214080c06d0014010304001420883c0200d40780700450f140360340e0710800090030099040198101d0300100416010070480240030900c003228038401362012404038040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 87167860 1250 87166610 87166613
    0x60304030f08010b0a0203030402090a0f050103112706060a0504090c020102130503010b010f081504090b060306010812030c071103030d0c020d0e0a0e0702010905162105060714040b0d09 81
    0x30b8820507404040780003000c1000151290340030056a400c44d40c159111b62450700e0310031424001e003d4100b15203448601e0100000180403240b1401083c00c0425141c0305071041050050441c3d4034002e85101d190365000340701040351418140020289c59895181c058141500c5807070420688002110070700040c0e40205554402c000c6a212902c01484118002c00c441160030300041c00d109001c4441d001405910000102d0000642000065400d07000b4401c002c070880d00e02e00114010300989009020344913200c004624048005480103041a900d900315040d95550307074080c0485e84c00b2200c05c98002c1d890042440550306e04002a042d12001684007140b00003990000a15245200d040c030000c00c0607074441c440749c0751120302404042c0d031410641341c04165200c0c00140d01520514400800a11409243c0d41100b44003c03416802e42c0c5041120b04045944501c1014011400a4003d45550008030210b04414050060002d11300000e203aa1400d2540d075100101c41500411283d407001500c807041e050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 87169110 1250 87167860 87167867
    0xd0803040b040506131a060604090c052106060403060902030703020a06020606040c0305150607020a080a031107060906270e1e01050301050c0403170409051006030e0a151109060304030f 81
    0x2580003481d5010503504640e152110340c20a1011b000000c0300440100c04103415841c7c4c0d03000c9038050300500c4024403030900f50050080c20341e8042d62511a00a403d00d406174080d000300300509004240080003103003820b0460b122540213200c8004200d902d485070070000801a00c070240100014101900500042e02d404001e1009031034461032001c1c10549030000f041090381200d555020940c90a41c4d00035280c6115201252451015820404091046900100030564400202d1400e002c1c6a82591380f40760f51400d0540f1200c070b45024680204180c05101030b0130903941c0040d0b010185901c5240f0026070341e41c0c4c4600f51000c5050702d400c80e24003802d807280784c2200b6101d0b040700e0041130184c00070030441c505550701e1140360089001c020201381d00100b0318049c07190f90800740c50107000c40940c00c002e03034188910740019001c92031141a002c00d040ca002803c003503001140c40c0309643d800c400100940c0700c1e000d03500d0000f4400f005d8403454625007806980f5031901c4a00140d48507910030b444221074043c0e1420080c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 87170360 1250 87169110 87169123
    0x31506040b040c020d0507020321030103030f0c0f020d05100608010516020705030a03030c20070302040509010b09041202120d06060206010f0303020a03080612010c0309150b060f03060d0803040b0405 87
    0x5000c2c030705007441d01c1d152580c0001c0e41c181150070f0380f4021307848680502c000781c201144034000401c5240b44000710010040d6410086048900c070b529400019260140165451480040098001080c8001d450050b051514a000005c1d01c19416102d07028109242c000c11074006c0d40101036580e54400421910b02807120036146505140d000500b4814a442c0000c0c0d40c3d2645008007e04250308c031860b81300030381c3c0a052034211108080890340903612006d0b410a03a00c400c40e01c8103a100c1c50402c0c011880b924410300c161310000c2c1e0040c00036519507860b5103c1498030201c035020141144500f640d9003c07034007a80c001608584c1e040d02d0003c00d00c00c2c504800285030400682007000610484081000020340000e0b6224030b07e989410944100d684900018150103a4000c2510340b95081c020f1190306547d06601096880f882520034201c043c00c00b000300c400f03c1d20742003c8541c100d0740c204002040020140007555003c20001c0500d094180c00b541d40450303176007050740c04071401620041440200316003405803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 87171610 1250 87170360 87170381
    0xf0411060c030301051005070506090d1e050d0e07080a080301031b0b0d0905070302150703110105010f14060d2c0a02060901030905071502030405040506030c03060118060503150604 79
    0x9040241c400d0100d92288810304c0798078461140440305130802c41c060015124070541103401e031240c0e8507080035160b85940c2d62555840006000782d140780120498100e00903030b010703620341d0f8150501660640c2e9000511b400e801c11300103032080007000504000100642060907100e01c80c0765032039501d54a00362000b89180189225401c541d240240445a0341100b0369040c1c468200000c2850310b09424114100511604060f4100a4407180031105000c1000100000c0f40b213941c0d6040082a1882032030300b01d500a0180750001d8140c10002c0101e0620000c40040850307008101a18118103000d080049801d031200003110108100710883e00c030000750f045441030340c4003c0e01070400c0b006a580064980d203d01c0402c903040c075590300e50080030f1207010800040540200b11031030502d84d24440010359650400c0c1b003164441e606110008650b810f0218001007010400350040040340d0810545244100c0c0c001c032056684ca1303580400103200e0f9010403410a86044030312401134503040c000709020030355102c20503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 87172860 1250 87171610 87171619
    0x30c030613021903080a05090310060305070b0a02010e010204090b030f0c060d02071104290a050901091d0a060c0318020f09071b12080f220309030b0f0411 68
    0xc01807500d01c00001046030590444400082c54106840d0801c5080242c10140c40040d02140e4100302c90f070403400a00c5460000c804607102640d040150a041d89d41c2404010312035000304404228520154015005601e40c0b4000451010a08070680d800c9812940c40360249035124030b014075844c1424000c440440809002403c0d40490304000310344075102e946201d400566001a00e078081c4004400707000c1d00303980002c205000b01c41e240b090010510245245003c9081a210140407143c82c00c0d05203042200c038042e041680e180c0c40e068030000106100b03140648000c515648810701c0c41000d0100c00d000038841c52000501d1554464014220703401e0105001915458817001405603407413841141448030110795104091f550072408440c0c81c00030550748200040b0701200d20003004011840c09902c080c031030f13a4441e0705a0b5041c03415186141c00340e074480b404407140b0302a9800c1d041c10a804009071382c041c1c101010410b650382d84d000305100c0100d82c201900c0c18180140000c0200c001c480d013041c07000849 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 87174110 1250 87172860 87172873
    0x41509050702030a051611060d06090b06070f022b0c060e060301120b0c16050105010305010b0d020a0e07020309060304060c030e01060515070c0b0f0301090f09030e2e020c030c03 78
    0x3d01074402e2140d40140d0320043e5940c1b42e020100600c0052400d031912014240c00d4030703940454011005061300e401361800321800c104860540b803c010083d20080c542185031240c2d00d1900c2d80901000b00350040c0c0d07604e01240201404840112207202e42a8043e2040c2030034400d0b5850450700501e5100011031103481940100010400c00545900c0e00c60102e800064240386a00e420300d80e000d031032140707449401d806000c58008a080c810190300050480740210300912011101100700024a407000070000d42c003032034008040c000304c143e101e051940001c0500480389014048400591560022241210065143c0d01000c1d07100c0d9040c003500015041e80d0000340001c904000000b41c0d02110001c18003100c6401003030385002e220346c4110210041c40c0041c0010355800c21242401c800d40c3c0b0074000c4117801410076a4241c0d0482942c03144401e80354160341c980d8018009c12007085506401368a0320801c178040f804641884224810590140366011303001418100c505d04140350901c102011268401e410a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 87175360 1250 87174110 87174127
    0x3120e0d020f04051519030c14180a060b03041415040b2418010608070801030807021c05160614040f0509040206120c0d051812031504150905070203 65
    0x1c410221a030443d000714155943c60341d40f140c6150700d03103000c581c05110072004000c125048001e80c003c0d64020b600200566450b074001c0500c1000480ea100d4000d51030a2038544020b00c9015040c2d00251098400b144041e03841d00c500c40541c20907a000c1d02e40d9548605241d5001c40c041000d00c00140c00b1a9071400c0500d41a1141160208028145030411654004001c204800344071142080c18005180a03800d40328440170b00b0549109011b900301045140d000f0410403409030824a04803075000c403400303103068015420300c1400d0015080c910103904000c1140c1340002e8007408120518094010941d5046140610003400c001601c1c091008002c02040240100c50858200000343c07101900c52412503103452001c1107092082424010150300c00c0002d0105002142d0028040020440360130302c4183c0b00c054010030307210742c900c035040081c0d4041d07203480c00444100350107103a005990000c20140500f074400850140e800640c074200305110031200c144a44403191140ca0f0700030200388011400c10602 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 87176610 1250 87175360 87175369
    0x1e0909050c1c0b0a02040e10080a03180308070506040204060b0c070323060702010e1e0307060b060904020d02030405011107050a030c02130204090b100513061206030c03120e0d02 78
    0x61040034020310310440070700030240c46500741014031a80110b0340340561804102d003200a404c5070081100c3c145008021403000c00550900c08203035040007000d8000d8842baa079007500e0f101ca4044040344840c0c107608000000c5070f00c10001e0121140244054410b84c03425104000840f0455003007580c8180382400b210f4102070700015024180d03030344005041c040c126001300c00700c0706600b02004862944075001c2013014032581034000c50011000881190300d0400c48000180300030920014014181e0320610035200480c41d1900f048141c000060042d51070003599901240c1031b07a100c1c104c245a500d8000042c04104036091207a844100e010a84003801c1c445a40e079199102e1604881c0501044a04822201550785482c01c640443c00c02d80c100b10358a035a5019101e000d0b000891000e44150086401c0300c2c442c0340514100e030310603202c41c2c02d171581c1c1505050050390102220018080c03007607551500440010240d0050f00091402450b1411a02020185c01014542c0004040b40108641e008941c01a1074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 87177860 1250 87176610 87176623
    0x21201051311030307050118060b030304060f05030601090506040801140f0919030e03070905010503150108030d090c1d01050901140d020103020702060d0507050901020709050c18060d061e090905 85
    0x24080c4094014010a0002070700e18090701c20050b101f5440c0c031203084596090b8110a0440a00c1001e051256103060820562680518865030000c40c2c0046010403031684144011036100405040034841d460319000071880a81041c0c215071442d81d55000542e0120b0060009554405804540300510340307812078103030381c68481d030784591046490070b80c1c401000c1600400c208014a0400350845540c2a950030500000d0b210a200700c038000d00440c506441c0c1c1b4090f5030102ea05a80018000b5031400c500f034005100100340c0c880081d03900342c0038103602081041d403408291a05c407240803000d40c281d504082c10024450810f920103424103208008500741504c81141044c119502424016100d20319800401d01c01e20840031201c40461a080030030052035080006045807050aa084640c49500d550742c0704100c9005a807100b04458062102d0410100c661000c12840140034050905190300c3ea41035109941868001c06065440181e0718001d008210348500020881d041040c0074000d896116075884c1c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 87179110 1250 87177860 87177863
    0x307020f010e03090910030f1a06041a0f010c0c09022a0616030207020603040c080f07050d08030c12090606010e0103060303050a0e0406050a060201050a050105040509031209280212010513 82
    0xd85c04001550b01d40700e07116035100440e004514054901c0c0c00b8034122620320724034100e000c1181e221001046003402c06120310005060381c083c1c2d074600b14000000700245e81c0070f0400043d04200300c1040c4180020014166540202405c210250b02c0350741c2d24250b0011040007040403808a01d00e03400f40703280c402c4001030483d04890f4141044034a40344505084010788039404010350402000400d00c800c21849070390210440d4465400d60f911058000031041d1941c00c0d92161507800740700d040034400840c03d0400299080381c0002d801c0340c50711440241200020800b158110503940200c01081025604a41c007403000101c01d02c2d04008003404c5641c05000d6010304002d52041010410303104440d5100e680c071090242200914891b070555440d0300c0203010340403c4038441c280c142082c0000840342410b010b440e0090780c00030b02460505d050f407100c005a80600404820040c4120104842807890800c414030b45802c0d6680801000c0b10280103200c41d40e17118488071006607240c801000013051007401c003280d455 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 87180360 1250 87179110 87179119
    0xc07080a110309100c0b0f010b0d0b031603030f11031e09130608031b010c05030c030c12011202210d1413090b03060a06050114030a09050f01020307020f010e0309 71
    0x2024420710700e580100045150801c540d203540800c1c0d5130f0081c8085072124442c07080b06140340c1c1c42004440a6140a03c9901c49007901404520b6040b034040c3c0010106000140c101c9003613001100710044030b400340d54410f40210350005501c2e080c4580c070032188650014035400542c40c0400300100c82d80064141c00e00021000000300b1030309801e50b22035040d07204034446000e003409041d450b101c2c40d940325444074010a0349189018100904428180981545031840da1a00f030305640d20078100e40e603107500c000d02101041108001c8011001c0340040214003900100d81d0a840e869000c0c4180701d60700340e007841108211110004070000400c0001a142c4140c2c00510340059606980c012001c180d000707803030b00c0e0070b54844025400b00e0120303400d0740035140f482021411a0115150301c1120300855a190003482d0020b41e1104a450300280f87c1402141c000203500e41c00201100700d48c60b29820460808200c18440e5000000c0c00390955041120201d03c00641008218641c2c0500300c0c9640c81c8610b03c02c241c0035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 87181610 1250 87180360 87180377
    0x153201030b0c1201052709010204140f090708060a03140d030c0e1e121504060b010503090a080f07061e050601180509270c010207060c02010e0d0510090b0f0c07080a 72
    0x40c0342c6d422248448601c541c605c0340340d42c1005c4107814040e4029001c4c0c400500004500700182d46000b5105505520026000c82e0140e00c6542d011a080b12008101b243c1020050000000194201500500014066000c0d11030300030521001815100d2400346d190802126014514203a9210b10350b0168070501d0902801c07603403e480300402c07910100e8000b808070f00d0281044000b001d044041c220f900c950b1240c5800c200149440c1c0065036140020307244039405a012012050020b1411001000c103044104407042c1415117691b5010305851080c1501035142100b0b00710100400103500442d50800b5003401d089081d070668004c600d1031602a84162449a0310020100383d0318440d941010807980400c2d03002408500f0b04501c813070b503034a04580761240140f1900b840043c034a03100303005800580d54144c0d40e00d1a40b00c2c140041050303c1740b241d802036031540540e00301100c030036505100d0303884c0c254490160444649441503074403200103002050741d030a4035004c002c40f0000640010407181e543c001c03402c107242c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 87182860 1250 87181610 87181639
    0x3100902010332070203070b0c0a0315080c04062309060f0301050108030a2606130f1d0606100c030809010603080d14060409153201030b0c120105 64
    0x41c00c0542180b840480d11199040040020a1407030035508180d5101c2c3c0d8095107504000326928070030184060728030f805840c04203820604504c01042c0014043c9000301e180306800c5103d5240c200d441d40201050b80c01020701c42c0b03041c1854098100100400c1051010542030350003002003910540c02807900c41e554620010b02c0d50790342c03c0b80d0441542d2000d0000c101035a111160360b036496000904c14000f003100280000283d05c00c000122604110400a46200e03488003014461200369198891210680b02c21003940d544540b03105540d008020003001c07108000e178020501c0e051031001f0f852180030701203900400b004290410242c03004030f9407503d0b240c0d43c50741d82c40744581c2c0100641e800081c8040c10020b5400181d0410f40c0001111007091382224556031649003c1000b2160b0052000703144c03407840007440201048a502003101041e5003050301a022000c19603420100d401015213040e002000c81c01401030144014070150300c0403010307102c03a1504100c00b0480140305014401c43d4812950002e1054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 87184110 1250 87182860 87182867
    0x9050a0e0609071a25060603140a11060313050115050406080102040e06010e031609050403110d0909050a02040504050c07030816090506090d0f050124030804180908071505070504050310090201 84
    0x4150104610b4200341740c030589000d1010705024401550030303420020401c0380d071300804208141120fa200c0420060249507806220381ca800c020070034116031220070f50040100e1400e0143c0e141c401210019610441e041904000844195400c00e8509078418030041c440800c04100d442d810aa0908004030b880340c1c1c002c0001e18200c104039012490b282000400030b6104007503081140150310940703440e4412010030308490b545111181703400e00050210b160804c00000143e100580040d140701e03015241a485602140907540155800c0c0a24100040d0100501da840502a904901d81c5001410303060285580182440603a0042ca8480d02c0c001596051907641e4208510145500105a05111500d0b04003a8000c0824006081c84403488500309c032041c43c01003c44c1c1c0252680090054207280c1032822228050f540180524000356480c58072002081c0c204c0064200c141c490b45001143e403213101c3e00700381501e0000d0f0502003441414041448259000310b02c550309036001a00c0007d2801c01c600049 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 87185360 1250 87184110 87184147
    0x32003030702030d0203130b03090a110102010b031603061a061801050d1d010c0207081e07030206040e180a0c150306090204090f051501020307031809050a0e0609071a 73
    0x3540342c4035010860803807580200142900e00c0c445071f44a06050b0384c0346160178951008032030b00503d42d0001d41d03641c000a0b803060390422281406200018a00401d0408203240125040007980007002a4404104210540c001d80400c400c500c8150003004c0b280b580428014000c0100e500c00c9000803a000901d03591103402900d000442111341844003203060381c00404010103034010304100b075003850b5225910a000040c070104032104c24000300b40614404508031580e840c000c1d01003100f070142d0381001002d13903940c0000d4006046d02d211044220300300044100c5c08003001808080c9581c1281381c0311001b064005e16480204c0d085840c07002c07004a1503580490082c0844d4200010451001c030f07002c030307480c44582c0c04450b9032900c1d0101000607071120920124a901d1009030390b4010381c003c100c0300d4002071060b1041403245481a4090b481541c41c0c031004400da4030300725200c0c200299200d1000c500182c0400209400008250140c843d0508000d0351080015a0b11101c0442078000a84038610202d40b1121 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 87186610 1250 87185360 87185363
    0xc010c02060318070605040312080910090809120c010f030902030c010f020c0d060c0e010207121b0e0403021b060702011e1206030c030201140f190507021206010608100320030307 78
    0x380c51455480d6840a040c903001fa0006841c008210380e041e1914901034003d2074040d50301d01009140343c0c034048044c03a010b481e13801c0080f24000024040d100701a100c684121b042401d11a020f000d07240101000100030031a90f00b0031070101410f141e8400c1c0582c4011901c4250b01c44203282074081d04001040a92a218080500c42d0700030b6104020b01c402d22245600007110054030785ea59640c3c00e50700c1c000480c0e680300c250264000100f90a03500c2130000b0307121026200b5100d810002c2110a540e10351000e41600b00884003600903030040d500348000241a0000d40990444c2101c160707050040790780009141480d000070320446615030411041855024000e941c90030f0788841014480c4503140d1a1aa4014103a031004901080e130440090000a00b0f01050f80c04984191580340d0030191111403424444100c00760000c1407200403c140400340c3c9800311410381400c4000e00030160765240100080641000070002410104208024400103a5102c0d40c803440110071500310800311701950020742948101e650 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 87187860 1250 87186610 87186613
    0x809010815120705040e030c0601050f040917040302090112081204030e030f030706050106050415080712052a09010c06050903040b0c0706030b031506090a0e0d030603140c010c02060318 81
    0xa10000c1c040d000542002540c4c000d031814040d5404d00b614860303580c095080d5844139074000304010301940c1400c2100c1c44114800030004590b900e0103403280c4040400e00c85403030905500014050040d03042200c403c6006204c0c00e00000740314050350300c5500440c0640e140505134100c80e9404101854401c507545861410020107445800c01343c0e0180e2030790b940c0026000c917040c9042a00000304140038406a40c200c0344450b0000c900740c6030280040341c100d04014000b0f0f040c000c0c41510441c6400e00c078800c0382d02c960b42c3d01e851100da02c0320a4490011000c20200c5501c02c1e41001c01c0440c6659920040d541000c0f580301001003040c2e182e5040f0b650448c00340c1e8200308030f07100d808213440040000000b101801c07180350391420000b5442c540c003072503100c010303194510700c0084000000c80c0881c1085100750380c1c80011039000007520740381c0554890130000e001e02da403c006a180d000c2070040c404200f0f010f94440030b01d00c008141c1410010000f0384202c140c2d50000e8030404000c400603610b41c55100340700b03910035901b40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 87189110 1250 87187860 87187879
    0x12020904050f03030c2508041715070f0e0d020a1505041205060105120303040c170a0609110f040203060a0b07140601060f0e090405100c03020c01020d061409040809010815 75
    0x50300750b2203503006030603002c109040010041c0c82400303c810f101031040d50022038040c030b41401c1001410b842c5c10102c070b60000754400d220301c0c00000488168ac9038007501c195611040114801c3c840101b0070041c0c40c5225100e01d003001018070040e5180d0406100b00c400c4868000018108000180d5050080c0c3c1e0105d01d01441d030700c40940030094040740c424180c0300100c82510b0f400f00038455050f56400100c030002d2004100c00418001401c080c10501c5603a0003600840c1c60b584507507610f02082d04c40083e001c844034a10101c42d145c4924020440c804250003d07a41103081d40707020300c00140705944520035180c4001c00080c404081c0000380c0114000d08165204403030b071559480342c0013005108002281c800040401521180d07901c0c1c150b050501541c3c001006040000c07190b180000100b0000034610141a0700304400c41441400b80040d1100824010000039400d1a04810003682c1404004031440f85520b00100000034003200240d803a0304400b17181c4038915550340a6541001408001110f80c06010711 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 87190360 1250 87189110 87189121
    0x503030114120d0206040f11060d06030c091a0607050102070f050c04050a0b0d0308100504060608061311040b03060103060b03131218171c080a0606080112020904050f0303 75
    0x125400c141c110700503a030700c1d801d03120403401d0581c0366548802c408006030441408074001c070b1019031284079014010844603000d100f070800028441c1d4000f002e600346094684200300144141c4242700e400400c5090301c00d2042030404001048064034007002544200b0f4041802400d1050943c1a075080741c2d8072036a80440310400b41041ca54402240ea1040c1c42942840d0000c0c0c0d4500e8640260401d40e540038004011a08066800351100c0000030f007540c0380280070b25000195a599406440c000785203c3e181c1200b00e05019041c420400300d00d400d02144603050451035443c1d00c11043c1203404072291414030a85a03210b0400480c00341511b6030100c9803d550210500c0746102c003102441d202c80c0c0c42080b60640115849400395000e440c4e8130300707100e881440b4607000c01c0020446454400d130050000150b80d0845240f40e101c0e1450848107002d000011030701410001601914890b4034098009400c00c075081d5854410104d8041c01c189a00901451001000c10101300040020751641040101902d0300e070710b0310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 87191610 1250 87190360 87190379
    0xf1e1e01031b080c1503092d0705240a050706020a0f02100504021e0d12090810050f0106030908070609030f030b0d020a030f0c150512011e140303040305030301 70
    0x851a001c00340110800d000550100700181520340e4010182240c0400140504005c0080c1c100800000541c0294500518a04400c0007150000542060400380012a40d0003a510700030442e00094090f0054480d02d292034000c103403903200705c07003145240c2550b10013400c0b408a03220b019102009211a0001c10034a500b140c101d228507090104582c2111400c80710710080205070b03a4142c1c1d000e900b00d01c1082408444800005801c12504005031103e01c20b612607503100881c080040350380d034000440104003808841030a01032001030542e0300c80148000d04010361520724026061040c0b03018955100403c208111144041d1860f6503004441081101100d060180540e400e1410b140c0c0064648058000e451030521000000c0e150003a0489042e9030540e980c00ba507145600340f00703540c06042d0500029801c80c3c100140e4402e8009030340c0b059102d440407002082c0d80709041c0c004210101540324900c02410250810200b1119000c03030400c07107010118080303400d610650304080d10901000001040c0f0b800c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 87192860 1250 87191610 87191633
    0x90f0506090d08070203030402010e130204050a0801020405040c02060f010504090c031a15010f09090902010507080703030b15040e070e04270203070806060604090b0616050607080f1e1e0103 83
    0xc1c1d180d02125139140c0714120303242d00c01120000e0202d0b104041c040c00d80c4c00c00300c180080d900194880145040e8a0342e001425210035903002a40b141c2d000070703041c011810940140710402d42d8a00043c6000e08041c80e4030ba0000c001401403d000725038402c154400d0101c0c005e075107001981c000c0c11319840c0d01221008411141001c0314840c100b81d1304660300d140c0c154401c8044202a00d043e5461012143c18416164060003079a0b00a82c100001800940049001c40004019162007a100003442c82001e0042c098880d4070700c1c4a46e04240024041003102c104101c5041e03900c2481c500e400d800c001c4521000800800240b4a81c00016409804100181d00c1c0d1100400101e8001c50407241e030141d5810465603201021102d01c0c0c2c101c5001d01042114501c030b50009610460001d00740fa0501d1010445616240381658059800754403c0b41802400d503001581603800c0008501c84071540e00c1c180801d0135003803150000d105603225500001980c03501d48040c00c000e00d5886003030b010000b942e40341440b060506 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 87194110 1250 87192860 87192883
    0x109060606020706020a03050306040219020313050901030809131104090605031002130b0c0a05030712180b180102010e0a0506040309090216060903030b15030a2d090f050609 76
    0x900d425808103400d400060702c601112016402400d011501c1d50f4101c801e030b0005041c4a401903020b00202c085c0c0b50500100400c2824140c1c001c503161005032444076042d0125a00c028011903480006001043d071400c1103504959059030900c801c4c03240310310500d00505907141a44601c075400300c3e020034194a20740042c0101c80045003150f4640c40a010880120f200d410340e5902d00594025040155000c03206c060b00104001d01c003914020fa003180c03078050942d407142c94203c8941c003071b03125045103c640002e01c0300211403912240000075400c166030900d2a115515140242e80b04100781140c030b503031003500080c100302d0260b0140c4aa50b0307011300d04035030348040642d01100818000c54011603204890700c20745842c6402d810040e04440e0701501c685008104070003043d020162112484041c42d12550036074600455511691580c0e440c00d612114116480a010010203e00e44014206c4520b2089541c44c80c035030b07a900000940320302c58986a08004a591802031644c00f43c201003100381c01c40894040f401d00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 87195360 1250 87194110 87194123
    0x170c0a0e06011d0a050f030709090303050709060507030e01050f160507030302011b0905010c15020327010902010c0803090319050904060e091c2a050c01020114040b090a02040507020109 81
    0xf00c1c04103803000301c0302416900c82c0d0f000503509108008520341903e4400701d922001c2d060b1150aa181d054400a1780c0744880d064002c07039144e00c00d00c243e032030307001890b4401805c0f289813181c02c0526603980200002048042d42c3e04112012900210701242d0308203c0c1d0380801851341c8615001154582151507c5a511043d0095403a142e01c1100d8508032040484d080403403a50740e54826401c0200549010801150607141c686481c00380190000d42c620056000c0c40c0c5403401da844012400c01d4181c507001101d040b00d1010303410300c615240141d8003d0740747c80b151a802101107440f60b84526981e840c6000781000e940d40c03410230b000074100c030b29000801001004001c1e0b40511042d0f4546607181742d09002070701d50030041e0303001c1c1c00843c4229035000008100402d40c2e15081c451940c1d107110b442d0381c46020703021244e9401c0031298a08100070007002582a0420280000d10449001e07000400c611600180f0213096a10400f0000d05210070500c402d981c03180e8018020459401d007044000c0c020441c030041150300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 87196610 1250 87195360 87195377
    0x3050613020903100c0c0602040e090708070630180b06040204180207020102150702070e150901060f0c020402030a020705060703110a0c03030b1507120f0207170c0a0e0601 75
    0x5603a0500072550b101070090010600c078103036408010024141c4540050410506144200000e8403500080c0020941031155585138240104013030704041981c3c1c45071080d944040e0080048c20b41003200c1e449440c041d004000d00280c040d10b0141d07503415080a400c1c40d060329000740b40200482c04411040e003980035074000541c1d9503510091008a1240e40581145c080f4030b5460000e4410f050b4004101051041c4151000c04101031200d01d50741d0800e4030b800000d60000c050078050404c0040784a42c1c40742e0780703002402c810f10b0b554002c546001418050f22003004511154090140d001d80b054550865025200310340c0ea15007001410000d410042c0e00f11514028100416201886801485052150230f090503141404540e8240e4000074072600480134141c0302d0242651907540d0441d151020740344404620b95480c00c40c81d0032410701d004401d0480c107000101c040706603010760015540003550801d100040c9404805203482d4600035903003505581c0306100810100d800b207849030b1444d00444003a03c96010703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 87197860 1250 87196610 87196639
    0x4111c06080307060506060904060303080a0b0d0f020f12030309010203010f120302060a0b030f0304030b062b0b250e030105070306030f080a14070f030216060507060507050903010c030506 82
    0x1600e0040c072401c4002e9006011000124015501245d013082c401400ca03072500c91900c000c40c0030380b500c550096010441880400c41862030078000c107400c9050498000d030091140c0c1e80c515403c4a107011029004081207440c003142516503851060b402402481180d841e8078114554034082d42c824060410a05069440000c3c01d00c4134120f1200240d6054025140325507442c1c5204c0d0080940004040c4e0511500010b011003407001d000400185001c1c40d000042071030081d0a0004001104908900005492101d003101030b0206401030300c100c0e80404100810388440c03020101800c02c0d0480c82d044c6001181c0c1e81142d45070450920440349405800a0066a0b2228016802c58020344000f400c281d40d1307191004001218400104420640d9083c03030f4180c564600c41c510b000350800c030007c4543d404000344200c20b054041144050402d41d40a00c0800a070410f20014081c0c001c0c1e801c0209003c0e1142c0c0446d24060213807066415400e80a070080180300490301004010700810750745940109980f4800f0304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 87199110 1250 87197860 87197917
    0x9050706050a0f0305040204110406120605032b05070b070e120f0c010309171b120301051f02150702030d15140603040f020406030c090c181e03020411 66
    0xb0140ca101d43c5641003103207058502503014220040049174815521070041e01d400303107054040d10182c0801c1d0350781440107800b42c3e1004102c1c3c0070b58000920982c0071a00541e41c1e01200301740d2400c11003001940141c910a031840568250140e0400140706544010400c00d442d0703848401e0340c030b40d544122940a0348142e8816801c0c1ca810114a0341603403900300c560801459406a005010342034802e2040748950803841c00c00c2159a04610f1904001060020b140301c1c9070207007040440c0c0c4000b91524454995450b00c000181440c4210f0f2003c200081116081d22842e8000e200a15118580c04110700741840c040100945030742c05280c83d003040628040700802d00c00340000082d401c0d01d0440145c88000280e2404000d02a00001c000300e403001d92005410005864a001302801144100f1061040900300a502400d850120b03403400c007006081201048404590021242140e48201c509483e040c20844a04840007450300f0194025081803da610a44100401080c14203550905060400c2c0c0c405a0756 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 87200360 1250 87199110 87199117
    0xc02010506090f011511010509060403021204050f040f020d05010e0a06060305040b0a2007050a0c0803070c0308090a03080c0601031704060f030b01030e01091208010515030a090302120403060905070605 88
    0x15804501800184058607205c4101e54a010300b40c104802c140d580f9121300c07400c0d2403040314406400d8100400344410581c04021802c0002908031000303043c43c1c1000040307030004240c0641c2520a0f929504d503c0821890345e0304907120130742050b81c24041580c42d200036a010340d81c10350742489920314041c1300040c040d1180c0725150046600524981c6203860785d034a4070b0003921201807601a0451704200b8800201c07864801040301d02e1188000d8035541ca51420401d40200880d031040000f03410401607480040c1001d08013000340d0740e010748003a403101030b041d01044054003143c01c0188070f08000a0403505003040091008d0403240b0828120800400800d041c190502851088501141144c07442100e0765019400010310800d06150015890000402c030500b03440203010143da034411007111841d0328986c0a02823602414050303c007040950280d40d01e43c4030074800240020035003552042403600b050710a20540070041803501041f501c0c2d0ba12400c11074001c081b1040d0440e804d21441c080015a01e0180703040c1d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 87201610 1250 87200360 87200371
    0x601120c02031801020f0a1a0c03060f120c06040909050705060406050d0e01090b0f040b06010e03030d0b04021210090501090b1c03110d050409150f05130b0307090c0201050609 77
    0x1560400c0604480c1e40d41d1480c03c000180e055004403102e2203407010041103e00c800d240a806101c0c4079101c02c1c64001c0300d01c540500301c11507c0004004100980d1540030440b1144007060790014045000310301c90300e0401c0c2e810000207030f000c4800280010300c41c402d9003003924001e01036016200066910010041680700d21710509d80403403c244190326581060f40d11502044410000225640c0c01c0c4d030b52a0b51811104440c80b181050324902030009020f10003101e40d0344040b007820285240540003000035501d0240e40c40c9081b43c1a12030b414515140c1f5140c06a500c00c1e4030440e00760055081c140c0d45010005100e000d02c6100b54075010000407110018080d0744540c20000c4c0c10300d450034008440f901940412028142e080c011100c0c90440614000c10036007000d645c0503075526840340c0c02e0828071815203a030418034641d120100c85060080480a1142e41c044440858241034602e9620303407805c016000b0350403c69494054080b0001d0320742c003d41c1011000444640c0200095035580040045084c4160365 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 87202860 1250 87201610 87201613
    0x40302030c011b02040c031e0605060d020a0212030106031407020604080304060207141f0b0a081005091216020114030f0105060c010902060d140c0307050a050a0903080703080601120c02 81
    0x103100c5480d50207070000440382d40c541d4503c030480094503000300e4142c0711001e421000080c0d8450000c100c242c007902e03411540341202d000c180085460300001500798000c0704a6500340c1c80e4005071001849000304002e10300301c11020041038903980c0d50f001c042d0040c482004003400c40e84074403001403038580c808552203101e1923004800703034210f4803240c48680c025084000101c95404590b124202111800c100c2c0c1c0d01e4816411020420310760074200380f42c0643e003000b10b4541c0100b9040009000004010036503603040351486100043c0c66561009482c0703080c2d14145000380700217001071441c10311401906543c820a000ba2110080c120101d9200d0b04603110840741c00480340780300c10040c0001d280402c002d0804981000000c035504075550000307042039201c16481c05400f9a50303004100002020540d05501803421040f0b18210303d440312018000e842502c2a030b100300000080c0c00440107002e4041500510340088071562100303400c1c58054044a0300361100e07170114450006c212000b694a004640c8400301590 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 87204110 1250 87202860 87202873
    0x140105010f060504030807030e04050f04050106120218100b0a050301060201060b0403030509090c09040234030206070c020303070f0b060f03010204120305070809060f04060e04020306090402090406110d020c010b0604030203 97
    0x21a034000c4d50300207c1040b0f08005405034905a01d41d124059030b0300400c2c107059143c809040070300d012403c4901952181c1c1c0500f2803907440501503a078482c6441e00c80c50000c058071015943c3c05814402015154100340c03a41e00d40843c0ca00106640180550306840d80d58000708205525071a0701c40c01030040f8800200001e00c200103408080c10450040e9802ca04188420785c1450500d03070014050741c10825400c910101001414800c0d45201d81c014205084a080702c1c403241011610001c1d12414010805800c0c06142843c1d0783c11510b04008850200c2d4100c9081c04030301e801072509c108506029101c1c54070444000e4624965460107108403000c031b40c01c2c2d81d55002c4622080d0303400d45058011881c1511541424881d4899545074030b001054030b000e000320700076a11410700e000500200d680c0d00565004500c1072082100e1511a004295045501143c110950755114036122001d0401e01400708130f00c0b200422444138502131070b0042c00c01204910028002c5008020910a840c0101d110281d459840380 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 87205360 1250 87204110 87204113
    0x603070e0403050711041109040b040c08010506070f06110c1c02061506040b0a0810061b020609120714030c09090c01030207080d0c05090a0509040f08090109030b04140105010f06050403 81
    0x60700100a2a4400c040d0045c81744c1000c0c001900b101d01680d130f1071800b00d000142c100c600b840c10740304a00040707108842c1000025251a001028104140070345402001e000030036405024040112148040c0c1c00b1000b40a18061201c00700c890740c202c4c0380803440502c45e1a80c1c4519005105001c854443c000398000c0580343d0300c01d0701000803040000c0c01f041e00700c181080080b6044407440c004040c29000d5032500000d60410702c1c07040c2d054030741a0344880c04000c240c40150100080955211287c5a011184030f51a40303903490000c0c40124514144160900c107030040001e11522183c00da00c0000800c0742503814240c194030038008400303070854484000d030708802e1145465600035400741c072455015100c041e04229421940c04110344c55001d00320041200459164041e01d007030f03440c0f18050041a110440b007810156900e111502003904010240c050220b203200d600c0c0d2245c00744800550b0841d000c010b25050605140c0750071161b9101440380382d4281400441e80703c9174915004115201a91000e1405103507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 87206610 1250 87205360 87205367
    0x601080609100803131511030703030f0609050a06061d03191712011a0c0c0112020c010603031707030207030f12020d1a1f0c020904170a050309060603070e0403 70
    0x9140070000040142e000c10f014400304040c0c0040d610703c8003004501401c0028030181c011840000030200580000c464400700d502005550703080d6454240401c481241c0c06461000e810141c0007140001c1c40c0500b00a01c1c40c20f503400c9101114230700d484116210f030309282c4011880e0004810103030181d1191001c9003c51450360f45400109001d0b50301445c2818030320104c0001503028013015000754812200600504015030036204406141c416800d2400014040b003644818066101e14144000f00c0041c04104465804481c10311078044000c000c03041d101e02d000f03070980e400d4001d2800c03c00545000111810300034801c880f001901612042c007020302c205001c81c0c91800e0f6805100c0115001d00254003500010300a9281600c410f00e10000704600e04410f00120003810404890a400c041c0b81c6900080c2d0000d045100161301509c1803413483d55a4101040d401e4a076079440c0038141800189800c1c4641d01401850040011900391549a03c42c88101685c0e607409001e4041e68065034408940001c0c003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 87207860 1250 87206610 87206629
    0x803060a0302030d02030a170106090608060118121707050619020705150915100510030e0f071a0a0f0e0f030f030901140c0703030e0102030d02130306060e06010806 72
    0x1400d040361607490782e010904141c0c900303039041d0141e40003180500e00181c11005101150940da0085d042e190724261000f040380c04948202002c0c02203500205d40d541c0d1158842e00c030075000709002840070982d61710075070b00a14081c80040c0c400f00112280849040d40071002c480320190001e0040903641c4550a0844030790031201050808594200981c0300024003d02400124a89900140e05a4908102072030f0400411264000070308504c0010000109013000c6a0000c0d140203440f01c91a080341d200098004121005108403103202d02c4407403081b180f80014840b01500d081c1c440c04809540105800c3e4001c2c050483c002000c540745148190016128194610010b02d0090010114030144004203040c200c0c4141c84465980001604800c6940c0105070702d00e07108030042240e41342c450440083c5440e000e60b03010050030400c084181c031840b40c1c070130400e8624032104041d046607151600c3d85020001e400300e1000300e0310f0505040340016070a010000f814440d03401a115490590385441c10020a900c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 87209110 1250 87207860 87207871
    0x1003020103180b040605010303080c070f060b010c05030f1803030f0d15050d0309080606010507051209060708030703050105010905040e031b0f010c03051005040b0112110409020a17150a030803 84
    0xb25000070300b0205110001c418040d83c011240015554114103000700340f41001002211030f90400c2143e00c000901c01c2d03190302d810940000c00015508107140040740d03d920381010140103884041051000020424014000c1c0c4401e9460400018150070078503860780285850400f960806100d400019107441c1c000501840b0016000b0041e0354840e03000440030034200c5005d07000915030010034090307440108007a0b138002c60b00342007103410f00b0040d40d21039a44200d00d08043e41603410105010a0755103900e0300f6100d129520184103030300c174034182000070010321091180c00e0000360001000141802d00340300f441d00341c034000d4004d103141c0f5003400e021082c8203d80101c402064032500f001c036407180100781303d00284600c41c0d980c08552410100c01003440040f568000070b01ca0f602d849654030050307820910034410303411030540109928101c1c0c2d4a0f0300d00750045a004d422030038000540072150550248000443c80c0c080c0071123401350345034444425140307401006415040f010020f01130001c0f0342400007841e40074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 87210360 1250 87209110 87209141
    0x60d060f021308010207031d1309021c0b1005040504080a1d03010e0c0414070c0b090a1e02010f02010b0f060c03040506040603060e01080c0d080306031507081501081003020103 77
    0x2820701c0b000c5140c1036200354072507801d1340d5011842c40100746e485441c1a41c0404c00d08107403200b00d4144800038401102c8941c2211240e5a0348000c001151244816005007030b0170100740510f07080c904d003801d10443d8000c55044a40355104800801c0520b0719124141c000c0c1c3d00051603e04103115000c0c00e03031300c2c200300c0054581d0320000c4510804d15941c00b40142800444140041c02d0709031000d03002e00090311500595064078401210802030040d51150950049941160b0004219201e0a6841d8105024480054040c2400303165000e44054004c05100401d07100fa0b0740c0c0b03000c400b43c1d0304080b422a07540c00341296029000c80007100715072804034046c21542c0b4459041c0c070f1405941d9030000c3c826601591050703010980340e800c00c01c000010015100c1c0141410740103025001d44040020309500b0300140010f2a001020020a905440400c803c0c1c5041342e4136681d036401403d207218003401c44130007141e5040d19a442010008055486561218002c0c95020550400340c1d0031680150007030885400c0c000140c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 87211610 1250 87210360 87210367
    0xc09140a1a0301051009230a0902011209051c02030304020f01050309011512051203041a04060204050409140708070305210c0706120b010906080402040504231005010608060d060f02 79
    0x1a42d50030300c9050b00610348003c114030746502d01052482500c603035248038098000703956000d03c1850400700100d54008000c40c0000303212152440182c40c4203240c64120301e406440d0049040030480b000407004a84180b020700342860740f618140c00c076502d2000f1240250088084100492a5401107021f0354004110600125201c100100d41140030134103684014040c800c000d148009018091240140c401d4442d807081d4070b14a0903446c0c03282c001444400f00d003400400c3c2c100040600040c2e90558000e01001070050042c0380d40d9040120038140780703d0800509001d03150002800c45800140101101e90160141c09103180024007100820802c0c0107070b00c0d0b039a8007081503003812001071084001510040c0c4503c024601d80c0035003102250328404000b8144246800b083c0840c1d42c00c04440d03a40030754120f4020030240e031280361080d000c078041d84480070600721000e1441451203002c5504844030f41101004c00403170780d0b03c24080794484c0043d02d0540e04441144a42000b0510766003012112034035840d0098075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 87212860 1250 87211610 87211661
    0xc020103020d09030903020a290a0e0a1d150d17040f0303090603060e010e040609031211070b060312070f0512030a05040311210a031104030b040c09140a 67
    0x10380b01041402c81c0000c01020040c0b04514244900340702801482d00c460a141074034008035207800038154900c000c9c1c40400b00314100d00c944a03411800a117200a090b0b0f644c1981d494048414540000c071500440c5110a00000c07120080900220060f9500034620f40240015854034400110101402c0504000c00c10002c0395400b002321b0ac0d80c00652003652382e40d480d1807600c00020222401c42e000b50041001c400300400100d00d4001146400c1500401c00140402c141d01e819070b4060901d81311203a0741410310058080e113142c20b40180003a103009a80280f1203585190401d6101c01001d490b001d030703160040c03000d0300107d84183d10603480148206c2c111f802512922aa07006150401c460001c081502c0b5010002010b5001004102000c0941c0c0145140c885000740c16208800e134628000e9569004107094003158401d400001103692440082a80c2d1500c0e420b203075815501c221011340702d1a040780c1000031042c03407510408260040300011148240c43c4d10203d2f0014080f00503200414021103a40244c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 87214110 1250 87212860 87212887
    0x531031701031a0a0e071401030212010602070906080705061209070b0316030b011803021302130b071a0705040b0a0e03030c0c0307080c060d270f02041118010c02010302 74
    0x14069030107244030140c0220108500c141d000f000030003080300e0354100742d1840c8141c10002150000d07924101412049240d80781d0049009004540359031181d00c004000000325203402050107410344031800c20500c03c4544034418640e5610765031107002e82101c0c0c01c204040b0101c9142c42d4141d0050401010340d401c0641e1824600740c076400a54021821907401c41102181c60307018465a0100c0c103080c00d01402070141d0401100c1440d00303e00c0003074041c41e0b0102040407105101d9045a12402c15564052a401d403101e80d140320300d4002f06c504590350000c000700c0e0a5910b119005141c8a40e01a581e441c1c945814a044d900080c0c010b100440203200225526050580d81031006e0a25080080d005040b0041d0010402d8604081d9a200e40754030b03000b04110000c0c60312800c0032910110200680070402c0040110702a4280c051140300c00e0800229202c98010411080c41040515000302d03800d0000c01904086021248210401000c0e89101a1406511940600140580b05005040050070860381c0b45001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 87215360 1250 87214110 87214157
    0x308041a040e0a02030609100311040e01060909050a0507090608060a090c050406170105070509031b030c0303030c12011e09150506030a0f0e010203040b1b0f0f0d053103 74
    0x6075000700400a0700c0c00c25002007230344000d12070403d111039490b40d220302c01c1134503400041c0b902079904c48400700c04d900002d4110798018030702d03903100308049402404c015464882001044a550080e41c0001524100600410040c2c401c51409440030780c4444046070300a01c0d05100c00c4642030680c24000400b640c03144a004028501108801c200f4043d02c4652802c440340100350742c0c01d0040601c020302c410389000550b0000c500075030b002d4140d454030b8200024a4040c6100b480340d814403000007000078000340c080c05414030591071014540da43e41c0303803140c981d0b003030b07002d14208280c0c1c03500d042c001c1081303401c9500b0000030192090b030381d03040307807612180407c20a9200716980344807203843d07400500590f4001c0c40384c1c80c7c1c20007800c4021811070426a4072543d500c20040d050301d002c5450011320004094410702281e00c00340a040040c0c0c0d0300c0b510081e00303031031613040020203454280c41c010000e4117061001d0103850901240342452108416422104034800d6403081042d07082000c2d40020042c5090754441c1c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 87216610 1250 87215360 87215371
    0x905060714031b0d081902070204020903070915060809060403050a0e0301050907060908120313151b0305092b05160c0302030d0908030a0516060f0507020d05040308041a040e 76
    0x902c2800c540201c03d07840c10321a050700c002045410300400c04900b41161000c1001c0900c1840580e03101564000a8081c0c0a400710041e49402007420004038039003913511615000381402c40403070320b10317a54003415911103500b1502c0a0b040d401410010b40001e01c80d0005181074008c81c02e0509003941c11402280c21518102c0d040d0f61103034401401445038981085c0074074010084680144006465074100c035000340005096041c040304864111001c006408448440301c0d074400c03404024404c0f03031491500b90100c2e000d501d240482e1900001c500805804580c0c81100400342c1c110b1412842d200c42d007491620a4070204e1810043d050000c580748021030322a141e1801d020342a0444901d0660040605003007940b000b00c0240581c00408019100d004010b030f4882d035440d401e0860312101c0d0140d01040800c182e20b0000c0043e03190054203060314044d54020f03800703600e0641c00c17500c1c01441500262020b100318080646210b205110800440c0c022403903690390202e0580f18903041030303991030714005891001da48 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 87217860 1250 87216610 87216637
    0x80403030e0f1501320a0803030a0501050f0f01051b0106150804050115060906080603120c0607032403061a10020f060601031401030605070c0c06210c090506071403 72
    0x10440205204503030680942044802285400b007901110710a6041000c01e03c0240740c2c91417204021a0f8412450000410405003920355a141c0f018140d0000c01c024001c491040711802004040350814025000c0b4a82d0184c444d540307000c0b01c4800d050410364504030001410340d00d0380c27004102c2c08844445128640400e44400b40503042a00c0c1103800c3d1000d4465255000580d14400c02242e136004500307408886081c01c021549441e03140201e03003004050b0306411460380d070004042105240008566100f80030342d68003000301c840142e4a1011221440d40c0c042080802c5960070710125105a0000318054004c0c81c02465100310403000c20203000040c1080030250308400c070313909928a018080c09500c070700309107000c12810b803a0301012081c00c0303c180400303041c81f50f46a0008400300e0181400c4030f400354119044c001340c3c5664035401003011440682a4103100348600788501d05070032900800e1034492440c1c9901980701d0404041c004d89820400007904c9421008038988c00095007800100035429030f052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 87219110 1250 87217860 87217873
    0x6030209031b0306010302150d0c09050f0f06031602100908070b1e0109050a0b030a0602040501021b1005160b13020109150e04240b03010609120308010501080403030e0f 74
    0x40070142040300c40400d01601d00c501d10030101e01030307a0101d80c60341941ea0446001100344001d040002242c0511000f9820300ca00e889048200d154000a40c801114400c4982e06007014000f002e00040c1602c96050f660441c80c04c0c000300d200704041c062640c444049034411610881030f0212036100380c5440c0d40c81a0784041c00061080188209403400c15886940d00b04400c032006c600c8100c0d490075401c14800c55400640e14004100b8544264004c284540320007011941c5542c020b050040084d4454820503002d40b00c1e0300426000d001d20307811552040d1700d004146a446400c480405d84081c2c0c403c480c4a03040d498000781c40000510f411001d10300035000e000340c4050100c1c00d0710014112880b243c02c00410202d5240c1c540b8000c070352000100c8a00301040d41c001c030b00519111000402c00582980d00005418050700c00310700350a41c200510f040300c8165071403003512581d419152901d4141c05102600285601c00180025405038104c560054840e10b000518031a00410309401c0118040c0700c841c0c1c0782c2103c0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 87220360 1250 87219110 87219127
    0x10c02060a0f1112181c0c032f0105090d1e0e12010203100e04050d030b0f06040306020d0f0606170c1b030307030b1207050904050a050d020607020f0102030c03040303020d090c060302 80
    0x886400009a100c5008141d0f804280704188661000740c0310000821420030180e4003010b214042c0d466000040120700c400440f28903104520003109c0002910440d86000001244242c1c00a40c0c0c1d04a00401e03100e41079030150590f40040c0300c0a43c500080e0612002201d5942180c4030303051480d4819580000041e16030030507100d52229408954800160181c4038014480425004a1300c200503140904000840842d5400481c0910710084942d0703500c80c902140010038021103800402803441c020104100c20100038241c413044443c11301550002030289021407030041750040360030703802480e820103050070401c000b03010390b00040100d1000000c82e0404018020313982c0c1c05014400e60040102d032051804031054074641d90b141e6039846520321134131a02000c1000c0c44400d101010880e9002400c0d9007012650300c4002c0e5132500103462400040c0b29602103003000300418405d490048000400482c0f031a25561401c801940000c0e800c03094065440301c1c280005031078207981e480103143d507460258a40010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 87221610 1250 87220360 87220381
    0x90103030207031203050106080105191a0c06060a0308030c0f040302130c0e011e050901030b03030a1110020a08010501120e01051f051806120304121b08010c02060a0f1112 75
    0x4c0c4010201031600b00001480354680040c52141986c2003503170003004084401d00826081c002507170228818901e944034045411861000600e000d901c0a02114820b80301c00d018040d0340b8003503200107400c400003800070a0403400c00e4401455500d0802d0710342411309403250005075001000540500d0b499075180600c0250361781244000801b15001d08121004804c0f80e41c01c00500d40c1d4401b0b511081000004036241d0030f078029400091141d030090300b241c0c0c4408211401400480c08040c04404a00c1540c180b004c40c034500d8001c99817440055507890314164603080c019035a084c5c100c00e151810f41d03180c1c200c40291940c24865503100313040603050034040001d101c1000704505002d8202c14041d1031014041d2211451000c0c0030340d0005416581d8203132402404103843d0640c09140c002c0060928490a00002e22407001e1307030505c1c442c103190007103500581d071036031414201c4850040b041c003d60040d4002a00183e03c5612100031003009280c0442c0d180400310f04481326520071212042e03420112030612206070311 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 87222860 1250 87221610 87221633
    0xf14010204060e0306060f0114120a021209030a02070521060406050708060a0b0301050d020604050a0f14100206150312040801060f090e1f091505090d020606010c08130509010303020703 81
    0x20306130050116810701c00d010540c1c0c4144101014184030140c0300700802403070000304441d10042c4405052410341419203110001c1d5219001000c1c1030240400807031011703a008000c4070000d41c00b03600102740951034a018004007801040440c42607d501030045070080c8014030401c0d2285128540019031880c081e14050b001c000082c2040b40149204d80040c007400d191203044030b055820031110998060402d200045461080380c00864100005050010f449400010414259141e40074401c0d03440c000c40b0203116140c98140000780043e84281c02007403a1100101791031000040203000d84940d2100c65007480355a07482580500c0c1b40b41e5441508002c4120284200741c060a241d10060080b9040c6094050b0395081c2095903c0101a0041015029005c80d034400c4a846612481e201200c501d8a200c0d07100400c01150523503024010351001e2041c85202003000ba02c21801619917002d0394a07d910b4085540e000180e1510183e01c0341040403809642e8585a00d0095200354010103040d8214980389a4854 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 87224110 1250 87222860 87222887
    0x7030c02070e010b070632010303140306060403030e01120c0e0306090109030e060c01060503070f06110c1c0f0203010e0c031203060607080c0a060906050115080405030a05070f1401020406 82
    0x40c0100c0042c06000503000c1218100c641028020031540d1035010400104800751f070400d5500b8000522011a0071002e90121303048a0003070712203034800301d103800e207400b1507120480d90f06600c52070070042400000d004003c048020001850844110011658244100d4000c1b03124480481c2884518686a1a080041580c07117040a4000e01906080365406441c0c0300c114100d840c42081c0106010700c02c00c40951203500182801803c0304e283c5645d400c0d03411104221402424002101c1c01e0b05a00703030391400034402d900980094003840d0304c64451420503000441c912012604102580f0050025036001d00402140103454000b42200d003500c2d0701054a00f0340c104c11402c0c0044018002c10021b6a070b803806642c030b0780d81c00543c4595207407403140c4110304220503e07200034025071500d0051818404540d110a06a40b01c0c021080078110a070320080e2404002241d0003811a4420032407250030910500242c00074521540e910b03880c1d504155540a42480900d100d0a810380d07000c034003000700c5580440e032203d1a5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 87225360 1250 87224110 87224129
    0x204290105070503030402100c05070308030106120209010f0f0314090303070201051806070503060103020708120a0c030209031b0a050a170601060305011d0711010c0306080606030c18070207050907030c0207 90
    0x250b941e0f480c0381d240e02000b00040d101c3c0c0e030382c1021b40c030f0454040c03114160700c1d42d400f209a40b031494480c60303d8003564000b03019040000d80341d800e48042000031842122a0004141c540100c0d0710250102114280c1c082440101015100c3d1245074590080b6508503020300c45000c050f40c3c0b81e1400c4040242106c50007402000500f200e0070b00703c0010100410860b400003203a1130f14070b03543e545050060700648240c42000308881d0002500c2d040039102082d459000345403203003090200b840c0740c0e5412420390140800159054000ca000c901c2c0b50003d04090400c0220b000d031842c1c0c2e0b01940c84e800210128500d511641d07081d4107005044160f03540c00d004050142001e82000c0001e035042087c2d4120118400c3c41003001100035070041009117020720701700e80c1c0c0450a00d0090080e0304a5404c0100581010710070a206403150f04080741071403401003400a00b0320740280101c1028940e00c18600c0202c08090710b40c10070340c01211408640c40e1901a0042c1c4150000e41300400d41101145001f8580f500c580c3c0510b050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 87226610 1250 87225360 87225367
    0x602030615160803071b051f0204140603090c0603010f1707031112010603060e070302120114040210030b060406030605100e011d12101b03090302280204290105 70
    0xd181120002c00300c41a0400c0744143c81e40d03244c041c1550240c10700c442c9488090104440d60040080002e9884480c4508103003e40702481c4030f14050041e0f01480c0280002c04d4026040c5040302e0812402030b55000c2d0b000d8046806c0c040301100440c00c02d40c000e030041051510180e1091020b00c1806000404c3c3e040703240001c03e6001c3c13070750b210221507407079080c1d28521810401c50b000c80c00c22002d4000ca009503420900c00c110822111034025503410561000305e000b000c0c80340a01d80c120906200b4154038420301909102c06686640c2041400d00e401c288000c141543c0c0c0c010500d41d600c41a000e000642019100000d2260400c2c040013541014412010100806c20610f0107269901881d45907000c841ca900c158001151203002445112602104028500c030b850482c625003c09901300d61610f120103c0d02403a40000050102c003a5044a4406400350b4860b104c0b241803115048240b4a5528052043c0140007100c1c2c1e000500f526803a042e00b0038a84981121489441d8401d00280285602400e10350b14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 87227860 1250 87226610 87226627
    0x30f0212130605030402040212151002010203090a1403040308131a1e0d20070b1f06050304061e0e06060a140402070204090b04030c0507050f06030f061504030602030615 74
    0x180c00e001d0b40291000c002012010034119140c0342c054400e2141103010a001c40c0c909142d00c0081008800c03d00303803180403842d4000c5030190042c401c403401072107420b010345162906c58a1b40c1001c0d03400d02e40e010f100f500c0304210000c041803082c406080442420011150362030f2404035000c0041010f00507001d5144010040b900c0c0410308808452a070505442105407030300e83e91108540101401c50165624a00100c4c1d06043c420b0660000d01d10303244114103120041d201c144454a40140d0040140d084e00d00c174020a0280714000d002845e0301c2485210007082240c0c04054048030030001c0c0c07240c1c403a03c68695120364025642481000e80c09001a540b02007510f107000c0b42c1556110f00e8a1245019030340c00074812042d51140c1d00880b0350386821012105d11410540f900070940304100300c0039141e9002e10003000c40c1a03c1c01c40804005091b0052805003103480b00203540e50107240c0a006607070701424175070350150380c6103030080544011030207080010b07201e180680c203200e603d50900180701c401c1ca0f02000030343d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 87229110 1250 87227860 87227887
    0x11030d030204081c1e08100e0103020108042d050a050708010b030c0409050106090606080a0b030304060e040c0306030b0a0f0b0607021c031202040f081504030207120804050904030f0212 81
    0x418400c51030042103c0303290920002d8502a050b400450030041c0c905c05500489600b2500150040c04480d1011411a076554004814042e0a0000a0026070160080340126034554000380c01000040052040480744030f0031440900082041200c858016601c103401340038082c00f00500400e131110090004100d0600042e48507440502e84600c503d98481404092107000d52186028200008007000480d0302e60402500c1440212414180d45081c84001c0ca440d09021050f01c080b41d0454503800304000e00442080043c3c40c00014100c00c1658440c8000082012041c506005036282d40e000200c803a20440f1100541390742550190141c0380030008040140c442c039400300507401c503500c024205400c0a2900b240e00008a505500c10f490000c00d0100e104511800c200045480c180e080302c0045040b40410203207460100d602501507003156104101103007019a14030807803032040040341c0c41c00307455000007941d000040e5400e0340016441c10101000c19010404141001010100f2600303108c0f8011003c2d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 87230216 1106 87229110 87229123
    0x60e06040c060f080c0304020d020a09050604180c030b100e1927020909031b0607170c18010c05032821020306060909010311030d03020408 61
    0x550b02e004401c41c038800a403a03201c0c141c80c1d0b84d0381c030000c035070a40000b002a07030006200c0c0200c0e001655082045d20150288080c00102c1d400d0507810b0204a03001040100d0b162010558240041076403903a001c4100d9034482c20107046a5504070400380315080b9584201c0c2c1c2c0d80d2130072003440b800800c9034959480042c0b09207810001c2030111000300f40c4108a050401000024a59114015040503214280c1c0460404100c0746000521959611810b50101c0b20400d40d420180074480d40c154000c0f114900c136204030b4442c0e102c0e414240680e080c00d20a03560000c0b441c0d1030740d401c0320010364010306050f43d0064003c000d403901c0d18410401c44004054120b504000700300d01c420b03e80c0403030780100c9440a0000f40c2c50301e07000e080c00d500360400c3d0003580081c12103a03201e801407041c1d9002e59518444c140c040d40c8281001c16800090078141490f0140443d00e010600d801400103000450000480 = true := by decide +kernel

theorem cover : BRFrame.Cov 87050360 87230216 := by
  have h0 := BRFrame.cov_init 87050360
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87050360 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 87050360 ≤ n) (h2 : n < 87230216) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
