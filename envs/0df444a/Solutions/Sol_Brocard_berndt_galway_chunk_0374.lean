-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0374
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:29:27.119601+00:00
-- url     : https://prove2.me/submissions/ba3ce9f0-daa6-4dfb-8c3a-13e9ec2ff68b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 67086333 ≤ n < 67266189 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 67087583 1250 67086333 67086337
    0x6010f06170406020a090510020a02040f02120708250905030d0807050316020a08180a120209060603070c0b010f06020f120f1b01020a050403060b0f13200c060f0f0705 73
    0xd500040061711072658407021103030b02d501030300304a420196004005082c943c000070f0740801c25100315424020040b052600109074020070f560402c43c08500e101107070f84180110031081c2e00c400c9201e0300441410f4290004c06890a090005401045920340c050009040a00080360b0904441c100740f40e6a05190b40c1c02050f51000520703441034016034690801c8610703c28082011600d40020080e61111000b0780305455200c11040c1e1244140c8006c0707400141c0f841080075220301c164000b413988006940d10b0f014001c1550005220200b000b8104400b000091590f001003070107040212088100a4141003001c2d141a50030b4681d106980e00580842e4110403c40c0c00300c0e000c0340d140702101a143d039045114038800071b0120022000ea940003280b2480720541c0034000d40b08590007030070103111007a102c01c18452150441d4205642201000480c1804011503400c031003500105801c0c0190740209200c0000ca19802400703990079240c01c540d080c408814039080c01030384c01240054400c0b1031801c01180280c000c3c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 67088833 1250 67087583 67087591
    0x130c05090c0918060102010e0d020d0309030c061406040e0a0c120501110c060406060605041419051008040605060a08060f0406021606090501061e09020f0c030c06010f0617 75
    0xe4248000000c0601c0d07800303000c2c0e40b60700c40c000e80b02d5980707403800350f00c1002e41110445101e80191310300040401d0003c000200d4103c040b030950040e120580040b90202d01034064103400b40d05004050035031800003111841990541668218030355201c0c1002010082664005022445281c0c000403a61001c207005101820856012400e901e1130880c06252071800760102c2c01081045c12130204102e001c0b00c00c08a0203034070072881020708014843d100c0703c0585860145000722820380035038908900c0345040500c0d0800300403856803001f10840e6661000a080140c200006800040703a1006000400036a4081c2c240c0140c001c48202502d1414800e80b559902e00051110041c0c1ca01140850300f8001a641122010040824915660041420840e01904038484100d4881d8681940001c41084114603410361040c8030b4441e000152520008001a402c81c000d00401c0c034800708880624101c3c200014004074106038094a560b44c507000c00f4800c0d003001c550003a0144601d00030040701c0c250240c4801640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 67090083 1250 67088833 67088839
    0x9090a0b060904090609050102070c1403120f0a0905090108150603060705072010051207081005042a180f060203030f0405010b33130501110a0c0306060e130c05 70
    0x1e6084c1030410710042c141c40e080c0a00b665200240810500c0303e800c644a0603104414480e18102a4013400e1507900d01d45000346810000c2d041c0407241b00c01c0a010014100c0e4003507443c004500175100d0000501415081e40507104941c0800c3c10102ea411211030101c0d0700000031800380900c0d1400c1007001d0000d10a0300740c014a10a2111010144030442103081c00550f40041c081e03410040c0d1140c0003a24550080007191000b46480002071503083c030a07800184581039810641c2e80c2503152200703101c05840044602001040e035000140110715130401404030351003165450703024032501088002005115500400700c40c1280800c24042e00b40c0001c101e9402900700d030001d10055a0f00d04200d8010b00d118030302e00d68007903080c4181c03a03248080c0808c0442c8280035400b46d02d0240c3c1a0384048070f482e1140d41d00001c03000032100d000304560b40c001c501c044c4143c1600c4094a629000594802c583e0040d2604100c810a179100c07014840501114249913210826145001d00940c458036104480e012511401c1d02c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 67091333 1250 67090083 67090091
    0x51306030506060d0212041416050909030f1201050f0a0311010819050a1d070302180405071802070b01050402030402010c020f0f04090b040218040b0712060b0403030509090a0b060904 80
    0x2142d45440003100d1140c4a009421034980180b06c21441120300142c90641e08440d1900c0c018941400200740c4002c030b0b051004564040a2900e018881d0500b00201140e009000a03c04000760140da40c0081008a02058602e00c1d503605050811a441c0951504e9a0064030100b03003e0000841500c041c0c1d0300000d00b428090b00d5650380c2c40d411450000766100d503840c414280410300c030304003040c1d400c0040c00c84040040f4640c00f2031000c462669800c0315100c040d50141c0144818103210405ca03080c80c2d0400c0c01a03058510711511208060070007810f05040e14010b079400a22081400035901340180900800c5400f5407441c00c040d00000c00030600142c02138031440e159002c4020613924001c0b400018600036000303000d03d100c1e6042180c092001100c041c0d000e16440c080042c00031403404d1559104913444281d082158440c8501116082030802641d000583e5030030001c40c1c481d5604001c1c2c00103500c070350340d00341d9a400220180007900c00050552900a0308103001d850103940c400080d11404102a10005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 67092583 1250 67091333 67091341
    0xe030d02090d0c09050a0f051006080c12040b0f0c0a0c02011b020307060e040f0c08071803050a0f060b030607020309040e0304170102041a03190504150507050a02010c0513060305 78
    0x5a20030040c80c2c0042900c031040c180003a15034103d40040707208215030001001880c0e40000e50609448085803141c0342d200c0d2140f0b0a00800b809000e07080d400c440104602414121070714103200415100744da041e1a0040010100180040780c0568554017140741f00b411420301a84050150440303000d240028103009041c81d103411039212001600c1181d680042c100d4640782c0e901d80000c3d00d192003c1b5003075030007282054102a4001e04c030340103049520703240b6907a407801c641d43d18104840d22640030058064041c0c020800202042080003400700342c500541841c0c1e44c18500f840d10f21700712001c6580c000d01981000c001c022441d500401a64a0b250382520041011079082ea4410700307512854100402044c3c50100f12454030105501600c00d480704104d6200000c1c5c0c85158003034080c001103c44540c5000400d110042070542c5402054119206208002000d6a0100081c050301d00449483c000260b01040300c80b00154240540070861006042c00392401040c401024403041303640c02500103041e194000310b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 67093833 1250 67092583 67092589
    0x2010e1504050114150111010b0918030403050303160e0f091f0e100f060203030c090d14010504030e04060b04050d060c02031603120c08010b030a050c0f040608060909010e030d0209 79
    0x1301c0550100542400c1c2d2421243ca00c0c60003503012410303030001d840e030800848584414480c83c034810400030080b903166a030303c26400c2c070141c0540d03118422500040c0030003c00190200302450103104c0c08401c0c94103884503544d00a06441640501c0d905c5002d00703554544158541040d656080068007403090410080c105c004041d11060703511000c80781c2e250306e0400144043c0443c001c001e9440c1070801c080580d0340e0725402c81c1d03280000d48800c0342c0041304110b020041c5c9081a0340d881400d206d560314243c40c10304c1c1c0321705900310340e01218181d010803008501c0b20054a400c1c4140c002074000ea04c145400d05080c200400c005014885000340425a46c15214424074001c00980c1e8070180008002490525140340090040e01c002d80e40d00c4080341089104009180500d42c454140e07107010785024190343d0741c6080c02010b00809041c0b9041c0380b40402c0000700c580000401032020382000d0316154141d041600c03e1051882000340100d020364901100445035800210448541200101026071560050000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 67095083 1250 67093833 67093841
    0xf02040f0b1002030c01050703060e0c09041b0302030619080a030302031b041701050c0f070303020d060b0d02090a08010b0901050108072c010206090109020a1a04090509071502010e15040501 83
    0x75039501528001c184140503900200501e643d48540c4000d1116803920035040d415039400f402401ca8145c50440040c0d40d0840c1c0c80b0141c09140e000500210700b034200d190b400c40e10011218885000260000104811403e180300c00c100c072142c404030140011490030039815211183c0d000000c0400d6000000304107108001286020030220304201d4039560b640e26030b0055004c0544001c0303603906500f0300700003461140207041a5203290301103030181c41c940040c56404800950145003115034840c0d507500049074141010000c3d01118000400c01a0f41d81c0700e000c02c100010780b01e0f81c08184940e0418214010300d0703d5015803641150400e0800b88540c0c2c440120a0781c400941000600030102013408011500000f210b0150b081b2030280c0035035a07036031601080c0c2400d850b075a031806500620380c000f0404c045000d10141c44500d11001410b9418152159441070540700291898200c603480351006121490403184c0e085100d1700d0030b0008100f010351b81d441040d1910042108540c5800001000030184402900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 67096333 1250 67095083 67095101
    0x806010b0717040801050f07020604170d1503030e0102100504020a03061512050706031a011e02010e010908040f0b18040b040b03032101060c0c051027060305060d0f02040f 75
    0x440361034a8507104e48034000c10040b50744021103500340010800076800030588502072a04001e40e411004081a00c9020650010200604241d9517018030039072803468030002030246120359101c0c3d52041c40703280024905001c1c03e44002c0490b2030242480010390f0752004081c102c980c040e0001c6281108003805248500807a40504000e40368130030701c503041081c0452084159045500d0030024040350b5141c003c00c1c03440c080d27480381c081911040c0b12902d07c00d085408014009681c40045003160343c00c0c08207400e64071000c500311000712002c90180f00d802c07100707016a0003809144840e1810030114a1010503440702c220449030140341d0742c01d1102031036221900058a0858060116aa1000090b00680b0b002c841c0c02c69282a128418002040c3c01d072245218548c515004801c400c4010b091908000e000311481c24028181300312a50000d50704911800f05e04246d0359540008880e4500e4040d014065900080446114500102d8407000050781410045503280d015203000506594421085004009483c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 67097583 1250 67096333 67096373
    0xf051c0507060804120915030e0f07030c0305010c03050402011d0d021c060c030e031e04031a010602120f0a1809110703020c030712030c0c0317040602160806010b07 72
    0x141c0003041d000d03004001c050207644204044a0400700310038017240c00141a0040340c0001c101c45900c00c846a06c44d400c40099a29940241c8090340101c8a900d884c180389544115010660fa143c10014000300b80714a207241046820207000600d05130340000d102d41c0b6591440d100120400fa07081255480355a504840540c2c0580126031202c041c0048002403998a0f0040301d11904250710b80703c490788079001d8000503c01020040d410f060340c080c0406108200d031041c01008803c140400000b2a16540d072826401020740d0508400b54100340c0002c0c10a80300b502d040010001c02c20900030440c12440c12079150402e00d00e070842d1018560802240d1008a03640181c401074200b246d10200244010000d25940d44250200c4158112620505455005a2144d4241c070004150f000010038001d219801d84280324504844d500307a01d90344c0711050b8550030a03540c4040303000400c09104980c0c0410848000500702050000340900d02420290307500d105001e1407402400119031001000407411503548660300b08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 67098833 1250 67097583 67097593
    0x1b0106060306080c04090215160807111e01140c030c070807060906030902030303010b03060d0f0302070e010e0f0a020901030605030303040809150711100903051b01090b040f051c05 79
    0x100300c0240901401c1c02842000c0c01360b00110490f51410340b00e0b507080f660703004d400c0704000d0003280034002c49500b000400b540c40e0000ea21201c0b000070310004c010b0607100d01c6207044160740f803040780c14040c58842004078080103981c20380303000c10b1a03078100a400b0100e42c46008010380c2c5417421400d690550240c1100781c5da481c400c440010442c00d501107509400d82d0469510614050754881c1d0441c140c84a0308406501500200014040441c20000550303000c0c101034507400d00710100d507845c04100c041d800020340040e08044414403514116000301401410720180800040c00c0092440164450260140700c126a00090b40110750340139401c00001040010305803900da103002c0c02d00c054191b2003018540d00c10b0600c043c9458035075007203a09071200c07160407040002d03a200d03190301031043c01000720b00160240320201100000088082001590500d190f0781040c1310036042200140408880381c000361a60383c4284400e115403808004c1c0e8008440c01103507040e0341100156043c1c0c0300e5030302413040501030f0b001c1c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 67100083 1250 67098833 67098839
    0x120913090b07230405060f03070302070c0e040b01050904020306160e061b1606090603090309090c050711010509030c090612010212040302070e0f0402040504170a03140a140403051b0106 81
    0x52419040e03404006607400b1031607483d521203100354000e15912a80030f1000c0190a108900916445190390030018038250041c4c4a0f0101f10b034850348040c000b09403000411042080f800761680c0180360959123080181000d600003a156000244161410a03202c180031074001d101d0342800400100c080d042a964a00314040b980f000b50183c00d013401c0902c600b001c4041504801c42c0120f00312034903541d0701c17501281450011400b03000749e52019003c00101c101c011074044541d101c1c00c0a101f44940b50039a59816920f004103101505044c0107050000c02d2001031003c0d1000b24001060302c034110381d042c3c2c45690341c43c0050418401c5608000407584040344d68044200c0c92182680078078026000c960503980d070ad900d070000700c0c003003101c90481d00a40e038404100182010340003140c220303229046c0840010400340c04810315410051140c80040c0e1078200320075512401500721600000c0d00c2c001806076605044c5402d20740c5102070001410410006000c2014007440c546c40507810a280d4020302a01c2d0b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 67101333 1250 67100083 67100087
    0x41a0901090c0e040803190207020415050f0d051c0302070503040e010501120203010b0d050601020a0b09070603060503070b0906091311040f061d1002030909040b04050105010503120913090b07 84
    0x428401c0c11500a0001800415266050100b0900c00e07a882240d4078a182d03601b1043d600084446120404519000e105c184016900c901a8890202d400c0d0621000345240004220040d480d6043c000d0289682c898a07802080c0003060f005103448031000c820006020740a0b00b14000d20454602a18074040420702203443c5403a409014120b40d026600d5000081c0a41d07504401c83c402885004100d42040002e69850b84240c0c00c5242c3c01001401501c0e0781803040d80b2014008401202c40c000d49400c004c9003400044d130580b181001410081d8020002d40f0700b4132240c103025101d0b91441c40e1060701d0210700284560f40d003c00d113003d44101c0c00002d1001c4030020030b84064a400174011400c41000c010804545640701e00020700703881c03101512840301d501003007003440014040090f641d4214001080708174172703170740390030188074081c91003036008046a01e49820203030708688041c0c2109100b9000029801407503545a0107131280c0030700031940301880c160000b00354002400b00c2d0304010700312045402080303139141d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 67102583 1250 67101333 67101341
    0x30405060705150c0310060e01050415031d01140411040207020d0602070203011a030c01080901060803040e150a0803270406120218011a03040503131707080106050a030b041a0901 78
    0xf24010798042d615441c001c46aa40411200c3c01c5980d04a030000b04840741c40390042c00c802038410305016183c00d80b1062501060701c0800c0c450000b00c0d4a8212080403140d000d540c065a001010001300f0a0b16042000e84504050140c405043c81c03440721000c1c48a03540f19412200d100341d0050104e6180c10b040d1410310041d4005a1b0203a1295191840302c5c20203a0341c2c4a81c07540f01940042c0644481c10303000006542980c4c001c0e101d00020342d038070300c0301003000b641c00c03c000d0014260980741132035135103070038002c180c03100d0400c010040c02480003501c1040342060010594006440150034007000200014a1070100e00040c101c0550150030414009010f03200585d201c9240c41c0280d91080081000c821a21801e05003880b0b911f02c801200c10f1030070220307181c0c40e028581051042c030a40e40b401c650b07012030b18a8034040c1d4101c0c02440e03080282d084100d600401034140104001030084c403180d440d100c0080e01e41d444900c000b904a6107144005000c12088800403080764005002882150074500b000500034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 67103833 1250 67102583 67102603
    0x31b08030a0807081e0606030a0b0a06020a0c0b040f1203020a02061204060b0f10030c020a0c0b0405090907050102030f0c100603030306090b010207030b04060e0f151e0402010c1103030405060705 85
    0xc41d84143c0071814900081d42441000012051289481c0d140d06c000d0106560008001e1401d040c2d40f1081020640c3d00c1c003446c1c5005201581c0180036551182c01d007661a0300080c1c2c0310003031079201040300f0046c080b10880301c4030880f100034200590900040c1016030400e2510301c0029840b04000070071400c81c1e03071030101007406240250820480b000120017408445000c544059a220058036281c5400324425040b030300540307034181306481c0d882420b81c1d1800020326494004500b0103034041003c0c810750512a0403907520400a80c001d008840c54040080e45034400ea00d1016a50640001c203c000483e040003900c01110304c20b0340c10071000750b580c1130050003418107018541c0d03618140b01c46801c03a91f2000030410240da412000400c620f4413180c3c0c403030f0010486402030501501890381100d8502c0c8003400322481c0c070041030043c202c0d5442c1a0f01160718a4410f18404c0450304101014000542d0740403281c1c2015541c403d103007001140e00180000d146014980c0030f10ba004000260f9001005004a013003218 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 67105083 1250 67103833 67103837
    0x17040312050a2003070e090405030304050606010503040f110607120801050f010f0503060405040c05062205010914090a0e0a0807060c210b06071401050403020606060c07031b08030a0807 81
    0x2074490301e810b41e040d68081c030080c9031075041002a00004031a104001c58015425090480164000b940800d040c100120b13815559900088208800d11105104079a4805400d00c1c1481c59490181d6601807807030301d003440181030340200c0e0010507080c2c0c540008640740a81c1003064905882040000140114802d0080314082d00903e40000c0295000d03c0c6008840d4a69491f10b40c110742d80d4005000c01420014419692000b1703a00c400a12030300d0741d00040c40c4010b02d041c503080090301840a00102815a03a00103410002803100c20000c081007501c01600011045a202c580b07515070030602c001801c1c040020303400324040d4425a40811038820300070900c8920502003409003000c400800d0343c200c58181c0f1280c1c600c034450803051288003910751103000a507c3c001c10079814100307140c0703c1c094218166200320340302c1d030754640500041c580c0400145a00035000c48901e45042403000700341d510b8154074480245a52000c0408501c504003441d40840605100011640c50340c19844004100100a8480c140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 67106333 1250 67105083 67105091
    0x403050d090806100b070204090c0b04170304030f020d05100e070303020f0c010203090607060f05010311090604291507120807030506030714030a020a0f0812090f0405040317040312 79
    0xd540b100826018451520903031024602c61600c1c0040039140d0140e0341c100c2c2c0c020b507910300820001d08d41c00e41d10009442405c021a031260b0400c130b011010344440d81203180290740107000c2000043c0701031482c02c40480e030685540c4420080c51419916050715140b0071100070b420a50f406c4905000014140304980c020350031103800b88450800135450345605004140140c1040005044d5400c0190003801154414003000075008000350789003003111000e070412240c138200d0110680c81c03807900043d4540c0015040743c1c1000b00380c1c4824375901c1d51464074000c20400c001d11410380009a0f952541c41e50058002203c05c6554541c1c500d44460080056008040441e00346004665142e00c80e02c1514400c60016008003100d604240040c0c0128800070221917141c4a445084e80058071200c49020051000c1048522800e05014109080040c24403802242103000d00040100c2e070340c0c00ca081c0100b0002554002842d84890608443d00c0a01d0014114401090380c140020103501035901003041808540801c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 67107583 1250 67106333 67106339
    0x50c0f0105071808060103030e010c0501020f131409040201030506120609030706140118020d0e1b0102282306040812060609010c030f21020d0b120a030f140403050d09 73
    0x10301c80f00424000d092440d44603000501c0064012803800c0c43c4284141052117501009950360340c01ea90010321142c49810300881c0e803100c1d069540c560f40025211561500c02880d80641c0850108100100060b0416171910045202034442203032a1045240c1003090300c140346004594103540b41e00c50300044a0140c6002c08400c091200181035505969180c184480c16000c898000c5019420111010100b160f6075000841404010010482241d403407403210f001540c031000002e0b040012a2240241402c480ea40c1c0004060050b40120b45681d401500c03009803144083c0c00708216400c0d0702c10a042031040b00c050005102400000c1c0050480c1303a070f04001d040c0e6132442805164001c021080307001c107803c2d1011600280c00b072901809002201d2600c0c41d00c0e0b42c041d00001540310040303540c0400c0294005400e0748108141d00500b1074044040e11611220f505801451365158035001001e81001a80c00030b40d000305120b514107a859448001d05162204d4503810100c0c1c41d548002003540119031481e17000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 67108833 1250 67107583 67107617
    0x703110a0b09150703020304050406080c010306081209190902070b0405071a0702090a090507091a06030106020319090e100501020c01020a03050d0b030f0105041b06020307080405010c03050c0f010507 87
    0x4031150322026020b09a405503030083c591554220b080d0840540c0024440420031380c507684035010003400c0e13950081c207810703050600150446145ea04050b4050300000410b50008601e44101c80c08000140da119030395008009d00d81c000040b0765081920480e000140c070405101c0705100c501c0c0914014000d80782c41c0c6a6400c81c0703650300c080c180340060200a00344407080140c6890a00d083e1300544401000c80c218555a03202410401c09400000007540e8a00d0051090740c903402d10550f10b0340d420746400d491541003200c06540c0b8001c4500ba01540882040c1c00e004891060210030014035840b10307580e50a00340250320040c03040e554001c0c58018800c00030504405c0d0b2000400b40866609a1152450081207100d0300010700421403280d078044c0308403001b100c8840024031405204900814100d12009212003100700d8a00c8140c0c0880304551085c04502c0108580c10125030440f80f013400c0c4031840e000d55140680e8203019846110800303001d4452000c0d48142d042d005144608075035603800f40e5055140d80b00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 67110083 1250 67108833 67108837
    0x1051008040302190503130e094b070605070b0708040f02120a050a0c060e120607051614010b0405060d05030306040507030212041a0a0905150a020c0703110a0b 70
    0x1c003a006038480714140902001d08107010031400e002c0c0056074a01208840300c05120812503120002c0e01840710100081040300340300d55030040c0c084090302390034100c414442003582008080040300c4034281643e6003801c0e079081d5400c400040040b80682d0800360356042c0107400c1d50005a800d0365480303071a4000841c46d40c459105240b10319032003428010090200d80034071201007258001c110052084140c040d020507010441641014441c5a20b0340d00c0a080403001020441c0b001c100318080c0c40e120403103000c8400040f0300b5075800812840d0803500c2d07541d810041e003c40301c4200340152103900b0712001c81c8460314041d0844460048246e070148100d03280c0c0c1d814842c1010703440c00b02030082d8100b80b011980c103240c140c1255421940303e00e40541072080080405120380400d84040b1010841a600001040c4d101212a030788440021410806100c0540342c00b522103100103550b540429401c400034510011039030584905041d00c0c0d0454805036280d01c4d0070100e15415000c0703c1e01c2550b00003c0080c441c2a2581 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 67111333 1250 67110083 67110091
    0x507090503061602010f02120103051006051f0c08072102060114040e01020405061314030c10080403110303010f050103050a0c0207050105130e0705070b0a05090705060d06090c030501051008 83
    0x8010907071641c0d14418205090f03030801608086540340e44040c010100c040c0050075000c00c80c81c40314105035141d407400364a00904807030042e40207814140b0800c8103a0b01c180c41881904003600d00070403100e822120031a00c0c1c01c0860001030280740c020131503105102c405030340024920381c0212600d621062541c0c090f0381c0c824092054909800f0490300d0b921050501c0d41206040130043c000140c2000c2d100c1300010b240307401c840b840001e114040d03c030030804024042c0110809000c15800341c03c0e1007528101007000c02d40f0071202c20b0140722842c2c2c04201014441d44048000c841e4000c1540e890b56100e440c10390010b4441d201c1d8600090400703010415444682c0300e01c60300000b607078000307000c42403814006403003d401503460032004002d02c100c001402c6889074501d42c40f49802e544d070b065444e02e4a140600c8261000741032088000c0c50001040b03400b00c0006045400d03190100c0d041d07510340010440c00d0014118542200c00314504000921030f982d5090307005641a04c908480f11311600b200d190044480c590b04907 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 67112583 1250 67111333 67111339
    0xc0901081e0c040504060e0d03060308030c0304020f0d03090504110c030a08090a0614040204050c03041a060f0414180d0909090c08010213050f061e09030c15070605070905 75
    0x304003000940581c040c000060000d0a00b500c16002d0140001012100103c41c251410307519500b2070300a811301400015460619030604025045c256210b0149901000f000f0140703900001021400f59a9516001d2610410040504104400038a8000c0102c851840343e14022400c050300c0707406241011041c2c039900e04072480158101840c820048416082c05814194240200300e15100419090b008803510059034034406055410300b0f00c140411540c00901040303041c5814000c0c44005a494400c80301d8448402410366060340340e40c000101c0204011031950b5119240032909c3ea210040141c00c54480d01d088483e1500c50389000c1001501c2d0001034100c00e0018440b10002d0110410603480113942d64003400c21003c4a949882096003268804c0400101e14400e80c0303000c00c241d103400f022440140400b9070b00d1038180b1100c41d190106070642000140300c94640400c0400080e242001509150750b002032502d210700b082c02c403889500f030f0b0140c682031707071401d0800c40080d10060040540504407640a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 67113833 1250 67112583 67112593
    0x6030204050c1c0506010e0a090203040507060804110904030e0627030604030c0609050316060e060702010e030706110909040803010320010807080a090b0106030b0a080703080405060c2a01020c090108 87
    0xe802102e00409005085e2070501824200d811055102c028084e0003801c03c440c40181e4174103160400310f242000c1d40c1e10007403c00030342100700000240100303200c501c0700d00d0079242c110032511203142c00c5c0c81d100040360308d09411071400f04551005007101e80d03a001c01d40700c80104d40c0c5458440c020034140c035807204503000340101c1ea13404141d0300000d20650100041c0f50090b801c2c0d80c100b075800d40c44916940782059064564644800c0c0c140942c44041c091184c01041500082003110820140c15490713002d80403000e0700c500e60700c1140340040e50240c0d007202c1ca203c42c020a0306403a89014680380c4920381081c0400c0c1d03580800403c40408001048043c60555801619a01480d698034a07084803c0c08006081400705030f152401000003ca800201c54040c12040c1c0307001c0380203420001804109640c80d070014131150320240d81000400c1aa004407020b81d00d040d1045030303680c510900014609401c00240aa2010340b07026098000808040d4504030440d0903400ea44038825000100321844a0078001c0c00000d404c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 67115083 1250 67113833 67113877
    0x703080609040303110f1902060f0c09010311160506010b03010e1311032d03030f0115020f030403030e0f0405060312031003051509010c0f0c060f061806030204050c 72
    0x20811040c2d0040c403030b1030003244841d00b00c219605990001d40e00102e407010040f40c0c20070241c0310710580d13a00700c0c403851000b1b280b0f606c1d150300e6491440101401c0800c0300740b400540000c4e68ad1090300002000c121141e412503032240d041c00d102c1007814480b2410760390741c0950710000c10030300da9035011a0b04a8001252200c201e4482c0f2421113011559030340304445101c401003a0f1009918180440c40d90b902584010310039089200400010300350072804d030400307650010003c00000c0c0c40051480c60540b004000408100250450140c1c175020202c07541108a00c400b0900104050b03100c18050b01e0318105840c0705410140423810b00068400c01d5036001d505030801c100c07500c56121510091a88100452404a6481d582e138440e0390509004c00394094160144004001803144240501c09411030a85003810f40002500305c01401c0d0011481c00801c0030352501e160400b2400190400c0029180b00042d040c5c1421400e46040010f14107444224011800c1400040d88429010b0a407a41c83c004c1d80e44164075808 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 67116333 1250 67115083 67115089
    0x403080a0f0309140a050d020a020604150903020a03200d02091308210a05070804030c030f021f0207050c0f03150612190606050f010f050a1403090a020a050607030806 73
    0x71100501004040da6608090003190030300c0c0c6481c40655080c0301a1602e0103483c1400e5041202c0ca0030050107640c4000914030044e1250b00c03c40e021513000144103d29034900f1003080f80c0c001c40c10740c4040c1d4002c1d0018404401d0100c011445500441c8008103021101c46000c180000b13071030840c030701079030155810340042c00703680b61440610b80d030b01d02c211500c5291040c5003807120404601500c900064800000c10007101845921031290445511b0810b4400b034502a5401011001c40003070050070001c44201910b4030600802601d42d0168040813100c481842c14840d050080d001320000740c1e000e228082d004d1507941441e01d1481030500d0b0180151802c107090300e138200100c40003e401d9941014245040f100080014019881c80345010010159903800504028060b0b61140d002a44030b203a6000b00700c1c0e413981c0c001190039406101800c0880d00e9a070380798400c0e18443c1d0785102c1c0481902c8000200f102c02040440c036819002e00c21242080810380f10000d0051602500100070081545003020500d50710b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 67117583 1250 67116333 67116347
    0x51308040605130305010c09031e0507180e010501090c021515040c050d020a09031505060109060305180d02071e0b0d090203030c120301050f091b0c1203010e0103060c050403080a 78
    0xc14800c240d00201e59a0742c5e5034600b100d03202408400001c500c2c10061040060400030409080c400740039503500c4500e00d4a0356078030380341c2d030f80300720064060b60326a1400003540a4210340c1e090005500204029039440f2310700ca0103001142492070050040031100c0302d001d8a140c007060302844d441c00b5445413a40610b420b104c010200c0c00d07002c1003800014040024500924001040030341c08594544101514510304141d032044117401407008503050008004092764403001c800b04903070b1285004655915003050360b4982c0c41d10003800c0b0416004400140e00c2c6150000341e03020446801e10351102046440f090a14040440c40c02040400f0600704080300741254940c02101c0c24600047c103407454031140b100402d151103100c800101d8103501c00303c010021351603d005000174045054812140d6403072311406001c1c8403803980410310260a00450200c211000420443c2101c0b1444001590f4071f58641e0301415504800748400c03145030b81070060310300c210b900c9681682c044032f40c0b0684081c00c10510480c1135030700c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 67118833 1250 67117583 67117597
    0x609050f06041a0d0c05010f0f0507061d010e06060f180c07020301240807120b0f15030f0f06180601060c060f05160201150f122310051308040605 64
    0x620f003da49007a0340f9644840040c44114070903014000124941000504095115118581485108000343d024240c1040440b054981d101c50001100c900c00000c4070101c2d4001034000350f0030361900801d12030720742d00000d40d5030007100c0480d1002210a071100401c100c6000c41b000224000344d000c004203044105400107090810300c02000403c80e1811b41d11400e2203609513440100410101017802c01c1030074000d00c4903001900c0600c16000e031a841e562908800b120002d0110140b0703040300d400203060301d05442c07610404090020262010b81d0194207455a4903c000d1040110354000d02000c10170104166011529512203100500b5890b860200150f4030701c0e50800f0165080d94441d4606c054000d814441c5510401c050401d02007151000503000342114034442d0848061040c090080c030004480400320000c030f0f455a24203001207a500e1030007681310004131018000d407840743d860780958808081004103020499043c01c20903030ba11440d00400398030101c040505032400402c4148505441000280702c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 67120083 1250 67118833 67118861
    0xa0c060e01020d1a03120c12131811031f090507030c0e0a1a030c090d081c060e01090b01170c030121020603070804061803110c0d0231020d020405040609050f0604 71
    0x8410100988d4501c80c1d4400c0046400070302102d0f50500815150386240f4480c80c1045100b00300c500458074008040344405000200002d1000c203001c580003149881ca04007070700c07030b0403024085401c0c140b801801a03ca0740c0d000c40c0100350b04401d400c1c243d0030f00c2e040072412142c00300084c3c0140c0ca070a03007182c8039035480a44140241364041000300c0f1151510071071a2015881140d402e90f0f20b5805180c0001055000507440340710604000301080b1800020300380c0c40c1035440d144000105030100100603078200a0801059007060704c144200b01c409000300000c0c42c100e4003000e00c003490316640d0000d80321900c1d42200700290310610500118200511a0340c0407a031044c450400064110340d034a01e40221010340c0f0104400049000200b0800b0030402d0280c403034090400e480710003490003168002442c00d0442502000000c1d00071001030740030720f0b261030813801c8038002c55000c540c0c034a8900d0040c4080c2d48640182d50085052690004902d0610b1040501c00c90312105036500b50b44440c4200000340c40820040030b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 67121333 1250 67120083 67120093
    0xa08090a030c030f02040b06030f04141501120c0602061303050d1d0105040309060e09010306050c09090c0c06060f1315090e0303100f0312050a0c060e01020d1a03120c 73
    0x8002641c4502c0758018601680c05039a0110a52040009a444022400f40101c0c07047c400d001e040c100c2c0039421500503074092041034104911100440c1780c00c80b04d02c101000308140d84000507501e94450300044205000d0786a030500c0944441d03013a40d0b60b14080da900c4d1001c038040ca0b403000c0800c0c40f40000d0400e2260094010400007140e40700c15400204001070403050340d40d100144002c1641100c041001000b450401030384810405000600030101488040c0c10561179074009803154062008603196540300a041240e5803c14201603003040d0810103e020303092107410041815460f0200004688540040110040400303020f01c8001a00c00001c1141281c2d07070064000c220f81d4628000e40040010b820000d640724a00050542d651b440d40c0e03480501c01c403080200030f1021030041c00c0d142c943d55544d4101155203002c48202101c40b5002181c010b4030ba0317840c0100d49800100c064000b0210341031917031720512000074407603035000030b0320482e80c48294035600a0014040c0020702c00f000c4c204084255050720 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 67122583 1250 67121333 67121339
    0x804030602030c03060414070203040b0d020c07120506012102010c021909150f050f120f0304170c010315060e040f0e0f0f010506060406030e030904090606080c010e030a08090a 77
    0x40d0503a0002c0d1498651070300c01204114203406c03c0d01c1641c2004000220458040c181500e0207912480381d070048202c0000005600a6805441d80450b00308040c840121001565940c0060032070ba41e41e5801241c05000d00000010040d82d54100303080008440c20b5101d404510a60054894540303e51049030002c24000c1000d840c0140c000c52100105103401001c18408140900f0900d0981141c01440c20040c0703540d4207100c141c032152031a507030541041d5410320280e0b01d40400756145c01490708074403a05100001f8042401d842c50965898041200d50444042c0420800190140c40d04820803a01c0b440c58458100500f611510700841e00c2c00c030140000440402c940d1013041602d1050703008680a81c021206032011f04000c020440156049400070041400c1007800580684102d1161408140e200c440c211074590f81441200c2c00f0b8007000300200075041c400c1c076054014000b2481141114011200881025406031000900301d102c0280580982c51700ea5441c01550f0300b00001c010341101c0102004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 67123833 1250 67122583 67122593
    0xf0b1f0509072f0d09081203130602030112060c170c0d0f020c0a02190f0306020304020112090b010905130203150907180f0513020f0f01020f07061d030610090207080403 74
    0x15184105110403c44a40c1d80180000d20b80a018000349040001d1007804021207400440c4142040c480404d5072580d075101d5108901d03a002d9008005090a440000009404200a02e601005610842c1e00f0301c40168150010395011001150110b04264031500094803409054018540050b454800150b05506c00e034400081ba0024600503809038851031444056141c5000301e11101a034100018000358240401d0844140d003600c4001c22454010000c2411617014514068900800e0041044004c0440c10301160b0600c0c00e20490442a1801005c5501210264079940c441a0060018103200f001311040c2c0c003a10b08010617051040c098110089043c2c1280c0064514003030081001040c00d1800c58007401c00c5403070141540c0c803c07000d05070031703c2d00584400344850f01945c4200e4190420302c4441e00141d080c681c074030b28640f040d8011900c0100c2c006401c0406d2003012504048070402f01c400c0f0201b03244d500d1720140d455008007a01c840b010842e610082e00101070b5075100c0c135800b605103981c968075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 67125083 1250 67123833 67123877
    0x30c09060b070b270c0915010207120303020405090a05040c050111030a0804022b060501210305030402040b040609060906051e1507050a08091306051302090a120f0b1f050907 76
    0x3a03120b580d007103841782c640300f8a020701e01542c1100d00c400c0c0703480b81d01c902c1c2170020307550318014840c4519494020502c10309050180d41520010704c07025003d5106403400e01441ca004043c100c1d421a40304001081c085a194454040640c040c01c0000c003d51411200810544a00c1c400a0003203901081811904d43e5074030008403421041c90720000f0104000c00f10f4a8001705840058008500c62026002240c5001100300c0544d4049074040c1080d80e5a5101ca001244c041c000b0f52050030741142c00c6ca0740000d414002507214400700da00b69101005056103560070000c0803c1c2a030440550b0b00c1051b89411000e10b400b0840c1c4a1814000c01c2952034070050351381710743c20b09142c5001903401500c04103480080f0300b81428950140302c8500d0b020080039041c88001032280c10f42500349400c83d036020418144640751846490003401e103030920000800703802d240110303030143c0f0050105c0d58044080085481c1c0b840103400040c0e200e01c125250040242064240f0960f414010000c90410aa800c60344046c80b0010307070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 67126333 1250 67125083 67125151
    0x10c030203040c06020f0307020d03110604080c070b03010e06120703170310050d02090c09040b0d080901030c081009020708070210020a030e030307080306040b04061e030c09060b070b 80
    0x18003503128681030400c040300054942c05041550004841c00500080110403100c1960f412204591410610305080301d042054000c4002c0340e200e48000c0c0400c2c04482c50141004200301411201080e40754903c07820540000c0c4030b115212100340e0007146807860701c0301c040d003c11031810046564450703580d11040759000c80c0e0780c40466403160000903c00d030044010b0303040002d801c060b0b8280103100c50b26400725808450003070407404c807000d0205d0b040740e8503595908001d40c03a420003005101107001604160542c3e80c000e407030603804a440d14101617100ea000e424024841d500c00008400715500d4000401e0196108100849100000300403640050340c403148404840319442c0d008000050b40342c81d01415082d0016041886940280100d000107620501281c0c0d0210040c1d40c04100d00d05c10501040180030380b9045180008568080014500044a61030041b68024003520441d1580c49050074200d0780d1500441802c1c2d030f01000700b00302007a10740d410300740c00034407030034500d14264080c8aa803510202001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 67127583 1250 67126333 67126337
    0x903030c10020903010f02040e04020904110d050102031909020109120206041a0315010302090a0311060f04150206130b0a1a03030f120609010807031202070305011d011802100507050c03010c 83
    0x880d15003c0e60809118101074401c2d050340c00c52601c0d0800399162501ea00040c0300902c070300c0e403110000c1d04006114521001680000d4406800089d9904d80107003c0c0d0411101c03404501c501400b0440c4900450041441d0160180c507445015405c00700c1420000302c0b652400d90b0404810440041d02c4081c01c03c00300b18030414940016124200010441c070020440c404480c10140103204c0d21040c0c0d070300c1924480031294850201c041900c1c404000c180c240c051140c00b1a9243e0021800050788070200300000050707180e40d0309850701035984502815104c61036010142c018840040041c03015056070780045004101e56a00702070b0700030010300091640d440580346084520002c12202c04001d81049101d410580489015105604201000e580d07200d05110140c015070a04c1104600d260003070180c0000f542e00700b0000d00090104254265140c40540b801c17142561074240b02010b0003441034025520340f64000d00190507000a08000c5891750081201074465000d01011440d86640c00d11400403c00303030b0340e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 67128833 1250 67127583 67127587
    0xf1103030d06030b13021509040605090a0603030206010f080d300c020c0111061b0d020406090e09061e070302090d0b07080f01270e0a0c090e0c0d080903030c1002 71
    0x151401c5880b80700041d000a50a0b010020b000c5c1c0180d4411201e02d10303601c07400000903220710f01d00b80010f0103002c56a000a801c90b140c10140f11b00c0088640240c029280203408070303145640c0e6505201b0600115100380b440641046501c0103034a48100c040003e1105221000c202d2414a0419411180c178003005074007004e50b4584100d03040b980c0520000310001c1d800d0900103d2070400207500303500c030035004241415148001e09100310420010040d107502007041c901c21903d41c0d40700d00700500003806a004808080080304001a41504000b8109114074820b8000c0a40b0f4180d0904100300f54102500400905030280b200745e04589440001c0c803c0a4043d40c035601c130038142810060201007019200c1000a100c5100510940105071103041801c040b03034409240501e801c500711801405007450702000c0380102101001802540c45400042e02d0040c001049880640e2a42d541d68040d1507001c0c1d50040211660600400c003248040d024480c07000e402d40f850601c08014050800f41400132518000d680 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 67130083 1250 67128833 67128839
    0xf0d020907020d090f0b0f0c0718090203010f0c020309041512061e02040605030c0a17090606010f0305060d03080405030403080c101401030c05120f0102030a020a030e01050c04030f1103030d06 84
    0x11191800780246110404805c0f000d0800c1c1580109101da2a4108454071000801801032403003004014014501407070409099044200b0f82400341140300c409a10030343c01c3c010003007042a44c030300c51074410140da40c00441c6480e54000500c40034024242407066000d2121200251a01e0301c0500320380e0880c800d100004507000340e2003509403960f458400d41c0078040c1c03051009221158000c000c407500103401400198440d000c2281c1194080303100f4040e003044c90102010301503036480001c0d0741401042c1c2601d585255400c460300c11011101c085a000341e12400003200300d00464007a54629070407502a1060300c1c074041c1c0b603454425150380402c02140e02c56200050300c4a0049840c440c815002d4800c0722656181c1d4556141c0910452490103078520695500c0c0e180c5101d00710400105400d2241c2d800255202e00d015650360009410948580c0c010034101982254a40c2041c4141031107136441421a9041500719161954020309030701c1c04841400c0441c1c04a031003a9000c102071703c03855100403c0410110b003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 67131333 1250 67130083 67130087
    0x10c02070501091e03140f010903120b0103092105190206011e06021b040f0f06050a050406050904030e0105070b0f010501120e0d0f0306090203130606050603090a020f0d020907020d 79
    0x81e55401070700e1640c0b208818020b83c2040c143d4000440340c1111b040708684160710b01480c00d04049082c058015031038998040c0405400c5656000d403240864810844401040010760544840e180d00030f0000070781003e00d1a01c1540c240d280314802013a0b00e002820146485034803003004085694150150380080010441d040d0a040500784240390381e1a00210b0343d14001020f50340b10078003c5856524010b1a00c4004035880fa5030000407400402041401108003846d54100180310780d004140c022080b0000119140c1414000c400850703c025040009641d1161070131640842d491010504025003040120045403810b00c03500c0c000c3c600c0c2528000954940b0001401c090030841407120424208111002903284c003244042c0b1252040c10088034000c1800021001403081e074010100151010007407101120f8440e2040c80300602c42c1004002e00e50304c820030000d280c00200d8000280b50320200039400142003a00e407d8040c102c02818050b10b54080d82c0c00104900ca08484101c010303400340400d182600c0e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 67132583 1250 67131333 67131347
    0x2040f021b0d02030307030c170a0b0906030a0f120309050a030905030d09060c110301061e03021002010b030a080904150312020c01180521010501060c05010b090f220203010c02070501 80
    0x14480002e120520707a00303802a403a8000248031a0070305944144000226004220500c3c8000e092042121a17240c0660010020040f0183c3c09028101010014809050003d1410101c5810105160042e540c503920b0700441c1c11034028050030107440e2500000050703004c10880a540d846a215011071506020906140564000c84c505c00c008c52100100003180e0401c60b8a581182c01044074405984801e0100f8050841584444d0b452590301c2c000d45035149446420030305580c402c13692100040440345049080e00c00080d60207526400100081e800604404014008a00d0150020a02c001c0703e00e8050312900c02948169000181446400d0040768103000840c0b500c1c03406d0070002240030009101440411680c01924001e00d440031b942c41c5c03001810034581c000b07128808024442036844040c01000c0110100088031550300302803520500d45040210706200d085113031014a010303174505200001100d0055a4880c90300851202400561004c0c0101500e0f10240d070000c0209a1425000428203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 67133833 1250 67132583 67132627
    0x603010b0d261305100309051e0609070b030705030907030206030408071a010b0412080702030a030c050708070e07030f020717090a0e010e040b1f0f0e010602031617040302040f02 78
    0x20b04104585001948a014a001503800c182c80540009110310320640003001c075000b014003103204da001d6040c01d0034280241028031f441c0c2a41540c0064443d8061503035140103500442481c40c400b400015422481a805594000c2c0f401c02140c1020f65290081005984140c50039580c0000000e41e0b2414484c0040c04903001c81210005205503615246500310540070f070740a9a8403c40700310003000144500041640c81240e00141038072010440c0d03140281041d008000202c42c68010204002806c050104250007201e0140b0174a080315524254200e006141c410342807001e0035405d001c840c0c041030048070048524010300302129920040081008400741084d0702281d000b610b600014002c01088003001d82d005075010600c850161901c0301001c004003000c2c101c06640c001008000100381400950080440d05460081c284a0340c0f140412600da21456070200500b1b410100320600080c110083e0740c40c90100018824100303a10b0340d00040a5600e8810408103440e0041002c101b040c0421058940ca = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 67135083 1250 67133833 67133903
    0x40b0a0f0801051903060203060411040e061504030b04030503040c0305190302250909050a0f0b0a0f0902060306011202090406180b030a02010c06050a0612050a05070f0803120603010b0d 81
    0x194003005102544c2c004040c080101000d4010003c1080e03070300e0340d40222002c003100201e0b031038985803104060040e0340030450309184140c643c46c00c145405400c1d0320496007640d0f000100354400b41d903a038505403007a41c405001101c840c1400c5c0d2000010440c2480380240d00ca25024105140c0300850400034a0181e10038249000d043d840c030041d42c41d1101c0003035040b040714100d00c004034a080702410003c0c01c040f1030b668003400e1261138114080c20000c000c05a13902c41ca04442e800c210078114520b105003202c02d1500001d410400400c0462480e40c02071000d0004030303051f8100546840b50540216044d6102544081e0070210b1042510410455500440075070360304c00d81c01006050741c0783e00000c01601c0500c00c05410301c0c0c0d0759008a5680c46032901301c03501515406640403010795091818a03580c0d8200c44084c2d4442c0201d540100b090034021107403008961088001754100014900c000013240000741a541d4150f60740d046078100c0da00d42c41051b4072894000c8902001441c00d03070141c2184181c20030b81c2818 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 67136333 1250 67135083 67135099
    0x106020303090c1c05030f1c0b0109050108180d09082a060a090807030f060b010e01120f06030507090606090603020c07061b0b0a0219030504080901080c040b0a0f080105 74
    0x912850001400b0051880403038000b40001e1808200181d10414200003400c06d01001400021000f000f00c0140101c205000c000700044010041c2803044400e1511041e000600010041207a580300d1125650070194811072400e2510740d400e146440e0404815086020943c681401c102400017400300700b24181c54034658812403107c210025007440120000c5030701c49c6c0e8010941c2090244110380ba58054840c0404954080d41c40e424041d080210084040340c0341410300c41440d005512406240054400686905000714070384440c060140401d80f80314913a1550302c850000111708200301050042103140c500080050800c3c500138040c012580200041c98010441c2d940740c031000107041812102d181ca0a07540422600360b00c102d2940ca141c1002e44a07420706414024a2080e5900038945000c540a101003010560081681925812200070b0f0100400703108107111035000c0c810f4140c1c0701d00451245880c2c1034031504070382141e410150381040091425036601c0041900420f04501400044032280 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 67137583 1250 67136333 67136341
    0x60509011704050f190b07050f07080a08011412060f0901021608120108070803271e010315120f061107060b100804240b04020a1107090501030b18100204031a0106020303 74
    0x260300d0f046e02810800c108140099540103141c8450103a9080640c002d000ba5501d6440d45030080007241c081c060440790888500d224031241c6414060400c4002c001005007096548000741d98104400090486000755000c000300a55130881020784c45041d8800c900d8039443d80344a101c00b120a203016002a000c0c0d80c400700303041c0245170000041c2d890703417102880a03400151100001d5448080e0341039890350045002c0380b10310008a02c065030151025020b03038081242e019807600c03258a08040d03105145114082c0c1c50504086202c600c1c0d518909030082c000443c8200e401030740010f50380c2c009281a1002c6603200b1481007603241841411600c410341e0300e8286503e04094441c121a6410f401500031541e540c99034100e044000d80d01318000418000b8411512080d03800400f5111200f1000c110926024002000c10710a14030310900707040c0d03608400418929611000000004804c0e4003440c1518411071000b444172242c18002000038612507910021599000c03800c829040c401a00141e00b5500188204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 67138833 1250 67137583 67137593
    0xd110315040c09140109050a03030e01271202030a0803070801030605010b07030e0409050717030408010b120a0209100f0f0504050a1b1407021203090109080102090901060509011704050f19 82
    0x1a4103840c0b005003100380c500c804c42c0040e501020164021070300182100703400010715801c20307079000801400b81c0715a05a21404450141204200740c0540d10038602c4400078490000d42e5043d0120592001d401c50b22208a5512203080325042201c2c000d0000f40850b005100b00f050034044c10780140660340301e0f44c0c1404019500542041c185001180c002c6542e0340d1041c007402030400c1010000c020110300340381e60ac07080300a441e1300d90f4001c2c09600d070389608080303a42203181440c41c608200041240040c00596049508100800201402d2074001c0c2101440110740c920300203e100c00200003c113034080c00f00b89001d05104c1a01c0d0000d002018883c640000f00c0c1030640030003440c501045030303440c0019003803840d203221400b980900540650800070030070b100c3c02e14080000081c000d041098a842c2540c5542e210345038242d00c104919250002c44000040002a00940180240c440141481e0002c110003440d6036030100001c0768142d503c0d82c4502c108590f04881401a00c040c000c0c681c0c40508043c1c00e030340325 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 67140083 1250 67138833 67138847
    0x100b0a02120306040207020406150e01081306150e09011506020606011d0a0305030f030402031e1f060510030603020901090b0604030f020111060f010503150712050405030d110315040c 80
    0xc00341074400040052007a540c0d070f42c11502241d500820420156484a20700408040d103280c12501148803010114580d43c0200000e501c81c00d01302281d4080c07090f0b80c0d030311040503081007580710700030a400103408640282d905003641e10801000000060021100c484004040c910394040c4055412240500c007090764401440d407190040030400c01e1154080c0745c0407400001c0d540c2c0c409009801302045c440644c11070702c00114003c80c000c50846420842080d044203069640c0b041d89041548940311060096100b0650802142940c3c139001a0056480000c2181101400c14000c0042d90b070b50010b10442ca031540010303014018803241081000550f401059980c8981c5c00040e0000c0f8204842404681c030405601c40b00d0030700724090b03e08600f480e404030550410203005031840303401004a071409500645032000d07c16030056694000000c8900844d00082002074030540356070001b002082e101400a00170130356152981d180195591400c100da403046401c04d070703540e5445242404413414180e640326a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 67141333 1250 67140083 67140103
    0xd030804021003020f2d040303050c0607020d050d050a1808070b010b040f03060e071a030702150f0114130e150108010c020a1b0515070312050405060726010e100b0a02 73
    0x14411007104861402c00310f61046c013032120984400017808010035074088041c24003800300b402100d0039034841c00707070a0780c5456105909600103101480820410711890b0403803500b00e080944000741e16211125010094596000295200d20000031103004000c0c480c1e07a460700500003181505d05141c10060080c0d0310300b249100281800d0f440d030001c11080035090151100408400c0b84444c484030b80414010700c0350304120b400d180035008000c440b03801e82d56007070303980742c070482c3d908504620030781c2042d00c401c10400b01c59114a400c20101c1e5102d10250306d0610600c1c20004040e0000d219a1014080342d003540c0005802403607440c1d0410000740102d68000a40a030750765444003150414032240c1107414425962540a60342c85840d0941d070364000078141008041c0d241c040d1f82e030040c1c0d1000300e800340410380c0c82c1620001d01c180d00402c0081c0002d8810850007540d540d2103000a541511200c006c40014207013078200000b100f83e003c00b07000c59282da886900c8018140d5041090400d41030200c041d4031206024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 67142583 1250 67141333 67141357
    0x5150d050d03021803070306150807050a090e0c030109050105481c020406080f1605030c0c0a0b07201504140a060507030b040204051e0f0d030804021003020f 69
    0x128213a040c45610b05448010f038280a01110321050b41d0b4140030025100300042141508078181001c40d6200c4041140c0c8240d60717010b00000c0e00c440c0350480302d02c001e0a0880001c02c0c98083d01c4452803003a9001c2c010403071294001c1d070002c24141010400101150a1510000a5464030168000e652920a03003400190031f400d100c242801ca85402c4031003014494030007040134031281100c81840031502c2d5030240c0143d0f8016907440d141a07031002c14481d4628420354002d02b03014002c003d80840c0d207114000640c1c0c082441c0360131504003d00c1d204c100f460b021007031600b2902c11044104100a95604c442c041c507038000707110000040c00180490780b0b9140e1941100c00400c00307070540006000d000310720066004da008542e04840c0e40d4035007400c2810080c0400d83e1134000185c28a5984942d5180900940c0c00345d031001042c0d807091401001c01c544203c14a1030601d03401070524101c030141780e525401070300e003254000c2d1140ba00c946001e1042054100213140c5030b006240c03043c400268030000e118141c4900248030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 67143833 1250 67142583 67142587
    0x204030213020a020a050607091415120403090f0b030604140c031501090b030a0c03050106050405010e01030519020304150e06040b0c091f0e03070807120b15090a05150d050d0302 78
    0x20703c0103e0600c80c8411024100b41b00b010103218901e903000014104640f80341c0703500010740300c0940c20407102c0c0356200400c41c81660240030701041001c24100d034540040c8282000303c00d00e40e640c4036900c0c100c1401e610064606c4c00101c2001018140f070300a90000c0364004909100740e1400014010b11800080d06000307141030606280d000c20307405002d00d00d000d840c5162800340c491400c0c084034009440c101401c0000641400700008000e03002d40305840507104161540c51a01c00014011002404028104d04103040c00d5044000d88650910086024500500307084125110303070340e804000d0740eaa410140300130b54044410003010501c0c0f0624240c00c03103280000995540c4040f000250140c0c1c0c1c15546121202007241e03009043d5400017044540035800360180d5501d5981d4801003500c3d0491807184005c1a540ea940c1000090072000c03c959100118015406200d40c0303110220f0700a1100311542d0a2440d0745900f440b10a1175014080c030403840003150b100100a244e5520741d0380710382c51501c0840600d500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 67145083 1250 67143833 67143847
    0xa021309020a182a0e0a0303050406140f0a0225030b0103030302071a01060e0a0e09120309070308040f170a0c0506090a0302090c1201061b02130b040c03060315020403021302 76
    0xe541200884484c50002c01c24400340c0c404080301030b03005450440d40031032a0700c07000b04074134203021000c00116901070700c8240c10245448408e603040414101c511049000030408440320781c82040c0030b81400101507000308400000d403610340c1d8600074041e50301503280b0030701c160401c000761611142e83e0550b42e1500d000743e00c07044140f5101c05001da401380d403001060100400851120f902881c00040407100b2104169080da86a041c64014142942d09c084140c2196a840070b580010741c00450308031612a003103901090343c0743c440d4485c031741064001c0103030031905440400c986455410100c01c059141c10140803003945584d01c0440f0f0298600c2400d0041138007241d072425599402c103154004580180c02c0410300d141183c180807407540141295a42e5801060001c220244500130810101016a501c1c2071521290380030020011241c050000c803d039121941d01300780c5d440784c0c0035820381f00701d00c1d0b00c0105075141107290465407032400304100101c6074410b00040015990344500390f103207901004c000503681c2a03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 67146333 1250 67145083 67145129
    0x105060619030903260a0b0f0102030d0c0e0a060801090c03060b0a030c0905030703050601050915031216060609090201090b03060607060e010908040e0f07020106063e0a021309020a 79
    0x800c815400768840044202d4050024109440ba84045d1410040030b0303003c50400c008c000c0b440e11030380c1c0142e1041c048440b092001d50300c00d444005140c184020030710480740014581904036040000000d13240302c0100076400260050301c08015083c2001d0040b41d0401e03007080c1850007a5a120f004141e2920821f550700b030300406402c0050040501a20000354a07802c00c207136a00710030b2140320f00400d40600000d01c280030006503506502e00c010050030604034004e480c4031041e00480036031003080e160159070b400092035501c91000288080d46000c0350103c0140005407540d1000e50119000140800c10044165201d008941616a1045001a011006104e0140140140d00d0000c00d00d48002401080c1d00d514200c2151185658600708032055950390000c9081e41d415114840100708102d5191442d084042c003c00030320880002520580e003100c103d8131403200352040c0e0280e0103810401030001507061000d0320754015420010306006095040e8042000e00034688180d60b52688003540040c0146 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 67147583 1250 67146333 67146347
    0xc0806011e09030507081f02090a0506031e15030c010f0806040f140c0306090c0f0304172a010c0203031005040b030a0b190b09090a120c05060108010903020105060619030903 76
    0x1500a030840300041c1c1c03200b5030641e4410307640440d41f0b03c2d69030034021080205880d000b16280d604010b015011348500e0034090090300c2e000500302e0000703481c0102540702020384451015100e10721088a2588211514003850304113042413944504010758082d00403900c54010101c140c0001c4141c0c2e00088060032111018010703c1c2c100300284444104d41c05201c2684580006507000b42011903800e501c035141c08420704407520440d1881c1c8040b04040c400200032030458100307006060401003156180940c5407070140902c5038450004e103188082005600750520b401d2080c02808801c1340011403540c140310540c003050000c035201d114801d50301c8012140064034240324101032907034403d0a0390b2103410718120034180001c80020f8010168a466075a02440c0303080c00145028010090160503489216240e030044d0004c00e160342d00500501340030440000310301300038450080000c1c2c00000b44c06580d500d0000d0079910007526092242c0c0040c85003800d0201d0309000d40300c00c1c006600700091807007484d182c01e543c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 67148833 1250 67147583 67147589
    0x7081305040b0117160905120102040602010b06130506070c090c2106120209092a03160b090f06040b0a0203091c0320070902180108070207120803040c03061e0c0806011e09 75
    0x1023402c1c03034001d0001c000c0540180042d1801a0028000b040461007885200e003c1c00c8414140c1c1c4046440400c0f07582807810041103078034003c4a01030403494a03442c0650588030f00e5038040c030000343d02519121940d40c00c41d505000c0080e141c0e00c14031250b0301c3c00035103031452000d5080c00382c414076540e804030381001c508000c50550900003e010140901d9840e101c02200c002c1c180c0300c039001e8024003442c0803004d151000030405552444003041c1c10074a2000a101241c00300c020040d42001081001089a22580029104007a161340c002c0d0f80d1010140144514820322021060061051428200010750040019083e640304446850400b12000740e1042c81d01e50540c1c08000d100c2d10020300c50003c981ba1300c8140e151002c003a00d51842c1750301c5186080340e46030b100d84148a014000b440c810b000045542c001141c210340584c607030120064407901d030340b821100711074481500b00c00c0e10240356420702c02601841101000a00703043d06c9524080e80007038092500c0024204860199000140c0081d0003081c40c0809 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 67150083 1250 67148833 67148839
    0x702040513060c0906090602010c051b0a0209010f030606050607241401030308060306091c05130e07110708030a0806130915150e010f030f050307081305040b0117160905 74
    0xf90f03003a040020b0314001c0c25002c0d100002d080580042001350050148003c403101c10740d034051914074040d00d41d902140e161460449680070342ca126101580c0c500814030302901c1d4a86415225500d546444000c4501641c4080d0040030280500c10104554051418204a00a01d50640000e14018000c01003c00c0c0f40a906124028000441455407003240244110320a804680d41a200d00144d10765400f903507100e1a215030000350014150520650140c11980000d80c81907660b20384505190007940f00840c0c00b0030000d600c1060f07081030350008205503802461420061032402003a001d0080c001a80184a2405524032108074012040c1540c070000ba81034220381c504070324602c94003071500503004201040b80091480740c404288200174403425812140030161a080031460340d607940c801e0301280602514203000900200b004950030381c0080200c00c4180e12030300e021a0030101000300321244901441d0400c00a42c907a0070346c02e0300c03a103150340d0000c0c00031409001021201d0b00c1100c09440642180f90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 67151333 1250 67150083 67150091
    0xa09020309060f130b04022403010e0702120c0303010506031003060212060a1d0406050a0e03040f05011b260f120906010819122006040c1703070204051306 68
    0x912401007082d40c00350540c034600103800c0d01c810b168641c200079609406001e0360030120110b801440c01800d030441665011202030041d00c15080b90640b1303504241d04c04800810f402d01080401030f410f11420118180c03c9a4040c00d2403d00400d0b56a03038001400346038043c4900002043d94114644102c10017194048030a651b240c3c070101c1c001c4d0070303160142c910758041c1d00c40e0703040404d004601c6c1d00300242e6102c0315188401951340e2600c0f1000508400b5081c902e605603106488809444144010301c080c058103616162401d00e41800100303001190f504d00003d0703102c0a1041c0001603140d00300c400308828a0000e01e8040b23022801c084000e4890000c2405018038002120480e040c03010203000d20480c1e0a50580340e0310781e80d40002c00e40780c00b8201c6454030090341401d40c080c0001c8082a46c41861901803a103403070500c020394400201745803030302c80c03c0189921141c100010091840c0c542c41c058203515042d110201400b02030b1560301c1c000c1c3c0b84000c1c4102e03107941c0020880601451803c84580c0c02410500c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 67152583 1250 67151333 67151341
    0x14010b070813060c060b030706020a020103020f0405090c0406020d17010b0705070b030109060e010801020705030a12090c03060911030706050d020a1b060e0607050f0301050111100c110f0c0604060507020a090203 92
    0x35103a01d40c503100031500e0720b0804403604581d1030089180c88c1200e01f650050100d00080e540118002e6000d281840b00b1000240400720701c5403603003846584580744409a40f50f540b030a2082c0a460001d60f02d88031010410442d4280d403541005010150440780d909454130380301c0c60f0500e41030b42840c8254000b840008400700000403030701101c1d0071800c04c4a0002c03016506c01c2e42c0750760b8058280c0c400c003038010301140c3c0308211500c03255118000304c8100c43d480785800a40e4001503aa8905096640d51007600c0361b40d1140c1100050002086808140d00c0d03080b0000c090451400b4005000c0c1d000d40020b000b1305560125018150502800c40095020000e0461114021951415000804407030b41e00720000d100f001e0020344c41600400446640001c1410146d00350313840c120045840804103000c228807130045070719400301075000d40100c41000c80c00d6280d905640c1c0d04081c00c81e1070b094100b00f50543e6540500c10802c0c50340c41d000112420f403400c52402a40c1c49200340085002d4003110761103250075520000400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 67153833 1250 67152583 67152587
    0x201140a060603060f0b04050108061804050c01030c0305070c080d02040b03010801090b01051801050d08090907170610120b0301111917190903020f0a0b090606030114010b07081306 79
    0x10406842d12030314100700141e115040b1100380c1c034850060300c0c01d220b0304100c1070016601540c550b50780544000d01460000c0050303050003041c4082034400300e5960b4850680354801d580c060051004400c65032408100502c1c000340c008042c002d2002000e0b0940d0400100d4105001403501210050141110801c1e502d50b9141c1601c0d00170300302d4400030ba03180d580c0e0308004202881c004c064060320b5000020b480201e0703420301007080112004620205d528104c10030481c07036183c0b5000c85e15440755400da1a02013412075420040d603e01d0300b00810f401e11030b0441603162041107401024201c0107240c1c010f000100309883c000070900502202c00c90300051310000c20403480c440441030f0000c90380101a90340750700f984444208112985016290242141d00d4000b0702603010055900001103580648100d90086a84002560801c03112860950711002c0d840d0800c02881c5013089070b643c00c0300040e0020080207111411032000703d0300c1801600f2070050005003003000d000340042550000c1075000f040e040e21329030319000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 67155083 1250 67153833 67153841
    0x30609060303020c0a0e070c14071226031308130b03040804031707020a150c02060f07030905030a02030c150903030f18040915150312050301170309030c090402010201140a 75
    0x4040c86090040000f10307454440001250107030043d81c607100f40040c0d40782e070788005060112900e41c012b07110704180000c4101000040070f0341940141100c036103d000b600381c0d035481840f5007088403818034410400e00002c040300e11401d58586421010b59500d800070300081400c811200e5001312031440000c420b00040c091130301c0c001e0044901c54820300b05481c440c4480c000443c00364400c041c2d40325140d02c0c003c210303691051075140d544108916008241781000d5000480a422190400582a07404035a500425420004401c0a41002c0307005000b40e10f103a50009a84040801c01c40307006e2039905218900400f0788409a48910f40c0c010162905d0380001500c01482d6040100564041700700ea4100340100d00301440f881c0c400c0c03508030310380c03400d9050f2200055000d032a2410b80c0002004000b038002022800701000800100e05035980d03165654940503119116aa609000c1c40c1e96400030065174141d90b40000b0200100c2c1e209854034901642c2e6400180c1c018070001e50848030042c030100c2002038111050380 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 67156333 1250 67155083 67155103
    0x7080f090316031e11130f060608010b0d0b01020f060a090605160804060b0d02060403050a03090b0c060f1e090715020111040b0310180f110306030606010e0103060906030302 76
    0x104441503030201d044141440c040c0b510000c0e0600300428003aa81090311070503510003c9014030315001d012904013000c580703008540c090410b81c1d40c0d03807041d0802820b2140c1c040c100c0100540d20708440154103042c0034130000e114150310305512950790181000e1a9000b8014920029454030940c0c00030f00d801c030190301c094035188900302d400920305400150003909a03102842600d50f60750343e070161541e0340d50b2520300401901d0040b560210003100a100169900802400a103100f0743c00362000901a1a014158000710741091412110610000d043d1100c000307030f200c2d070011140701ca0003065201c894100a101c4a99030f00c0b0703c01040c410341040358800c0c0004a03241110000f900b80483c19000e08412822160750080c06446c0440811040000f02007010103140c014910610f180340003640c5031030b891404455020b06138409070301d441c5217503010003403446013035550905045804c2ca1031802500082e100c1100034034642c1031040c1841c0c601c1340390f440b0b50708c190041d140c1420300b0065181c507824003031340d10340c1001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 67157583 1250 67156333 67156339
    0x6010b070c050402160b0403090b0d09150902060a050d0f0e030c0606060f0703030902060f04031b09110f070c0e01140405090a0c060c03030e01020406050405040b030703150902040207080f09 83
    0x3030070004140c2070510880342428044526101340c1c0a8564484503ca50050800c0d03080001d440d0020542c582d241005000c1d122050000241200c101d150403e0245449a0080d4545107403070110809600c0310000c4a1448401d89000d540d168080800100182100b0204251682c903000007207000c460000014020086103408484560362020b04100701e5214040300450300d00414032034400001d000f904621a00d0780700410701418580404500e41541e0050361080e02c201c085006ca00001c4440224140064640c3d0202401108840080010507100304010815448400158142400ba8205802c005883d80341602d00b580d507500c0e00340e0b0b03201c0e018402d406481103250101045002c8000901040503036802407031440c1c40b40c9840400c0e220054004c1c000c3e0300b07150303c2c2c6440b0740d2400b000f0320080c4042c112039150f0589aa0410090004407507a4446080c02603100040c140041100294003940c0c0e12071094020440ea25140f01190290040010041024078081920080458080d0227441665416 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 67158833 1250 67157583 67157603
    0x4050601170c130303030209090a0b1509040b0405040308061c0b01030803070210061401120504020d02061c0c0306140405070e1306080f031b12030402010302130806090c010801060216051201060806010b07 89
    0x540340108840300012f5a50703001e44079100c4c2d800c3c0600440c2c050200000001c0c40090b490008402140581d4000c8504074001007009040240d00c1c50b02e40040840c503a00194501c100c40c840d40c2c0c2d0000240418003001d02030600200004408602c00c002e00034000441500c14000d80c3e07a68245005041e55024442e40401c550b0003a0004c4a407180c80340c0392049800900c100c0c1d0008060b0240a07169101101c100c4030300a41d0b54200c89407071a0380c0142003141070f29540000341646840a50480c82c01c81c03041072441103080c2024041130030340c054000911203000310f68030221014160b51a00c0140420391081c4000d02460340701d07484441d03011018040d11300e44101d81407000f091030f00400d41ca94070503c2c030b14482c4103c10300118002d54032035801b03010400000d042041d40305446440151030001c0440b00c0e120640d101007640805540e120030709600405441c002820a007880514040622000f03001c1e45009400b44950f5101c0c80d4825008070008069000c1521080d5071201c02c501903580c41001d080c0c0340d1600d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 67160083 1250 67158833 67158841
    0x90b01060509130c03090c080c0108060411120711010e07080c0a120b0c0d05010e070e010201050105150705120f040320100806130e0c01020c04050601170c13030303020909 75
    0x590221010024000c3c00f0400030321a4141a0300200340051404003010b9507500c6040019000d090081c028081903401010070400746c100060126800914443c06981800751070000612041d081c1d80c50319500040c14030700b40c2e60340c12088650303002d040d07000117480d03007090390102094030045070603000e40303100c142510005444a030038400d540200c0c1c496944501c03c03182d45807001c51031042496810445e140300551928141c1c2c01c0004c11b40c3c200b03800910340d400004083c400400d4105e1800000904280000e00c9190314040c0050201d4500004091000c9800a030500404c60207009901504039181c3d6000e4551804040080d600e07089804201c40605111000c2000480c4941d00c4448540c40200540766250b00fa240480d10340d040900342d0340d0010740c501111000e0100900403400310200d01c00090000038050000240341c200119000780c0180c3c82c00051040a036441070b00100150343c1043c00e4500c541301d4180080309072183c03861038191024040e0000c410980d042d002841d01d1a42114500c405484d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 67161333 1250 67160083 67160087
    0x2010e01110a180e01061202070507061e030b030c010e0609120a0b07020102130b0a05070c0305010f060e10090203070207170a03031d1c0203091305010f06050403080a08060f1003090b0106 82
    0x20507004144d060480d540042203078a1203040d4a629030038917031801508188070360b91020303e0000325400100104540301601810032a807002040c01c584207a03e801e0040004031390100f903e807030319101103a0400203103280605582d00d620301222821400540f8074420700c06403081640d198490742c4030440b001c080800108440d60705c140241c5900980030728440034010319042a445c0280c3c4420803050030702c4030030701110020408034029507009500400003c910700304240303d00c0301155a203801c400360003554103060103a0792203041600000d550b04540d00681d41d8a4504041c0d2030024107502c5410a014540111482240080b48002c1ca043c803940302884070403030018141d0391001040d40341200301c5d80115903e01c600301c2d5074962540303100d8141c015245080052404510280400b0340d800507510340751801044400d190300108001400e00d444c20600f0a411070780c80d1100ca1040c3da0000e000c0240e4000807500707555502034043c500c00001000c4080000c5c081034058060008d0341030681d20900354500016601d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 67162583 1250 67161333 67161377
    0x21b010302030a15030f1e120305060a03060e010b031c09030807030e06070302011e02071221060e0603070803090303070f150207050c130c050d0e101d010b150f0a02010e01110a 77
    0x80d234811801000c406d9550000c4005140091402d0340c000707041d003800130100d107070b9100b401814250400080788000d80ba000741403078100300c12911400d50320f02e44c034178214082c0d100100009032a4000400741d0346480030306080361181c00c0701522543c0260002482c00801d5015071050b0184441d070104041017603140040c0c94101e018203207000e403842e0181e01240c8801442100c10300e0b803200131001410600786a0790307140c00444215401c82004a071100050100c5071404000d000000c00d5210005c610780b941810101380c481c022103000804810100c0d0000c070030000708031007050850212a8085440b20058203041d50b840c03000c4000540181440402c0c6e0300c001c2c0c0c03240207211300000380340c0711039103040c0505103408018559a01d00b81d1840c00f5242210409000a004070010754900c013080401400514603017a00b115030b0380b10305520808001c0c1403181500d950100796110111030034900742e1503201003d801e03409030100a4108095518103003040100e00c1c25100034014640c026130b03032640c044112200f03070030301c503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 67163833 1250 67162583 67162643
    0x40914011802130e0402180702011401050603070e01140c0604080a180e0720010c081608010e01030206090d061103011502011103040b04020a0f03080d0c021b010302030a15030f 77
    0x109141d6052000b4850304c501c0300c0d04148050302150100c408407001d081d1140080d17918a0050b5103a410b101c0c80342c40052400c501504089034054914140288050155580c440340c02e4184140801048a40d82c0c102d810369125956200640b640d9162601d8404680d5200742010008146030382c801455800110302c8101c00d40315002181c00d11612038000984205035901216400740c91103800380c01c4010401e02414414050382d843d81d9070f1904000d0302900c0411503d145100c02c000084004104120288135850b0449405039a035a603103c0c2d028011038011462404090206400e1021004840e507080d4019412602c106d5019550328402c4107040382030340c180c101c007401098009c1c00860b01007001000902e0300b03d40f00034071020003199982051611145170360f0099805120200380500038a00074041d007110440f0b40d10251040580761205103030041441401c240c101640400080d1100c81d281c0d0142c0809031440001000c0d403556464030894400041c40d0132252804036002c0e821180d10007280402113 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 67165083 1250 67163833 67163857
    0x102070b07030506150414011b05070513060e07020703050c031603060e01021b06060301050609060310050903090406030c090b04020f03150a0308070501050a0615050a080a02040914011802 82
    0x658980000c214090003001d40181e5005e004c5102e422a5091050010070061400e40c40050012041500240c43c9d11004003401580340c220f00300d03120000740b0110f00e15090b50b404a801e6940300398031600300c0c070061070b0980200d411502420240070140ea00010f10a0480c1d100b441103034183c2001d08141070700e0703143e0281c41c640310422280c2c051001034440d030000c4810529003000142040301c05a0301d40701410401b091409a0707003002c000e0001c0390400380102d5a20001c1a50500c0c2541000c0c404a80e4611405c1031403890a951800411109001402224008100100f00b4411a522410a000420319a01c507100c2100c3c03130420400c1d042c0c2054001c3c0d03110310b0a501d40300b40c10350380e07211203400b0031660490141fa40550100800700004240f10040c19145010b000000391a141c0101290104c41080e008912000c6c2105805503085510504403030518003a49003000280e1601800200640115000b0055160420040d1800701d00c062000604030b03180501010303040340800c8400d10880c440d015094071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 67166333 1250 67165083 67165103
    0x911030f1218030f01050f0712051b0306042408070f260c0604090506040e01330512030a020706080105010e0402090d02090c04050111030331060203040c050a08010207 73
    0x10701c514240c1c042c0a40d8042c050315425408104503600311841100c8280b5022181410701c03811503071080c0d02805894407908100b02c14100740c511041d91030f003400c801c0c041c050700010004100e41c4440c1c00c0034045c08880c1095492810018004242c0807101c0d003e2981180b158080000c0c403003024400032350489051030044c0031036035450040c454032410406001e201c20300c00d014245c101515020004c1000380030680001806040c00c2040005458441c034840c0c070142e0400103008681c280c242d40d40c7c000b2490000d00e000340c00d034035440c40c5403402003190f0160b44d2011740c0d4220003d02c004080014031035681c19a00b40d40709141c80710800c3e030740402c0a018150018046441c4614181802d90062000c0c0074000c00c1c51210708150b500065001008031400c0e0740244001c602080f641d40c005084480b1500c650000c1e5045141410440e10b01004240301201202a5080300603020b03005c0c1d04051221a030081400d651703a251906100c41c682c1e00520409029507101c0e040012094818800d4a41e09036100700840 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 67167583 1250 67166333 67166347
    0x2090103030503040f0b070801091109180a06050d1103060f04030807050319020304050d020c0d08072d0309080601050904201c030c05062206050405100911030f12 71
    0xb500c0b500010402c544040c071962148011030318110090f0711070b9525680d003ca113036051600d008183c411482c3c1900088000303100000c469655410380786041850344000100507611740541202030300d4250303c015000324074001000140700e600c10803d41045000d078104c0d2051340383e520480d10840d90458024000030a44804240080e1003a4000c68100380c144525107200d40c600440c1070101d900542d0304070390710b500100e0074002d043c0c1c060100482e000c80880b58107581840329141c8800324071401100601e641e00014120701c01c5045240d0009050705580c84150504040b46006080041c1c40d0140c84514401d420002500e850914030361407145038006100001d4919156034009403e03506003404d0751040d03c215170081900c0011610148050017940d40e9151402c9504005040250180014803c4111000b00080c000b44003290801541e074014000242e42e80c4030f0034214104600745071401e428604000381078051000300032424009020440a4540c007544100d040d965030000500300c05a0084d0600c031070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 67168833 1250 67167583 67167587
    0x110309031c1b0e1002071203030f0204030501061815050105070201030207060b100909110c0715020304050d0b0105030f0a02100f05040308030414120a05040312110a030908010c0206040209010303 85
    0x1d03481d01d00040800b194a8112103510901010400108000100f149041e0201e502c1e004600c4805008540007070030b8441d00f0203001c8501196007010150600d5101c1c0300345000261540d0441340110f4014008011507078071546217000d4181d400c840110028209104040c5595120076107008503101612024079252080c0d0065002c0c2d0081c4c072040e20001c0e5140b2409031507481e5803510080c001ca035960760002c0c1e2402c041504007190103800c8145404c01061141c4d20045a000550030140c90004501c000c041c812840700b24614444c5402c4180c000400030000002c1014101c0d580d13069460444c280d416003100c6102c51036503014015000381d8444046138504050324040e03404070240c84103030b182007490503850340c80b200006c1e031082c0c4044032004c038414804003a000d418003605c02c08500083c022072070724440180042150195000142c40e066151201c1d00c5003c0c066078400565030b0116003034a010780303114140905002e4040c45040015403d1804098010344082a024891a801840d280c1c440e400c0d6241 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 67170083 1250 67168833 67168867
    0xd050306040f020909150a080a1227080114090c01120c03060305060f0a0501060f08010e0c09120106080712050a080d0b0a03050c0a0f03210311070b0a11030903 70
    0x41c1c8003207a64200203020007a150040342c103206186c00c1d000c4909580300d00303091010013143c40d48104540d41060707401d04002a45c81299600401e003520b4a0003405412201901072401c0f03521054120401d040000103a170304064004415081c640300c070305a0503a9442070b04540300c040c9c22403003030700040c50940c0d406401c4090345d0040f051060140f41c0003030080e490303544452174041c00b03131030340b10b08414940300300000980103001da14090070341407074840c41000e00843c2c017410004060090f00304c0c0c450b80e1000503682003208016140340303d20081c002c188090508510b43e0080c41140540c40fa00d0040030000f20301c5141140760b1141040d882001491a03040944a59045800442e21002a66165105500650b45103032501003d503001d01d01600060580c8810070482401661061305c08481546003080411101c0c0c65404041e01c070210101c80350b45000004030000c11054020030703d41d40c00882d100041c8501800c07014490300841504114035503d0301046031542c0400c0b03c804842e6441004407035030001d88185 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 67171333 1250 67170083 67170101
    0x21807020a03120e0d091a190309031e110c010f02100e01150e0709150903110d0501020a050c0106050d0206070305180607030309060f060f0512030c06070c0201020d020d05030604 78
    0x20001805001e4500705078140307201000c100b000201b14000600a0103a1494030a1a140008105030b10f07040241c2e144841441c20512903009040d40c074813004003490b00480658071913050050350180009604100500b0307111a001520046101c0c48100b01c1d0954010504803c0711135281e0001c10841038084640009088682c16007001c65417540d8104900840c04101c601c0030344000300003a2507918210000400c0c0200c03a81c8400a0f054072423071a007025540005c00c071002d580d08140010804000140801c0344035100b03100c001c1596200140c000d042c03a0380907001d81310361903002d0000d212003651001000002c0c0d070100806075108404008030b00002e40120000d00d00850340041c0040c032040c801d000216a038000b03074401d902280d100ea02c41c0003088164480e03c0d40e1a034082c001000715a06000e29480e05003110302810380280c10b49a001b40ca07908040041c2c90a0409810885420389046a00100202c5603540c04a0152290900211740180080340d03241041010f556214295030b40d010802001d017a541d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 67172583 1250 67171333 67171367
    0x1180209040204060302070312090b0610020a12050307030e071a090a03060f06050a09021801050c010902030f010c020607140a0c0c0506070c1e0e01140402090904030903021807020a03 80
    0xc14000c032034849002901c0100301e80d440051b1102c00741c2c1806880c03114003801c0d5040300391074032001c00c0002e05291859a080700055a40c19060140803800381c0c60965070314406800820a62008110700e5408001107109a600e03079024042d220741010020340c0c540c010f000f01c00b002c0f0741121800000c62110005444004001002e1140440e03590300e440d8200c0710003010840d55035032131320014001c504140140900412004108525004d9803401080345010f18451a50400c6400120f40307141c4002500302908036a0000c060350207100c140d00155000b030074285034120250240c4d00c00030350754074025014061076030203a1900300d00c0c005a0143c11a48101203c070211003080c3e25a10103e2a510789001410055105e0301600d24050309103001c0b0704082440ca852110381a007045030a02102d00c1e8154807604540741c00789103405502d001d0001a01074011003000c1c680001d0000301704414035a10107920000c030790090b0754402c08a00e10903010a4194011100c1c400940d0012500d07500080c41800d54100c0e0203444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 67173833 1250 67172583 67172587
    0x90307050909061b0403110103151a0304050d0c0c0603050c070b070806010e0a0501090506070206160c030b0601050304020d020d14030a03021b0703020904081806030a0507080601020106030506011802 87
    0xa540007a41e40d1206495040d000e42c080c008000b00059550074040f81c038054603481c80d06042c6075986e820207601515807144e04140d111086040d40c070182004a0010300b004511000c10600300e810300d401ea6400845090b1180d10500c07902020341402603407907100e0345400c041c19900e000c2c100720040d00641005885001a003204011900100d142006440c0c040c54840d0341b40401c50404400041a90b40c0641c8164405c0d100e401d0b040006a0b00000d04008441003075590a407034050302e0000404500909900d8041d01c0b50009215082040034041d85003524400c1c0034040c801d45036180111000d000403540250009528540700026241026441c502144601100401c0140d400c0c00c0c9811904801c102c0004280c0118003801e20810145210b80c1000e110350050000e03910b0750b000a00c00101c05400070301840c4002400d101e142c501400c4003038048101038860fa95070b00b40080b0701402442e04440490003c4c0b03480380860960361043c003c030070449801800801c456403c248811080c42d0b404280c852402d40d003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 67175083 1250 67173833 67173839
    0x3114091902070c03020102011508060a0c090b040e010e0703150b0c0f01060608070f030203040c060302030702030c0f0304060e060a020c041a031605010311130603020d0b03030d0b13140c090307 84
    0xa5030006002e07103849429066640c0746036100180c2550020450307110565030031041880007000000380c155111480040102e80c2018000341990300703804540002103803000028011078820141d8040742d040310010503452074039545011084045078a1910040c0491404400400102c2003402c003600b51001d02c0415505940b00c060340480c00c681c0598001c00c08101d1000070001602c0e00120241000000b0b41415490752034070f551540c42032000d43c000d10040c10b070f0100100d4000d03482001900d2000400200300c0d00031011869050340d072600b05100301c20000b401c400b060003e60405200307981542600780c00810002c00c1c013108100c0a8044c00701440c40e01c80f40100010856a0304008094148003412850101d81e4100000142a602c600c140c00d1000c40d800c0282d81702030000c141b4020200d5040340f400507251190341d075198000d418200103007a4144004903440d00b030304445900007442c50304112590350301c682c0f00c00350342025190240c1030703041c000506500090302c2595410041051100c000c080e5030303007551 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 67176333 1250 67175083 67175131
    0x608240414041109060105070302330702031c0e030d0c030209030703030804050d05030615090310110d06060806010f05222c010506030414010e0102311409 68
    0x2821030b4161591000c0522100c014104960301d103030442d6081c0f81803032400078142c40103540c600d00e1041426600c104801c0c1000305440342d40c21140f050880350001c0a290809540c000d6513900190710f04a40d540180383c2d030450680c0903100c0c0c55030f480100c0d00070310308100b07100b1121001010003403c0c100505400f0462102c595400384407440145200e620360a0540c2002d0400a103443c55100032801488020010300c030341030792045003c00400c1e640daa01c0707503501d21001001c0707420101c0044070401c0450400444013a2451401d000d01001540328808002096650604440c61101610102c0c04548103516074064644a81e0040c030401d00c0da280003215900c40c4031154003000a83ba400301b2800c43c1082d151030070a0007282040d900805403000052010750610740019000c0c8070140c0300078841c00c2104516116400290004191050118021900d0b920002d049018986106108005c41c2d000c2002d40e40c030b21005003801000796540d21444500401c0e868060200b00200035291709150082c120042480712 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 67177583 1250 67176333 67176371
    0x12020c070522060504020301030803240d060504030f0206040308011701060b040906061b02010509010f1709160e0907050103110705070b120c030402030c01050306011106011d0106082404 81
    0xc6420907000702200c0c041501008a03040f6030805072045004100400104032080d083d2a04a0f4112895855100c24014100500380c9052012034121410350f40c0c10082c0103a55120a110f240643c44007601c113110080c3c200e8450f0003c580c001c0210700000c0040c000d00e1010002c1c04506103616000282047e01c403900564203030045da11100d1041d498600c1400001d5022421b403030034a121842d02c42d0340c0007050780080c1941c01481ca0007030400004804540196100c2c0c2e80c020346140c6401080742450900042c804d8650000d1000082441030b0903000003411420040741c140308d0b41c41d40000d8040a8203060044010303100c400e009000a070310601c09080440e400b804090000c007405100c0310740d02d56046d4450200818000c0560444100a0003080050313200171450584070b84092802d0f60b5039584100050310440326226a048481c49003d001150300d98001c144a0388500d4404002612030b82e0300c901c11210100c04484040700080050084007c08058001181c04494010400f196865000745108560 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 67178833 1250 67177583 67177609
    0x711100c02010b0a0f0b0307140304030309031d18060102030708040f0801290f12030406030905010e0c06070803040c1208070b09030a0c020607050c04020c030408061612020c0705 78
    0x24550310200010500e8091003210031200054684600591814445000d45080c510070b84440c400c00000282c01d1902c9042c0c00c1c8984840c0e080146c0e01c3e400c06050080c001d0240300c2c400c40109a10b50621041481406540303080c0807801818000340c0701030441c90414004c0050b01c107906500c401c5c0700da800000c0041700940050101e450b0010350349031800c45602c0c02e6074a0043c1c009010074404507050240c0c1034031144003180c183c2c256400c013200110b1101003040100401104540380c000800c001c622280d05401800000d4020700092040001011000c1d0f04e601c203119030309a00c044204214070001c0c1c9542c0c00380d07600c5405260407000c010341d41c50f209150010b1400d0211181a40040c00500300700032907007800e402000c20b200450030002080c40240849050540191113100003280010802008000800c0c1002000e08255200c80c41c40000542d40e800034020b00c034590040500040650080310081d96010380e050307a40030310200440c50f109000350702401590405004640001c070306a254118035a4207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 67180083 1250 67178833 67178863
    0x304061b06051815040c060e010c050318040e030405010507021903020d0804031b14011206050604170d0e010c0b0402030a2103060e04080d021614060a050c030402090a050711 76
    0x15403c1c0501050600c803022071520b691400820a1001082081b00e20205584081c1400701400c100080142e903001142e002c010054030000414840d003020b46843c80407102c905643c203100d0300180c200c440e41c6038000d5008050000f4010301250001d40f9006103400c0000e9400030003519103544a07004100f80c000300340401e81c0c94443c002000c008111a04901c6180f4003054544642c85070300b850410440c503e01c103007115042201c014150040503065500401c0208401080340740c2e81c80d52504a5001212a07600308405070103501c15561880c0d001d801d500303840103016520703800c4030700c500d641c1c1c017100481c0a130046c0c3c0c05100e04800e0703a001035100e48481030110700480480030030000002c1c0082c161b49490304804400c2e01c0c00300910001896613825204400071002c00580c1f61b411410760015400c04400000d400d421944040701c2c4c0362000820514060341040d101807181d591006c014601e00c0c4010f942c000d420411032000100c1841d280d03030080d9042519442d1003541e44100d0240d00d446c0030400404004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 67181333 1250 67180083 67180111
    0x11e0504030b0609040b06010e2206050f1008010306110702030109050c04050a09030e09040503130b0c0106090932010c03060806010f03021509030c040c02011b0503090304061b0605 79
    0x1c10301004401c22030380860211000b00b20352a01c0e0751841ca480c0409002d19051001d0b404d00909560354213010000352185900d1030902c030b0284c0e58403d5001c0c2003a032060074050b0708080003550031410b003150000400d84a40d110100b1591841c4d403401d008050240d842810140c0a000c00710059800780210500346005000a02142c0c4c021020041100c030064098600740e0720b880300f410000b81c0c10054032120b5000440d4070364126640ca08141d4114402c04600c20b06840e803001021616107000c00241c01c10301429002003004544030104a400c5414042024009080d80305200c0c5418145060b0703440c4188000300c0c001c1450100c0c8000d10b080d2292144601c0110b5212102030000500070000140100f0840340150140c501d90340216148030140004804841030001d0005030a86040001d00e00c502d0000d401000100107000c0001d000b000849a440003502d000f501054086224a05480c082d01d82013000e140b41620300744040e07074103644d4240c5e0318004104c40c0c041000407134981e20405102e0418151006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 67182583 1250 67181333 67181339
    0x6051f030509010213030311070905070206010801140118020c01150b0912010c08041e0506010906061710050409020a0302060301030c05010f030e0715020328090b04030b06010c02011e0504 82
    0x14040c0c500050145820740c4c41440116004a2082d403900b0481c1c0d09418820341101c81883c0c00f60a00380c041e00100045418882484140c0b680042d03440d040f2158031000700304a400c5041400b180150a00c28610504487c00a550184200381d0083c269000f1a0b4000a501c404503030b82c8034007402d216401543c2030000800c0300071860801240c3d520803165400000c02441d03c941c04040d02c6400c010f0000f801c5c3c00200d205403070a4240c12403001c003072143c0250480b1029a550300f005001381c800d40c0203002c0000c6148400056810f12292440e00503100302c56144001420101403000410003410709a900c15a031403000070158480c80001c0d4065070165950015050602c00090140030a590000c0c08040c9070480c19080e261012440c28161007140c0e40300c014030040640c049147d400f40c1a6900c41c504500d0066150080c04150020082c0800e611194015036942030310002c0b600803480040c1c48040d84c0b000041c801d6101d03c90380020a84141001c8036241c161322401b020000800f1a4100443c1c4005414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 67183833 1250 67182583 67182587
    0x1050c01140115090b0a03020306030f100203070f08040308010302090a060f03060b01020706140d020307030e06070f0e0f13020d150b0a0305060607110d02130905070510050c1207020406051f 83
    0x240d0f110b840542003510003035161001e541402c1c8500c520748020142c0c04008217089540500c50622030340c0921044451030030595980b0402540300b585e049c4041000842540141c3e80203468491260340c064440070056840e5809200072004000c1c0707100d841e01c0c2c0d24100850040c220000d0391024602909000840700030361400645400c5040d080f0740280400441c58240c140440811955421182c100141e103030348446100b980500b480703401d40c1c0c50b103002da0030070494034990052210302207000d6075807840c00100455062100300601c118000d80c01040784110000111043d03001456240e20b041c00c00100c8042890307040070300c0c0c046500104080c10000402242480d454052127030041000c0b00e0703a0341350180343d51302c000d005a0401c078014041d8a076540c0c0c000c10355950204000d818407202e402809072030920303d01242c580c0014003407684904021924000c0e8a8480c05c2a01e403000403100050200f1006134418200c2500901030483e80306445803400b0815403503413080200c00070010201620250000600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 67185083 1250 67183833 67183859
    0x1503020a080303160c020402190305060a050a060e0105130302190608060a0b0a0e010c0c09020a021e03030f09100c120b12120d020c01020a0203030117060610050901050c011401 77
    0x1c0502da01c00d006110f07400b98400d080c184c112a541c1810391110041d4400f20300680650440e00310b00c4a01555280d5400d5010f400282c401c0c14221303403101d62140c444040061404031350080b00d00017212a6003545042d406200241800100d40c1c03500b4801e1603a0b035000030107110880107180c20f6403203040020050341e5004440c007600908200c501c1400d80f41051020719a40c040d50030600d080007005024081d0f43d0b405501d4007512031390400c01d600b4100d515034840a010b9401414140010302c80d03a01401c18800100a0001c0c00c0d01264014628503102c2400000040740301a124420174020714036850780764580d0b8880c40036a0342840e00d030501404203070101e1a0454142610650050903194000c005444021408a4403040485191071312040c0d91b07d040c03402801003401a040c076602c000303822501e081d00003003d9412100d91031000e0745422503100041f900c52109403407441d04101c81c5003403021400d00030406410001c40c10324100b400e080b8807018881c29500034440500e402c010032001070103e001d502c05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 67186333 1250 67185083 67185089
    0x70c080601030b06060f090405010609080c04050606040e1018050709080a0c0603050c0919080111130e0a18030305040c0614040506180603040602090f330408011503020a 74
    0x180c611585151030b505814a80180304a00c942400030304010f01a0000c010b441007050090000c2000b9a10303400084c000c1850fa0240072070500c58805030071000e03c0c050180c7d07440741502038141420503240119043c0c50800c0544400d0380303114030b40740c0441d035040703903c40807031107400c010801050a0624200140a0489603081044540c10000702d20011551080d00101222420319000410f46c0d603205c800040c500130345480175845100013051141c40d480c004810f006581c00d5034000c0080340e8041808064a1017400c2c134a02c0f01480841c410400c0c44041c80e44140d22641c0d41c400031400390903141e56100181030041044020a9992041c4401d002074000d06002401550034211000c1c40388010345401c50240e4480c2600c651b0303000074000e00c08010b105107070803500005041f0a440741024030b001d001030f401c0300450500030b42c014800940e803464440d0241e0120601295040300407001d80b55070511004c00c801d02d404051508110002c1c4061007445011680b401d082c1440c4051401c600c1086610040c9074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 67187583 1250 67186333 67186349
    0x5360a03030509120f030c0303041106040f060507300207170a2909100f06030b0606070303091202011d011a01050703120c11010b030105010b1e040e0c070c 68
    0x4201030000a07001011944003c5003262207030400f902024082d0326180054410340d8140c0004a8644901c900c00030185016601c0b6814490b5114801c50a200d40d074001c51007070b1051049010f404024482c050002005200d01440f40400c0b04101086e4509104001c041e03030107800900303088003614a540c1482181e020341040e01c1c4c0d118100c5004421165100d206903405070001c40c4920030503c502d4800b10541d56004000c0100740358924100e10030588400f4141074880c0c0711410200c0500d5028558450368080c3c0b58002604c00498a4881c00e03c02075420104040301855070b604540b50100307064002d59118422250700100d1b144000aa1003014201d45802d0100542e0404400d041e8003400341d08a1280003100f0b00c0c000384c075808a420101c40054141c000c0c01211407030305940d00e8045030f005c2210320503442c0041c000c1c03111a03000e40a040c2203500c24441c0c001d0f003900c24000e110003102105071f8a20542951203070141401d4880301c140001e100107480e0034540d4100041d004d4100403030241040700030b0504d9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 67188833 1250 67187583 67187599
    0x8040603050f0c1903020c0a14070b040e04030809031b1609060e04020603090a0f0507150809060105010806010207080f0105060906060307140d020d140a15060905040c0536 75
    0x8460f59011406030303031078140014116910424110744a0b605031004044800c040781d20960f01820401540303210400900c03102d0085c00808904082118121411502c010f001800c0d20b070f40e02d880840395014082d10302000c80c002009100c586030488484250380751802009002040300c031110a521200054cc8281202e40c1880000c02842e042501c015520035010390341c056403503807903401a50400ca00254010580c0b4040c0a0321420f2000024000c0161102502c80250991481c0c009403400ca004541900640c0e20500040c44194421900f0542054042c0122388006440e403000c00d040880b400303e0300c0c143c0d80d0340b03900300041454403e0309143c10050685c0d04515500b0444001001d2520000030103909100020740303840d06c10703183da0445600f4540d00c10b0400800810b454240000c81064418880c040e0900c60202c0074100c1529140b01100c44e203880341c0c290301c1c0c0741c0000d01c0040c0840c10090024803506004903108600304454100c601e1a90780c015010b103082c0d500003500c0010780080e20034080c44039 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 67190083 1250 67188833 67188841
    0x70e01020a020603040201140301030606030308150303031b0c030c030d060504091511041802181e13020f0a02030705070911180409050f0a03020c0405060a17011808040603050f 77
    0x11404080e010740503580311341c0d66950f900050343c210540c5c06032401d1100d40080000144030780d9600c010b0603070b0711941e07400300c0580340c0b6040404004055100154141c000f08040b904414400384070004440d0304032044e50405000c1943c80b403c541000b014003200d9003000030504195081c600c030790809058101ca00f040640d005444081586100340783c101d4400780c2c2d646c00741188510074000d90b0001c1007070f068060f4841c04d81181c090041d401c91a04080915501d42c0340c0d150071f103850440c0b8034141841100140228054500b003120802d050400841c6150342000802c480c02c00b110001c103080201500207560700d04140c540070380b07850748a40c400c41c203003807626001e90203a06540c0c0440b4043c0e0798146e00350700d0100034080024010584250000c24074444d08a040c40d0300c6902060050383d0350700079001d80303952030591020300c0b041e5541290031641c000403005052096407a1090a03620f04110b03a000000c0c1c00d100ac18410000c07404181041d02e0070407001c94100121941805a26440682c55603040300c42e0074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 67191333 1250 67190083 67190087
    0x20a090807080307081b0a0f050613080901050703050f03090a1b03110603040203100c20070e01050d03020f0613060606020c03060a0b15040b0304020a080d0e240c070e070e01 76
    0xe101001800301400086090f2400303480c54034000c44c84122010303507d0007000c42c42d0107000f403281d00c1011079460048500103860a0303022840240d8003030300102c02a2900e1104801101c0560280c6422000e10905104011100003408059413003081c11800900800c0954100000341c0400d050304040e12040c0f4510500020b506601c80c2443e01e50213a890310744a0321f8901c0002d0030a0343e003000004420340380005240341c580d031044100f6140030081140380c4082c0502400702d43c4a41e95070091407540071220004000c18206819401000350113807058420705a080c40c442030405009461a0360422544040e0005103c03513031045000401307490000708080020400071079281c14005000c14002940c40503602d0b8a925290030180b410058941a00e0355692a03c0710360081b5001600c00346d000e01d441c2c0b40c01168001d00010000c201000649452404510350030070000361040c4440760360a0000d0300b00e9004040c0205201030500503402c0340c0035040c19401e03c4108103c40070010114020410391400350041a6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 67192583 1250 67191333 67191337
    0xa0327090903031812180302030616030506040c0c0b040c0506030106050a020606091303080901151701060801050403090306051003060c0c050c010206100b070c050d0c06030b01020d05033403020a0908070803 90
    0x1036070350901051000300c11b5608140e20b41c040c4c1c4080c0d0140180d00801001d2091f10700b554109401c251030420140d1500f506100840d01500b08640125140d91048004903440b114a030f60b00500c01e480c0742c1e1050f622100880c64980085e0300480104402140d046015074040c0041c60740800e06a80c08810f41c901a000070a010b861000080c2c103000102001c00c400040c20b4009412888035140045d240c5a600d90414000005551820005519001d0007040501060140030700554040d51080a401d00b0354130303a600141009041d91411880480f0300000051550081f40944031144e200d0003092507042c00e0960900d6084840360341113400c68400c1200364040c100c440d10547d8060350010791106041d1420f00e0b28003040d60460780d8411a5032407080300300882808600d081e03541b580d4042c80b00390320301001a681c441801d84039901003441400001d15020024840200c0c0740c910826901c0d409404640003512030184150190009030002504007410307402008d00c50040c5103c1d401058003d00e00320015071a8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 67193833 1250 67192583 67192613
    0x2060a050c120415020f010204150809030d11030a15060f030c0e0306090319020304080c2b0804080d02060118180b010f0e07050306030a03270909030318 67
    0x100002241c0800350a104114610051202205480c1e407035444a40040c00030002a800d400107102c0c10382d251320994418002d40e012a02e6420300341c1280c4004120a0f102c1d042d0003041c541103880140603c1c4100c7c0c40742c0c00703010302e21983d9819182d07490401c000020140e038011a003503041681d442c4003c00c0700710f0f440884c1c441d151405183c0080d14461640044130201c8050004940c14401d040070f1001002010000705003107181030004200c032038080041070303841740502c1c4249061600018850180b504101e1100002c40c40307440403502c0c0c441a101090345003030040302c00c265075050000c60240908202000b092030002207030300041c5482c0d0300d00011803600030310881c41014469155141c1d00f45d180000d100305074840c1c0e84034440301903568581c0403040c1c0103071261183e10020300e046404102007030b002c1e100312801100301402600b944c1c02c4540381503a0041c8020178020b04800c1480e61601c04d481c20009040180c03109200100e02d11704a410003c00307584684180134000140d16600e100024001c1c00c0c0c60f800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 67195083 1250 67193833 67193837
    0xd03020d06090504050c03060709120206030703060312031a0a08070b09030a2414040203030304120e03100e010f06050604033002030310150c060213050a0308030a060e0402060a 77
    0xa00c2504038610380140016502c40311401e420101404100240401e02e451500380c140d0446c0d40d03543d14000308036224012446440e80ca92003a602c0d810150a10200440e801000d9060200c0e51555039035400c01d0210310f5409a40000782d490126455500d03040c000031603101d604a8118243d4350a001600781c680c0d049100f5081c0304a000550700740f49450500c820910b0540041c541d0700a00310364501d160006102c40100310315189040c0e21252014021000140119009002141140e68541e03070a003220b40340c0d038680800d02c211500c42c609259020068550301140012020645220040c0505c0c25034000700208098142007020511660300d40c0340c01d503401c90350820504000c410410588071a54224842c1851003a00101c00180280c1d0300040114001c05107200413041443d0341d0070322040340228404020300000d0b80b881d90306004c00c2d020740150200e8908600e11200741c658942c0000d00601c0180e20413110b1030717400b100700b0101c1451403082000824142c090008a8070703181e400a06541310780545103003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 67196333 1250 67195083 67195087
    0x2032b0305040f0236040c0506070f051204050306010e1302010f09080d09051206090c060d0b06040608040b0f070f030513140601170f0309040b030a0b0703051b07050d0302 75
    0x42c0020b0502801020b60041d105e003521000c551031a103c00030010046884014407041c111540d58010b032020340c0700d1608a4201800a4100020484640e000b11400d82e00c03a8034011405012035401d1200e614200f0035080c800d80d6032440e110505040050590041d03840c0604801000205c100c015170800040e0390903c1c0031510285c2081042c1e0718039941d80c0050443c1d00c149284007070f0864010f00c42501741c5a080f202010000c0c002c0c61a01d641d241c0450b0b0320050358225003411034503410140042d02d103101e10301c20042002d119440c04191a0740003980003000041c108010f001c1401000807c0507000300b80100f41d41900d241c13455011f098407a8074401041010360394030029400c100481d41205a0903400350a280b2001d041c0040b0707a41c0c0f10020b0055804484a0000803221030301d0001e0b020066501c1240035604261000080000501201c1015501400741c42a8800021072441e0024406e07000b5860001d007901b0040b414120090b8900c8219028030000c00c070040210f08006080c4c40003a12610f0f000d6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 67197583 1250 67196333 67196341
    0xc0304020d1401051b0712110703020d12080f090a0201120b12010f0e0a0c2615040605010509010b121008030a030204090c0305041709031203011202032b0305 69
    0x484000d01041d01416030880116080315526043d08024001c101e20301100501500800c045512031182c40070042c0302a141c1d006c03000d0014010a104030328501501d0590381c00390354a8004c2440d03801d004400b00d400d004141002d002c002cad001200d01381c00512a00c0014081d1428044c0b0689d18202840068107101602e1005410003c0c03541000704414006001031203c150a0815140641f4060003030250050800202c031038840c0300010001409034100c06011442440c00c80c100b489a41d2441e007161500e02b18400468590b80b00b00000c020807080141c44050914042c1410000c07100180c1001d4840d03040500100846c41085060b502103040700945c9810b241c840c9000d40400b109280e00c00c42090002241d1510000d070164040c1013142c5190340148203865000400718100c0384101c800420000380b442040f1288202480a809241005030403502d291111000c011801c3c1c00907440304004c681c0c1c1c1d0907141c4c11402e0078082c440c40808514000716001c1403085400210509403103020041540d100009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 67198833 1250 67197583 67197589
    0x200706090807020a0803120a020c07060302070c0911040e010602010209181e0c040609090b03120c120f03090d030e0c0d030c140105010501021c09051309060f0b040b060702090c030402 80
    0x40310b80c42d90041008543c5943d44114580b0707a04074110411103c46ca4000060900d90507000300d4121103000005081e40c01d051001c107134001d400c0400c1c1520720600105000c1041581d078801c0300105103904010350340b9185003030b42001602c04145c20103000c59005104120700c540752620084001c4400c1a00361100342d0314619101030312551710031110a03000d4910300f4003240560620042050703400e19030340c094007580c55100c00c41c01d40d270030403441503003603840350202d015012301c520081c2c1450200351042e264844146000308407183c000e900300000307841c000001d2091444080007000d4008038681400d000210f0b0440385070f41c6407001001524081c0f0341140d01401014030821802100381c2e40f104001229004440402d40201424007030103001d40b1038a10300e0904d21035105902d0050404907900c8003151030904060296009829001403151900d64030010000380c060b000d80c203a45040075034009101c000704000c00054880300511203003d8082040400090780f1059240707980002c14140e03072a540d495038404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 67200083 1250 67198833 67198837
    0x61508060609041e150815092a090702010911040509030c011104030605010b07080a030b040b030a030f0e1813031b05071a03160309140106060c02042007060908 70
    0x25036015241904d80658030300c0c41c4444904103a0556000c1010722410440c0e00030f103c0313680c040c0e45060390081c0140d9004544403c8090b50002c012026510040c0c401050080300f403401d0304135038807400044030061915007400780c207003540914588000e110340c4042da04d0320440081e20f1400c0c140140d1715180000c80105040044a111800c10402000300c050008260388442d0031500040300c58904080000611200d00000e8804641e000b0300d6261400c0030f5010142c00500f5042c1d0b645030469100c1e008002d45980500400418034040c0c0c94420f80380982000041c4100c0e602d1007158403d2440202400f125400303a0143e039888407588006079260709141c1825201c0180b1400090b1040145080d00d104000340031815000f11107140442c50380350003002540c0d18281c00100c442d500203241c40c1c00c14180e01c0c1e00c02d4100c084900d001c2c027038240e17400003000d00082c03d6130103507000180407500c0e101c400011410144101140c6009107040110084204858803601c1e114200d0050070460b02c41005200384150001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 67201333 1250 67200083 67200097
    0x3130507050612060907030204030218060f0901080f0c0603100608130606031214030f0f15060301080102040e01050409050a0210030e100c020607020105070206061002120c0319030615080606 83
    0xd45034841c0480107600203c00340445040b4060711000001c1034140b80640255401c5da80c3c014128080502d90000c00e0320403c074004c2001ea4003129450005825840790f55119028121394070240c00006100f4100e2840c0c40058030b103250280c1c10410800c20b0b004503071040f6209568040c601004242c4030080b1107220541c1d01e9802404003450031800000300404800c010a86940a4403031110345c0011001615541c041210100c3c4440c0c1c05000007404214034001c8680d00007007002e68400182123000101e411900241c0151029a42c001420b20052300d021082c0e43c0140700485052041003066900e8917280c250a0070f00a00a50b000c0c501c064116000c2d4102c401707424503240480340480340400d2110060042c2d40050b1025000d1007020850951040c05114440c504c16002131000b03454410601c030f208030750312124a0450055824000b86c01c40000000e000700d5010701c0095490f02c105880b0340d804041400d00300c03000d041c40c00c0c1e0704100741d2812103c0200d0604a5040811460380c0e200b010602c82c0c41850 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 67202583 1250 67201333 67201339
    0x705030f0d0207031101050705030a0c110604080318300f0f090f0409200d1b05010906020d020d0302070f020405091006140102060105060309030702030706020d12020307050313050705 80
    0x400e01c00d0107140164003604803940079070742e42910001090461404c95505072005000500d003040028034054040d00800d889581c103140400b90490520318103810040251801c5448000c00400d01042c24041009010440d0f03011010341600035044a10b2101c01e101c05a62205607410410403c00401b580380507614420071240000c1c0e646c80a211000074136600103441d55200b00c900000c000c43c2420f0500c918502140c1c4041080d80c490782c41106503140c02e0f0b5854139164000005030002d07001035040c40c0103400680000515007202400c1c600050480000341c5c10440841d8419220b02c3d41440e4001427084201c030700d60030010b0307079640d186c01d12880f40140c04c01c001c0e400c82e040a05102608070001103101011801c4201040f589480c1c5210f0004000608186401603014100500c001c2c64420700541d004000c0c8022039113030447c1940481e0600080368080009608003400c00581e042c0c010081d0104103c86040852a601d0441c5002e052408041c2c0010542c100034a4884104a410401e6201138036000f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 67203833 1250 67202583 67202587
    0xb010c050a03030e01050c0304050d1404051309050607021501061404050603040506070f02010e0304030308060a051804050c0604030c0b0c010f05130302010b03070806010314030d020403061a0f01080a020705030f 92
    0x40c2c140500901552030000a40e90300c1c2c0000a0b07090b40c82c00c1e0669004980c00300c05001d9442c0c60b6031044034034aa0b0003041d480c20500c100f100007110358440711621951b000940340032400c00b001d41801401c2c900000d0000041d500100240314000601c0f000c0e86040d10b803241040c10480319019081402c5015a410442e00007000005200500100203030742842401e2591b215a036016981c00b0807402d0f15015140c403161540103010034000240940080380d030000c0c028041d05580c2e9a90070009440c01c80d51440b50306211001000d0009000052200840d0340f402514120316052540c1d03074800c49510244100f103e090000b01c1d82012044003034002a010200c803e03800d100508003411024860070407d142100503610342030070b01c00c59040c04584201218036040180449030701e50744451400d0803600310420030b203000421004580303c1c1144003400256014441c0055840f807004448000c880c04135107000e00c40c2201d046040c803280e907c2200c2550051104501688944803031501074030b18003030b507908000311442c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 67205083 1250 67203833 67203853
    0x512040c030b0a0e010e0a230f0307060209010f090e01050405040320010c0905040e030306010311040e0c0703260406020903100603080a080c0c0304050d0c03060216050c01030204180b010c05 83
    0x8241c21180c14400c3d00d9008000f000f15111ba20f659500e01c2100003050051002c40301c2202281c84249024140900000d4482e10703550320800380d045034008042181c036541d010031142020b5902030a5040b208416040c170032801c030304100c01c202d19050144a2940b089032241c1c0010b00701031007134807101d451000612070780c1841c00170182e11a005c2e10b4200311480000e00c007403000249034601070140f204102003040145285441d10f40045024015465441510000800c4001800140441114400c1e10508101500d0300f0300c924006040c0c0c0c000c11402c102c0b2466800300428080100d40085401640c02580140d0351000d841c00f1904102e0104811000c45281000000a000460700100000105581c449042c0e5440c1000c0c581c1d2070040176100c0c08280d205000a11060501003a203804c618002c1d8641d4440b66900d0b9180c0040e68020101030f00040e1403503010703c0800400300a25180c80c0d00c242410b6042905290300f0404180a804c0050360842c1c64011442e103d0f4010302003500748980080a0310a02c0e16 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 67206333 1250 67205083 67205101
    0x2010c060f0e1209060d090201050c03040b030a0501061103030609040219090902030d02030301060c030507080409110a0905010504060e01081009051602060702070317070c090c2d0512040c030b 84
    0x1c0714002d42c194015101d000b07002400500866a40344001041c4a0810103900c3c250402003140300c0d01281800701c10000b00046482c1007020384018a94043d0031503407854909003143c16504180e01003018000380e12035141c1002000300a03a030b4041005c0c3ca140c8130a03916400001d140c0101034030344503400e0790340d6403000c21450b0072500560205402030f0101c17a0403540d11721089981e44001d00c61400040c26040c05803001034410801042c06500560240c2d0506450300300d071030100c80b03a5195074112003030f00180070440d454000d12504000e1000f4204181020719050015100d88285410a0b04200341d880002d50281d00044100c006000400d400304400d20308503e50b40c1d400d1143d001400094412040060b200300e01c0020000300740d03a030111004800503130714208051546c0000314100d03280c49142c03402250186043c8074040c0103e8076a524407010070700c512200d00710080c040310145010003101c3e44a84445070400200d403241c41180b1414000340d900c0d42030500b90003807181c0004007108041420b0104440c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 67207583 1250 67206333 67206341
    0xb040b180406090906051e060d0302010e0313051002010e1209030a060e0d120b03070303050703020102070f151406030601051002120d0b0a06050c100c0e0619020c0102161202010c060f 80
    0x15103c1d0004014540b154016081702c1c10784115031f140364950500000384e0604000c86485001d034424000410700c5070b40c0b0a1440c3c00d5400c40104c120411010a408104030310b09a820410700d4201c40c0000c00405981075200b0740c5403840c810180340b14980000d0a9841394500b04001140140c011071704002c01100409050746443e00281d40b600000d101070040c4c1d0815420303108211030210020000c02e80c4925541e402e8540317403c148416410342d503080c0886804502e0801c0780040b031a01c2840b07030b101c040c40340251110842c0c01003010824031139540c0040010350b07280050744a0665500302c9030442070b04d030300c802d0407403912444805004030420007089003440408181c01042062803f1941c20100988940b401c948602410148171b200340d0021f80b403e014102c4d10351000007558898506050b49490f4080800d44d16409000004045418500c0380807034a40e06101c10612141c0900c0a06118902055039200c1e602030340c0a6a40e0100240c07801e0811680900340b41807a0035031101b024082002d0860014001b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 67208833 1250 67207583 67207601
    0x102040e010911040609180e03070302070602010f020408060f060a030c06080403031803050706050a022505070503070617150a0b070614070507150207020303030f150105040b040b18040609 82
    0x389040c600721038954036400013a90192000d86e80c50800280c60044110364540f60350301d90800301030340c8003010024004240002e004440c0250001c1030321929110009085450605d01c00d40003610500c018044043c003c10309940000f104407800c40d031622400001020306845a00082007a2724a0200080064005858500c218040c0d1400c010702c94402c0d0440801140050000300003820401c420b400284c3c960b4442504000d0306000182132008030304d1a1240004400c010082d048001302480042010030400700000d0101034024041d203d107829006046d241d002c030582c00d802028880061041c640c40f00411200d0715004191103282650390b803004000f580811003e07244241020005070b1030044580b0194011066540d50a00d41102034485191299603c408444002e80820240000d0307a0101b02850068801c40100400d60800040c4201d1504207042c1543c144081804100882c1c5403207029117080360281541c0e13a660b4030030805201410f040b411903d035803091900300080b03840e4010758804600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 67210083 1250 67208833 67208849
    0x1603030e01020d08060103051f12140102130e0a02130e0105090a06080613030c1a06091303080402042c0d120207080403020f180a0207030906030c0e0907020307050102040e01 76
    0x11040a2001282c6410100301ca2102088006012505c0381d4400da002c107034007034480c1c0498076001c03143e000c1103079222a45a11801c500088802402c0c00d1049442c4c80c0d500058105000318a054040d2122027100196845000d0302400448002041c1c202550101d0b941421451741300d00070f03540c98907592102e00c0c00a00404e0b00400c200000212100d20521940b0241c60b80c4070001d0849584501c07104a040140150032001c1007842c1c800400010700f401208001229030302c60031445450200284140c50b84010b03d000e24088510702c00d80007094101000d113030060b40545022422503003141c0501c015015015070300d80c04804c83d1100d034503809004565038102008580e140050340c020190108140e01803140c01618002c002c00c020401450240b60103030b01d028000d48171418034106410074640d015000c89034070b1461500001c0e102c003050362080c030340c001602481c1800c005516811000400400c003224420340107801c4800460030b003a00030025103c03e04d610000a541c2d0300d84854441204c480d0a1140d411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 67211333 1250 67210083 67210097
    0xf0403060218030d021b03010609050a05070e0d080304020405040206160515010906050616060e120a0305060901061b03140a03090b1806040605100513140109020301050303040303030b040e160303 85
    0x1924600130844080c80e0260f80d00500742c10105480450050500201441d4559a1040300185808150080b02d21550302e40318001014601404058a030a06c1500014030403100495481c0004107000305507030300035130141c500280755510361001c00c00c240b01c0c4000100700301c04005036080030410000b401140d00c19600d100c14800742d90b501402e500340c07205801240d41c40b420034400c000600d41031008000e0081d0007143d01241c040c020036050380c1048001d1026002509001600040c1c2c140c1502401d500403034103540b03401c525171514030300415000c000a1501d1175080001010760905100340c0c0c82d03040b09040e01010301d56519110780301800602d610758080f40c03510b510a000401c460200c2c40c010509103040d6014120940c1c4030390340c030001000020400024600041400705282c0c903903050450360442860301c0060302e03400600341d045625a050b803040b14210300400040c0100c0d05c000c41a142120780c50f0a0200b5032036010300c0050090501d05107a1149807240340b1042c000e03840b0020345c0c281100d0194079101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 67212583 1250 67211333 67211377
    0x212160203040e0f070905030f0d080907031a010e0114011407021305180613030203071202070803030408031503011109130f021602100201020a020303071d0d050d090506090d02010c02060f04030602 86
    0x1601c440c140c80c2c9c00d1030150055007051b0500c81c001d00c0d6890f800f85002003600c0b4800d40303079685d000071001010858401810401c2c01482140055000107000d01510100400f40111000000f4001340c03a1007420384c01c9640100e41c020464651080c194214035001c1c000b40704510f4460390b00150b554504005070428072a000203e40100c0d04a51007090058041c0d0103103190212603260036421039034074900c030740071441070a00c0040d07070400a10155000301e202d02507196407800d191505083c090915110304d407081e4035106110700400c100c44120346071517074140c68500305410351040005c020100d031000d000001d400003e0130030442800d0759242030344903c200c41d9107107000e050980c100d00b01d004004460026030b00400100e4207060050400030400b43e02c06892a0741c0081d00004140300204640040324107901000c5143c1c1c1e003642180e007a0004d80003d5500ea400c0c01c03038120028a50005c100b40190500c003003d0300d41020754680800f129038028160441035940c075a40e25004009510405015a4032000d00b1204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 67213833 1250 67212583 67212589
    0x20030615040f050402070c0801050f061e030c10030b03060c0901090e011404050c0403050a1a010b0a171008190b0703060305030a2f160602010212160203040e0f070905 73
    0xa201901c1040c504511601d00f05800c1c0030096106d542c090300c1302c182a0100040048090240e0741c442c08903880c0c1141281007860038444e040d100b4406401c5a999000102000354400141449400004490810540f0b800b170b10241d00515005552a8142c0603101c1007182d0301e4480801440720803020f9032a49096030f03890310351041d548402e00840e52040052034801d003581c90650403068006c981e100d21586899034995409203805000c0c2400c82d00c880d03004071000d0300ba1424001c418018280040c4092800c184900020300310405002c22442009a00d40440c0c0340004441800007e4196242140d0600c0f1107150305aa03248100d80c011100070152900140c0c40300c1c80380c051581241c2d444001903050082c074503001c0d03a2005075000c044651540b0481311041044080b01909002c0b0840005017420b05070024602c0460290740e002103080da0700400290fa002070200b100a030b4028041007015072600c0d065a030403070a520466001142d0000d1041c2403200207400c400300c20740910740c41c0e15410240c4e80c0d590f00f4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 67215083 1250 67213833 67213837
    0xd08091203090307060e030d090f0b01051e04021e0c161e0e06030a06020f090319050319020a0209010f05040506180a020d02040513061502010b0904020f0420030615 72
    0x2c5011141c10030b0210310b0028038281c1104074043d00302d80a40e401c01401d40b000c1800c460307946801b039401600c0861a4001d21049020b402d01429040d2030780000c0300c0c11802511203039202c140e0244d0040783e0004042449003084100c070b001c0c241c48440110342d41c00c4902c04c200d07600d104032004499900c0b00751000068011034405451412240203100007601c0d0300e0941000e0b10f02800424441d0903010750741c49040021442c0c4000c150700d0007604c00305600d91030b980040c945801c901c070031001440d419060a51001c034400100b074495424040704861040e40240d20100d042294084009420046280000c1100108000c00701d0544d18107503030130011030b83d60070100109a080900d0765100031090901003917064800c0d40091400750081480549400e9552000c143c592508907400c1918a5507414240200c11485a8a0401f0346c0340f88020712607403030351000041107500050402407041c7d0200541d1440703a16241c115490072007140e001d41c1e010404030585480254022100c5a01c185070400d1007018070080002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 67216333 1250 67215083 67215091
    0x801090c020d111e0106140913020f01050c100f14061008090309060c101103090309100e040e0604030e0a180908070506010602010b040b1225080d08091203 68
    0x4020091503041d403500355401c02032481d82d0829401401203504403000b0b07200e560000d04e04000d0000940300e03d01507000c500031210310310013441421000c040c01030780329007010070a42c0d80b40c0440301c07171804010402c01030701c0034861401e5001c01c6000e03110000c111511103071b008e5500c0520148003801040c0c0011000d40030b140040300c41540c030065201c0c100c1500d80c41401182e40c02001c007002c5038604000d00d40000c40c2c45d003040c0c441c078103994029101c2001da40786a00411901b050b02072401c500758103042d21070903120b018031a000d034041e048600030707036075210300c50200c0070841c041c054000c129400d0362003006510780c481203509074041544111414100e0030215420001c440c48003500005002040c00c580e4058409a40242e0341030300f081c01172002290046c001c0b58003c01d00354000080c0c10140c002400161501c0c800c0c2039205460303041214603055804200482140d500e66540540c41b0f00c034030142144030200341c0043c080c80c0314010702058115000040c480c004e100348012200075825130040d240c540d00c4116 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 67217583 1250 67216333 67216337
    0xd09050709090c050d081804151205070e0c04090e070b0c03090a05100e0405061f02070e0c0403033608010c030b040204030f030516051005041412180f120105070801090c 74
    0x800c42604808603647c010704103100500201b8103d011882c1036400f110141c209182d00d00b072458425040180810000c0020a0110204212403608880b0784481d40110b1291860a075103441d0800d4051805004020151448518240d100c00907035800a41c0c070340100e05c40d1800f8100700c0c200482c0c1e03071038038503c1c0c3c180c41c036555500e0090094402c0b007804007400c800b415403a001140c80ca03a04800501480e41410742d10080d5000382109841c107400344110541c050054912100c040100307101182e0b00036035545002c500085c01d4a007001840461240d41a20b80c0c410850741e84940e8800325040d03406400900038a00c3c6650b050260a040c0c00402040744111f00c00100050b5481d807000002a000d0703000340075014540700506480711001d85642d8100003412108401c069580d0082200700300e0005407180c07140d154a070003803495841111440700346100320341090400d1034817181c2c04216a0703110440301c119040082c00d195151001c0a000c075028050a4502c4008034200300008207410440e07218200d800d80c115 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 67218833 1250 67217583 67217587
    0x1909030e1c1110090314160e07021c02100908130f0e1503030f160b0903120106030f0b060d060501030513150207020f12070608070e0d06020d09050709090c050d08 71
    0x18400b0042d00340e103401d0190060140b0303c0c13400800f00b01e0310556070181c4054000a4641410035414500321a03090760425010065408180300c030282c1c1c0050784400c0c0140303030016158081404202649051b8625411790704007400c0c140240c0c204030021000e0f2a2018410b100d0310007083e10345014001d02c0c4400e02481c1940000c01d00042c0b003501200200000c046009020f40385007055940103900168048000701907075112038207036002080120000d050344958111301642c01e01d030600401815510040c4102c80c01c05894000b50b1800c259039510145c00030030001d000980d10342040110001416082c8500c9000c81c1c07034030001915400244000104141d40700c4814a50340f103144900f900250043d040580c1c00260021140c240341d1202642c1c8006600e10f88001c015080c504807004216000080c02d00302080b1510141110644400d000d00f007081c5c1d031140000d605c4a140201e00c0000340070904001e0641d10801800040c5042e0542c0010f00f080c1c001c44115400940b10014019400f900210040c141001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 67220083 1250 67218833 67218863
    0x307020603100b0d0510060509060a030b0604180605030f010b010f030f020d02070605090d110706121b050d0f0b0609010c0c0b0c010e07050f0306040206031909030e1c 73
    0x1180008607030100501007940c04083c0c48070044001c2d6003008000f504010f81d10018009802d21b40408800208220318186140c0010b61001c11a1401991101400d064450704015801c0c0d4844080d50040c1804003440c10545114120250242903a0b1003020b0287c0201070199104641c18052200c5149068661040b0346984100440081c040c202484261a07820701c02c08000d070f101d03800181141800340c00081098100050003074100b010070889202448180f4000700c400e01e1001c1508800c89004e030801c3c00350245c030780d40240d02074030304042050190700c1d003890a0000150014050b180280d00d41c6400c01501e0196082c504c100c071061954075a10a5041c03041c40038541c411801d01d6411842640b5007004280d980031800352130340140300c0c170b050f45944410500a05d52010000d90740282400c0391004103102c44100400c0e180c010243c00030303000302c500000095210290f01100880308101540c100b02042c501e0030001c10400c060440d0b140720f441000c41c4041c910844c09000d060a03a001218056160b20f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 67221333 1250 67220083 67220089
    0x608030f1b0102071505060907030e10020c0f0102041212030c0e040f020d050106051b030313120203120103050703141f0b040f140108010b01080403080403030504020a030f0302071511030702 83
    0x458021546550b40d001c0016070000f9a0104170b12661840b1600c012645040040400c040840010300c807508162400900071a440000984001202d40c090300040c1e507524200605810103c114200076810743c00014001800182c03994403800550049200b0070b1710341c0103002c3c12001d845100703080b180000c80441c00d40c138240c5807a40c0262952a000d0b90b006203001e91441040d010340d0401d90040b00490004109005901c2400000144000c0d04101842c13452030f20802c1511520f404400c007030104200a01c2440400f8020000c451006a403500300c1c030f05640e500c1c40c00960310b01580c04100c40309414801300301c0030814001806000150118681c0d0700729114910803200600c0b240314038550081d166282c412041c119849842410501d5941d1035550798100600907003034550402c0500c1c108a480b208200120f030b0320026003a040b60749843c3c08a20343d1901d0001650513917880e000980542c040d43c4140c8105a0000b45c1c0b28201c6d005928040138140b1417900c180d82038541c40d4040304d0036030000c104400c0140307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 67222583 1250 67221333 67221367
    0x210f0c09100e06060d050403030b03010e0708070b0a090b0f0a02010b041a0d02040f2405030303090307151409060f090705030a02010c060f1b0206010b1804050702010e0f010207060608030f 82
    0x31002528160405d01c1c68141c610a4610659050700800c4d07840034003119904082c0034170410660038400a01c103251402c2d85a554070800e91003404501107020810304145407103420444003e002070300b5442d07225280075001120b5907000480c4800550b1a101021640d42414001c0c00132150180071821000b41101052005028001608030303417156030f0750918240e0f804140305045450380ca60984103200e0541f50303600801088103800151180d8014403c104112707030000112b462032980408040c4c4030015200c2c8010140100368880075406406004124000400180da036224811085170b48400340c58000499448000da4010190142c000e43c00b5800036502907803100c2112441854000380302c241140da0502142d04004510a43c403003002001c07000903504000440c0903003003458180e464900030b480130304582641910300c0e031f019580f1100080d0485001398851200394044609031040c1001d0004c100e8001d61108408480251a046012a040c1c0c2c000050307a45038000c0c070340503914041036001401d82c40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 67223833 1250 67222583 67222591
    0x50a15030506010e0301180b060a0f1205010207020414040b18030426010c02030a09080f0318030a0510021903020f0706021b160e070503100311210f0c09100e 69
    0x807011000c1e04e0200b64609102d01703044401a029050b40b01d100b18a0301440120000c0c000d41d11510b864601401103044004c412030842d0140500d109030b141140c90810701901501300041d511610305101c5490302c02012800c180f089200f1500140c030741d0f88103019612034030b80d070002400032640700b403105000f8a544114140035070f007a41203804001013904102030f42500e03060407841005070004110000d4440d04a00c180014011403005840d80707147e00034816a490180408030851110380000480540e2020f228190030b0365000404d55a0850b24003564001039801144201404001c4600b030103101c9211388260303190441c160604910700011070300c850000e900461007014841c202001c070300b4141e80041100d92210f07000a0408190702e40342070501100000010300031400c0c401c0c200300300301201940601d1031003642e40c0f103c1000d01103444070000c14036403c6a24a24200f4502c0740810021001000904c4a000ca1b20001102c0e504018142400b0f0042025142a0302d11400582c0900481078074212039980 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 67225083 1250 67223833 67223837
    0xe04110d02090306060306070c150914011b02010902010503040f110a1508130f1412040b270114030a0b0402030403030906141b0306030304090608030c07050a1503050601 74
    0x21294002501040354400311141880590000340c2c04124142030007070325400740301107014009900c1d0040026040400c0e0601c0140540044a00d2601d80241d650042000981181c22301d50b501c12151a110b008055064111100400000d43e101c51180705000d88110300da0b040e9030750350a68580d0340e20380304400046c020444480724204100c150b15214040c54000800070503075940e8510312004800781c443d41c40940041154400c2039000c501164032140e9403030407590320000b070091140c4002c12440c24440500ca2180503504000380000d64141c00d000a04032404a00e5610060b50703082d407102022924a44d110540840c44215070744403400c00b004046c65204100900108080010300c0014089074411201100426529014041400060703c15504141b084807818482400c040b09c4087d800f440420301a1b00380d120000c000740441d101801510000c1c81807040c1403000035214901c60351284c00c1010420070602c9411070000300c51a01008a5044400c10b62954589050104045000d04401000a41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 67226333 1250 67225083 67225091
    0x1204050a0f030c0b0901050f010b1c150f080f1f1b120c0309030e06090a18020a1d0f040207030201090b0f0a0605010815040903020a05010c0504210b04030e04 69
    0x310740001840688544a60b5a40e200805685401d0b200e680b07001d418284541c1c500401c001c06000781d01442810740300726501d010307100d103c4031100803031904060701780c88440c60600a45035025141c5814403001d03030300000055a440d9460300903040d42d9400101c60850907500c02903000350085032800c0424150302030344c50b01003044100d00c6a1911001c800500c0ca0000030481c034070702c6240f904c003840b880206000c03510b01405604119100140040341c00302d0414400c110010340150341b41d840d813400c58010003070629110380000210000700c000750856460300d0f000c40c1e01460a1041c8080415540140180c000c0a01161032800e0040c04000d4205c00c10440c195035a401903c4085000280014442d1034803d40300152458401c04000648945038002d90600c481441130280d80864071004c01e03149902521300180c2c0100c41d007401c0f8a0b0100011000e001546003065680c00194814003c1081e9100ca00301450142c07070f141d82512190801120103020b01908802060002c0c1c450b00c400f0742d0640d00104081 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 67227583 1250 67226333 67226353
    0x402071101052a06070908030703020a0605100f14040b0a08030f130b1c060609030201090e090703080a08070206060a0803031b0d0c050309010b04020403020307030b0c0d060e060307080f03120405 85
    0x105200340703c2c200001caa40d004404001c0b1003a8084030030400341c43d000000d1401c101a50368060755480b112000181b5064650000556040505a50900400f513040311801c803183d458400c0700755451108400d41c01141445d06080a03403e01c0400b07181180c01020056140c440c143d008103050703420886420802030448000040e045464101074448414a400c8078060100034103100e0044450300d50142090010492081002d80c4e040b101c01c10072a08a081003001030707994220400d007090b180780c0004191038404580012a01d62002d601442184150201e40b00c54444d1420021903032103a2003460a04d138002c00010301c4150700d100748a031040e0020700300242002c2c00c250550055595600688000030b00100400200d654240500040c07103d055030114603241c15500801d0711804a07000260940c0e2104c0040341e00d01d5514805c035400301454020030000562614022040c400d01958183d110788a45003010481e400049110110031007088015407800b0300c45080c030700c500840204203440b2809403145d14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 67228833 1250 67227583 67227637
    0x11040306050403120c0f031a030307032601030311010e011404030309020102151906120515040305160c030b09010c05041203170708010503071202100302180d05010515040207110105 79
    0x454020015481b481003403800d080c0011304560003100303e10130302c4040c00c00e00c009a0b01d004c022181010340601e08800e482c02024440f00c0013031b4076681040b807a03440b0f00d40000141035001011050090b5003100a0000c1c5024685040c06e0700c2c4c450014003180010200030600090103580314206152041c01525188a0007104981b04010101c800c5107a001c824002c4918440003442603034007514540803100081c1d2640d0f03c8969844c17080040b401c151504400100e002e05003c0c80c04e941051221070308246941c07003d85441e080b01070030340c40126036004401001c9044032806014004401507030f5a6840c0c00d05107408111341c0550b51205040c0e081c0700d00d901c0e01078608903811020a210310390584807030445514142c141840e001c4c081d8012902824920044c20040c0d403003030f00c080041425031a001d0b031140d80900d0010200c4108500c0c0b00c0d80030201c0041c010402406400103446134150761450440342c0078440620040e0721520a005000140100c84040c1541c064009001105902d08014501404008071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 67230083 1250 67228833 67228841
    0xe040b10050c0706021b010c150606050a0305010b0909060f010504090f0203012405030705030a0b100f090506040311120a020604030609021009150c0206090a091401091104030605040312 81
    0x4060009280015150000b000800681009080f90310080070b2001c01070f6002c00076079040c00d0741c0604000380c0e18103010512104031040ca03985411940100401590344c41d02074000d0b0300230507071039002c01c1c10134000051021071302056400e00c000c050044005c60740c440701042005016404840d051040511010915503510706c589400840c04050042c2d0300e50400481087c10074622240c04c021ba103410342c2d0001070719803003002d898002d241414555140d413529241e81010340b05282c4101e400180309000c0b1000c0b142d008800c12036401003520b5880350700741c0b500140f00c2035104500014204486000c0f6901103424180e07040140281c40358265060500160700044055001d944180e072103503290100b01c2f040d0714083c10110300c031041ca420400c105034075005044080051002143c402c0c400000784001c00d40d16007900711600040011706a25005440300250002804614420903038040300c5030002c60381c0040f5200300503030b01c03900070101c909051a5544203030113400000c0046082011803e11514070410310b000b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 67231333 1250 67230083 67230109
    0x2115040c021c0504030501060503060c0f0a0306170102030f0708073005240d0201080105040e0a12020f0c06090f09070309050703080703020f0d0801060c080f1803070b07030504060e040b 81
    0x2982c00d07611383c41e40c10218207491150700418030031341200e001c1c4624420281c007180e00604821024030b8440300400d00503401481e980d070090307129040200c1ea50780e60503010341c005e44c882d13040d00400d250107481700602261a03030811600000451951050302503001c803810b00c1d81c24a0f569a804040c0c480b0050320441094401c1524944503c20100034034402200d0010150342804805454aa89000c4180c000031301250042c070610303015554405d00d4442004051000c0c00790036810071010813010003a85802543c42d03a10b28200c45c43e5000f8110710400516100046600d88000117111320b6028120030304000c1c84070000f81c841d90600d941e4808e2400050014130404000b10300800c140d5481d2081d908000e030422200c0400228140c01200380c0e1820130f908021001d055a0f9207240c6444003544a141c001064814808201d41200300070079004000075907403002400180f42079040c2d62180744d84041c00d10319401103080083c0450030038002402040d00c81d81c01c907021482c0050010880001160210b551015014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 67232583 1250 67231333 67231337
    0x909020c0c10031d0c0d020d0224030109140408030a021c0906060303030f1506080903090303032a0703020d0e060405040f0902041104080a140717032115040c021c 71
    0x907a4011341481009400c0c3c13880000f400030304089032842d40042c000c9260420000d100351f04040d41030043d901c03450640c070f410290300824800740c000612425007582c0c009225145c54107003811001c0f000c84000300c05050050398040b0005003951600c0d54600003a400904e072155046030304074544100c17a006405030b08009030240c0f9002401b02c0c10350030010107442d1642c41c540b00712410001e00c46420204400c0050449100341b5101019484090f0614198401c1c8401c0b903a25110102c2848a0b49000a403502848154445000c80f0b098401c0b508507154006c411029002d82c00c00c800141c4294004c200ca400c9001c0020b18241c0b5060719840064200c1e40251504640c0c50f96944015045090510451514649848403141014a030041d031540d40c040b001401090043c0100809120841c20450718000e8100510b204a114404c9009280da940100c1c07210610a40641c0040c0c601d05440821140a010390300c1491502c0c0c0744c0441400007800800c040c1c07004521820480700b15208403021a40705c644156 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 67233833 1250 67232583 67232591
    0x304080a030b0a12060f0204060c02010305091006081507032c0a060606030506040f02090d0609080708030408190c03171017030a031a030c09040602070203030301030b0403120506010909020c0c1003 86
    0x4c0d0508000300c400c05404180502e02c1004188050b90700102503100069091a0100d42d50347d80c2008103042c002400703110460981082008a501c5001280c100110703249401d503000d441c0d650403011001c2c0c0d001101c1040c0590300b501c2ca044490010314000c0d0303100f024108202c40302c054159541400b1909a036004200199030b402c2481001d20301801042c08940d0704d0641941040c039100300152860050b450020803495540390060104103645055841890300105040d407203140c00c1c2810000c5502c280079810101444181c0203103190301407090b034100c0c60380580d2195001c0601e0700b0004032012000e081c0d0340d61084408000a544141d04240160300d081c8071014507203500000d4009070641c0c0cec01d000302c2240403903804002101920001482e10b00030f4411901803000b0340301c9050a00013032094040194040c00000004014003640160442c09988656100b0303154100041d030100032903200380e40c03280c0020100304c002c005043c0356030045c0c20058101c1090310030ba40500b0b070029030000c000c003074480007203611 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 67235083 1250 67233833 67233869
    0x12010e0a11090609040302060133080f010b070b0a0f150303020f0706020601031208060d0609060207020f240331050708030a0903080a050d0504060b0907020c060304080a030b0a 77
    0x3880101e0700620113480c1010b2038201030b60040c0d01c5500c1400b551402000390540d0b0703114181c08415500c010345044102400d400f0802c500244803010440315120501c40300c10000400f030000314201c4030883d030013400c02c1d030103520f86041c450013921028000c0e403846901c0da92040c04c00404210150000d500ca900240030414401414604000312a44508250340140d0010004508058143e950602d01d030714061100e1f43d02d200c000ba0345140d8210700034200030703d030101e01c10801440d036000341003190084541c6170102100000f08001c140901070181d92000e0115030020f405203000004c2d40d00300071001082d02c6124840b1821080341c3d0780c141903002040485040b24000d01c58280820006000c500d00039615040c850341014100134100e1000500a8100245003201980714009841d403103003001c1d030309020701d00b8582071002c060144004118854541701d00031900b100c0c0002482140010301030074650559440d0303203c10201c0e4110541d280b05043d02e0b000f68051360364419200d50043c0151348510088484 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 67236333 1250 67235083 67235089
    0x815060a0504180b0604270c031203020a0e060c0c19090903030204050f120d230d091104050702150a0204151d0102060705030a09031202031003020301110310030212010e0a11 76
    0x406064140194a0240281046081c004000c140010207054641000318185850442d410f020b0303201400d2b001403e00350305446685900201601d1a482d40c540c0c20000c2001c0401505100360841041c07c1e900100f04403e0604041400e01690030600c0460485541c0c4c2c0c01000050700d01e131250440c00aa4005002e01c014a028844035411245c00e8946010000c0b02c0c484099542d21400f4100c2d043c440c040784124569038000b8522542456207500d80c0352240c003e80c4080015000b0b914044602089050128003581418030480e44200c055600030040e00000c01c007040b601603400b510310140a6020000810070403a042640b82400301c0c2c503540c4d02c480504080004040c0122800341c3d60464100405103c8040e0340007054a07040700392200b00042c2103007240b13425a804d940da859034132603550010080208069170311400c102240e00030350081c00403c45441070007407903101c101d482d0904140c1030710050016003440c039070540f01d129461300000781e5000811801c42c44e04403c40d60484012100b4226441142 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 67237583 1250 67236333 67236353
    0xa080c0d0210060b03010605030c070c06031a0108040803010506090f030102070305031f0305030906030603100518010c021501120219030605010f09090221010b0901081c090815060a050418 82
    0x142d101d0104101041c1011003c001603c010722403030080043c04408500300c0d00072001215500d070b5001d41504401039035204c018014140c0e901c0426440f0fa02c0e031807100c0b0316500595190348600c1d8401100b501d540e01381410428150003030074106400c48145038200209440910040c8035040c02074461944034070300a00c02401c800d40c503c0e06003a11601e0000d0400004500000b80d0352140d40440d401034984e0764500c0801d2800c8800340140d02c00604100c188800b5216500410180a04910080c024141c0013042640d585c0c0ba01c010503000b2480220040244150100000746410710007000340d115220389440680040310150400e4907500e0b40c800042140c0f0450b44503550050220341001e200c215a150001030000307080801c0040064582494840c1d00d40007035200a128440050a0005650315280300796503d94508145a91041000860203126070003107102208580b040b1004099947d25041d07184404880038190716006910750780c0218007a55036000e02100320301108102801c100c02c1e801c08050701 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 67238833 1250 67237583 67237603
    0x714030c12030904050601030b040c030501091802030c0d02031204090204060e0a0302060a03090521030a140c0406030e150403050a030b0f0607060908090907080103052401060807020a080c0d02 84
    0x410116554a45003003011054902d403420413200029190344400c01a4094200ca10b64590302c580b500a0b4080c180d5016802503068803444c7d0010032451901050300c4a0140c0c400202941c540c0c48080e0340f034031515207020506410341c03003d0103890101a10b0074403850203810540150f02045d4010605001d0254450900a189801200c10700d201c2c0e0329680105081c4e00c243c4c80c1ca6010551039105d00014400c08010700d00380c038600c0401070046145003032800c50311030b0000d5403180e0ba114100442e441c280480e500d502d6006000c0e082907207244c50710f011801c2d001408040d42e25101030154805071100003030200c0307600f80314a0280d03c0c0c2c50b0391030001034001011144180601485070810b0000f5001e25201c40050700c400765804071000808210398103041c00103018a82c80242d10034113070020800410740c440b0555040700e20400450742d406113a00804003408a4a001c04000200c0e881e0040011520801700150807688a0041d91454001a00e40c42105c0c0d00408041c8200d0b40511800102142d04000202c02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 67240083 1250 67238833 67238839
    0x204030b040b06180610140f1b0d0e1c060617010e1c030c0504081212010e0c250b011e050a26071205060a0506061204030318050714030c 60
    0x30701100010a44580101800c5503002d078401b05820901d803405a2581a1202402c0c0007941e280d070314524450020b5880240042a0f2900a8403654441c1a0001d00317614020059100e00d60300940003c2030040080c0c03800c105041048644405034041242c1e48140805088405a124100b28280a6850039588420180d80b401d0344890b07203403080c41c1c080e40c400c01001c4940c2d20b000f091209266501300d03860300454003d408079006040300482504005c0d001080c280c01c8203807100407203aa8950140f070401604481c4200402802c010b049801d5a00d0f405820ba41e4802d0b507900d442000b12900c400c0070f106400d8000808100340741984441c1e0741d61041c0f445000340f1f011034580c04460700f40401403001101544c010400062500d110301e42d01c00342801644042c0001e880b028400d0100c0c0d0828903910402540d07400b4080f450480490443c0c107280c4202c2c0c810094450f240302e0591180c0d42c04400409002d40180c0c03028040010310000104107105480c010f040c6030a80c2002811680101400d244501205901c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 67241333 1250 67240083 67240099
    0x21e090108010308031305070b070309061719090501020c010b040b040b061e09060304030e04060b030f0f07020c030f03090a0e060a0e13061e0c08061c0f060204030b040b06 75
    0x248580c1d1165009042d04e9018108a07200d4a81c6450005450041c0744000c5c041c4c01756000c00708440081101420034a030080d07550410b89943c414040d11040c0d19038203c090480400e000090b08021303050f180c9510503ca00000207420162a10381d1400c90300400c21480859448034600001403825000d0600d822104481c10868120403c001411030321421a100d1400101c4404c00ea00c080c03859003c0e2006e07000083d20f500e0b564a441e00d4002c1010b4003500115201e04d2405501042d840d102000303507446000c0c0035990a0f01610f1f142e48882070400c00410450461046401960749070700c0c2070014800b241400341c021901c0d41c1e032000c100441e5904640110402c18070103010011543d8030404850111841d40c0811005a240c000200c0600118480090701c8981070002c070904408180485c4126900302000c10409150103d104807048001a00d41c198000c0c4182c0c514114080303e5110a40e100c0d103d180310b6035282d40c4a42e1800300340c0c1c00130f902c29aa00c81d0041e0400007480518622140d02c000200c0e1001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 67242583 1250 67241333 67241347
    0x2090a12060507030e0d09260105010e090d0201050112032d0507021815010518030703030503010602010b0d0c0b0a030603151e02070c060309080714100c02030f030105010305060d0f0303021e 83
    0x41042aa0740700350190008c00d00348242c861400c0172094201c600303008009100b19078540301c8030700c04c012003a03428108900ca9200490300062040c4a000d0688940710080304240c90345031011960415410030024401c69908002142c078203003003d481c103c07814944c5400791600d403940108610840e0300c0c003040200c3d0310382104011440a03a03051a9a04c5402400e0050302c502409004100c003062600ca0320750103200ea50000310505070814055412200b40342e000f80400404401480302c80c8010000060807035650200622128600744041d1606500170720b00003400c030b952500c43c2421030080790b8000a6a65803840507207200c40e03146038008040d100c0360005620f4a48280da440071903052501c501802c060303071a1914010840c54100301c42045800c2490581e480e880c000340d1940383d20b01c0c0e103039480fa62464001c0020040740080141c3c2c1c0b001d01e800041d03034116031a1a0055000e05401801c840c1e20128510800000507a9034102081c0030303010f0f0742d0058440f18210005030408011030000e020214040c0116 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 67243833 1250 67242583 67242587
    0xf08010b041b031e0207030804060f0c020c06180d0818030d09090b040605130510080c0904060e0a080705010605030c060315012007080c0a06081902090a12060507030e0d 74
    0x216040c40d510300051604060300251307640015515511880382c0c000242903060550040c0d0306400303a805058104441550200e820b0300302d806050540c80940c020581840c02460008080c1540c041800044284010581c00241c103910940e41c0031900744c44042820401400c1491607030000110540080000040d003641c0640969681d00c612200c05480f000e484070b041c1c650307807c06001400c01400c004044264850428041c001c06c5030721504415104200084000c0005020720062802400d04100358403941c403100081d142210001c045841681000d0000408100081208030300940000502c07904000415060a003481c03c0c1500c10101030082c0040340410f05005044400242844000704001c10030f00c4101601840e030303400c02d5019005000810800c08640c420b1815022220a2090740c0c4802d81510018000d82c0c0d10001d500042800c4642c944080c0d009081440000b4080f0013550742c0c07501945c1c0ca485100104071006d42e00d0324180302c003642e014007032520b01d03408070405044003154460380 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 67245083 1250 67243833 67243871
    0x1050f01090b0a0f030305070b09070605090906180702030307110105041a07020106030222060902031e04050304091a0103050901063206040b0915030403080c09010512010f08010b04 79
    0x40c0c0101c1c6075103540c0c602c1d25984000251009010740460303070504a0740da080203490f0741c2184c1c000b550030504442c001581c40c030b070126454090360030781e0b01c68500b41a43c070414000d003208001e18140d0003414500c030704480160b0520045102e089181e00859407843c040700300400f0800064181c2c10039a04240611002030000701054540e4070078080d18421644c2e40d04800c03409042c90f0b44c0040c0d001404681200e040d00500f5000803011a01640309000b2191366000303a00481c0302c201c0700708003002c112681454000720b080e41480d40181c01082240e00b0310340c4622504003140c1645044801c1c0458483c441d010030b58050140541c003104210003000820301d0300e202c000b01c1030403000004602103250420b4003000000d000080e0710251001e4680b5841d941c4561440c15654452000c0d07a00c100440d1101c920f117245400e0880b84260f506503035080142c1c4903242140003d03008074a45e40d05010044c0000c0c041d402c0030781c491500811455440380d03105890030070210300b15140d081130b80e40500c0c2407052802002c003a402d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 67246333 1250 67245083 67245089
    0x603060e150112080a05190233180f010515041b0f0e0a0b0403060504050115030c050108040303020c06041a010803071a13020a09020901080604051e06060c010e03070b0901050f01 78
    0x241d603551071000440c01c1310b040c0700b0508000d014030381f0748024074812035000a00a201460035012482200012150b00310b142585c40c0030b042e400c0d44a40c0c00101d80c41142400200310b1a000002c886203603840d455840d0039500c0c22a02100000f42504c00c00c1c903180741c14000c00c00820342c003088144104680380402045044441c10307203028000164002c0c0301c1c03074890b0148c420040c40001d41c1c50b615540c81e8681440541001d0324295225802c1c000060b21080700f4900090850b607100e810b41140d1031030040191a6688000e2007075003451f82c248034040c20380c0302c1400700e58400c520454500d003001d612480144c0d030b129010382101500e6031050107510002002082480c0c000046d480c0400c40584e140c910754000e4000f44c4a00a400442d0040c00080c4021240c01130050301d4401d0f00c9400580d5505003d2108540c0101c840404207030361200ca000900f4440d0b40c55982091010308941c0c60045407100032403e544000850310400e030303c00141081407050a1240c030750001c802d2002031086046c0300c4180c1d1002c08040c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 67247583 1250 67246333 67246343
    0x1020a06051f0f140f030d0c0f0f050a02040c0206060102100b0a0302150406121103010312030906020426031602090c0705010c030c020c0306010509071107090603060e150112 76
    0x820380b031541d403080c1084154006112641007035200c0c8107080018402c0d2081460441c000c00d084591850b1011411003a00d034094002c00744a000782004030703282100640240d4581d011200502c5c00301d440310303595225990065005180409452050bc021150300010410454103d241405010303a030108518030725112003000072901344403200015868091650001b035102040b1400c80702203029010141c0103e8200c0c0d00e03103540c03c2c01c40d44640c01c255090031000340100802000148000303812003141c0a41348801d0300e000034401086907140c000b00d80c802c0c4c21482001c5102031520018640f02000c81c2114031400d0013440c240f04d15901c00302010701c508507000348a4000701c40003d8116901c00705540c2ea4076000b03002401200044c050107801850031507202c000500400008521a00740018001e04a6202800400c01036070307903180c00c40c0d0041d0040c1d0360103610300601000003848070090090902440c0120b00020701240d401d62020328004100d40030700d6001c00f401d8010404846012000904c080d000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 67248833 1250 67247583 67247591
    0x306040e03090306090a03170403170a021605010605040c03060312050901110d1e020a110f031009060212010f03080405010c02010504031b08010f060b07020f04090b010626010501020a06 81
    0x491000e0460041c4000b554051044104020340721500040780c2e40716a01079191080950300d080c0c000d02c0112021030f800387c0440c10420b42c800c584481c00883c4e030390040c29201c0c0141040880c1c038001a0a0540030380548584c0c3d100c500c184128601403140020781031240c201003080354996510310000d80407178500c900c04d02101007203001d507a900401e9803080c1c0700d005a0540d9154442c2e0f41000d03040c0450704951a44507002c000c3c5281c0c00390300000707a00f5591034024030095001904401001581d071903030b01259426016030011900920300c14060b00f021140705000250b218a400000c0c0428031005900030484085102020008181070324111029034000b840c001444000b1400141c6891146620042805103210544146041c0d1100541c0560341200e0003070044440805290081e101107002d18030091f802004400010314029808440f2014050000300303424806440d540c100040c268420000b05025002e1030703501c000c0282c031811607505840e000e18929410440000d58400f041e20700140700a6403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 67250083 1250 67248833 67248851
    0x80307200301060b03040614060105120a05040804050a0303080604110703080403030f020403020d0f0b07020c010e010e121c0f092313020a0203070309080105060105090904060e01090c050f040908030604 88
    0x700707400c4807000d400100c038090f0752401c00d490443c0080a00004140100617000007190302588102d0407134249000d0001c0401654a4807291f03c80102000307402161941c50030040016161203500440000f5030180e21880722074580b0f441403000356468030100c404114404c01411000a40214200e0340141e098038000446100c0d684410000748101e03000a940305180d204104100007041c45c1512209200c4c0004a8140d124442c040c3e82d519030a0000c207001c21542c0e510a01c483d48181c00360414480014038014110501e4101d40e400c0c0704044803800c40845c5425404040240c1108554844148510b0100551351500c500c2415464400596041c05260b10825400541d200221001d0102866800b15980c2ea0042d4010b5500d5110041c12170202d07003400c4000841c240c043c031600d07100c0da4060310b41a1509900c80e00b0448182001070084450994941c80307807019210901c26101d0491080909800c01811312042106518543d82d616206a080201003070000b041541079035040b42c8141c03000f08450b51 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 67251333 1250 67250083 67250089
    0x100617070e010b25060207030e0103110301090b0112090609030f050f040510030207050718140c0d0e0f07030507050103050a0b0a03060e0a0b0f010e060108040302031204030c080c01090c08030720 85
    0x4100704d0b01c040045220040052180542c0200f082c2446501c80c0100480d109006506441303420041c00102a0b091004200c060016000a451040149000c0030f40844640b41002103443c42c03141603400d50707500e01c0c51608060b0000007001c1e00c0502c0b0b06103a818400c1110800c11a03200b40c1c01460f0050840d00c070400791250294040d82e001030340c4001a14180c0b070b121f0440164540e4502d00c5001201d00306248826000910403c16005d08400866185803648280400005e8001e40c242c2d880301d4424204103102c500d20600001014501c240058400c030361800000500751240909000360562400c0c5660300c950351034035808400c8a1340100c0226072544501076680c01c044080102500050b603e8082100618510203407a060f10f4506458803a9915403c0c0116201c000413103000700564010030410440c3c0d01da04210302e0b4010b1013880c007034183c0100b03035941480765004020200120b07912110392400b007204008082c0c0140c0b2418006604280c45034075280d80030000b2280c02c10200f482c1c007040c0004d5403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 67252583 1250 67251333 67251367
    0x180d030509120d09051203091c020a0e010302010206071b140106091805010f0c0503180304090207050606100f0210020c030c010504050a17040f03060203060a0503100617070e010b 78
    0x1c4004003030100900711030541c540c4912103203a890001500500340482c440c1351512100201443ca08019800d01d00f08005101c81e01100040e880c03400c401d02100d91005176140032003007000e0a040810342010394550f2001a141007405440c00040c0b1150030202017542e00ca0000c6203800c0384d04000d05c484011419061a40100300c245c03c41915181020703c004c103140003041007200020310910081255400c1c5c5007011044406040b04040011020408184dc0752554861861281c1c11102681d1034150707202c07483c6040364810310080700c01c1d40202c0200311407440c0ca105018250f2080f410800030f980c5086100030344030100e032080780800980c00300e98118a44000c1055650060440c3c000f04038500342401c01c1581ca90000310105d641072550003403044510b003050305980840340241c0400c61094119660a0041d400041400ea0044c0000d5030020b00d40c1d41c05c120f00300240d941d019002440c0360604800c44e10204542c14125507075441701104001000d0824041c50450b00100b0781b0a40315414281080184 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 67253833 1250 67252583 67252597
    0xf0902040e07030506010b0c03041a09030601030c06030509070513020a09080d0c15020a0801051c02030703110f03120a0302030402030f030c100b011107030201030f0207060504110a0506180d0305 85
    0x30924101007031200c03200018540c02030368000d034201d030030701d031f99441090740188160702d56040b0740d40040c40100881ca101c1c43c80d00c410429055032035070400025501180c03030b02409030310a83e5441174402003040416054400c00703400044400191881c0c5080101180741944080070360300d82c0c258006012a003143c814101c1da0040c0c0640d0040d00d081180b450f00003000e84424005c2030361807030900042c00442c40c14500c02c441000d40142c40d80141daa10703100c20031041c554000c004041c86d54440f0000d00069400303101e2071020310b00c41c103290608106142e00380040d003005444801e00a41c00800250320790088802aa0702940d11403402607500e41d1103201084c1001d4200714800528800800d079450603030f5010400d5941c00035115010040d000d0310b0001102c0b1005400c803400c0654000d01c2007440594030a411241d400101101d01528141d002d40e0f646085440499040d40e4004524425208031b1030501c0c1c40b04000d000c00c0300e80c14101034444404494146640d135150340305ea00326403211003c00d80180140e8084d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 67255083 1250 67253833 67253839
    0x301020c01050f161d04060b031807170c19080a03020d1803021c0305040b0703050702040f0207080f03040312050903070b010f060c26040602071505030c0d0f0902 71
    0x50311880c200c003502a2105a6a810344000820006000403419114810038680f09540d4100c40081d1080390084034214801c10540090701c648011400c2d055200045001d443c040403003000045140380c0142c104801e0760043d0984048007401c100710f6038400690031044c0300d41250340b0000b91a16160500e1703528842d91144825020350040c00040c182c020581004040c0681c9500d000141d01e4201c2058003803803808002d6001944203c03244c200140c1000c407041ca1486402c11914150329007c1c88541034200c40c004800141300050000d00b10b09260044100c42014001305508000803036441c0507407802050640800003101000040038035120711903400d024040c5090410590811600e281d859078480710054070b2004038100006032840d0b01c122048211509a03881150318544c5075684283d101f901901c00c04102c00000140702d114451100900c000c2040740c000701401480c160644281c00f41400c0c4c0101802420301c200030310a03510800329040030414010003c0e15031111400f8800500b1210780180d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 67256333 1250 67255083 67255087
    0x408121c06081014060105070f052b02100e060c0c150705030105090709050f060c150a0509100603030903020108060103020d11040f080a0510050c07050d0201061406130303081005030102 81
    0x1c2c4200d000c216040036060354a414080e268901034109008841a03803001c0c00a07400304900008185802c800107007007441602075804003010131400f6034a0340c01509590f9840700d409480d5080c201d03010410104120f030049014066200303070700150754841e40f0003000c110030b6601c009050001214207001003848401c240c0c40805050070400002041a0000d0045501032000714020400d03075400786607240100c0321300910201d00c54000c8000d00c025030b0060201482d0034450b2aa014640814003088540300380d44a41c2c00140c3c0f131402460091501c01c408400000d41840d00b0001c1c07012039800100482500d80a081041c060707214003004030000e1096584030b04030b087c0350004c1214800340a100401c22502e120128031845900d0314440e5458664481004101340e00c03400c0c04c4451455103030080d990004070641000d041080316182c140c02c090b0706504040040c0d5541d0802c2c460204000f0103400100306c1900d4482c288451b0070301556a4145a000290522001d9030018006540a500910140202030000c4d9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 67257583 1250 67256333 67256339
    0x70201050f0f0322200303040e090a02040c08011d04080d09060902030607090605180d0206180a1505070b0a0b060703030504060f0b060f03041109131103030408121c06 73
    0x2841c540041d13a030302c21010007a400760221940c082d18034010307458011940d60146400001c909009000b000d14443d05400140b01c00210b0f4611490382512600c020760180000f400c2d10b00c104822a1900030103c2c0034861404014482c04074480c400140c2010346100c0610141c5590401e41094090310440a01c100c0c24011644100300c0780d41c0110207503e01c02d4003103c2031170300c0702a401d80350401a8090000015014040255000301c85202c0d20001c4101400e0b0070780305115600802c426500003964107507541c030b244081000710300304155154000c2c0310040c6c800300380c404c540344000c0c4244134003a0054801c0c00b21801040782c401c7d00754446c81d0b481d070004114076504c00d0309180c081d01404049600380d8030a403424880324150f240c103010b420144880241507900e48080f410b0041c80542000d1f100b5a80004651480c40181d280d00744028041c0e03004c200a8004030302d0351b213800d200703c0c4001400c5600a42003840200192800091100c10900030b18512035262404030758003013850345081c0120541d0b582000400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 67258833 1250 67257583 67257607
    0x6040f0201092706060806011202070c030206040f080607050a0c02060307020c100c030216030c15090b03240d020f01030c122406020f030f0304080915030610030e06040206070201050f 80
    0x10480f030200180050140039a1303001305960b881d00840d04d2902154500a6605174004564020162248640e6030300000c01c0d22500030400540250b0040c1c00c12400720780d8144006201000781c25404031061800510b0450020001031070345e001042c00034003a407004004110030ba8001d00504086100182001510018021008054652200068001d40190183c4a91043c0c18103845402d894004020a001c0c1d4038051800340120044280340d01007040d098000714220103a0360040d8082c1100c0c034550301c3c0c500c0318028803d2031180300c284958860020f0303280f10707030040c0c1310700341c110007082800d003800034468a48440a40c1c1c501c0805c42c945134003500d03250b00c2c07041c01902c0001140c40070316001004281305441d1001669903503910140310b5a194020b00c121240001f098005550151003030072407504164200340031a5052200c52420f0348201d41c08810850310b8206071030131019040c42403030107211540151403140d4850101400203405402e0002d2841e0039640180110761088581e45c8440755216990880 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 67260083 1250 67258833 67258889
    0x503090c0907020c1801030c0b030c0c03030109020d05090a0c230d05010c14040815060a03060e0a030216050d020904230105061f08191107050114060a0806040f020109 73
    0x2007030b1143c2080180c10790200079a0002c5c1e8166980850341d10f65050900344d01ba85542c0004003e81d40801041208062027003007800618002c2010b80c2c4056102c2e0503004c0c100c402c0e01c00003000c500d032580c0110001d0b00441c56008481c1c0880700ea00800e16110030424104e804c100e6400c07514640c001c4409408a0208841540b00c1e9103010990340e110302481030000c490762404c1c89075120340701443e4444e04900d1410820070407241e800501c0245a004c0d2190380369139003019a52802804281030300031205400c145501440044183c0c4140090000850300303150009071642d01202020b4000c0274200c00207810860b540d603c004c41c0c420781b40301d180c0320f2201d981c0c940c0d0b0190008a41d124020952269000c207960200d502591a103441ca4071703a48010303a28071503169a48031802c51588042d603100c1c00c1440b40075408500810150380a040081400132050075070711504000901414018100510100042c140c04a005a00142c0c0000200e8103081c003800125603102d0b4940046d009074050003a403520840d14990 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 67261333 1250 67260083 67260103
    0x1206120c0b0f220e0a02031911070f02040603060203040c090c030b0a03060b010e0604080706180b03010e0a020c03040e06100804050d050c0115060e030f19030503090c090702 76
    0x40c081203a0703280c0c407a4024038040e908002c9180c807402d0001c4843c10710448605070100ca02d0310010b6502a90311350b003d14410390181da203012190b41c00402d00059a00103051071144600d1100103100e1900c3c59080c540080c810700401034505201e14004c5402c560b16030704042c00a580041c019502c9040c181810f04e8130342d115100311100c4600e00801c840041303000707010381ca4071010001c003444000ca14503126480a0a0501170b650f04001c4514a200410760b00d00000c0c00107090082c0040c000707a414007034007400303902c00000806e0625074509420042e005003841260305544080080c500280c44404142d000b0303010305074030898203000204011a0300400142c0c0f8921441c400c45280540b4905140180c0d0b010320309990252803500075810340e4440394001c01c010030404800900004840200b41d20641101c0443d130400400208401414070390351404000c10840c0d44251000f40c410600c0d20b20030000700303000c018001001d01c040440000c108031010300074009090005041403034030340352010340251900c507514 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 67262583 1250 67261333 67261343
    0x30612011506090f120231050c0c010b010c020303180604031401020a09140d12110109050a0506010b1201050405220f061a010203030612010e0a0f0c09020901050d0c120612 75
    0x54006030b44200c1c9203003000900d401501d809420400b9058151102c3c59144650b101e00707c140c10020203894081c41000d100f02e20140d6816152a01c480100382076920034061241003101d034194101c09130341c002c400c0310700c110008288211030448540108880d401079504c06480c0c0303103280b010800199010340081ca00c01d074040ea9800f24160303c42280d000325512070300b284e60304006219890400241420a18581040d560401030054402040524250b40c045101200c0715089480001d040141c10030240d809007503003191303032810f02c813002c1d0405410003014400d561017a5200c0307001c07070140140d400554060914503000400c080038607003007403414121003d6040341d26528000e84a1030015130681c00d103c448a0503070145143d43c80b11010001031a8001040074025580e820240898080070021865861720034818070b1800c40d06400c0900d90b10000d81c2c1309030840c03401004069581da90040844075504600b18002440c0d51442c1801c561460110300c10300c40440c034100020542150100104e03c05a2150b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 67263833 1250 67262583 67262609
    0x60311010801030f060507050d02040315050702060421140703050a022a0105030415020a080103031101020a170403200705041a03060103030c0503070b2e060503061201150609 76
    0x8004451035403007444042d001c00e41040e000c10006101e50420758100701d49142c1581410603c4254004136446a4170032507000c8be540c0c40c94803040b1040e01505521003042c0c005003006191540b503622403003100450510702080c20340c6410400358010100400c10781300c840314980d218926444c2c058a035501100c1c0400240c40350030740c511a5490741c00041c055111130404c4d21a0950003100c0191182e0b000900103c403060341040391200710038402c1c406042214001e550b142203552460030043d0843d600c0c00c14a00d190327401081500109a00403503083c1a42000107690074003640c440c2411140203014203103c0c4201d02e9a4a214254a6000128442500e030119001c001e08949207000c02c19004880e4000d5403d900309000400100e4020002800b8241c0030341e0070b8910b4078040b075030342c11003040013101c50880d002044c40c0740c420b800b030300c51030ba000109083c01c0b03024a1183c04c203040900140401001c05200d0903034030710365041e152002e40003014022411105146c2c03d5031110303000f5028000c0340c0140c01020082c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 67265083 1250 67263833 67263863
    0x140609070303140903030d0f0c2006060d050c0a0e0709050105031e091f020d06080309030a06050a02070203072402070b031b0403080313050d0201140c03060a030b0a0603 74
    0x4041800c0080301d90648882c4038000f0400c0e2107503402d400c82001a68180400d000b01c001e0450240503110b80390640120000b014640c0401c040d00008100c0c00c2c0784c859882c10051040c60300e000203001e68000d0411603030840300104500d007861800d054800c0b0b05410035403020001440d4640c04580b14011340c0a601c40301801034440c4011501400100da0309038254400c0d020090003221084c80c185e403c10314120980b58020945000c00041c840303690100380e081940002d40301da415242d8815203000d88040c002031850100000c00103550342d0400754010348990b603030300081800307010a13a040b510840d43c01b8059810142e50f1f46034400e12180b110083e10b82a41c0070580c84501a4400305002c0300b510b644038034550440c2c84044031031099007a1082d410400c42020070010cc08116640055485402032150039442044a450010f00381508402d903030080d68184070004c5c0859502c1c0c0e003042d03070000c029000e45840303548900c0042c2e060700031940068440c0c0b03200c400344401094944c01401c2568000c0d01500a1012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 67266189 1106 67265083 67265101
    0x190203190216050a031121071805060103021213020402070602030a0c1d0d0206030406140c0d180201050906030a0b100513090903140a02030f03041406 66
    0x10180c084100e400d2200d001180143c5015581c488004e03285641d20b03500c0c0305062820501c40d182c0c0f031103904000c002c501c40400301040114101d03000250344081c9919145440c65028100a04000005041c0c1d40280200c0d01082e603440f40e0103510341d41c1c000c5403614001495100b282d204d0740070400030001c41c03194000b5500409901600140b0f040030001c1c05000e0351042a050103007078800c001034002c1940c1d004004170000383c054072100e03542d61703070380c64a4802480b041e84440c071880245401c2c081c1041c402c00103400c400003c0b803810480e0700500c0600d50649100b811009000030f10401000d08542000070145801002e01d800c0850046160750010b10160084450100020004030b00c40040000c0d0003154001451000d104100c0c400795903c004048003010320b0450107241c000030b07100d010144204101ca07040101d0034510f80d181d0a017403410140c01003112014501e1442100003050301c00d5 = true := by decide +kernel

theorem cover : BRFrame.Cov 67086333 67266189 := by
  have h0 := BRFrame.cov_init 67086333
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67086333 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 67086333 ≤ n) (h2 : n < 67266189) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
