-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4712
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:29:38.328754+00:00
-- url     : https://prove2.me/submissions/34e1f147-a754-4cd7-81f3-ad2f1fd6feaf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 847302158 ≤ n < 847482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 847303408 1250 847302158 847302179
    0x123030319080f040b270609010608010b1e012304030b15181b09061305011106070801030f03030e010203090d09360617010e01060605070803060904031206 68
    0x1e1054010501d03071000f094018000d80140382c40785030010350518194844241080108443c0881e42041151401a4040d801c00074000c643c054141c00c800841c442342001c901d03c0c216141c41c00388602c0b6008074000d00401003c22018001c60f010242490a410300840700c00700601c6c2100080701003100400100481001900e400450040100f0903804000c80d0540b4140240c1092075503003200b2441d1800d0026444100c40d0103880980c401307904810f810000d0103800b20780f054120b080441f0380503550160a000550b448126401d251010200402a13420002c0014003c12010301020780503207201007000c42854020b81180d0450640d00000310340d80c0c5461441282c03290552401c580024004440002d21100800d40c00300f000804040b640441c8280840881c280000e0b444a0a101c56103520000a4210740c2e8540389a80002c00e000100701d081c0c802c0440c1c3c1c00c40b0f0a039080841800002d0120a02080440c010f59903c60f0b01541d065030b4681b100e05068912015910600120b5800c1030000305a58498 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 847304658 1250 847303408 847303447
    0x9050c210a1d06041403090a26070b0715021317010617030a1107030f05060106021c21060306020c0a020a090509151003020a0905010510021501230303 66
    0x229082000340d00c0c0010b150782001426a805140c3c0d800040401c0c00709502c10340c401da03601014000c503441d040d91034002ca04134603140d600c44282068800070708022074003040c90501803241020044e14503581408010b8449000c0d07802c0180440f040240d56640e0060241e04666100d400c026001c4549583c4a5404108030003ca60114043d4203028000031401504445803020403044005181025483c040859100c01000c01d9220a4405d800c000404107850440c07040307440e402171001e8802c40d8101140a0310b405140640e42c028102c41c02102e1801a0340240c02c00d0030190040e0813903900342001845c9001420417508090f0801b403000607907441e41800007981c040040d1081e41c0407590240e486107640c4c21180b00711008417440c0c002c0603d1124000d501c918980d841120f054840031684e880e40c010540c80361481d0810b10020703030780d00014000c03494103803201304c40241188001c10129401e5000910020410303c1281035042e01818000c0b000b02070307481810806000603088986a010240031074400d102c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 847305908 1250 847304658 847304671
    0x170a080117014109100905010f050c1215060a080406022b0609110f1303050d0521060d060f020d020c0109060c08100e1806070c0203121309050c21 64
    0x1008a035111800f014141d0043c0705800200207408103900b80d51040005d00100402240c0d079558800d5089020701807480303501d01501da0f034404d050300d0b04e5401001c6010b550015103420703410b05512066080d10307510001100c00304400c40c44d00007640d80319480d00401a005100c207501505640e81d4650305498152a40b048a05001c130006104156481102008035226a10030480b0540e041140c400d00d07000e000300800c10721081810482c41d05a80e0344034513050a82055400c40010400102001c00c4800f143d01d11801d4405142d00994604250000840c801d00d05400240307030980300c3e01c0b0240d003880b40740d0548001800070729040d5130707131114040324500074407000c6001c5506074078026048403201c2c8580c0d40f1038412001c0c440e010a4840c01c284240300f0620340106082e101d030040084d88100b00c6000d00401d402031600c0d8a4046070002d00344101410300180b41340c1c940101d07505000605030a0840d40c841400c0300c03018180041c454845010010785881284080d240144d0414003a03a0b400c417403074288622844 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 847307158 1250 847305908 847306001
    0x61a1e0c0d080f10121103070b030c03060405070503071b061e060f0603051e0903160b0a0b0103022119090b1006020d0509040c0905100507170a08011701 67
    0x50700d8034202620400d081c0265a880080300d045c0030300060000c00345501951005044030341c096940c09140342c8603070049505d00080480130080c002c29081c58000c00c1d4211106007041d80c11480e0502d0020882c14118190360094450054048140b1600d81c1c0410504418650781c020000044a0b014000c1c0c0628880c07185018030341840003980034403c0c071901d800740b424910a00410240200d503044505005000d50700140000c00903400380082c0b15a40901c0180300b020b1807003036413420048000440f007041d10b0660505004000b981d40962400c2000900c0d2920481da019454480031040e81c040c0010614450f4510318004000b03040c089903010641c80313544600400c810803600c4003002c0740c440440c01c8420000c11014055a41245051b40200c2d46032941d51612960f2aa40e40d40004c40c010103502d440e00102e440021074109000d0b8660b4100314401070840d40d18034180c07440c00300901d64403051140c14000244401c0040580c1002c0d00b09610414071403c0c1401d20030400c4e5001c24124040f41c8000e230b14003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 847308408 1250 847307158 847307161
    0x40f06061d0d0c1206022802011410121109091c0509090a051f0b0c01060909020303030a0c1803050105070801150e060c0727061a1e0c0d080f 62
    0x515012182c0c00e01d86610941d2828442e01e00b0078042040300b01140b04450b03642c1c084c0f02110721140003004a440c41c600d0719001c8131264031614406800c643d001c0142c00b002001c00401c000c0e8070981401030301e00b12103100c003440e0000c5415003011180c80e03c0d003030040d65000080d0814400003440c000340d01021b610705620107954141045105503510301c00c842c001900614501e00181e201e28965114540c8a00f400c11a07451105400c00c082848214580142203141d1012070f084040071400d20034500506007912080085c05110b0b0006070340c2c1e0000400c1010306e26120500504210310510f092414104624802c03c0d0300c607100d203071050180c002150030000040d00c80000244200140320300c084600c1054441c01c80c100c0c071080900c00240c1c4101d448200b28807038003070005500340c0030b260b0111800c1d03102035080c030b040b4050301c3e01e0f8800d484d1a03a0006403202e01254001420352071120882c0e80102c1d682280d11101440401103040301c0c05240441d010303a00800c40b00c3c440c41c0380c009101e14810601196290b00340e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 847309658 1250 847308408 847308467
    0x409020d0e0a1104050a09050610090c05070809060c160f06020105061008070309320613031706010e060403030302091810030b0a0e010e071d150f040f0606 68
    0x1aa402c0c640098004120400d03400300c6130901e94090394100c071140c900451841101e494031481c100f0195040c14410716204000c0003e003800b403180d00d146842928280d40380c91242d484840c0c80c1d024550f107051260800182070800c0c81020020032965000b04043c011259645031072118101009201d5071001d9420140003800510388030070406502c0c400d584520500741c030b600504600900101c4400c551000e02c145440080400c0140c120000d00e4485050848880d00d540d0880c1c01d0a101401000d400d031110382c001800250400700029020100e140450282da43d6440120341e40480e0f01c0e10150803000001c1d001c000e25500d80c004013045501510152000c1108840b0030402c004115006003007845207600c20b1002811072540c1c5074002c0d42540020400c149104505800c440126055141c1c50784940002c00c44c50306984800c20710747c940400301c005a40780c10040d6409507203090121a21032204a5605802560341381d0090030340c066081000c000d02915048003802403480a100e002d4480701180201b4030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 847310908 1250 847309658 847309663
    0x204120c0f05040522030903051b01140c060c0a1803060b0f0f03100216060c0c020a06030203010620011401030503041a07050c04021303050a08070b01062c060f0409020d0e 75
    0x81d403400b00818804511910010030710280b482c17401c50821060a80c00004070710100019110100e650066881031052000090011074002400d03400c0b0040074410b48050a00118465602c00841d11125070341c0c0800c55422142000900034199076182d003848080b05208059101640142040c0c90035a1415001810003840340b8501c0907595140c0d0060504101c854440e402810801c5081441c0c1c0250406a94400083d6582d24180b0340000c3c8114540c84150301c1d22a8402c001006242011440c5504100009080307090403000c0c0d010b407a80c426003101d2200e500758040078035a000480c0403081c0c0e5840340781035601d0b9800307481860030403944100302420b6501364408039818a54050020101d095000d0240000b9421484035240048001c0b08008045241030040f90641c510403004555617011601d011803840006030407a508000031030311039600103090300b02030b50140c0c413184002405c040c01d09000255207110308540e80001c02030100b0b0014060101e0b402520f180c10f41002d050002c2e4152038030307859 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 847312158 1250 847310908 847310911
    0x1180c050313030518130b0301050121020f12011d07050114030109050403091e18050105010f230d0204051e06030f0c1911060105040516030f0204120c0f050405 70
    0x202c81602d078900500000340214010100b04a44103c2c00310358521070b6002481030980604100e82c03540e00c03060304844070b10b002e1080f42d000d003005400d4840550007005c1c010014001d09140240140a80464403000741e980e9800d9a0007451104001e020205400100081206100711002400d01c20b42c400494590b014100c1d96100c2868101480d00316843d0502c2200500030181041d0180082200301140c401c800740a200207940500b162011030b40d1038264482030700307500f03008402c2059142100505c440d03a8031900304091f15221340780100005035429005148886a10240009084009614510501160094021508100d88090031080700000048800c510401d03e5644940208001032811000d080b1642e04506d81041003030602040c840b510b201a0034406e06140480ca403100c841d402d4510070400325025100070b5405016074209002151040000c4038451400e26807100081c940c408101d40c1a10010080712b40750101c84d00075800d0401042d1b10350300815000000d40c04011070740782040d01446 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 847313408 1250 847312158 847312171
    0x3020f120726031815042a1a2a0d12050f0708280902091015080a0e03070602040302090a06081c02031215120f07060c0f050d0306080c15090105070203070e01180c0503 73
    0x81d5100d12300030b040e1b0311550f4015080b440d01030f035030000d542004a80d00c00700c054106110400a0044103000d0002400400408a000040d5400c0004102c0c0301204501c02c150080c9031410006425200d0b4006200a28040c1c09070000601c80c0c000300c4c032100d4181d81c0104ca6114002d0b41c1d08200c944850b60601c1c1c03010003038014014401c2122145a0505200e00c02942d404008420002403080100c5222801d65101c0d03c020b482050f00410148194a0260b03405600500915401c1105924018245440b003000105105181468000c100003290080c41100c1d13610b06a07060455141c900781080c0c2032801c0480b1061801091100b1076000c110000084c0141c41a00e00c00c0141125844c0c2042141c100050580480310003090085007030005008003d503421100858501160b181c0c101862240780845840c8418419000340c40c00b0006151040e0032204000000c2ca469640c6511030300201e4a020001c0d40030b08401c41e000d000004d41c580c072035901c10200108042d41072241c514070100c103d03003600064070302 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 847314658 1250 847313408 847313429
    0x100309110d030c0b041506170606100504050d05030a030c360918171219020705190201030606030e031603020f120726031815042a 57
    0x103101140c9000c038801d03101c052091078156005555035890413807041c01035034100c800e81c1c55145500142030403070255601511041c4203080c01403000c03042450ba14030000d00414003e8a0b45070980c1c1400e0b204004540182c1006071590310300520901c1c1007a0b0f01e034411b82501d030002e4176080c0340001ca103200b4502d4410400742140044685055000591491a021800b10090b86110140025000c40601031300c041c50010003c6241c42e45844c2c10f01d24005440301a4000c0700346000c0280b14010070700180c58903040513441204181044070552600020b10852802910b141714658420480d0710040641072074280c030070303a418008243e89903c2a025141038120010131038000340140d450490030303902084d101c0e501910442d810304014420041c102004000880000c0c040068080d0500401202c0700001d0800c011003403603070414803801c807406d40c04003a1000407405080d1800300c00070b550401c142d403056100c07605020740c0c0d824180713040214201e0340c80e00d89010310351041140c0041c0301e090f542c44003110030000e407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 847315908 1250 847314658 847314683
    0x9031615050a030f061203080c0c10090219270504033c0c032304030314070c0b07051506031209271015020a02010e131a100309 56
    0xe06440e540c002e00d80010405941e443c42d12152104d40c041c0c0b0008103003491401c040c24800341001010790900400c07494142d4010000e040c0000703000a1601c2c1480320000000038900c00c01c0c0b0005105280802502d000742008a0010030400e84507110f07200b80080d070320414448151946100000c1c1c9004480280100b002d80300342c1d5452403070400341390010402c860703424104482c0540d4010507201508085100040f090b00c0107204168001850b034003981c03003220980b44000c0910320030924500c101c0c00f0040800c00d503402c011845004000540d40d880d54800e000507003507030301c54101d0001c5400515040d1882d1080d0350b42c160182c52950849030080d54064040c04a1803000c00803040c503613010204107500300ca01c4e07a036451061034042e05512503054072000084400d05041821b9900c50501e50813444010112010b18407541d80c00003151030b0032660a00303080d080d03a071000001031b40c0784540001003202242081000c1c900d04002c40700210300300c10b08864a018900312a10110700301c40c08403600405800b0040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 847317158 1250 847315908 847315949
    0x106060f03090206090405010902030601111c0f020307060212160318021207090905011a1225151e050901050d150503030d051005011b03080a061505090316 68
    0x4101099060020f4915072170060b10001080444100342d00c020980341e80172061000d1581d02011004480740c1000003003040c0c42c5a6509010500d0308201000107010461351201d20381d80c0244296000b681c6c001804640324407482c1c00110204004a0304982c0d0281610940740c4414042e20070303290140e0b081050904031411503424040382d03c15105e0643c90710710900710b00040701d100c24018082c2d000d20910021594481d4291304080039402410101d220340e0044240c5540796000040c0c400000341e00200030604041510982902400b641d000700711034015882c8640412608011181c0c0100c2450007100008501c0d00e40495107401060351950000d6800c00c403031118018240c0100840d9030340100f8548003280d50f01c0000e480c5034461840852030319147c0c410800c140f40f0000c110b030b000785000c0c200284540c007218802c0c1006080c08034014207000c961800704920401c00d038442d401604000c26200d5446000e03800150060b0005011148640304062110b0074620002000000700da810345c80707580c0580c0410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 847318408 1250 847317158 847317161
    0x5060c040605092e050702240f070320061e071b0510020a2613021c0506070512010911040515130308030a0c020616030c020c030706020c09090106060f03 67
    0x1204c003085858a90980c00710003289245504440c0d840545515aa0300520705c1405941e01ca144504800101d201c0d1441b01006981c5007112421400712450319035800c1da502d015201346440c81202c640c440000301000047c828000740140c01000b002c000c511031110565141031400701c00701c0d46400055454401d58201c40d2043c43c1080b0024440d00c151030408000380b0841381203030481a4400001900038a0f18004070f5840c1c01c0c10b031100d0640d42030701d0345c507840c043e04074610041260100a00801c20003c07010320243c00940d40054141c1e000041d5425810603043c0148540c000030048150310055100008242204d480758070110100720005900b018503040400c08034540d4041600c2900c00c080102030300d000e4010609501946c8268500d5441c2e040c420500c0c401c032030010040030150b500034018452907600c204a42c0d002c0c44650314010034070150b843c070200e0911040110040d0907108041c401704507030fa000300780300c0c3c807050701a51500c00b00e5955031600d41c207030f4141d44500c6002c40c01c59076480748424131a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 847319658 1250 847318408 847318429
    0x1a15040903090b1e0a080105010906030e1f15060815030f0a240e0304090e011a10050c030714061f1505042106200d0906090b04060905060c04060509 65
    0x801d02d80c107000c000e65004013109513000ca00c2240c0050395800c010304c000d60f0021403200c0a42150b14040007078804810030705075240c0440308a622070310311861000d40906040d400504042c40d800150342c541c640d03602d6001e00300720700540f02c90b00c81d0076003d03003840c40e1414009600780780c42a2041c014084403002d501c07594a21000250440a51070320070020507192022401440084440ca0000f155510319000401c4100c840c840403054107641403403030100e2500c41420340c1c064001d004442d000c01ca2080d88900fa600752080100040d2035000100340301c410f001005529058500381796058428940c0c440f100716901e0038200c404d402d482002d402050100300f1005140c2814103140b8200309140c6626a0242042c2c010008e0f242c0c4019032243e018801004914010302c00b0720040003000902d18450b0391055070300c5014209082803690382c2e59000d281030048580040e54050341040f9078603100d0070542041d2000d0f18481344240d07140e1041e107000c41e00d070364120303c1290304a031159541c203070400b0700903010068500603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 847320908 1250 847319658 847319677
    0x60c0705090705070b0c130906050d060e1f0603110a06020a030509030c0616030e0603061305041e050f0d1b03031d030c1615090b03070504031a15040903090b 69
    0x5041c0600c0f40024403a00085d4000c0300b80805030780c3c840300035030060342060703a03c1d030803030501182130070001c00041d1600d15a0360042e65001d0000b1644807900c1c01a940352014200800c1c6100c00200c0990010381090342c00082928011103403a803801400209000030203140d8411100142d110b885a00c0120707108001402c50400014103030317406581c1c0d1400082094100540b17249000014807180c07001c00d44c000100041d800b00aa0b0b02c5401e6103010070001300b29450b0b40807945c1c450b43d21f5000003003c02441d01102080d06401c0b00f1964070140765410b002d944d80340c1402082e2041c0c41440440b00d103150099140c0800c00d100e05086003981e030350983c1c040703000e080744820034200d5504244003a0074004051000c0c044015800d80105260440c0d1089159012a250300c00400f8404091408621a83c0440e980301a1510313064220760340c2d2200441210b0501c190750018282d032064501d005000d030201c0c00c1c3d0354001c03920004080340c1c40d13291004010803265044d1009020850320718003008141031820141c03d2604 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 847322158 1250 847320908 847320917
    0x105030a020706050103031707031e0e010e010203070c0c09050c090d051005070e0411070b0c13080f060a1406031f0f060905041b0810051302040c0f0e060c07050907 72
    0x18019503a003000d1303800c01e8104030f0104408200c043c413111403800304150701c00300511307082c03200d0840e050440c001039200614180c101b0f500c0e14551044041e09400041040c403581d0021952480c0042c401000300001c1d0320700b1616112258000100e410a03400303141d018034032090000c2e2810324001c08000400314002804c482d00d010b0201c40b0940310800d84107091003082240c640c0710b0012185400c0008555407000f030012034000034410100420001600d0b6548140700d0444135545810907001810348800340d5019074118825020843c4041001068040c000c2048100c2401070446030005c0070100c1c20115401d58041e400b621051084414040f07a08000c119039000000d01001454001c6c000c0da801c039044070309065101c4050004014691048656920a003125107150344e09210906445003005000740455545070008180c613034011a8944072103075401002040544210480070b4490990303140318201250014070380c030001d402d20300222001544004085c010550404081241c07000b00580f640b820030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 847323408 1250 847322158 847322167
    0x150f0e0d0614060402070816050708031b0606040506010507030e060d0f02040e07020303070c0b0c0d020a030518030a091208090402070b0108120a0f0f02100606200a110105030a02 78
    0xd44600d90815015809101c010a18140c8220812070400780a00080d001d00c1c4108050404501e124056511b0514400c10150101620f400c1071850441c2541003981c0c2800300049020380d022030710a060759403080400a503505581d695080100700e501c2140c8140c04505c0801c005000a403144610700c40440006080c41d00300041c0f41c0e48001161303a55004d02410981c002800e1140c00100c601d05070f40107280784011442d500d8044001030010070100c03030040c849904200440c610100690664811561516003103449400c042d40c01000f0300340c15940c81d00303501c0684504052503080031044910050007620b503072107918940350700c000c2c0a001c2c410702070300d203004144550210365035a40014200da50003a64070092650400d0314150030b003002e256110140c2d1408000041c450342d0401d080c6100d561031030a003031481840c4124142e0501c0c0100c03286011291a080d00403e881341c10640910042c8951741c04c00f080000703040441d9507182c40c0800f016000e4410380c410b140c640d6214200540d40949a8500541030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 847324658 1250 847323408 847323437
    0x60f03081e0c0a03140f12071e0f0e03060f0c0903160308091801050d111201052e080c0d02030f1614040b0d020f0d02150d0e07150f 58
    0x100d401038541c882c5540c01105060f0103259100301348075012506050100c0c58010781481c08100c0d84141c030180c610f18414800054502c5e405640700c085068920050401c01055440c402811464401d0314040850034280704c0b8507642c140022200e01c2541050f880c3c1d035003030711501841c1071307603401c191a840d905105400c180c500054a4194030001107200755042912084070104100004603050034444602d50003100410495690702d80c4a814650444555072140d5003003004180000160500c0e111150b00f0070080c42100c0040040303580c0c0d41c062a05240041c060308510313090342801e041c402d040c0c442d4840b000c0c044e2280381c403802c00e0810398802002c54500540181000b03050038040114a031010b01d2140e030804c01c112017402c20318103511044a0400507c0503810000307412458126019018460003c10700715191549020b0901c0780d40c0050020f03843c084c030115522441c3d4080821040f07410700708000d04000301800100134081e1102141c0d50303420750005050840b4601031040103035040064005180b0340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 847325908 1250 847324658 847324717
    0xa12030528020d18260702040524030a03020303010e091e010608070f0e0f04060605030102040f080c311d010506040606020d0f0507020a0b041e09060f0308 68
    0x407503803100150b02c407044040200102c51103407035100d0b440c4ca1420909400900d0003190150f401c0380c480064010141d0013010010070780a510402500030385000c1c2404103461000042ca8403a540508210003014a2078091544580c801880213015a000344018441701e2499900c031070b030040a03e0120f0350105641d0b40c0c041c106202c00c514410960350350b1202030046c0032080c800b02010304001c2c82e0b468065132604800a8071908002e040301c900d2000000803500b0011990080401024010020740d00c1c0c61b15a14403610030b60b01c41c0b0405501e4800c1c903a00c400a420044105000305584070340c0f0f00020100f80002c0e0183c04500e1220001580c1c0d00c40b8a1520652404e10465061090000024040c40d00c3c4003804106e5a468002000f50740c08100e001c088980d2003047c01101d288540381ca01d1300c0349107030300c041804050642c0040340040c2001c2030220b483d113802800003e000404d189284406961030b82e0900403111b890240381b0a01225210030707c00308592100801950602d550604502413480d11441e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 847327158 1250 847325908 847325971
    0x211e0203060c1206030d081504110d06180504050d0807030f0c030504030810140d02030c12061f03020f09090f0f0618121e04030507060507020907020a120305 69
    0x488201000c90144040340c58010007580c40b11301540113291000304d5810250502000800b0910010b401c10445a45c9445035084250203a103800c42d0760f0345131141c003007500c8007074142401050170100b8540c02a44042000780900c034003558010014114064016108880e4940010b180c8001e150711208400020070a40c8500010158155000640c50601e480c0007001c07100c014014100910121300140b240040840000c0a140f0040340c19184181092020900382035150394511742c8040000440d64002802180076449551080745800c3c0120303801150000c0c0c03882c039002c040e421000705814100d16084c08290240c104000d00304644c40311410000c400e103015081d08030704101b9008030050080640090810100310b41c585005420103107501100e1080b58001e5504201c40041c0c10700700101c03c2c10941080781d02440e08681514001c0340c450f10050019400040708a0017008148005010980b0101e400800301ea4000880d10012004d101c049001c1c000c00303000d139114061742c005441414940f004429 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 847328408 1250 847327158 847327171
    0x1706271f02030f0618061908070806010504110a020c041d0105070903030e01030911280803040f06030b010e12010e0d02100c0806010903061505040218030106211e020306 74
    0x160341ca2510620900c411030f000343c4101d0094520070b6080c9004c00e03200072426404031003a0f5040c0851001403014000da00801c1e40100558060020080b6501e000499103606959043e46c0c240484a80c016898109104404122006030081075003c981850725401c20151072111540807a0704143d5204a6403c5900c01c2e80e044011a0200c00c08000705a04040714588440003400c00700314132081c58481086c0b000301080d20328418aa0380c41500c00400c1c1c100c8425a0313101c5016241da03c41c07500d401083da501d03803040c020100f0162040d90005101442030083c2070124006079100038811103142c0034032142c0c84014010a0305952900091a15044100914420003082d58020180b0b510008212001c071040d004112080250a00801001e641c00c603e4200803250300c0200000c85103018a804660b1950795080140e029000041607100b461614104a00099045000300a0107907070b0034903100c40d118511a121004c404281c0d800000c511030307406603142c003114406400003c0034280d00081c00c0c032100310ba04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 847329658 1250 847328408 847328411
    0x60204080607083105151e0604150608090124051f080402010809100908191707110123040b01060305011202040b041b03061706271f 58
    0x10030a40c26449400c203a0045102590351032210442060700800341113028400a102d40c0303401110040100800801d6051458500f0585090400c3c20700484040c92291038070100d021007034049025850103124840c2c0c1081031100c40c5030814a032040c2592480b6008215001c155660b40300000344100b10b40ca6a113082d41c01280d0283c02034104400c021103441c80b001d08010200341c282448520607040f1003d1508150242440d0940c0d40d00c4001c2e00749004030194a55110605002d007010800c100d000c064450441180180e02c10800b4003c07044640900340d8681c40800200300c03010400c014022511036007103400c1c01002090036280300d900500c192010380d0000d210462030030700304020311903081100750240403a031605101c1c0f54907004070341c4494546a04040d100d15650340a00c18940e44550001b980d11400c083c0440b07014030b034410060002d0a151040031001004812443d00103580468034511034151040c4842400511448000a81d500e00204001303510640d22890080810800c4076804c43e815181d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 847330908 1250 847329658 847329661
    0xc1c021807051b12030a240308070312051b0306010302070c08060402040e0f031c1e0905010c0e011b050c0d0c03021c110f041803030e0606060307080115020a0602040806 74
    0x78070608940c8103e10786150820070000805500071800c0300d4014800b0a40801c00351f101200c12000c9007a403c0746410301c80e03a4440b000040000c0341000d003550341e000341c5aa451400c2207401748001c1d06c0c01283c400c6c411403040c1c400b00404a10304000b65401c0712040c50010b0804487e82d6562a04480b10340166074103034003042c04c000440c509402491343c0040b040c400340104402c00e4203456581e0291107000c1c0c104d500100c07021264000030341c6c022002c541010103031208032100f02e416080103284281c400d480315400d10140404003801890320b04030101040c0e54240a803d070080c241000070350b400408a8181c05040304007d89a6240b01d26044c0c4175020354414000c1c5483c502c10060070710420020502c0482941400030045030204002558000094031600e082c071800000160092551b25540000d14515400c80d0742450791549c442d803800840c42040f2540f94407040100103040c001287c109000441c0d4200610040c0e603070301022207031145140100e600b0001595640320690f002a0841481d5a11650 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 847332158 1250 847330908 847330927
    0x12070e04061707150206070807020a02060703081005040e07030f14120406030c1713060906061707080102032203032d050f010612020f0d05090303010e090c1c02180705 73
    0x3007254010403030130b40980740080c180c1002a40310000144402c082c01700b0080041c180600900ca84040d49038005c03e00707a582c176414a13002d003180b4801c2d035414011115a010201d07450410303100b2102c9805045000703000342c603e5955900c42400b2010320445071540d08482c1400124000c000c9680f40050b601412a20740d41001001011102c2d5107400c3c2080010780300509036561100b0001e00e41000500d50ba900080f503a50034002d000c7d248108005103020710b4100d00051026000030790f500300c400c084050740c1c120780d41d44160340e0907400181d4081082e0411200903c030400c00503847d0580c128071900b00420f810a1075414410b03004403401a1426078000b0503000407000303003107104060340810280e004001a50502da4000c020810f00003e070214154006410400172105000f03031800400e0500040c8410f14200505036282c0e0000e10842d205807401c1e0020070307072042010541c01d50101003d0308802145141404c042c6031000307176600503a0480c9445a15445000a14803a41d100700c0254031210358034000d86 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 847333408 1250 847332158 847332163
    0x406080711010603170c160803030a0c0c0803181c02010b01030b0103050709030209100504091401050601020d0e15070b070206062b1203110703080f07050f12070e040617 74
    0x1c502880c0581d1605405000054280c0c509001c0c41144007603c81d25a0381c0a006245010540301c0795000180340842c00107241d0764000025449606502020301109184041c11340d100010840000c01c10001800000c0f00c0d801c0c003810560a22401008030703000c0c1d800000a500c00140c40203004030041c6d440c0c228140d036a50300341c01a00c20100080c60204014501230380c0c0148bc01403e800000d1240c1914804906000c0ca00030860010300b40c024020414661540307400b8504110800703955801e54282000281558004a002c000c429040d40307803000826010f0040100d40910f051407410010300620842001c00d1404410f00d100e805e05800a00e4030381456410004159483d031002a000450260580c05018140c1c01c00100c4561000d216203550050a800f03401405803000241e00d9080003140400505078040e01ca60b010712601d04295459494401c000c4446100d15581625a50001c000c0c2d10705103426080c0341a400f050758500724000300c0c6036900040645a290340f02d1260420000380d980042c080a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 847334658 1250 847333408 847333427
    0x305030a0906021c06030b0c0405030a02010e040f0e03071403090604060e0301060e2827050f060f100603180809180a0c09090b031504030512010e0f06010215270304060807 75
    0x40d415102c0c09c0510703100000790384450380b034002070421032030201032900c60b10313145c005c21444140c000d424801e2500b403000d42540c0344c0002005894107010003c8081c808440401152998880a48400e140a09062040c1c031003420003a030260f010340d070703401d00016a003582140c010700525030250098030380d02107009072003034200c0c900340c862402c40d2802014802d0b10b001c082c94102281030528100307655030001c0c20800d003000303502e41200c0211700941040098110748204003500c11208241012103294440d034040701100c451030085000c90700d90400700c801090400d4041c01d01440003c103005019034860071024054001928208041512a035040c00e025400c400e01801800c9060400c101da0304051000a543d03040d005000d5944002690120703083c50f1083c02101d6000300c402601d0b44080d41e588052102011080302d0340d8a00d1014640460308a62011444011550890310071680b1912220112800d9200314807299a07040d4801559824415003030002d000204890b0321102110310704540040d0a83d541c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 847335908 1250 847334658 847334671
    0xd03050702030d0b03030c011b1119080714010603060c02070b0304020f0d030c050a030801051c02181003061a0a0b070b0a0209040e0a051b04090305030a0906021c06030b 74
    0x409040040c5254004103a810074103000601003070004000011034194480d60103110030650a004515084001000c000b500e001c01a90301c61780f5038081020910703110307150250950a600f51825842d000b00345040c02a0030780030700840000c0c92030340d24007c0312400c4039015072040b2400c0c0d031102c40780c007484c42e010f0082100a200f0080242d145190590000724034443c0301c00c520344514000c25890060502c582e40b0380103015480400c81e1203490303d504024010700424481c0c14419861603400d015040c0113200090103184e4058100f041ca84011240310f102048020040d44400d00c8030000000403c60714010410701400062403a0609601c0005105454a081e040300d00381c020200004400100e81e6102e440c1d00171b00f007400041c0c0741da50900005014106a1990b07590074800c0c184c008052020120b412000c6480c8600f0081343c24241780d00f80410b8801c1c044020700440c0c0c00b0b100044a1880e20707080300c03181611401005143c0104040e0000f80f5441901d4900b1070705640700300034001c1060490340b5980180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 847337158 1250 847335908 847335911
    0xd21020c031b091602030f04031b1a03040f11030703030903050c030f030a03020306030c04060e37111303050f0c03030909040320031b1c02070b07050a0b0c04080d03 72
    0x110b007500810b000c0003000d012405088904a20004034170b200340252003520983c0b100c40f42d5955540e00f05080304c44002c0300112a220010400015030020020000700d001d40f041e51914119503913500d9000c002c0e01c41000036994002c03036140e088500d40e40ae0168202551007621920343c11402c5007000d91422a911b0340d4907019503c40c01014038200d070004240c80840b505880e01581e283d0358480802e0034440101041904603040c49070210700d540310f1900040c8140c1659010010101c4ca40010003011040c4c6401070420507002441c611a9460381d41103090365000d0031032183d141007401070400700c59031100c2d802610207802c02080340300c5540d0207022803492500210b0045082504220001d2502540600014140856400c0000c10440b4240a20310540c0000c2d0903242c45410241c51000c41c0c040102c00100103000707810185805c150080312025801916500038104a030401c603424034660b000740c1b4180e81c03501c40c10b055440003409064040d8800d400030324100391210701e0201403910b4100411506010706 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 847338408 1250 847337158 847337203
    0x90313170c060f0d2a0c030819390c02100e0d060603061e06120b07050c06010f03030e040c0f030c0c0f060209011107140d21020c03 58
    0x14000500781d080d4100c110b411540c0c40381007203015451482000071040840741011001050444105060464120001100094100302480840b09801c0c0b42c03030002d0214802c500420301e2032140d0010050141c00311345000603980d4502e40460b0121206144c03d0300b595a035000c0c05142c10151b483c0c90000022207081081e400da40c02ea00241114403081008403c014010001c042d0710f560300a200d031083c0d900144204a59616403e0607001352042e0038600c40b8494182c1c4006a03400480d20030030b400c480c06241c0100c20380107603070b4416941000151400303080040a00c040310a034101400024020100303030702003509403031841ca0040c0c44454011070b5240f0407450217515015140d0007190004e2485d025103000a0014034042c426904050540c401800d40895000c40801b00300280e4014440850241c82d01c40c0c2400220352407070f5451100740036841003520001c10004ac01d040031061260701921902c0481c0c01c4205004032283c00d40e85400c5101d0060344101a141300e00e003024000c603210b400071030350720410f030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 847339658 1250 847338408 847338449
    0x80c030f251d0109150501090e0405070b0316120207030516031b0305220305100209012a14030a0207120602070b090703120c02180a0b09090313 63
    0x1922001c074504a10a86070075018895003070503000050103010440d400d10628001c26001d84a010800d01903a0a61450400303030b102000201e140207021511705940d1482080d0410f54040c10585010307008940e036105000002c02c00d07041c00e0014500c10380c0311901400d07014000c0720f80201400030354030240719098410800b94000c070741d0110031104031120142c180d00601d02c1901d4112103a008180860019600b42e200c55000c15900100600c2c800412104100400740c101d04031041d41c04291000811903442851201d90b03403082ca802070019030740c05040c01d02d001c45009083d81460010b10349603101012006c402d2008100b580094240c400780440c00940c1004c06d49500603580b103200380540c10381604080165420000f10b6011034407035690014220302e160030245c40399652040c00d40401c9403525540b04c1400c818030300c20350f80515801d4009201c0140071024a403003421084c00a00b0f078000d10b9444000328022500d82d0581c45001c0c0080c207000b19903c000ca005003242d02581034001005c1681c154034840d48 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 847340908 1250 847339658 847339663
    0x110405010b0a120c1d2d2b140c040f090b130206041413020a030501030c0e0408030606091801061d09091506031e0c091602210403061104080c030f 64
    0xe02c2030380c4a00ca40c0783c4190b00018075041c04420f0b60f06c40140c0000032a035040b103080c4268a40b4683c19980091031007410500b40c81c03080401150900e10003181030040c0082800e901d50600c024141c002a50299090f08011030180c620b10011155007584591201d4204003124182c65408060102c0058041071150300180c03076031080e4451448907400e0144a5101583c81c603801c140e400060450441d07441110100150281000b44001e4403030b0808448001040b5140c91502403056134420704540c036542d1074a0400001b42c0000e081150000400c1003080c00c420140403465000e0095038036201c86030304040340307442c0300f031030342c440c0c1c07081c040c401c814103101d0740d4580042c4219019911140003002a524100482d02d00130040c90a420350301c44040700803182280114407141d1900094580100b59960800c0060111100106100060b48000403d4000380400b94140e03810703a440c00720b420b00e4a6079a8403080709890303107010f00c020b100100090411200d0070030005c0102d128800ea0140008190100b034030354 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 847342158 1250 847340908 847340927
    0x42d0201030203190504060c0f0c0c03020120030c0709060f05010206041e050a150b060313021201060b0a02160501080615070503120a050a14150d110405010b0a120c 72
    0xd040c035401001040e01c04240034519401c5041e126000c220034a0700c0c2c105030015040d403214000102d03154401080140d4807403d504542c25030000040710311245035500464010034074101c401c5a03902450780b400030700740060004080780140b003001480302900f0841028200d800a5100102601b40c0b03103420006070340c001c0780340c1d64450703044136408450007488c1c03089030b035262000d1074003e046025894404003017218903030020300c40e0320864404001d08500e09050101070301c81581c90042400540340f4100061030f0101c500c0282692201c0003150342c0c1d80c1d40c20030440c0d5802205203c0b005da00907519102d464412500044001c01092030440c81505084006c1002c0e8290360111b0000120b001a41c174041c01700070000c84414200303000c28610703286004c419480c020102603551925240c01d0600c2d1980e031081c000480c1d40180c00300118410013000c8003003001035444540d1401c58000c00d480301300751990368580c85214000e020103000300b55680d00110307000780850b486c0c1c40400d5040e032a210904a01c25404449407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 847343408 1250 847342158 847342163
    0x90c0303091509040603080708070312060e180a020a1d25050c011103010e06011214010510090302040606020604051c0903020d0201030209130b130905060a02072603042d 74
    0x1943d01c00402012501a010070740010300780403400151501080610001084030780c3c020350740e55105104000d112815554130b4864106007000f1200817072031103810181c000038208000030894501e030340e0590110301c44804e16803015990706004260924154034006030303907500c01d0812002e0070144d003081c101d66000110b07030346101d01001030110311400440d000b58001c0782d4010055040310786a603901d442d110542c60048462600284410004c9560051076002e24102000702e8420001c280c1e003008180003207520030040140411684000000250f00c6a204440251400f580682160700c1c280c00c0683c039042208100c500a4848080010a59a40007100000303030380e03048a80380909040c0e1700048010f40a4001105e0b80221308500c8100701c2e0400364042c84861101b510036030b29003100c20440380112418401c014141d40c00680000e030000e5aa03074001d1001c80e2194034031002908a0549040c04154041da100900a000205101c1849800340124581c0c1c6005100820030003183d0a0701140c88071002c400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 847344658 1250 847343408 847343449
    0x130515060f04031704082e1e02090406050616110a0e1b21010603230408030907080d03050406060e070e1207081207020420071506120605090c030309 65
    0x94020714840b0300c21140103260020403954000c502c0d10714247d41185081c0c500e20303844001e45604820b00340c0c40c0906a6140000100d445e024900f0883d00d00c06540501c82c0d1035030280c1d50f6074001c03545903100c1d0b001d0584d02d001d202101400070716514148442c040500d0b0800d108503142d0308100031601e001072440d6071014116103a401d14440d11544514907009800a0180904152065404402d0502c00980c1220000e81c0c0600c006140f98034105038588004d000620620070710400207011400b404020b50700150b400d0100d0b000c2607030390701c20b580c14064040142c00000383c444081c041440b446005040152401485031405030070702140c084d1800440d6291107004a088250383c041c000024003010f002001140c040c0c8000c1c242d440c4aa2800e0750180714100d03c102c1c0342951800e600ca000880301e4000b02c4800109928206103a103810494082601807401e00d140c0702c80000c44c4a08050003640c9100d4441c1c2408039040c1440f01c0110700340540104810f00030350003480856010b0f40c50508941c40406075012 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 847345908 1250 847344658 847344683
    0x708030a09051009110102210d11070c030812060f09070323010b0c0106080705090711010207060c030b030f1209060c1603030906090608010f061b02130515060f0403 72
    0x82c11810562000d0340029040d00e0718800206014602c82c8143d03004000341d080e940301052000c1950a248114030003664101c0742403055030710601d943e80c0034600070701c81d828086d4103100c1c065459400c0d5070f9140e0403c075101040411040001c003490002c4c107401440448092041910201c085004560020702d10b8003010b4403004503590a0405c500c1070440d04040c082500e030150f0f10703000802c0705070744840980102d5610b08140041c1a01002c141c24080e103800400800d400c1c0c640c0d100480305502c0c10326500b46155801c00003200060035920641003001503035100801c1c4c218aa00c00c050404e44034031000e25441e00611101d881c50060030046491102d422203c0303588a000b0342c003480d031400318000003e1b139002448403404014180c02c40032650441c2e06580d40c2c0d4040e1034850008440d440428400c03c810f03290800400d200c07650040803448000e0310b07038400e0b20150301c02c1500051800403180c5203000805a4030024480d2013100d000ca0081e680c2c50a0710018030f44605c000e4070305490b100714030010701204074103034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 847347158 1250 847345908 847345913
    0x2031204150606020c0114040e01031205130602010b1003051b0310030f050a0606120506010302010c060f021305030d0518090601022a180c071205131e0b0708030a09 72
    0x222000406a1041c1d410400e10fa02c07110007950b21024070a5207030125a442c00401601000181110103a0f070401c5802051a4a03650743c450056604001c020140700c03090043c41c00d52000554400300415044d8004a9a19218070600c03402c001080100c9042600b044108001c440c04a006c003070f201755113000c0403503580e510a03500300304403151504020115500d01c0f001109010001580680c1c2d240501d100f0012155070300035034540324110340c900500d41c0c0c001100400c055802850010b0409001d402c012801c0c2c080000184202d038888840c0344c1c0180c034136410610490408014040c0c0c2d24205050051414010010a0001c054003035000c0c0d1242c09040002105a40309004140c0c1100c501081d94511417084a03040c40e145480140c0e480c06500d00c481120380249000241500480804441524181041d11101b1130101c481c1c00354024807800b08030001030004144568801001d442c001c29001c00800c1520408a400e142c1c482c414400041c048100407400c5001142d130005158200010703038031140d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 847348408 1250 847347158 847347173
    0x70311041b120b0d050a06050c0a0f050903100504140106080105060604230303120f0f01030f030302030402042d05010b03251404140f0414070c030908061509070f02031204 75
    0x403202c1e2134020000301c803440104400040c540d03120314481c0f1014040e0750ba401e440d5604500600ca40b400000e241802c440300741074000d80007481402d1005c0c040c2c446802440c1801419650161000c030307000d04800100f45445242849901d000d04403c0c4024001410114000740540c092400394a800f002106051023190401c2070842c0a0040082c06483d02c07003856848040c001201113030b004010440d041c3c00140a00809411035041c0d0358050460b00188080d602c0480003500020f00c102d0f0050355840c008071240c0b002260781c484040540000c642111100380e4101c080d210b040c0e200341c4e8084c90610500070490b2203003d081200b9554070450a00d100341c1c80400700c51140301c075100f2001c00140090040b80d140700050820340103041c01c1d0358020641728942d091000b00e0762084080391070007041c0404521040d01c03030038001c2e0340382d030080c038080e40e0003a12810b100303044c410140d40c0c1c4104444407125015842c14852a5507074802164100720880d41c0f04000c0103500c9114068a08003014000400a4100500c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 847349658 1250 847348408 847348421
    0x201241412010606020106180606200a0f0b06010e0d081902120412060513030806120304090e010f1803020303150a0803070c08010609110409020903010b03030309070311041b12 77
    0x500003d0044566491019000700300c81d010380140000c3c4083d100030503030301c503006120440d1000d54800e000003c140c07049400e0319100340e01604040c015016040b0110303464450900300c1c02d01a030100311407410800c0c005404c5004c02404035001d032402d031031000041409441a21940da0007403030745049240c00d00314101c0c1406122007480c10207071004100400c0d120191008400828030440007004203888141d41c895001d000c20100900081c00c000c0095842e007003841c40105071041d0001124109610b4071051000c0d601600300044440c1c0d940c003264202000e00d070003050141c2c40c04251114034103045490081d200c1c0b20007032007a046c0c4e01e80744611205035111210707141d00801c02c401c20780c0e031520004d213005500c070f01c0144100e04580d803c2400204200c80c440c490401d80754074040f0441d01e091724040c0000003940014501e25415540c0e5503c1440740d84060009520420f041000750603658114a40041c04401d21070400b4001d52400840c005612146441c0c219142141d00308110000b4684170000090b011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 847350908 1250 847349658 847349689
    0xa05040f0303050a022a19180e070f0e041101020a0f0f03081f090926120a05040f030e03070308040906050120060402130e01021902012414 61
    0x103841000081c03540c0714000e0012844994261107882c0701e044004100c00600d55142c1c080d01c003c154241183d0b00d0540043c42416051803c0c0c2002c0c90350360442521540345402280310115100ca4200c00000f90600c00003000e45610425500050306200800e11250001040184520040c0c1701c3c504c1309a00801844810039072164511201c101e05280c490355059010404501048048001ca0341d8081104140f0140b244511a00403029282c0410310300500640c010942c1c10425515050400d8141050780038841501c507462150303244e03500f0810780e4440c400200600f0b601482c01d418040020040039400307040c9500762400348488612400040d007010403a0f4001010078600003400110315010303402a10441e0001d8a90055500748042c0a14101485030946000c2d44c01c80e900080040c42e00c0b1144421070b180c00307400000c216501c4100a42281e01121641c9140408001c4c6800c0f2141d09000d6009106a5100c05000740442c4013845900400030740556070941d402e02a40300b040ea1680d81102c0704510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 847352158 1250 847350908 847350929
    0x70512030c090102010b04200d060e040c030209150a05090a020c06040b07020c0312120c0c150a0506060c0a140a0b0a0902031507050f09010e12070e01050411040b0a0504 74
    0x40007621900707280e106032140c034007650030300450310060302d0148540c04030b002d0703030001d041c0e000c0288100038603440e801824452803007940e0340340c08290451900c58107440b8034443d9004800503801d41c010402c00103002007680e07a4081c1071815003c260303194030480f0b10465505442c2501e0f980c440c801070030040d00407010181031500c200030030407040c00302000035180244c410390250741c9250007000915407101d0344141280510309082106007c48500803d01c40c0d0301603030202d9403070305000b00500420306180450420402891482080c00400280380c40780d103401003001c5412a20781030b508107080b61078a10f1484007810381040c0c1004443c1800c02400002003455120380b02203000d14104508500901154600b41d00902c5045a1410325541c071018180c018001f58403507509090000708501d049501c090b030146d04000340060003040304c3c1c1710320801c280505071280c09072060904002c03241b0f41c0320005a00061040d41410170030000040c10804031426160419111559240010415643c510035503001c0d00707001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 847353408 1250 847352158 847352161
    0x18090b0a090b01090603021e1503090601030606050d111003020d0603050a0b010905071704020d0f060f0c0e010c02240c101b0e090912270a0b030103020607051203 71
    0xd045548003000d8580b1500420aa9980740d40300d500844080f4040250001d1010405007560401c480c4414041c40006000c94081c2e035240c0c107501141e401c21703a00380095900401c018010002d0134005d00c805441d043c1c0742c851011100ea1540b61070881c01d5203899000b6400740d007540180602c01d4045601e06260320030240245a561b20300559104041a4242c1d5000c407003c2c004903040889004a9000c0c4030240c0c2c1d03514040e04c1e64045120040f6024108030fa0012070803200000240910480c81d81440c05808001056000099220140c41407a500e48080020000c5e040c1e45a030703004a6031380c14494041d1021035801708160047c9030142600c600c00d07032092102146051000600060244040140c0300040c8242400504a0f882c19281d01d5040d40c0400c19070848940e1500300350382403582c460050300c1100c003d594100450b80c00c6030b01c1290092000104910403c0c01c550a0010712508005c5c15185107030100c2c68001c00906501060000034410280001e0179014841c041241407070308249840c490355203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 847354658 1250 847353408 847353421
    0x105090607170417250e1005040504080301030209100503060a0b1c060e10060e04151503120f1403060d260405041406030a06050703022205181018090b 66
    0x103001440f00d041c0900c241e56000e07000f01256000e403540054030404203007549080080045030400011f0030140040d00405001407665118080e10b07000302e010301511a569415030040c000f540340c0080c0120940c01000c0b0041145803030000e400d581c0300561000000e03800c45400c00103629024201c002d1501e10000c45038040c02e11003141e100782c510540b00000c89054444000e20801500c0070340c424800c082e00c203400060003140c05030411300b01601c01f5680000e810501d42152810b05002904203551600c0050701c40020b89030000801e2140c1e040c18141031540c1041500081a0340c0b000410031401050f20b04114010800b100c2034480d041b106202c0e9580c10101c8803032010155810520540307228074188008541901c42c0010080c1c0142d60103005000c22020540b40e800140c2000351928080580c00c0200090204044a41d614405404c540205000d403910007040643c1c2101100c096004820f003050154104503150250111160803601080301c015886501009200068002c2c110503600c5040005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 847355908 1250 847354658 847354679
    0x7021207060510050a1802070204090807142e1a0d1a0105040b18060f060a0504050414130f17360123091507110306040201050906071704 60
    0x402c2031000d01104081d40e9820800c140170440d4030a0080c2c000c0d20300141450410190018400140007401c042107140441d40c0340181a0300a000a40e00c1c0d80759900c0c1280050300c1448401d85513028002441c40741d040e441030000100801e840c100110682d561030305200c41c001c0c100d05501190004084165911003401d006a801354441d84c01d03810b0150100001c00c0a01d81407242004600000d840aa60401081070f0882c00c0300028000d00e0344096074900300e4219550700001080d640140d41e0344c55071550b140005100a0360180807280170300408110409c50702c8040d44d0704a203146500074004040d007040c03906140c4c0110b085c0d41c1202200030400180c0288030444002e00340401009905540f00c22418038081d0900035050342d080070300040001001003801003284c52001c00c04d8140d1145d146c90140000b0005100c0c50320550310080c450404180c1c00180040c80d001c40003020350a8020b8003a61805a0000300944503054a180c41003901217980800c2c4244030190f00d45600c03084030042e603500d07140c000003d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 847357158 1250 847355908 847355911
    0x15060305010812070b10230108010902040317071b060804120c243c020702030309060f120408190e0a0603020a0c0c0e01170c0306040605070212070605 66
    0x20a0601000048203000000d1044a814142d0402130910000d81e82d40c6002c4000600b00c1c9181c0703030002d500414402d1214400d1245452459402d103800c00c01c484c0090304c80311059001e004020320600003000070498640d50000c0804103500394a56034102443c0801030500403505480340c400d020540414065080780350700d40a40d025050f0021201d140107000c54080d210000d0003800c03d01516041c030180d45021810702e030110081d400c00704000030700d40003420741900300c134010206000d8840751907070045555180e5a509003403012001d61808199030017080c0d60340f05000c94207019820020b00040640d152109031810402011080c02c0f86050a04042d14241c000c14050030b00c2c023040c1e17503042024600400700700c0250070000c1c1409040070b26008054000b500308000190900a40c550601c00040c0d45690313680140004900d00280c55052a9000c45180030400800312590311001c0110010340c0e001070f89030350048e4004808582c03030ba5402c1c401c030f0074280117071801c1902e4000420031904214a070f4003c107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 847358408 1250 847357158 847357169
    0xc0b010b090a3f051209091e1f12030c050f0a050a02090c0f0406031514010206191d010218010224040501060e15031002040b0f1c15 58
    0x54122035201c0c80320b40f084442c2c000f103800903000307120803100c80240c2400942c14082481c484480311006651125414540d060700640324982000541810340d10300008060b801c40c0c07a4a80140047d4005001c4200650026140380e03452005200100103065480074500d0103400300b200c05d040c083c04036150180040d00031610403940e600601000407480000000c400d040d540d00725005104909940d003e0000c012000340107180080030420550400c0c101480c011f000404a40c1e40003d000c1d0481500d411103c48140c10109942d051030000512a0781c0c006040d030741100c00b40807910079441e8480c01010043c00b41c030205124813001040043c00d148419405051000602d007034a0b40c590a5503001261503101000000034174140b0700b403c9100024070046801d500c41d1180c0d00010758140c483c44400300188003100c0c50f086038010640082c0b00c504040c41410495503104106509280c10201a030107180510450112201d00101c0d0b100c0100185c0c4c2c0a94541c0c84907248200303c520a103601020809100c2d0085 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 847359658 1250 847358408 847358419
    0x5030a1503290f190506030c03010e06090f0102030f07030b010e130c08060f01080106050f04051e011215150e0603010b03061002030c0c040c030b120708070f0f12030c0b010b09 77
    0xf5040810041c0b0a51098400324249014949048480c200404001e090b6540520600080320280e403030034030035006400703000e0300100018580101528500b00c070b0a200300d00581d0060046c0044145e107842c4480c0c04c07000d40d080c08612156604012290315500c02d2a07a50320425400041d0b010241981c03107440c4000003580c503842d296417000f0138868a4070040400303d00041d9030170010030142e40b182024241c1c2d000b90300e1107180b03000c0d5120001080d101e200366101c803d0308001c3d03050f1111982c004100d42010003260b60300380311146c2c180035408503950403481080c0004183d22001d001182c4140c20b86e040c0e07030710001d05a5489503154400c0e1042a0404c5898038010070038031040000d0380d4000016600301150b0304009141104200e400c3c04040c0288003000c9003031540303801e8803c2880d43c0c6e0071a4444000d14850050040c10f191070344031460f01841350301003000c0c6071021748184008d050f662102800d0359a0349440b20030071061031034100c6401e015110007420303002c448030010802d107858400816022004440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 847360908 1250 847359658 847359661
    0x170709021305090106031e420501140901050f0c070303020105010504050a05091203100807080a050114010b041a0426070f03020123090303031302030d0504060c02040506040b030a0c050a0f0605030a150329 89
    0x541303020308102c002f041e81c41c0080c03294004642c440d07402090004000c84a5034280100f440c1d45070b28200040d002200136035194401880341c1d0a00e84204c50380200c203a54288030a042802250f603c0f05140700b0000741c850800400034040081a0b82417000802c100c2c8111003060b941d44003080e0312150403200444480d4200381d0314890b421000d58006050b1145541442e140c00c2c908514a4603000d03490004130554007060000040108405a416143c96001050080000f010302600c604000141c1c000801e0440942410300151b48d00007510f0070707482158202c0c0c400482d1030940400760742c0181d8070000d5151000104103e400e0204062111415100350100c4404c803141e4241950680900d004100004480d40409030143c5015003110750807120182000920051400100b0705102d041441640c40980580c803c21840c106610010300805040c1e0240c0c18982c1008070003007003444040c110700c03500c0340c55086050340d0365440000c0b80003c3d5406010b04240011142a10700030012a0385801203100c0b04d0070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 847362158 1250 847360908 847360919
    0x11010512011203140d050613110a030f0f06080d0206091b270705120618060d170a08010905060f0a170709021305090106031e42 56
    0x40c0c416000c9040d480008a80c280340341c0703000c2d800c000e071026803c100410641c8076851034642e000704a049000800801c992428a05000d03040c15486561440503140c007031910b211a91080964000d43c00910303010520344105c0d0551405010848182c1400c9880c1c07038070000716444002800c1c01c89520076000d0ba0142d94482e19103649501c03a042035201c40724251001132203a450403410168600d900081c080c0c1c05050a05c590201030442150084040b58000642d02543d850840c0c240d60f11482c11030700011003143d0303030100301403252014040030700542c10702c0c550b102008194001c9001544043c041c0c16200c50300e002001b004504207200b500340e01031a203004078455050001030366942c032201510b07400ea800d10300f44210865500341d100b42446802003050114040040b4001400001e8030320003004c8005061008214000406a202009140c94a50164804510103403110003100070b40c40c0000d1086a010b444400180d0700e4a04140c0103801003081c05800014074910070813000c031004050b80c09035100c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 847363408 1250 847362158 847362167
    0xf09030f0d1209120c0213051f0e04050a1b030b151809061603020c01021804050702030a090902030a1803181505180d0c0311090a02040b340f1101 64
    0x1c900541618260818000010700506142c17422510252400d46030b00d1305030300c0745000c44006a0301c01060200010f102403114070710040217170140041805484042c1000c3e03039490340d03492000000601f001e01b1140d034940303100452403030200203640194810256140014040f03111400115030f00e8482c02c0241c0a6800300900b900507903104010000040840303031a0002e600141916150520040640070050300380003040a00181840f07940c04481d40d40403030303041020001500d0000b40140c046506c00c2c0801c0e29059032000da0300081301c0c040c510041c1d0b20745600c1d90100c06400f0951130f0320048194844403004065101050b503104030b400007200710280d9210341c0040d0182a001d044100011030038482000300c000c254408401d4440e00400d0130010307041d240d40705481d40c1e12592058404034100d01d6120040e042c0080380c140d014101c1c0b181146402d0030a8006030b010701500d6203405503900e250010074070444203009038018248048004103126030a600d862802d200b451902115424841401c030a0f00c0e5019 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 847364658 1250 847363408 847363421
    0x50a3203010e1f0320030c03150123030a0f031b0318080606032d070b07030207050108060105071b031403070203070b07020108070c050a06140115140f0f09030f0d12 72
    0x40910200159a0303506003940401514801780d506001c0c0c442d200c009964100089045044c00c4d242d1034250350b240c5503a403070300c1c030950f41d0514009001490f05504c10303903004104030300419813012040806050600302100e005101400c010307074005403003054009154009010840b62070300100c04824a80d11411354940701d410980d002e0380c0550086441d04c002880c07a5406801150a005c1c80c1c9880002448440d0f19081056005075400080011110280f56040c0b100390007a020a003810059030a182d00000c086200d4014040e15040104031903000031096810190001e6400000a844c02d41303903046810303100d50100c00124030074814039100044c465140d0301900d001e00c2d0140c45204041d60f03140e6094681c840940780444041c003420290b0b8001540e14450780351400d0760380050340784941c10030f542c001002c4a10103981050054128648921b03c41c1003007160038a441400000d03484405003000001140501d440541d4980103051800c0c02044002601c01c001c01c0440e650280f06040d0480d6000c1190b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 847365908 1250 847364658 847364663
    0x50310090507120501203a0c05090a0f051305040206040314030c100c090605030f0a0b0d0510050f2820070605010e0106050a3203010e1f03 61
    0x903004009480315940c291100f80d0040d400820040b0300e0300d554082071603920b4056801c0d401e0200d00c00000c0c800840682001070611b03812501510406031681646071800c0c40c841a0164491000fa500c0500c64420f541071100302030001d040207901c030141000403c01a00440e070007002660b018a1a850381030141034052500a4442860700b411500d401200a075071250125151004118041078035008020f50140c1d004214030009551090880080c00e9050650081c0c04011041c4148042d8030300c840d045641141c0c014800092061703181012408520000901811600800941600504458128520070410440d121129941d40c1580300b85810400c2d8204640c0482c10f2058140540c00b40d01555041c1d490f00540200b40c2200000a0903a512100c0c00b20b540d10348542c0104018040e0071900c50140c1010700300203080c8080030000030079105440c401c4482801c0503908500c4100c994030482c2c240e41c2114070f002c555035a182d24042d0005441a69400900001440103030320f00480f050b40d42041e2a0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 847367158 1250 847365908 847365913
    0xc02030f03130f0c0f030b011205030a0309030e060c0708010b0603280f1b030f0e0c041d0303010b0a12061a03151f080901140714040b03100503100905 66
    0x12950444002d4182c10242c08807202251254094081010158180001c060003902c81541c1402c40c41d202d0305001041e0f0259466250040c10803002407008400e0303a100204030b1a0024440d440d508045030381c0b260100080d600640b00040f400c0020a020031040141c031031110007481098203c1062100c144012641c00c980141014914020729201d12040e002401c50f006c40400d0201140c6022002c0301c0e10100046601c0785e000c1d04134800182c05000744000890944001c010701b00071617040d15211004103c03041e101f1a13440c00707102c0811480002008030065030350112a2039686540800e103480c0e00c41c0078100b02090b0b000314403042d03984c44d1340602025600200425107400e02a030500000300d800140c458801e40f0441902d0102c503031220b018040403030b51001d100300f03a64a4600030244c941c1c40050660819a41030103000c05034104032810050304444945062140c1c031060102d0507850f4000c5400c054181b280000c244001c0481c4400010140c0f403040b0300752800c07005142c2840007211401c41000348181c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 847368408 1250 847367158 847367161
    0x30c04020c0f0c190b1c06060f080f01060914060c0105040305031b0a0c031d03100f0c0306081e10020c0a150509120a05070807150b0d030221190c02040c02030f03 71
    0x1c0c03404c2c40071b01000400d10f1101c05e1340e004c4880307642c001d85045420220004100720390030a9065400181079170007000100e000803181d414180d0090068250f402220100006c1030b410f40b10b1511040222803402000354001c00907428180703001481944182c0d1052040a218109018020f0703019007221341354255a00c4181d4140c0c6c80c0d03038003600c81c0341d5a01e59002e5404404e001d01100b03a00c040c014040f407400d20060000301e01c04d282c0204001c494401d4150300806180107014005c1c980700007014610415140101041c90408002d45490036500218442c44070b400455080d2101c0c100051f02c2c06c0d0039101d8201045410000841c103411240100c84c1008968007010b400c1881804030740091802003180e180c0b8614150042d15034a049030302048040311100c160300e40c00c90f0080c1862040351007003401200c2205200c400c9440080d5242c9007181c150100040049000b030b14884020221007050500c0494850840850f40000d0002c0c1140c0030240c1c090f500704451128032510100481d0000707900c248406045 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 847369658 1250 847368408 847368419
    0xf08010e1209010c02040b0d0b070f0201110f0c010204120506040203060f06090412180b0c062206020307030207020d030c0302060c160f14070b071203020a1d030c04020c0f0c19 77
    0x22013208480c240d03000740da141194a0030b07031200696440e145014403804901d0381400d180051095450b11051011a40741c84110720494107008102d0b299500c410103003e440c1c03000c146500740241310303a61040664541d600d000c0d800b0400c02144403031082e8000c40a41d002c3d960344c1c902481c40c1c00811681d0680c0800d07070400060010f96410042507920440d0319000c03409010101e078030508104560040340408402180e4100d00880030000c1c00e50140c2402198159105122003000030009900f0340100083d8010000620442c480c0e81522811600140341120b58601818040e000078a040710640041c001d1000061748070201104903428040f206a2418410400e0b4175800c1c2540c0340e00c601103a00064000b00c8a030110810050440a480d044282956407500c601d009405020040b01400c14540180280760603240c020310302561038009618800685448000040d0900c514021500da00c588080380550f5402000a40e21030b030000681c040302c0280b4494010410004090300c040019800f4500003840b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 847370908 1250 847369658 847369667
    0x712110a030236100302040b030307052d010f06032003030306040209060c1c080a0c0e010c030c0501050c0d0609110d090c2d09022a070803040f08010e120901 69
    0x202018450400c0b40302e0410f50620b1800c0a00303903540c40d0404141d960030710a61510340315005850004500961070b0070b0316603503659112001145e03001042d00c41d0b29201030a00103c1c06c06445442d00c060300070011030a120882e20014a403500042d54a2aa141103001440783d01005440300808020000c504507541c1c001040044c0d171040071126007208050248010443c410400a1b504a00c40d44010034003824195004151101c0100b0009425041a69a64281340c01040c18040e81d4400e10700b4500e031040908013a80d010354075420040c03c0e0340c0384ca0200109807103018083d0500d40513030003090040b141d84a08072070a82e5880f10540895250820000104440f0f0b03a11002c40a440703115a0038800c0d6480545802c0d031003501d807400c1d800440c803088640701c800c4181c40000103042c41d1403085041140c0301c41e240282c9504002842c60320400c2000e42c0c1c0d1030384000c21562000707180d0401141e80d180c1d00d4001001505a240c4100c108941c208a01825112808070b01813021388161114182007180c031400458 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 847372158 1250 847370908 847370959
    0x40f06050901060902070506061014090918100c020705011403010b0306011103042904061709070b040b1306030b0117041106120f181510080712110a0302 67
    0x1d81596164800284894503001038203c05018001500c940d280180500440400e0701008030200140b0202d10440c046041044d07501445082d208040389985c0e801a450842d5001a4204814407035429040b40e00c62640d0485107020741d00e80d094a850340c2ea5040152161004880c440511f02c07020700041c0000700b03202010f150721a50524081040000d2594003e05603489500154400e00d0411008407a8441045110460b540d02110f03452406107006002041c0101d8884a42002c2c11440c002c50504881005410040c20101002c3d40d41c4603602c0340414030662000c01c0c10352044560a40000e6a2400ba00c6a01065035040c3c54001c0700642c499a114488800144221941c001140c6841d840f9207400e0702408500c059800501c4075801c00304582c582105004120200e03401020344103288036400805c4114138080307800c0761000390b91105141e028800d0319640050703d04d03202d10080010345600d4403d0b032000d00d900551140b400e60105005100400350f243c000030b500b018269800140040c0078501c0c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 847373408 1250 847372158 847372171
    0x4050a1701020708122e060507020112020406031a09070e12100504121e020c0607030201090605040f020a150504140607020d0b15010206130210020a0f12031103040f0605 74
    0x1032418140303548501c100c0d009295881810b107002c100300440d40c60303441c07480400c071940403c02c80c032986c0300c203c0780303800c0c618aa0150070704128011a9034021a40150f0b070342c2c01c1c1c40c0d20450081d502d580e2901c130020001d0803004036071401d140541030902c0b12130511125042c0a01840e0f40c410b00101c88080900041d20161010301c100c074400d80b0408044003006106250250384607034020a401c3c00d95050080c802d004941e18600100c03040c00820000c03d800045801400ca07040d0303070f019242d0010303090a0307005200cc0e80c000303054141040100700811080c1015900e400d84210b81072148282c03654a113a010380c211038082008901c00708018030203202d1303155040c074031044010511458107610303a01040801d03201e2501203c2c020701410a2100c0400860344c09144039200784020460ba190058000da001408000080d018142d100d195032040f80c42800700081594025540d0405200340d0f26201c1c0750104545030800001e40341a500c014100100c000301d80c013864101e0011150840162a03a03001000040c140c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 847374658 1250 847373408 847373411
    0xc0506061512070206010906141f0e0301110301050103051003111917010b0a08010212060409020414250e012106090f0e0601080c0d1104140408190504050a1701 70
    0x240c060790620ba140c0d0a100d00e11580c00381020b949060708050554003607800200000900003801d6103a61103401002255403030411030440131115106081e12980e09400c925605942001c40a90b180b245802c020360407188203a800b08020b90b03034148070820025007400003e01da42060b00c1c481c1020f140c1100c0410843e040101070b081d510740c0d2088280c5180e014202001c800365100d0f040501e19140100325800103002c0807000303600d0001310010070301106500030038a510403a80c92400c0300940d11240e11106d1101c615150368000b41c10071000d1980d18101410b50308400e201407075622174415129183d0f509501c1c07410703101c0e10480000b40e0008400810400c080c45243da5585000280e039400d40d0084900341c82040c600040e50010074018241000c0058000040c107500080c203411090711000b0020040030703000f0703609071072a404481c001405052400b02d41c9078007960000900040c08050402845079841114905041802e4910203451a000718400c1c15806000050100080a00032400c00315130f1113400300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 847375908 1250 847374658 847374667
    0x1f050f04240e01050702101104170709020c0303101e140d12170a0e120d0f11030118050412050703350c0405032a0d05030c0d0c05060615 60
    0x24a022240b03000d0858865a440320309010171180c05022955075500c21041c24004017019207030003007040c0b08a105449290706a044064160300044c040000584003108007507548405800080b903603900155500e621241120400060018800e007070030314030022401841951900d8140000e003c0a01e42c1200c07030300030050b6402c180000b04000f44a40d4220b400c0d440c1c40307410351803031445645035500003080071084030f1030030484d10400400042e5201c12611480441035403420786081190180c10540d14aa940340c2c20040d2504082e56910b001d503068070706140790100f250050b1000201901c4040d6000741401c2070a0803424859881200205485400b0341400b102e02c9103803642e03442114418111803500c4d0f0060410440c140c0c04c1e1101c032181c00c8a10042c5140c200303824240043d886000c110320058110060030b400c83c0191760900703001110030300010700b58101e400103820000c0e00c0c1e170f0020b8000c40b198054000f80c10342141c0104004201560401d005014540e0707034005222070511200d401c890382060030310 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 847377158 1250 847375908 847375973
    0x301051216121a16030b0108130f2d060b0102060403090302150f0d02090307080609030423040513030813030909050903090904060207052112060f040c021f050f04 71
    0x1c1ea00c50080c0c16000c8100300b8903071204401002c5035040300c00300e410440140c042c0405200c0d040c0007202c04940003040c45030842400c1c2f900d082c1da0380c007a15554424800880000903041c441e01c2031880d015000390b9003070084d41e0742d80c401243c0728241124000e01295004406101600b440f51550002c1101d6000180c644a03207096002e01c00d800800c2095481c0e600001c0c20001410140038040041103244000d04160801c0c82e40a6200d00550050012a52a517220261302c806110812045404058410410f5042101071600c0d00c01b5080380a40100f05294082030045940c4205503d0b0550555142000207003800e07d030318003030000a8070a0340b0070722050086c0505640e40c000101e000d94400d81c0016502c2c0d2040c03402174108042841404800c585a034998179050410314200c4481909822035003200769079040014480307160410200390001c1c548180060119000180d2010309000c2a42c40c1d1545581301035002c060360030450320180c54845060100380042d003540000b561500e080304480140310071a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 847378408 1250 847377158 847377203
    0x303190b15031f030201120b1f05090a080318011202090603070804050d0309020d0213060e19060803070203034306140f07140915030105121612 63
    0x841c0e800040c07800000070300030450140d0b00080c00c000306118181c4100c03803440e000030304181a01030f91f940c5e0060302c7d050300c0005581d800d80500000c8002c038000e00704030b181288005025800000c2200d0141d240c00c0350225481000209507110b06041440b80304412403100c00464110312000e00807607040ea001d10500d074003540c501010710f2064143d56a40c035101c0c5010f05116140091000c4030740c01785481c102040d00542c80b1a0600103110b6015680c03041c000003a48489802003001c3c2c0d001c0000d04201c61f00b8810b0820160406000c244241c8906015058a510703559032a0721403003074025895881041012810150b420350040c1808280303541c298044c10b40d8445d9544900607141c40102100f5107401c18040004d144292808490207074820701c9a480d00803040000e4020180a0708140f0020800b07802e00340c502441210391210001e044001c13503074400c0d109030b111500b003801803078030544400c2845503009000061030341002083d00c0000000a261103140d01065240080030768000c204803d40c83c218503006c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 847379658 1250 847378408 847378429
    0x11d010312051b072c07050d05090a05010e01021c060806130c0b0a03020a0f0201090b0103060b130e0a05070e16200f1005150d1e020d03020d021203090303190b 70
    0x1034112a250b80c80a400300c0c103d1441030395400170800055071085c050090381c01000e54402035070316034000a940d01da01715038a2400340c902d100100f0a6003002d20080200206401030010f610480140840c015042a070100a03200c1c54080c0743c200d5808400041c0c40301a00d410020001c601561022b10780d961101c807100503540c4403444035008030342c0024200700d016a001c40c00c1c1840c030706d02f807000b00044038495540088142041c4030180195454204c640010f68685070030303040b5900740079030800000544001d110345035046640240c40c54002c42d00c0004000203040501407080b220000550b11440c0e40c5801030700d01e8120300727450002c20000c540400c6e540d503030100001c40350240080024000f120812203440181c64000f8584040000d01404504171629901d520780019a400040d00e80380b00001150049408032405010750301c2503440c0c10399000c0c1a000701d0084500109642580c250500c4800050000d100c15200030003507910820003d9115000f8445445500e803010381e0201d07902900d0000548550382 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 847380908 1250 847379658 847379669
    0x11704050a020316140d0507080a060e010c0203031905100302092a090a0b070f0b100e0105010509010c061a030616030b030f0712030c1505011d010312051b07 69
    0x41c503001003540703020010f181a6003800d000440c01107050140010380482040c0103540111200c10703a620800800384100c0028040c0201155054039660905602510040d40403030320365482d00300f0a8040c14404030449109882903951010201d1300c407500303a4000c1800400140589904800200c0103030f9404014038002c440041ca2001140b10f841c50803000c0c060b0542d8904050356040104103401c2d164410744208940e04001440e07110380240c10004080b0403a80401040301d140c15080090804031408030714250b0711a480080d40507038030b900042d81d80780704000445010900b007104880008003a030704500381c1540040041d0841c01d5480c0042842c3c2103054800401113240e6040340d900a80d41803244611041c0d08800406240c0c205856694031403505000d01c0c98440242c11051041c18083e144100c0f031076910140340c1c0d203030540c6042008002c00b400e000e1246890701c2c1c0c000540513000c00c5091603040c2c0e5000403041005200d42c1d00d0640d90303030b80254102a0b12100e004c10300c904001043c01718100514 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 847382158 1250 847380908 847380913
    0x6050103080918071e12020c01020c07080c010512040f0203060726010b0a110307082706181017040f12020f06071805060a03240806060f01170405 64
    0xb4078000c000f10460100404148007003000e0800500e9a03101001c014200d030780031480d102080081c41c007180c100b2074540c492a050703400000c8034040000c055005103441e00f00481911281601c40ea002c9032141d07089619280020030030300c680d2940346400700030950410302c602c24221100d4010703804681084012100d04000c034141552808500c0d19818140400354900c11102005c3e6040048840d124040c80042004011049118191a9104104070781c40146c00410813601d4404c00a11307014070b02c2c403d0b441c60440c80c807602d040d80180c0c103004060b00c3e040c2a18114440d41401c41001b481070703010804111000308400305d22502c0c1490425501e850155001e1100c5500c4c062850a05150307007068880a907003150f1280401002d5000c000c01c4c60394000e6003910384144590036069180c120010150851580f11000092111140f50117501241004908860b00441d02790160050f46194825218021050f00f2000c0025202c1ca0400d02d00c8080150504102c0070171034107a0781d0343d007441c203080703c003203c990703 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 847383408 1250 847382158 847382167
    0x31005090c0f18040f0515100501052106130e03120903070b18070b03090c0907020d090501080c130609080f010903170403020a170403060b10080c160605010308 70
    0x40005008014007500d040e00c010515020070008550f08142440e000310405024002050400280554840f08160414125141e1410780002000a54425126804910707915440010387c0d50041c0b040d07581c100307010240810413007440d003000e4040c04001440c1c258000d806074000d102c416542d00ca580c08107081c040055884558282e201801400007402d02c0d001a84180301c0b1000040046003103a41c003d81040010313a0105900741c2c018a0032207030790420301640314080100305a8200000e02c032991500c04031030b09861600c84030f0059860395032890901000660700c800c2402194001c022142c2c1041c1c400f0703081032030100021280001c5500380e0708261b0000d4491101004000002c10682507050f60381c4000700051189980c01615560384000c0500a40401c280060107160003800003507503141c0c00141c3d00003001ca0f000706080982e4054041100e46030301d00500c581240c10704100071680c40311251580c048946901c00843c415400c030055000c1070400c0300c480040007071b4072405424001c520034100c05865 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 847384658 1250 847383408 847383421
    0x31f051003020c25031707120f020607090e0c0f07051c080c03091f021207030c02121e2b05040209011e1502070e010305060f010e010806190b031005 65
    0x41900c07140704d001d44c00303203140f114030030162041840c20203c1ea032118a2071210b140028074a4214080c0725006000e080d0b41c1c00c5600c9001c0d822081c1c0e03042207013499003550080ea951002c00d0ba508465800b802030542c54000006801e07207012001444080e0b243c40e04281818003903a1418170307000d16074041300140d900750080a41000c1d085010306d9001403d02000c01e04504d854410f0303917a00d4072001f04d045000c0c1c0c10150098135018565044032614061a4620141d40c94001070140140c0610464140140f0503140144000b00c0004140e0380768910510003845516440601005280c000c90b0520000d081080d80090300807900d002410801e03411085d011409242900400c80c6c0542e0590003a421000c0040d40000c5083c8013450303581c190b03070141000e1001c42c003030001c040345402c3c05600500300f00b04968001000b400360015480340310704505e20f807030203041e8ac0312030116101c648280310344d106a5001c0808580d01c0070610746501003003002c0481c00103400703200e840024a80548032901301c05d07c6654030140482d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 847385908 1250 847384658 847384663
    0x6031b2812120c030203071104181209170303131b14090a0606080f1f0603050103060b010507050d050a0203070b010b13060207060e04090f08030f07080106080705031f051003020c 78
    0x101075043c180341c0a2420152006503e03441442c400500038000c0d00070041460b030341c40d4018041d14142d00d207002c40012151a154066a4040b0101400300c4c01c00480090211a402c0580000342c2d484005103003540c0b143e4403c5680606032510480e00f0300030b81c550394000411038101c0c2c2d600408060f103207960800c0112041c80b902c9480542840e065a04000341401502d070090b1890b40c02451100141030580e94010020b44095020100784071041411840041d4050341034200c0307410789005a0040125503c3c100056030f4500c04c0360340003002c9401c100403081d04280131b00050320341010180185d9103001c10507669801851000d0b0482c01d5040f4010800c002241081c61000000d094140000c150391428060302070800602c1c00c0950380318a4440030400100003040c0c1a00c0b0160360b0054003a500c9013843c04c40c000000100315044000908840300010301540300b802018000c0c800354841920b90388038240d2481926045142c0c0c074403143ea146e48000342c42d403101c0c42103450326503480c2d81c01a101d0000902450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 847387158 1250 847385908 847385933
    0x213030308010b070309030b090c0604090b092a07140a0f0b13051b060c07030b0f0a090c0905040602130806070258030203060906031b2812 61
    0x200d450fa010b01c14100001e80142d2503505030313030b008283c5072070694901080c039140006160050340c00000c0030800042c107407801d030011031078940f044602e40f60994600c1e484060005c0c14131b204128002d80841d0300001540c61000400005005400255151040c41030031440c1c03185040007103844042d03000701c0e00140301c1104445600600550701d41e500b038114549603a665926004110003851880e04001c4045036120812919141044003d88420558a0405e071410520443d4208100352072100010390b03220080c482c0050f600c0d4020411341a43c0d003003440e500001c21000300211401582004000e402c4041e26a00b0001418410000c01140c1780c0120024104001208060301c00c1044e0540d40c3d0400000079041c9514420b504100c400c17860400110702146c0c000007142c054490249400c4280160f415002503102c0c01054038000110b40b180001d240e076450340d03800050707094901e200310140039203094119801c080c03c28420003400c0c02044005800300643e558400d040e810303802c40c1c13564200300f0755440b441d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 847388408 1250 847387158 847387169
    0x6080603030a0c24050c0a0e0303070305040315090503180f010207080606190b03090309030d0f170402060f04060810120b130602040b0403110109091505130f021303030801 75
    0x79420080305240c0a0401070700210001c0c401e6689404202c0c00c00e0300074000d14009824180140864100381c1c0a59031300d036104869080004010007038218460800008407039480e9810366030381e8903080ca16101c440201c51100b8425001e02d4549425002042041024190010120900c0c114250030781e02005100c0000c0408141950840d580c20455034101144442d8051010390317003109000c00850a02142004e00d0308900420980403082c00400d1000002412203007a0940c00c0350246280c5038400d450000d0036416050004101c04690f0050303443c10583c542c1c0081c1701420803810000001541111508030760009000181880108261100d041e03560030b0041050011000416a554840d040c007010020003410344990403007803503020000c099040381c0c01400405402070f01c1e1a02c07840e007001031142101449000403102100480e05124078401c2170503041d03091141c403840710320b04401e00c02a4080340310420880c0e503540400d21003a042c14002032811203c80190070319068254079000d440044181c110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 847389658 1250 847388408 847388413
    0x3090f0a0803070311010f020c061e0c0906070c05060a030b2107120f020913060f050108100b0607021c050708060720190510060e0c0f030705070606080706080603 71
    0x1007000380804022a0700203030301460b1140000038025241c0380503200d40b1003400d00c5244001020950380c031340400c0650264825000c8a01e40c0d081c10540414400b00503640c084581c201040b6100c120b03d4000c008002c0c1503c1501c000c80d0b1540d840c000189036421101290300400e03155071a0480920b091044403d2880c0d0094030300c810f00414080715076071154075004501502100c018402e0610100c2001c1c50030040c0e00404d100b54503c2d018168000b061040001211114101148004103110362302400e41039440c010300030210a80515000e20140c1140300030750760043c0007000304002680311300c140c140a00c2c0740d04400b41c1c5084110700e4002d01d0403610340c1c04102d541c1c10510601c81c80c564000a078803054044020f1000c41ca0300c9980711503042503088905d02032a403051140c90400c1040120780c0b070703005940c04541000f076950740d10700c19010520201d0720740e515506d04000d110071024103000699040350300d03841c14030b08000550350b40208031091a0000a02c540c07050404009140e40000300c0c50f40041c082c0d02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 847390908 1250 847389658 847389679
    0x2809020f2a0102030103031e050702010e06030612060a240312030504240e0610030c1509051203070b0c04050d15110d090b0903090d03111e03090f 64
    0x840a00c14050740c91031850209403810822110380801000400c1016180021956965a0b14014007061580854464003000c2c0c9010150b159000b403094501290701078403808000d1b01000e042001652000700440d521208440384403442071000c201d1248900034001e00041c405680c4000190820b48171690b000031901e040c0c0e024000030b003400325030280280076801c02041c1c40c6c42d903140c1000d41f01844088a484210a24255030064035140c0085945c0c140d600150381e4662901d8590300902501c80c00082d043c6050400100407240da04100101d51103510701c2d01010301c9071100f0004103401a9000c4e900327050340c000f003000024490f009800366080b04000388030604d002e01e09408105aa110700c0005404071009107024031a50741690000500d000707c6044196a51082c1d6031810001c08103444203030781810507440010400301c80082107421164004220b003110180700d1380c00b1148103510602c4180c0780d00545054049400103140c1001c001e40b10300300a1602c1d25800002e1004a021084410b07104048481 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 847392158 1250 847390908 847390927
    0xc0d0914031c050711091303030b030106050a051320030a05070315122118050609030312040314040314010b010315060e03031621030207021008040f02280902 69
    0x3007400d031031164500f0300d952150540c0c2042d001401110716004e8004801c60200081d84140440c445c11082c82034404014240074601814225075103401016045422894184a2440c206a109110b4104044041030044801e034503c09002010407801c010040c0c04010b0000038686402034070740c0b000307182c40c0820070007041c604180396070606440345407030802c0704421140610603010f04a032131002c400008103490117071103000100306c5641209000c0080300c224038042603900c1c1000840d18500300003001103040c440d0204540c800800f000d40224140041400d19400981e0888040c00045020301d804c203262800d06080c050940d1100c802c1c440c105842c2000b010031007100e1120101c20b4035807500d0000c190f580303944042807131480345605048240b4404a641c2c01003100c0116800e225290520b8041d5a0104104080e4160f004660000394007c0351041c0000d103062090079510352190051212515a10054012800c404101201840790490414810003c3c00c40d100c001d0001702100e4404615000c0f00701c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 847393408 1250 847392158 847392193
    0xf0309020906120a2a0f120813031e200d03031a09090309010216031e1106070b0402031207080f13031b091a03060f0c0c0d091403 57
    0xa1955102d258241e42001d00c0e80c804000da40e06007a44146a070070920300b450f42c17801c010410800d5442c4d08980907071011901e0300032194203200b101c0c0c0104110058452079541c3c1045600314100c042e0f42401e00020000120380e044440003565038020888903100d48443c140040308507280c01695a130180c0709a2a0442e039110807002c00800e90309480c000484882d10416145105041c844903540000b4180c18080b43d0103002c0300600464500360202e40313961302d61008036580c050b814417010300400a10040142c008241c86016004548241446000c200c188000540c80350040b01007600c682404908100850500700070118071945d00400c4241882003d6640482e14822044501e200c1e6001040c03400f01181c900700344101460348911100481d0b0f10f001c5010071444031501c10918800d0a00e20f00c54000e80700311000c513000e228050050040c0341d980e8050300c030201c07070090040700345180b040000c1c81401009100d601c620401a94451000c40d19110301014040207600c2c409201e40c00581c2c4042107450314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 847394658 1250 847393408 847393411
    0x14040b060f0a030b040b100e130501060c24110d0b2b02032b170105012c040e030a35040503070b180613030905011b021305070f03090209 60
    0x114507002c10044c64010200c0c01074000810b805130400440b0301c441c2c840e5901315040704055a0150390031b0300b504004500501c242e640070710914001c00c4581c0b603280040b072080d100481d41050761204613241e409400b01e1031400c0303c1c000401c0e00107101c00480c0300b90521a030b0b401350010208040b252109821180d11946d1072845c040900c05081202010344001151402d111401c1800e0314601c01705120124000003002d01c43c1d80700b0b0080c00062294540c1e40b07070200300000717580c16100c040c3d4508103c180c41d00320000304415105900c00180002006107030150b916402102030f84110440036603100e000d401070240103e0180752181d4100384001800005402e110001c01d10011507400b6018510307129070401c642948a0280c000d0440c07509002044006c49000d4108a5070f082c00100b1541c072540d600c0311840c00740c020300c54000e001444180040250398492560591220607035a00b4000d020074030750018079806540c041031b01360583c403007040006d82c1350042d6221804054504080c040da1400750b000078000e000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 847395908 1250 847394658 847394677
    0x92306011d120604020a23090a15080d0f1403060d03140d02120108060f0106080604240906050a0f030b15120a150c050301090b031614040b060f 63
    0x40c00e804041c240603101c00e2a549045014203000b01400307207500d401e030312550700300d40580c0114180e0400043c030300e2403002c1c06441038101803014405600001c00300a0500005402c80d00c8d07803600e500e41510305168400541004203000401410049076205020380417680c3c402400f400d2001d0a0802d150440c00c0307c003184d500c000101c0b041c0310321807101c0ca01076448003801000d111180d540461040c1c4121610f43c0245105802c502c5404030070781c3d841d000070380d90b91012140c8080c10020784004104c20360140202daa00480c000703001242d43e0130000004808052403040c03d463300b10302a602000510141e225200107801c058450084084c202020100c25030241d100080c441044600014418020124201d0058070000d03d1480d8481e81c01c1805540ea4800342c009070390105a0103c200c450018910601a0040c016110704e03007960702c2d1110f80001490b012403030f5a00350244420030261142c010948201620078422101521909102400115035500010070f008100800c40c04144036112003d0750340c1680c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 847397158 1250 847395908 847395917
    0x80c0607022701030506060a0312030c2601031101020d050f0d090609050c04060506090f040b03070b030106120c0201020703050301030b13020a151124180709050109230601 75
    0x600d840802c0450090308011500003181044407141168036050850490340510100e0302c9036118802007103188142880018030054107540c4961400e07010342c01c840180d44460400f101c04a4030750315501d40480e0300c2c1803813038681e803445001441007000030150f00c0c0c12113000b071000380940941018054454800c0d210b11400494000c200000700501941020020950007042800900c40d180f80155844e41002d505c0d500c41e500340407000c642811b0090544038880c40c020107100c0040002824440207003643c030758494060140c00000303e81b07024108000c60090915550b901c400c0102e07140c0700011039a50340449006c59004124441c0440d50020a43c0d041d00d40022840c0d50079140c96800c00c5501703c45100094003c03600910019101c560450115103180741c90f2a40000e01c0c1c4002e03c1c49458891001000c072149804405640860038041000c40e070104041d280f180005c0b0192220a2030036401d0740c40302050689600040c40010150301824500c80e4094102c00d01c100716280e40503500a000418250410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 847398408 1250 847397158 847397167
    0x610050c01061806170a030909020a0c0f031713030903080a0201381801090e1203100f05030a030e04110906040b09090c0f03040f0f02030d090501030e0304080c06 71
    0xd080c00e500c0603000701031542d04064800c05940240f00540b02512a940060b1317102d200303c800199001c10400c80c2150f16a4a51000d6414011240003d403c8010309408103c045030b03a000c00a076a0300c00d0711501034065224000c108a600e0401004070b40c1c01441e1242490f2942c1500c0d0020b504a8000410b9903840015035032200d407500c1d812801040c03007042410860000d040310f0395100001910460030841191102c021941d01c1c0720078001c4050350f0400d40c007109280d1300010810072000c1d9000e8003032400341400342c800309801c1d465070041d00d40058440c00100ca00b04881005512812102c80c0300038401079018cc840c060403074601030300c8052080c03e103c0c065511042864000b08407401190070f2908020441130b1a6a145c00004255801585059015042c410301007411001904d0982e2902c540078004545182e0311039968505800424100f1962840c2030700d83c020043e030701030000d00070251065440e1595246000001010385400043d20546c90f00108820b12541c000030550480203e070030364145549 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 847399658 1250 847398408 847398427
    0xc1103030402240a083309090a02061902010b09040f030c0311011109090a110d0218040c02030304060f0b030c0f060d110301030c06140301030b040c030507061115061005 74
    0xa41c03454003225403c121000a00c048a5600301031110301401c172a48000c40d40560540b5a488280e001070241101001c000150814503d0448403c81d80a07807481d090300e059203100c2d40401e403550084135201141ca00a8561040f80d540d0900c100040040101d4247d00103040a8480324801c000181000c2c2c00c000e0200d407080c00703141c0030b002840710005c009002008030b10301c01e01440540da0030201160340b155210034040341044005004246d008801d2501444c600110b8000c0300000b58044c0070802c50311101081150115130f514451000d035044c480d0051a0b60745001c1ca004030498404c06081d08282d07240000c480840e0714002a80d1100410a4404405042c00c0e0b0000030018051200182c203a00d0400901e03480d20041c0304081c2d4102c0c0d00c12080c130941c05444400c02d0368030172290751403800c40c44000e2004101180010741500c3e08035000320b00840036a40c49490f49410107440c3d400030008103180542024034008208003900c500302d007000d1004003030b0070f1400c000f4400e070941181440811a000ca40c0020313 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 847400908 1250 847399658 847399699
    0x506010903031e21200a210f140a05072c0409140c1c050d030506010309380906060415080d121103090601060f02070b16060c1103030402 60
    0x2013054100d00d00c0c2c560010b0840e01c09015102441400340d03900101814001040340d0034044e00e00314110ba481c0e401860207056403215691400d00681c180340360f2107071a841c04010640c8106c0e034200342040c0c0610340a00c4e0900c5424240c0e84d01910034020488000d0354120310341c01032006100010040c160200a49041c00001005040c01c81d401910014803003010704a8800001500b1118071810740d183c0004104040c1c22001c800000500645a504403054128001e4803960100e030344000141000034242071551540c1062074030864000030030411803103003450340b81920491302080040141000a103490311511481c0c850f0005010640030b82d48940020000101e048040700103004a103085400d200b09480000744145441d0171003e400358074003806804007031410030499110301001801421686d2070503608640c07545c07a0703e01c00d400b103010303c150100311100e60340010400b1241c10400c0110340b85c1c0c0c9082100c00c41e00c089204a05021002000c10300d007140c0802500e6105030110384215880d21258050304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 847402158 1250 847400908 847400927
    0x807020c0f09090c1302070201030c170412050c0f0105070e19090504081909140f01020c10030f1410050105030f04060513020a0e0a06080111041206061502100506010903031e 76
    0x645c0031040010801115400b58040d08000e03000f66824092607200074000c0e141c20031545e0a804440b080c43c400a00170520308031000b1400350061428030320b0182d203115200e04103001d4445801580c0d44030310500c915594001050020070b40200d0f07149443c190910320043c0290224412220016180c000180c140040072042d2036101c01404075010068851602c02040c000c07850182c0c6400360000001c0090a062040c0d12030420503040c2c00071304601c0c17201c2d000c01c45102184000e13030041540f103100200f050402401070700040c02d0044a400e13a10300700030324241c095400f141c0200781000700610402c100e202416907019000341d08051b00258540314041c0c80051140c1e015006508011090400100051840d000a1180c4030b90b03c810020303030751280c40c11800d80300783e45800b11000c0c00510040c06803204080b00500e02a200c1c02c40001c000c5c3c2d176140070440320220341100074090b030400b015002203841c0d64041d040e406582460700450890071a40c010381880c41c1c2c5a605040000c22121034480b0704d00800c0c0c000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 847403408 1250 847402158 847402183
    0x7030f0506072a1b080111130b03040b0f1302311407081009020301030f03080f0603030a030b030102040f08030a0807030b0d061109040609060906080303060f090717040f030807020c0f0909 82
    0x1f8414940c4004000d0b03095031101050740c80030700042000055640381d40341524000c3e42d006040210f25281c01007203002d0b00c00040e01101c1c0002202c52140010380e00c181405628880c4c445480c0744409403008841c13070418901108440d01c9081520900342e034140013002d503a102e42a03040c603841c40d4807180001042d00889400039070b00c240c030005c008002e1062504601030407610984c0d440c59940c4e15900d085000c0c00c0305544060b007545c0f0074071103420218040d801c642c00035170015000506155a030310b40725800c1450b41d03022714200e070800100c0020030381e444404198025003a0905205811618002c03a80049220310040d00b11a03403001d0400e034a00c4050120346070090002d10500620f034603060604002c0500b03120301101c107490714000103003113240842030724803844c40144005c960f03240c80c1c028041c03141030081600040210003040d940e18800c203110301e00e0081e070240004071614081c529001d840b40a02925110070341d03018a400040503900c40394031201c03880040d10315408a490780721145103060020100d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 847404658 1250 847403408 847403411
    0x131409101401350102031b0c07050114070203010609050a05252f07150c0c0506031b191211072301090303020d0c0801050901150207030f0506072a1b0801 67
    0x3015084015000355008403404947c507801054600700b40601c500c80c0c0030743c50040d0380010004025035801a108a500b800e00003c0d06880e00c081580040e0845450790081c901c10782c0d45400340188410b0b02c0c840c03690f00420710308a00c030603549056110911039049841503410840d0000716407091069000881000c0c180346004084011085001d40c4c0d1140454041c0c03a9058500950070321001d4816940d402d10b05401c02440d007640ca0521080c80034680c0300901f14014603100600000c2c03020b0400d0001d0000f5403865183c002782c0b155401d0000c1c00140403104000006e03003000f851403111010340b4221021154080307030085440d44405400c0d12030140166024109510380b102943c00d2607090740061442c152141c108020032208400150340c206401c0c021a40c1200c122030062210000e0000d0250300d8421500480d01442da490b642c40c0c0251002c0c0c10102c0f0950002000d0101d0b0640003080113641e69283c0d140c8420710703003c94400c001c03481140a0003600d10309860042c0c40c0503010040e511005007210000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 847405908 1250 847404658 847404749
    0xa0b0d02060706050714040b0915071e031103030c1b0f1603060e1603021504030503030705090907030b060a050d0b09090d020708070602100b131409101401 68
    0x20880c00404d0100c41e03000c04506c0644405820710300c044100da041ea101380d03240904001c000b9040c8034902c100c400c00249803420410440d40800c14a490303400310f8a04110890030306402500e0000c0034007078905060250740d031090041c4080c00912609a8240d0039281042890b803e8500000c149400100390025810340610555041c00c0e0550302d11030740a680c02000107200780e2560200380759a0f12403001c02004410301c550014401071402d5000103007446006925542400d4894840c80c1c29a030055a01d48049180010b43c11000c1c01c2000940c1e51210b141d040c100701006200d808100d003807003542d074000e042107000500d45071442c019a01241d00c1c12006030118140d0716101e10034030390700c4014104d0304016109449002078295400141c40055076a140d004d402c0211903510800e015101000295500501030070602813810121300c00c8400c4000240040c030000e0805c004124102000355070780d40318040c01e0807034001e4031042240040b41181c24030094086408400c050106401c0c608419068400d041d204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 847407158 1250 847405908 847405913
    0x105071b090f0c0c0f030e031c02010f110c0c040b0406080f010e250b0706181218060c11010c050a080306090c040303020d030c09050414040c06050301030b0a0b0d020607 74
    0x40c40b0200680ea00041007203003105008003510303103010600e8001c0080112000740e00c0000e00c60200311140c0540901100c02c1c82d8459280c50306184600c038540c0300141e559080c180720409540c01110700205d10740c807900d0300e020304100f50705031510002400207010780d4a40c11a0180c50301c444d400f120080006400b42c1d40c1048208503564040e05104c105010306120b07040e00c10074483e4040aa000c170310034140702c0302100d1780d140c01419940fa4101e880305880072581d882c0c0c00440300c4000b412824601d48510540e1249280c9018090600089464611017401e0060400d000c01600010180d00c1647c00030002c42c3c0e071080081c01262150074080c002000f501032038400900b04a10400518050308046034180d0484e62074001c144100d0255110140050b44a41e020b281c13800d0013580001d5049000d441c117010015100d2001c2400c1e5490400140f08140e5150f003003201348680912000081e0409141040c0f440d4510380b629110700c00081c0900a5080d900c854104080d501c91044001c041ea014018580312081d50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 847408408 1250 847407158 847407161
    0xc110109050601050f0f0a03060f151509150f0e0f04060e010315050609060d06110a05040306180203070b0a090317190c020604120c05060d021306050c0c0105071b09 72
    0x80c03161341e0007080b4140304118503241c0104520680c0b0f001501240445240d6283c5030b0140c074800d4030401d1031680d9050710303a0740000c4001c0d8000260190140c6521a000950001021500c259100c9044d44000c06c600c2442c141e4080201003800d426490f01d2f8202c04021f100041c1c0c1ca18112114680c094603040c400507130300d80a0038803941228000c111042c19180c000100005a4008483c030350707842517002001030f400c1d10348200380520740ca000700000101183da481101000d035020700c0c40c501c0810004103003007007001483d015413501c5101414001c0944580c035408a40d0300c030350600030b13617644140200340407191a00c10030241d0025134011004c440321030822200c6003043e0303000c0500c0090303402d15690b4021140d4000c40022058075409410301e458070340f41c500600110030b101d00045540c40b1010100041c0d0303580c7c12020301403258413038400603500c014018030f105c940c61065101320144903051007800c81d03503200413400038822882070034a169100c40307a19080c0f50301790034007901044c5200144400705140b03c13103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 847409658 1250 847408408 847408411
    0x703170919060c03200303010302010309142d01140a020c15100303030606172d091e0d0f0f0c060c0c0615140d050f1504050c0603070e01030c1101090506 67
    0x69266070071600c10045170901c10310003000040c1e0a40e4010401040103511079408411064050850542101441c048040c106801e065150f050700c803002610000544d203800003129100c0c035510080042c00c65903807807116900801480d0340c084580c0840c6120a080d428003802c461803085401d01091881e101c000025215014003080e00005e103080320214a06001e10311002c00031100300c031500c6140d1360749000c22814116104c2200755031203035010f1001039001c06001c0c0901540a010140048040e2491420480d0201d04420341e020383c8440d15101801d0742180a1403003c041a15044030600000a0b007507900341c1c2c007000000c282c0741c0b4090f54004440d40c880722210729a031090000380542d00002c1c2da0207034040c07214020b60074100740700034402c0340e5803603d90f400c0c0c3c00003840344082c1c42d600f4000c007111b54103140508480e0482491294100010410309200201149a04964003410350800c032000074030b8000603102c6103040c140d40300644820640515824000030b42d035000203008000340b519045868140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 847410908 1250 847409658 847409663
    0xc05090f0a060e01080a060e0304120303020903010c3b0a090c02010e01020c0705061309020f0a031b050301050d1407180e0a0206091509092401020703170919060c 71
    0x54142c0c0401c014240d00702d0f15040f200c16200501030440142c0f150001000c020880510511081100103201c1c5211040090307814000d850040c1c41d980b07000240750943c1c0303503489200108182d011402100c1d8881103003640144410300c041c031070295070b146032001d003085041c003a25501001c1564001150300050300a020015000da0081c0030040744650403600340d001b100250303803058209070004c1c40181849000f400241e0003003c1c0b00768150740e4540424081740d1281c4d803806d1104900050300342d112909801000310010f16051103140000b101c01000749140018012a880f48141540040a2001410741ca1070b01c141aa41960728250360b07518083c2811144a04803118141440365403401a080030840740c22907a00900158030b0200300004020004030707052504024803100380804003458aa802c0300070b1160802114040b02c1d0303143c6880c594101e404101100c4e04550081000f8000240784aa080c0010600d420b65207803980070000000f1502070b52055110915801d48000090540d4002d9007001d52a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 847412158 1250 847410908 847410911
    0x20309010e0d02060129040906050a0e010b03181f0c03150b0304060c020f0d090e0f060d020f030a02060d0c0f0527040f020703081504060e040605040c05090f0a 70
    0x1c0d40c160000307440e908500b6031100560064001001404080c0c0704221034403024030410800c2c14000c07184040743d80c10030b8003d64086d036902c030403d10860600f1000c810107040d200b044d4000c00e62400c05404044e00c07000304006908005401215a4002d08100c2450f10b001c8a06803207034144031700c00c09080100400084080001d0a0880840030121a80705240589007284802c0d4690b81c0c680d2070300009410301855440462040850807440300c08140f240b1035205c0311a948207509140740c1400d1080300ca0b000303002d40341c1c1029800d05009080d80c50305815801d03e64107861032100c12008100203170603c075590f00e01a402810001c0c0317100c4500341c6680b1010600546d40c60f11542c000521800300e90301d004150008681c103400c50042d4000d401020004901340c50020310210b03096940e20703440401d98015220840100303d102c02880840d180d0b8060903004a0300a070360402002e4500180301006500250028165030b50301c0010505024100c030541025010117086d4100074107100c0e19103000c0880842d82d210005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 847413408 1250 847412158 847412171
    0x1180b060a080a020d0f0b0a0e0705040e0c010c060b06160b071704110a03060c030e01060b0c0721020d0b0405060a05160e19091d0609030a08090c03030d02030901 71
    0x80c036010349008190b801620043c65100d041e81d091008080501c4c41c195403100680240f0000a0f081ca00c0740d07881054150004950860608002e900d04801c030b4000303c3c0f08505005a40c031520400240c8a803441800740390000c00a282405c0400060010b580066007045c4001814003036502c0c06075070f6141c804c4c82207507020a569a1500200c1307000e4880c17003c045000f074201c8007103008180d4031510401034200080c08000c03171a030381c0c0d51903000301e5072451443e201094407844030b8058030400380b250f40024080c82c450140340100d0f49000f035441e510140070b1403000c0c0b403010300c460ba1a0148a901c060394540e0103085480202d01c0c2e800d054201800440d800c071014420f0000090031a0080d004090207107216021500c0c0381440e625040e24185011055690000600000441c2ca0901081d1340d000401c0c4411001941c00000c071100e80440c010003e0003045907024070140302840da00041168012000c61600c14960348a1007040c80c00c01c1c0c030070544254184408110044000c1040d4029070240c0c1002e4003c0104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 847414658 1250 847413408 847413421
    0x1050729160909111204061410081603020603010b0d0e1e07061e0507020102010b04050a1b210209150403030302090f091e0a06050d0c03060c080c0711010c020301180b 73
    0x42e00d042c4d0904401c2944c0c140034481d040c44104442580282c855080421800030511002c0c00041c4122100b5480e5413210038108a0800c080c0b1246070003d205080400c0094110313000f00e0034920042c0324424a505000400004007081c1707a1211400342e0310031050320341c0b101005a10703140004280000b01954041c40d240020014068605d1090322a801c00007151270400d9981e084e100ba03005814140d056540703c1403111142c1d6924442c0078440d00140a001035401c5070180200c850311a098032840a02040442c40d00180292117516444004014030141e551103c0101261180410241c4600030540200d000300400d0b03015009441c031944181d5038540c3c040062401c0100300c20017a00c603001001c102d22407001e00b001510540c20b034021701441000c2074103659000131868840460b50103a610003040542402009800c1c0503043c411141c1d4905800141080c01050000340b00b400d000078401070300c0545a0203d64000c50020141c2d41e0010b001300050310312024055450806107504031100f41c88000082c0a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 847415908 1250 847414658 847414661
    0x109050a0c08250e19031205120a0e12030106090503061012020d0227192903240910110d0213030209130311070501050729160909 57
    0x20803040e043c282881128100f407a601a008a40000b504000581c08252110b4a900000c070108200103803076014440e2139402c240100d40c1c031400b21141001401c110054520a40001003904140e03840300010b4840d1006a18034a0100107031310b10240ca010100c00003407516003058401048600030350564400b81e4500d8400790100c03046001c0c0c0100c041c642c01c042e50160400c3e0518081c01d500c0a0204520507156442c1190402003031800d080810068004002c0c44e0348040c1e100295400d4080404d01628170541c1000b07031002021103040d6010b21812214600d030342c1c0c00b00522a02c1c048240316984004518282d10504d40d102101e510082d44940c612840040c0014031035060310042800c00141800544200ca9000c1e6225003001095008191004405680c845032002d00900300030b151030041507040c0ca0050a0350754100701140c0581c00101c03040200d40d030440110742c14694025034542c21021281003001c2c040c505402d02ea0000400c40c410860041011181000c510905448444400340d84030040740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 847417158 1250 847415908 847415911
    0x607022404080c0a0602041202041a06090d030c08040608071701080c0d0201030b03010e0a140102040f060809030c010c120e0c030307061d10050f072f150109050a0c08 73
    0x902003121000014046040d5201400c0d1007510346080e2000c6000703640720f01069800507048280c1c8110049000d4045162611490110348103005a0012281d4180e0000e0003034060b01000900449140c450002018405c41302080003030341c8081d60361f440319242c1600412080c411120790020a4955568114a0500b2a1624100c0d600c000040079101707803000620608510410089050546904400d0301d165828001c1e8003004011800501c2c4000a900f040c0c00e00d49000d80c42682e559104007c18065020711111080a40390f05080c18100340d201d0314410380c958410186c64051a52070441c1581c62541c1c001c0d16041180c100501c144903010803141501c1d12404480c81443c0d26900811200c0006002904007503000034044c031042c1404020f11000d282800310f44201c100c15176a8038020891460341e00355003d40c01c100546029040c00111000328240700b2250002030500c4ca050200501c0c0e801010801c0014a1a25031000074540d60f681c100c0001414056030075060301d03402e040d40007660034440c1d010396 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 847418408 1250 847417158 847417213
    0x608070e071715030f03070501151703040b0922200a09031104110a09060f03180b0a0605030f0309040b010e010c24051609050303090604090510031202060702 69
    0x441c8952110490f0003040d040110b241c54140c00f44518410300c03d00b0910107030403828001c50020607011800c90704105e40b441d0541001c0d1341c1c8500c0040702d200b040c5002040e503041d21103c1110301d0380e60704403030009543d00c3c1c000340c2e00c00480000b04103031040c0c2c1c4100e80c121400702c4001188400c1c2140041c039001155000e44514880004c01c111020404200c803d40c040303550080c060030006404141d141000140c0d03000c5004800401c161442c200180d69010383c0a400c10345091804100c40341d50503842542400803030f1742c080e08492408011a5803152280c1c807110041400608681c2203c02440103941c69401a02c050741c803480c075081c0418a95401201008070340c41050b0347c0c8070b440300041e0f030701d000d01c4025202c1440c401c0c050f96105078016500c140311f0240554001d2191100300719898a0061120300182c0006019800c180701501c81c546420040e103040d03038091400420640d613140d003032210760342040e8800740c02d0200000c00d40b4501600807820a000391180c0d1700f641d03104020001e0b4405071401d01c03506c9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 847419658 1250 847418408 847418447
    0x2120c0315090a03081f1e0503030a090e0601090801020406030b1503040507060804030302301e15030a0507060503011a04060e0d14060405070801180c03061e0608070e07 74
    0x2800e0009100380342859100380c1d6541c1c900300280a401a02540c02029005010400c01c10401f0007910284000000c00414085005510b040c1a86800614884503807040f20340201c801004201107030300810f600380282407044021034480d41d1350440140640306110030107005082d011020b1175185044821240f18942000042c815545000021a0207010040084d01010760070b10581c81080212410328444281d0b400381146400e07900400d600022002902c284804c04080d075144c0e0a4110111100740d1040e0b10358010300398001206c0100341040e00c1002d0003040e030f00910902041c00c1d40c0000c080c606071614800c00300ca1400b904407060016100d02c0c0651404500c280c8e082500c0b901e00f14810301003451184000c01d403c14102040b0510b84001a101155150042c400520556400740314180b0800c45082ca5252540e1580c1c850170656070881c000a09660780341e5400010100f81c15448883d0801d000350200162503a801540d034a4100314045c4801446407072021814075846682c403601c180d0310300b102 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 847420908 1250 847419658 847419673
    0x4051908030313031e020303010306050a0c08074505310e0319121a131803020102070506240904020406150306050301060b030717070c02120c031509 65
    0x3103a944035a00030401c0381007004405036943c02c2c0101d507880d01a5070030182c001f991a5411440c10b070055500040603014920b29003171010905d6a803190404e6000340f4142002003c041080a03070600100105032141303a59048003060350011901c1241410b94910b1800c0514411500d500c204103486c81050111001554180f032031500448100e4850200101910f50000b00242564107407411078010f0384640c42d1044451600c146002e41004528440500800701041342c0c80b009450484403401c645840c2d030250040d80c10a402c41c150a42c0b0078a40c90710701c595a119006024540240031b075200c1001200e5a003d00000b1400c07104031110805401070301150312a20822040c2e00340980c102c00100140d0303000380c884400040e040d425482c08200000160b42c00306600381810103141c00e60741e00c0d074030030750950704108108669030340d100070381d0404181d02d1b00e9820080e4481040840c0c0c16594260b01070362040d080b4203c551802e40009007000c0442c03003074007621a0048030040032061660129054089030b0000003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 847422158 1250 847420908 847420921
    0x705060c0306060405090108030901030f060b0a03022101030f050d0206100308090f06040605070203190308071101090b16120501050102031c20030405150606041a07021302040519080303 81
    0xc05594800c501419070750405580710005540c52000b03174850a016000042c0d203c0b103a50b818092601204100070041c00780c54070344130300003180388104841502010ba000c241003100d00005545090301a4014454031083d5840c0d0520741814056188100c81521504030000f80c41400030a500c3e01c04c030b40c040601100d4600c3c684503d441940980d81641e03200c2030030304c480d00b071640d204000750001d030100b90b403400d440d801503205140c0b030200c9418004d0510540b054901c000a5030180b051540a201c0e480d20180c64502c04880d14054159600001c2c1080c41103410045018007005040e9803800c502d0340c81e0481320b00503000d4207089400070b000d1280140c200300a90100c522600300b410040500d5494000b40c81c0c4880c3e8005001003403905203d400e904030003c00d01c42840800c108140b44840c1304404c4076400d0428a0004810f4415882203442c0c02c7c6000800301c281ca00f40390203aa10281d00130b07001581a00580090300025402801190b11a040f0400301034440d21400b1a00c40980b901e1200840c510386030030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 847423408 1250 847422158 847422181
    0x150f020d0c140313140a090902030d111203011e05041808250602120610080a2a090303080c09060717090622060c0b04020f01020c030f0a0b06010203070506 68
    0x2d000281161004100f07032140f58080420322401040307202802c001043d402002c00c00c21050f254043c80c0641d051940c0e40c4096500071540302e50309000c50a0a0751601015204641003031600700c0f0101c03071800084000111408012503000144106040749804c00b921502000101c41c104640c90500c13000240030b03040054220303002044803d0b0a1040d80840d1000f800c90080300325440e80e400c0302c00721b4001c82c1003604444002d40c4243c0107501104e0244507404402e000a11404008144280d0035487c0c440740c07810050210510440350300c00108501c112000780074090145002440110000f405c200c001480d8803101c00309403501404001d040b10f02d0030201d0303200e481405818003803100c0310034820040701d985540c4c0d180c002c09480a2054090261f0740300035050030780e100c80f2030703000000344040300740c045001a000c2e0300e5450303015034100c414400745c03903c02004034686040e01149d540c151160404450300000002224818284280b00302200390381c698004917181d0080020080c1140e20032400b003519041d07074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 847424658 1250 847423408 847423433
    0x1e042c07020615060c071701060f06020d03020f190e030c0a080d08101710060e010f0302061c0e011a040e070302010807140706050106020d0e24040e01150f020d0c 71
    0x14111400c1607400d2400c17500304066540180703615152168904002d141c21700810005041380707500d0101180c500b01c0c000e5100d640e440d05e04020582e00003900d01c0c8042d100720a4801045000d03085491800051300702030500402090710910a00c12143c16150510780004800141d90140c0c1c041c244513002c40400780c0b843c180152420895402d415400f20300c0320502003000c0940340b00d40005052040080e06a241194050740140d00da040e0180b00500108000d44a81c00889505642c0275581e0404581074440700380310b1302d1601d500142021034406000d5015000202104941d1a0245034016103804110403075103000c20251581c0c1003080c04101660040d10355903442055400c141808440c50003604499038080c3c503023114400c0d03940005000c003550411504000420328280b05000c0300042c4005610680c00d0401403c64000007584600c80c0413001d02070768000c0112030714102c041e503101c2c1c600340d0102940c0300560001a05010700c8880311480005c201282c2c410300d490f020b45030405601c0300607043c030380e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 847425908 1250 847424658 847424701
    0xf030207020307090c0c120804080406050d1b0203041e0f150c0822050904030207090c02010b0a030501020d0b0a0e0103150b030d0305010608070c05030f1e042c070206 73
    0x10314500140320138140c02207604540d40c564403017841001a240590f0700d220244203520801000c0010000002c0d408400c58090390424284151580820602ca00141c101c2d04c00815207040c3c03013000020100e800101410940c0d0001e03403070350b0078081c540002d07646125051040345203000000504100c405200e2601da1901140d901d4605448a156243c41001f0352041d180701e040042c5411150b400d024440b40c4400c09040d0441c2c401000b800c0c10b460080d5102c83d1401455161640e402c19000054002d612034455108064400c4282c282c2d6424100c1c003c0d08917500e0308080506007105410f0b01e207040e02050086c2d42c1d980c0310010b081e03401e5031110442410a00a06070300d00750b0301c0120100340d903410000c226900d00142d0300400c596052100040c00c00c6d001502860511284c0c0c201080020341c0030007900c15840111008a40b50141089003408920b000085203200c8840060041201d4058200190b1003110710300e810121f542041180d030a105008407802e00041e0071080200f402418617013105005e004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 847427158 1250 847425908 847425913
    0x6020a0507080f0c0606060909040b091e0604060506121e07050406030807031202090109121a0408040f0f050a0501030504020112020301140108061f200d03050601020f010501060f0302070203 83
    0x6140e96540380c10b0f40c81920107000c16000800c0716182e900302001000da0148042c0c1e150303403c02c8100d02c041019214098002001c1a640358001000ca4104000d0110254141d41b4024503550b1301e0154180c80c0d10058406640031810800020a1414000741403000c0b000c8030001481038800690003031000702d0031401180298002e000000030076070780301e010300f10203503010707400c1c240e600c040c40d02d0060f10032040d449003403c03814018050210141e0b00010904100c500c54034820804508624100740000c00d4001c003001d800f08908103000034041c2d264040c0094070383c105201000e85840d500899052407940c420310303511010200050015502c6a000303030b0340040c4103051040c11041d00c200c0410680c1c01c01d1b080024560301c1d0344001051136911145041d040541924101c202c00745610265a4001418100100784840d01c1000c6031051403901c50201b40b000500103503110b41502030b00081c041c19003a25045d006100d020750b016036442041c4603040c100d4882d03849442107181855020f50294101600a0f030341030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 847428408 1250 847427158 847427167
    0x150408071b0b07150b010801180b1c0c03120207030203060a021804090b0601020c04050606030402010509011101020c1b10081605040b0c0303010303090e1909020d050d090e1e0406020a05 81
    0x209046014081c0c00f0320819a40390011804d005100440e001c2c540401c1c10444218010480b06011491a5240b43c44803078011a4a01644000c2a107000c0c0c0800c110308119415103201c01449200f02c441030a89204c0d00205154021400003241d40e41003a001c041d40c590011000b164460306194000c206140300301c456010061200c800180807201e2200c2d059440141000400050350ba0500440041c04000c90b010015401c013a40411034601005200a0512100003006500e1760302445034225481c085074004e65403180501034254403180801c0109a01221004c043c10561130000c0343c058400d181035441c04950b40c1d40d9807110444161160116080c848104008204a0041d80c01015403a00d044000c65807075140d40b030010211031703159100301818420715080c41070301480b80c0c00400302042d00c403070041141401400010988c00e82d246009100b8850080f11804440d000014041203440d504041130f0207035111102c0c961900e04010121513003051401c009000548a580540383d14070061400380c0c00c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 847429658 1250 847428408 847428419
    0x30708100803161202012906120c0405041808070b280506090601021212060a17010942390302191d090c0c150408071b 52
    0x1164407005210000300030f4202800300340f00341000c01c2800c240c000c3c4002c200c1c000c40d1200403c0810b40034000c000e0140000400500d056481c8410744920308003510718100b4504141c4d400d02d6441d41309100d403a006909000140440b940340780e42c1490580e402c00a41c900e0110383c1c1d556904034100091009485546c218400d40c61a08101c0c0c4400c5980740b4408000340380c4c1031a01c03c0007002c5074010070680c1103510440d000c12450ba01e8801391011442d6020141c40c280e102c0000042c081641f5030041070f90903511800d41001050150041032442d40a0b85282d07600748221b00012072512110303040075020b81440282150042e0900305c220054090540c0d0000d130701740b03032582e01c10400030400041c0383c0341540c5e60390440f20842c40112500c400781d01c02d0604501d005d407010071610301d0090207010302092000b060191041c06075403981c442c0105030002c118492a2400e030792060600d4000b050b04401500c00c014861824080c98580b044c01160800041c5080072025580c481c1c0c100c114000d68082041d00100000c0c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 847430908 1250 847429658 847429663
    0x32206021605010b0a0305071a0f070309050103050f16050d090b0a050603100203070f0507051906050a18020f0f0a0905070c020103241703071a010302030c10050307081008 75
    0xd1103608a45041c00c035100741012800d4403d020401842032145d4101000003400000c5d0101c00c4407030345182d01011000d1402118039600039980380e40000200010035a0805902c41085800c0d80d100344c804100580f14103c4030806440c0850700d048061038502c10804170309020f41c020b003092414400b000714106100d99100d1480c441e00340c03030f08040305469000340007141c5420b2010075925420804110b046103400800207250903188845e50381400400140001403280a0146141c0001c0b915001c1080d2801807400c00000e083c120707100b58400c4d00c1c005c0540b05200c02c55610900d540e400424520325540c0c003000f00000521241e907540c1d801641e41d440000c5029460103054862280c5d0348812115420a0001600740d9081031030341039400244484040242d6a454081d0065900041e5072100f0301460349041850341c03103049030107081032071265030403080c02d0b03000305a8038142c0f8400d0b070580d80d004035401c0c140180c60700002d0350780300480c03004e200040781144103051050784040c44a8825042960b203905560 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 847432158 1250 847430908 847430917
    0x309061803060e0f2406010813060207141605031005060d05060901270506070818070b0d0c02070e041103011e02092b080c0f010513030905030a0803220602 68
    0x208160016519400c0d045030500c42803075070b01580e0740f610f5454003011017801503c001c02000d031814000715001180540585203008202541d014404560303448103400c000c03000105880821001e4864541580688210701c101da20031180081c009212800408000c00e001d000700500b0a41c104d21700c500c448000c9001000014041e4140c0400090b8440303244259503031060360280700080170b00e00071500302c00150000401c00d07405040d80c0b420800680f50002001c5010403000c0340001284604d09011a440406000034103402e81c0e014410000f41790100d80591301c401e12440398a611102c82c0c000240883c0d41e803031032003526000c000c00010b41c81c2040f6044400e004d068a484496295000c03401c1606d40c10b1082040009018000d0080d039001c0c0d61101c40c040400e10490010300ea0400840d948a00f802c4c1044002c0c14013402100a106502d80210954000540980140d00285540d02d000440781000f05101c0d40c510b030418201c0d0b01e995201c3c60842080c1e01255886038035014004507400c081500c2c0e10142 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 847433408 1250 847432158 847432181
    0xa0903170f120109062301050c010b03160e060d120f09030605070503040201031d19020a050a060f1202120c0a0210060e191a040507090b0c100f0504030906180306 71
    0xc1c0d80e9504101c0784030f040703c18a4001c446411410081030741c8079000782006e400e8001c005d10b0519a250886403a1502501d6980b210039090310540c074a40c5802c1e0400c0d544541502c906a10360810707942d50700d00304403440c103004c1d202509003104d12200402c0300f8894007900d903102d4036a04084405036525a0340c00210340d81142c001d00060808800e200c2150380c1806034030b401c5841503440860083c0c3c1012030700d440e080300c0941c24400903021000702c404c54980d248050001e110003003042502a968030700c0508000983c81d440000030300c400040480811243c420355100b0641401c458a06075542a020303500756102034825000e51181a02d03c0080d5103440c05200040c203464000d88044e420103090890205903035043c00c0e460070b824806c8503114407460030130711501e0190460f0041340c0d82d2103600c011f03512019250030410003500000f5007100001ca0001f003259428150550030865281d40c0031441003103c10a03a001800101001c000b04046403054a4500801d40d440940d501d81580d00e950b16022a00d019580 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 847434658 1250 847433408 847433437
    0x7060e120c011d0114070e1809060a11030906041707080c0d030f0e120d0603200a060c0210030e0f010f060e0604060f0b07170a02150c0a0903170f 64
    0x3100c182c68038041c10f00f8401144002404002503c80001c00214401051101044030140e8100030f1642c8842058220f4243c15003042c1103801c10b0301c0d08684a94084030001034540c01c02000003500d02c001e4040317900c00d4915101401c3c03543c450b560340609441c044144100000030038840304005c18160300042034038100e500010030081104c42d401806440c0d122501c6403400c0e1a000314200c03541d0011071408043c01044c4800380c0c0c3c44082d0719004c4020080340d0006010382d50300203e074480b03800303075501d40c90b40d4460102d0352000341941ea60012551810203003402500950708440340d840c014003d400c074100c40f00b04442900d68002401c07000c1030844244811144401e074580f0740c2040003060042e6000e40010003560244046c0d810004030a0744014144144048400000707a980140304170340c00301c04454400c41c881d00d039032003080d810300035644c411015148480d00c5840021820f5a80a078044410f08901511040100340c5544c803440165440282c4007071b2030b448200940071440760007a004240c0004502103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 847435908 1250 847434658 847434671
    0x604060c021014090603040c03060504050d0810030c0b0310090c020c09010e0108030f07033e211b03030f010f0e071b03020a0605090606040b030a0807060e120c01 71
    0x100140110310266103414885500caa0110f502c184038112001c1c071005480b90b035a691034501e000700c00e60f4070075803000e03040b01d00d004148020031401041804105415585604098407640c5103044141d596100007815290138100803c400081d0002865101701512105180c56030381d80f801c50142c500381003820b0300580004100010a03c0c01c0007a003405403810800e038460640c18403506aa80c0e2082900c400c10020010a58108040c4940381c1d4511031540340d05840e0b07036000c03403154406450308031032a1110740504000080c030303c00c80009030342143e140010581c10940c6049101e008130300c1e44005044411030014285440d5110360400007140945440c0080811640c03500d1000d0405003801e800084071954600240052240d11054401850401c0d19500d10341480030310b02a07181031040b0100034196428001044003400780801d0045c81070300165010701004501c04105a00c401c0501001080c0000500652001c1100303980a410140c0c2c041003105d151400440e110f190f9074211140d030010582d120740 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 847437158 1250 847435908 847435913
    0x1c170406051e060307030215071b030c140d060515181e0106090519050301090507090b0a050a0e130b0a0f0c050901021b0102010f0e0312060a081e0c0604060c 69
    0xc000280c0540306a403542d400d04203000005d48801d440e1101070312803109081d02c08511400d241c11030b01c1c11a405074804401000d00c465111307041c0954441a9640c1150010000303070348070b140c038424490403c01003c014992040ea9104401400d000d00f42c0c1a032780b056880e0100050310303201c0d4140500c3c0107840c544803080c40c144140c2c2915940c2d9801510001d120a0010800c0c141c101058030140d5108580484118492400d100005002d0b540419415820583c1c440f01707106021440038141c400b814801e1141000e502c0c18044504107511640d604450b050104110f410414804d560b0445000d484036443d0351495140d052506a0a64a80010310350720100c80031404844d200702401c0b0006420300720704000c000c40020703484121001c86040c10011031450f01403183c0c0300f0341c4020b00b5184803034000c000000410000c55540c3c1c000c418501a0340402c04080795a030300d8501e001004880640c40101600c102002c107a070440c000041805503644500d49009a059641c4800360016000542d00d02c5e00600311070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 847438408 1250 847437158 847437181
    0x1416060e010207020604210204060b03040501050718060e0a1d091b0904020603040309030209010b13050418031209081b1903050a0f0c080708040509090c01021c17040605 74
    0x500300300350240e10401c81c10700107885074820364084440d504281c0b03005404800b000c80e0100780681c0021360103844e10002060140207800034501880c040e4000304415070b00d40501791400318544000e50402103180c40100072440c80f51554a20a40018004188681c5da808060581554207880c0002c8030300204104250395070100541881345210001d1481850442030218203200405440640a0180080002c0c01d15000790304a40003164050034060040da51380d0306240041d003080000000c42a41a031000034686842d0160002c0c074a5050301d000540d0401d90340a0703408018801e0922903441d01e502c3d02001043c181d602510421013100e004005004c51104c0207401c01e010b130590703800c0075030920540f08042540300044d101000c03461b080807510310030300d81c2007500c56205010000306450700000e00d00c01042201c0300a002102d40c02d4805080d03079140c203032401d52900d40042e034a0380181c1c001e0000c07456060522000c0a8034821f1800c081c1000c854140000e114107008071801d481a544603010b220032070003203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 847439658 1250 847438408 847438421
    0xb07020a1b0506040311040e0a080c07090e10150b040b190215040b0601140d0902040c050a0c30020a022409130b180106080a0e1903141606 61
    0x40d2a004003142d050000045031030049000c0900329052801c52540c3c151202c0d03102807110b051403000c80320306000c14903209002d54032540c401030480c020f408000503821058000d1158115521015083d50544035520030001c29000e204001411403034100051503a940c4801031015020401c206940c0e8582034540018081c55251008215802094440c404020b0051a150400e611004882d01070f00c0d0031004031500c424425078480d01080000310801c1d081c60541c041c030340c19403082d44e00780422b00700c501c030a032407030700607062803001059031240c1080024170030060194040a950040001c6000604141a800c20801c9036460250384011111419480c000d07613125105841118140000348c850070006400b40a00451580909010044c2040001043d00300d207111200242c0000c04d1040c041d09000703134101d420300c65131010581400114a2a00321400385248442d110b40007041280f140003c562628246101c040d010030940c0b14048003540040c1004154281c00d44003004040159410a001201d58 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 847440908 1250 847439658 847439693
    0x4061b0e100e012309060d0911181302011707020312010504050606071e080c10140403050301121a090f0c030d0c0305070c05100804110102010c0e0613030b07020a 71
    0x2140d03502c80d81ea0201d052560540da204003c0650604003030348401a01406031010f41c49400865441c0808507103900c48100180544200c0c2c9c44000c104040c0559817181d1004071149040440008059071941c0015800081c4180b41c5031103540c40c0e0700d0a0210380201681d490300140c00c0003c030f0300d0440c80390f01ca846000d410700303c408006a08208000070107510444400030903040010704580d11500b034601418035015009132181390307038000030002684c4a050300004407480030303d40703440140000d00d10403103d44a954542c43c0c10b86903034209030041ca10030383c000d101283d0540582c000309110180c03120300207004107028402007013a0300c0c81c03404603401e191400c2d43d854040d50100b0703000140107074081e40b005c08598150070078070356401043c240b0105554951700f000da00090041640110142d11005142c030440c01459002ca004803000012800da9014480700700002d100184184818a4603000034824003012002a00340c5613566075036006031100840300070000d40c01c505030800a11000000382808140b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 847442158 1250 847440908 847440917
    0x90501150f020f060a0e0c040501091e06030213021c0c030515030a120305130f0c0905010603141518040c050f010f050f161a010f08030c0c0904061b0e10 67
    0x5140140503036590300003d040d117440c0c50301d400c4100300340d041c01c2c401d807018a0f01c06042400b440d03840d40541c01c0940242040521030300082d454036903001040e8450f540640743d000b054001c050309081ea0304006504200094181401425480c4100d00d0161103010700c0e108641c2c40c003003407620303140b01e80e940c01c1d00e09484010f0180c0c0150600e50005441c9170b240164102103400c0000b40c0742c5510545010030014000b008000301c06c400380c00303001d00c05410103c10403503c6810341404140c1c2c88640480542d82400500e0031603505149c046078070320140c40350217418014090002040400b807218000c003400c02c10341c0d095403003444000c0180f0650810804004203c102030038542e0a0003c0258001d006202d00100e0320030f00c5202084010032500e040540c14130b40c0b5046a000030040f0f41c440c59030306200340d003880366142c0d80b6680c0f540090941000f1041d50b500c0d10480020f07240491308002401001180103104503901a074681869401d007a0317150038406011050f95501422a00346070500c000c844504c4031480901 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 847443408 1250 847442158 847442173
    0x301110702010509060a090f1e0f051c0602311202010801030b1e04140601150f05180603040305031902070c120201120204060c0606120506130507090501150f02 70
    0x41c3d07004030440743c60880580300540da40d5103c100c1198007001941005100c4210401d000130144140444803081d01e00c000108a00d45940314840300303e60b0304520445e50020703050100200001c01c01c80d5540c89040c01003034003529014020b028500040d4841e0229603441407001d1034441803945245030300020f49410b81c20141054000d0700040d00403c4140320040c084403c940c000ba01201c41c1082034803840007042d41d17941450034246880c0d1107654908025211b14401c0e107000198580b13a20750b07804207000054072140b0080100000880d0640c0c0051400d065403442e1000c080c101e03899803401140700d5030081e583c054407400d116694814080051000303420050061115401040460f400700c01140d04580700b443c20003217680300503102034070088807007480e05101040010300a40c000240040ca00d2203043d04101440e10b500700714801d0a050310300503060703030310843c0040e10182243c030014003001e0040c1c04035a51642d94030b003001c0640310260040c4603031100721421801659000344601800d2a0f40e4000740901 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 847444658 1250 847443408 847443413
    0xc0d11030325021c03053909120f0604030f0801050a0e07030f050a0c0239030f070602073002040b0f030f0d08070f090603020708220503011107 63
    0x12416600c1000b501002c2403050039000c0d4001c00012500d20f200704520701c2d01210420340070f00148021120001481420300b8070003281407000c0030f5503a458201001006070816607140001c40ca130068200c1c1d90708282d031381e1210440c0390403c000202101900d400100900d2600d440d00030840381803680454180300144005202d41c2c0d5400300100140c0c0c03c6c0c018480201d07600da001c11000b48c01914141140149842c003440100700c0c0b1a000548400e01a4081b9055201d84840100410700e52042024a40310000b2004c00ca001c9541860303092040d0090840b8080100400c00314200030043d031110000d87d015000801c04401c001034001c5020240700c0c45000605c140d040460012442018024413076940d4400303101440d07403030404841a004000e4111142944020048e6507600d0080c9808000314040b1400030310250f21808424112485541c3c0d26804079140810580c003a400c0000121488901440300d07007040143115003000c0140c02500a4010785500d010140341c2101e001403d400900c000070410f4101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 847445908 1250 847444658 847444681
    0x70e01020615090c070b040c03030905010c030e0f121212010909020102300a0203041a07211e020a02040b01030b0d0308100e070f0924030509120c0d110303 68
    0x42c03609042e214000140d03a80c03840c80350b903449040c0008190409010078081030190346807000d019244070351039a0021a07100c40054844032a40140100010354609541c0700e1804c0c260140158402c1c054001120300b40840e00c0780d810300700c510400b00f02240020400c01c3c6000118070440c2e00420300b030441003002d03000d01e400003500c5595502a0382000c02c6403a02c0c0640240ca041045e0174040f04028016440f0060440000e4803039106215904c90740440c2c24910464500203c202c41145500800705004508811401147d400d01d071392000003485060b0300b210080801c03818007074203640519405040011440e01c10401203807840e2034058101403800c907034014981c8030700c02c2e2600c1d90307500340c1040141380d55000400f094540c800c0d0000d4032100c0400c4140b000c0260400620445080c0688940c02e5203034540b403000c5040350400c820810800000b29426000e28000d07808560010b5551084d110300081c00c03152000b103503200103a440c2c0f0a600c081c47c800c0000e68042d0b90b4520701034202000d0341c554146115400b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 847447158 1250 847445908 847445941
    0x1e0e0609011505090c22062c032808160201080906070503060103020d06150203120a020f090904020609030111030106020f01020301140609120601180b010509012106030f050303070e010206 82
    0x608200140c140c8190400f04407514502ca425000000000e4450b003004142d0481c0e00708c480781d14204840d100044a50324004100b030882d01a0040054030580100e060740c14082481105100701c61400142c0480c403181c0042510080e0729285109101140c0700041801000912100198110006020900b1b42c030100b00ca030000c000f4130300035071a00e99030004400246196402100703a81103500308004520f4012000d020b82c0314400290b0007240e80c03070354080e20980c414000c283d120440c1c04c0009000514169428035009800502103d05048081c0003003400c440140e0282c5d001401c0110040020716030403c103e00d02945480003d60443d450604201c141103040030209200c0c83d001700b2185269100e45d10f41c00d001c0c003888011101d80b5617465001360700c9000300f100032000c9039040c44402e4141d03501910480d44201010303510030f0744561110703030814249001c58003880c807500d4540c1c00c0040420085441507910500a40c0959543e040111020b826802e9400f06a0b066420900410840e10b441c40f5906 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 847448408 1250 847447158 847447171
    0x118030614010b21100f180506030a0f0b040f0203060415050606070c0b0f0c03040b0d23270d11010b0a06120e0337051303061e0e060901150509 63
    0x81813903240d81181e01701d400c03c56003100f01c40b020032180000300702c60300559583e000b19100301c0030010350322030100781619420162400b5103091303801c500820000e290551019401401580c212042500f1680000d0800301e003560190b0302c0e10300d202c15800720000c09101d155044a02101d1040c80e01a2503528031030640300d20b10800141e044d021030407031504a400021110340c0011403068940e0b441d2181e40003102500702c0903402d0007451030540000740c07001002d01120300000395580249059500c0720030343c2d508040100b0307185403010320300d500d6188002810000d20303003468030544504840908070845d5500f181d500c1959188174501010701080f46980117007003c0d03030383c040740c85001c202801d5180541d0301d50b1181d1140206400039005c000603000400c1d030105004403841e0314500020680800007144e850040380e1014940c07510300e540030000110103034030030113038098003d0551082c1101c0155200c04c540d92840c281c03803030b0340001c402c00540507420301c0703072a03442c0c0c81481043e602c640c200700c0400c0c3d80000c02041e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 847449658 1250 847448408 847448467
    0x1082406030402120303090a051c05040e07110f100506041a19050901120b091203070f020a15021b0a0f060c0e13020406090f08030a05090118030614010b 67
    0x1c030b015034450f60b080e01070b80c2c0f000c14100c030395034104003902e0756440305486003c8e12030b0300904c00565101c410a108038881e00300c1c20764441d0b043c5800d1001c14044000054010b1040c0403441c1802d031004041800172402c5071445a020b8038400101c041141c094400040030217224515001c4892980d200d900780034600b84e1019a04c01d8a0307803412008a00c01c0205541040307a10a074000000102968181d49451b0154450340304130445895203003840c2e80d5540108400d00344003000340001840c00d031280a10003100822881200e08a50302c036210252740e081400040908030707800041007514005d00312500c3c03d40159903c010300701c0040d0343d21410000030110200402c2c50751240140092148240320f2001c81e00c0e4010406800440c0b03440c00c0c0030007580709c1e101d2080032525005001843e2000c024224040700c102d50040c0d442e0140b80503088403a0351100d02000e060007485501804a10b0300e81d440840503500c50480003544031070701255020b815005030300c02c0e40911020881c00300600d0050743c05030780c0d000e290f500e03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 847450908 1250 847449658 847449661
    0x60210140c091201140103140115050f18190e031801031104090f05040b070e06070209040501060f08030d0b0d0218040c091a040e0604032c0612060108240603 69
    0x80c20f1003070b5114556905608240040032000e014084203412240f1503405c100241072203540d060700f40c4501c203101804841002800304601c1c2000000362200560040410b1800040300b4030031640c1800c00c1d174645401d503800c055a81c040c4906031041031503da103150001c6051516810104920b0250200d81758101610f82c00b034150240803880070781c1c1c00392401100c240403029441d21104000c10049800b40c0c0d5940075100843d06880c0909280c00c0c00400203000c0500d01104d039001d20105030300142041f55150342c0c0d040005410800b03001038001612000c4041c55480c400091880e0698101c514854800c05035000c02c1c03001641c0d02003102001030409051542c10f070f6541e0425184410281d03005212550402e1038072110324604820800b80e0101c100d504109503401c002c0142d585610440b401808115100102c0c60712518014543c0441403007046001841d0303500c040400c003190801c120507500c00021070306000c100d60300500d82c40c1c1e001c49a010510a103a5100e10200002c0080340c0c24035025903400070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 847452158 1250 847450908 847450927
    0x804082b05010b0d0501050f13110403050703050708240703091a1806010909030c032a0309030b060f010e332701090311031006090204060210140c 64
    0x10320003014001004030030002907940e51030381c08081e408200c0390742c4a00e150400210301ca1421481124282101400d0f04c5d82981c4030450401c0204109404071020400c02e0000000141082000002840c4100081d001c041d1402c10006d1030a240724281081c40101030541c801d0440820030100d620205c0e40c0340124041c07565007401030741104125010340c2590282c2d0704015886118120113540c40018104962080c1c1c1d941c403009040320f84004006000550084c3d0b8600440c0c0728402c001c40405003144900e91400020240340e141d20a869001c40201e6180501003040c802e40c901410381c00481034407802c13400b01d69880001c004800740000c00380314145044a41840703c40705403803000d518650b00c400c0008403c0301c80704191145c2007a001c4c82142d03040c401043d00c0ee201121441c0b0105401a110b500030f40e0b081d81d90302003a2458801e15560144190095031030710303041c2c501540c0b0040c10b8038040140e969041c0300c0c00900f0580208880760b140f508002c03903a4000e0b441003200236070040c0101e0043d0340f200000c0c1e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 847453408 1250 847452158 847452217
    0x11202071e02041d010c0f1103092407050a03030c081608180610241d150310060f0f050f0c07080f06191b0f020f0307060b030c01080408 60
    0x245040c100041e2413540d80c0e00308000562041407a03690b151205240d20404c400101d444406002c800c0b031194200303000c2c028040c104000d10b403035980c05140042a0240c6100314074034698000542c00d403455030044e00070505250300352040c000d0106041ca03010788540b030401c0000d1050300c418800714041150110000b42003900760f8819030081c40c0102c05450f0581848003d0b01c104d04910300070000c4030207240e00c004a0385010801c040c030120519132126514404c0407002c1d074101d44174000e60313a07400070504802203488050a100461080d064043c00703100c500e084c9038005101c040c280c5c00c0001070001d5081c0c0701c10350680010541341074094080c2aa65200035104045007081d52030b034070410041c03140400d011495400803d04034440c0c80401090801030514072480f42c2504d0b1604c04141682e50406c40901525200e201040c07080350150040300e00d1202d140c0ca4241c559070101a003510701d82c0d07a401c0c82080601d0706002c0821000002d01e0041d0450520340c4035044a403159155031050790030700303191100005806 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 847454658 1250 847453408 847453421
    0x90712020c0a0c050307091b0507030507150f0c210e0a0b04150e010b0609040c170a0911040b0927010507030501081905030306010c080f07030509011202071e0204 71
    0x8103816210b128a031071408070301c40c1c01280650b070320030b0040306c0010030341d03000c1c0c2d104422404854041102c65102e4000099550f42e03c6084198100300041050f103002c180c0c82002061590303000c940000321003504010b0081102d000c1c0280b9000c1150b020b1248145030111603559031188407494000500e884990301081c50480d003054020400c021940802050048544000111405615007404400c0701d02800f54200c0f00c1d201a501d601150911099101e0f007003d50020480448a0034042d080014003000c60520010483d05610070130340740d500a9040180402e81c03002810000e0b5401d10000305008005020300b100108043e00009401d60f82038040594034048051007440000200403900b405103000700070740000d000e228080d01c03070300e2141c00c002c1801460b40c0b5042500b25024500f1504c809004580741940303038505440c0f0385000d000500c81100800010184c0b14800d49a40703640e150303864001f401003c051201e81140303c0c8180f280501041ca41862425003440d82d042d82040300fa62413002070003c001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 847455908 1250 847454658 847454677
    0x115021c032f0714070510051b10020c0c06030c07140321040209090a0507150c05120a03060e13111f08060a050613090b060c1005040201030b0d0209071202 68
    0x800d000c80c210222003080c01000424013607000b084040f2400f80c0c0540d69071019104181d00801c01c1115444c09920503c0a0b0600c5103017100c116408641d00d240e903514045000e07200c00e044581c009003200e46000f0410941c0043c2806469090442c94240041c055034007480c1c0c0c0103451541c005598107044803050044485028945120303903101c4e2035032405580300800858049024013031038400705540ca8800140040c040f580308009001355401c120008065121401c1d10b001440030301c0c01900c00041051141e0007407544c001c0e00c07007500c2e840380760001070035140c1720762000c0100d038000010700901e0100d080d0072900441d0040c070103940c19240d00c030105c0c000c05118001310b400d1900301142c034408241c0c44030300030f0300a80b821501c0c070403070070345400400149101e5042c80310f150410302c020402c43e1002d140c01000c0b1403a0300501d0681803006103c111800d1180c503194810b5500da4a0381000210340c1c043c03160610115056030343c1840802103a0100d40b0419010304207405018a0101c3c00300402c010b90111030540a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 847457158 1250 847455908 847455971
    0x60203030a11191106010b122413090614040224090406180e03130512030c03071518080f091207080106030b0f040c120c09140115021c03 60
    0xf40103a4000c216002c40c0100304050b00901000113103444098041d80e40d0504070021701c82180d1a45c1200300240740c000341c4421440361500c10070501554410440411803000010041420f075a03910f040030403a01080000289a1007001c2440050303250121034075040c0300c1c0c0c0c03081c811020030700c44810803a502404003110b912604009000c035003a1070303503201451034000d0b070768041c000178030702605107a12402020b0f4001c448400b540402c100c0f510f05003040709584000102540c1c503003a440401c2a0640e840307084143d07200c035220511003903640c119104404200340d14060146000342c075555000d80030320a404d05a00c07a100080303000c1120b907030740c80c805205c034044880031180516074440c1b0041c0070b4107040c4401c2d1050200000000c5150b20407641c0b41d072107160300080c090641420040c0c01e549110b240a800c0d1005010a40049214400c5101c0d810f52901180055100c96250032981c9480072400c03d110800c541011741e10401d03034201c0070101d0115030401e04010030003941001641c0780c0c41c21110000050742 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 847458408 1250 847457158 847457197
    0x9020f0405300c0102011b020d0807030e011a03010516081302130e0d0912052e060312030b01090513180f0302070f080a230a06060306020403020a121a1504050405060a060f060203030a11 81
    0x63f110081608034820190000e00c03c1e03070b44500104110841c00b03008100801d03540380010717580030400d401c0410114401012000c490015000b01002c0340ca841080750b00700c0e0303c0440080001c9800c0420320004040340b18400300000420ba40f02c0d034a5915030f40b1220303051101c0e40c052003900d042e1491035552610140c80704110003a07407810500c0400010003032800210785400000c01055119200c1c8400783e40000c2c00c0940441344001b00140100000b50f810404220070342441c000003100c0f4101060011300a6008003034581c03c084602d2400841c80c0d0040c422070380481d00c40c02c0010042c0c0b00605585554251801040905071b142c1070900403035010080140c0c0c900740b4003000304807c1c4e6002e001541c1c000e4a000f50407a0711410317009a00341102d20301624029010305809401c0c030412041e00d5110448800d10807c9851013800328003940c3c0d003503d0460f0389411030350400086280f90311030080181040c0000300d000c180f4041000c0c0d05e0748070145c061524241c40c2d04c80305500822000880e0041120700811a024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 847459658 1250 847458408 847458431
    0xa1106070305010f06030b010e10090e0c030906060427080904060803120a0b1806010905100c0228060c0804031b090609020f0405300c0102011b020d0807030e01 70
    0x28082401a08031349140d611000c00c0e098442c3c40341c02c16458040c4c558008070300d0200d0400800480c81c030b00d0f1800704690440301082c0d00c552140c2c400c0c06141c0300c080b002d03141d003031106546061200081c030a5005515002080d14200d4a10000d5400f52303a4581c0a12450995404e1141c1c030313441269090b41c3c116090030700006180a0002c01040c0c042c0b03896070882055180ca140032000e580c06400b00715071100380c0400006509450301c010039040b0700b0504181707008a0b62003011403440d00a906c805e00116640706403a00a60500303080501300c00c03820303c03695500c01458a0040c40b803104070703014040420140c1d0008000b00243e000445014541012003001c94801486220f00500482d014461042c3e040c100006925216402501c070209280b031040c505150602d0144481e13142c040a2410804030390501e8801180701c2d1118a42480800c840507011b0301255900180c00e460305801c0312141941d1b1560340000c9a50301086c64141c24440386800f8805403101328080f405041441148444d0354601580e80c0007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 847460908 1250 847459658 847459661
    0x2120f030d1409031905091801091d0d0c02040b040218121605040c03240911030411100203070b091e19031b0c0f0911030c09060a11060703 61
    0x109118015060012140041840001d20400d603098001603100380501c4580000480009940170343c1460150300300300b10903000403050705821240c900c64001c020010b01c0060b15502410170080100e170309000c6545080c901142c2d0b5400c16401110070032020510f03038011940d5507006010b115000030b00c1503460341c0a030212003900804015090b4468607801403001101c0740d010600e642c040011100c1000304502d4001800003401d81c0714554410169140c1c910f062010100200d05000c890f850035000c200790030800c84804542c084070586c0d03c800401e00400000078442980c0544030030040d94501881a4030310b40582ca07500895100401c010360b008100f19071014001003603010074018042e1140c2c55140f204002e611001000310301c42000b03483d98500404a4000e40c07403007a4000e81004402c200000986410f620a01c0c80e07007000600c4514984100880c64490007202180700120300700c4c0e4a5401c00d0441420303588145e5000900852000c41d4196406014441545600d00d40710141c610310b1030003110040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 847462158 1250 847460908 847460917
    0x230c06030103060e07051e150903010c080a0608190204020f190e180f07140c0706030902030c040b031506060912030304150605030304170715020304061d0a050d02120f03 74
    0x42517482070200008a5141002e42a01240d04d114804241d405156061001c144503a241d0070701460380412039808a510244076030241d81c0b130780ea507840c09241000000304043c0c80191780a2039403640f008440c102c0f1007185510004145904550041c0e54004080d80c0502034001d0303800758080b120480c00c81c240c00d135030003601070900604101c858461820a00814800141040e1100700642a50400040030580580f034081b9001d5120204d440c108040000c2c1a03160045075000381001030348445400c804c6003810010380f540e19508580a008100125001c00d42c0c0d8240d000032000507980140203d181038503003800311801c00030007801d0490a01c4a0804e0789a0342d0380700b81c1c0d00311002c6a4a04500801d01c8e80c512804e03041c2d64000300990700c0c013464030004220800c10710403650b01701d0044c01c00004402c004d140010580c41942d070081c585a0380303414006440b8402c9100401c0d01c00c0c51811a11005603a1408002d065034411911070f00c11018600201e010341940d4840031415100d80e02c1c066241190000140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 847463408 1250 847462158 847462181
    0x319110a0e01142b2f0406081b0d0504080406182303030424090e070f0f3e0f0a0602091f0804030f050304230c0603010306 54
    0x80c61084107900111034003018000b241001075401e1003036500002c10f000744031003030f04a5481244104080880c07000c04980c01c446004000c000c1c0034025407860407101813a11400c00b14031a140381410f18007040900100b038000c2403580d102c400203440a03d070016140a5404140c92400200950300d0301e0f19140801d43d01500562011598a452a00c1c106034555848826200d681107140e6903603140096509029802c004a03e034140024040420010900d1075031072000841203000c031140180c03140c000b8103001c110f50011302034590768104009402d501300016480808861170101c80210400c5400c0360b14603044440807903075010b04018004d84024118524140b0303810303545004500c1c5180134107150780b42001006910030760400c54040000c905d0329801b80200c030300082c040642c0e50710728217403400840300d000c0e1910000c1505502800107050307200c2c40082d5540024108180b07076040c19100c004c00107800384525074100c03030fa040307942c0500c5006006200b100703900a00300c6516541c41e45085006004e2203600d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 847464658 1250 847463408 847463417
    0x12130b070918090c060f0e15030a0518120d0f0c0305071e1409030f0604080c0607140313080c03040b07120302030712150b0c060406060e070f050319110a 67
    0x7001036082c0d03503c03400c198298810307080e5010078500741043c0c419403200c144443c14002510040901c0d81c698628002143d000422000d540b0300d0311185080444c1d9024002c03d944001183c11403414182c00500e0030004901440444e480c1c0701c50849000c050040d0102003100c2c1070809041e904101e4054000a005640d02e89030803c0103803000000d40e200d00b07114003400d80080c0c50f00196240b0740115400401030448082e003501e1f012003055044900d80007098404071409c460008144081400c18009507821001a140c8002400300210110046000c060090310202f0f9409e13560000300201002103d03030032040d48040e00e40316a51007401c050503400c504003d0307030940d43ca00d183d142c1c03091080c0b08076803045a49031540ca004e40701c040c150350000c20b44584000c100a5480d0004904420008003806012100d4801080686440c0c5010000da514681c061401240207000f80240e03d9008403968013400517924022f0384039915500005c0c08888913803032000c2c2c41303480d03c058100d02820980090805110944a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 847465908 1250 847464658 847464689
    0xc092d04020a0f0c0212061f050f09040b190507050405120622060b1536010507031704080a1106010f03030503090115090203190e0312130b0709 63
    0x140000d030b105600c03a020016148850480c1581e0060444031682c0f4009000c50521000e041e06040c0703080b600303603940703d2208000480d83c0c50807080240000d01900d801e448250040c8514030100c1d507005400303072004000c0d043e42c5002441203410044403003542020b64209001c18200408060b00700d6220303010b05030044101c80f00c0020310080001e5814090556030141d07181d00c0909821903a8403640199044802c1c41d140d818000701b940d21038803074141401d00414810b03501d40300d04a0061a2060500058410100862801810108084000e40c0c1c414007070824981d070301d22034902200e41d10072443c000b040d10030810086c04140b141c2207010b08130b031540540f15014101c0102c0041681c881092146100b040800001803002078455070185810855050001c10601c1c4020007507619808140c100031032903603020082004003104200303010079818808a042180d40321785a07496407a486806031941d0740d00f01c000040340c0103d664130302c0700c0d400c035411a910001a04080380d008007124040d00ca903411401c00d288 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 847467158 1250 847465908 847465999
    0xf01060302030c0609010212280314070e15030f07030b030609071203053001050d11041a0303070f020108010f0b071b081509010f230c09 60
    0x116250540c0d400500500c1c04034401010041c0c81c2d800f6400c04d80c11030144045401740400b52070054031210409183c100d07064240e140c50324105c80d021441e040c1c10103061004e80d00541001c0c540c850740111451502d03031004820f41c1c011800040300c1c840c3e4000e4000c1d00000300040c02d20340011490080810ba0b03401d200d00d0f8112400c040d646c00040e206144183c011020802a200700d041c0c80100c0e041c400d091490820030912000c4060014000100203642c02c2d190405078a403255804a9015090480344d415403a00c1503294503000000071160503000340e90f038060a060354414400e40d9155050003e00700c9507030b664507103002010181d8010701240440c5040b800814242007100c0c01d0402e690304681e4541c01e2010b251a0790031204d04443c000081c1800d014000306034100c0600074040b01c0c1e01404540b02c8103051030031209084803c00011540c1d1140b416500c244c1d0040130040340607810b18500d03442105521483d17003c4220b441504015540506038040303000c2d402941301100e0b16409041580c0060040301031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 847468408 1250 847467158 847467161
    0x61518080307030906030f0f0501060206041a01080309040b0a0302030303070c210f030f0914010e070b0306010c080a0210091a070e0906220504030924080c0a03150303050c0f01 77
    0x1242c0100864500d01091010070b201c0c0c0c1c8401680c50103d0310114428a4200e106001c80d00b082e084900181c116104120500400402e803ca0752400181c0c081519071412400035200e002d021081b0380301e1622401d40003416501d807410480655001800e0300d5880c103121201030403101c0c01410403184003014402100400c103401000c255080d00300d0300c9510b0082e001083c1180204001b0442c804142d640b45c042001140d40c00d44000748003243c3d4000000c0311510415407503d8110940d2043c0b5101c1030400070001c0301d0341e000802480c80c1351702c064195100d06600c0c0781a8103040750300c00d5401007103252a4100c001e110641c14444001031071102c0060b034a84030100d040300d0368800e0260f150b402500d0704021a03168205403420504001d08007000c200003609240203c004d807081902e05500080c2d600f841445103040d507d195090004000b1107d401345000c01c000a00721100c02001d4031f8205001040001c000745c06034104002c07136a400041d04201075100d01c1c000d000c1703821008a101c444c0c42190801500c02005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 847469658 1250 847468408 847468417
    0x50106091205030703200a24060302030729030903090108130f0210030905030708090114040e010317041e0305010b0a080303060616150e15160809010615180803 70
    0x4400950304d0240d0b80d840690b202469081c01e14024413600d80912400d540611400080c03902c6803070b205001054490402000440c01b040070b10a03c1e24100040006070790000b6000c00316840072a4288802e00f0080b16105912102001144001000020400c05010210013004c184030240ca400400d44c0361700304650381c044030b9510001c0c468070701480c0060251800350181844110207241c003140111072a6140713403c5800071b070310171950890003040d90040c0750307044150000401a20b54042d400c152500e0700d403040064061001901400079400c0c950361089011023150040e152800300900b031006041e400704060a035522040da019403070009070360700c2890008002011111080300460440d11640100301240d030041910301e070841d03845403103800054034214400810101d0200000b58100c2e040c15020b08001510003620b0050f00f002d0104510080901c9009141c0d120515010010f6aa81c800301801051a0740000641401003604010183c0d03110380160000c21403800340081c1190765200c415664003c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 847470908 1250 847469658 847469663
    0x30c03120f1b05161205011407120b030114010b0d050a0203091b0402090a1203081f060305040312051005010e0f0a051005040f120b0609060a1403030c060106030501060912 75
    0x21101c60705241c1241100c00311101d00d000e82e064413a0740c5600791220000c3c020541c0100050015001007806201081c80707114046100810010f07141d2600420060812815907840118140d0f901e010b480551400d5020000310248103108000e19616991440301d01d03089444600740580c10003000506504540c004d690091000030001c0c940440c8890401080c1c4442d142da1541213542448481c0d10369a450f50510010440100d0005120501e400d000f04030a030010100100f032001d022062034582c1b10340c080300048a0280c82c000613503441d6403404507548405040c6161a603410705081c05801035940d0614002c4a4090b02d60380c2850881000f880040100c854069034400c0c080041004942400e0190300c0010740a072800c1c1e03150a440b0041c2c2100c248c0640c02410126030254114030070050389000183d04904110346194461404038002040071142e809140c40d000b030030100b00d9000e5201041520a0801600240d4000750307100c680040040c00c00b441a03c0010b0005000000e030041311650b2010b100740c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 847472158 1250 847470908 847470917
    0x20301051003030f0c0813091b05090904110d05010908040f0e090a060b011101020c03070b0703021201090e19051c11030f0313050a0302161d0604050a0213030c03120f 73
    0x4c51004142c400342c1c1c10102c1a0b074215400c2009900218440340080b0241815010000b040200e2008203081644458026011b12400b0403400c002ca68488440507400b503400046400b0300748410003c070740c0c1d5001c860350050066003081e44c1c800c10040050302a03c1510002d441142540d981c0380c500c2e01c2c0c3c6840c255400c944582000c150000840d0307076500200c1c00c4010604002241c0e14091441d00e089a0100c40e940c902d0b50400b041c4042040001c1c0640c9800c80d40e145802c0d4205400d0444910980c3c00c18071030804081d0b076810078110010703028040c04c507070782c005802d100700516018285140c4072011105111400e0180e010090611030181c04000428103141d8011810000c1c81d900c44c0406500140c003c059400c90b41f0403c6000410412460b440c0c10300c281e010300448408040ca102200c034041d0488500b44200c00d03054500012050445030b80400c04644c085400d07100d40303007058024820040a103008500c610004402d002040b450142201d03c504540751200200d60021609060000409030000c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 847473408 1250 847472158 847472177
    0x3020f0a06200114010303080106090b0315090901061805160203031e040302120c010c0f09080c011b0f030807020c03011a10180807050301060f0303050a110c040c030902030105100303 80
    0x280c0080400b800e260380b0800001407003510500e0044819809038421000101c581c00107000c461391001031031001b803e108004908500f040c00c034800503885404911801a16000d001402c0c040c005d4200000a120724a071802e041c411030213150000d0701c03040300c10f40030780301981243c41d40191001085a1090085041a00c030100912003000403045c0060000d80c110321403042c0c0d080308101050010710a00000c3c400019503003001e00c2e0083c108903100340c1c5041c148414000708001c0d903040800d0340a403140c030900c0d1088074804030a42405404c04040c9014181d51609000e80d800c15800960ba20b001c1d50003071302120f500148050405090343c02c0e5441c02c5070910860311404503a0309081500048007003084c2405260340c0380d05900440c401040c0e074004803040c0e03c000e008100c02c0c1800e1265101400660034150075840c256200641b161141d03a80c0034007041440d40340c0e1520703030030203001100c0d110100a109000300c044400c0000c000c1d03c01d240007a0b10075407820380802c60590060105104032903040d160155079 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 847474658 1250 847473408 847473437
    0x803101a1809040309051e06031302040b030c090a1515390b06010c0516050f0301021e0c03070b070c0c080606090103030f03020d11041706010b0304060207171303020f0a06 75
    0x101c1d00c81f24603058045040500107199551501d0155201c0d4154126515a00c0024010001031380c1641d0703a038034002d801c0815504e0960321585000c40d80918516800715070380c9005500740030755031a00d0f444803840c4003140c41141251a400070f4107880741d855000c1d0035140315035601017080070f0111300080d0090021410b0f0b0150001001500c95503801081410b10210b1006140c803143c0c2003081c0031040ca05c1c0089480014059803600314040120404251f0013142002e464840001884803014448424624041400003040380c04000700d030109a48985500d41e6400c0601d0058104099444111903a039130415000c2030300200083da0510034040201041c05c3c4c1c4c0d280d0341301076035448410542c0b40c0405400700800c4801408034001d030681000c40400d002e07681c914091081800d0015602c03000c8007500450010812440070800392600103403c0640103980b046180740c041c07405600041c0300301d44c41001081e441e4500107240780b40300071070f0300948200880410501c00c1040400c8203024820106010003a414513 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 847475908 1250 847474658 847474669
    0x705130c020d082a12090604060e01023115080105040b0d080712110313031109041a07090323010c050c0a03030509010f060e1e01050604030803101a180904030905 71
    0x6000e0368980d9440d040c07801c000b0a155174000c461407034060380316209200400c40107216021301b05030103000071170806807010403c1407040c01e1462801500d60070603a6065030590399000343c4000784544104407801d5070354244003401100003440340d04c2c8640c1c43d00006941d541010b03004015403580c0300f00340515040295031250f207d40308072813141040050041c0c2c40d440c00c0070104000c00c45854068140280b261a601d400c01c126944403e03142c1c010010130003440300150b50501d1540300c3c41c034084078040c901d40e107104044074841d00740c2e840a49000d2803410b00d190703070114414030010741744414002840455003000c8151036034070861000600c20b42c0b01c540e0304d4005c03d10039840305800c80d06420001c55981078038a0704030196403240d004101c00382241028004003805040750807040600c40c0c05400c1c60342d803601c070008401d40242d11010b00490b40c0000000c882500c03110540007d00181d40074140f4214150729282d00c0d0fa04955049080c0c110f5480144000b440d003d84c00354800c507415034826581d50b082c50107011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 847477158 1250 847475908 847475971
    0x10816030c090b0a091a040e0103080d090b010608070807030c02190503040308030106092405040b070809150301090c081306020903100501060e090c09100f020705130c020d08 76
    0x2042202c080408a03601280d82d00a00c264111685d641030b550341402c3c58607440180000c1d031403d0000040200704000d102c80c1b0348080c11640c2011075552078010008600020700502c04004094480500c004114250048000c80c003600003552103200c2d50781daa600a03030403501c1020605000d40c2c0101c1c0000720103a003004040602901c00c0342901e082603aa42d5a50155070020380000b40030803c0c8103400e110500c2100c22130712504201981c0c2403035807444484007a16070310550003102c1c0c070600f00080c12824041101c003182c9404002810710541075003030901405080c1c000380600c030704d901d0601d03154051080c0700e000424007441440d040b40c001c0f0161035480e94025030208403100c1d014000e2800c0e0707011490151095034001c0001380c6448403454625401c004080c440244400710840c3d0070712410120f0b13285c00640901010f0a41813a0010107421042649030038501d40c000c90307000040d140030103141141600510540c04090302100c0a05c811a0701c140c54001c3c2c21288400e80101003c04400150750190300340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 847478408 1250 847477158 847477181
    0x15010803070308010527010801020901081e0109050402010e1f02010b0f030c1908150a0609020f1c1d0a02130b0d03032301061706040209010c020f03120c0d03060501081603 75
    0x3005e141c8083c034650720510707401d911505181cad501040040055030400c2802e544160481032140040d000c0c03860151041c4418014040090742e00c4001800f16401010341c900458402441ca203101250344004045c109104a06480154205021301d0150304141c9011019100010081c00d14003c040c028000d50a40303048900c0c151360700321140012240e40c180641e5210103c0d0013000100c614281a030714003510380715407282c211107104001c50030b12550300383c007a5100d04070b010f03040c00c0380440d421a83c00094100d100910042c07031442c50420071802c00004d00b04002ca0300c266a42c0030705196071a0143c08503003194a00c2c540203071141e025400024403a92001b2a141e110119040d1109070000c0401d880040903004000401c0180e2a90b20401313056040441d03001500325019403034444150002410000c240304002c0c02016104d2584015070f90900034690000c10222000d52100660115241c0d070720428500b1401081c9400c0c0701081c1c9500c120b804030711411440c46034801d44100100c04600400d160320b4034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 847479658 1250 847478408 847478449
    0x40e04150207052503082a010c120b0301060602070302060c0a061d300904060801090308180a0b070c0f020d0c0f0f05030a03180f08150108030703080105 67
    0x40d000d501000c0c8003510b0349602a000800d40d00c00000c002c10140c0c00483c130000040d40c505842003002461803070868050319104a4a0083e020680382e8481c900c9003c80ba450f103055023480e144199055205210031400a41c4110034480c041050007031508941c2907025810050300608820304c05410030f100200314400c107490881c0d014a145850f02c9045520b00c0c902c00181c0324642640e1003d00008110074501c4a2042210240701c00400d00300800218800c0d65444080502007000c20150361964040401071404000a003c0c013195480e0007081d01c2030882d44a584030341d0b142c425800d04800001c0c00c0c5503291b4408150740160700d800070305403854004100c04640b82c1c09605140e034010f885003180c5106c424441c4503048082c82c1401c2503228945242e401000700c60f000c0442c00c00c6990340000d001d061403034041c00c04003a043c5003d0708107066418150440805805c0141001600450000d403059000d090600c04155690b26850040e40b2441f5100c1c0103800254030310018481841d00303055500210707149002c0e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 847480908 1250 847479658 847479683
    0xb07061104031a04060507031407080702070b0f070203010c020601230f06180307060201110409020c030c061821090f120d0306090e030c1507200f15010b040e04 70
    0x102c030024200c04000070300103503040308280400c010046c001c0c103800c42c8544c00c0c188003030104040010319804000300b50204009503403010840e41d070700a02400b8013804880440701d5035800d801401c600d003540400c034200d00030b40c40c11650428180c4040340c41ca05031101c00a245495054081840040c090400c00d803513800304003101444020759801d0300410644280d0fa04904524600b6010942440c201e603004500b964104081415501004000c44083c3c901c0e0402c016150022203503400d10b54021003942035518401d89090040c0030101902c000c1c0e00704420801c903010b80ba0912072240ba0351082900091094000780010421483c0c04850401c81c442c2c064070420707541c1c540002c40c40c0350400022a8502081d95040d09105406843c0074264000e0031841c000d500d04290740700c8144d034520351007010646111600d0003090380240720350700e48a84000190200c10030360b20060410340d210704148074042418402c40030021028110f86a0440c101c5240304803044c20240f40c16405075003144010b00483d0424401031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 847482014 1106 847480908 847480913
    0x1b1306051b01090302060406050c091e040f060f03110603270708030703050c06090c010e0409021309050703031d3706030e070f0b0706110403 62
    0x40c00960341c10703141c00c42821452905480c1c2076107509003404002855400106140114004e5074100090b8440e600c150026110f0180f06075040052a003800b45801143c0142d140c116034043c00114800c2440c48800040360f465030410301000235421014810710501c04003200740c41c40113450301d0303145042011001554686a40d40180c0381c80800d0402900e0b0302003031103040d00811030141100d450700d80380d20b03016155420101503415140302c3e407000102c03141c00014481d500d041c01038540c00344610442c418400078060002081e0780102c044c003e02e11406405104802c105401346004d03101307130350444c1b40c001c0c008210000088000b00c03481c40d0006031552100c1d5940c218419610045081800d0455001c181c1100000803010790f010310000000c1072a0181c00070340c80300381040c09664800d0346500343c43c145424117005448500c00184031050003d040d0b68041040b2400aa541e00d082a80c0c07036 = true := by decide +kernel

theorem cover : BRFrame.Cov 847302158 847482014 := by
  have h0 := BRFrame.cov_init 847302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 847302158 ≤ n) (h2 : n < 847482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
