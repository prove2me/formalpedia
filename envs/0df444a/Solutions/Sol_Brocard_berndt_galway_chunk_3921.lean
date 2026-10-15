-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3921
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:03:53.284228+00:00
-- url     : https://prove2.me/submissions/0edef435-bb62-4261-aea4-dd4ebd9cf535

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 705035971 ≤ n < 705215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 705037221 1250 705035971 705035977
    0x809150114191a0f1303030906080903070b060f03190521040608150d02060a0903110a21020117010609031209031a060402041206020405210d14041a 65
    0x10490b40551001c2001c204403407501854440e030000184204180c1a618040c030300246424401c1524071460030241103407000c806403455200303c0000d801080d00700720003503006a000e030304508900080c41c40e00032152280100240302812082c821815200d40e0691658100240c0040d0001105900309110542c14080d032a2648440c0c8170100307070081c40c0c0304055185440110b80a1740c0301611781041c1500e80709258026444070541868004004030100400340e41e8050142540400d1960391502c6c090461034100d02054064491501032100c01605210803a0030601c04150101e040340380c0d004401d82400100d1b00c119058010341c00d81140c100000c112503502040000580740101000c00705607581da441200c4040407884050a5070030400d1080007100c802903085a003181006001604140d16080d40000340340440004403107103070b8005030410040c1400f00c103030980d01800f5406c0f100c000104481c21a2a510001440002c1003900c540c841024000b0780152000351000e403180c034046d0525640f00e060366034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 705038471 1250 705037221 705037259
    0xa080705011413060b01020a02060409020a0f080903220f08031207050315010c0c1518052b0f0804060e090921130b031f09020304030f08091501 63
    0x2500304a00014030018004203a40941010b0003110f046400b0f94681400030b00c64111001d0450141211300307005070303603008060030240922240040e41d03000003000240500801d90400814050b04e4000c00c01000c80110503500c01403942c4001203076030340c2c3c0400e0907604080b40e034214041c1616121004210414000080c2101407801603051499031a0344600399081c1c0421511031b00c161101c40b00842d000c0d44200740c103589580c4101035611060752101c1e0390701800c0c0c038528102800583c104030640441121040c182c001070109031520b0030034004100c3c1d41550074011000c60000c5814001844042114140d103602020303401085103034440c0d49901c00100000350a00c5030713a01c50103501e80800d006603000300e0b01c15070380d2014490300c4c020301c031545080d02e0381070300210b248144600c03c0d4100003070520b0840000314410382281ca40381e404007884007401c017012441908800941441841088006500420070900c80c039114108180107613290088149030100000f034440381e83e40104e00000e206d08040300300e04024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 705039721 1250 705038471 705038473
    0x1b0d110a0908010204030803011a1e300705031012050c151603080621011506180b03060a080109030e09090c0603010509040c170f100b01200c030a080705 67
    0x640e9070007202e82030f40105d002c064a1800108010000b007040316003c0400c000481034042d0408161011121481e440c0303480c41c0f0326a0800203030340e10500030030007030b50b02c81c80030008041d4180d1403681c1011011010000c01d40c10500a002011451148000072124000c00446545100c02c25580c5411a16903074030114050203828401c0c0e9000b1a032010030161008038031003011180c41822035880403644030b1001b610240d00300c03130b07403540350349207485015151940c42c5030f260b0010a0303171146400710604044503548500c081264204d41c0714010056492010121a1560a11500e03520b58400142104205901017151580391100020070550004102402203104440c0b0303805c41d0b910084880e850711244090694401c02c00c000601071403a00010044d0064082d0700704400039900d60040b00c0c64803c0002c0309044a61120303684080c0048104802d48650300f8844080c880001c44070b00181c0035407096103100004000c07050310f80c0c40071402040001c10b6600020111240440729090030751182e8000d51050360f003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 705040971 1250 705039721 705039737
    0x60602062503151d15030303060307060309150c020d021606210e06041518030c080901030e030f0d060b070b0f0408160605090d0e0105031b0d110a 64
    0x40200741031900d0a19295840e00119200340c2401c4000b00b0041d81442d11000340c0c1c01000c1a416500400c120401c4040704401c09103040c95075036074420010008030303240b0940c4100108803050310085001c13011240c440c18086480740301d510308030424032a0301200e04140c81c50020300f450709650004a5810700803490b000e035011080c03c402c4809031002c0c035000d07076404a204405000021203106240420155507940d00040da10f200b090024200081510155945200409041c0442c0c0062284c100301e5840045103000800765030b03502910a40115401800c0c240740800e24002c05e0740a5004191038000301d9041e00d5079a0b010351214800703600507020008105140c40380c0419000108012691a00d4000301c1d450416560098030800720f49004008644541f0103025215848990b16400c5406070b103d41c1c03010650745805800985011101e461800c1008030f095010802a600242102e070440700035030801e8040318543d00036074204c2c818202086482d43ca40f18001c0b088640f540e014101c00c0411344c4d25000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 705042221 1250 705040971 705040981
    0x8030a0207030f0f0503070f09150e0a0b0c190f051501060f1d1c0b070314160816110610090e370501020307170a0e0a080901140301060306060206 64
    0x4c1e11030045034007030010075000c0001c035490034000c2e015410134281a01d060150b141e252030041ca203850600740d5200104840b03d01019407882c20040d0315001d02440c05000742803103440b8440300c2e500d0340140c01440c09988000c0d2500103100c207e000d0305048580050899030a210300000342280340000344908800540085d101d406100c0c882c0d0744000500007603a42d030f0a1102d001000700700d010241d020009600b920011a0f640028030701900c0701d803284400f07807000241466408181a0401343c01003aa0506640e400c60154580381c000f503215400070110b030000704a0f40d5411100b600e041e4851903115100c0d22403201000320b800b080b08544020344031001801e10030500c0c20900b0310f6a0b00c803555070341c10749580d101c40400051050305081d030b5282c400310045d0440b9501141c65090880e030080c0d03180c80000700c0484d24550300074840d0f480e158016048100822000f484002006e40308c01480070000c00c9000c00086c030307460603071140c074500425a001501466507941d60b86030280c0203085900c28040540140b00001ea = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 705043471 1250 705042221 705042227
    0xd020c01020a2622090513050d0e13020c0106180c17070536091314030904021b15060d0b0a1b0203090108090a0807170708030a0207030f 60
    0x2c218650281906030000d0042d0480e1510b00000c45601d49800c10600400c0700750384070480440385200d180c0c10303440ba255040440740d0741960070090011403040c414012110000703d000400710502145441e0503101d01080030300041c3c9164000c0c0d503294a490012a00a00c030701019800042200c0303007000707000052081c0510000954094200d4207000c62000c483c0780b84c1201c0103074100d540c404a80d207482494088088d9914000b03c03041092192601001103200760384c104580c11510f01034030122201001450078103142c140f1190080e0005001003580840e46400305410015500c0c5c07040300070415511203060f05a019151800154000041d104041c41560212190108540201c0003d000e80302c103010765841303000c000b22014007015401943c0f85aa8941c0320f142030b0328000300c50300c0e65004c1d5a60b840a4000106828001350590b8100e42003203e042000404d10022600d8103a40100424a10210402c1c101e106005d080b80241ca0740300c0000812800a8841e4001c02d0041d22946508000c08507043c3c0032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 705044721 1250 705043471 705043483
    0x31709030a050f250e0c1b0646020903191101092106020702120f101a0d0f020d0506040305120a0b15160f050a03080912091e0d050d020c0102 62
    0x80b4446040f006c60525013040c0000d1074035000c4c0a0701e41e5050150b080011f85481011251100c4100485480c11600d0700003600558047c1d020008040c10000c0350200306400c819074803460311910b42d002400b2031803510140560110a00c00d5050011030303450600300038a4100b4030014032800200d42e040c0114498440564903001800785201e841e01c0109155190f400951002000b0703640020b0042440c01c03600c8080101407211405c0002a203048180550502c050b0785408400b2190b0a420344042090381d124500e000070b41d550014103034400e4070030741d002061050036000c13005441c81c040e050411003815002030090110308010740c0300c1090381d5241c90340c2504403035525640079071104210340340410805071080640481e44005000340450481aa10740d88644503020007118242c215800c0303203044c107400c62071321359210242c00c001d400c05a03804070031030001c0e1086480303c0e40b0408a00342c0c4048201900f2107800c0480360041d000344242c06c4142003040d642c1e001045190014490f0706c1c030b80c80e880e51010070a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 705045971 1250 705044721 705044729
    0x18010e030a11130b09070e040c02070503190c03080307020f07050a0b09090a02040518160309022202130611061506040e04020f03030313030e060301031709030a050f25 73
    0x3042c0040c80402040000480180e49004096030701c40211041d255640f0801c180584155129508201d42c500c0911058408400d845000d54000d04410892914081144600f4140101028440700d0309880c14034081c0005400180c40e41d02e0100410401540000b55106100d14801c11501c0055680c01004802c030605e01a107a196602071002242d5420f140d070580d40c1110007120054241502d0b40007180700b00308444041c0c0d40a02805003070014a000840d8074070a402c4c03103460144404a4240c001c5003a81007120a0b002601101d0140d4050980c2d15034151200d40b40c642d80c10110b43ca50700c0000030f0140d0785200c0905a940070714404a940c07081903012260303030b4003800b4004e14200f07403a042041042a00081003641c0100040b4800c0142d1369090008503c0755009041c0060155040d040080c083d4a242075414018a420801030001c1842460800104142282c2190b41ca0140101003401d14411100c0140b16114190b09011041c0010910711002d0000040e142503504078250821010483c07481 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 705047221 1250 705045971 705045983
    0x207060c08041a041509030c02090c0703081003050303070c060207060903080a0e0c09070e0a090203010e190905031c090b04080d0b040203040206091c14030910020f07170f0318010e030a 81
    0x145140d040246400070700c052070003030400e60045c3c023030ba801140005c107044a44050180340040c2c070104041c0c21042c403503040032194498056080c1180d448038ad8030310020340f05600b8001c2283c803a2007040030580407100f140e64444c6051207002e00c185009400d54800b695407c0885040581c04285458001092401440000c10719a19038640b14000d9401018008540d0b4000c0c600440100b840e80721400118003c0a40c010556490301c3c020138141019130a0766000311666040c40799040c0443d5001090350505446091544010480b000302e00c0018184030700018594504403040005000c17070040540000110301405000303030940c050404c0100e100864000790b0241d01071004c07146a003401e000c10541161110080b4420855a40351074032024902448025280c0c00001d004481d41012072626003011060700003000040389514000d51946070034098000c070710000701c9128040c1d031001c000314030355a0005010350f90703184045403081d0f50307032400b030000706010501c00c6007030301c855003400200c40e0306290b000700c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 705048471 1250 705047221 705047243
    0x5100c080c16030e06070b151002030f18060912010b01030b1002070e07030204050a0b070201030c080402010c1209050d0303050103141c27080c040624030f0207060c08041a04 76
    0x2640651318454840809a0003090a00c203410010340350543d010700070000c00c50840c40344c1782c1c21020003400001c03a1070440c04541040c024060303103181e017900340c8210b05c912064410807121140041016030007003036071113544411401c1142440740c1c419402480d4506007031740c05000c00c6070614140150045141c00003030043e846440c0030400703550006240d80d0021700e42d15001d40b4041d075590005440d0035840c0c01000390064002011300071580c1511902300480c0442c10301d40c00ba4038240d0000b9001904400018010040003200d2400e40703031144400201808009104407103c1c1614103008004003024041140d20300009850002800000103240100e01da071002c0d40441800d041004035a090300e1100040010b41844c10251021181040020040c0401d0401002d484a000d42000280e40d400d52184a8080c03510710b1418244001113403c030385111050030081070002d2800f05400003807180701c9000d450302d80703802d51020030540d111310402d0046025507000c0e614400c10004060520b401a60001c0941c43c0744 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 705049721 1250 705048471 705048473
    0x120f0c1409040b041409061614070f0209070932060a030b06031305010b090403120b130e070608071706010c0212060108010c020d170105010e0a0305100c080c16 70
    0x403000340440c00c03000d4000300f55010031001042c1580c0205d42c2d400300d40d175500000c1181d44901084900d901802142c00d1000390354403c480500458651401c4044985000507100140000c4018100300b01e503000c0c050951a01e0000d0b0010a40080e5010b0b2801c04481d090884404256080340b11250701c01d4501100c0305201c181c020002c1070b03405015480103250311095500307026544c80010358494007031070302070002c00f02c4146441402c40b107207500760310300c5443c962303040c40003080d030005c001c800401e042900003d083d855000011400140c0c000c40d00151410494601e1014101003058812039510361101c00c00c035103800009448040e400c18026160040c502c00140c51584a1114100e47c603001521880c20308040410603401c240d0240c0048205039103403c28080c0b81a03040050a040425510b131240351401c265104090150041c41598104840590b01700c5181d5a080c0b01a0010740d804000c070307841e104030700080c0c1d000381425404041c04030703e034480025412640300d001c82e5240d030091a11034101e01c401d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 705050971 1250 705049721 705049757
    0xc0b1f1e0b09060f0c0a05010c0f171905190e030414030d050f0304080702040504060e1903080103060f0e03190e0a03080a0c0501020903101a01090f0b030405100606120f0c 75
    0x1004035208548620b07000100410802e09c90410303031104036a268824048691406440c0c8a80200184c807203c1c0781c0c00401c0f00e50041e512120401c0005040c2c041096180d07145410452481261010340907031070101c00103074554002000f8130031102c800700c3e0301c2c0030006a002016119020f10807500d0115400300322000307484c6003031801903070700c9880b40260074144111500403804454040f00d0441e4141c0d582c6102e030300c104500708a0109010f9552142c000d80301d50642d07008281c20740c10320006000e01d840341c40400030860300750051f90300b95851100f1280c81d011b00c13403800d05000103200b060101142d4240c2c0b904040c0d007014801082942d4000c0e000c40e03e044a050b108a440301044001038405550900c0341c1c121981d001e10080b0190b40c10a003021a034140007604e1a04506404100d007814002071100420400170100c4c042c00845503400015500c950b62402e00d181000b051a005001c00c03440e1100201c1c1060300301c030b0307544085a034040b81080151100c10001c011182d5000d07801006c1002c0e01c08a00041803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 705052221 1250 705050971 705050977
    0x10e01031704032405010f1a090f090408040e060405011203110c09011d010e09070510050c03030f090f0c01050409021b030c010605010809030304030c0b1f1e0b09060f 73
    0x1840ca65503514082d81c0342c881c00ca4030030701c81d480a030b81207540d039040140c0d03134034240686400b41a4000441050300d140c0a0003614140102c540f4400000012592210b1541c1c3c413903540360984c001038600c4142e40350910344001d8540c0b080c058280c1d82c0e81503401260036424580301d80c4e4180c4166801020350207426840965070b8100c40f142900d01d03403180740c6500b001c6444600380c01d03000300014001035000d40e0340c106440520400582004000300298402c204000310009101002c49005550752035800810900071038140c803c4150001031440300106001a04100d10841441611840280c0f071101c0c2210110359254010009010f000640c1440240316200c1d1650050115000c0c2c0040010400006c0601606507086818025007a035074414040001d543c0244036940e001c0031110255142d0700d0b0555025080d103c000300040d1804003135a0002e4011800c1142d03c0081c00d00ca9040e00c000f082d0f54448105201509883d03120540c240344a0008042c0e591001750707a41090000c0915040c5482034480701c4440e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 705053471 1250 705052221 705052253
    0x5011e18020618040c0504150309110f0102190515090303041505060604120803010603060608010f1a0f070b0402031002281b0510050610020303060f040f0e0a0c0608010e0103 76
    0x3090f030b5002c141980d1303114425400001041e0719455212843c02c0840142603c071a0322401c140b5041c4148a00040d007110f2002e04120400c44030309814410030b400407460a1641001c04482d0145041d45005005000130b07110101c000f04040707680e4540c2d0b002140e5442e804281c41c0106001c1011134160784040c402c1d04900d500c1000946a9030a0580d51400d81000701c90794803090716000c80c008014030455a040c02244c0140c110ba0a00c0c005a524240d00120480c4003131083e20250b4051741c06032000b0b183d440d4101e80040440d28201d648403040390a0001410f00b0075102240709100721308107054819074a000f95083c195003003200f200d903085141c54005404400c04140d00800280c107600d1011041c003031b840c4840c072030f0154008022010b4803c081400315540500704038414038421240140203540041141d511400550300103418216050103d0f0250141e160000716031402d00200d000c02d170100103158402e06001e502000103007a9210710940340514203004010364084000d00500200c0c2100f583d800703c803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 705054721 1250 705053471 705053497
    0xf06080a09110a06050c06130309030303020706110f0903010608061909020f090106020706111501050d260d0b06070b2a03070507030e0306190902040f050405011e180206 74
    0xb410740ca0001a842c440e068215402042d4041341c1c0c02058082040444c0d4488040520b107820038032540c4015003001c070184401000c041d00000d00748200801c03604a08901c41c040048036840e20142e14520340780ba008104002c0c001e600e0408005000b890004106000d0b9030f0414656009500456840c4064101e183e0166007006a17407807807244036280d40f0031041c02021603a014008250a1140003082207405640025055100301260031a00c81d114101a045440440d0125440741503840c0c0040300c40c0d1403850303410102c51140131400c0c9510740ca90040505141c0f48070200030009810701040038900503c100945000c584500241c40261451004100302c04108000c040300a039640200e0b030241d004440c850001040031681000701500b10380700c61003181c4100c014041c81d1410802d190415143c2c42c1603d9a440c0e00d0700380410664440b41e210b804d507071135060740c248264a40340c213055019001d03032071121101c0c143c81c612181c4811114462007883c80b2541c0d1414007140290b400f00080c17500301e441200c00c0c2c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 705055971 1250 705054721 705054743
    0xc18060f050d0624030c0e0408190c05120901030b0603041e030210060f1814190b030f01090b0112031d0a0e1005040615050f0d0e0a06020c070f06080a09 67
    0x312139900044260203540701d10610b0640d040d4075020901c600c1036403040e0100b000b40028400040e1070300b803c0c0c0c2c00c0c126071010b800d96041e02034002125000e0f4080d002510900520140c4000618140010183c17008203880034020402c890050001d1480210740160984901d61901c5a0502405040480003400307071048441c88142c1e8180d5400b2a005c0d03900448800500c0d41741000400c41350301c03e1200042d40308404100b9010041514460742400400000c2c401c900040f40c1d03000720050703a12000d00c01d6809800c0710401c0c1c2050154600810b5401807e40d40f100e0400300020304200c6601c03040c0c0c0f001c1c0d4169216842e80310a040c0000b10f041500c44095481a0328050205070619100c0700a481101c0304c800d8040d000389020240310885107d908000c821690040c40c0c00f04281c0c10000302c460814006c4005940ca41c003048011000b0000b4001d07a114500401c8031b14001e00070380d0f4016200c501c003140c4c151520144d036801f121051080e50f10400d0013040800d0001204860b1503030006103064020384410311 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 705057221 1250 705055971 705055991
    0x18032705151e0d05010e1501080609061504030305042301140a030902090a051806060a0e04060908121f052107080d0f110109021503090c030106030c18060f050d06 71
    0x1040c3e4015800300d403022591000100400070040c6809a0401d154840c41d029461510000070508040140071074010403840c004140183c03269600c0070580c04c111400c140d01c803903c038500241140e116104403402041c590610b610780d042800086d16000301d051b101e235803a92820080700c034a030b47c21501c1d842c0b051556071100c0c0400740e11010388907840b440071280c000446180200a00345410755503400c09401e5404681000701c55141c0d8a01e150a80d5041c01386500340c2d41d81d601d00740000d0001250000c1012a0105289041c845000000e60082c2074441c01e0a8500d50070880e0703881d480c83c0c1c521907160302c07121010310071055104640000e01030444c40d40c02e55101c41d0b2140300b81c514208200034100300081e502050426402c2d0b2003021003038a482400001c1c02034802c95000a4080e1140480c5595a08000004500c294208111041c007005000d0000c0c0030083d903a0600b09070503000d41c8544080109030071003040c0c0d841004d00c40c0405480c0202143c50b003040c200780c00d00c0b021940405086421540c1c40140356 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 705058471 1250 705057221 705057277
    0x405120715140d11071209030203060711011d1e061b030703150f05041503080304021c0c0e0123090a02091504260f030703050d1803270515 61
    0x31361003078250048580d94680524002100303503c40098403040002d000c03400c0c070040c1d9002c107a2940059540ca4501c1445403240301c100d00424400310713010710b40c41c0000340c5035a42420110b81c41c01030040900c5150158080150312700e494a9040b285284100b061210503c0c1800300300019680060035480c00160b028145598028014107a07000222010510182000146094060302010602c464090b01c0e5080c69a580c16049000c0604001e200300c00d070554019406004401440c00184c0080429480556a00d4402c0b40d084080c0151000e4200d4560400c0201125030085122200d010b0203041c2982d4030609541c00a4214042481d8400c039a1210f0403074210746a40507002400b0400c0408112000ca5030b6140303881c2070340d107800740d2154011283c1c601c0160301c08000d558985801d130030304aa860424240c4200203201054046600d4880344e100b00042c144d01648040300031210445580c440582c02a060915907150311445030b003c08800e40d00401040c904000d0030f00001c0d100c4d40e014880101e10101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 705059721 1250 705058471 705058481
    0x40804080f160b040f03020d170f180906010e0d02011e0203090a08010501030506130609060501150305251416050a03120b010507060504020a080607050405120715140d 73
    0x2412181e12007040380d450303a0420380c2d903000240f00988860f40362a01d4042d40060762800c3e071202a10420401e4140014400044041000b12140c808140c1d81c46920101c40303074081e04040208280c40154003096a41400d20200c2e0034001e5805844806030501e1400400c900b5080303215040707040180d148004aa40c00100140c01e0364088160055a08c0d5594230041c0400b03c452a4001c0007641e040c440104049100440ca194100c0d030382400351060f44486060403000b400050100421a900e0500000303028090454540340c100b1250b9400e001e143c940c504072000641159018540c01ca4640c900817405502982c11443c00180c00c181c0e1782d081030111401d01c961400e0001c02640c26401201c010410190703c4101d80c0441d520a0b40208041e90001c00000c01e14000c90070020082c0d42d1303600118043d962401610b4008100071400c80b0f1107440d088800030000d41141c407980c0e0003180d25000c0c1800ca0f03403021070b00c00140c54456031210158007020b641250303066180b04400300704603820040d00b010b102281c054 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 705060971 1250 705059721 705059743
    0x1030e06180c03240a020702031005151e12010605090c030106080a050f0c0703120c051b01060509040b060a0305030a0207060e04092406120c1a0a0c03030504080408 72
    0xa0800e1820100c98440c00e1080790742d0200e101e0740089641c0500040505502c11041d801d020342c81e9100e5444100c640028400c08074040e50500c6002511030760042a40c200500c02c080364110140044201000e00c41c840d034410441003000801c580035a891400c05102101c0d5046984c0d00101305103a0395800705d072038144d0070b881000928000000512506410425260f00720a02da8010403082c9881501c142402c84090300c0700b04542c40006410b01454072511540e020140c89200030001d50b0300d110405040c1d0f034045502e5160314103281c2c3e0310b040f02c8081840755800316000944041040d60b1207955032600c1c400010041c0e0780c801c01001004c0007051041001d82203030180e680081003810704050002c1c010052649241b8031490500c09100700003810b1114220b070b01c20341e010080949a40c0e0180810180c010307900200608003080b00040709003d03030810341400726041c0e03d9101c1c9100c0c0719a4070100c2e8502c188842000031501c001e2034071300024440c2e8000d55000d0700803541c542c10943c0f00c0d0074080c1401c81e03000d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 705062221 1250 705060971 705060991
    0x913060f0b040c02030304030e190e0f070e0d05060430080702060105100e0108092509050708101a0403060c0210050718030809030c04090f1506050906040b01030e06 72
    0x319840e8030b050511842034039079201e000650461402d60f600511110000c00414020f901c24400070b0010100015060701030644022102524501008604030704242150380c100012401c80300300d1090b0030102969608290001c010b48400d5a403a11a00f070107407041662002040d0030301c002d8242c5184008080310501c8055515400c090030a00c81c020b240c85010303009644209001d040200e101d54200c02003e840f44020300b802d02c40c55481400d1a42020207003c10124148844c003055608100c0021259054603c05803080101d601c03001000c5503254000c0310382034928141c0d02c2c1c091103140c038801d0700c0e19403030305040c56602c0c54a510b9580324420380f180c200101000d40c0c007049031200758600038002e15500821a281080038410004920f00704864984005000100c001402060310744040c4103008100601400034000103210340ba0031003011294030419541d0f2108041c3c414101c5201d40646022600014503034901610380c8410040104500b40741c00d0f040c1a9034114040c0504414807a43e4403c40d181a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 705063471 1250 705062221 705062231
    0xf031a03030c16050306070503041b05091e0906100326040b12150306071d09090604030813080405010302160c143c03030c070906090606030b0f0913060f 67
    0x942d4411400d0360b130700998425000301c010456000d9000c400e40c2e034425000402c200000d810005591075a40c40358025503000f85030030041000b0342d0f2102d02d01c5207a800302c0c404020b007a0fa4403460103c2c1c84a40903510584018000401003001ca01408512040d1840014070110b485000005004241d0300c03652001001407404035a4102c4e491781c0c8054144d10105003000c0c03030502e0710352600003501c8043c0146118288404444d0084901000040b04401d5001c05882c9200720301380400c41783c0d031b0380d40b084400f100003c5260000410a000360744140441e1540414072a0426091200544c080d401c8000500488056440444040350b140119800185031041c0e5071900c019188080c420903213107806400f5212505409941d500708110510390118400c107040780c070740600c40000003070704500c145d104030a4244101003002c24074011581c400030854460400400000e0f540702015000d03a1030b4140b05942c0180c541c1a004600d0a090b0b2002e41d00005000c2c180070004520f070395500484120002000441c0d50351 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 705064721 1250 705063471 705063493
    0x80d212405030d17091207050a051908070305030a020f1b19200121020a03050106080115111002210a0504020901270c080702100c0f031a03030c 63
    0x44030802528080e406080005101c000c09482040034a1030008004882d0002501422040c030041180f07141d43c40e0011b6a900040c20495512283c10030140d40502810b5541e14a009540200e40c0040d07900c142c94909000d10368070180c606400040c080e8044580800c5004650214400101481081801d100b4240325442016038070f01840c1010842d07280b40180780b00c902040d12045804200d10910817015017044e000b40048074146c504070410f1032119594102200688120703009480f200280f40d50400480c3c0c2d030b60104039031448083c42139034406403900b003651040f40d00ca079280003081e55410088032100c0c406c40c0b4000d0101d0344508038807001c0b9110060039030145d241594581d600002c020f0814402e504080c4c0018660440622507085a400e50a001410002407061040d81c8441f0b05181000000301031240a84001002c80c3ca42005004110415400108901c900b41c81c1c0d80d0b090742c3d4083c40d4940c8503400e4004145680080020782d006203299805540c0c1000100030440d50100076281032500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 705065971 1250 705064721 705064781
    0xc0e0103030f021b2b0501150315060b0a050a030b060c030c0f03070309210605040c030b0f10140a03050f1507020325080904290a080d21 60
    0x1030070700084c0409880351511640c1e035078a034508411800b40401c03620610700c2039080c5141540c1014000d155500f0b08943c18214403106500030100d0b03014034050040f5085024040c011113005002c0d4800c0700b0750034440001003034401e070052b1080c2205810002500009040020420741010000701001d0f840040c2150740030205010100c0400545801142026032594020301007124a0113020fa113141c905550a0b815600e40c5400080540c02c610100100e00706800c1403540c58030380c0d0005039503070f80c3e040c00494500c08007203e1141c420030604c003c1000c0e079800c0c080d441000c1580703000c0310b541c8000016400301c0440c20a0205050300144940100740700102a00144107182008100c042075400034010b03007046200c03403840000308250030801d68149030098540b040d45401002e01c41030b0820310380403410000b11018200c0540d0546107003005810004240b04120482c410f50145422a4000c030a007401c01030b00030801d0000b0301d0358580c5d072585904d8100c0745500845500700d000307070214050a1025400588 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 705067221 1250 705065971 705065983
    0xf010b04150503100e030d050408091509130c0306180504110d121803140708061302030705040e0c0907270b090906032a090603010c1202070c0e0103030f02 68
    0x2003106000001490040025110342886013400752a41c0c488600082c100002d10888a501c0505a02000306003000e0030300c40c0c0250040e004180c0104210311089807241c00300019181e180c003008200c0081d48524011440240070010340084c1415200d0401080c8040414204194036002e16800a80d078901410443c0d05e103a103544030107005005000007440400c40f405d1445910090606101c40c9041c0000e0028a94035519130001d04003900d0002c0c0b100c980c00002c510300c001c0b0b4030500220703403c5444041c13401101c02942e800003036043d070044404020b00d082c160006000d10209105036a1041604408200100000c5450000140020400340721842030310344101010b2401c003200342401400e00201c250507110781409a4441c051810020348036903003c0020300400800302e21011140f00d002401085000501801c607032140c1411000a045400d051081501e40085595001309105445c1d014038001e40c0191400d4911118041000c202c1c680c0b5086c1081c02548640d0b039005000020120007410b00f4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 705068471 1250 705067221 705067241
    0x222050613090f0b04020a030b040b100b0408030d050c07080f1b0c011b05101d070902071e0c050405011403011a01090611010e010e030a020715230c0f010b04 69
    0x203142c0240040882c0b80d009410410551204d003207207907529a40009406903003140d100401042c0c40304100000c11450404150060544034204052143c0703a00d0314803403900039070141102d00c0c0d0041c88003103201d159680010750032420128000e07241a0003521902c0c05039001c10301000c001d410009031748042c1102044880c0d0039613801c402801c0d40401800c0000c0c40341100490308041040a1101c0340c1c1402814030003102c098001a404200b03201d5100d41c0004121559140740e02c203070203000e20015003c07003180202d48505a100e900c680c0702464604d6060380300060040c00382c82c41c200141c0007045039110391050318081d00402103030b00a8540160100760035564040d44500024401501007600d60341c1020450054641a081c010000640941c0560041c22000c40d4108c10b9800c0060b0746411000100082031903039840d40c20f80d611151920800415840401d00150000e2817001c005896546e0b01540700e0303901c09101010a18150188404a142210a001c8003080c0d941d9940c040c4840d1516104048050b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 705069721 1250 705068471 705068509
    0x70b0912010612060b30070605070f080a0c0807080702280b0309030d021b0f06010f0e15061c15050a030204020c030c1507030c17060d02220506 63
    0x296041c8203c2c07141004007800b004060381e807228031000c00c0c0c2e5500044401c0c228076021028591807110240ca03c40140b019408800f05d000d441c20100d14a0300c103400700e0b0401908152044c0000301c441d5100300c8984e2103d400340017009100c0c00309000144407000141082406210015204c0b01240100a5040a040320384186520100c1a00450000304000c80301156074407103074640c40703550f803044c150300794400e030301e154540c10b48005040c40c003404020b009092020f485d902280c1c0350703004045005581e06400c0c013604840300c5014008010054452001070342c000c254800140d60034060101180264010f0200c0102c2450900c0080c1c040900b6441241e200003c1015000511880d0002090100d003080c00041c2c016074000500011040c010400c584c0701c1d00b8040e040310480f0f84240c2ca0303a981e4010a032110b4000909004503a10003e02c42c680304015664500501d4100362100002c001c180c0403002e004a80002200034045040c1080b011503400140f00f02c01c001ca02e92410b2000c0000703400c0c00080c1000300c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 705070971 1250 705069721 705069731
    0x310b070302072c07090f08011d030310090c09030807080306100302041401030b1507050d0806010302031017010f0c0521010b090d06020403050d17090c090a0c050c070b091201 76
    0x39041d65500425020f034014408140d89404d4400c4a03d40c10507005a40000e01d4001c1c005500d0310150300c603206443c09002c6800c40c0034442842c2584a1100b680c44098010a003842842500030607842031468003d50f060844402c0d50301d554100c1590489a81542c1c07010010080210b1030070700480307100360811030b40380c02c600d440d042042c50300c8148100030300ca60400d40d039041c40c0c04654407034031500120007c2801d00b407034444600c0d14200d59185850700b007510010309200c01003600d65019000340c03401480140c0000b11b089003000d5001c0440151140743c0850b070364890307800b07401c0c40307140b8895031034101c900b81e9aa0f07650340035803005002003010075241c081c054803c1d00010040c0203c7d060980e4070b01e0100300c80f980e02c0380c0114213068004c0e0180e07400162460103800c28000740c558011920302c0e0030030101070004440e90b41d000781264884000003811900710315110005803100d40c0380e51000c000e598141c1000d6050a8030051458540000f9410011801c400040c000e00c940c50449035001e10400001c0081c81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 705072221 1250 705070971 705071009
    0x90314060405060109020a0905030106090e1509150c09130516020a080301061b0b0702060f01150905060a1101180501140c070312020c0123100506310b07030207 70
    0x10340c43d50305201340b0315840e41c04140e6201040c800d130340800c010300b0000c1c002e1000c10380f00d003803040081148044080c082d02c140411641400784900465100300f440c2c202400a29401c209016840400180740e01c80314501080103807100d59401c805004240d114600010715450036230100642d05885142e408117551000c88900c00082c4035408581c155201b600d06402c914034a1076801c030000d0f01d0801c1c010b04c0341c01c00504100c0c00355070014034544139030924408460030ba641c035103ca1210149050702c010000b482c0c3c6805120320300f4034800404a410492800c1c15540250b0b141b00b5003102d9614440c3c00c40240481d2000c01402400d00400f50354505400c041c1c001c0c4c2c01d12480c1410f0600c03440300300030207104910402510148503030f07068460300700d0755000034460141641e081e81a0b4100c0801152423107459400410b8100c0c2c07014402e00103840f0083c03d410310340001c50039071488200c46502800c00d00e403501c00315030010700244410100181940900c4640b035070310500d4068203108131a04100000c003499013040c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 705073471 1250 705072221 705072223
    0x207051206060f0f0a0b0903100c050a03150506070b0402040b091003110406030602160c08070f09020c0313150306150c060905010b030d0c05240f090106090c090314060405 75
    0x40c1d00524100c03414103c069200740030071401d0842440d2203510005003c00055609081c1006040d407180c11419281c0900078490140107e8514a60800015005001c40c0030707140c1c0681d000c01c0d514902020581c88650b5a50002a01c580c4210400c0b180d060740501800214100360240100d1010129610001031500b030000c07001d03c0340f503480003400ca02220328103050203031503030307032004000d103403c0f00007555220b15500c00522032446841c800c80e04030072240400105050041404401ea40802c252041000d142a080300c0c06500040050082e5002c100580700c42e03036500d124100c0084c0307003110918860600005014045518a42c014280e04505080101c4c01560100c0740d102180d42c40000024901058207000340101400c906407500f500c01e0684411180e900452403080b44c5e4460401c4800702007107101907000020441e4408241c413120000030540c000b200b40e118035802179074040001103da0341c03401e5041c10354040e0300b03509000c607880c908103005001640145462a490f4207004004500b0582e50705 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 705074721 1250 705073471 705073483
    0xc0c41010b0a09060e0c1e030a0b130608070b1b0102030108010c1107050109060809150108030415020f0303040f08070b040803160813080a0c29071407020d030e04140702070512 77
    0x9081d840000292117440c01f0204601303203621000720840700d4883ca0603030f081c1e500070025a451740e44200c180000c040114815030003600c042c4c07902c20028090b076078a0809185072541094402c151414035085441010760750034030246000b4181c99001048140942c0c6001c3c001840540f1522502c0d000007a003801540d0b00028480210b542600d425181c55030303090142030415516000b00d8280184490001136150800400740c804d41e840119400c05081c0d8290702a42c0e43d90304051007902581091002401280c414040450103a004d0b0000901d08803840d0307550000d00c4c00403501200e10160210600496034400d00d0720720440c1c02241010526800c1c50300c0c031068072400380d04004041840c002000f00015108038039060215601402144807c21480f03920b000145001c40740500c0c4401700000542d440b0310556106e00c0001d80403259518102e010f4080c026013200e01c0301c1c254240300e44514412441c2d11540f11710104007080101d03050950800000081c1400800d0780400d00c00d8003101d03610030700c051000c100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 705075971 1250 705074721 705074731
    0x20c18101d0c16240c02010905070b070f150e10090302210904020a03020c06222a0311090f010b1c06030f080c010c0c41010b0a09060e 59
    0xc060720742403c54140e102e00c440440d801000740139144c041305015425041c4400036a0701ea40400e000595640408a0888003009070140c455800f01c2810020242c40b10010010a03004812161919103162100341815040681642c0407030755516040c840c0e83c5007401641c2010b105103900b8002403c507034900035510400c0c180c4003011a000c854038400b0386140d40048818400001d00b01b952036030104540500203400c486400c02c41405010005665070302d82c9466104d0401c0c810002046086840d1206c4041000c90381c0340d6040880008400010081c06143c1000118415000065020300c100c050007228840501100750000c10100103000403403581c0140c40d0300d80c0802c528425100706280c01da9003d008143e10260401e242910000d0500c111103005102c00c02c0c0302002407001c002c444808403030601c00054064020307400b00d400b0020031a03010b0b5004d1042c4050200081c4c014400c80b0400f0841045118500410b81d9030303c9041e41107061900500004114084003000007a24110b0010303250900202 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 705077221 1250 705075971 705075991
    0x332160807030825241a03030a1d04050432060c07030302070813031202061b031321020c0f0604050105030c16111206130210020c18101d 60
    0xc10f0107902d80078036000712213682014011600480c42e101c000350701000000d061021504002140c07504419105805c0c41c1400060700840c0742c104000740845103801e60b40a9100c00401402c0c1d000604d0f23440f0700940b40038a002c0e41c0c2c04151a050442070000f90020b070703900c2000501b07021284840081010a480350700c000007411081c0d990405141c21030007072262840040603a40003180311400320540554040581e44203c640c80e2060795040d0040e681e0718800ca641c0c0481c0c0c07461822148007150360001460700038040381205d048588440c4e64611030070144104406100754600070114010340d0410458444031030684040e07011078155004030b030141c4914020141841f000102142c6141d84000495000314a0558511031020301842d100042000c0145400d108004815401400d01c6001c65080d010351565111000840c4882c1c2c24406e01824071082541540031780c6110906985840c440500e40c81d80707040126205140008120400b00178907003012948400300040803c540010714031450700018009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 705078471 1250 705077221 705077257
    0xc0603060411040f060314090303060d0213020a0c110f03030412030504080a0309080c0108010b03130804091107140d0f030e010216050a062403321608070308 69
    0x100401d000e003207105003030700e030040000030b00080030540f0043d01d20945940d96014071030407906e050405001e22066400c4981a00100040742d5a860082e1007884854400782403003005d84240c11200c0101d800aa411a0110705c3c40d5440c4410800d03c03100c0c210030310004a6642c1620740c140c1d000f09659010314001c88120825412010303003414003c000340e500034a02601116481e980a1034002c007031620a00c42c1c000a0700c40c1d0341c80068a58090b610181c140d0305402c0a036400c45d42c0b00d0715005000b04400409480200c0d0270400400d128056014401030012101011070380c58045260007041210710411071b903666007001402d03465080d48040120100d000e1b0303107004112100c4051a2900900c181031441032041400703c10f820802501140b241c09a03405680c0811419218800d19415a4000cc00340712184060808c1400000d07070302c0d030030744000064880041c20b2590004c0c4c44042003141c2d030800390790140d100c45c0700c600210100d0f03500d440151007141c018141e154590340e1162024050741050700b5050040b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 705079721 1250 705078471 705078481
    0x18010807090513061d011a010507022e030e121806180a0609030b091f090c05060301080601031205070804060807020f060103060c120b0a120c080304080c130c020c0603 73
    0x243d4208a64a40001c41001140c055403ca0111410481150f0202d542444d0180c060031034840c007580402c03401030b16030616025803942007096207900a40203c07103000001501c1980c0c2c000541c00d140b0071608644000900c1400d012000e840c100300180c85402c410010002030446152a10110201600544619454050300306048a0358203c2003200c03070b007182c910000041c080d41d1041d0280111f0f4081c6185e51500c2d1111500039031541c0c0c490320107105640d82c4810b000294052a8000840d1900900c840310406440e100000d01d5684281e0000300564045401403041c8a80c03410002000182d03800c2c010b1503c2c4440c1c1da1590750740030307620496050084050004061500a0014842985403101550000e6849140060080404c40c42800c0010480c1c5850920603410f0b201c1da511100303009101e48882e034940444580024050841114109140030002a0807441080a00060000c0e10b010700b114a50440a00c0034200c0259441880d09080284c0a110690003240c0c0004404007620035070340d07075910 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 705080971 1250 705079721 705079741
    0x10905030412051e060403110c0a06110f0a060b0109050913060203040c1e090b01050c03030f0a0216030801090f0513060905030c0a060b03070801060f060c06060b07030509180108070905 81
    0x10000c5004c03480c002012200119500403c4482c41075207c1e8846151a102d10f070b047c142e840c42661a40354101890840a10481740102c1801504841070b10488034204c400d0602d00f400d00d107070f04000f11481d0351a06607140303180da0009202c0c0081c00041d1110b02e45480e1100640e19007805070200a4007180d4004042401d00102c1c0ea89000030341111f6548894881e20301e41010366426103403041030007503850025280c6003588244101c40d45c00e00400000c60440d241c0c016659080f51001d0820102103500304842a00501c282d0340c80644180241c84403003080d0b26000c960019110800443d03c0c84519200800c08060b01c60304410010719000007002920020610b03203185944140a4050168400c510541c000c00201350030814059500b5010381c3d40c02e9540d00106402d980c45030003505c4006d40d00c1c5800b40b0003d40700ea0312540d18503008603008105250b90704082c845543c071444042e00082e40c0003e0080090070680e0743c884100055414603c0d0540c94400095102c80340f074012100450740704c0c4c022901d0090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 705082221 1250 705080971 705080983
    0x92b03150b0d0b10021e07030506010303020d0206090304120f02030c0406090b1809033001030b013f291e070c12110114061201090503041205 62
    0x2696003454003240c5030a4080000c0d0031141c1c0c00c0000038280003038142507090040300824080d015800618124810020f070b244064880a08030444e44103603000040802c4003003248600960098001e02024280004001d0420000811201880d4001c2100308601a0406a0006095000000d1011070986440000c0c14510a80082c543c4070341400b90104440c40c2c941d00c02030380e030102140c0c0e0b8603c1119080c07400303442a00c111545e24841d0001d00010422a00c8051103044891032000c0da00d11401c80c030410030001100a0300240c4054901c403006118181d00d200c040b0b113440807009840307103a00201b2204540c3c000d40c01220740b44000a981450420456000003400a4090351410505411100310000203101011100042c401659044c40d42c6d43d914075202640c01207490765100084488141c451102c045000c1c107684042185001c0020900c1d4401e100f25205c2c2c001e04a00c4248500b0700408021014403800302c814a180d240050b5000000c00000482c3c080344c2020140801e01551824080d042c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 705083471 1250 705082221 705082241
    0x2061b030909010f0501020d0206040f0f151109011b0f080901030b03030408030309011503080d05070c0203100e0d050a09180b1201140a0e0a03180f0803090306092b03 73
    0x802c1c0c0c0b000407a9810a9019a2003601d00c280c0c01c0b201b050441800807a511030040e940034100800028103d00031444030241e00380018020401c40c8504c2c0100c8061504030340c184100c003a0024004502c00d00301e5a4041c014181018240d031824514200c1030721204d8400b081d036900117105410000b5100000c2c0d0007608402030070400203055036204c0d60b4075440540c407030b40101d9031540c80b94641414010700c0c1d0403040198040d03d4001c48280d040c050310548400040102070710301c40a005c4640d00320001a50100f240c5c0da090360b141d00000c42c045100160507403801201c4480c000070b20400703000b103941d85540038011030110b030100810b14200c0c0300700301c0101c0010845c842100d40c20604103040490b810380150001c01041140d0a07042e88260398050092080780c802c00710110b2583c000c0d00810340480c1c03050305070910700c50001da0551781c6030303945440407460050785a02a40340d941000c0f82d00340b098942800065445203800d4080c151000703462030640390900310030310040301800b0f003243c141c11204e2007035100c00c41030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 705084721 1250 705083471 705083479
    0x5040201020f070915050a1203030c141903050606180108040f1b170a1707140106180e07080601170703050304062a050304121505040f0201110a02061b0309 68
    0x6684492640010f880b5066142085c400405000105800d15a030307002c08550610b807443c85400c0c0c01c1d65040380541040000041000101800408040c4016006001c0410954010b01003403680c9100501034410082800b4861103040c826410a20488945007120036004d107012a126500c80c9848151880c0600000d041d44015801844191910314907180aa50142d080c10820010140e030070340d650210040014504403a030860304050040810160070854422007840f03200311499035980b400c48040703502c17106030a2100b10f10200e502034540704020800450384058040541002c091980d1040f0611072804a400760b00302d501118103040c480c0b580a1984401540c0c0d8680c0c5e1030f000107250810050a4480c002034144c000c0845405002c5859000c0c0d40c8030010314282483c01720b0310b80141100b01c50584600c480313221401400e0a00d803050138899486070b485191054883c2c00010914040002002a2944075803020030241e070710041030707c0344030b40d02030040b052203e100d089040c11401100c1c43c60ba00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 705085971 1250 705084721 705084733
    0x3020c0a0f031b02150306010509040f05151c020909031201090c090e040b07050c010b120604060b06070305040510030204090e070303020d0509010806100311070803010320010e010305040201020f 85
    0x8005040011079505406a510150801c2c5220b40c0b4003141241240001d60120a148011142c1950480070f554803c00c1410101d04003040307600480d081d03446200920f01c405540f04100b0250040d403104200462400751807142c11402c80340c0440e0342c085200b15000e885401008005040c2c41e01c10011940700c0e1203042c14100080d41d40701c0904000e480c0f88100034001c250321000101d42911409041b80c4505d800c80703510510380c1c6505e0000ea034558000000d1040700d5480c0d2140102c5521501800203030203441c18000c00440c9841d040036021603100004c002d1145004100c8000030070b074414280c6d010f5520484500495180700b0b18150024031130355000040e66401c0c8960203440800100301c0b102100c1c020b4013550306440246100b01c585104031a1090301156540300480c0c10f1b818035070a0ba0350900100d05002800d503560010040c0b094212982c2210080701c0040184200702c014003080003007a00811040c0008900240043c06105450b003810b0b04059403100000d0544e80b0810085881054400c00d8400d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 705087221 1250 705085971 705085973
    0x60f060711090f131103030c01091b150f0e0609090106030504032a030507052401031407030b060108040c030210020d11160302012d0903020f01090609090c03020c0a 72
    0x922045610501071140c0903500004030400d4080604601c144500100b132200c00d0060f64a0216501584000c10b8045c07106000114040e18240305a40805001d80f50702429684490300040c0340b66519081807003014841c950b1200c5503601301601030042c250506180070400222000b0400b1401000520350380655603100014506405034041030050317000b65520307110412020080c2038a1a0041240300000c2644036100d03010922840103441d640e0302c50029500718100208280300400b107810a00310f02402000d00420800c0300360364141c0b042000300e1015061052070740d182c51006100041c802d0707050219100c0003504010712400d05401556004081509034541558025501c0f5001600364011030515856181c001380d002442d85951039425401040e2581107a00440303030f860210000031501840803110380d058105100144108850399698028a680380d4010000d03030200c08140c040c18031002d20000c0c045175912261200640314a1007003c40c003005007001c02c400900c140424074640e8022000204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 705088471 1250 705087221 705087233
    0x140a0e150d0b01080c01030e0303160302160c0e0106020f0309060f1306030507110705091b0705010c0f080c121803040b03240907052a06040f0605011a040905060f0607 73
    0x43c2c1030384c0031082100ca070a02148010b4044401c0c0005800980d80180000b50441c000b0074000700d012204c0b40703405820152201600c17407c018041c07004651018640c3c4081c403d058800407458014001351004000c02495000c40070388a104056429000300000500c148080d0042c104462105401c0c3c48a03000c100c3c1c2e1448002c00412069407040009090398094200f145000a00001900d0009290a103181c881640760a5160704210303480d003040d60140206004110b0a1140100509690300c909004070041d68004100c64001040b002c43d00000784003850282054000c01d5501501e580041c000c81d0788440c1000e46103010320b6110810300b08001003040700c004a01f0014609084012118403610328047e0100562000100e0340d1760006602800382540403900380e204010710500140e800364000000c48211400e2004c101d805070348080c005e8512004004d528400d1500500c400b8040030710745d030034149014110307124520814102c65282c0d400f080c2c7c150344a4070f079502d103c00c00604d03c0e0b507110a10b241c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 705089721 1250 705088471 705088493
    0xc02150a0e030f010b0303030a0c09030c0b12070809061303030f0f0204211208150a090b1f0c030810260f030a0c060f060519050a140a0e150d 62
    0x498068024183c446540040501414003000710082c040d605580e214100ba0300205040600304c81000003100000012902c4014550081c0c0700211840e5503a011111070030805aa0150103001003041c0c40041010010b030104034640c01040f060907240400300e090070102c020b01401118803c90341c0c0740c90855900710109034020400c13030b5201541180f041c00171071100059001034140203410750340c907104c0525080b84211f00699021140310b140d490440030b1070012480c440e80f030341c0200040964911a449031032421000d007000c510110700310043e003029052402000d68483d0103004040c00034030404154464070060b00900601070411628488400300300260028000e940d950070458091034004c5c450040300402202e60261a03511015900540d981e20540200150b000c4005119a81d220104e401e90300c81481c0f921203200780ba84030268a0408042058240701d03540f0034010605014024002c0344c503a0180b000850302e80358040d88041e503c04003c800c2c3c0312049007490f81d00007510070207401080b90300d0b400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 705090971 1250 705089721 705089747
    0xb030c04090906290102060903070b16090f0909030e0d0201050a05280215070912150902150903070e060d060e0a140615010c05100509070e090a1403030c03070c02150a 73
    0x1f01c603455181e203035819440784601a0003514819410002a10110503c110a01c0b4401289045034400355200c840c000f40c01043d400c082c2c400303034440c02c420b414140d102a4035652814110f8541c4030f01840d56001034001e215003011341041c06008540c0c0c3c00c00304103c0f8230700440780c1c442000008210301c80410080d120313030000401e641170504000c0458243c81c81850070300c050342c42c1d44031a07200941d400d45410f00e8594241c20714001c5941c503800c0b01c00050710743c000796044005581c244140c0715042e6004050506a030751700300407042ca43c400b0810200303980d03017080c42c44402c0e0801070001b50f07c4c120302d440d54200752a0041c094480001c45040034540c413000180e140c480c075420f4841b40700000054004688040c10028042e042c0e6005410321245151759a000b40d0b04606075074212121156501c214505290084a00c240550801c0180c002407041451000c0800484d08e4043c4d891442c0c60030704658140000b40c200c1041040303201e00c41c400c6440c2c06a4103404890265030352501d950254000604195041031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 705092221 1250 705090971 705090973
    0x180311181006020d0f1403041401020a020714040b0906120c0312190309030c14100e1011090d1401060506030c0910050f0703030506040216030207030c0b030c04090906290102 76
    0x4135101426121304022540005c059680f180e1b074010f0700b800380b265500054025281c02c01c041c1444800300400b44010042962b05801410231246040c141e8010500100c020031b0140b0300b402d0741585650f60743c101071544080126240350016a83d04200c0749040c1c080c6108a415109205017481c601c8a4038010380f50a010701483c80b180200c40744812001d540360f080c0010081800050010006030b078000d01c4292850400301100c01e8440502040c009880380d80350f02c10f040b50487c00320311001c0e481600420240d0080e90000d24076002e280c5001c40c1540710547c0c800f03070014003020300c2005107480a40002c00100402017130581c407824501c6035841e195008600c0244100c1082d09034041e81c0d0301038029194000c115280c1c060514843c0d4605034040c24000b405254002d508010b00b0008081c3da044503030702c8500a9000340314480c150b14184590000a4204aa4800040c0100714605008d0800c56041d2101c0840102c0c103000c3c203141081c054a80d24244103882d403c1070410741950342c6410a425400341c401d038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 705093471 1250 705092221 705092233
    0xf1b050a0b2a1219090b0114040509070501020706050a02010e1006140307030305160302071503050115050309070501030b1314270705011b05010c0f0f18031118100602 73
    0x414005514482c3d00303003009490403500c0c0000c080c0011200184800d0b0000100890410095956480e03000026080355140862041d081900d905040c42120360100300301d0b004003007660070940040c0d035038580c80c480c1300108003000071002d80741c610170341198541001d040202c4015102c0703c8005806011580180c038540c05071072500103483c0c90f0000f40ba004680d050344a01d881e0071468140c1c00a10840035406074190301c949080054030784040d51001d080c80601c0d6800117040d5040608040030320403202c8503001000418401d01000e6440483d0130012600c0074280007070684025404640c0e034011500c0b40c0c20300203251035104000ca0384078005141c81918903004100041c0d0b000305984c4a010031801c0d000d081503012000a003c2c0f54010508071030307a600190184101324166584050030f5031503508000d8005000d0038044100307107030807800001c0b0b900e02d2418145d0026401c044c2d185607901c0d00344005050070007031500c014459110310300c2c20103d1701c00790140f1119070319205c0103010302c030b600512036040140b04c1c3d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 705094721 1250 705093471 705093541
    0x131a040c0e0a031103030405090a050411090405030409021b1b01030c09030309050f0f100c061a030d030f0e070608100b03010f0b0a140d05160f1b050a0b 67
    0x240c841501d104a000740146005030a6840c0c0c0c410f014145020365800d0f100400c0013180a40e00e001080384a4007102e40302007640d1529140101040c02c2c0c543c00d450180c02d244003800002140841642c05a8030004001600c40d075000808030a0380c8030802c011003c901035018034074041400c0032950710340400b0a0324203104074500550110340800c41440b01400295104005100a181c0503040340f400d650024116040004100c0c001a210405090b0341c102041d03541a16000300a003d010300310403114036150300c11b8038440502c0481e441e00c07592040c0303404040c0d45401040509809500c403110601c0d1280494100607180c15015180100594100f00383c0a40070400003216255002201d0580e18841715050100780340202094036900f12481200c00e210140320007003850700440005d0b29050540c80ea0100c0c3c10304080c6124140300c0311a9002c041041034148840001c15001003412403000100d42031011003044c82c0c1040c0e401e1850058000b407034001c040007802003441940caa04590500c41c0d141c1c40717500d4100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 705095971 1250 705094721 705094727
    0x12030903170a2c060d020d060b0d1802130e0703170c0f0715050a090915140d020a1a0c03030109021308160e0628080c010207050906060306131a040c 65
    0x10005110f042214052110980d500700440a807943c101055009802c2610300ca10180c04d88445411092003240c020840e800518210300500044544507110440f0005140d0080340c410091004581c0c0b005849000b081c040c00410010b000045800035800f0344241c551800b001c100e940b005c0001d000300d10442c5100d11054802062250454445c6801c1100720700b0500019070b0141c00c0014a01e051004170740e00015009520701680000542c280813894019003012800304800c030120000d00d005884c1c40b10b0500c0144c40c2d4110410503946e50481d10b00c482ca420f2400e020940c4589a501801804003000000d0445055005491000741018a0059050315800c810799244034141e10075810141081041002d1145140080d80105020b80703141c02080d1001c11240440034180e5015028900c00314042100c0d58003070003c086144001d01c054130b02c880c03401c0001117090802421403072058100002241032a507900103040f83c209851481844404040342020714815041d13240c0f00c0c06241001c1451001c2d030301c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 705097221 1250 705095971 705096017
    0x1090302031903060b1b190515070c03080103020f150f0d0509030a093f03200a020609030f0a0303050f0709150c0203030c0115170102120112030903170a 67
    0x261103403110700302203441012607031070200c01980d0701e03847c0544641c92090345903c1115201c0e850240c801803150005a4161421192004020104102e90340d81c032600040c1c2d10403582411280c046072086101e048040c00036206031803424086400440004d92420407007000750142070b07540d40c4d02a08111990752515926240e10511001d0000180080800d01c20488808000d618440005e2080342e014a00c19a0344005000c0800e007840e43c40070a6010002010760004074a0f9180e07510344400440c0200f03c008840ea94a072004001707105440c0814000e401f600c040050484211201080b01c880d6256410b0103801094180c81e01d241f200c49110018000d82d00442040007260004d00e1030100d41b134880241114242c41c40141240d00d03001c20004980c120200f4010b205205031044c0262152614241200825030507008424441d640184a101c0c10441c2004445044610804a0090000662808841c80d03110394100901c001c0c8030001c2c1d0002c0c54035440140070b001e03010740c4a10400907038020100c070180b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 705098471 1250 705097221 705097229
    0x905120d140106080c160606260d02010b0a030f0614040f060c08070806010f021f02041403070f0302010819050a0e0105060d0b16030908040e071202041d090c030109030203190306 78
    0x45c0800c030480144000e100d840c008940a10000074141c1d454141061000e00900c242c1600e110283c510900201070600201840740300e140020010001c008000c00e41c510381a100240c40c00000d900346009020083d005140424056541c140d403c0c5868500310103000901e4100b500c4d45840e000c2d265600ca4010030185020341000d0320381090b1540d5800044071203490031400d8600714010a941c8840031540300c09049104101c1c2980541c0b100d09001c140c0701d4002c003000f00b80740320303600121040008070084804c170b034182e0b0380a107004000b640e1a00107074800380d90403441484d4002c2c0f500c42045583c980c19403180402c00443d900074400b80e200c1c40301304001121849030203442e030b601c04804100f8400031f0461a804a000d20300f40402c1881840c0c481c0f80540d00664410a018106071040013405a030000304da2a04440b000d03000c5003420705100404441c64a402c3d090b44c105c04500d80801c0f800002081b400b000d0100040083c00031802d14a4001e407207400409d858858203458517002c900540c02402600152 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 705099721 1250 705098471 705098491
    0x90806010e16110a030f02281205041206020405010e010e03070b160c03120f0903080d0b0d051c0e040e0615210a0b010b0301180905120d14010608 64
    0x9407502e0502801a41046000710180460445840030250091016820107030190f10351a040f040a400c0180c00d110554032501240205c1c05000401a01c0c96006010310a402660b213610040c460541550039100e9900003002e40084180d08100308803081e0001c100f80d8800313036941c00e40030b500f03400152442c0501c0d2030301c1079061b081041d0920280041001070301d100a4480d65802c0e100c5030948920b40021400e40003600c000e86002103003001103400400d0202102d4a518201c00003034a0354807420001c0c0100240706424030b0302c41e805841d041d0b58200114080365041820ba41225103e48610110000094145008240414020b040c280303070610800050101d03000c040c21f5113507945250214001443e11829a1098040c408003943c2c01c1a28070307481c00310880320000d00e00500103040020b4600d40590142c101d403101000188060b266000031112400c64512001c5001c034120301d0050b040c0030603925500703a103a80115103452031100e00d07005032801101c80e00c08804140d03200c480880d8094000c0f5220146 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 705100971 1250 705099721 705099749
    0x90b04261908041514270a0b06030703020a061d0105040b04060819020a0503041e1101111e250e010b1602041d0c01030e102007030f09080601 62
    0x41d18041e200c0d10307501c00c2c45402000c0803208141310b440c00f140c410030001d007500400c0b9410048510040303501803c02440000c07403207184d1038911400690707070042200b000f0494800b140c08200326840c00c009803c051075006001c4a0229140e41c4028448692800c032150520443c0d03c0f50940b55014000300c5054440311030440c1d142034140002038507030000180c4500c580c076181456000303031024103102814007007480d0b43c0e803641c4d85d043c0790034103107410a8071007240080960410508400110841070b0814074010a0801030881e140a540260802031250000350484d144100d03020502c500c081107051904840418210144203003023a0703903510011078080d4114105240c1d005020100d441c03c0644a07084650000030300c140d07075650124095401c0240321208500c0a103400356000c40f8107024085110703000f8607041055045940c4225954503101c0002180180d480d1010b5841c01c0701a0100580d9451114000366a200c030384c500104010f43e800722031000210742c56400705031348602081d014121078400010401c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 705102221 1250 705100971 705101017
    0x40302030a11031e04030b10050306060108071716260c03090304030c08060a1a01081f0914100b0c071401090801090303050a050610020a1203090b0426 66
    0x1454000c100d42e915841c4428849840c0b10320710900a45410201c50b01c05a85503851840e01d000c2480303020300307002500c400a48082c80740703840000b00c2d41d03448002442e10b58400e4441c820181e41c01e10001f044d41444001040030400e03490b08400c00321200018981d28000d40c41ca4000110b1a188259660301481342d44840128540c03903d05005980c01015035400d6919240e42c0355a00040121683d00044240e008042000300d400395601c10b8100c1141120700d42c090415400000824601b4010a0440070b00c3c0346510901056080c40e44c03210280890120401030604210340c03004101c041100c10310301d100d450550105041c3e032040c0640d101041401c0007410742a05100e42c1e01070248250440c28104035641c034001440314424090144054001d880c00103940c14901401025a0001001180134503005608042220360000d1844002900000303107a40400c4c940748c0440151215000152012250b0700074801403000502001d01c5080e1400405a059200041380fa0030600900202c50200c060711000c420b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 705103471 1250 705102221 705102227
    0x411060f0414011b05010506100f080609040c090f14070c030801030b0601120204180e1b040905031b250e07030905010e030c010b0108090730060216050c09040302030a 73
    0xb08100c14104104030a440030071100c44080d01e02c6007901c1c0e6030346502c103000f054101019018000503480c81c01c208a40b0508001400e0800c0140c000c0e4004c90498001400344045902c0400c0a4201da00040c032601d10800c003d0310103808080702002120360407001050b4024050300000804642c19110007183d80c0c42c58072056800c400045c515414090070f044420101c05491000704040e002c442491000c05255400c1d0320112000c41c0344a0005501914041d65001c20104410032401c00c1140c01140001c1c603071030400d095018864003a40c0b2010380d4a075030880000b020414210707001085c0c8400c2e0081c10b00e060f0318400300949101d501490305030400410700e064429041030b00b4980c06000007048410652520034916808800d00d00f00d580d55941241d021136030721041311a000b169400c0144003143c20400d80c4103440d1300071004609d80d041610342c5451540911058840b4440d007001046460b00e800441d410b41e0400c914a00312454024518015441d24285040f240102d80550056040ca4981101a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 705104721 1250 705103471 705103499
    0x9070c050102090619020c09101403010e0111070b0c030f0f04140601061110050f130c12080d0b013603080412030f02070b070f030e12060411060f04 65
    0xd55003550200994400c5881e070f9402885009403070342507202501001c000003801c0000382200c080c441d98216040c080764802807c0c034002079440020a012038401280c00103401007140c6e034900482d80d402e001c0c0300e4503c1401c101c00352030480e000b00718402080d9500003002915200444036480440010310118a00d900c000d4800c540c8140310b00c261001001c51000c40318034106d801d0b440b1400050318043e0450203114140421120039440d420103103d00c1c1840910201d01c484010201c0d80007003484c540c4541030229040c8008003d10912211040b03c0f040ca00380442241d0251801e054120300b00200300305d5a5100d0b1503100f003107804010700030035400a14045151038818507400c0111201c0c0390540803010030f01d107100920040400080c04007105140d80780103005004d100c00c5850540d00024800c110000c14001200c02c1158400000b0300300c10741d18079042c3d650039444c442a03504211100c00300203002c0700c0040e0079400745004d20b49590020301c10008000c914450044c10044200042c482001740488a00c1c0e8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 705105971 1250 705104721 705104723
    0xe0d020307060c0e0916020c010504050a12031412010602011a09061302041a09040e0d02070e09070b1c0e060c0f0d02070f0b0f060a03171309060810140609070c 70
    0x10f00d035040700e483c009940004165406d01071100540842d2814a40410218544242c2828102d00b8a460040080d41e171000a100d5020002419001503040600c144100c11003074008070f41107038840078030710031029821070240608000b40d031078030794090100500601a80030050000b006042195151000c1c0680300c030144540c5204950288408100e0107617404050810200d0344207080c0c0c9410300103041109480d1442d02011058004034084941503901150300e40c1030f074040414144003902e0700391029242c0211988104945100801e50780c009034502804891024030312407041c8514050654401d4039038105890070300055070104419140824200c02a28013864030600c014180a100d0b210034050301090300c4101c414240410800c403d9000b00228142c02c0041520400041820b55543c0e0700c071008480c640308a81c0d8004149040c0034001c1c4e0580c070001e0060424248401c50707407044030303a95556881350400c82050810307005c186082c1c0b42c030003409e108a20007030482c0d48645510b0f0040d00d1000d00c01038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 705107221 1250 705105971 705105977
    0x8120306010e1311091903050706050f07050a120f02010b010e010c050a0c270908030a0f1d0d0215090d0309170c0a060b01030b0315130b04060b040e0d020307060c 71
    0x1000081d00c3c10910030380d010325000311586039440c09020300700514500f4103034004540c0840a0820b0021507030001d03c044c1a2840380c10415500c440c2501009e00380c1c003440d203000b4507a114007058042002680f01c126a04880c25444103400003200341c00580c203899000d0046800903041da17400d03425561107511a0001c090107603090310880401e5840343c0c1c034098160b0704441c3c003a4620302c801040d2484800e003105d656403803600082100d0f81d665651445140b00282c204001903444100f40c000c901c0e0740350702030a07101c0c0300044650788500c0c01c01c01c03554030303400c9107012070015000e035440005122a640c3c0c83d5510402c0303050040e04042043e808190014809610b042e00e02c03030b92044880b00014000d000502071031f03200754010080401a464104280e4001c041d14904241c108580e1403425200024034500d10101180b070901203649010805980c0c068041004c1c1210705c055060005108a0358000210003105503800c0c44000380c510001d5585000d50b081081c01039008210034070201d469544a0780c01000e96207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 705108471 1250 705107221 705107239
    0x916050d060e0a020304050706090609050d08190e01020708010b01080f15150d0c051810050c010c1d0105040e01060324090b0a0512030a200d02060f0108120306010e 72
    0x501000360003041100c3d0050455400800e0005110013000164000c102034036041805a084c428000c005105a210342402500d8803e2200c2c2080806e60680c1c0c400b601c915601044480c0e18100184103040c000a886d02601aa282c0800c4001041c02264010380042e141c4558070740b10042180004d4078000c0030843c85800b144104012a694586070740100d0048a48461700d80002001210881d522070340d640c014172108202d80c2558450040c2d034114000d030110f03142640c0110314182078907507106105d002c0c25203510344800c40d01015088001100414400040c6412a09200c00152480d00c43d50041d420845854030040010510075000548100491135400070001c0300d2200301300024101e034020815030f540f603100c19000741c2481c10100c402094100d41c1984002c031035036510340e02d81c810540940301700300c696150301c04c0d41e204c1c0c401d075010000302e0001120010002c1e010000e40b5490182d07090251060300e0400003c082100183c01c21100c08170702080e9146450f1f4000650f009002514401d410021139 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 705109721 1250 705108471 705108479
    0x90d050708120703110105070f0f0e060a170105030d0c380a0c020615010f17042102010e031603020a0c08160b0f03010902072607110916050d06 63
    0x7441a02c50991503025070301c0d251400307403030b000c0d000c00400604c0601d01d82c035003000c0114069010000d03c2c04150705080c4240200b221034000c80d440941d12110715080781d40040e040e40b0450b0b1085042041940c40400d50403980d032900201074803000002644030001d2109111072010420600101e00608940a41c01d8481c85120101034032094001c580618003007a120200450310045000d90480050701d88080c251519001c48001090380754040c1280c104018100c0c84a02c041c0181609007401c050206851024502464107110031584554200c0284414051402000b0700502441d004024030001035410420803021030150741754008801c0d41117125504c004804138a1002c0e042c0c01a140c2c0c10041c1020064102c40f0700030078212980294100c00b41041090300c585265001c4d641941c101810160f82c3e1100d50801651001c81e032156800030136115040000200d009400502d0b0b96445090040c081c4146002005a280011100503601e2020f49544440c0a4442c000500303001c4040300000503880c1d00d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 705110971 1250 705109721 705109723
    0x30c0601080d260a0e03040e04060209030706050304171c050403090806090c0d141608030909060105040b0d050415020a1d040905071a04050d0302160b0c03090d050708 73
    0x70390040155410a401c1c4000e0b9960068088010003014050a9020f40495007107481c0000300602c8184507a988801c1304180400a0080b60000c10f03841c528441642842d007483c1d8025401103140901c00e00c5a100006080e90007001682d12840d00721010300c1910360f4a58615110782c1c0a1740c1c41103010b1803a010701022701c0882d446041d000d030b0b0290b60b500040302c0c14818128a8040041d00085142d44407141c1c03aa13980c0c4d600c502e00034003641d201021040c1e502501525070f03d0300c5070000c144801c2c0b085010010451000000103003010400c21640014661079900043d10b540c801c90244410260b020400900380403c903402c55030f0810302c201c030030b100040c0030803a006080341c0103000c1200001d5400c41c14070704603052041a40c41d09841c111010000d40441fa65916a601130a201e00d090703850044520503014001403042d94001d250140604040b1121440c009480707085c211800d00d000b118041c0b012403003a11600c1695000d18400c402103141c446623004201c3d800c550b001c0308540522070316201042c0284 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 705112221 1250 705110971 705110983
    0x203031519120c140607020d020a050d152906090102100f020405040f0c050304200301020a0e190b09010518031009021e090c07061b050d0c03021801080603030c 70
    0xc40080614042e001c03072812080f032102d60340c8101c401c0025200e02c269140d542400311005198100e540c0c3d40c12174801e10200d0722402e00365200d0b80d804070016003c041402080f20314070107002032485040141c0034000341c0025030b45121845020b20044050003050082c01d04000400c00d041c41401254450131000c1500410b50f041180c0d17942e8801c4c0c01040401180c20070f8011020341c8491031105111042c2c2c401c100520714000140041c01801203545643c840c2c0c0b0003900042d010003c050700039036440584810107028035a4180c00c04d0b0088044941c000840000c4402c04801d50365424081850450104011540ea0b00312042681548080c06402c40c500d9504208110042d1900c681c00306420303c45004009020702d5440d83c8042c450303031800d00c8581e19610b00e0340d6190300c504000019512603032a4208030000b4500e00070710036800d030581204c10758a2034200000e0161415118018014000c00380c00440c00ea005000d8211965004910500b41d950300030700141c0d5000d440030782184d04003681001c84a150038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 705113471 1250 705112221 705112229
    0x905040314180d1407050102060c030610090e090a020f01082e08030c0d0315030b06010f050708070c0305070b25050c090103030914150304030309111e1f0203031519 72
    0x70304c101c1a248200b5005114220040c03000f40082d0490f07182c40c0350f0003800d0f0300c801000300d07200391403411020a182e4040c0300440c015000f00681a611450050161342e6680c482e000c0583c402d180d00881c1d42e510351b100b1501300c1d1058400790714000c042d4807400d414000f0074140052440164043c0c000215120000b00041c201c10641c440007404142b641c480041d0803904214200051a20139135000d00110f11228003d030b030071400c00c1c07809441032a42203e04a4840c01801001040c600000500e0b00c1401007109000c800d803030064003910842d903550300310041244651080b00310f50392005000d03031a402c1e0711410120151401030301540d4290103900c0c00210401c0c802d800031408184029400d000e48041300318050b000d1641a1510780444201c160802c1007404010030040c101601c2e2030b01141000b10034031500c0400a4050f025209030400c8605100070800c011034420701a8002d00c13480c40141c034903d031915040050302d402a503c0d640703076241210404890040c0f161342180355924519007160700001c1410040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 705114721 1250 705113471 705113483
    0x10311040b032517060a0e07030210050913020714151501030911030105010b0c160e01090c120501090606031103060114130305060109090501150513020d0605040e160905040314180d 79
    0x5d440d000e00700b801140c41039201d049103039002c0d005c18801600c2d003a034400d4401d107d6007007841c0c480091f48001007101d0326002c5001d00031400801c803a002c01a102c04c00503000c01e0008213459031004500c46405030103004440c079160410300702c103001c04254040e81c0303d80090750081101b00c1c0119210f4010a0030340f0000e90084060031400541c051020000380510a0304030034015004002c2440c1c203c504035070b40d2060140710b01c0310740e98040501540c0d0184502c00e8601980c0031040c4100d44c0c4d2291000014042803068901003820020b03041c499108031000c891003040c0503100c0d40c161801c8900112000d800212901070f5040e0350300c80106c04903604015060013031500e401c021407000000c2c40e150f82580c0b042c03440c0340d8602d42c045005000940d1001c0803421005054000184c44a860048000240c1000e900194210b4541020440e02c4c4101094810301030409854403007000d030340c401a4400b11082110080c000a445e528031901c5215084001c05400704240141880c0b200c00c900019000c40d44d0910841e00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 705115971 1250 705114721 705114733
    0xa02070302270702061b031312051e040302031c1116240915140705030d05010b07150506060c0f1005010902040e060616150203010311040b032517 64
    0x2038001c0040c03203e41c0100b80344061703e454200060409044c000e50840140c4075100800001c3c4180484498581c01d075420505210000d114040c2c050401d030301c01c820b45a00340c0f140d070140c0d9050f500400d0480302200e601900800386910780d100c204d03154001d007030044020400c003000c400c0c6c03c144040080e58401001c100c0f42800440c0340511200e4244281d038a0b1002c8041c0080c040d240440c3c00c80c0400f412500f165004103001c1d02c0610040b0344e407400002c1c0300d401090300821800244100000504030f0b83d80110010031060340c0761300703100c0720341c1c010104001c0602c00c6d0a141d60500d25015001560440b01c0605200d0601d40821022810644205240801c503030026a1580b64001203008441c018a014041180fa2500345040c3c031080c1c80d4001c0110b40294400240c1c03000b49880d8101000710700340c03c01d43c80f01d6800d11640009010758820712058840307801e049959030007840d1504c074102c506c4400030000c14041e1030f0310800030114010070028021000d41c0ca040016900742d130b2600d06807144501030207000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 705117221 1250 705115971 705116029
    0x3050330040b100509040510110904020a1211070b0a090602040f030b1b0a020c15070b070903030201060914400501060906030203070506071704060914010e150a02070302 74
    0x1401c03103903a0380070f80c0c0300b605172901340808968046141040c1c400e200c1c40101396002d101003802c0141c450030080a40051000401035011540071035010100d10816130280034041c40042004140d0041e108040c00c00242c00001c41c2c044011a409000c0c0d141c403407107002d41482c0d61042c0d1074240188582c03081d03840f22281c20400102503403230500c50005403201d100160801300c40000084d6a103071405c51403030054041001e5040340c8090a0151501c41c0e900080150891600707680045c4180002d105c102c0140d801c06201245001013400380e580705030078010f410b902075036604007070240040f44580da05c00320000c8080c1d40c0d241103017500000700040c0100d40b100300083c0110700d062403c480c826441020701501e010300910060f60003080b01011107508131086a242c42c0300742000d41c100170a18804902990700064000b0b01103800401c2d0a00301c40380c3c0c0c0c0c0c4419071800344c0001941c48400310a40f8942c04a041c94212184031003940103007410b0402d920440302e03031507200c0e0b0100317180c0304160f0910882006a202641 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 705118471 1250 705117221 705117241
    0x180c03011103060316140402181e0a0f03030e0114161b0e040215250b06280603020a020f070b1b0f030a0e040b1c0606060903050330040b 60
    0x41d20400c1d44450300302d00c06d00d4000d010440074607101c0c819200d030360009815034907075100b0b030044142080000c040d82c80d008210a61100c1042040d005207006401c0070600180950801d54007404981d00750304e07241c0c080c542c043d00441311181c148021070745081c0240070054244000d01c510400e0356103d15200c0407141e42201d45c1e0814208503501c8044181d41010412005032529001422100d41041c0f40d02d40316418100d02c1040d404640d0310300c0f0304110f0050074030018425401c412500449058402400d0075002007580c03e0b01c000746150300412001441780c00c22980e0310a034004c11600c956441a00c541c581224456814a9041ea00501c5081c3c0c010407440b143c0c19821801781e01c0c00712604000c20301c82076a02c103066164001c1c0341605050101007024404141c035280c00404003803100505030300d003c14500400c1c0080111012003034980603d40b80003c200d181c0034a540200b50780e0418002d5040181003416044c0f1500340403170244040d03010003043c846810715002002d0243c0d00c546030300c1c00f003864990b80c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 705119721 1250 705118471 705118483
    0x30f070305062206091a0d060203070915080714160311010609020d05100501030b100309080d241418090c0405010803040611030909010b3603010b030d0503180c030111030603 76
    0x40019450703040f8980c0b490347c1c0307451207010b03091703800703500580c480c0e40f2640e0545080d04641d01414102400080600d0340039803080e0028070a50080e2940a14441084d0b0601000c1c06000c03906007002403407400040110780504501400c8000c6032001141c030984441c21441030741c0060300c550b405141c543d414094120704620011016020a2804000032450440060860b480d20b4140c0b00c107156443d84940180000181100d400b826480801d000215165850714010f602e08651810200302888010451090b1180000d03244400144180d100c080004000c01280c1d1014100c1120381c41880b180700415262401810700800c5020091901c40d490800003500c2e8107800b0104180e2900304101440c02d5903140c0e4a01c506541e0744c5525181c6621515080e00c1a24140403c00444201482d0300ca00000c050841081c1c02094241c0082c0f02d0032504500381a80c6407200070300c0401051007440003a081000740d80c0120700340680003049894040385440070a003146c0800e40707400074800b03001007040f003281410810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 705120971 1250 705119721 705119741
    0xc062001051005060304061407050315030c01050406050d09050105090610080f0a0f050a060f0b1003060308030a022d18030d02070e07031d150c030f07030506220609 72
    0x9001d0362415807900d5a0210090042074440d04001c0042410311801c4d600c0401d4151003141c42c4409400c1810025040d80c2003103803c1c04c203180b4199807440003401c001c50301c03002c0c00304107841e01420541000c00c20303605a0040c801c4405015540c1d452100860024081c160103020460080c05480c1841100740741c00414a4103c184a0f81c031410009008010006100117050340041c07162800d0492450010b0078103401c4400500b100d400c01581441c20005a441942002c40460380680050320005080d800e0310428440945070394400d0001035040d0800782c0090036401c0d0703001c4400d000d188083c640111035078a101c1c0b24101e01940442d0b210a0001384041018450008800820b21280b0740c00c80255202c04074042c0b1070402d04203001080250f40281c222500900d40360748944000d0900c50071045d81c8079501041064801c000c00c000c6020001c210741140d0044807404240e110507514002d040c0d01501c801360603241c110003444020280300a040c5c000c80c5003404400d00110300107107026070380c81c19504d800074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 705122221 1250 705120971 705120973
    0x131b050a0206073606030c110c040e0c09040803060316031101200706050702100c020108130503090405090c090106110a1403040f030b01150503060a050112090c0620 72
    0x400c000c0290002260740d4030446a1801d002803503043c030000c618030200d040e00008018141e03c131100424600b1600c11041c0c45043e5020042202c43d10400c407681c154180040c001c6420822101c1e02505041e000340400070820780481e07001e0240100811006030781100d09aa1100011090041702d1406101c000e40459954440c0100c003400e41d210b0b840c1440c107c4030b089061000c4045940f0514040601041c09402e85900760b542081d940e0b04050000d42c0211812031040d11000240300d030140c040c4000110098041e03480140d80c0e80e61046115a03200842d2003500c0610042c03040b45d0480d42c880c0a00b511580e000d0003d000408404400d000040c0300c1a0084010322600070084c036411540014003040607030b080510401280340c60007041e415803281d41c0105102c10301904010007031000c6000668101c5030b140c1c4c07071800800c29a65044455000c00e03140c460f0300290801d01048150b10490603800c008500800004d1800581c0e03a520700640c01503440303400411601000140000c2841403507807070140d80e40c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 705123471 1250 705122221 705122227
    0x6080a1401060f020106051c140f0a1514040614160503063a03020d050702010e0d060209130f0b061c2003010f1422020d0902131b05 58
    0x40d0300300300000014080c00e42000311500007a203070940f00350001b10042102a004501880800c10104042d04d01100142ca20300c54480ca24850f40c2030028002c07240c0c01590000d0402c009069403046402c2c5400e0a0320180c0d01c1d210700c064401402c074000d0380d81c00b407407155000242403007000b0180c16540000900300c1007404d100700c00d07588815030010210783c0e018400f10f03801d1654075100e2a0703262100d100140c01821901c00d2141000c4640000420f44162034000e4003111000749070440121807d210311a8002d00081a020240e891400c0404806810b2442030704050b0900fa089004a4440c410a04010b090303251101c0c0f030104a88028443d00a10b000b040d10001d1030080320b0100c1d0203002c00303607040c40f81070780c3e0f40c0303041660b8440d407a40808aa031840f4014036030342d00c2d6542d0b42c00408089040c06941d40d4811120682500351511030305401c1c0c82c036050000c1070342002c84501c01d00001d40040310052000303030301c0700710000044e0b0b15107482094801c01e102e0000354a409244031058001080380780041801020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 705124721 1250 705123471 705123491
    0x3c030702060105010513090204080a0615080c0d03030f0504030c03030c0c08040509040c0305120408060c03040201080a0b120f100501060908060112050a2f01031104060804021f020706080a 82
    0x3007000c034107442c001e08110341d507002d583c00280d164840c181e1104000302d2020902003034102c000304400c0c0303109004500030310042c19807030303060f030039201d401c5c822840258450140003016041414103d4000c038042e040c001500c01d0701c850210141c85040310202d00080760000c94a0405030580700310341c030325036103840d02e01160001c60303440314400e00c6940920b41c82030705603600180c1004003200c56070001e582c0c00300c159241d13200d0030000780c86c4641150180031449e0103410009000020721400341c170321441e0140d495a80380d494268400300107149524010742c0003001c0e204106407260b4100414204e00784001c000301007001ca03d0500f0000c0700d0301171700204d003008408076041029070400078025040d22500000320004105516029180504031400100000107040506046501652400207072918240210015450300340c0110200e40c030884032007201540610041c82114405c0302190790007407010340000d40704120700620f4071100400026075001640941c00034448290f21084154000508c500140040069 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 705125971 1250 705124721 705124723
    0x91207060c020103020f0702030d05040e06040516030509160b1209060402030a0b151815041b1107080717100b01022a09091b0609030c010807053c030702 67
    0x34075400b030704040e0040391040313a00090b403086800c5264000d080340c4426800341e0002c0c0854026118040d1010b070038100160050400f8009c1610803c0e07031a86005010310009d1040d4000c100282083d0303c01d105540301d50200c000c00890000140610320421070b03c0301c020100c40c184000e401412030000783c100744144401600d000a48121103a4004800b440c159969198818600a02c1400c1584400e100a1180e0a182042e81c03580c080d0002600510300000140b00780700580e035000783e10f414503030150881d001906104241030034550b050707441901c06040e500c40807503203406060f030000c441c040d240b0b0300d5030000020104403a1520300c001030f0301402603558103000070b51507260b0443c0040c0c100700400c102800401c88125000c07181c40c4010950301c1700303080422071541c1c0c034400c00302034411540c550310003038051780740000070380e045004024000c2124410501c011565148090f00e40780a100080c0a41c4001e440c011000e0001d45481075842d190368044281083c05480d903c9003a421130030b50402c18440c0180d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 705127221 1250 705125971 705125987
    0x909190c1e0c0305160c03060e06061f030f050405030c250905071e080a05070c0807080708090612040c090603081b030d02040305161706010303030b01022109120706 72
    0x42c140342984060504003a20b41d84990f00d48502c5404100000301c1c101b010745803505d4181d80c050341d020012005601c034a55035038001a160150f0148100d074140130410f039910f152703505401c0175260220300400e0702c2c03d5543c142c42c801e440031070b4a42c00100d2084882c000402040700c05150141d180040780d20340210b120000200c0340034100e541c07510380001442c82030040403c001c0105801c4244a0f141202c1c01c07005001e008152000c46a090600c404100c8580c42031b00c03162a02d942000c00d41c5d01c0c0861955a920650f400b0800885600c6400c0c01380323010940e20350b000f620705034800c80301b03c040e14642454080384a03c515045000c4441c0b6000c001c1c00481d08107410b591107480480720522000d10b07050001c600d94096482002c8003107000080c04400c000c0040781c030140784017a0383c002c41c0700e0680320464550304410703034124024aa03103c5070040001c1380c801e0300150444070041c0141c40c0801010800284204811001c107402007a002900c900d46061001e003119a1155180140c40c52600b07001008010711 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 705128471 1250 705127221 705127277
    0xb0a0b04063206070605100e0105010f080a0908030f0f0601020d080f18160602070b0703020c091e0112030206151c0c0b0d0510170a02040905030909190c 67
    0x2d1888010300e0802c5162502c40000da0030024096501d5085500d01107015040031542c110081d0301011000603d80100039040b8140c490503140d40400e42070080040f03451010007003080c41c14607101c0b800d260128104100071401411105200c0815144c4100e03440c00d00400030b040d403030466001e02c140d90022940b0140303080c3c01100e83c2c18035200e42c0c0c5441c11030440f100740c1314141c0c45080c000e40c010f1091501e61040050b00b21103c5800f65100b6907616410680719004020380600035030052001e4910314504070340314641c058059029108402030980ca0099262800d81041d4071800b8201d40d641d09142d0100078007588003070002214407140c4c541001080b00704801240780003005080418000030800c980440002400044800a85031024880e08401500040c1d903100e08581041801087c0d001e18800b1489200c403d0500030103d94600368240001445950420388003400240000d0b60a0764805000c01d0140c02c822a2080c684c004549a000c103e030000c0c1100401d0110145a03600041c091140164180f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 705129721 1250 705128471 705128519
    0x21b0307110d2105090109080c1809160828050a02120f06090106050f030319050d0204030b0a0b21120a02070314071d0105030a140f0102070b0a0b0406 66
    0x8107145807409442d51010485521203c0020a00b01c0980e0300002418000b14240d0b190002c403903440c0d808946070b14081c1c0400b900400e11103980c40038030035104182da810501640c200c03560340c140245a00c524140e0307604108546d42040304d050244012000703086500301c0c0780240c43c1c0c800740c1c881d5903925918212200700902524800c80d900c0305008040c0002c008407080702d0306958203880e025145034001d0840c1c0c005c941c4101402100c00b2140d040c00401e4a424001100340680b00600c5c00e00d040d01d03250001152612925001c10010000404001038280a10000e05000c01c08401c0078040040040320200100d03920741c800071a501c000080058180c0103480c1c0910712a590b505e03005412401c021098001070104101400240301c00100001c004003211115000000780a0a590800384072002c2807040a0340342c3c3c4448601303804141d2110307190540580320b000300c40c03400f0a20071a0341e00307a030441181a0303420000081084031046480c02441c4200d070003114100710427410100003401032031341c120101e098 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 705130971 1250 705129721 705129739
    0x311180d03051c02070b01080309101404090c030c02010b06091e0a0305070303050c1605010c1b030510090606140a180e0625180504090c05060301060201021b030711 72
    0x703141c0140b0865905003d9001da004402c481d24520501030741c40650100c0b1546101d400014000340c0c0401a03840c50b050061014110044c00c2c03030212181c028a101035a500d0038104030000700100c182c410380b01a40d0450701d0100d0740c0c10701080043c0c2102c001c110002c4c02490104124401d0713036102a802c3c0e03101c0c0503841400b12040008400715071110845c1c1c01c020464492001c0200034150003402503d029415001164848078110501c1020841984100c0d4003103000303030940310006a11f0b07030000344824444103d078003101552510350030300d001da001e010031169554840224007404243c7c02110042c10f000d041e0860341c10a880003207000596144109103c030500d203148500349090766003000c10000c0588080764090f0500350b410030340c050301c06200281c0c4000c1c00305d15040158040c40c488401520b44240c01d0042038640f17014000038000f010000c441000988c0c4c80404e4959840c0080d40c0642195400141c0f01c941c0c06e00c2074134070310040480c20300b01c5d80d03c103203d10b1000424400700300c1100d032029070f21121 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 705132221 1250 705130971 705130973
    0x2f0c0906090a0f02070c0803030907091a064009050906070e010c0602030c090405151e0a0504050c0c2512030909020724021204110a05090406020304030311180d 70
    0x10085c010700d400101003c651202c001340b01c51307000010398040c0900000ba62070710fa82d141449001c461600040346481c0490b01c030340c48814903040016082040030710018008401818910b00e45107030041d02601c0c00030300c0c041540100441c001003010043d1007020420450b40c10b101c10820780c1c850b40100040c0070401210030102040e4030440940700304981c0010301355181c0c20414080e00360b41d088055980e0240e482d100c002513404280c20a140c40000740500240300d00d4002c0508207044440309110b25401010503080000c1503280d51040038032481028004a444440b1042c1d09401c3c544403860b46100004001e00f4109159100d0061300122503a094500311040d84500d81a116003820754801c00040d40b000c24080280a9941d480e18001042072941c2040c0940143c0c0b0b1504038002c40220b880c0b400b440800290008107484c3c00c456500c0d1005000e56a21a50340780010700d000c008550880d000d40d004803e000405d601402080035982c1040d060504105c184100c0702640602c05084903c03601d40410303004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 705133471 1250 705132221 705132251
    0x402010203120702010209040b060423060c150103020306161e0c12020c04110301061b020303070b070c061812081b03010b07030207051806102f0c0906090a 68
    0x14040b40c1240c8521280c0e10707280102070b0003500303c6940980528100288002903290007000ca03420359092005c1046141c240d011207910f85d0f1a441019070b040340c000c2010701c006020402c6540c405480b003008942656041d48181030070240040d19800c800e41041510608060b0400c0d03407a0004031103508440d0450221386c0741103448102002d0003414002c03e8001104100d0350108110111100c181c60a0250401c04d801c041400d01c003d20804c1e00042d00425941611180395000002d02800241203c0c02d0210a0301c40400c81d660a591604c0800c1c000080301c01004214010485285400c400d281d40800040e250521070701003200c400d1080200300d9001500c0c00304140c00301d00104150b50581d54496071a0464040981d1000c58142c001d0310441d880040c01d841c0483e025168410b411940d494591240c00071b11070800a105403110920480c8507003000340c0d4007900344e6420945a6124030110070501420028140984481102d00420094003040f000e91510001c00b40c0000c0203035030004514091401e04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 705134721 1250 705133471 705133477
    0x414010f020c0a0e061008010e060f06040504060602060103030810030209010303110109061505030f0c1e150a0302070b011403060f070c0209010f0608071d090a39020a0203030904050402010203 84
    0x5140c0c0044050340110b12a54150070191040c4016074100e40c0b08441d0850941f02c07124244200b50041030000005401800d00001c11040300c0c01c0034040700d08264840f00002c0641c2c40c242c00036001644800010000d00d54424902a007204010201c5160541542c0206138000c01c14000078040c840c0c96142d002500300c3c2540b0500603107030028030401000702916000c041140031791003001c0c840d1080088141e022600407a50350700c45d55000b400c0b2440404502d5501d40c44240311024070f5072080c1015000f1404d8441c28009100c003a07850342c5c2c0165514400d01d4030403403401d010381080328901d4000203d80d0701d6440008102d81c0064401c055071156070b41e198002c40c0c1e0040d540000a410800e818000980c41c104441d52341c0c04e40340b494444888980e6042d0301221307142d88000c114601c0200341aa0903880c2e0500c0007200d9003207103e149020509440b982599424040d414403d01014122442c08201031800350030045e8201c0b03400e102038120080307207400103541da01452007000e00c603d03a2240440c00b1a80200b040b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 705135971 1250 705134721 705134743
    0x90e011a04031b230102070302090402030111040905061c1a22062f070f1b06120b10050d051509071101060602030703050d150f080307020f04020414010f02 68
    0x8440c80003c4411000c82d00202511a03503040e00d0b03840e1484249060400c0c00030024180690003030020034a50f808000154001400903030b05956a51182d03440c004550000700301030700d4201c3c40810703541000800c2c40300403858203c0700c442c400c0381501d420300010511a0a140003504000c02160103441d00300d40e004c2c104a00e4180103d11541d09200001000800d070009258a03444041d04004103c1c120080140c0914621840c440b548003000410001503020302c0080c49540101c0140800700010207e2210740c10712034100d140440e0030200704401e6060b41e4001d84c2440e00d015261030407400c8441c24050400d006800c0b064500c10345410024241c410946040c4181090046c001c003003600740301d000034100030700031580c2c0203595090080101c1e81d0383c000012540c00e154190340d8145840711000300b410062100504045003403039817440c002101c0c003909942001900c00c01010f50340d902590f00c1040081c0505509450003a13006000030015902401100340e0f4114080c2840307034210700c042c0001ca0400d011603013 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 705137221 1250 705135971 705135983
    0x804150e060d06030204050a110708030a0f1401030b071107090c0c0503070605040c0b0708030c0706090f0308070906030e030a260f010501030f152702030108030910090e011a0403 78
    0x816080c07090305600f108003228000e590400040d182d140f8640255480403c40403508103080111000180702d0200440e1b10207840000000c0741118404054107986040c52948543c0340e9000060041c000d0300e414558101c001410f01510050016a500751144003e1041c0e900f40d50f60384003880c3e50306015142c5071801a80c03110640e9690215407074a50700404042c0c8003603079142c1c8480ca0201c6c0c05000c107422581c450342c00c20b0045045a8070300804014641c00340d0340403a0107584809903800059142542e412030f01d0710030707260f00342c091414100080c101c80441c0e01a008140c28a28110350382d507004811a0740d1808a0325280010217100c007403103180d01040717000480044d016007003001541060845070700d069031000d030f03404d1003100517101c40038045d508101500ca0107059000800c10011419009003c1c0b2007a4000c4410000c84806044c8422604240d1145005800020302d0712440d10b000010684100480d050840d01e50b800e241802c0c200040c140903105040c0300312000c20103c49400010790303000b198004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 705138471 1250 705137221 705137227
    0xa0803010b18011706060d090203060a0b09061009260d170105061c09060b0d060f0e070e01030b2703070c0906080d120b0628020a0804150e06 62
    0x403103002902d501080c02c144401000b88040403403036202d83d1901c5100c2240c2131040c0d99680f03031a005c0100c654030201d800c2c1c0703034659110003800058505008182c85899821800038106800e401840380401c00201a180700c0c1111545d00e40c0d81ea90046c0c8280c00791402811920001e1418011f43c0d2050240c00f80c040a66229526007003000a03845500d0b0040d095074003803207540341e036a0380043c44414041c02104460010001828580c9580c2d070760310400d440c80c0101d0001c01d6040c2c1000115850566154055840d00d485480000d12001180543c070b0400c000720300101281c0d498801080d04042c0d060200810842101000c980004a10408454105849421581e110b207840410607035940c450a803c503030501050038001800900b612480c0101d40045000e80000881d249045950402c00c44a041e10265a225040e01d15141c00025080040e1008a40810b101c1d00024159521800155450441d07001414080c0010a090295011540c8561165070b0224115030141c0f0304120341400660410004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 705139721 1250 705138471 705138479
    0x3030513032a0602011e0e120a0e0306062b051c110d0c02280902030c13120206121528060201150506090d0c15120507200a080301 57
    0x311040310401510065010998419084e82640c000c4048141d013031860f20b201040548454000c5209481c194080d1118542c00c0049007020743c1100b10b1850014018007e21011820100119608610202c1d050381104c075000080c28021061030115410b80e107200c1811034108002040320007220710110cc496200300409101c014104002c0d58140c11030781c0b0034910303882c25a41c011401e54401e0754000d440c0480f03440001001c041d2214840300001286041c4aa0006110b83c10384050745c00b0b22502242a82d032060154031034524a0160b070428291010094031640c01030780d41d00f0803512605005422031400342c0d50202400207043d804e0700819002040f052040301c0c08100250324002d0315805c40440700447d60bc2e104101e080f0389008072090034501580d5402c4c0f0140c0b9181001c1e181c03081005103c0130036549a40d40c3c2c0d1482269551001041141c24904094145e8108810450903040804101300503e00514010643c0b02055448a011182048440c005200030b01c041d0705059044101181e8030350f52 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 705140971 1250 705139721 705139763
    0x3040305061501031814030f030c0409050606030712050a11160507140310020d181a010e060603040314160c03050c090f01090b01020a0606030308070e03010b01090303051303 76
    0x1c2112409060404410310082643c000d10910510840b082c0f0414202c1c0916a1074619007070100d010000c05100030b011000c403000041000318460245108400d85482c83c214102c070a0b50030180031a40b04900074801c100001d03600611034140341c100e1082c04a1680c448040d8980103002c0ca0762440e8142d600007070042600640c0f03c20403ca06442001111030859540c90313224050140301848981c150420119042e00705440d401414103481e80d81d00015000746c140a0011540c80000d401701e6034803200c0350001c006e2030300300340d80140144045506400303285810780024881d0310000340000e043c0880f414601e00b0102810041e200c0041070b403662040810b00d01d0501c2c416502c0d951008481d20b01c65810380b480c05062284895004004810200c1401d03406e05410384081c04445184604510407145200c003c0342a078007030b080040d802034403000e00500f88068024049000310000600980c140100b104181e60b02c08060001c8980500c0d205480360101312a030b0b17581c041d140c0e10140201015080590800e45 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 705142221 1250 705140971 705140983
    0xa0329010b181c0320010605060d05090c03070305100c03050105011e140f071e0b040201200d1e020d080a090f060207060b030f0609120313121805060309100b1203040305 74
    0x40a510001114600c0303218103402e031f540798042c1d02d410071020300070b20601d41c1e0590009500100450705a0741c3c000308580210703107040c04075801950241e00070010009480c1d880c0c85803107036032101d501d000d01581d0306010010303001d07003402d070080c003503110301400c01480843c0f0842e041e00541460349600c3c1da1f04d1102c40d0003a80390f03410045054032058080090144068018a9041c00856206c0a0b144180d0f4841e0011b50b070200c20300480c104410180c00c19096511800d000324041d10a640d150512446039440c401d03504485000c0c00304040d0751294034082d04040d0481c44981e404091248007050700c0541d441e1069200700c00910090800d030010503840e00708840c0b07420982440d0780035000c8076030300380c0c03000e244030341e1017105403218000c075041014072003142c414100045030700c2020780e0148582c816499641c00c03807541c90701d039021001480c1c6071040801c44540011190041004886c04c0e411030500300c040076140c2e01710040815009030340303140710f504544038103000c1e8201d44500429241ca440d0380f41006500d0342 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 705143471 1250 705142221 705142247
    0x16030f4b090501021203131407090e01020d060b2b02040b07120f08160807140334141b0a0510050c030106080718050a0329010b181c03 59
    0x101403501d076002c00d481c0000540740702d047d0020318a580c00c2540d407a148240c070714160440d40c85008849021403401c5003401892600b800c41000141c2e2140802c0c40141283c0e0b6940010184460802c0700075048540700408036081b250384412400c07140100d03a403400c000c0c40740f58400c10090a001c10f81c03806200c0749145099611036640c82e0350b10307026100c9901307c501d42c0080f10b0740c07444a010061510070045c1304509150384240c080c01c2101d448840003040a119400c21901105043c103d00403524a0061100e00d41c07001400b020035a805a10110102514039264451540210000402d075640a442c1c1e828501b150a0450700560f810303881e06003070a9449081c0068ec40004030700701408514a40c003004101c0c0d04803042c80d80c903007005464080c1c003200c880c444885040d1108080e50701c040354036030f1801c2c040b100443c07041c0341d40c8006008001c445a0000c182c202c1c0c0341056202100108000c5116508882116a50360300f040c190b003101e4000914500320440c1c02c018144e00700140d220030140c1049103c280d41c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 705144721 1250 705143471 705143473
    0x1020106170115050105190c0501090f050a140c01021504050709150609050d030c030818010e03090102061609030b0910060e01080f010c09060e04020f16030f4b09050102 74
    0x6584c641006403503034401e01d07201c0d001c0d44450166182c4154440c40b1344500365480303400080340c0b20080c0d864400d80616000c0056826400c07014014080101705060020400c1386540070b401d6100f042d800107500d80d0300f109885a2000c1c1c0d500c0c00901040300512250014000c0010108442500c1404c01008071046000f080041a05524081450700c1c241014448950f40360390358100681c05030303608866a00e00600001d0140008282076009280d0070b002d04c03554550104029511404030f80c00080c50400054540e10502c5500302018000c25070100f00700d01038079001100080d80303444420300507140084100c030154200385401404200a0384e200d00a6040321552001c131803012901c03014140c202c4a24007180c1020403600402045054091200e50b001703e60000c0c0300508020f00c071080c100b01a40140300c2d9102c6c502e0407207580800c05801640c120703028260f51400f640c4078100d45050100020b058880b0440d0100751a14001964030048019007800c01e6110340d05503403400d031450191410000780101809 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 705145971 1250 705144721 705144761
    0x309090705090d060216020a03082d04050105031801020c060402130515040b0118090507091719111801030b09031c0c03020f120130060506010201061701 67
    0x384922600968000980003001c039480f104150b074a4034029441100e140c1101307886000341c040580d6408401c20015400340d00c60319a1042c2c0782c44001d00c840f001d4100d640420350300f500c148030390460f1740c1d00303071001d40c1c00c203080071666a211071180404541d5072035000141980001481d481900011407114000c0c1c0c42960683ca0700c0c2040200c40c0162031040f510804e07000340984c82d0b0503d82c9001d4000480041042c1002c0901c49010080e0341022a10368000421103521102804030b6203900841084c010002624000c19540c074017900175458480000c48c074102d400407504004244200d1000b02604e1490050156404501900001712584c00034070007641c3d0110b100340004c145260100c00ca0324a0311070038100c034040d0405840032100030311030442d4000c10143d085c081c0c80c40c51407890006185510280c0800c8505600d81404554004002020603104101c003402020201003542014101c140d40443d01040e55901c036030040b0f00403c0140c2c0030301012181200000c2811b0f10651001c528802c00c0c2c0e01c0520 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 705147221 1250 705145971 705145981
    0x21806030403050306040c0e03100608101b08040c050a15030c1806050f192a020105070204050604090b0112021e010219140d031409070501081602100905030909 70
    0x400340411900900460400c200042c203a18055000e1614400b180c02e1915002d0144404289003040c00c5411a400680d42c01040c000c26400300b003d1100d5440161003032100d440c198520119459401042d4402d100ca204045810010000b800101401003d4061194280d55418845103c01c103100ca48010a00d88110260702c94890500f0307000c075121483d0b01c51601361401c03208072032582c480d400e05000c0110a0111640c400d42241c0840c2d203800c405e0381c1e03c2c00f42c0540c1120403445542540c0c21005201c41c0c3c02441001070740c00c5001e4654076a01103400285a5032400d0104000c0c00c59280e0003030041d0301080c004180c0320660403280d80c24030b000b5250706c03d0354040942c0c400c108090f441d1109000d60301207840420301c5004100000300303032403041ca00d80c0ca110868010300d0f0320f00f129503881440800c0c0c8072945440d20092803002e0b20352241c0040d00501000b85031000283c1a01070203807416030b8800e401340a004606008010046420452000c00c2142d000c2d40d00308281c1b40d400082000d44600e0a99011903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 705148471 1250 705147221 705147229
    0x14100f052d06060a0c06090507032915040e0d02060a0f09020a0510050409140f0a1e020f040803040b07020406050619051b0a06090303050a0603030914010513090218 72
    0x40c0303103106070029409612070904000450b04078001000801003414a00d0000075202d00415801a100750000c22189046141a58040c00354500790141007a0103045c81d5002c40038030000a4104940c0800f03805c64600d00b5001c5000b0703120507044509544610355002201c40d07030020321a481754031038600421000281c03038408020b60b0b11403280a5801561000700740418503240c00380c18041052030618918143c1d42c1c0b0046000d68441c40040380a2000074400c1004480d01c0412860b80a41c010300200040d020301140800b03048614610703680041ea0205002d00360604030b0080b41c0103400004200d0307817940d81d0f07241d0888082d48460000c03402142405000980c60a200b030a4803400702141015101c45140c401007192030780c1181c18405001c0c02e420100ea0080001031046d070401c00d00070321010800d040b040c107000d0160b4801070701210246241c80000c0001ca0303804580c580030365a001440c00c03440542100129454024640c42c8250030880543c00034980403680d008002c2d03180703110481c10410700200100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 705149721 1250 705148471 705148531
    0x40c02070305030906091906110c04091e080d020d0605030d02060c0f16120e120f0c01031505040e1f09080316020109150f0506030303011214100f05 65
    0x104140d000b80821302c603d20300320001e45410341001e403044190400c1569040115032455018102003090100740c10502542440304d074101e20800e40d414070101035550360700d4001d00c7c0d40035104602046142141030800c8a06800c40300121a0500c0075511038018180340402010307184a00d0b4800d100324060903c41c1400428110721401d10b0300d076000d041c030001c21802d40050388503500d0f070b2030703101291102c8000045541c4515290101d0540e13481c0a00d2148809001e2010700c03a80f21035031a80d005152800d41440d0026011a41480078a0003048080803da051340e0040c2258000d00e51003410518644040100003514980b459826042c480003a207001c020101114000d0300046d20030313481000002c0840b282080d03079084400c42803000107407000b040e49a0328005118480c44540c01629400742008030340341801b0321604404e044015500c0e65241000040c2c00b082c0da0781c002000b06c4086450365480c0071060020b68001c0f1100701d401e10141c0e80b0f0000c50801000c0480c1c0100440c1c088203211002200003180c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 705150971 1250 705149721 705149723
    0x90a050708010e0c131206150e060411071424070509011b020d2001050c0d200307062921030d0603080409140702060106030504030c0b15040c020703 65
    0x1e01079050742440401400310034000c10305401200c08014005050102c000c500000b0500030900e050741042c1850010140c4102d68078900d190152035001f403041200c41100e403604a01d00300c4001036580941c41d8240784500491802605049590f1030b1030801c00c5000c035072203441121301c0d02840001400c1c009403000b041c41c19280c5a0000d10300340550615940690415007058260205818803803100f0b03800503500c4000c2d44402c58002110304100e6240382c0200c116907141c000c0909003241031282e107068903903455800c10303c401d01700300340794004500d90b0b0a00090615005803030b0f01600da4422440c14a41e0103000d08028045120307104000913202d94030205403801c030880e0010060302d0906524a0840350a8042d080d0f403095a001c01c01841c00140d68074400d10000303504c075a080a0700e0360300d064992000c6800c0c000d442d01c10301c00e0780c4040103000313907011a600781540c1503070074006181c0d10b0340d0a08448114180e83c1c0200120911014840507c048078511090054204d0301806110000c00c0100d031200f5080c80 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 705152221 1250 705150971 705150977
    0x1e010302010f050415020c1903020f0409060b0310020a090e0105012f0a0c180504081603020a120c020f0307122a03081e030f070c11041a090a0507 64
    0x510040d0301c41d58403607940020382e1070001e060a0315018004442e80e11420f00c9000360384012a000914240700f110035405460340381226030810720f5500800c1c1c504006452492140d0390315000c001c20442d1691090340c454130041d0072100d9601103103981000039403083c4400700201e854060001141020146424140c0d401a9034100109560382e01c1c04410754803056492a0003844a000c100d60402c081000104003805008024180c510709240105a07110040c2003050b001e08107000c100c040b0340c2c032000303c40410030300425580f016501030508a0030808081c8006200c007100350700c0205103650021080c500d0324000c0b01c0300310507140342d0390805a48400328810804100d0a0240b1400420382d501c09030354111141510030301e9804408141c2200400309900200c40c0040c0c0030680c10503003030b0880241043c0c98130315441755265007046a5103910341080200020100003624031400c04201c2c5040d00b01c030125002078018404100944404514413005c0d08a84d40521095000103072254124090389003d214252 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 705153471 1250 705152221 705152281
    0x6180203060a0306051906170a14010e07090b03100c120b040b12061605030103081b210307030e030f071103030f0f091e0f01030b12031303030206 64
    0x110004040d400003015a58032500303506000000c00c41c40c1c05460711404204225060107001c80c100c22080f600c0c650040c1c8540d010100382e111082c44005255003200350424580700000501801c400e02403c6a144001002c0c05a41c3d0f0004002203207030400d21900a08400740c4a5040206141508481085c0c40f1500020a040810030320550964008007050001401c081914541034012415411403042d1a04080d0301070005c00c11003540615000f01e05c503201d450003030f02d90751451b1958001401500042511083d25003141d0712031403010804a15900140ca1403844440070a0340385641e9500300300d40d035201190810003905104007010040b04c040317000e264071950500d661912410b03240c92407505041d816210800544c101d5880170b02c094601e480e8102c1780c856840040b0003c0c05101d030308160700e90880f0b14103810707200304640ea140100001c584080c0790009040410000060612000541603030880c0000201000d80030780c072510000a5a010b9003c076016500c0f6162042c8001c20541014202e00c2c601c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 705154721 1250 705153471 705153509
    0xa0302071a120118050f150613090f0603030801050604061b02030723010e010807020d12021c020301050f15070305162108060a0b0a20030301060203031906 68
    0x805100c50a8032030300700026040411aa4600000100a800c0f042092900c04104105140d0038041c8580c014182e0703082000c0b904014440034103007505045914410035000c03465140c5104000d0b03000c0000d00207880180085400b0700341041c010030190105500041800300041160304020301210101c41940d0b444182003400c0304040c0403903070b9160000f01d0341401401400148250b88000041c40d42c510320b0000341a040001c400500300f10804070140303061040704010441410740120700a840365646e4103002c413000038080d858000900c0303140281303123602041c051100703145000c65000d1410b0b5103090700d08000c680c900c00300704650030300d10000303e44825408018100c0041c0c8940050029541c08005407115070303141d9a03540040303029510722603510b420046881c55115a0011a041d0041000e4501d03007403950505c4c404160502ca02c61051051040d0105081100344281d6020a5440104425681c132541c51315402500c80e4401c0d81d0b0385c000740109114041e55402c6510601c1d00f1100c500031400140b00d0f05c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 705155971 1250 705154721 705154739
    0xa0b0307090902060403060c05270f010e0111030a030e060f09030a050c03040b071202060a05061c23010501050a060e06040302040506041407081602030c0a1103030c011a120a030207 79
    0xb1010040f40c2156090000100140c401d00039105c81043c0c944490352035a640f01250a04881c01102c100b14084850b80501c4c8552282c1310300100785c100a1804500b2402080f00507110b11880b0301400304a8800042c036007000726491340c031210120701d80905a07030a544590030941540e400641b4120015041080002d0f1034a001d08024000f10aa1009603410a41d0305c20202da00c1c0d4000d000241c0d07035842e103038403002031959051240c03a901c199403560401c61418402c2c00300c1c01075000441c4807440f051900815a0901410413120220500848c503540061600c0404080c0645028400c05018464040010030b0b02c0e802040301034030840380500b0481c01c252540e02000040c1801803c0c2e190088d0351106401130f01c4000f801940e100f103145440761481c5007440300113081f2070b109480400b411504240603240040d00040b0328180d04d1504000c03031056007121b000009040d880f408584007500c3d807a0600d098410180b00b00d24100206080380d1000d000b2400101a40d00e8201c84c90009005800c081818010181 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 705157221 1250 705155971 705155981
    0x50619030503040509040c0825230f040e1e1e150601110a0317010b161218030f0537170a090504110a02030319230a050a0b030709 57
    0x1010390000d071f0303c040d0303500415401e100c445c2c042800c81074030034505845807084c02100b01c0d009000090450b8038046408000c8541d4404440b80780d4031440048d60a0101607456403c0301004580100694030000c0043d003800000b0760305044a06c006014201c0ca1000360040f800010b00c01902e00c0780503000d540d59003801196074150081826042c4040003044900c10a8100704000c4054802d445216500103001225040039805920928903448101301403041100444040c0c0480303075101280c131903e1862844181c5907000c0510904141c2c41c0b11550020070312800e10545038255000700e040e52004450350030545000038100480c02400e4199000041042c039058640820a074056030102d084a407424096101c207a21001507c4002030004c070301444149410f00c1488034038406030000c0c0b4035250b0302c0c0001940b2030000230308200b22540d81c4400c1507188000354220042500c181c11003080c0000307042421001c880c0003684c181012030710700000030300660030078415480280c034010000d0040c20700d40040140580 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 705158471 1250 705157221 705157223
    0x90203060612070201150b0717030603070512010207080c070f08060c070224180a0801060303141b060f04050d0801080606060f07060e0d020d031107060b1c030305061903050304050904 80
    0x3d0f40c3e0700d0b8004407820201b6500d0000d40348820b050340c0c0d1a5118201f10001d2500c6001d8005054030070400c1c0300c40344d6400160541110f90907609402017540969400b03009004d05070300174108200000d80b07842881c10114600040c3d64880e030b00d10030710503152940c159a95008907011a2004400c01c07400b405494200b403c05800d504034a0540c000300c0d03844128802c55045603004003000030002c03410000514121034041c001d8007203a4002c10a151440d20f00800f046000c0c44545030316027000030940c1c0103880140684c1310341040c0c0c90803100d090500200074401c000b02220309407114017a4000702c0a020f0701c030f014100e04855902c0010099616980c0070808141d1000d003401908010400036040020304a00800c081c59020001400d1030855003040603040c031102c221300e00d0400d4038100343e86170f0780c0780d08106440e90941c02c11000501141c10a0118141120b80d0341881c4015202c003003c41c0030164550011f91141c0401d541c119240080919103100240107404001c007250001d02c41400607041c40c4007600d52007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 705159721 1250 705158471 705158473
    0x9030b0c03060d2a0e0405060106031e0606020307111e1002241e090619020405040207050a03120c12050c040302210d210c030e011a03070902030606120702 68
    0x12045955030360304c030480060131411560b030380300d0142c55040c01400030000a0011311250402c0d4039050392029191101401081c0074569620b490400f107000060958001d01c4802800300140703510303168069600d4100a0044442c86070342080040d036030400c1038005520528007190030801613541c07001c008003074844403448021807080001d5001c078102c812002c070641c000c5c41e01d10740040341014a070841c03260150f140703204640784490f81442920100000e16542c0401111116000034080003600b4010740b00741c2d0721281d80240003084c644240500841c80381341d214401d80712040115039415110060b41d40300c005040c0440e6542d8440c40c0d201c119a040164400100e9500c83d103001d0712940051104000806940040441300c0302a0710084410012001d440d8024240041104001c070140100128900d04028030700d034450401c200c0700d03400390f0031140d0010140310090158008010b03946a05c14809003001e407103031003907070b500080c001094801c4a0060002809140c80c0008044080050f02c81c003074824411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 705160971 1250 705159721 705159739
    0x30908070201031e06091a1009030627030518010e01091214030c101a0d11010309140c0f0a0b1e0705030301170d0908030d09110a0303170709030b0c0306 67
    0xc2d204c840c0c8a007401501c400500000c0c04001411410080c038500040d2034000c0c103040c01005c0c0c14a40002460044070b501c018049849403481a00c4140704000c14211481140204003280030190400007804034800c461048a5100c2c400740011181d40d1100307011207003c00e40c001c1060102410481c40480401e00506200c090104606002c1d0728503444200d18440350741288281d8282d400c00341c0a00a03062840c083e83e03034590710418000038400c01900600501d00074005000381d0f00d1740d0080c0c00c803000311034200400d00403030540d624906458649500d0b0241c8141140d03840d000e014a482c900102c1541c0300740002a08104100d20303040700405c0302c040d551130740c050107005940001e54100000c5020303281510840700c0007500d1108807842c10a40880240501c160740006000f192400000d44404a075040e101003040c84150501c50200030b4202c00660301300040000201c20b05400c44141c085508800c0d072810752944d1000360454044800d0300008050860b21404580c1d00510346001d1078010321b000f008020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 705162221 1250 705160971 705161021
    0x2060d0f0e070b0408150c1b150703050601090b1806030903070503030a0f050c28260f010e010e0408180d03110c010c170c0a02060706140703090807020103 68
    0x301d0861190f03c0809000e40028082c40395000c10320100030240c1145c0c0a0001c541002911000180a2118650003841500c1e00210801004019400c10031102a888191a04090b9070041c0600001c5600c140032660000c000910040004102d4500602c40d05401c0803088132007040080590020b05010214482032154201040090004600a821034400004c44000d0b0581d00c00595000070081f183c07508081c0728054130700e40d07181c24003100b043ea0365416001c0c0108010302518452410500c0e2124041c900444a1003541b0280c1c40c81c2c0122422400c9481980c2d80b034000d00c4c1c06a5003401000d20350039015000c58000390700540505081d03030a05a04840100001c030108032500c4001900750300155040406410500003408040c046d4503082c03030544c0f101165038442c11119030501035601000e181c001540e001e01a414881c500d031042e4010045503443c0280d040000240c070484114219400b00075000c50354050007031040c125202d620031885130030a210307900154003e240141c0031840d00c80070641c03108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 705163471 1250 705162221 705162223
    0x70311072a0806180105060a0602100c03020409060311090c030403020703030f030603171b030301060903020d0203030c03071406012c041b0b0703080a180b0c0c0a12081302060d0f0e 79
    0x3d445030b0560348a1024444d040841c0da400c1d5400a00713814010450550103110013a404030b82041210482c010105801042c3d0004800034400ca501c5111403038a0300ca030100c100300310640c00d4006000700f100c4624542d00c48032304a9600780700945004015911101e1304000080c01a44030102644c95400c0001d40d06580342c40e035940462010404e90f0000c14009140b01c01c401d14000042d10001c05600210705641c18018050038584560101a2090350940d81c100215a01002210400f8254100341c0351604180d01d400140007828000d40c0c01d4a0140000100710507003403600310061004911087c2e5903040c40170040200c0000e0180064036440040c0708480d100680b48c0b80090010403603425a150b80d01440d042c02400054003134a01d00c2c409082c44a2070304400d04050645000507041038014007161292410381100b84114038081400d405009120310074403000404140030303d901a203640e800b9944982d2002c68083d05c030200254440c4052080710002e50880d481030300103625051000515610003a086 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 705164721 1250 705163471 705163483
    0x210a02070b131b06020c060f070f08091e100c03230903070605040b04050f010531060219150b1f090e010f0e040f1a070311072a08 57
    0x46001031080310144010480c00c55940b070b040f2100c11812050036414454002d480310100c0844a220f41030206400d400ea4214070101c44040d03911401c0580030034418941408143c006002180c410303d0f00c1d0000f9070900400b03030900600304000a080c1d0140741103000033a0307000812040c041d4200041c02c4800700300241080351001201580614a0351503c0c101c800b01407030040903410070400c00006000410803040781c0301c00c0e14185e0f04110303646205401000f004076402e00a10040c061445400403a051152030b202419410441d07010404c00c400720f80f83c1e001640d89181c0d00d41000102c2d0100740f50000031505500140d804c507100000701050032020040000c06440c006c4100754042c2000184c40c0c7d403015042101d003c010074640c48005665858440c0c0418020315510502e1151541c03040054200101600303100768060f4041a00c140005c84682c0c00d596140703007100c00c0030101e032a01041c10896821101542c0d000d40c2e004888900c00c82c0d004612200d9100c21b03240c1e907103488801507c003141d200070601036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 705165971 1250 705164721 705164731
    0x70503070b0417091c0f05030307030203010305010b220f230603010501080606130c1403010b1804060f140f0402120a0c08070c0b07111006060311210a02070b 69
    0x14610346420b250410501c090450001100e0308101003102075041d40355681410100d020200c4102034000302c80c104003020400110004186000000400c00b50381d4040c0d02441c141e90045000300440500da00600542d0301c0e10b40d041c001504001c52080e2150b280325004203ca0000e44003020408a8074290241481804001c10325003c0c0c0c2c2b00010020079080034070980d8010300c404001000c0ca4204440801d82034510031550850781602d582c0f01c1a10079008d0402210607514008103c2e6807580d5501c403035002904544d01280901e145801001d61078030b0240921001e8400c1c50303010320040703881c1c00ca8010024201030050340c3c2000d40c03d641c102d601e950328400f0b00b0700012041103800340c0b841c1030000c4404841d0047c0381c200c240500c3c401807001d9960320440a010381548600345084a03110b00400b070310f06010b040090011031140040305e020700181074020a003100c0441e1818809441a0300308102140540d0388604103610720007c2c444291142d541d405508505a175500502d842c140d62178509042200300c039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 705167221 1250 705165971 705165983
    0xc03140115120c0f0c0609020d0c05030607020d050a1107050402070b061207030b0612150106050c0c150d0b06070b0f040210050c0d140408100e2b1407050307 69
    0x44616280e58105034402c54140c0d0b650410040e602c6402d00180021070280350140812030707411400010001180d0000c1c03080754009280c0785803900da600c2c0c8600300c09040d0040b0b0f4064040d0780003213503405000040c001c0c070f03d139081d0302e03600e00b040103c050844108881081e141d90074401d03044005510b8403607100410000780101c00745a817a2a00c0802d014911000c1c1c410040a6403140c481080410050071002e41c102408032005941800c844d9591480c00c039089032008200344950000140040d003140060011400741c1c8140d0710342d04023170750800400020304448a2448081000780dc00100d03607980c0240c035001802171003039080c594075890351080e0310003c5455100039807111042c0410351070700411820050702c1c545130041c9000c8a090245884401181d0441e0510a1015184801101d118241d5001c3c01801045401031500c1070343c041e014011403944002140205281e2240c4608058100150540c11451140344c1506003036080300c15040b84286251108801e00061340058000c1c002406070b14001c40d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 705168471 1250 705167221 705167249
    0xc052106180a090204110322020a0302090901151205031b1219020c1c14010b030a0501050105100906020a0b070c231005012114010608060f24040c031401 67
    0x1300c18001143c060b8000704455080500c101702490b440340700401c030700d03080c1441c0700ca19162051000c213001020a07007001358000c4840b008c014a0b101e05610160900301c106002c101c4443c0c2e180008080000070b501c000e88135400400c40c00070184e02101d100410102c01c4000c6500300501042e289030745400c4480c1036656011b0349945851119410043c618407450110340754090b154003400141c4ca02480300000804256051541c014821401c6d804a0141358018003920054003ca1a003580207000900840b17200d0803078107499601c0c0500c42d010340d4090b545103400500608405031900e000d0860018005010007210045074400a070b14140fa01d103800f503401d035030381e4070000e1400341d6907090448034241812050324282c0100000440046542041da00c10111180700c1c1995082150459172442214002582003020004900d00c0000348a44a140c21510600c21610780c1a04840072a8038424102c0c8140c00e284650081341c60560b00c0b600070000c0500340040c0c0640c40c000c444400900c00da204c10000007800f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 705169721 1250 705168471 705168473
    0xc0303021e0610060c0203070f1418070804141606030f0f110f0d0b060f070210020a050706030b0d020d0c0602160b07060216050a150c052106180a09 65
    0x80c4085071408503103809001a4070b02075180d403410034002d04c5030344100076001c2e1500d01903490a00041019100e0841c000503072548030025176016540c2c004101d030003408000541c02c400505070841a0050499950b2039089840d56100c00c40c1e20285c844810043e4080c550500740e580d00740f41c104074001c05258070041a2074140030407110884243c50303d5000d046080c09511300802c00e004088820580c914190030391600d130541008002090000d8190390082c0000442c080704078034841c041c00c601d034400c940f426920400c4020490b21242121002000d40d8803041003809140d000b50000321240c1c00242201d6084441c5800044c07030001d90b10ba0035a104442100c0900503294180403007420b520540009130801850201503142c103115201019011a90200382e00c8002d46002011255890300030045901c0f55065003040346219201d00c0d03003040e2440c90000f042803554045d2040d10301c0d1041040200c08002000c049001c1e611a00038030896000408800740308601c8280080d15008003012107000400d1955 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 705170971 1250 705169721 705169753
    0x21e03040219030b041e050606060d0b04050112060e0a080306061b06150405010b0418050702160306140609040f02150903031605060c0f03280c081b030c0a1b0c030302 73
    0x40e45000e4661004440c006000310b9000072305a40c204006490a0b0794411078680084001d1014803840d503486810700b0300000304100c080074070f01d0382140548400c00c105c801e040c0400b81d80d08007400000f000404144000343c0140380140207000c4080c580000c42c0c1c82a046c0440003401e18804842c000303503071421001c180f51141040c0c440c460245c560f0640481c5090b0800750303680012424a29814000c41d1a800004d0060707200313001c081d504900d81c000040c0e19035200d1130300c0000341003a00b0301c8040321000c10000454616000c603059028540107500300c445000150281310042c00d81c0990401c0c0910204240c540340d880c10401040b410220a41803480c26080d481c00e18280302000d0062801d000b0103101c2400c2c51a00c0342c0840b90041c2c0f09110311107058908505031080480b1001c2d00b148007614007400789880da82c12802c8140b103020312100544141b1641c020540a41c0000e03030700c0f1000c0301020f00000f1181c6001d9940b1b11694643c070080d800c1c10250a0741e4120014810781c20480c01600410755002515030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 705172221 1250 705170971 705170993
    0x20703122a03111204051905030a030e060103030522030c0b0406080a0b010e01080702070305070b0301050f04140a0b060408010203091f020901020d0e04020c01111309021e03040219030b04 82
    0x1081c2e14080c400003415500040c842c0c0a2041041e821807410b8000ca004c101c0104032140554400d441162a80c0300d003800c00549942004035501e000c039040503140400d119010032818141c9605171181d0341040020000c020210369110704002020315102004800f0565603061030004100051041da40c0d24100300c0014244038001c1c2001d5a5903013455009003180e80c20209c40c448240d005c2c07910544541d40e00008a207048103d610151a6008000010948603801402076040e9031041d5106511000c0f00300078401281d60041c502e030000d102c032a02050210707415070800300c1c080e84000c00aa003490b0300c410085003240d205490408032a40304d140740c203c40c0508070040c644540c0014a045041c1a0343e40c0010f5202c0110003c240c08204410016100940d502e505a03036140c41044000c206986944449212961202070b408040064090001451115038021101200c2148055660444d0807401000c20f81d00050f20032680055181074155040c552010243c000314020800d400490030030342440d480c124 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 705173471 1250 705172221 705172301
    0x12a0314100906270203130602030c09040507022b0e0307090f06050d110f01050706020d060806060307031e02270f010e16200a03050702040e01060f030602070312 71
    0x100c4001c010313002c42c24454902400d403468076501503644d6a80103685d0740741400c002e400501485c07002c001d0260021031500078210106007035070104207a0300e401c1c90503691501e07103c2245000341740c00d500780e40110b071140c0c200b099030961900313141600400800c0000d09113075003a000440e4040c3c1e00c551a0300038001ca401910020042603d030b50340020425211800403440c04207a00780034050109500310103921401c00c0f03070b248a4216a003151909645803141014000a100d941a00d200303e501090345441c0100d03010040b80d903c034401902801440c03900380401101e400c2c0c1a40e0110103c80003150184856142c4001940044580d50035894540440b642210040e04030403100043c032010080b074117807586028440111182807099608414410b00c854a0b40a14402c1010340110031040d002c254200000c0c0c00080e2080f542400013a1401107114201c070340d241b15580380940307503003400c0020800c1540140822406840c04140410095200b030341030700c05800c1c440b1004200384079000700786501039030001040d07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 705174721 1250 705173471 705173489
    0x1b0e0f0c0f0a180f09050603010e0c010c0b04020d02100807180e0106120e030a0906110312160309050616030c030501030203030405150702090f07080702012a0314100906 74
    0x810500c80c8460314078002c00ca50142480502c0e60a242c030b207210884804001e022800038100c40350b440300c800c8405030609445542c025824094083c000c01008135017001c281006940390009850390b502c540007414030180c4281d801054042d9164096250000860004c40450312005090300b403608000700801681702480c0c480d4880c1010503c450185401024111440b80c50503440d00c241c4010074100804c80c11460580030f120001782c80d0082074010386000d003100d0254841040300d8110304911503d9104c1c43d0850107804504900081c2641c0d01c01994281800c02440d0010340d59825580b02071401d50256820040c65100c025030492855040c0180e800b10000d62905002c42d51440c0e0200313680b40264000c6c0d920450a1032514020701d040c00080e10030003600100030706440d04000c042c109a127141540c2d0b00340020940e00000380c45c14014014000c00042c8a0305c40d20440c55061190312022002d200710804040e2a054041c003000c4038102914004c0030803200008109180c43d9003c42154100d510044030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 705175971 1250 705174721 705174727
    0x3030402060409020a052109100e12251a0711060a11070218040b010f030c0306020d0f1b0f02010b010503060609040e07030c05030706050403080d091b0e0f0c 69
    0x16241d040540e421502c0b1040096140c0c800044161345d18066124040c00000c00c0d00040082050f1700a030f094098a8101e040d19001000b060120301138a0940f542103103070307600a01c0c1414880148000034541c100100d81d40d0008001d0092a0080e0003458440a8501d500c001124072003825402092036042402410b01d4400403003079840071621844024080d00c2095602c81001900303c14810454201d82c0d4010110b19460810045041081105490a4501100041c0041813128112000a040d0383d00038094a018501c1c0d5902c42c0c0c040d47c42a13000d01052521945d00340901d00c0e4a0007400c48506aa842018090f02420001080a0700c448034120071a8108100d00c0120303604082104e403c030006403544c1e5034031546c010124006c0c0940d6541003101b8854040c1c00800c1c080281e04c8041a50000c4003500d071001e42d01c01e03044034280114003018007450700402c000142018151b0010f000c040c452411480c0e4100b041c00c4800c28040341d03a00003642100c000341041440700c0b50328030072688000d0401d00300341 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 705177221 1250 705175971 705175973
    0xf030a1415010c020f1003050901150317030a0204051e100516030e0301110a021b01050304080a260c07020109081b370929041122030201020f030304 65
    0x3900e00c000e1401d02c1c107204480040c4425922618840f030b115001c0504a040c031001844001001001d04440326440f6510f0050441e9202d151340311523008881d00300041c5000c40c543d200100890350704c0500903002540e4204400122034450f041001e03040d82c06020070710103030400c00051244400c0c6039aa0141005010840901809140c118015445425191401c640e00207000460300400140071542440c1ca80801c17259200b99002803040c00360100300b018600e5540c03101e00155414002a1030042002d4001e204e100c007000d214806e980c2c9250240b6088203103080c243c60b10499001405e0740d284950702c0300020030400713550700075651344010302072080180520007095460100c844d030344404c100e114621114a00107064890045009a45104070111038406a58440c0210f4104180304911038107003001c1281d501100c00d1854241d17803000b102c2490700903510a02c1048001d00e60192560040001803103001074500001450381600c6074056100c0d19042d00314000a032510011040c084d80c19401041000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 705178471 1250 705177221 705177241
    0x504020a0b090f0909070503210f030402031f0b0103110f0d050618130201170f0c0a11070e0f0112050a02060a030605060d06031e1e03090b0f030a14 65
    0x5001c035800041000e4880c480c881c00202e44040c40910550f00501207801d1000010010444000319402241110700300c2c400030f41c400003082c040711110190544180b04880390f1100d22002164410b10041c256a02280201704003c00090b05141d40c80c251582e6840c10151540c1503c07030502d250015895050410341e0390304603010f00f4070489282280359922031001c10782e2601e5000f104008116040c01904171032404640c142c4010a100d9016400a000500018866030340a06054010005200d9581056482c00c41c3c00c0c40f940c3c00074000f00700300300c00003544c1da1001c0d80601418000d0951464441c03100d0031320600d28031800c9410381040ea00000e244503031900061001070107000b4281d05542d4591640303c6090140d00400689d801f9a07001000000c084046010301d07444401502d2050070b4503c520206240783d01d08540c82910010600b80c0c00c1c0ca41c0a200d2149643c00b0702005100b03160050b20161a00c1412016800990b20620102c001005000602e0010b0185203400301040c040301c003072407502c07681203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 705179721 1250 705178471 705178489
    0x6160930030e19140d170f031506040510080601050c011d1e101517060403020d0e13110f0403031e02011104090c03061a0a090510140a0302090d2004050402 68
    0x1648680d20414000c41004134501d0100c6c2c2c80d803607904095480f14103c00f4400201c1d4422a403c405403410905c0314030013854003109803010b6400260400108503210041075401c0b41d405030100c1d040c8203080c000e02640d00c109024054802000001c25200e84030405801440d10411000a1144d0400300b0b050748103032000001c2144900030174040115028100d4400218400244c2d0402c080480c200251100040e01c00a034082c0505d200e41e0880d050b11041c0c00c07045914006905c40326070300c40d80d020b500141d141c086070803410300c800b40301d82c5151a08100d00b0701c00c1200e43c041d6008402041d4010101004034480500b26444403c0c40d0000740310803000140d941da00c03032040d070203260700c078580c0c5a0041c0c0803c1c7c07003a80640301902d07806040400c268080034030090141c101851a00004d82c188c01e0214587c1000c0714198000200c50b2502c0403c548040c680c1c2200d908a030329444109a03080c0003030328540e41c400e645000540d00071000740c84050901040c401c01c80440c01c00081c05036081805000c0140c441c8424 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 705180971 1250 705179721 705179759
    0x30703140f090a09050414060601050d1112100806100e01090e0f060a0f0e01061206020702150a090609050d02010e0108060303040308070b070206160930030e19 70
    0x1032140c1c1d41440c41e024261a0060380c0c0c280e03400c040350b5000032503020720744d0b403240313000e640200300c03c200d1612004226580c1d801e085400600003103040c41807280300c0801d9009105900c240c085400e0400d00c0c018400840349200f2100400c020f101c0e464200942c0b4000c0c0403170b5400c01c007905040074a036402c100204200040601c942c18000f503440e81a001c18140905c003411007021814162141c83c04c001d50f042d000b6100450450360300501d0310340044c0d92508140316110494603001240030718030b06607488a100071340210000380c2e00700e07582c0381c45050003c02100040c21081003d886480380e260a2050052405000d908454020f024800034000945e07002069010700300d20928148003250340c4c0b00080303030a40c05254002004c1c090085240d104229151850600c0f915140c0e08895080d07482101154104400ba1141d0004c6100d000c0305102c104400b894071101c92451501409600140c4030760711200a011820a034002001c0102c050722501e4280c22035000c0303900c850b040e81c03400b90030200100343c0078415601c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 705182221 1250 705180971 705181007
    0x70e060906041410091107030206180f030c2512020d05010b030a080c010b01050412060b010e06120a0606020718150b12040c0609030f080705010b04020c0a0b09030703 73
    0x100007081551030b034103c0f03049084240c0310a030250521818140000742c01c0e000d12269541418418000154450700743e40c605501540101241d40f14107c0ca9164507110030140a07a074005c00c01d0517003005400700000c29480c00508014200f4211002400d00d01312101d001e1607114215612080214842c00d40704e01c0883ea8044440f4103504200385070030380c01402c040751116094022450080140320603200036000b4204580000e22030075a00d04011a428425802102c803182000d0000700c020030180c3d4420440501d060502034425401c01c07002400c190400401300341d03000c0c044010031190b0061802480000c01e2903000070130700142031200d00b42c01a15000310340c6001c95030f5581056820400203174180000e2a00c0a12242d5440e40c0700d0517800b202500302c0e4261100301d0f600000144140c49140d0b000100c07034100004001840142d92000c003550320201069a0540d03c400d00d804a0750355030310080c4032409203400201103541d210700c3c08100000c0014001441c50b0420302504c80480d410001880504c05507503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 705183471 1250 705182221 705182239
    0x11208090a08071502250b07080909040609060f0b0907180510030606110f0c150d060b0a0e030f070509042108061507030903060c09090e031b070e06 65
    0x440424007100c038940c80b100c614031500c1c0b000540700c03042d84101c0d0301c0160b1580c00d039580c40400e108620104842e0314903000c0d01620b200c0042100340c40704000340405620070b202d0f5a203032441407030000c1c45030401a02c081e40c5642d520800307102000301c40c1c400c003200084941c50500c02c0200c01400185a41c1d00207041009010080151080f0300c107500d0440700140c6401040c004054007940070040c0184068001c3c040031480070201c4c140c0070380c40018860710404503403005088012050702801101d2803005404c4030700e0b4000380800891720071180a014040e04d02246101d4464034010801402c2d00481a4200e0013500410303100c81544c200810b064090360400c1d00c0d2040bd540310761820040d80c0304013074800c48001c082c6e550a5440107901c08010342c01050300701c0750050b02a016a000203403074456440b0040c04035202410400c0002d2070350708135030086400c1b03092261905036610f0000040e280c0d24018202a5040000d0507034800310100708900391951803900800342181017418044181901074652481060700d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 705184721 1250 705183471 705183487
    0xc0f080c030603100912030c23132103020106320a0810060f050604052101020f04060c0b07090806010b031b0703020d020d0f2106050603190501090203011208 69
    0x8000c054030000c2061301c00c11500c8254103118840000d506100300000b030801184511003845401000040c076203028039040c01079041604074210b0341c02861540541c034504080010402408401e20380c008450a03e00c0780c0c1401246002803c58507150040580450b0030307148201904180f10000e05107201c1d000d4000082410351001031401d4195a018185078401c03680b01403c8000c03990000412100755600284100e605c1e0810016680100e0280c1038128400a044443d903445403041c8800320341c3c1010006150150841240b041c81d40203800440c003140c000c44204007008404006107502404a10302440780c03c0c03c0072902522060f040c82030303102d818030210104074910005158150803007100c2c461540e07509000e00e00651240d40d000051000f40c080d006e18012101d00805012034141c03242c1e0780c0d00402d1056100512110041204038040b00380c4e0340c18000c509625108015405814002e1554136001003c0b0f10110550340141c100d40c120500500040081414000c0c49042a55100c0c03540340d01c038a01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 705185971 1250 705184721 705184723
    0xd11031b0111031e0906060f010f030b120106081002041401080709090f0c0305160f11070b0301090b190605040b0306010c0f21020303010f0e07050409020c0607030c0f080c030603 78
    0xb0201803644041c0780001070100d440e00329000e0424005000c48a8100b9590f4003901c584c5a00d421520641c02c121860030380c039019885150101c0d49a5018100021101c2a01010501d881c9070641c070b802040c0e64031501030040d8482040404003803c80c080c403c0d440c160500070f03a04a80e1560701005414440f4100210f2032040c0908030520140c041503008000d225108140c45021f40142c5400070003080c58100801c4100c040400c1d840818503194481d44050300d00c0705800c40d504100c00d070399101c040c051000049580d165480c000c41c001d0040030400b2550404071410406041807160a128090740c40c9241082031680103c00c0d2012184000e00d115200e41d90840107075412410400300174030844075000302c1d0040240040c2086000005141c01c42011444507100340d03501c1c8802c0c0118100b90703d52400410056038001412030740300c1040e1404a00341941c800120090f80c01071000001941c100c40100440181d03d071003201d255034000c2c40d06046001042902034110b40703010b88108500c0e0380020000d42c0e40d0320 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 705187221 1250 705185971 705185981
    0xd0f03020322050108060405060109051005041710060b0406020604030302250507030b060406030c1404020c0f0c0310060e15033f120a0b03011812020d11031b01 70
    0x526100c55400200b0401092802c201e00d80200c034042140d41001c160359003005d21030540300d8032040e121602d2950400c403c0152b500450140bc0e402c000b001c21000c00c1d001c1d422800d42c04c40002100081001d440007802c01c8045c0c90080c2c00005a8400c1404104503041d03001594581054040c140140d4560b2070340c5803100d60011004041c41141210320f601070403c200082c1d01c1c0d007181d009040000003500c2d49001c1009482c190b110182c2034a800c03c006025134954034070402d100b0600203000515088401c2402401c0002c0542c0407040b0344c0040800e1141d505041c022381214284d054010032926090600641020001900a000701d500c0b0403080c075440c5e1010000308001001401844446040c092103d9400c64008a17404120074140c1142001144002060350651840782d8082c400384c0d40c0782007108001b028203014499140d03480342e160a1490360140300010f107041c040c64600c0702c000f410301d2001e454400c42c0b0110508000d105068210141c0e000f00643d10761181d01095240400721046d00c480c0940 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 705188471 1250 705187221 705187237
    0x907050a030c020a0c0e07090602060105012c090c040e0a0207020901170f0f0706120902010203271e0f0316140402120a0603020a0b0a02030304060908190323060d0f030203 75
    0x1100b020030226004441307040080c0311f50711070303603402860a444001c03c80e143c0030284200c83c085082c0303074103107264440e9001da44583c1503070145038040020480000603000ca44140c40707a5240e4200017505001a2090041030b41c0d0168140209614000c003a902081611105100700f806074560000c0e815030f22013003400b250281c0d0b1004070454122440880d02107458030309510400300450f5001003c1880944140181001d080d0160051420440d0640c50000300750940c41c000001144c0c601c0b2040341c940c0d60000400c1d0050500194058418291010322941d1040d051041d4400c0d88104440c001b070301c4015210205036110005001d00c0b000101c0b001c40c01a008204110100315030100400802c0911a0700c10380480c1c2c000c403280d1107600d030398000c499114803410680c080142c004100280c0890703066000821200c1c4142001454003a40c8040042d6030203031880640000703512040642008240c0c21061441c003451841600918180100007030700400440d10000c01d41c005004101003410300a00940e0014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 705189721 1250 705188471 705188483
    0x3030c090d0f1a01061d0d080306010507080c0d0f0c02310216120c050d051b100501050a1a1804140103030c060f060806040224040b0304050c0907050a030c020a 70
    0x243c005000180000009024840001c0c4101c0f585200c40070b0a412070700107500340a440342d81e1000e05600c030a0b00a42c4028112070501c01b08000c42d800190380d010081c01d95510200c041c00100701c0340b1070003c01c50720702c2c40c1c111020080800e4100000d81e4400f0200f00c000c0c2c2c26100d054000c01014054203d00c0e007480345004032494404540a00072800000103807140900c01e158401c4003030b00d8001c0559220203540005006580022540c03040140202c0042140054194110f8010558860b0180c40c6ca00c41254240f2003a46400c0104520309280140780040c1c43d500c10020b030350b220130082102c0706004840310344010428134007900f40c840d140e0b6445007404d002881410304c220740c3c4a003005004841c40140484000c0c1ca480c08081100225128480903136801b24068139968595400308118095254a80c014a44000d401075281d107584d24020700c02010f100c034605450345442d092850900103201246406044510b04000300681c0c02000c481e0020750340d040c001100c3c404a07100702d1410030603040003460 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 705190971 1250 705189721 705189743
    0x50306031903140c0703050708161401020c220f0c020c04050604060f0303050703020f070e06060d1e0603031206050609010c080405040c050903100603110d030e030604080a1103030c090d0f 82
    0x80500301044172401c1c0c1c0c0c0200100c0d142c25a54005941c0e4503d1054030f40c1e240341071002414400150402c00b10481c140c014412110300460000024120314901d9407951b000d001754044414801340c213400f60300c0b09012141001c110303000d0000d001030745a145103081c491050390f03180009811651036a1045026040e04840c1d030219a84070315018009900584c1d041c1c000d486084d00c1c050780f00c000000ea000660b401d0400c1d0030010b8030742c00b0a00109070000d035039a81c02d4548800c440800303d48220840d02100c00158408540146035050191011815903809981181045000d100580303d070400c45504c20028600022008060701f045070311750042d81c1115907c2410301d0985440d996002015010b03d40003102590842e6482d99111310403a000ca00c0020070055040c03c4010031450b00c03510001900e4080d08000a02d40405400a410007804607821181c1941c0401d0000c0040e5000c8060106103071120000c61440c20140c051440e180034054400c4c0c420800c40101e0070130082c028404500c039a82c0325044100c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 705192221 1250 705190971 705190987
    0xf2112080105180405070b030705070b07081e011d190e1b030303190c020102040503061801050903161b1d010302040f200a1b080403050d05030603190314 67
    0x2105240c20321607140702c1c40c0035074040c1c0484100350402600481d4040300074041c003450880d00c001181c1004103560280181804040702050310405070301c1c0310b01002da8481c0d07020714040e8178035400d0300b00112008030107081c04001800020303e04080c8480000902044520554990318103080c1d480d80d16221007149400c00f0b400c0030340d54000003100282201e2a64022480700a028103160f500d0200701c6035080110b880310706070f804003819980540c000e071505200145c03030715840d113000c40e113401025281c0d06550319680c81b004081c1c400078481c0e15085070345280694900b4090207202c50b4020740c00d000140504240307190700031703800c500712000a0007400c4a084204102c40744c2291200c2040c024801640104d01b08003c40c0105c078a14440c040f0399400101c0100c4d6248070b00c1000340330030341104c1519814000744c1c0940001d1404070005c40340b03c00d841514a255070740d04610f0f01c6030500800360b6001c001e219043c0207020721507034007007001c0b060b03800d0a120341169041141000c440740413020b03030300455041c00019000d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 705193471 1250 705192221 705192227
    0x1021c09050a02120309011b0b1b0f070f06050c1e03060613080c030f0d1409040f020408100b040606090b181201020a08010e1005091b0d020304020111070f2112 70
    0x68034030426248d00081001000155040f00c0000790003d010085800002e00099860613843d10000e20852211382088031170903100c0f01652150318160b91300d000c04005d040400105008083d4442480c952107820a062801e48011041d00d09a500545080110000d006d81d02c5000c01d40303003c02c0d82c104a56a80d66503c216050300c0d0503034140d1881c00b03800384040c030108109000407464051041c40d0f403a05441144c000c10160642c00400070703241d100781c0b200c00c18461841a03001900281000d0000740407001c1d4092515021107164140c1c00703000e00d044c0242005407903003010f10b45084681d00702000d03076600c282000512001000040f090341c1302c8090642c81c09200303815405401d11a01c15100e2030401e980b9891360b0a11200c1c11030304900c0c1c4003041c80d4140319604019020980028400c0e2800014559400d400103003504400008000103502108000c15036901c0680c803420102401c014002c003070704015003101c0300801c9001d455101c000c0c4441440480d465a6800c140094000400310898103503500c000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 705194721 1250 705193471 705193477
    0xe0a0b0603130b100b0301090b0301060302030a23010b010e040902060d06030809120f0a020415121b0b190809121309112d09061804060801021c09050a021203 69
    0x20341d41030083e0000112120780c03442e918810b840f1109001410340e8a40302e440350160078402015034055481e56000001a2010049010240d1187d40c00395100185e42001250300840c8843c0c01c1026818100d0965550b604083c0420380b0f80d0081e54049586003090000c0313005445014081d01c1c07001c0c80e01c000002032000d002d0203004058000c41e04241c04641c45840e05607034592140030300000d9003011071458014607095004d000321607990103010324002d80e02d85400c4002c034240e010942d2044864030500001481d018068000b402100d0185401c00340c0c0742040b03025801d6083c0b00320f8144040d120100741d400008014512400f1030340c00302e5540c2c601c100b11035400031424030b10440c5080c50520400301c03504800e680035180e1507800700c07106002c11800014030018003054010091000c2e030080001d05441e442e01c00044c2401c000d02c010080306060041e0038001103505030740c050b000c142d105000641e101310103c013106000d0348c1c4d0110040f489540d20309040d81030019400f0300a521104086440001e09408001303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 705195971 1250 705194721 705194723
    0x4030c0203240c0d090c060504050a090207030e0112020906071a070c02280b0403051515010509190e180d0206070c0308191508060a150e0a0b060313 65
    0x82e10b220a20702294a040c2101850150400e000030000042c80e10b00d40d5405811401005240814400019210705412a140b0307007005001482c0050140300351300700100301000030314414208528008480d10300501e2401c104604a0401c0015200312440800b5901600e11031500248803d940714890319046c1c0d5000031080c51407980745456000107484900a00e01980042d801502d20800004c11f2540e02422a40091200c482610a28008a40e0780300c000e019001551203180141203c5901000001c20740324003d0229081246544401c545a6440070a42d1800c0030261660410466240300041508110360811540322292104114110100c040c000301001d01410988200c0003509c00c003240c5a41040f1904000b01f500c5488200020b8450030459920500e4003000000c1a0440d01c0c2002c10b40d2a4807030800654500d45109110b01e4800340481c5810000504e020482c070000d24a8508070090320f84103920726025600001030900080350850b08024400800c442d50304c0c68411200e000700c41510348 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 705197221 1250 705195971 705195973
    0x4050603010213030f03090f0e1e0114010302130513050402130209031b0d0b040b22020a0302040b061201090f0f0c0215130b04080904110406051213050604030c0203 72
    0x4089192410180700710394108079010310706002c5034110744825030208000b01c1c0403010410380c1040000c40c90803525003140038081c61442c03000c00d414011a0511a100190114aa45080f460041000e10b40c1ca400d00402c1003c00c0c02d015843c0d0145186400c01c07180a980070580240100310441341c03000c060383c0f20034403492003120200790384401d5000c00c90490213460070550b0140e10450700c0c4c09007507251000700304002c03a004003e13008035400359440c01c0c8181c4007528100e40e070a805000b4030000048a8008004035136002900030440541c90300050341a0010303210182c029540c03110300745150b4890808031100c03d102d09020a80300c1d41c0d240701d0540200f840b0b121220006241403a65543e40c43d03280204240c0607159401840f0980b042008903403a507201401d417a1a00384081501c800051040184600c10703801050a035032541320314400e10050315560810104100410081440309170b4114050750181070b0f00300b1050580d07681d04d0704020a210480e0304041c1c203d200c0c03c01000708159000400c122018400d030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 705198471 1250 705197221 705197231
    0x9090a14010e12190e040b13140108010c05030c0304050309090103050c0913080702120f010c030603020f031603080f09120105090c060412020d080d0c1107151b021f05070204 76
    0x10804040d071301404040c80c2e4800038002c44034100b01d203e01a03007607003007500a00000f032003c10b1000140004a648a8009545850f0020204c00d50f8440034058010100480240107c0e0261a4014410312000f000d03461801c0d0048003241c00d1210030030640b403003648040c0140800356141e023007141d039604012443c94410034866000521302c5000c00f1030281d8040d8448080f40c01c0c031016070700300000310003581100050392007002e10146902400f401140c030759444a880015107a1300314010301c800c45410701c01081c0250301c407207074840c502518105a02c040343d40001403542c45010703420201c2c110b0b210b0300d400c2541c0001000c2c0107821141d01076201c2805030031454212a040402d84c820f0100324000c5114207945e0603081409400542040c8403095901849000b070145010900b498001c120360301441c0c401d000400c02a5400c82d195001c0203044041c2c09184900d038001d20174401e0060400b0100d400c0308425190810310802103480392001c1210360326401d250500d89103416240100960070042050380315034241 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 705199721 1250 705198471 705198493
    0xb0a030311100204360f09060608030c0604120e0a09020a120902030c060a0e090c12181b010c2103060b071502070804030b0c03010603050a150509090a14010e 69
    0x2803080b281103800c0f01003a206000d0403182d081c017150031009003a40f001201c00c422034044084038859440516035500c00050b100300ca0b401c140c0115020303074110708841d510400080c040c14100040e00790340980d110607152106002a42c00b1182d105040f1030058000f01d0b0420f0220f1a6007071500501042c1005590740d0310a4440c0c4c0038035500303682d00c1190182d010782040b41495080e091800c02450703022842d08101d000c10010300302003800c01d64100d5455000001c0410031211200c1c428100a0b0400c003007040400e0710344016150709844411010000d9000e0340c40404155040c0d00030319100603101d80254039126900c00e0b051000d01305054060601000a00e01240814104054030640d40ca06400540d00807109242c841c020000b9440b110056510341030500001000072000a40749205154089403039403030754500f2202600741d0b0006440f5140c03150606020850300344290b03820702c0c1104d104071003501c05601d81240007030514a0060f006041d004582d040718650110540040042c00c820001300d40204801c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 705200971 1250 705199721 705199753
    0x3021209060601090e090106050604030c151805040203041e060509010c051e031506070606080c060c030733060f06110304060c0c09020c0a060501150905060309010b0a030311 76
    0x708a52950100381c44400521806079506401079003c0e444030000a8078684500000b9883d03001a801156039200020f400e01450180314040318440340390342401d010001c1c20015041030340341345000c1c42d401070794040005410700c0420500c16048456500c1c00e04a04505030802c03070043c140888010082d5801d0042404203a03100c0c504480002c2c00940d40d50080702880c51480030ba40d0720250880a01200c58909040182c0ea03440c004d00c0110f00c22100080c0003886c00201500b842c000c00e090728800d0905003c0300c0300c5090702104132100560b2150907982c407606490036035820301640344c55800840300403503950420800c80d9401402503603030420002c5c0089666080813038150102d8543c80041e0b0b00305020800005000e00c1940720201c2c4a00ac05000d21030311810740340101e801c150310410065102d8500e040138403109200d0240540440b40c0b003040114041071014014035601e2103094007640f800000201240707001c0d40080d294940c01052000c549a5034200140b40784141c1c544402607010791815082d103d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 705202221 1250 705200971 705200983
    0x519050f090f0a0314030406080705070807060b0d0605130209060402090d0b100b030411101404120f02181801091731060311041d090f0d03021209 64
    0x100c140401881c20580030140320410b0040d120507500a401100c0100019001c40011042030266000840c3c981d1715106000b0400303d409458242400000c00604022540320411200d21030341150020039091f0070003020503281d85011074041e011500d000309000300c0c2d22442286000c04e500880d01c502c04d03500c0340000c000032840394220391640401d050b0050b1002403d4059596400b40c00d203107610888076512240b180565004890495602d1485403c0c00c030b203403074105d1407184081c00c0352078203c00059100d9007401d0a8400d6024448202501c409c44c10200800c0031001840356501410100c0412600d02192000c050207072150003c101140050412411052058072001d903001f41d0300c42082c4e400900d040d1035a621010340d20b00c81121042c07103403a8004040e88040701807081140c203480c0c083e1600000400300c502c004521420484c080004004c4185460700140c00d106818420250036240c0c80d8285103882d1049100c003510f03000309040601d01540541c0940700c1c4880003804121107541d03900120741c40d04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 705203471 1250 705202221 705202237
    0x10050a0f0518040c180204052704110a081f0b1c02040903120c0903051009081b0c03060c0909060a03030503190b0a241812060902040c051905 62
    0x51458036418a10482000502d0700b250041c84e0070b0048580303c0c0c4122000c1c080c01d008001d962900000c00700f1107420000b01c802e101d01031150709120380320b02c3d24000913032181c409440074183d4401c8c515680002c1d9580f261a000034503500084400d03010604010b03085102c10404225821850030402c80882c2c100409088070120890b04100028070040e400c0200a0070f80e008180c0c00c1180ba01141c0c071041c41544102c0241310340b07031344460104510318036006e0300d000d04940a18200c6420a000100003441050686408040d8624030242e60000c03444110f181100701c64156601d48151418403c003010140d0092505e20800c0d11002c03121f98820040c841d8240b01c0c2c0c032005001400400000b0a102d00395690003001c85507071f4101003140c916040c00102030340016001000e89901c40480710480313003107070340c0180400380d8107081c00111b40308a00408890f8410a2007001034107070361400210304001090f4000d49ca82d42e03004108119501900320b0040150b04440040502903c0785000c400f111406030b0300b511010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 705204721 1250 705203471 705203479
    0x91e03030f030c0201331a07020d0f0501150801061508131a070201020d27080c0114070c050c010201060e0604020c0f10050601180e06090403050d0510050a0f05 70
    0x2400c0560040b401040c50f011040115562030002c0c120405184800d682030821400c5040e03062402d02d400400851403075030205d882c2024a0446049030000c030001c1e940110b404a5150407484240e00b40b88070a4881031030000c0880d460b0240c007082e07040e04503480205030b48045000300800b40c0c44200302d4803441d403600e9034940420196000540003036158140070710080d100d84164102002e01303800d1611030100c2550071501603500800c40000c502c40038450520180305000c105088103000703500910382c0562036170018141c0741000035400d9202c0003d401600001c0c150600c0040c01d0710301072a004040701210803046a050041803c070320115841409024143c0c0c44030103044801d40c417203504000c001d50101446c01081d0003050440111410240400f00b800510741501050902d030000004184c0d000000c4a0340480036050002d0050050604406900071070a0b40c002c0000e8440b42030650361030190504c0700c005a800c1800304200d10200129003003c0720300543d41c0d5007801c1e80341d02d500d6041a40d18001d490300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 705205971 1250 705204721 705204737
    0x2130f1a04031713090609140c0306090c190c0311150105060a0c0501050a020a03050105030721020f1c0c0b0f1c020c070b0c070504060305100e1c091e0303 68
    0x464031032030b9044014032200c940305141a65200c1060a2904140c1c04461099600c50081047c90720781d00440c0e040707501da800c2c9002207240c00940302d000f9020291206020720096000100702952407411244481000064009141008500180070754007a10046001952941d201c1192542c0000c2c108414000300180700300c07503030804080c8071148c0c101c84000303410415009001d07004141c00b88281c030301800c0d241d80e0150741d9400b109406010b617078060740490b02a0b44082010006503c00b1114071680300c2c5a0548829011004d00005000c800401d001d07590015486c0180341610380401e01400d0f0300d030705c41d201424119039201420f8440307004a10501100e964100302c481d0703040e44490982c200c440c5d0150801818041082c40346850280e80d070f008114180d00010381d92001080c20000000100b000702c4092020904640d00d268071000c05800d80c410194468a4801068105201c90f01c50080c84014a44070202c0c58100242488414402c0410340c0c4152200b8608900e0500e4048098035059242e01c81 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 705207221 1250 705205971 705205973
    0x1e041211151b070b0705060f06151806040315050615041203050c01110c16080c0105040e040c0812070c080c0109060807030b190e0601080411060711030102130f1a0403 73
    0x1280003035110811454000c3d000086401001c2401810b0b40d00c0c0200000d203180e1416404074500d141026044c03510541041c00c016403188032103012108100c0c20440313507011700c150034000b00390f0301d00682d0001441004c013841e45c0c41c800c001c81da1000c0d1140504482ca510740d074100760404a0360b840f4078040c03058440d85505000c80840e02071802090b1410342d00c0000500a4014070b02450f60360800b81d89121950003106403241401454005400601030a00103060140c241d0000640315114078881c0d402070315001c100140501a250001e0402090000d05441c2c0c680e06450b041e00c42a07001d40e40403038806141c11004a080070000401084940c1c041c0c4401c15901d00b420410f48132502d0083c6014101511000c2220039600c0385c601c00c0011294050980314004e04000c00000c007e80001c0c001d03410040e40b0b600f08000f18550280d1441002400d942d40396940c101402c02800504d00058030355055030001030030480d141080076000c4100c1d50001802c48a80744c488050b1700c0c040c0e07000c1080d00702e115800d110501c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 705208471 1250 705207221 705207247
    0x50f0402211207060605030d0504060207050108070c0204050403122a21060803090103110c0c041e061d06090403020c0108221410020408070b1e04121115 67
    0x6106400d2600445050400282e00141c0691241d0412551507403140d008229500b410016400302c44000c4c1007a41c03e060420300025500c091500c901810040f12401013075616000d02105450380340c010f801480941380c50f00b4058030300380540350f140441601e00702c0700350f41444001f0419009980c1502c0e01d0203c803015094221080d0101c85400c1c00d00304540c1d404801006024331030100280050000340d80c07100045400901150b50301030307c0614084c401c2005000c60180401c2d00003821204540008501e2440e0f00300d1841c842a29107044002c0d880d200c40031420b542401b9100c1047d0f50480988001c1d503984d0320034045501000c2e54001d026034020031441d1850f44c0a00e10700365000d02d400710340807103140300f42e82d03c5121960b0082055440700b05a001104a000041c0300190300e442c00e604003580b50614040307800f41d58948034480c88094070030200d5120120083c4c0e10400c0305460402c490b0382c0d102c1d42c80e1003442c144454849070848126905866900f50342c1421100320036030403011844c0c2420303c01d68007103031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 705209721 1250 705208471 705208519
    0x3071b050402070206070f241b05030609130c0f060822050a0b1902070f022404062609241e06030a140a06140c0703050a1b0303050a050f0402 62
    0x221007600c1e14100404100085440e45481c0008c482804a0003804400403485141c40310000c0e00c0810400700b04200103900d80c011004d411440e2a404845a000d050030a80b2921040342c000e03041c0203075034807800504964072101c468042c6070840180e03090b15900b610030420840c1448001029a089100100041545441000d80c080e10840c2a40001480c04000740b0481c3e202500440d0070807418a01001076061490481c940079103501c13500e002c0107560740c038860807501561003014200044000d4240c00c0c15200c82c0d600a0f801c114a1103594681032280c2c049803071340104900002000044010002c02402c0d05006500031051040190803520101d080b242c000b010041941d90140308990a6100103142075450380b030104060b0025041c411007518191041d04d61500071124048011401e006071080c01c402155900340e03150424540e1180d04100940e00b031020440001007265601200909140d05500030b00d1140032121420415681c0b400710091404500341c501940140b0641e00484a500702d400d43c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 705210971 1250 705209721 705209723
    0x6050a050c06040b010e090a020303180402070b0c070203100c0e1302070b0f06030d051806030601200a15020c0a080310050604031b080f0d1b0503071b050402070206070f 74
    0x245071449a91466140040075a4129a07601511004012092001610a0f04810070101408400b039a98000991f00d00480076082d085903aa9009940103039203e038100c0d10021743c81003103010746181c45602c0d80c06035003040c00103a0103801228a4040b07a060988240f5205000315141c8410034124141440040710302199a261021f500f003050b81e01083d0070845c10762144d03a4014600c2490302d4440d0a05080640f60540c41051040920000c0e80ca41030b00c4000440001d0152000d0340c40340e650800403a100e10341115502c6110645a05080000c0c6d8003007411401a4010540d200c54030021481d15012407003030200d0500e80e60040844140090407440045400c1000e560520350000c0c0c075580080c802d07038004d07030040f1048494400d1050b204100c2c03000c410010155400034012411064039140c3c4c036070440d11074207420014a440c01180d14564110045411500b207401c070ba48805071840c04403081209180c145403418014100040c0d0b0b0300c1c181c001c85074002c1d400390056007070a50940e9043c000c1543e88170 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 705212221 1250 705210971 705210977
    0x11103071b060e100501061404120b09120f0306031501030b1915080c04060f032d06091101030b0a06120506030a1b0303080a0605220f020a0207050f030a03080106050a 73
    0x803030b0300940c41d010061803d01c4c941c2e8502c0024254500380e000b4114245d10030407810720250500c010083e00c214248242c2540390131044000080c0d0729100128200141485a81900c490201d041c008580c0609e01540c4180002c0d421100f50801ca030390018481c140901c00200441450f1001500b02511101c00118440301c2940100740307001200700704440c0e00002d0b04090301a81c0180c03585640703032819004600041050b00c0f01891200c0c1592030321600400010401e0050302d07140c0403480c208a012011041003035412100400c000030b413510f00010054400d0034294002030900c8000740c050f01e000412030742141c00540b0f480c107103142100e40c0a0090728005150315072500070030704440f0200d5030104118824525029940d88082e080d40f4001c1d02405014040000780740c90941c042c0040c4d06c455020b248041d021000000e68801d480c402ca40103403814400c1915402e00100b0b03201c094940000c0d080040e6030f000c4815541c064030b03020506aa4034001c8102a0000e071041004011143c00381c002402000f507146 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 705213471 1250 705212221 705212231
    0x702060a110a050106080f1b030d18030b04150506010801080613050703080d0509060a0203010f060e04180501062102030601150216060906030608030901020d080a020c0f0f011103071b06 81
    0x3c0c07141070031160f15034801511a01302d08580140c50000b0b0040c68651070312800c03100341c0300d0140408680d68490030003000c401d101701070418160310101240c80030000c43d40152105150700d00b078600841010440c2049a24030740c00c06001c44d0b0b0640c010070340203040e00d050710001d0020b540c0f006070513840603805180c10340d1503004010021000c0b4124100030541035411190104583c20840111840c110000308139070101441032005100780e007118201241103601031310b0a00080d00d0304800240c010300070300ca00d014240c9109401035003003003019009481250075038040019500c06c00b40b04100380b0f66401e040250306801800045c000418102d00d150035444040c4105e4030300c60294030183ea581c0d240d41d000032021580805003046100c4c4d04d40511130161804c0c0380550f04294080c00041d40d221611f400003810f0101d00000549401e40d180e064410b502c42072011200e418012400d21919060700c1c5036403120950900300920440380c841800c0324055040c0c0d0b0b4034a1020882c0620a820f41d00c039401c2c04988803600d807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 705214721 1250 705213471 705213473
    0xc0809061e0307080603070806061512151c0c090c02010e030d021e09010203030403200d110105070e0d12122307030c020709110403080a0c06110702060a110a 69
    0x404403410350341280c41c040c1c590b43d0400300c4004d800c80300028860351081c1d000e510309000020300030a5007900600c0c10b8407600c50921220911140b07600910441c040d0040b2004200000940501401c0c11a0174094624030042c00b03c3c01c800580c06004c2c40c0c00902440d000c55000c00c03001c46c443e0b014144c0b0410368400014210f100740b42040c21030307000901490102e90040340001c00380c02004600391103000c1e014a528138082000e0b0002c3e490b8000100007405014031800c0c00d8032101300521140030000f8602007a50340c24074802d100900981c2c20380680c4075040d8130300f600050144d406090620012000148205060441030340c6200903420702c0310f502d00070031041c018000c00343c0e848c50003040e40750701c0d810305546500c0b0b1004907443d608080c000d050104050070320b480040c6d11600451214180c9075001e002154616801ca02c0300400c1c82150310003000110300040fa104c10991251500c05024494402840b100842850740c414a0107416006503000500704204194a0300030700362000b844481c002981e20183c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 705215827 1106 705214721 705214747
    0x61e0a09060b03070f14061815130306050103060b01022a221e1e020a1e0302030a0b0102160608060a0314031c050402010c080906 57
    0x1851510406000e01900080740e01040a0100c83c201e6a4600220340070030403900c9603030320444121b0090005445c0560071980448000300c01d80950090010400007212500c80c061041e041341008600c022401d5196003100075809a00005032540c91070425070199500703002401e04541045543d4812840003001001d584006d00e051551500b103017102041605505e82601d483c040100020340724180510342040c0648004000004e40e010544450141175481c0165002c1e412400c0c11100720080d40203034094119203182d89070000b0f20801d8515000840141e040b10100000c2c0c00000704020389406024688800c0028801401019100548115410400d00610f800c000f40700020403559030701c0c03c402c8000340d90003216540c0c10b1071000c80e5071580d0f031303114604010301141000380349040042607200ba01d1240390180c5600a008016a48004e4503a124204240e44200140080200020 = true := by decide +kernel

theorem cover : BRFrame.Cov 705035971 705215827 := by
  have h0 := BRFrame.cov_init 705035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 705035971 ≤ n) (h2 : n < 705215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
