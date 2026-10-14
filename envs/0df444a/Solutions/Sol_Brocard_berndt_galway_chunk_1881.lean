-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1881
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:01:03.685409+00:00
-- url     : https://prove2.me/submissions/b5e463a0-596d-41ac-977f-c8caa1942583

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 338129496 ≤ n < 338309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 338130746 1250 338129496 338129513
    0x1b0f09020c0c0a03050d0f03150506030907081207060507020c0a0b2506021206090420060f0c0d0e0411090f060f07030201090c0501090825050a06030f050a05010308030103030c 77
    0x20b4203405070044003065a21704060b612106428070790b1012528000496110603c21712035010843c9200c541c120009041c0824002503810080c4196007611642e2004914464200880181016807400d01e903580c1105d4035101041e200d000c0d225100795440440d400903d661251941c0782030740c00c1d0f103a01540703d0044041d254042002800802119401d442d4030354140a415001840006c0046541c1c890301e4440100b8003102190880c0c005e0310823070b410035165440710b4042c00c2110f100200100543d0a000c001b0104486a61160301d2800c455405a89910306054000c140c4509802c400c071000c03c680c2030414906d54042c0316031040f15116098081d8550110303920780040d2204440a004055141d150619019008260b04001611980d01c043c03000a010342c0308000c260180c450070700281840c044c0c084a0b51000e500e00c1c1502d0000d1640b0514046a00c0c2c81e0300305000d0082c6102d65010590100720344c070400880b4405010a5030443c202030060001c071f40007104680c11241e0500c0c0413240c4458a0410101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 338131996 1250 338130746 338130763
    0x1120210030f06120210111905011b0f171504020903030d180308010806070903060b01020a0b0705040f050303040302030c01180506160b0601030e0c010e0a08010e0a1b0f09020c 77
    0x802c1d40f5100c0e0110b042420040100e500300c1c4241c0e221002105220802d40d480c00b14803c0707860380e81c2c0c070030565000b441074001d08860074148180c0000c240c001c000500f04600071042e40846000503090f1442d90341280d130001c0224041d46260701d01d900326052401441043d060021012030169400041c0340e40c1e991410401c0b10740ea4186440c00300300004000118916120b00c0710400da00103494400007280c0c2d440c02142c228024101500c6981c039032031550b030301c0401800248080c2c60640c05412440d02c003141c107450b0720f984260115691155941c4c10329104401520230b50300030b14000da000b0b10080c401600d00180e240c3d2480c00909001411051202f007a130101905c03070700131350740200b00480c1d40305e22400a070000d070b080684143c6150260307664500044003110b1203c803100e40f170740c1c0c00000122259400b414222510740409003283c208580c82e02d2229003525000300740312266500189961084c4a00c0b43c940c0011074803010032008c803540c80e010a201c0c0e401c18a02038002a0390f070024140503070010822681c02d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 338133246 1250 338131996 338132021
    0x10f120606020307170412140c04090302100c090b0f1605070303020604030f1d0145060f02060f1509040309060914091914150a06080112021003 63
    0x400e081e100d100007501da800c07900c0c08844982d01d48501c41c148540840a84c1e042c2c0c1c01d00318002c2c4110701c80d0345803030304881d00000c031b0302c0b000c1d0050305904605a1110302400c0d060500940090803042c02040c41c0c00201c9107064a091300b0448244018010100090100c0c0e070414141604c2a448410014030340390724130b080c000010910310910200004150b0040f0360315110341d004e070302c0e011b01c400b8424006079452400c0d1080318006007407454000200b9805074242c01264064040d0042c04404040d078140c450358040016100340c0c10100384c1d44665010982601c2c40904418030300420760200c40840a995244060400f40c80b20480600140c902c11038005e5648401070001d2034000315003414100035010407540e00a050000c0c09910000c10001c2109100000c1480040c0090303103140e9841140e841080003124204a071951107060525442c0720314a422805154040c1180e641565014100128088207602c004103000707000c4010080c2e10410b8065407180f80e011703154100c3c0552608000c40003000c40340b0481c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 338134496 1250 338133246 338133251
    0x70f06051b09301014060108010b0d0e0111070506010510031509200409020c100608100906021306020607031404020a0b0d1d2410060c0f0804140f010f0e010f12 70
    0x1c04c103480e4001290011494a0140319901d071003004468003082401400c581c80e404110140c2400b00c00d9004041050008000060140c804000c204141c2c1c403070760080d50150f2082d40180914500743e020038405048d141010059a0001c000d0142c02e940c192080e145031300d6a403610210292040c85a0000300e12075102002d90703560300d801d9610002d4008812045080c40356403400c43c08040700d481130320306a80105004000300d003880712486010303048070101110301940a00034202c2c051401501d51f00070b0720b06278000c1d008616000f50010b00722134180c40780502d494000801d00000d40c440428180c00d45400914035507545041000c050047d00c0e401c2c40f40c541c01000c0e40c80400c80c0703920100e580300e01c0c192161511900c3c2c1920717295090503400169210102c0d081500d908000e0107000d00340b40c180d014840e42d000c1c0408000e98075200507641082c0e0103420100d104585845840c43c0c03030301d1091040a400d080c200a9501c05400080003020320159545c14848241c8440315800d014000001c2c0c28050500309 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 338135746 1250 338134496 338134513
    0xd082503031a0109060816050409020a110d030203011802030c070c0303110f03190c141207110607050a080d0e0f10111617070f06051b0930 61
    0x1070051000b2801c0d03800120202442201c158424000881143c0301c9070b640750290789800380301c3d0400e4042c00341c0c0f05040c80700420000035480d4286c0050035428030359031103040c0c000c0d01e00700c1d0441c10720301e8000b0764400301132040006220045411900b1031610712520030050f102da40c4d009048005100c2c5440103407031900400030000c10103174442d180000c4c0d04020310646059100714100e096a9020b120034807141640709201d0130149130700c25040851760303a000341d000c01070540d000d0407502c0c20000305440180c41810005500c1c0e00f44540103c00c1d642018050700c8545c60508162201030701d0390003c18008084180014804101e40c9680d00180c203030440c01010784100c211b031312004580c1c8038460240c012500b410141504890001c182c1983c0c012010212032403003c100690783ca10302c43c0202c40c102204184140003140100d1710100705203500600c038a10010311810800440c2e1034403605460303072240c40c0d801001120700e02d80b030321880403000e140580420030010200d082c8000c514408040311125a10a510f074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 338136996 1250 338135746 338135753
    0xc030e130905010621021c0b180120070f06021b0105010e070207030f03050d0204170c01090905060a0e040c0e0403022a0109030209041703071101060806060d0825 71
    0x4075540861103000200107090340c0d00110040d1040070448254170300300910b4044054100b21205d01400641c011100b80381a0150b03840c400040c4042da41c985004480c010701085541091059071030b202d000c41e55610a5100e030611a24842c45019001013004014421000030001e03640c06503400a040d4488010340354a044030068002c0009229141d0400d8402000c22030301070002c107805003a0780e081210707030610b10300385d440940392640680a0207051070b40c20400007410409004009120900d680040c104214400380010140f40f001c1c0c0080000138940414081243d4071518100308071401444440090b0740c40e070901c3d182d042c1c10f6a0040f5494810304d010481096404941c0c250658011046241e1030503000c10001207050b00c1004140c0818299030040c03026250040030180c0c014032650a42880e816030502e0a03840c0d03001a50504082107480880c0c448444080c000c4c4005003113000000c180710320701140000c2034090003030000340c200480001c1816820360850828580744001c880e603071315100028503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 338138246 1250 338136996 338137001
    0x906040638010c05010218010207090b06040b1c02071a0a0e030a11010e030d0b01140309060c07140a030f0921020d02030f01021c05090f06060f04090b010f140a030c060c030e13 77
    0xf1f80090040c0904940801c8911051040c140c2c8104050301c442c3c201030074204e40d6a035540c40051010102c40241c8507086540b0030382e00086c02d007180f043c5400d410050b28080c00d450307104006403401c0385950070a41424200349000040d1614139689103030405110b000301404038010010400ca95070b42d4040020100304001c1d070703504011020700003a42c801201c010803a512440342d02055800310404c0d0005000b05000088480140c000e29002e641d00e10351070801035050600d0602c440508402090120072526111500f007005e00e401458030724550100ca0002040c18241100d44080080c81024072064400564404200c0d80d1210946c0030021555480c5000c150510710600961250100e41408000350614401017100d1009000c1840100300300c3d26048100014481d15004840e003083e551081c21000c11200c9515600801e1444220f000c203a0a0481d03180c13140c20200b105600a81641400704002440b180301c120447d2000d181524040d00140740807200781682d16852580000001c2e02c0e4003003a1240e6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 338139496 1250 338138246 338138287
    0x40308030105030f03270141040806060d0c0b180406051813081317010e0a080304120e0a0312030b040b1309050102070b0906040638010c050102 63
    0x310101e490035442d00c2c54017030f0760340302d440c44403000b03130f034001d481b0766603c10104001c0ca000c40070504040c1e00740c10781c0c0c20a001c0d40d030803c810b492240c048054007032000c50a0031603040c0d040c802428042462709080a103800d40c2c40ea4094485409814012030342e609126400035214050103207140801e50f5005d6624014a0f140824200d00d0b110b1841c04d01d00041138500001c054414044d814008401c5680d41c03011190701380b035900d8040c0d030b600104105a1303240b180303494080c202800c03950b07260030101a12000d0b0316013140d6120f001d004199024840c4407011426800544e64080d42c415080340112040c5c03201101c1048625003450340003900300001000b0000c0c055505540303a50a59010852061002e08000559920441003508060341c8807030801c140b84a82c000070200c600880025207008040c0e81c17100f1282c00211079501594229106000c200840e50140d00c40d1a000b401003101715006152140325605460101c4908040307828203c48440e074010060301a12035042002151035103400c1d80303a40c40f82c0126 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 338140746 1250 338139496 338139499
    0xc0c030d0801061b20030a050d020706080f1e1801050115031406010504061224030c1208030a020a110708031308060405071a130305030910211808040308030105 70
    0x40003150713442102e143e070b5690001a048407030000300b6000c9245502e0b184141607680c2d6094011607945001140040000c1d90841045600810b0f2543ca8800e004103003960240440040c241d00c482030002c007080d4111441242c00ea00c4114580c60744500006800e0300f125051651625402c103000040e0006000304022200101a2005d100074000294110000300d021101c9501184050005000f054400c060785042d854608200003540d007900383d011445001200811150034000031014000c000b07462803298010804517103191519001580c6421860100401e03a180b900d501060789518984902488030851003e03405403800c2c907031540c1c44944c80358005000340c4180100034a0004e508180010010b200301c2d088000b42003003504082e04400c3c00310112854141d20007003403080d01450b40e9200461301c01940714070b0007107503a04124414400424580c503094800d0124002518900c03615007400c00829024004000460201c880c14500800742c490f14090b20304000410b02004200c0c0e01802181030350b90 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 338141996 1250 338140746 338140757
    0x509120f03250203070e06010c0b09070f060908071e0302060a0c0209010512070b030a0e0d03060303080109050403051e04180518032704181a0705090f01050c0c030d080106 75
    0x418070004108414200a4069020400030409190500415900650140741c040c0300103026492b00d40075548142c400c148280c000c840c04011543e003041080303009100b50300f0000071851802c903841e6110012445042c3e054900c0646039121003001c03444000c007559008050540395540028014038a00769038900302e018004600005c943c516098040303a94100020004040e600d05015400075a07800207010101d0380340e242d18190100c04401d0010100a40c025a000119030f40346080042c080340040c1c0c03000c0700c950f19201c140000700368000708850030403805450708212040305d002c04810301d00c1254000c0080c25562207250703254082d16000540034481820001c0000220041c0080c0c41f40703e450581d03008101c0552071540c03900010445008818402000001c0c0507074807400c0084001080ea400310303010b01c141c0054242d015a00201e84e50070030345070702d042e50074030604030045482c060010252506001000c42d8540e0441402c01104500c2400a42950400c1c0e101000c003a08102c0b003802040041407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 338143246 1250 338141996 338142037
    0x20a0602031315180201030b0a1512061d24040507210506060316090302130f0f0b010e0103020f04050d12080a0203041203050402010e09010e0610030204050d02010509120f03 76
    0x50f1503008140c508030b100818642c0110031030780154020000a54496080b9041c05e00005a401204456213500200ca071124034841e400d00c1500402c481c81ca411030001c4401c14480d80d50502172101c4055405441c8198050406820180d64030703142c011910350503481801c06040000b041d510400c08410a01a031415045130407142a0f01c3d801c0d1041190055003281082c000901035103110404241400f405041c2008015265000300c0c0000c1902d903514080035031150406428080d00d88100103a64a506004000b01a80040000c2c0b140111010241c101500420540e03440360500f022100100b01c000d1040b14446180d01c4d1000070f81c1c1d68050808082a4038100003880045030b4002c2780d01c0340380d005440030240304240c14160700904001d0803d074104415052040043d440b240d241a0103043e0006507008203141120400c030f041c0c208010f5110800d4014001002652528011111210390900305241c03104002c07008500a1084405444564407070b90640301e48801020004101c0381c0d55000740c6c2c520b01c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 338144496 1250 338143246 338143283
    0xc12040f12050d0c02120d0302090a23010f020f0a0606030203070b120103060510271107020105030117010b0a0303050a020606040b030c010e28080d140d0b01020a06020313 75
    0x41034420181880e0000f40310811071a1150480c144010b100a203c8603604d40750058903440d003a41c4803400d80120b40c0c0001c1e203034407901e0140e40ca23178010074207056a2507440282943c840d490010410450341482001450407509a00074044492030720b203050200c40c681005820400301400003031209038020301888034003240d1801d00b9402c40e40f00c0543c000342c41310164138698440004007401048406458005040031a08500104000c7c00d580d110701d41003490310b51356610041c1125800c0b10900c40c0c00c0c02c01c100d8100140d070058181c81c111400b841c1d280c00303101c800408a5001d09800303880c0e142e010522003400700070942c00501411680a541d801c8620b40d5880e40244011600200c0b98203906500040c0700d5032580d031241d80f045030b00c420081c049810b54200780c0d11440e0118210602480c10440c401402c0c000c2e0a400c00030302d91207610b6490454800c0d4520346190340340340302c3c030220074103941d4031000400016402004001140b50b8002c0c0308541c0c070300e040d40a980e540c2002040c100c4101c4402c1d034500740e08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 338145746 1250 338144496 338144519
    0x3040314070b0406180b0d14060105091e24040305010b012307020f0a14010e091e0c2109010c0c0309090f0b03030d060501110304150e01050c12040f 65
    0x1903a95403003802d880d150600c001550b0f000440010f1001420510b840400c10707183e910040d10160f905c000000c1030300a001081c4e080e1503032004010034100a8140b1a8101c1c03a66901c50901040c0000745c54410700400c07031408620301c42034511100c44200124480c000b030983c0708500400440340280000c01203000c0c4440116010500e0090503480520a00007207007404030a8002060881c0c40207080c0c10301101c8a40100e03103c4940da03030110240d8641e0185101c03075560440d140245000341155142598a46100743d0360099113450009010030301d0480025509115940c2110401a44000d41607030200d00a01100e5140c60110342c42101542449a098401130044280b240e4065058941c4003a00b41010004d8004105840a5066054681d401010039441c03d01c02001d07280c1c8203400201d803941c288000500900c0303800e5440c0030942e000b00001c00016100d0f550302e10300c0200c14582a820700c1d06c09001200d01c1e0141550424181c0201002041070311440c5008004481c0070745000c2000076a202190220b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 338146996 1250 338145746 338145749
    0x2109090a0c02060a1109040f200418020313050a0602040f15081807050d06090302010c080103170f280e01020a0b0c030c04031202030a1403040302100f0209120304031407 74
    0x940d120740089020413085800983c1c20140d1074100d181005100320001c0e05a400341c058090325950789410a0080c1c4048c01041c441c0008081d000724902454804031101301000008003200c26030b1b0100205100101c071048050f00c940d0014100c9004900e40e051102c0294468030070702e03464086564000070743e814501c442d54100031190300d441d11240c1d01c0059620800d40d085d00f038569540660000800c090b07031740c0d910740c2844038010140003d4021683ca0081e085404100040060003001401040000c0e80a10341c0e04540a011550907103514070040c0c03000351405a1304001d0010290146032030201035203134280500c1d07060260745100b00c00080c0c4006980310205004003410200800c8005608400c1032801950010a03c5d001b040c50036540b601c401601030201001c810068000003a0a044280d0168120484141e1100d0152031414035540203590790744002004805980c442611016840f090ba05448030404094010085901801021038890b8001d0000b1038810407411101c0290071400a1100d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 338148246 1250 338146996 338147021
    0x6060306060c02091026070e2206020f0c0a0605010e060f19240305011e210c0b091801030f0f1b060c0201021c0f050c2109090a 56
    0x1030104810340034402400801015050405c1c043d810026100c1100f40700740180e40b048000c540c1020481c0e245e09410103515a00c4814009420390501501001c056500520340d20710f10f62000a12481e13282c12000ba0040541c40c2085190106e80700c40d06d500081007801c07620b442020204407980e04c1da5000a440c00003a514541c00c0034440320400c0d0b450400421000e17480402d645640040c0e5580c080320400d20a03414196000d100c8241640032009815000d00d80c00b52018802c0c00c0714104105207a2011038080e03200f4011441c00101c000d20120b05408000350070150070080840d25103803a0840340b1010b51112020314055503070091044201b40e10400464142c03a400b503070411a11a094507100b021700b403003060656800030f52242071800c0032082c102e05001082e0315290203200600600019040c0300c9504004103010178034144d08516958000e400b1114040c90b42007450b1521040c02c000c0713103030032107545c3d04203400c2598151008241440074040d201313040c02210411060780e43c08000c1c80640b51404048c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 338149496 1250 338148246 338148257
    0x6090718020f0408010203090a0b0f071e200d09050109140f18041b05060310060f0201020c010603060605040b060c19031b0b010e010b0f0412030c020604030b0108010606030606 77
    0x4811800054000304542d4005030702480c101612003103040d08a0b401610410000d601096440e0200404264035950007840a0304420341803904c0c01b0058170800742a0440f1072841c0e041e01035448158001c0b01c6a0003060340142c44285000800b510055803914042c8054020401c07401d80058550b100310b1004084d00c0c1a48090081c1a0300c0f2818084141ea404010940c4079517000600c2c04c140d50b8a15450303100b00d005031070020340b0640400780400c0c0d450554001328001d0104104210843c070800d49034404650f41c62400f03000c10000888201d00a004071201d2070410f5090510000511640e604a0000e851080f141000141c000d9030800503031340305201020040b07030032082d081c01d401d5011900014560f4024242904004504c41166a2002d01d031f00044400e4013a60005100101c050741a45006d848203000440c40d00a8402d10040d0300e004070b00c070700e00c28095507941c41c604142c41a040b0030100c5901800b242c0d2102e403030b4508240008404d0140700400d603e00030001442502c24010442243c01036102c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 338150746 1250 338149496 338149529
    0x106021b0312090105040b070804050f010e0f0907020c0d110306150904060c0314160215090705060d06080303070c030e0102060f150f1c0204060f030302060f071106010b0903060907 79
    0x10b410031500044515410310400b40800180070130b03001c0017460114400d524a995641c02c00c010002c2031244610200e04000f034845448402d901c3e81c0c41e0b26044001c04807031000055903802d404900c2e01d500210705640290a4045907402c109520005403c1021f0840035541e00c0e90310003000b0802c44418100303950b8401340c600d02050100d400b540c002c0300d0384022403402040f001d803a4403902408040540c0c502012403c0303000c0c0c4202065040c452010084c0b80c01c5155070b40350603d01d08142d0384140c14001d10303204490010340c0c0000c03440315a000304001c00c58007094030384a01d41040301030311908400c20250f02007628901c2144041d0710102d4954841c100364413082e002a202c504c03a120344074061141c15a0070a140c40e44c1140380f80c0c0c0e030304101100200c1200007403000da200740c810701059441c940c3c00b40d100c01d20300c400306000107a008680c403503001c02103c020708025516000119601c400f400101c501c0341c0220300000c11070500600c000c1071010340542c119078080d1100341005550f14032500c0b03024540d4824442c2c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 338151996 1250 338150746 338150773
    0x6060b0906030c13090603080c0d09050f040e0c12010c0912030909020d091505060a0503070f0603091509050a0b011d070518130603141b040510120302060106021b03 72
    0x25001103083c00f0100c813001c9407200400e400303d82c4190026155180045601c2510820800503560001e18520b0018031181c50300300852000301b0001041c82c440e41d100e510840d1602010031042c1d0b40d841005209050a032a00c80700b00b4002e00b19011a1800106944008a801171b4001d5685004990507a50b40945518003841e10300250040c1c1c00701d0315440d4640110201003030340c0d0710888000e5090a540000c103803c0c21810083c1619455020750b000c2d4001c140200840c0e514104020211000781c240440d451455181074600a50030b249030300071981c9004100707000e01800041c0c00310360f00d209101700841c03070340c071070220001200c2c15420404240ca0105c0020303880c903101c1d10250150100f142c0d0810030840d9043c0c0000d10607002c01000044190751a4010000e020a0043c034660001c65480a0009054582038241d0700160384500b0030700803034a41012030780145c4503c0f2510010100300740d40c1801d400d51482c000f5141c09080c4510390052007071a4900c40d80e100014080c507032502e002030041004905800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 338153246 1250 338151996 338152021
    0x1e0309030504051905030f010e06130f020901180b0402072303040906090f1d300f030f071d01080a0b03060709060f0806060414030111130306060b090603 67
    0x1000c408204007400000b8a540322040224681e114403055110460700b440280b5251084090f20103849070b05000020685540200300b0540120080f0f905441e000b80c6400d01c0c40b018100c0c024000c1d00321740b034400009070110001d1b42035a140f0741440403c0c404054146c040105900801e00e02814410140b40e0300c0d106009071012042d140c06070700094900301030741d030720003a002c648095000c0305d00c1503201c0c03594965000c0c2500c2800c40840340c60040d40d0340c1e05905940a561010001030b11001040c00c40d6503070b2611040b80200a4065411200c055034800d80c500e0817508030b0f001902c02d2403194018101044c1101d000360b840340011503030b02c640b4a10109081d401160f61480241a03080c03220b079500423410140d101440078a10413080d6031107003800585091002000320040605e0a1b08201c0610284074807903548000300d0303040b50320329000c01d00c5e00140400042d0040c42c0649040104840c0015004180d125010f060800c07280585410480280c1d103880e034580520032030800c180d009504000003600c100505 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 338154496 1250 338153246 338153261
    0x50a061209061b0905030a08040b1303171b07050f0607080415020a230304060f12050a061805010b03070f021c0804111e150d061509061e03 61
    0x580c001c1584856511140101c404600c5544100314410b00e4501d80749030010550002840e0036030040404a44503100e100f041e0059020318908600c000514040303003500c01c1e958001454029814910306103000400b030056510080841c0b050440f42d40f5800540000407070110201e0b2406407000040d22001070030400c851f408980d04407514901400041943c2134960701c444444800c64005000003551130400d04400b403020b45440e0803002c5111001d41140c030000c0180d0307003144d441d81064040d640c0e2070441a201c441c4440e4807004038078500b1003008400c40f40d81c4c03c004201d03240540c1c511903015031000d56006032003090165012020b40cc2000c18100e502ca140b11204420310307441503510342401c0c80c43c90400c2c40d502d490046e0011390741400b808140701290042d0215102d04543c042140070400c040f0208441006280600c540c1c080f482c45400140540d08071403050900380c40402000d51900003820303078101036002074000525425404030740c40d40629038445401c4009810b440c44480566821030141404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 338155746 1250 338154496 338154527
    0x11131d19060f08150c031e0a0f050718060c0519020f0303120915070c02010c060e030406030204140d0c030f02011e050307020105100f031707050a0506010e060a050a06 73
    0x9998001075203442c0041d903280a0f2459501400c9030118a00300c100d6481d030302030070108030500104240601e80d19580502400003151940c481155aa507030903020040003104011a039050820b0208a0290740c01081c43c5000c0c2040b90030311a0701a11813108455484d1044c1000308581c2c4401d40300004034009084005802e4402811601030941c0031700800e00303540040d614040c07074058000030b05c043c403503041c45414175400e800880b0400034504000d0040c28002800700c00381c148200c502c003001c14400350b07402c22090311521108683d0b54a607240c030024000c0d40180f14051040c1020380310301117140b030b03c80c0c80030321103c1d0022030740312031281142c840541440039a5000c03410b100700288400300300038810300680c001211070780300c4e00c3e1289024400603003526001410681c1140000800f8007011005e242e940701625003001403003400c0201b00540761140c2c413414401030018455441c02c101000000901a0306884900d441100740c3d89400c010303c200391410340604ca074450300140741402603620950b2101c40a010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 338156996 1250 338155746 338155751
    0x70914040213060207030c0506031b0c100606110f1b120a171b0d12090303110d0507020d080709090504240c14250c0911131d19 56
    0x890b41c985102c000103035803041d40541c0001c0707820014042148010802014291fa05520710710f00700e44400714551174451540922803010500c2071060070100010072189030408020408991208809001c1c2c1c0c4c2140d4600d1184c1c441d002c03201031514408203094210312506940c1007444d65018007040f4419071a004205014411602c0b040080703040103d03220481050822296036401c0320160203250300520fa080082d00e0343c403449102d0540e80c0d00c811001c00210704520f0010340c0380524a0102c000c3c1400740180c0c1c0c030b03008000c038003a9450f0400d0f03848180038050507000c035041ca00b00c0985c03d0b502c1600444d02003000c62034100e01000803952942000f944940308407500302440c1114401e00c1000b4000700420348956503920404102c1c90342120b0303020f040c1e0b4036103c101d41c1400c5003c4010100c038089129130100c441d2040c0e00c0901040446403401000c1c1c0030000c4184001c0135160041c2d0444e400c008030300c8141810108000521700240e00c1640ca401c04440040d280321ba41c1d002601d449110a1403c07143d070703541e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 338158246 1250 338156996 338157007
    0xb0f0102011b14070b150111030313020114070605150406080d080106030507050d022106181b0702030f0102030603010612020904170409141e0c07030c0314030a230709140402 76
    0x202e0041c2818071841034040354206006c90f01000400c4100780c0156116644d204105002d2206242c1568069035582481c1685c070642d003e1a18200754040c09000604007030800c0e0500c10100d1122150350415001900d0800000307948244d220341d65010b451203400803946440040c0710740c6e44244c00041d48902d107820124540010303028408203e901141e40c503000c041e504107600841441d542c2d0502c0d0007400c2101c4211950710304038400400c0b240080d29800c61311501da28041503140644091314103031600201603818884250382c4440c0030f9401100c0052180d483e0800118052450003d14149039070007802601041d40d90b507554001030000350559100052041c00000340110413070058038076229003803081c05814105142039002011032504060110301c4103108002149206800380c0d4102905850700c1350484455040581f003112409810384044000007081184103205604a03038401c201c1c0b1000300c1e1420f420311800d40d480400940e00403000840c215010440c141654000e1610708100034001441c0c40c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 338159496 1250 338158246 338158253
    0x130903021c0c0203011b0207061107030203060117010e150403110705090106090806151f03150e010825060e1207030c051e010e090c070203010e010b0f0102011b1407 72
    0x1801000007000c00203140080400460400380929030541802180512000b4181c98000e92180d0b2107014507410400d80f869080c0500324204020001183c01a0640301c49507102d00d80d40c1c49584030035114040c41e60030301c0316060b00341c3d50019045900c400d4079040c5038203548442e81e0444600d0f03c1c84001400038403464002062075942e2030051402481d0548a0f03407000f61420664904018006200500030744041c10030440d182c4600c503050341c40d8590780035060711070003002c002174000b40003441d41c0065a141410010944c48440c4504038160307103440c0101d49a0008000006003100d0000030030303990510701c0313001c1007020300e0007145005003041c0003d00103040100303a122101c0c6810150b902c01d40d01128540c00c10022418001802e201d4011182c200000f4103040d803001034200c5409040c801d008200100020340c2c2d00c04820250ac05c555401802840b040071048000c602030302203d10054860640084804410f600510811018001d0304000846185c2c218a090f51800328071124444204030400040002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 338160746 1250 338159496 338159533
    0x50a0b180f010b0324041205040e010b0d0615170705040b03090d03060b0301080a0816050a0605040308060d0528121d0402181201060b07060501050906030a0213090302 73
    0x200c00220000110110907504040c509140910f1125034095174100c5c02458002c1d01090981c803942082c020424030b5040881266244925440a03040c3c00008002107079401208000b042e0b208800c0c142400b5003505c1d60030a0201c3c584101c034400210b01d400051994403000c88600076404030260500608090307444810200325401250140074907041550350b008441d030107100700300c09481c0b0b080d8118155811f00101d00e80d00e540380300e8082c210110201c0e503000e500c15004c614080003944881590709083d0300f40340c40005810140e41c100c0c0440c203e8400a0039034101080c7c040000c41e0400000c040c04280100410107411581c0d0701c440c000f004940d40c03980490401824108501e2059580902d500c20b20a00000c1c80c10108412512680c0100200d4100c048030000c3c2d0000d8400484100c9045082810594010070b113980c050541d40c0000304200007400155444241221001d1b2900003941c2d0382c20080644991102070001e610006440c41c500d48410143e1110002ca8840e004a80e41000b030602c01002c2d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 338161996 1250 338160746 338160763
    0x30f1b0105070c1a1f0b030414030f040b071a0906010e070c110405060d05070803040806161e120204090905150129070b01080303091207050a0b18 64
    0x25a9185000005100002449900d030301108500d48010103511541e82c0d10350100d0080400181d2442c1680031841440041c0c41d502c045404540ca40f00345d880d07440300490721580007100c00703580281054146654404002c011500e4407404041e0381454141400c46c00d104ca40c202c080d09580d8014070000940d21420340480c2680500e00c1e20f0f0060a4540c50302c107c1d1040c07548006c06240811000540c0b50700003030707540e1031043d0551400303c2c1c0c041030550383d02009c5800308142c64400f515038441c411000500440c00b00003003080c2c5107608140e031107980d5080d4000e803642e6078810350324002a8500d481c20302c1d4004500c0034210100380fa4030300564140e411044140aa0f00030303400c0003101c25541d00d415000c02400300704503034011807400f51903100c3e503141201c1141c554510a440c443c10480242514405102d074008580c0e1140c1d0101c400c89055846015866680c1c1046680b000948910241c4001ca245910140c80842d0307807200c002c100c2d030940c540c1c1e103034040c16001d04031032104e83c0e17030030041c003180201408030f201c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 338163246 1250 338161996 338162017
    0x1092c150a060e060f01020c09040c05042003040602161203150e040b01030b0c0c01050f01080c0a0b0f0d061701090201091508010302090601020f0a0c030b0f150111030f 74
    0x5109001400d110664140540744000070303894040e0400c210003050412036800802212040010700b1030b200144c0c24040a4168aa072080d00035041100304100303120044203449058404201c01030034010071980100700d0000c0454004010300005000821640050051062001560400807450303603891101604181100c40400e4a0f00b500c045450300b042c1510008041c900e031110708904060300d42d4403041c00c041c0000762031501c0410000d8084842c036000c40d18825180ca000b040246002006a038600e03030203010b5008140500303440d01a0740d151400f10300d401e5034034400c0b1440c80e040e9080760044640d03000341a1440c40f03507110030b0300080702c122000d266491441844000300390040e051000604017080e0b82c002640c0407000c06080782c5010703407200655055130b034152000f00854880d90010b0f803914800000912803440b50003035000c20440380c6107034030781100d1013a80c41c2e03c15919080c10302c02644034122207002d201540d2801070410f0f98411034a40b40c0c0f09594501707403807500ea05d005400032258003080448 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 338164496 1250 338163246 338163253
    0x11060a08010e0f0606070f0320010f06060806010923060d050a0605190b070807230f0a020f0d03090b13050a0e090712080903030a080901180b01092c 65
    0x4009184125104952010074041c85007140e00e0031340c001800c2d5014030413011307004420003800d2400f054020a452561003085500c038040980240d0300c080d018140461600200c81c1c10a1000900c1c6401000c1e114090541615030b01056800d02e003010b804504020181190071400381400825034a03804005d15400c0c0032a140070455250185c0e4003c191980c903488540241c0c084082e180280003500300807000e8a41309011180c0e1454a420f180d010340c040d0340c9001c0c0c00c101c504101241f070440d8814602030603c0c81d1105503008260001c5026407580b400d803101a401551302c00707500410f440c10921103480a03100f81000030485803614002c1c41d15410001300c10544c0d0450714000d10541c905040403a00901c4282840300c00e900d0110700c41625a0140d210703031a40c4003a0b500c201010060010f003034468440c8003408503619045445001000107400340c1d080d240755480d0054110180d02c4040c41011155088420914264a003c4402e001005040452240b400e00c0d490340361500d254240055840b4550b10303009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 338165746 1250 338164496 338164499
    0x40906020703110a08030c0c0f250b0f09060f0d05010602011a030714060309190b01030303180b011403100e06040506090619020901030905030304030804060506040b0105090d11060a0801 81
    0x41e111090162003c5010380c080018640000c249004a0f40d011854010040c4c490541808061415281c550020100d000344220809100711024241c416540c215003102409030751110b800c403043c41001298500504204420355041c14408020255510103c66040c81c1c411401396203c01c0314802c3e040000140d4603003101d16114041d180c000e101441c4110003400d403041c40c01044000c9040168141303401508040000365540c0c03401c0c451803c94141d0100301004001580c500185007503800d003c100e0200f840d0002405d0301c0d00004010080c00d41c1e02241985540c0d09056031215081003004280768184a1004020309404260148480d00101140140340908062030300c5070429030014078181240c0d1000c020080310f650321501c1c421100301003400060380d070311000004801030030340c0c810090a64032000041c04101a8480c3d19144100d018040800c01c54440b01c0402043d1104041502c0c002141802460010f14200c000e10703c0c000e100d2507604410102c0e07140881c499800c81c0c2810701c04502403200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 338166996 1250 338165746 338165753
    0xa020609130510180b03060a050c1c0b0102060c1204030e13090c050405060105190f030603350f04030b09030d050412020d0206060607030c0507050901090603030e1c0f030e0409060207 80
    0x2504c903040040c840034003500341c0341c40109981d04401413100c0310b0071740c4580c080b550940f000011144a6540b034810501e02c0c05c107905d6640d01503e184d6400500601c254000180020511000d4407114620800c1c035210343d84907601c0407558500c41c0104980c1c012802c2d500a1107000c0c0324031401c2031807449196009540361800d41004202c1d0002002c0c0740c1400030800031150301e04000d4415010740301c25402e21840000554001710000c1113160401000000015011042c0102c100c00490042c04c00c03004281d440065808621a14007072081180d10145081c001840001c1c403202180307a01c4180d240469080c544001450300965000b034500340c031340312504c1c40c240303e58541c1440740703110302030b094001851380b400c2c45000b180441c8070b01500501001a1304058008102081c4451f9004080040400c841542c49480c0b0100920b9144411004181d110030584803504000607104000c0c183c100e202034004616460340b041c0030302d28803821000c01030019007021007076580d841404480c82c0101c0006880341c42518 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 338168246 1250 338166996 338167019
    0x40b040f0e1501050a0630051f06020309010c02010c0b16080c0903070504050402010302070204090803090706020f10020a022104090506030303091018050708030a080c0c0a020609130510 81
    0x340d05031220302d400030061109488018400045580d00d01d810084c0403c501d4014415060307020000c0c02100107a15502400442600454007801c0d6240304005d101207a00c0328002d110350544036100c09600103000800c420b602030012040c035540181801d403004480342e038594488140c100d41481d2900d4107804100c8030a0b5100404660121500303034000d12b09101d6400003582c5003c0b51250920481d00c80f8001011a4480e40544a8103a130280c0f091080c90b0b101e2030401d866801c1242d80141c0d503c14020000382440c40042d1014031504400098822942200e184d0006580b040580c80150710580e00001c00d040d10086146c800c14810690907515541010b03003800c00d503000036000030702c607900c01e200f0711094000c04600c50f01501014400000d203007000701c0071030074103540f244c1c00a130041c000c540e8001103c1e80080020410543d40790b480101d941c0e51400079001d14051b012064285922162510006051080c0208491000100442c040174200788202003902d8003100c42e9400c8842910040003c2c81240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 338169496 1250 338168246 338168263
    0x4021306030c0e09090f12040807120311030c01050405191a0c1306020106091b020d0e031c03020d05070f021e0304050a03120f02031c050a020d2421030806040b040f0e 73
    0x5041d000c0c581450198419030b9074941d4000c032940d1092f40442078003054020a03080f151400840203a984494503180454002d04049070305803007900800c803555024610041c50300150961060001c4039079800c4003000c4405c2d900c000e140c540d901750b04000c0c920405481e829594000d0446600215a40382042c25a50680301c1800c0d01c4003d840c03414540750002c640200700350001e5025460034038804243c140000e440c00003501d50f0810350f40c007919480203565505400815210031690f00902468480080c106c6800000380304110041c0c001c01d41c5030526000c01d0700d10111104000b4122414591600d0000301e40403040e920455040044020060501d900882450400e54150001e1401c240d15401c003409801900c1040440d003695502c00a8a030140e10343c16a0341099203850704100041c0071703400c0c021040e0030702800e9070200440c060001070386203209039248100000b440d103568643c1019540c20b0300c41c9074014101030703401f0f81c442600514030780f141d1240101d101790102001c2200c0391740d00001414192131 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 338170746 1250 338169496 338169523
    0x1620030c252d03080f0a0305160e1c051227060a05070203070803040b070b25030b180709140303030603071208130b0406090504021306030c0e09090f 65
    0x407040411640400071012400704441d0766080180c0d000c01000041da2442c2500003c01c00040840e00a62203c0d001c2c000e011481c815850420a545510081e9100582500c240100284c21855a00450b05010105000944042c03142210b50201907a4250a28015840d0342a0209003c82e110b4440d035840d4022650000b44884a10032805492012400328400c107840c5005200c0009400b00c11510b040258400602081040d41d45444e20381601c40010781c06000e050f22032100300b0000c1480072105501d28034811021215a010800300341030254094651180e040f80d10803c1c001c01c40d1400d901102980e40700d01150303a50b004415007030440614035004412850350195009108000c015200002c402098131143c0083d1004007555240030140c600c105480f540c0d4903d2004030000d40300e102035000e4026102c60b80c4070301402d243c980b4180022802030000d40180c0205401c0d00300441c5000380c8c071810110344c6503d49200e00a16850203d0800c1c1015104212540d0004800d4407849000307100600c00c42c0b51 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 338171996 1250 338170746 338170813
    0x105061c09051c0804171c05010e090c01080f130204090206180306090c0d0b09011b0c02030c040908071212091103070b030603060c0a03021902060f010902031620030c 73
    0x20079480e1011555481d950001c1404e10015420318240740700b10320030222042087c3c040c400356845100c21160601c0c240c0c1d10403518030422000850703a6004010311889014124000c1e18030b565101c6d919000321305000002c2c0d07006035a40c03403c440581c58190041540d081c4280e028140d48450300213161909000804c1803c0580180c00606100c4d034440c004c003000180c01c0904c1d003206403180b540342c40c01080b00640d4429030488041014010079004080100d0043c0201c0035248540b042c00140000c0d2a4441c0d4014040c40007045964001030f02203180502001b03217450000005191010594104c400000040d5005451a940c0141c14601042002c0180c58148000da00350b050110100b0b58841c0003600e05a51001e0214031030030441e22035419030b4840f0f1080c26102c49058901100a0b48851066230841c041c03a5584002184402d0355000301d9018600320f010400b80400d0520049401170001041c02c2c9054581c60a9810550001c00c09484864610340251504002d040900101c20f0056800e81000d4071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 338173246 1250 338171996 338172001
    0x423040501080a02010e03010b040606020715091a0a0314070504051203160b07020a1a0a0c030504050c060906071403030919020112090510050108100f02040b030105061c09051c08 78
    0x71800f0414058055082c00c218514141050001e40500f18003040c4c0c680091501c039000568941c00250b00b000c81d09040f00400e100c014080040350b401301180561000441c02400390350070000c40b41e00038100140c0038513000071070351208801c0540c10f2409a511000158000c5005e000d00d2500b0910219120640c80c01980b4241d044e0b0a80c1141c100807100c0646401c10500004600341d0003400500038842e4048401110050088070341030388040244e80809015140c80da801047c5030081c452640965041030041086814074403c00041c1da024079081034002505120355000652445403072405510b11001030360f22481c24001e034602c0d11181c68002004018a04031400260360840b02d020b00c9a42c50100100d42031005040441c903012158100282c420301c0c10000140054000c2442d010303404038840c1c1480442409501441a80140d0180400a103010001080a8039240740105500c09810003a140b011304510403010071960350707940a95580d0010b01c240c0071060400300c0030f4030403800d5508000b5401d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 338174496 1250 338173246 338173259
    0x140c04170a02181f08030a08060405040308061e04020409020711030d05040e13050d030b090105010203040f090c0c0804080c04150b12040809030d0e181b0904020f0423040501 76
    0xc141d040c0f010032071410400c08a44034003400740510350b42d100d00d0300700d650b110344e50f0b001c502c0c0d070ba03a102040d40c40c0051074000102c2e8080c540390144074050b941541d07400c05a61640020044003118903044289140300180c0144e0700e0381c40da40040e00040c801e03202c006880700c0a0341001a1440d031003030201442600502410a00203400100b81c806465071203001c0701c4d03d82ea6105600694003400c08018101707100300006401c03d40d074075801403071008005039011486a40e944006a9036402107004d01010b1700c1080800f800541c420b58400044e00c051468010741000380340e211101c0590164120441c40d030094210284c060801c0d000380d40c0030401d0107084885840c94051002194041e2641c1c80108800b110041402c0c45070410036900c0801000f811356011a4010f88040d05080341c91030f0040c05050304441407401840c00e180f41e00d124007405060781a1011982d42012969442007018982c0103900380035007502c0d03284180107400034204803496034061101082c2174442c0f1082c840d01046c400d500b00320051240 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 338175746 1250 338174496 338174509
    0x80705010c03181b120803090c010306060f05130519080105010608040c0312090b04080f060901020f09010c150603150e0f1906110c0105180d08160201140c04170a02 72
    0x8940d000369a0344010965408542d80d80526070703001c1001d000040174000184402da000547c0200c80c80c1d811114030624180054003a2a0a480b40700d020580400c00c404099024800030030300014259000d40009480750005030200c82402440f00c05004101024003020034240b24142c00351086061514881c907090ba2080b6031a030340f6010046c80e10b075046214030750890248000c1c0004c0d012241c186c6480315102c040719603441a9a06d180035a84c415030380031900682043c42110b6024124210300d031318000b0902c00540300a003c1e0181114020034141181883c6c0c0c40a200e40c03070245108101c4c1c1201c0c0b10801108030140d43c0d6a601c1c0000c160803411400d184400002507401060100e0910643c0104d12030400500074580c8141c451120400041d500340d02c46410760249100766903001c14044510082c4502c5c0780c0c0d500c1c0d82c6c1c40000c0401c01e050046501c0180c40140d08400424510020416101503c2041741803241a142d40e1600301c0b0104052180108441d840810f00c50004001c2c054107403203800107a43c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 338176996 1250 338175746 338175791
    0xb100809071205030c011d010f06140f01090b120103030f0f0f0f11070305010f0621240914120f180d021002071d090a02041116080705010c03 62
    0x11548142510300e402c03c00140284d40505501030300810006107001d0850401a01c0740d0102d00c010351904012562040c1d041c0318440c103851070340d000c010080f8811814001820a00381c07282d03040c00400750000a0700414040108500710b03d501c020302c2d95500d1032402500c0c5881d50703140ca60900000c039102030019035007c00310100e00002d40c503108400303035400c120980750021128a21075040c040c180012091210542086000b2400c80000704076580c1d4034101c0c85030800c2801260301c0c0c0c048840c2d2007000403801e0903000310092080704002202c40320034ac044090803603600c19000c440f02240001041e07100301060201c0e00000308580745103890303c03800c00100905882050782c2041c0b40022135600350186e4031443c001c0e203000e660180c629001c0420707050001e075842000e88603400c04501c00f0070303100a011000607a054000d0300004010144042da40d4200005080050600741c0141c5d014410142504c85800e51036180790300a4281603946c060b90b041c020700b5a90207090a9080c181402d41c4041d0780c01221a4840 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 338178246 1250 338176996 338177009
    0x2506060f140d1b170f0303010b070b0411120d0306060e01051e09220b06070807030305040f02150408011112010e040302120f04061101060605030a0b0a0f03060b10080907 74
    0x28050760940c644100c05251601260800c0c40070f00e803001c00c1050245040380c030724800090480b1aa401010103a86d070783c1c4000d0090401d41041881240c1c00910440c0300c01707820910a104040b030802c80d006c00302e1104075600b1600b00d80e56004410100c44c494040c4034110142c2500d10306103460005202c00685648140ca1014501c0485100a840f4220f16001610380c1114020009a120031003100261a8000100c0300242d12500e00301098255140142c01c94283c241d00080c0c00781409842d40b03060300200b80040c01510341000c084000001070340c403a212403100b0003240d851903407546e00701940503003101c150300c00303412940b00308001c1c5c207165110b11400d160454020000140c065940c0d07140c04c0341000e0112404840854020a801c2046c000b9400600f003030301d00c5680e4a0800b00c0c0c04c60764480c00e84446106034070100301c00300f0101e80d610340250042c00488001401d8048204d5640c580c150816080b0391003994202d50752445001103140c10821240740c030030203103440c400c141011030490340c5840c0c03c1d11400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 338179496 1250 338178246 338178259
    0x1050103022209080a0509091303020a031b05100606020705090c041217030f04021314070e010903050303040615080706080c03070327050d090e010b0904022506060f14 73
    0xd801d000c01903000036000d1030340880b4690702d034107000e45c01078050f40185000c0e5104140301c80c00250051301c01c8490141840d0158014000310394961810744006041880c070000510030480b100000c0764040040180d4000400000102c8c2c9140c000000c4c20a00e061700018442c080300d400f48035014041205850503111040c00000c40b003a210b2600e0341c43e400c0c1b0300700105062000031013004050840d0a590324425030080e80e4610a02d02804411011074418a8141c00e955400c40e02042500340700d4094491b641c8418105010fa1544984403145075030411101162800e0716050034070072030381b00500340100800030b01c0300400c01c1504100001d82120b00003441d0040c0b40d1000300000f0700940c480d03044408103011403208406100164840050016007100040c1c510b88101c2090a0159214030001c2c403c5030480c0902a81c16401d05640d4a4154070007841c8613402502031104202c00d0700d1503056004480f032200d4030500282c06620702642600c040740d222004900c0080c1c82004490310400410718803003030403907a8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 338180746 1250 338179496 338179549
    0x905060415050405090103050c15031608061203072109060507031206120303020d0e0c030c06030405150705131409040209091018020f090103170c0708011109040c020105010302 77
    0x3190980259803003583d0005445e0000800d00801003800e1800750025101400d540701e502590844500c029555214031102c8801e00540342441201000c0e008600240804540480b10300c00710302e1608100c0080e00e61041900c0d480d007e8600442448160015a09007a039a291400001034018050400042c0c14020005070a0a170102c9076800036014010300752255880342840e0400400a400096120340d0f0300d40351140d140c1c1c0708040001c44038280e0320010024010101c80b1821f0100582015108940510411540708410100214103138412a8a580e80c0c2e515020200c10b2407003054466802500e216501c0e450b24130142d114045125440340e0155411405510717800a074038900802c130780c0500456440c15170a50124040d8910350800180202c43c0040514608410490301c1c0c04203200003803400b103032001c1004d60004498007414054074058140c458541d0f0301c5910b20709507803200103c4c03e4540381c0000c14020300c1c603061191441984543c40200a41c2d8150360201d208054103035400d005421801c1300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 338181996 1250 338180746 338180789
    0x903080f0408070603020d0f06030b160201090b010e1e09030307050304050f07080106140301020c0303061504090509100501080118060b0607060920060c062409131209050604 76
    0x31500144410011124004c0d40c600008009400c00c2c03502d50441800c0130307005c2c9041c610074001c003401c1e01d40140c2e010000f91035821541c010030080540035010755407a50b0b1110b001c41c4001c17003130b18020260082038172490300d0101703903010741c41d2145801c032958000b80c43c00f0b00150000000599500080f0f40c2003013550f9031101c0c100a4030381020441e5108891054030000702d44004190440340403954821042401c03031880000701400d17402950845030440d80305100103251031411901c0c0c40a89482403030318034601138451807070700d007070703c1c0304440f02d911503800786c0c0000320990f8152240740e0041c60280020000c00000318611500b10001c60b4014101c59101c1b41e207400c07203507248002c460f1160350203c4200540e05c964905200b200510782e18184c0c010131601484031190501100316520100040094540d5a9036101b203820b044070001c0c080184450702ca0004000303511107042480c0a0a00d011422071140200d01c0d190700c0c81c038030b025003140c200400248108440d803240c1040d1800d42c1e15418080c9001e40b000c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 338183246 1250 338181996 338182027
    0x10207051503150607050f0d080603010c120906060506160312020903250b04260703020303070615050d0b0a0b01031a150c120a0801060e090c0d0605060a02010b031903090308 76
    0x40000e88280140b071a94520100c000548015236181919034030078654404081601b00c441892115000c115840e06500c1100c180b9404420b80c2481038000107002e40e00d40c0041241a0003090440b40140000c00c00c0740107064000301222415032100f60154a400340104c04039440f80c0002a21404507110520300300a200d0010740c201000d001603a008030340b01c0781d03609100384c210394060002c4003801d04246d43c415010316012a41c44140c9401600440c50003045aa5000080510205000307129102c0c81000c1402e5035114800121640030300340b00d820310306000481d4811100c80410076030506107441c03660000288603100c0c0070b09046080b11000f0715a054400700700d201d48100c42c01a6103e00800c00c0582101515002078804030100f60b5501d00c8981c0c070383c40c09840d1944c50400d1790f644000d0210004a48030031050040000b0401600081861691078020038116080100c811025075104c40302c4110504003003112443c1640c40003410030f00900140ca01409100c1940000703020441e0018070784c40f8901e00035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 338184496 1250 338183246 338183257
    0x603060f010f0e09100f0b0a0f0804051501030f14011b0531030c090507051603050d060e31111507030207060e030a200a03020a0e060102070515031506 66
    0x180c41c2c03400d14500f40c10044c1d1070175124080c02500740d01559001ca9000008020348082c510143c0364251060b400300c8003540d140c24020301c100c4880c8110251001640342000c1424003c510480400440081d50b01d44032801c040d440440c0121030380f402070041196051409221a110303a141400d640ea941914103d1249450000e1004030f2044001c0c010703025004640440d000726806080e030b44100e00e403220b0a60095a00070b07966100015010310001e68000c00d42004000078501c80d0404a1501c18040c0074041686c0d5160700c0b000100c2c03007007010803c000e01c0010708240494101c0800000c09090b001c280d445282d0269005051071001c07024040c05038444882c024244c0c207000d108039072103802915009598001038080d0301d001a403004d032028194240001c03008480340d440b043e00300d143e92004800c0c00c20307203090502003507000c0d00303003d000400340c1c0703a141d801000b4105081407030015180140019181c054240c0c880c1d400390204108084100f5403050a43e50444442c0ca154450280d0035400600c190042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 338185746 1250 338184496 338184499
    0x2100e0418030f0203070b16030e1c0306060c0512130e0903090a090b0f240d091109010f120c0e0702032116120204080a030801030302010b0603060f010f0e 68
    0xc00c40c0341c140e6035450101d5100e159109a0301c6070514141090100e803030340100480102450442c030041000b50200b414000c684603400e2800049041d80300008c2d43c41d1914940710030142c0524107030041072065160149102610450600e0b031585021507075056070b00c207078000544080240c041490020f600400c103111006140c50101b04102c1c0c01c0241d0041d4580c0d003d601314501c84c10681c20b0009007008207008800c0480030080c2a021500c03200c0c4280014004016141c0c0c0c04500c01c2200da29180b82d00c100940004459034070300050107100d41c501034502d1846401e03118483c003441310041050002d5000b140041d10303081c00c82c10301d0080c09890800c0824105412003406c2ca5541000c00c0000c0d03a000001d040301c4542c2c0c3d40c0007845c414011440689208040e61402e010010040a003580503028186213412800c60b200010328081d903031180c10341400e5081400710001580c03c1c00400c00e1613424001c01d0001407044600900c2e60074403100189800d004010f400e410f015000b8801145030f400b424050029180 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 338186996 1250 338185746 338185751
    0x1202091504060e040c2a0507080d020f010605090402130209091302091305030d0c0c0f230d0c0b0601021905060105030d080f011e080109061b02010c0c02100e04 70
    0xa62180304a800034000e030b0b000103400454010a51030540102241000d0a44814062100d0500e5011958801c14400c440200609030000c000070410800c410080044101400d00c0d11908a00281400104004206980c2c10060300340405d039660082241c1150341103507070140782c0d044c4402480103401010700b81940720a8240411a0422252424101c286c0c030854141c2203030303900e4030100c00050303504250241107584140000191070f500380e8002151004641001c41c01240360780e075030340d00d400003d59003100c641240341700400000001162141d04489001c025220060190300c00800c0807000c41005826141c0f00c2c004903c259009005860f018407103225411440c42d03503401c140e03136101820310869009106104040c0b2581c0d03c00d111240c0201420b07200c640c2c05034600001182e01510b402100014030307a2080e00020800c4091052100b01d5108101c00b0840d9844c07a4203070301042c0d403150b64000543e4140f9400b024200d50185c81148103a42c115600111501c2c005030840350a81c2040000fa000303403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 338188246 1250 338186996 338187019
    0x30601050f010909020a03020712030e06011e03020d05010e1c1b0812070e1f09030f0201050f071505060d030f0807050405040c05070c120f060b060d240b0a0f120209 72
    0x11fa00d600101002e600801c4a4442d15880d0300d011004c5a4154041034a01d401500041c082805e124900180b00c1108086000013240c9a0300001e04c40d5850801c21200d6039541e11903c600c080701030200013041840400c140c1103042e012038018281404480c02500c02c001e0421551040098403000c1ea10180c030103900180c42ca01d00392038041c104441c000032151045903032060440403504ca00310b0505e1115072a44c3c0e07020000d4610781d2441d419403604c4004a05111f018000e990482210308083e001c0180281684411070300442c0355001101c001420b064003030031800c0d0090011a07086540b042212210340742c1003281d903484603011030711405140c021a82c054104100b00019a610001a00206000c0c40c1100c21103070791520b064807101c24101006004040c6002d80700301003a59503011080d80e440107003e05d45021100c20402c0211442d903440c01c0081101031440c044840303c0c81c003410b4045c00c0700c914041d140c259121405005000c14043d070742c0410044892250f541c005940544200304d401800e240c1004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 338189496 1250 338188246 338188267
    0x3020712080307020106140609060d0609020a171e0408070f0b090322060e0607050102092715130e0705060711240f18130e1209030601050f01090902 65
    0x70b52098505900540c00c0220118450b51441c00c03801135551f00620f510b1920b009c0105201c1680c1129214400c0261b40d064001017400d0a4002031200100310b40c2c031141210350706441002b000401820100c0190709120700000e0280603000c1080d00250480469522244c035458081010100c0c01801840c00110b00144441800000b02a0803016036403900d1414280b81080003000c504590f00ca00d0002848901001d8002d042400040918034084c1001503e4202c02c880400c0c90825641a059038062840700118110f040350380200d504012300084e020803c42e281000504039890030410000300c04d42d00e0307401c1e008281080101da001420042c180c1500d41c100c6003030182c180101da18509000381d4104071036000c42008051010311001544a00e103080400601e864051a0000c82c155020500c1c200200c560170354414001120104e1070310b002162050095001d281450040c02c000c3c0100c40c01408107400c00e036804a03580341920001d036076280f14803280d4401254107a00c590300c1614558400160640e65 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 338190746 1250 338189496 338189513
    0x12060114091f02071a030a020309070803160212030a08010e06010c06050405010f230a0510030f0c0303020c0109080304030602030603031209010b030c0109080c0d0201020f030f0304060510080703060903020712 91
    0x42c20390702511541540c9690303540000060480350301482c04200b0005100b400b00c1c0c2c0c003940d08612a20f049171845a11a040c0a1640d440101c01d0380344402109441011032401106030021450800d010350301746644503c026207608018003e8400307058540000a02991080c0d450114042d080701c02030040e8141b034108070b4024035001400724030041c2440a486c90001104a0003a039260340c17012451400da4901f4003040080c20090207041500050030400004650804050080540110b0308030903054518600030789000c0c6260800e038140446180200200a00441030ba0100c030341000015960303945440c0020b0842c42140501511a040c050501c070b4100070541c030840d42101c05908032019011b0a60041d18401d4581c0b107020816030159880300c0490a1502800440740c3c4180101c426220f000410760742160030201c00d01c00d000c0c3c408800c000620125028050b005811100c000c0c02d81410145030b107460741c8003800b000d00b8658844134843c04041c400c100840c01003800480704111446546028070b00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 338191996 1250 338190746 338190799
    0x30309030e4504110a031a07020706031808160611120105040b09011509080d12060506070c120804030b07030203010302030c0a051f09080d02010507090b1206011409 72
    0x540700c2892582058618040c1c2d0500c2c40b219002061206070b51982c0c0d030b001c1c0d84200b4109890300920b8600002000a1005640003a1040d41d8a150102490201002441c180466008008240c02c02500d0a4042042000285900e80100340340340c2e04c1a20300d00900d160084402d0040c9030928050349000c18400e800090030f2900000e002801541c5d98810401064400c1c2c0014260b0248825004100c242241c9120303940c1c10903a402d103449129560f08901c0d0030400c0c0c0229507000709001409505801c0c01d5486054003400c1c0490707019041058030340358560729521900460350310762034800180042c013000e502520019507100d400d03000c040c078200c60020040d4000384001ca00a108a00081c00c1c60301d0983c4e81031302a60006412100a00c00c810a00040201c01c1c1180e40c00b03009180c213011405074004c0c40601c1c1c040040b40c002280703504013200d0041114085a20032a4645014010504d81003000307100b09030811300c2460b0048403881c0c02450054a07200d0309122550098100c81909141e17440002982c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 338193246 1250 338191996 338192059
    0x308220f0f2c06040b0f1002010b010f0c0f0308060109031e060f090f120302160c03050c01020303010b0d0906020c012414030a02060a09050306010b031609060c030309030e 75
    0x1848000780c4401868401e0740440c1e02141c10b01c895001a50506240d07100404c0100c0081c070000009101002044804549101800050351662240261540c01604240603403196141c1032110007141d84500700e0800b41a40f0040402601201242c2580e10038401d41c009190410303034015420030400000d000c030840a00c022100d990601e0421440c0c005544070340020a85c110ba910080f0502c0ca9079020185160140503009165080c04045040d0110390b81c3e87c42224400c0045034003440c04e6051445c41c00804003135070740c1158410001405195100d105844143e00045e1010882212034500480640140da1544a90390301c0c01d0301411844807071484c1000c44500c05100044c1c000e450750028610400d101d402c846d0103500000401005041c14401480e495000d80340414010361640002400d064081e40500c01003c400700501000e0404d07440010072010302c40c200711600603d0008040c2551061010107018103070383d0340c00502410b00403241000c849000805c040c440c00c01d00450021400d00260802c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 338194496 1250 338193246 338193269
    0x100f08100b011e080601201e010504020d110a0b070302060609010512211909031502071109341d061209120a0305040201180308220f0f 59
    0x124041d402403e214140740c00c41100c511809210030401c4d682c494025203014100314019900c5520a1102c0103005925050040a4a659545031940e2400304040c03603500b4030140d151400f230000690f1450101c1c844154400d0f041031140c4013402c0002d1100500e45c0c452210602c0000e030302d808055011620500c503000840f01d52401780d07203e000b440407182201c4040100365011050300011060001030907102d0b081c8001010349006c0710308804007000e00fa06107007200840c4194009000b0080c8030b0b1450040089181021420411651030310842c0484000800317020705c0e4500040b882890a0080200141c0c0341c0701200c070800009668000c5d082035a404041d4005458001c501e05030000201e80030404400c02011542411a0046805600070010f8001c4a0310b12401d04421035482810024109901070303510000b48a24203400090404114504840006a1060030900c0007d501e8010780b100d200001c54031a9902e800c0c42001d901c1d03091113410811491501a1000900c8220782c2d8035082034178981c0d13112 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 338195746 1250 338194496 338194511
    0x130602160320030d1e020f0408100203060a03170c01050f06032b0f180f24090911041e0305010c140306010f17130b101d100f0810 57
    0x910b15110301d01d140b003111682040081c1484510142c20800441c917069019044030880380ca0400102e92001411768024072002c2010407220b80244562682100170031350035803a510b4404001800704910740001090741c20b001d0074074520900705070b05840e204803105000300038505010720b10320615403048500c1d910900c1189200380c0704101d2000c03c0703071003c03076400200d50381c1100c41c0308241c0d00840415007501c00c101e4110191030840c8407042542e4002c09400044408013820100110100340200ea103d0100400d0401c02401240c0e028405a048480000c0d00155419002d01300003418031540d40001a1009600341e2851320002800107003088078032072002008001d0414205940285035000f800c000b12805000080d07480d4000d1003260390900261402190500b4180302c00001120280c2e1400184a140d603605010840b2401c0c1607901f050340000001c0c401890980c000f07940f00c602072a40e0141501500116106210350300040024004192011390016101c3c000160f451140110b810851805c0c40c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 338196996 1250 338195746 338195777
    0x1203120f021314032b110d030b100e100305150d0c05090f060108070e030a060501090507020d140d0207110306070f03060e0709050108090c04180605150906091306021603 74
    0x5030030701c2d2803170044426070303000c0d017003442242c01c8200b1140014140a8030200e41030843d4014050580d13403840948002a06811560078404001c00c901003003002e0200403060200a0742d40ca141032084c4104a21f8007203129a10140c0805021b8950103400350800c40b50300c03800c0c0c100704000880009464060fa8220b44c9540c4000380d00b0608001a20154046001c805c0415a481c0c400d0013900650340016040b90304248040d40c41e030080720800d0f0700090b10a5600c20601c070046605203c0e03805609691301d401e0710300443c0703c08407110500c50705c15500e424039400511403080141d00c5100e0f080070703d1300500782c4c4e90038580140041c1401d2401120740340021700c0d00d000402c690002124890041a0640d203400d240c60a004c01520711000103003101d8114031500e200c07409103a46900403071804601c001f15040b400441d6103810800c3e21800385c48628100000c6259070340c2c0d030319400000b650000b0103c031000d03060344850700708103800c103060030002e00258000100091800c40c4480144e02c460f101e0b13640c0c201c52074400f41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 338198246 1250 338196996 338197003
    0x2070605130809130e0d090e070c0312020d0e0708011e14010e0702010906110d110301150c030903120c17031303120b120a0c08071203120f02131403 65
    0x929410b802c1c40152074038104007588500954401c00f001841c40c000030482450312002410510000e103105106000c640101d01c07405400c2031060900c46510191607030050401003010200c10051640410300b0084020300d42c00201c00380c5041d000342c82d61035807103516050207407040c041600142010341d880381555980c1885076000713200d00b005100d1007590810f034035883c00c020041d2400701159200d148500c0807035001c1c071440c242c01c14203042050f03407107880c1c401a00c00c0e00c94a50300c81c45a84428001004490003880380c40c0ca11654516011660082526090710307000d40c00d81000e01103c07a8604503082c415004101c0006590061912810800307030b0001601e684d20003115083c0b0510710204c842c100081c05404000b030400c044080120300041e481000c80d545111101c620040303503200c007000c1000e0190f5046200c0243c0900340241480a04080000030040c40d12440101085400c0a0343c1c5041c22072a44070b00300c4280c260304150f50340c040c90341185604e442980500307031403164040288a068039000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 338199496 1250 338198246 338198281
    0x1050406121104021309050f011403070e130206130f03110604120609020301020f0d02090a06030e0303070f0e0904050a021009060c0f020d080c0607030b0d021302280302070605 77
    0x1e0403403220b030b041207090001a403c0364011015180d02d1180100c1c0c01c04150040c18850b1142003011000b81d032402900030042107442c2c4c4000e0080c3c100d882c00f880f044084441c3e080e07204171540118110004d044c404503440384140b2022441703d501074000401c1c00c45920142c141240d000780407440d102c0300e0120230840d242c030840c468140c22040300c0b640840004d140740c21000d515070000b000141007400f560034101440d13200700f01c415402030340022030b20040c0c43c10071940c0e0040e111502c3d003041421480a480d50350b82c8400b0302007006014142d01140502da00c5198089107140010300300c180d050030903240844e91a0f0b0310344400c03440345540d41c003030103a41446044008210341056560024080079615850501001140e00707a07001043c00500c8804036040600030080142001c006080c41e190070f01c0000e084a20481c01d1134450204038828801603512048026901d0060300c0005035100e0a0300541240070b590401c54140d5901c503940c10314009605a4090002e05020b40001e001c035544400303000280d07200c1c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 338200746 1250 338199496 338199503
    0x71b0f1403011e0e010f05131a04020312070f23061501050301060c11040212061203040602120307020c030a031101060902070203100213030b0408031b1c1505060f030105040612 77
    0xa042c9008840301c0582014060582c130300c00001c1d050005507000340c10b43e00b0843e10400c000b02c00d60940010420100040e8100c0350300c1c80748040281c28203500080d1107042c0611156180d0f003000c6860300a008001e40d104666990000c0c00744107201d1410941198102003045c401c40034000c040003d13803161081402d042000314142e507407529681c2400c4094441c00606107007915500c4c00051900803d8550344014080040d040a401c0d21501c1d125040040d5618050810002c1d50420301c010010345400142607050b8034101c1d60a10340325a00e400b0124074180f06210358a500d41710380d40d100d0b410f154101c0c03000040c0103c140000d2140d180c071480c3c080d00742d01c114103000790182d000030503012410241d980600095211803032007000350b903501e48501000403400d441c2030310181c02c004140b0902e640c508070300c0c5180003000d4442e00d0800e03a0744080d001a8020700b040546000d0b480d81d000c0c400c03900803c0f46520142c0801841c0b5a11040d0035000c0c1d02c1283c2007402140c0c0124940070010618080c8c2c0c244000a2990 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 338201996 1250 338200746 338200781
    0xf0306010314010f0f0609110c1504080c06070309021215040b0a020c0703030504090f0605060702120c03030d0614092401020c13090303050a05090307020105071b0f140301 75
    0x185603200001003110070728007103440d5030f2425003d54075011401440445c580c0318501250302070901c0407400484600808c00381e0515420030004066620100e0624987c00c4101090221584c86080c000380c01e101d208421a840c1c0103241c20040f4803900b603840504410b00070380b0350401c103d843c07080050b641e4014038410000c480d1210005000614813402541c0e0141c80040d015041c8508070495500d0151903070000c60101da0301003003d2084052622a040614243c02c105014162070032011525521079484003038009d401003952a50044000c202607800c42c400034003103030742d502e00720003159008050030f000e0702402402980301090b1034600f00c030065004918205054080100224a481407111241091b5055004003d48086650381d580412403801e2240440885c120649144c0201120402840ad48205151100748050440e000040c0c803c4147e0a0a00b10355560b140d003407103da1132501001400484881020100301c0084d0f8421a404460440043e05544c440d8401018240d52400002d03c44115 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 338203246 1250 338201996 338201999
    0x903080a060e0105061218010606050d29010f020c0603150a080f03030c0d0b090a06090c080108070611030d02030916080f030a081e090d110313092403050d0e0f030601 73
    0xb40e01302c6c040d50401108582c455000c2c0e02c5540349130946080340d00c41e1012400203d05d5800d04443d6002e16502008034243c24107000518258800f0b480c1940e0741400d041140341290a68000e0080040c1000164014040c03a2280741844046041084903000c1074003c520105001420001c005412600c0342c01c2040650f0440d41ca0300007007000c0d46c02c84162403195a41324541721000e512a14116030003441a00004a070303990a240350f4005507042040c0003030400c040c080c0108014000820188190b800310b107000c68140c1500015107185019040200d82040d1000051080780100000d60600c40d203414840c1180300741d0384401c800e03103640c4d51443e51041038004020340115944070314401c55000308611544815240341d400c3c010301c0150b080700c0000b8907601001c2900d145a8000b94502d1081071944010351074806141da041007820715600c41e03101096242d66000d0a01038528015040c0c04045c0c40d2401961603580c100280d940c4800d85000380070900380891075a45040040110750000740c064010307c581d9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 338204496 1250 338203246 338203267
    0xc010f0206010f060c150e011b0e030a03030e010e10020405100f120504021f02250303170604021e0d0f110711030f0d030b0909010510270903080a060e010506 69
    0x18912000111001c464100c0143c00582680c41014401f1500c1000000e402e08061451400c4030120000c883c00e0051520040400360360000e07400004d0f030b516250119a46001c0d208040c090001c084010b0715034010804642c040c20103660191003254000c4504e00ca481040c148140d0342409019504400581b011015108905280c1c0055411a201070843e00714000f002d0b4520040361003054944d00140c01541e00c000c041f01e140001c00c070061186981e20b03000380b8656075018010b003a03507815021082d00c9140c0001c000356104d0b419101d100d0100c40700d1006d50320716074410701096032101b984003900618189a05e80c1d95985840b404ca01803101c03480036460a2516203c1c01c410629901e5219031500c1000b11041196100307000c014101412901d002c00d0685c10403040040d90b1600804640c42d60b0f150404120014144812110480e09603514900d40c21000460b40b034841104810300050305800e100c0355608141c1d10a0308284540f00b81941001074030707140d802c41c000780b0f1028800c0c5035005409024420343d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 338205746 1250 338204496 338204507
    0x150501050a0e0613060e1002010513060f06050a03080a0f03050105061b100e07080c030a1a0702120415030509010606140901030b04140f09010c0915200c010f0206010f06 74
    0x1c1d8035008003d14140030410072103c2558815410010000b00340c0302078108241022400b000003100c05000900840c90311010303400b40510f00390703405400f507030b1110b0386541c41d4981030384541d001d0640a083d400e91151030382040004c60703000011000c001a20000100032885c482d1103094140d44008240c0e51800b901c044804908880510306959076001d5461a4804440b80344240d0301c407284440c2c040d000003460403031403605100c442c0150314002d8019207580c1000074801c4182450b10040e02c10441d0035501c441a080f403406a07406184215428002004203a0354030301031015152032526582803103950b40d90304605080e42e0380f070b210704c1021825032080341244481c8038002c0c14100c83c041c54005449a1400b001400f0b030b44001c101400310344010802d1024407525070b001e03143c7c80144040203001e4600c0b400070042080c0b4030b03031040b100d14120807030303c0c080e225110742c11505000400034030f80008020b1041002d40c403150020261400300c0d4007540e010703401d180080b034080d040ba5a20310260481502c0c010080d02c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 338206996 1250 338205746 338205767
    0xb1e04020d0f08130609090b091905040c0b03040b010f060c02031e0c03010f090309060c12142109070603270f021503010317040305100e010e1f150501050a 68
    0x3088101409800c031030544c1405070758000c200d56911154407038030b04006601110210b040060003101c4403030800041e0002c8a0000e0044404007500140c5640c890401000c404480d805c0b0400c13006002050005022500c072105044c2d80e060310070241e00698460701a10524644a03000f074040d00308036859241251302240f0102810320307080c15602220020000a400c440b200340314941c0707180da00c011140905034413580340700181c41c0c0c60030170020804042d20342041220201c100346007042148203400180180700710944280000c1100e54100301403125402c50520007084a402c2008e1060030b02c0020740da88a4082d0a52148180c81c0310585a44800181d2040201c080c80c02d44003890800140c000580710071003034500f6604648c003c0ca48950440c03801c014051540010342c02e6518041c40280080742002c15500502c0b0a034117000516504907602580c090008401203d5460241c0c10340c10100b800108070140c0c00c404001800c11a420f10306941d00b0149156029090000340c050140c4580240540c84101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 338208246 1250 338206996 338207003
    0x40f02100e030a0605090d02010213140d1707030206061009064b0c03120f060b0a0908060c0c060c0c030c01050a0c0219032f01090b1e04020d0f 63
    0x3a0150781d24004245006103112084a502da40e800030000038007014010302800d500c880c0300a42c50102611000405031480e80a05280c9a03418000902e8940d94170010681541c1d00c601e40790002c45005030854899009a2010340260140c2c0700010411b00d00460203d81442003922400c4105042c502c0403510700800d41000f0708102a0440c018900b09451142c01e842d1480e200c2c07410003240203098100c5500c02e02c52114005005141c2c3e06903001940020311800c0009000344001210135605581c1c4003d8400b5501c40181038a000580300c480c0796000d0114400d59003402e0450f882621040340480c2c0d584684054090706800c11004900345080b510010980c81480c08100d9082c01c004124407070860b00107a07450540d0350b41e5881440c0d00550180000b28072012a080c2d180c540d44840e4602070324022094180c203800107103111607000100aa40390300d100091241c40208410201450540c00120059420006103410401441c070740038208144548102e03800341101c007441259a540c4a0060800d48088 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 338209496 1250 338208246 338208257
    0x1804170a090b070503040501090b1207110a0210030501090c110c0d03210603030e0306151201140a1508061e0a2717040e04140a050313030c0e040f0210 66
    0xd02c4401c0600a4006240903402840da240d103480c0001d41140500c1d0b04c007401c004020720215a142580c00441580401075060507490241e02012817800d0050b038040003903202d1210b404500c421541640494143d0703140b0001080300d01034288041c4c8000920041440082e401428156a01d04003c40c0444000d03200341090081c0f0580541e000b6181079120051f071010580c0c402d0300300305140d440301301c85002400c16001b801450a00c080300400c00c2440c410320500626151800010f901c50941c0045808484c038403104400b401d0604003140074051400b180d5680c11681c40010072048004180d1070b00402400301300c21940d81d4000200f0850345401030403451303070315a04c204510560161441e10801c0b80d04403c0078420b8180c251502d400500c0f85e0800c608840c040c02d00c010706c03007410400314035a085900f1102e61201c0c4009209a1441c4c8100154020924000452550002c0440740c5000054902c9004000c0349241c82c1c0c0c0c8591400c030400c4502038025034080c0c515001500b80303481d29010006451412 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 338210746 1250 338209496 338209499
    0x1081b10140d0903021e031207090513060807060e0a09051017030c0f0601060f08060409050708030301030c060206060d06020d0f051e060a050609011119111804170a09 73
    0x40800e6410903000303042d42c1c0362a80a460101581440226141031622070034412440c80a0301c030a1b030724065108000c50401005000c14180e03401225454010079005141c0d003045056141890017602180c402e0000310720807c0408104e29000d104010000840074265910b050b1820b6603c6002c0c03d0080c1c028080b441502c0700104840c1c08510001594400000065980e0417800304000d1802c0d001c01d00903261a040100144281c0d6400840c02041c0c4405240544043e200e240000b802400341c0701c00103207a8030030303120f002400910100c0551f040760f020381d00c22000f2554540040c1c0e02d8040803103a90794400f4130701c0010710000d006039015064500ac07500c00001e80340e41c1100c65004562b0103407a070701070380c1d0400400301c9181424110525030210b8107031442d1032414501804500640614049107062000c2d40012110841081001c18607030440d92202a041140d1424011401505003000f1405005181c501da1070365501c0010341c03800303141c2c000c00e038090300030301206140d1241d00031000001c108400b8410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 338211996 1250 338210746 338210777
    0x90b060406081f0b070305030106020d080f01090e0f01050f1b070308130602070c0303031505041b26070906120c0f0302090102240a140103170a0e0d0b0108010501081b10 74
    0x782105d06d1181d26607035500d504000c2c020f45000c400038140300130461181d04003c2c000410051443c11501c503158041002c4c0b11805595080042072800c4481c20341c40c080c1080307a40540580769038024540e1100034016200c484042c0b00c001c0c032800314082d02040041001c00c080d0510100c020700490300900c2c00504003120b0790b440040c0303410240d0040e4002921003890300e00c80308629245500414084030304000c0300c2041e05005018590740000c040501c040861004020030701c0d80766149041e5500b003080710003898281c00107010301210b800b8180016403245004001c6c000302d072040d0880700c0000c4d00c039101010b20b046401c9001c0d43c40004000c0c1103002303040300501c90391440172071800b00c9004a050301c070507032400054100c100c0300c68034400b4144c845001c0041002c03c0c80c0c0b10709004e102c910313165400c0c3d8542c4003e106076005035500700c0c3d054000310600c500801344101d4200c001d0503940c4550080c0511399a030b90001d580d5860760700d480c00d60130000c02100d4075035107012180381000304013078100079048085211 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 338213246 1250 338211996 338212019
    0xe091515121602010f0603170717040801320f0603030f04122a0902030c0f0d050612010e0309040e070506160c0506041202060304151104090b060406081f 67
    0x3034103260614441040c41c2e140680a000d40c101c81807564030100007042c51904c60360b507170407419074803100e10764000540e010902680640700e011120368010702c00da40d50b40c1c44001500a01c01d150b0740d40305401c2d500e82004824504588540010ba00c0e4030440d03a00d0b81c5a200c00b062100b040604101d506104c2088204284046200034000812500070191040c0e01c2c1c90800e4407900c540f2035101d840c4191a140015003651501c1075010a85809100050f203075601c036110b00950b07200b0314800c06811000891010040394154001c644144401c0e01c0c500311702ca00b05800d02d400d0700d00c200802d445ea034200b4009624141015031004500d0081401114591550365000c03400a03441030a1002b100c0507040e014200f4040c0f61880140140810340314640340601d070900482c8440c41e400780082c403900000011400780a203900b1145241005c400c030800103001e2048940000e58403600c0740078881c1d030500e000d489861602c101654202e68640d103e40d44d0a40d00c0807014001c101b010100685a03480300c00f0085025500704 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 338214496 1250 338213246 338213251
    0xb012102031b0a09060303020607050307170a0203180a03050d02160605160f050f030c1602190f050102011103060405061503090115090209030a02040c0311190e09151512 74
    0x5452049401210302d041c031100328040d800c22806981400340c1040003030390004404d50300c5642850100d4a9031150300d4122800345080600540c140c10440a119101d0f800340d00950150700c0002d00c110707002c05030150301a1104120300e03000e00825800c3c482e8600c001c002d600140214503808820024001d110358a1104655041d42e0300c185c00e1f6050000c0100464200540c0f0880c9655410000d0030303c50544001c143c581700c0204841c41008000c00c094480c9044145408140703940100460000054103200680303072540d9105035814005e4a040c0040c6950040c89220907800c104003083d03180d81d451001740009450040d00350b540107552a44880c10091703010010318094140c034000407445c0e90b40000c6101926025412100a091040200d581a03550001d403a1161300d41c19180401c041d0400300c000d800400000400700950b0200180103c20b51100700d030003c240400e5600e502050030b40100502c0840d0348215019100728000c00c0380780c60300e403402441807805001c0380090940340c000030941e00100280103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 338215746 1250 338214496 338214523
    0x1d0a0b04090f081b0303010e0606090109090222050d031205060a0f090203150117040605090c0d060209030106080a0b04081c0c0c0c0509060a062a05100c05070b01210203 74
    0x1041364400b1200ca1310094113441214001107096504000d10200b4807000a0809441103c000401400b641d000352100001050076001c215140d4100ca850301700558218400441c0000c1500001b040500e00542208000c9404d0360301d461420040540803002800080c0c04140e0003004c3ca000003800d00006600310000d460154000360b220304051000808101c07103401140e0503c112500109904d0703204680c4c4030307030154100f01c021800e40c0b00c2030460345c1010b04c00904a80c000c04021380c0303a414400650024060808180c000300603c03559030f2001c5450f0308130610010030259100003c10301058041000e00050b28080d403074002c0194040c40030400320303031100d00910b0225140d0781e881018003995046070001460180c880c000c0c1407a0010001e413440d41c2c50300522052000ca43c521443c0001c0405d4501181c2611a4200071942d519040a9a4070403010b0544c42c0703407600304034440000901c40c1e01580c0c02d0551084d901c410590a1200001c1070506070200041d1a2400c0c540b00005a5010840303004115507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 338216996 1250 338215746 338215763
    0x210e0f040f180b241306080f0f060108060c0910180909020f090f0705070302190311060705160f0f0b190f23090f03030705090a1d0a0b04090f 62
    0x2070b540303054062480001c208580300107140d40480e0300c0305100088265084400c440ea030a099448548600003000640c00062140c49442c90f80f14009900086100100007046e040b0b030403da03682d1040c030390307908001c07500b0058960003406150003a040100c90203200384141e040c6451542410354040c040300e83c046d444003d50076140c0f03816100b54104020000061101034520740c0541c40c2020410a00c40c0029100c5402c020b00003800c0000e01d4800c0c81095169820304098412007151818002e02410781c0702807596443c020306020030381c064021421200662141681d1072010325150321051080083c140055560340c4091034072000141c600010701e4801c0b81c42c0320180030886592000e80048420101c2c0300c0513540e00d003d030b05805850303d180c0740182005050f00041403542d2501e07080303820701110041c0d000c030921000c010f00007030a03004800380580810a4941d49259559880c002800703a43c06210210495882004565154143d070049400340c20f000e8404134010703001d503880324040c0140030003c1e500b545 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 338218246 1250 338216996 338217041
    0x5010515040b060304020d2916081008060c1e0c0f0c030a030e1e061206010f0503070f030c020f0a0803040c0f031707031416210e0f040f 60
    0x14291050b201c4920050303851608600c0c00d5400f04801c4826401c018010700c40700d040c90106085400e21844a03501d08004c1e662582c00c0c01c14401d003108810700900300106010100052032001c022002e401241c4500c00105126251042140f4a96225030581004110494490403181800c4002050040000401020640c200381d600a040040044000780300c1e8100d021140007103a40b00c5480c00800c50219034000800034090400701c4211818481d490304000c020450750503144060181d588110401c6c0c03901d40380c074044100100c03003900c0225203800205402d1142144003034480e074440c03044907003580115039042c070b00e1100305450510f2540b012500c050700041040108500000408010500ca031000c0005905694900c0c81a08150b02035149100c00400c8090a0602c034010054214406010660796000c43d5600340010402842c4282c03440400300e8240074810800a01952100c00c84c2d42d02d0801030006801004403040b51810341540c400c6d15800c1d0b110400159100c0ea201c1070354070f00d05178054030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 338219496 1250 338218246 338218249
    0x13030803160e030a060b060903010908030f010806010b07060b030a1410060909030e01180906090902030105090a030f03090f1a070f03110406030b040213080f0c0409050d05031305010515 81
    0x2801e064400010803440010891980c0c40c0055000b04495004001069500340303000440c101d40101d414490341503080c45108404e001d0080002c500031041035101d50341d075030780301c110303041da5510b081c8613845210900308909408203a080e40b0a01a040b40181a1806882d05850310300d1112801920414150000c11284220b6680380c4118001440e03403440c28090b034200742c1c9001d44110045030320203041c0130041c3e24642e0308a03072003522040581215003003084909c1c1c4811100c4000c11045178124002e61909020940c000000180801d800340e160b0744100c16100090021405015041030441c2c411032681082e00c00918030641e69104007841d41c4400c41149071041005212910314400d42c01450714000c4d01c07261482d004c41c00c0b501690341c2c5060208100c1034a0b40808d00a220b078880d4500c100da207614010400040105100c01c4108403803085480c0e44a0507000c0204844c0008001070942c0d000c40041c103482805407000d96405030022407800b407461a19107400e825124126007118240d8141148004039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 338220746 1250 338219496 338219521
    0x112090c03150e0a0f033c0806010203030426040803070609050610080a08090a090c020703020f0a051e0d1208010303091a030624070807060605040c170a0213030803 72
    0xd03c58200000c054524044c0c5485070b01c3d94840401804100007031052500e00010030030802151103801c0000c1c2c043e12000c040e592070350803460214600040c180350110b00c0d1136100005907402281c200b030720245001e511200c43c182906801000f0040b10406000004042c04d0502c0038041e0580240400301c1c2c118810b24019003800030090040500c9100254280720940c0006080c6401c030394421031282e550317420718002510303a2000b0351200b100c0364105440d00d10a40da0102c1e40e03004603442a01d43d0090b2101003420000c2c00c01d65070180d07941100008140c0c4020300c19400c80c40550400c05071024044010351f80303d42c14420321400e48040810341142c0100100760703003e40310100400c61842c1070907425600c3d5224000a01c0003910b410b201d192600c642c00c6080a00c2c0081502c0f12003128030455030b9401c0e529240d515504039440c2603400c0740c5052400036044c24580541c45001800e80e5829600350001e842d00182444041c000c0d41896909115046c07100400b043e103440a140101811503ea1400c0c1c00700c2c504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 338221996 1250 338220746 338220761
    0x7081f050f121009230a030c062301090e070918060f0f0203040c061b0201090618051f08060a0f03080307050c03030a0e0f010603031b06090c0f210503090112090c0315 73
    0x10075448004a50042503000551038239507070748800040340d01106201030343d2113202044044401c2007001400025450b049a100004001d514010784042c943d44417003003004c40d01101c1c1e40d130403441501e201c818005000c50b44070920807011381c100020107040f600c061504903041203804648884110805210094202d80b80451408a0014149040000343e0000b00b00644902c6907205100d4258440480c030400380030518040d00c4003500e191070b404c1d0f0407806030f550120a40c81050100c2c070104040740450a0000310001a200034030308011010b03185035280c294a0744010500000c2000c1880b04041d80d00c1c0c01e1000714000d4a4002002c2806945c3c9001a400c10080300c48012043e0b2400c2c0c0204006a08180c00c03040030b104603600309210383c3d001d080c40005071418a900a1a00070046000308401d40b00079019404d8810350201c40030320344148900d01d030100b01c0300d403009491503000380003103641c42d807282e000006011201032010076102c2c52640e410030081c00d503401c01c03182e03c0d0304007001226980c0c0c14406c218 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 338223246 1250 338221996 338222063
    0x8070203071a040b070320030a140403020a0b0c030c030705010c030f1401030308071101090b18160902030c0c0a05071404090b0a0e03070b07081f050f121009 69
    0x7101040303214501d04052180b8031a84d00c602070049081000d06008000d14070641d0920141a505802d2000f0b00c280c4a034050780b40e00e404103070185807036a0181c0c04c0405590580741d0140c1072a03409810200781210f580c20050302041c0c548010040303400d1003507062000c2d09903144607400106d500d02220002606483e8483c081c4000700b482d00500b00000d6151140d020304603070b05804c01c88420b89500004860300c840c0386011802a41c200b040c082e040100c0981c2c258440e4944400324100711882441090711010142c5041d005882516000d20448070183d000b15001007524803c0c902c2c7c03001c01040641001d2000380141c820b60070140d01045540d40c0c003034030140c0c984002c940c20400d0706950b0f40e600d02d08403401f421100c0b5266840d10a4000503204004403862582c1005103500c441c0390500004101d20310440d10b00f0b101014580301700c000d8038002d0160300c05440009140f56036000410381400038100349115210224482c80d00d50300e041000500c5600b4a0302d02840107440c0880880324084d6500a481d0181c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 338224496 1250 338223246 338223269
    0x20303070b091e1e010204120b0a0b120d1419180501110d0e13020309030a02010b0a0e0f1b160201030605060c070e090a020a0905090f010b150f0c06040807020307 71
    0x100c202074000c6400c1610714401c11305100d03c1802c0d101081d00a0140303401c03030518403418010000502044148592055041c03c50070702801c3c41a400f40a01120b500800c80c602c0e41c0700e446103600541c000c1c0d1705c1408500b9108540760400c5100300a40340b102e0040402c040100d07400050102900030340005c010050442803c040d84a1101c1500455481745054044420001c01d500d00100c10368441141e045030354808101591281407002507142c80794080d9804802540c640003200c0c000b400c005a40c9011686c00d43c000900c15130b9050380001c0780d41c000a040c2c20b0802050300b003000c440f00c4244080c00c1c0c8200003004030000c6040c079100140844403a5000301d40314800900c07910035030030300c0022464242d0301e000c0705490f41f50300d420081031310b02844184001e41c0300c1c6803000c000c00c07a10060703807204d407180100508a45241e0049840e841c22140e81a01442e0050002c50000b410000039000070861a50b070910031600d40400c8001c1c403070802800303941c05c450194000507920b013903107001c1042102400c40118070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 338225746 1250 338224496 338224543
    0x6100b2b11070219270e030424030506030304030303020304110915131109061e040b1c0b0d02010513090515030105070503010e011e0806040f0c06030e100216020303070b09 75
    0x4080c1144c0055505894140d141c0911031603464004400501c04502203c1d12107440300c0644030a910b4540f440210115807800c030301c41d114407a0143c2f80c01420040c001c1c626090442d10220040d610050091f2241000e00c02404000d440f5143c4440c441c02400303c2d0060003082c00d504000b560442500060255402c02212220f58002d40d021a0113a03001198003c0d0303107001040442c1904005003503540740b040c9021400250607045400188000300110030f0042d0740050307854840b0226072020880582200b0b014001c0401940100000d0001c2c0380c0441048d41425510842d9009482c400c945003030381d541c00c0c40040700b803a00b002d00a1507048909802c02034255818a61982c600304814070801e50b078440b0502c0c4808000c920400d400c00641a958107544882c5018201044030a2016404451a01004200003032107407084c841c1480b03414690004e0821b10008054400180d00007108010707061701d0540c80c2c000182d03010002050000c1c07140000350341d0b030b1a20490341401e00e0850710407459101154040f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 338226996 1250 338225746 338225759
    0x90501180201080612250509060d1a0711010204170609030406140304020d06060b1314010e090603010204170d0921080c100f090506100b2b11070219 65
    0x107003e980f00c101900c0c10b40e68520014003c42c0340118100c0c03030114480c20b5820351110b62890181d02000d4803025100c102c841e4940000380840a01c0070b00c0080c00c0c8811032400c003010b814003602e185412004600e8101d0059200581d020708a80c480d92081c0ca0141c62280c81180e024001e20015901525045c040d5050600d400000f40091610003010030341c031080000002c04541d281d0b429014080d230040c0341000722030b0f20b905032550700740d00c071070401400d051480d04002140c00d140d132402c6520000c103941781030702c200b14402446104440a00115419502400045a8085800311045000b11020010220765144c602e014011124542008040d000208a00020200020300581001d5441b5425959400201a200f03042000d00c02c1d0340f030184d40c1051541e104080498018680860140054400756110006c1008004e0641e2041005240084c09443c510a888000e43d4075000420071412483c1e614018206c000c49543e80c068040303211001c1520f800358103040d03480508101ca08103802c07994a04020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 338228246 1250 338226996 338227007
    0xa17040806010b03181902130606140901090302040f0603020a14010504061421010614040806040f02150703051c0207170c07080a06021b0303070914010e0d0501090501180201 76
    0x910302c8003100000c0890110071a0100c081101145d40c400d03220540c1048412012107810008207a2080c10840f402003422411445080c04075001500c400c001080c449064040540000f02f07140c1c14043c1030000003001d80c40b103000d9140414110480040e540303045104120f4064026001821080b100b98401c03807013641c00c1822030742581c03454102084003101c030107003810251090401e82d290324902c8070340391103e5060071074842e4161aa25101c00f20708250020402086001c0d0340303d04041d0b43c0c040c002050200340034100c005c1c03030140041e024010142c2c2c070680544107070380040012400580c0005d003108a513514600e49010079001450203501d403003000e0b22401e07914a00b80c2914040c504000900700080d000c1048403000820f490002e9031802e080604141c0000e4002e00c507086000d0115902100c0104000f1080b2032240d4015220304691508000000034400d82903500c49040c09070002454509560320710103604000d00c610b0020883c42030b40d14000b404c2d1401103180814250302030801a0040c1e1700720 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 338229496 1250 338228246 338228249
    0x105090102091903170708091c0506071718070b0406020303010501020c01080105060a111006090b130603030219030e09010801021e030615090d0f0b0a0e07030c0b03060a05040204080a1704080601 85
    0x1040041c1c0b1904107051140c2e540c417030242503991041c003e18427192003212102950308100d000c2c40595941d50390382281540c4003625a9050f9440690340000245010100200381c40c000c1c003600200c41141c0e0321030780f0000f41c582c080e07040100960b10101c0100075a41e0304120a0382d45890a180c9403403194505004512a8003440400c0c4e001d115880c103015042540400014000805038030f024400c4035641c02803040140405141d01c0d01805805801540128440c0205003c8941c5540241100d04102000584481c034121044040090000c0a41c2c00e6a0b21000d4660107010405e000603a0b604a010440d2203010306041880c15011040c02000030a0b620359806114403044000c0444e40c80050400180001d00280d5000301400503098600301440000a0400d1040441402c1084400000c5500340d0340c0d0109031100603d04036145206000b0000038101854100b1406402911440e480b4000602031760819005038219030b00c1814001c0522020103074200c3c989213601c60103071819081812841d01c52805 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 338230746 1250 338229496 338229533
    0x8060109110406120b060a030b01080a15060c060612140615150702010306080604060203040506010609030209150301090c09020a1205130209330103050717270105090102091903 77
    0x40100d113980031a200c0e000f040580c500185290b50741e101d20748015004011002440340094103200000708140610f115024164111031146000b55140c01d4045036031502c1e59008a030110707152031000510b044450010010039210f495100c0e44074041c0fa07c41d9280c01c200800c4003c5090054a0459881e2a01d03100d920201028480090b66491540010b0340a002c19900000301031040c401000240318081c1c4c055406071f4490400e40b06107036070344e28049803020f00900001c2d40c01015030002c103c51001d5a00700345c902010142c004903c0500300d488041d04001079501c841149500003c1161803181c0c0052101c42d03030704502104001904201c0200310094401c40d5000703001340303003000c04540d00070408124117003046000c4a121540d260030366511030380003008604481c0864103010100f15520300610340a2114000306d41c12402caa075604004031000411000e160510020f6241d201818503028011184a450030200250341c442110003030100d01e006088041c0c1c50244031140c10300000d00c110100003034440c44e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 338231996 1250 338230746 338230757
    0x31e0209011e0306030b090a0228120c0306022a240702071a040e0a05041e08040503121e0a020307171603020d030501050f10030e01020c01021308060109110406 70
    0x980003090f4001d100c04e0300b010b450700311120100984003c00140087d03100740300360780c218141003203805640502c107002100d000005002803c2405400540e0414156150240074100302055480c4c90300c200320b0380f0000f4a844007500296070400301c0d00c00032000300c2200c41c0000c010100d0350511400302048964089680d0705840300c0e00e0100c1c940c1c1e8420440c03c0301074070a501c10700040d03100d0751000c1440c83e4000e100720f0070702c0d01d91140003524901c40d17480f506200d141c1000c0003043d6008034452081c010103036060f00b2240100c3c00d00010503141c4082060110b4440041d601940e030f41442c07540f00d4120024154031a40c084000c10155420507030200039504501d48c0819906405100c000c5d046034980945010307196034540e1030501e03109140c0c1c006014102c5442a440412903030340c036a0b060200c04180c0b03010160300543e04119040041d03100f503000f4402290260b000500b042000846507081e68801103c3c1c1070114082a414000e13102c0038081c69004021190041042005100041059010f940301e408103112 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 338233246 1250 338231996 338232047
    0x3180b040b0921240705030408160c0b1209031911070b0d050124050f0f070b0a0e060a0b01020a021012060b0307140c06010302090402010909020a031e020901 69
    0x101c402c0407040709280b030206401c041c510414229031350f8002001d028002007041072031941820b951141441d004006030b07903416145907510b44035030034160700c501c5902c140c00c1d0f50300810302e0118986240b900c000d031203000045c80d07407160704881c4800381c01005058014650001c2049d0582c20540c040c11926440c090f003404000c55044489541c00d00c100741d800040d250100041c208403010440c0d1120b4142d80445014444440b003400065610100c3e20419130041a400c0000f406903d640d03401512082001415483c544042c6584481891030190f900d00a1551030700001d0408030300c18418168010b454400c2044900c0c09000002d50b2181c140c000640039000181450400d50311400600d034240301078a50900400c1d40d01c0300c10769076680c400c03104400090550020154040c4295003158010f041100c020400d690840d0200b0003540f60161049060040003074001520170003c0c00074046000c419180019020103945507120044021245044150320410242c001d0744e07000a050780e200f000304000c942d44007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 338234496 1250 338233246 338233249
    0xb0303040b0f07031e08070815030a050c0103050105010516080702062502030d0f020312060f0d05030705010506180a090510020c0c12030310090c050906070305030403180b040b09 78
    0x103200341c0e0041c550514000488015a02440000b048081d20980d00e02011002c40e542e56001d521840c002d074000554070802042e0041d1041d049240c0040d40420504c1c030340c0410a00080c98500c1c0d84804031a2030b0048076505446682521815006010a0800300d152118035140241c100c0e4040100425002e400300349007081d5101c01d02560308410390150500154003541d100489903001c4800c0481c400e206d0b080103102d9840c031414281c0460039042d0011400c08030b9110352400d1042004003403540041c500450310b00607a48070760301c2006113070250300650741c0e642c4c10b070400c2425600010700c0940580c590310b002c0d4030b03040e0380d480c2019808650720700c1c00110b89035949462030a00707021442000015001243c00c1c44188004540c100072203c1c05c81c0c5074807030310058072881c03600c0e40400c0f200c40101c0381c12150100400c00c1144c00c0f58440c542d040c034109240c400c0a600040326600301002c2600040c4010003000700305904002003894110320403030a5001e241c60490100d8283c880c602034118000c6000c16602004d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 338235746 1250 338234496 338234503
    0x507050a11070b0708090a08070b27030703080a120504172d0a021c051204050c060409020a03050a14011202040f0c081e04050a0b25051c06080d030b03 66
    0x98070702c0d540200c1d03071200301e400e2580d45c50b0011400035100319a071b100002100e2a0004003001150041046c083c24204c0c00341040580e16074154132120701244007448201240d03030034040803001d03510038881c40340ca400b45484010200400041c810303101d6813070310003440007141d401c007aa0076410500c5d0f0f0040b81e482e4444150f844038014004a0310301d01000741c0d80020701c1e2900813406031100c00741607400c0f107240c14203600030500c11280f80c402c104045002084102140740c107280090354010b0058003119041c02131407001c40c3c015406507001001e150750101e102c512841d40b5014150300070b00b03650018085003202d09003181701050180300d003843c86081040010110340f2070340c10540c0000724000e402c001c410b028940140030b8500495180d440d00107900c141041003c007020304076000d1500b1400030b084021442d9660701881ea0041d0129001c40c001e08080e401d080c0c940a11149800040ea80300c90711900c04140c010186d18520145051284c10004240314000b4001903204c5040b100340f8011a6800c2c03441c001ca0306 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 338236996 1250 338235746 338235749
    0x60307031503030908010c051204110a08060406020702090603060613020d1d0601140604030b0a02030a09080d0e06180c06030a0204050901060c0c050402040e04061515210507050a1107 80
    0x1080c04240400001d02da00300c044e410844035040700030f008100800c10704035210702c43c2c100700b181c04070340d0517000c50b0200d810f0364060000c03118007800c0d5014072a244c0c06514a852011501225a0743e000640b40c0c0440c00d229142642000b03060300184220b04102d4000703100399440311615401158045402608141160051945110040510a10310351040680ca813515801d0081c051407080320924000c580c1480c104880459420285910060700d1340c00101d806540b028088511031034a80300c0041c049041c0500401081d05042c170002034a5440f52282c40c18180300a0411180da003c40415800050001c50054140c00b001c69449940340d4403400a80c009001d030350051500302104030008135500d9009949100404d00400480418135518002c02081c7c3c815070040480c5a480d8801080c00602c1c40c2c0c01003100c0e440040180010140c44070103400341000301003405000681144001c07912051384648210760201c140e6006d1140b4a042d000290151041c10000b208005144180f004114000d02280c2c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 338238246 1250 338236996 338237021
    0x90302060711071a1b0a0f060b010201061802120a0507020316080f1b3d0e03031005011b0f0f29071b0203060106030e010e03030906101203080606030703 67
    0xc0503801320440351450300312041d4000f03180c02c18030740001400d800003070340201503600c01c1d0032054244240e6582800f070855000c096042d03648501d004585546020704a00b403681d00904016101c10103106801c081e04005400c0413045450f0030144903031151301208480b103950080e490565082030034644648144100408481040d0000c1154605240c42c080790b0240ca022030801c0b03400588605015241d010403440702c005900041c101350b04000401e0300003004507815440f000240714203c040741c090135a03000726280f10212100c107209014940c1c102c2004c0c1d00101c180000c451341c01180d0754034a40b01c0b40d0080c20240609242204190811240000e0138a1049158003400204000c02c01520160b0000b654a107011440b03c25001948058002c01050341d030350020300421080c4d19006054000381580f850000c610b5483e4900b501c0704072001c000543c02340c1a083c004144925101c1c01001204115400c0401403401d0100707291f0200394412004c80e00400c089580c16030326191148194018000000c041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 338239496 1250 338238246 338238269
    0x70c03050f0303010807081c08060f0a0e0a1a15030402150a020105010501090b03041112070e0f0f0c030405060f070e09160809010e100911220b0409030206071107 71
    0x4a162100c040090f40c100c40e804400c84002c10b4540e003189881e4040c01c0f000c103000080c140c42c8980c4483c410700040c0e8008501400700d2003280f44840c00300b9210456074005d020701c03001c2c6c0024032908014030b1050400b190070542d44440c40500394400114401c650210501d103c0a0101c042810340d80c5d1100940e001da10010686544c5003626400039019040910030035010442c0080005010441c1c1001c89108603400705410074141d00724802c12034040420420011180b00d50358020444c81c00000f20303079006500b010b4201560386458010030721741600003044038140003400c0c400c0c00000b50f0000f80f04c0d50001e100d008030b1003203542d540d9421a20304501d62852644925003400384032140708a0035138131484040990f181059540d608032a94240d1b4003c411758a459071065090b248103401c25032000c820b1034442c240c00342c0401413003000500107802201ca004684698110440280c00d581d02c1002813000d400c1d070b4144852099a00c0c040d44905000741400c05000340d105c94540c6034081400b0b000040c14006121 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 338240746 1250 338239496 338239513
    0x9060f03090606031005070e121006090f05060103020c0304030b0402060702040c120e030310060503040516080d030c0e0a050121020a03020a09090509030a210c120b0108040215070c0305 81
    0x6071503503100b090b54018000c1c000c0d00e055440402d158001c2500c01c044584404803805668018403051003c00c0540f24002d0281858207041c0890300c1c00346200418045401087c0c010700140c0701d2040310406403106050500c1003124412565001c4243c508590f00071025011555442c004580c051040c144001d5200b4030b0300c2c01030b4840c03980001c041c03072104410202c10070010302c0307007088280c2e071388030948600c80101003400d02040124400c00096601034481c0040d60b008280140300c4003c0c0d030400746c2140840750001001450200c0d03041c0328411b03000034a442c02c4e500f940c0703c110129000020718050b46040050048544020800110005001d001c81c88030455441e0152003000f4000c0d0090601c010002d0f206000003c1d0900050003030038040c61340740002d14544034054900380d03200d0790a4103a0305184204103150004504d4588103444840d10607807584426140c01420050440e83d65a512340c1c107202600040c80056101c01000301e5110200c03a040079660b0708c66046c225401c504541c00102a48100511b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 338241996 1250 338240746 338240761
    0x111522020a0b04080d141812030307020705030d0206010b190302071410140603030409050702071d07091e06050a12150306050610022a0d05010504030e030304140609060f03 75
    0xd10451303034010240c60159940c11000c40d00408540314450080c0f400341710030704040d90040319210005000510b800c43c0c10b81c60b950480d00f50f070002c490b40000b68221905c00c0000c1d0809020110391071440e803018140560420054214a00585020107070b030090344856003000c0760207581200d40d5940c200d40f54031402c810482e881c03a90390481c0d0660a248a0400040c9124110b031589900e000c1d1000a01842c2420f040c00c015900410780102034400b1071254020015440c1021440303070b00c40b03000a003d040c004e86008403001c0e05907405648014444500344e041381c21614104181101500c105240c0281d88040d403c204440700c141e0364104c1c0e0001c0b440c00040b00700080d400258401242d200e04014800745c2d84020810030280a880f46100140c1c003c080384400b043c0c40c2482c0b100055058116090b00b1401d07650106860707070512541114035030340d200144428140c000e030502e041900214025851310b400e00003501901c90441c0d803168041c40b0041903454296407800700b910304200070800441e40301c0c42c1500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 338243246 1250 338241996 338242019
    0xa050910140d05030d090206130303020d261503071a0702031504031403040f080c0d1d06120a020f070f0605010807060806090702070305011803111522020a 68
    0x124484090703062480e8a91a400c2c861004044103420030055410006989800700c0905500b44049a01410030014041030240e11203c03440a103001e03500801c0b06901012000c0c01200320041c0c03442030301c9007020a0558603800140b003e03502084084d00e0544185c032460120b440c01c0c45a82080c034000c00048100c4000c01c824502400e40b180c021011103003004001c6000c11243c10094402070000b9455401c000b180440c0e010081d80c10903c1641d13900b208940719200e40f11f0641010320342100c103030020750f94103030750b10341c40b4000c0b49540c0302091090380104001c00c00200c0c1481240e440e4000f5580400000e000c1900343e1303050f03402100310070507440c0c0c1ea100075280c40300e9029002001110740503d80350010440b5980041e012040c3ca103140c076103883c20344640341040444503004142d0801c61081407400b00c0098020b02600b08025245500404a4906481c01802c0c00810a0a20200768001c4c0540e000020001240c17135006440c1c4000002403c04019038100d441e125104040d4100e010098000307034140711030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 338244496 1250 338243246 338243249
    0xf10110d02210c06010e0903160c0914060a090e0f0d02060402130507090302210115090b04091101030b0a030803040f0c090b150c03130312270905060a050910 69
    0xa21884000b902c42520079105000c0d03a9481600b95100354014040e600391030001a07040030940d01180d0400e51030000e14095006501000c507803a1515034001c0101c003450740606c3d500b024034182d0888403840c18101140d0004081d103c1c00000710345415200728400c80900110f8405d0241d182aa0850115581d01940e01c0d54182ea040340940c69802904501203401d1089034000c0c0c14035642c548401d4074607000c011404a140c0c0f014425503001d08040000c0e4203091240d0001c032030b510019401e0451500c0040e0f001c82c2c0310080414040c41c240b001980000c1c070304610042e034004003400c0015205c10b041010070303890240740e007000708585800020301c01800f1b0300f1034181103800d105042c41c401e031a80319140306e01503854440d44903800c48403000c5c2e0300003550043e1002d4405000d4a0084904003003801c0300103001e0040540c0305441605140002030b880990200c101580c5c06034a900741c680d20180c0f40d6108000e6407461264a001c55900c4012070107a944401d00340d8010240103007a00521304004154a400c0f0a0a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 338245746 1250 338244496 338244523
    0x8010f06170a2103020c030d05011703090303040302091008031c05013003021228020601120b0a020f030a05060301320a060302030706051905090f10110d02 68
    0x10845101c110000010703008110b0354498941812046880700400143c62200c00ca0000d00d0b03002c0c00b6005001400f04043c1594040480700850355514103180100011201384550149400c01c00c00b00300d540e14004221401c90358160380c642000d0f6140c02600030664550b80002c2002e004c00130311002c03d05101e5080e41070700b00859004102da0f036601c0e0059003e40308003094100381c803402c90003044e80b1102c0100215240034003e0055070040d510f90800d001460784010a8003d01d2144040d030600d024968103540c240c0c0d01c42a000501582d418004056500c600c0c001c2d006255501b41d400080d030180c140c0c1c060718400500f42003140c0d164144220207102804007100d0150103580f0f00340b0040c102d020260341e8840500c0302c01e40c0d401072401070180741d003001c008001d00d0720042e103484490000042c4c908202c1440203007019541d1a44400e4503100518516118909401c100301b410310408600b961000c2d07000e00d42d2a000c4440081110000d082544c101280e1101003140b40111f081c21088141c01181c400c0300c40c2c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 338246996 1250 338245746 338245769
    0xb07140f0c120f03240a0b090f040510090501090e03030402100908060c091008040308181203090a0323250c1403010b0105180d03050d0204080304230904030806060408010f06 76
    0x11000c561814000341030116551040d8062420400302c0c3c1f840300140a440005828446490218030100f42680d00c15200c0da030a0704018401085001c149220b154090000310bc800e00240c165844115920f00016101a100d40d030640700ba210454002e8014500900c248015203485140c204080d80407038001c0450386000d01c01c046103071000c652041002030700c00c035856201c1c0c0c1ca0075120103071403002c0c0b060302c4110800c00c1d1040e034076000d4000f000a40a90311a0700007000170b2a035500300d07103401030070443d03060341e102c124004032600403590030304040a8510081d242140c99550070b200071400741c810544e85c070001e0040d0106101c00b041c00f44440c0c5403000007003410380c028408241c1d29001141d80d4070071103004202c640d44482d98500345190100c0c01c032083c01c2c0030b4a0003d06114049180400f260303c039134083c01e40c42d880020200500303104a1031607400d038150011403003503c4085101003000020020001420000b1150000700e40d5a030700f2003628050640c5200810040c000700804600500c59409030040004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 338248246 1250 338246996 338247031
    0xd05130501020606100e0307050d080306030f1c0c031b1109010506040501050702060912150709150203071407090903030614040213030f0203280b07140f0c120f03 71
    0x1400003c20600400c800750401e40c60b039590a03000c55101c0c842c0c2610320380c1405003200019450355000343e0341b4841d6002d0250f440e5a42425000c05141001601ca000c0e02604081070045810300c500c00c00003c41304031403d000b42c40c0256444c00715418496414220000c80703050a000d0140324600a1a030140801903c0003440303031345c0703650410010303001d60300c1014000780c4104030b034030010300300000504284c070009072a00c10254103c001d41400c2c074842048842d081c80090080080c841c3d40000e21000400d1800d0121900fa5003400000b51684280315001d81000da40700c00f00e440c000003c02c00c0030000c02420504010145403480c3c02000391070688921031840c0600e441e441030a2405100b2590b10f00801208034000f10f1841e6181841c5080c00c20f420381e41401003005245001d54440b40b4002d101071003030300c0081914800d15055400c05809851501000140350b40c900742d10040f00c044403902c4042041d800d031580505c40e08149407c04181d42e180740c41001068016490411101a5016450540c200b08414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 338249496 1250 338248246 338248249
    0x20c0a140414061c050a05060c0d050f0105060306010c11030304090903091403031617030c040306050901140615040b040303050c070611150a09020306010e01090c0302030412200d051305 81
    0x802c1d096644960116510748000e0001d85420040001c003440790702601c040500e29243d482c14001c1c1100c012402c0000041c1c4101035400703600c01d440d070024103000080303115414400419a6400010142414080d800c068102030200c0c00ca03210301c0c03591004085a6035039880f0940c1c82c001d843d000c401200030404068000c90910800019903606c03441c050b00950801c581440c0c00b0407a044a03a0050fa080c8ac81248105a020396070300c000d42c401e80034010760f16511442e515200d0219070b001000c0700d04592410101d034804800b0740500c00c2c0c100702c1c00c45100407020881c2c2100701503881150b10441c100217000900004068100b0040c102c41d50190701a07400b0641d07169420790b110440310754840066002251001c2d1040c0301c41e814190085205030307000400b00419030100e1300d8148281c1245c0c400c445040c0041240401c02d004010100314140ba0a504600f800c0c1c1da0200145d2000a050080c0700c045c80d0400561420840c4080b0001d1600c81100c03408d0b03a424001410395400071110a250420340000824103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 338250746 1250 338249496 338249531
    0xc0e01030905030d2313020901061d040b011710030c060c15020a030e010c1e180b0703110d030c1b150506060c0a060621031b03020c0a1404 61
    0x107050700000030b145080145100303800285095110051a080301c0140116207020380c40f071440c401c0e0208010010262028010429a000145e00680c204500070400c0441c1c5a07070021070060040c41a600495511203401c0183e51528454120004824600c0100030041c08010f40c001c04030ba02510211038041d450b000d08039050407601c00302822903507881c04614424030455005240300d00c098034000404644549400b402d48104012080006411070140c2210718900c040000080c5903904003491070540c40c1d4101c200208883c418a54051030101d100d105050080040540c000c3d0010b05440e12988050005030062040401a40c00101200054100701c401c2e00307a031800054010311003051141d00b19580300301500006000c1030301300c1070501403074025940401c0b0524015115002c0422668107001404040c2c581c00e41068074600b8200d10340c54003003504580550740b540002c40001316403015a0409030301c0c00d540103940540204014000068110036144200b044031021036040c028000c21401174500b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 338251996 1250 338250746 338250761
    0x1507152304080309071503050a2405060702042003150d021e0f03010c03060801050606040609062a080301090f090c0605071a010905011a03010b1b0118060c0e0103 71
    0x110315004001140104400300d0181d135000e250305040710141c0fa122002d5520b40d03181412218003090700d031000e110b400d08103070180c0300707822075184011101104a420462043c00c1c40384115401030303400103541001e41d181d42d00040e42111400380c10380f00d040e40051900d22144d10441d07804250807070504010000f403030300202c0307240555002001030030f0444088410404c1200d661190940c0090340e004d0307034681c90314203004510401040740c80005449140c030307500e542175410040502e8400c00742000140301c001c0e0000aaa401c1d900145410344c1d1040c60300621800c1e1108010072084400c6090700d92008210031703a001507060790400d80040c4140c060000d041025541484801400007002c1c1038103000040c40b0320301400c5c61a00583c040e1201c1c196902080c000041c00303030030215515460b40014480c0380402c0d0034041041c0c80c0341c1c02c0245590b1505550940900803810f5060341303040da04200c3e041e60741003500942d001440c0c0c240f8004440c10586407180c000c0c812145100046824540212010342c0607114000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 338253246 1250 338251996 338252051
    0x330a031212050c0d0f09170406020705030604051c020a0602070c09061e06110109140106030506010b0703050a1b060c0e09090102040f050909030408060c0a091403030d0b150715 77
    0x600703040d40c84910002900c82075181d178030300030f9442c100d40c80456080002030716210b1240058a50359810100b0090408085401030750099004105000005000050350021b241c2480000031400c80d031410204c0c100030820300003801c0c440c0089414000d100205818004507000407008000311961111990040030580f080716001c8441c00900304545402483e841007195108030002403490801d41e5008007107142d00141040b940c0d903441c020f004000b020000180034020059004d402e0501c01d0350002c0c1a071288402c4035042000480000c40d9681d1000c1400d1000c42d4010740a21245e900c1c9140100f520020309442441030304c10001049034028103200311400c1d6114000071b1000103050809202c101200a040d204a5100401000030b40040a01c00240943c1004403d281d41d80d00309a401804031200b50450320021589401007a4242d800200701d40c08a80100e0001c1410903455002544c82e054038041c4241c0060700051103010004806000386042c6441441048075200303a0612151082c0748010b0344 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 338254496 1250 338253246 338253271
    0x1c050106020c0108090102130806090601050117070f021603240b0109030204150b12160503070815040617010b03070803070302060f04050f07030f0201080a05330a03121205 75
    0x25542944210750280e0b21600210003d4504188505209001d880d09d920014054020000303102c0f0b480e00c1400a10f00608091a1015903121000d944078041e52001e4031900501000314000140c060007800179401c4a01d070b03039030f560ba084d0b541da007040b504011074103410196a01108034440780314151403050748030078041a51a591068215820b0100810310840c2c0c0c020240a11040050440800c0c0020451055a01828107103820302301c245c410002c1d000401001400401d00800c50540c0e404440f0507401012206290740035113080e8080b4004001d941c1000d00c00c000c131030040055a03401500302800c40601034084913202a52440751903102e0084080080061700b00a021828038078081c0d0742c8540250081082d260119001000a071070030700c080e40120f031880746650400f001e540e084410540d208407040000e20442ca03012580d1203803054076020019081c034103600321a00c4080307081780400032843c0103003449103602c1e00e81c1040240405458141c0300000d003400e50190203081940501405048030b440d50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 338255746 1250 338254496 338254513
    0x305060a08100b12161d09060a0b12011a010e01051e0703090803130e06120a06110c01060305030730050d020d090c080c15030a02030402010c0c03081c05010602 70
    0xc1e20b000d00038403c0980c0c2d01003c0300e908a4406032040c0480410602529500e04a4603d00303401c0a070302c00c160951000220450000300000c105010a025500c000c1c00400020b44964540019071406000d6550180390f40c030303204030384844082c01c140c030034801a0300740c9441c0c8100d003000c00112814425284443d44080142c0e50030401e02c1c00303100103070030700622038205200510303150305203146140c01c1042c1180040440b4403041142038058802030390004810344440e4a480201241c0c4c03590365013049402401c1a40d5200304c100345040c0c0c003059075810440400240000303981d80c2041d42daa90000030055420304805072035244038510310310300a0a40740d4200e0040308465225a81030302c1c2504403045045466800300194941c80d000c51003070302100740c4640c2d8443c900c1c03030501821504e030285483c07500b40200101c490307400c9601145000d480d4400c586550159a86c3d680f44012141c5000d8a40014081c201d0600040104413640c1d01900200b00c1c640030308000d83ca00c3c00d03007400680f01d00303229280c0540c0001a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 338256996 1250 338255746 338255773
    0x81021021f1209080918060a0501090602060f070e040204030302060115091a031b0d0c0e040b06070f1401050c030f10050108040f03031d010902120102210717070e010305060a08 77
    0x43d540c070f1401081481e00f4a00804041141a90240c150640c928055403c0040618203494144090b05080c40c2c0480941d041200c069561a03015042d52034469142000416541c803c83c00045903000c00b40c01035446603034070b284c043e5a0301000c0c05071714030208030750065030b00782481010004119410f07000e003403030442d4a4504000c0c485c1e002030005600a240361441f400310003c0700000301000b14a581e8002280032101d1402000c810090366480c0c816400c10b000c0401230b0361340c003040d91106138201400e0b9519882d540b40007803ca60000065840c154206001c002e61f121080c8055403203004d00f20f01c1c1203070994903e072044150300c105000f0340d40800c10200104001ca1000c641460340c0906c00e0600142412919a140c20b001011041160181c4e440f00052030440c10454098030040c4012402903060118844208241800d20300031003120780c03007210016200610640d9000c1e548841d0410300e603c00e0500d41d40080c902401e102942d03020034100313804140c0720b080100c0840121042c030401703850801090030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 338258246 1250 338256996 338257001
    0xa05060c1e0313020a030f020f0a0303080a110d0501030302071802040303050714030d1b170606070215130e010f12030e19030803010f080f070f06081021021f12 70
    0x180009a0704502e0484000180c44a080b008046e50042102200004180c410002c04a010041d0760780600601d0404100280c0c008000302d401c170b44640404100034040394801816809180e00c280701c05818840008280b6402081790000e44001c5803042540ca80303d01d101c1d44c160f2140d03210040008030201b0a401c0410034044980724030042030002d4926007004214201d05448040010144981e1001c0800c10b4041d008090010707116050090141c02d0b207000c00009030103005083e4080c1c09501e900a071003c10804840071180480054028800ea041e1138011451890000340900c140d800c801c03490108032048031450340015282d040c1d4a10522101c0782050182c0d403040c00c0000e8643e6104c0c2c034004000548150080e501030005401c07007010f02850000b4040c074200c000c1e100c0d1a040c2d0040d01081c4000b20500c501e81d0180d84403810800d906882c4d410309e02c41c03d02010340c80039034171a9a44c0f1100d1001c51a00701d003112028000c48113083d010551721801009024011079a9011903a40c03d0304c1c4c2c1c890207454 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 338259496 1250 338258246 338258251
    0x1906090809030f011406010f0c1b0e010609030501110f03131104060311030c0a0609151701090c030c051c0902060702040e1e060103032001060f080a05060c1e03 70
    0x5000450a0240ca2000329141503001448041c1e241d4641510500400c2000c4d00300c6c3d4402024a00040350500c000000b5000e105030100103030088100a901c0b410044191340034800600d05410845895030355528020000a40c078001140c0550030308ae00b1160441c07094050340d04c440040c0d807c1d2481c58440c0740d0010708180191004aa001c1c194081813025582c0385e10810004500a00080d42d516500b5400c141c117051105002e580f162030010401c1c8a0282e009502c041030360503c181928242c6140842621207042c8070001c00031544410f000400d21642e00d402502d824040c6031814821144016025105800740d00280581840300a40403034504105420070301baa140040d00076894000ca07500420203440001408290903404a800c1e2210181c0030000700d103000300007001528995043d82d50052404080441c180600b00c02003181d08030f045029445040140000700c054a91607503241030f03c40e1206640001590705d0700911000071000078010084441c54082c1070540a48110050340172015500301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 338260746 1250 338259496 338259503
    0xb0f010603111c0b09090a0b0105060c25080604030e1f05030c0d0f2f03040b180f070326030105060f07051f050a110703020a060e0f030f0903060108190609 68
    0x559204d00300585890442c2c80c050104140a0444c420a500708840000b6060340a00e00500c01000841c0000c50301040c1e410320320700100600b0001280c1c10a20b00c81302d00c4290050300442c023591083c4000c054001c040100c0710781c020398002a0307282558000140e41d002024146000c41d03010400603100254070402009000600d080000f40c40505501550861f889041040003614a02003021103420500000300d080360810440c0b9440c2d0f25080d90f5484070300074080c060f5400150208903203560320b0070900028000700071013402c4600e095500c0c201201c010721030700c1001c9502101d0704141c0c142183c0aa04990603101c01900c6a490001001110b8603540e10040098070103019030340d8480c05013440c9000640400b2480c0a001c00c050414100c83c03000c88140740e8143d04401c008004803c006a004070b9811415504a42c001402c1301e40320704039038240040d010b5041700f6404001429051240320a0182c118080c0640031103050340c0c1c0340c0070801e580e4085074640c003111009a99010300007560f10780109000510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 338261996 1250 338260746 338260751
    0x6100f090801060b0304050f07120303090819020a030e030a0b0105090a0209060c0a02040b01030209010e090901180506010807050906130b040b06270a15050705190b0f010603111c 78
    0xe480041d40e00316019500640407489002092000b44001040624003851840303028007116450040c8103500c904095800500341a22200e80c0400c4c0440741003500c030304030328080b0310400345008824000e403107655a1104401141e05408a80450b04001072800311031607011489101503402c1108000c3c1000005146009032502040100640d4459401800d8100c62000c0104502511803042105a0f04c1c40d14120341014410f20118049a134080003c13440040e0599510039503444075131096024200c07601d901d074a030320000903442c41040740c000341d843d04031401c04042d51001929002048000384c8107541956000c049040700b4000c3d03c010b03600c80001064001c0c000540c0d0851507001c10000d400001d40012400000c0301926103003e83e400b12885828802c503401300801d81410020207000300c80d0350040080000106000e410440c040100a0004000401d83c1038629a58903107454113560407104006031030036070400099640c1c081d004031080041e00c0446541009582c140722300781c0d10328445044001a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 338263246 1250 338261996 338261999
    0x170a030309060b15040e0a02310b2703010e0a141603060504060c08090304090b060d0f09150504050309090613050a1d070f060819050c07020f060306100f09 68
    0x9442d41070790054038407000c41d929107071490a21540d621b03040040000507400c0c010445200030b0007408107507102503202c190552400a0548a07400c1c824003960b00807100002002491489001c81c9001d0410503103240450407160000c100d040c542610000c1c04404180d074013040c0c4410000e1b201d001c505500020301c0c02101c6681008400300c01102c1070551055450540e00c5082c002442900d0240101e80161400d00e02d00c0c82c14492038181d5071f480307144201c0340304603950400201d01d81e1b10642298420340c0000810300550155000c1034005080318602114076007007403c840454402c840c09245d00c1650408040c5050000100900460301d038020000b44d80a481c001d40140b400c140381c03050501480c2404000650003a11440c030350070b880d080030014005603004040c10080c01842400724410f43d0b074030b458018416182e02c01ca44100380c80c4070100c0c3d100c1701e0402d41003000c400904400743c0790407030085800702c80301e1807003800784161488107542880d00070002007840d590717150155240049444003031400c086201d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 338264496 1250 338263246 338263249
    0x7151e0b0f0103110c01061d130515070e0307080d0816050d0c0905060c0f1e1f0e1b04060609030209060405180a0c05100513120804090204060201020a09170a030309060b 74
    0x50310700f0380200308da82c20442045c000c0c50401030300c029800700d0350444030030100406440306590f401d021418198540c1036030300081c11081c03065000854031040a03085600c1d4030b860b00342e0191100100d203005030006da001c0700040c100c8000301c200c5046c482030b1600c41c20320b00070011120304c01a1904039212002c3c0401d003240040d8a0f241c04004092103120f1601802e1292a14000141010a1400302d04a80e4860b440c61498541020441099076100c203200342d204001e2228080024040401c10040f590042d20042c4041d90380b00700c00da81210400b1201004066220300007511301011500000e9040b00d00309001400314103059102d41e0b0419451050707003512600403051640740070140141150340801050301004030f810103042900c019900e505140d81052080080182202520f1050410fa05816a8803405000c0120100c50182a1a80e019581c445d1940d1019000c1d60003610f1560000b200f481000595490305004111300b400b140b00581203a08658400302c000e0006554162030082d0749080d00d01d410b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 338265746 1250 338264496 338264501
    0x10f0e041103010603020904140c1812030a02060a0605100e010c050a0b0c1e03040f031b080a05030f0610051815030a0e0609070e06130207151e0b0f0103110c01 70
    0x1306015a8090713941d01c4440f0500050b00c24851010202d010610305028500c01c0307040c01c0d100e5132000b0440b841207080c400000030f2100c0041d412041d0860000007030b094020341e4003044403481400511030900406a43c0c1e018404401e80c0850f540d40041c6004200350f0745503106000c0a040c04c0c3c024001c03601c2c0700219840d581074100c01030300c00350281d10340055200003900c1511440d5051200c2c04204900b1441c0c1a01c0d142c82d1040c07a40310083c20421004001814044600c00344e520701c41c4c00414164845192540180840d072050300e64901616880340091001d2800c0000c007121903d0655409081c2240700c00707450260b1140018503640194a00b11080701240c050015600c1042c1c0c80c940480e9010341c00c00c001e81003020103801d42c403413600000c01c2404814424040390340c21000c15141c00313216103c910700f07940c020701440300c004200c809611130401070118590051f6882415040030701c5190410440c00c1d404442440060682058220000c0c499541c041d6101c4020004c60b01032481c1790070000d0071650708 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 338266996 1250 338265746 338265749
    0xc030c2307061206050f040c020f10050703060b0328060503010e010609051b16030309050f0606030706051201050f03010b0d0825030c020f0103021303080415020c010f0e04110301 78
    0x80c1540445810801c0702d902800e401da10001d40041040414108000708000000c4505668051611907805880943c801c10213141071a0340030302500c9940c0700d03800e9102d015100035195000042d041510200c0c0b641c3e4003804490151441c00b00960010b10304008181c0719840c0c080031403401e159a405e001030035860078003d0640044255000240450070304286000326000a0920600c4001d0409196000d4204801715000324901c2e013008501c560581c64210040d29500f8801800c3d4015003407940320100001030000d0091808805450119032150822144ea0154424009510210200400103810141c0d00008083d4001d400807921380b510101140d031882c03842c64110343c006400900c900340f441c42c0389112072000540b901c0030601042240c8005011074a081c10280c881c4501ca00151003136806541110100c00003c00c66001441da2400c080740507030401e01c55007440140040c1d0144e811840410500e0103110140c49556698100c62011510074200411450b0041d41d00d0112008602c0d00f00302075030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 338268246 1250 338266996 338267063
    0x30b0f1005130c30150303050a050304050a02130c0f0f1b020319050615010e01080402090604140c0a0e06040501170c040b0f2106030606010309050718050f10060c030c 73
    0x109002c0c10424000c11140d541074840c0b90040e117102d081c00020f50020481301e0741c01c524588a6106d4035a41041410a454800000d602440c0061107400d000760039040118405615200c031804250590000c0d00e003580403210301313000100c0780c414401c1c0b2841401e1519440a00207400c5680c14082d98590040941c510007051310720358010000c105c8a0382a04280380c080000030f2803c0301e199000640041c002040c0a00000c3c40380e4032460010341c6944441d40801a54070f601501c508d6942040400c0c208680d020700c1e4039a001075010075000c042d6017080401c603021584107a480340b1042d24600307084d005208000e015241d4140c0104400180303001040c01428901e0006110030380e640c0008691541000c4400c1d141c0c0401800c082c08102d1150b03070110300c2550000003801d01040901040c03404031305081017500007030110f80f88040307002c01c0c00130700d54000c921a2120000c514032944070201c0d1414a60f40622680000908900520001074412445c0e415218030070010002496070750500c0c1008810700e100c855 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 338269496 1250 338268246 338268317
    0x70501020712090810110c070f0614090d080703200d0e0103090b16020c0a03050d0e0901120219151e0f09031416030b0f1005130c 57
    0x6038240240a8107030691510ba0b0f0030b01d00c0429281c021040d44600403506603038103280d560002011940d50340000c88030f4810081c401e992600303841c5e5040f9100d68549015040c0081d040c07941e040540c0e904801100c60b103200050624903410003ea03550441540301d1701080f403c112101141c28483c1ca520302030396161003450005081c030004405030090001b030080c44000d0415013008000c50104294843c4036411460341700f0b8a10b120304a084040c2e282c002c500085a030040b5114400005009000c41c0c20022a179190b0380302c2000c2e01c070000801c101101c2c28060440544d1242c1802d03001403074070750b810b00c00c112070441260400b180d0316a84074140540c2d0289a03400b042c0c010b2540b110000a25580100201e41d60601002c0768450060040000e22240002881406500030488160750100003040b560080c1c88884142c040d101c0c0703002680e860046d00ca0080191111002c9244c41402030041803e403803000e4206000040b15120b61000f92203420001401e1000c400c20300031900070f402d146000561440702c0c66 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 338270746 1250 338269496 338269507
    0x1080109200118030f330b060c0f010f060f0b12270a11190b0d02040e18010b18040b100302030d021605040b010807050711040903090302011206060e120c040207050102 73
    0x80d42c518203881c1c0d072000c10b44220070085035a19050b034524140c0001c500c00040d042d071f001c8004c14224441c000d13640b58075104040c1e2a8280c040150000c803941c0031140801d004a07940c4580b24180b48113540101428000706001c01d0291030340303507111540d02c10402040c0e041d10030706c00307103290302d28009843c580402d07a0400030101c0248200300c001c02e0344400c001d98183d8860303034001d61401d45402c440d0145c0701c0048000900155584a150140d6000d00340707041d4285d840c6e0905046650382250040d55a11440d402c104645685203450f102e115001e0901201e15603040d655030f590000102801050240403c018003004800b58030100001d45004a1580040400241c0c10b42d03100044012a44924403880c107001000c8050390780803030080c4d04511079040c402e807104c400c0d2514600c00108141800d030010310b8560744030305269000d00c260080724001c3c0c0340e2210040680100d9000d039411405100003103058203180ca10f5038186107910b852000c40000580c0c198502c1140003601780da0110809070b48a81d0003045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 338271996 1250 338270746 338270753
    0x30c05030316080a03231f080327060a031b08040503040e040f060c0e13020403020604050906030f0d0e100503060a0b09060c0303010e0109060e09060a1505100f020601080109200118030f 81
    0x1401c1c42e803032041c7e0300c0355083c440c81c019116569108800d02c0741c642c0f504201040021541045c0396480308400200741580700d2603c0080203001b4003a03401c00201403903150710100d43c124040c0c0e5406009540000c051032415051081a180b03900001d00100c0303501c0c07181e0341c001f00070699911903030702007441c5e5950b0b4a020100c51010031146554120b6105442c0b4810002000141e5482041341c00300c0f80185d030610440d9035004c0c0004d081940d0002c0700401401110004a0745690040e0041c03d500c0e01116014400c1c0e41c4002d0031a15800121100d82e08819041303003d01c030340030301c00c400361800710002010303039140c41d20820145045400a034840362942d8040001030154104038001c00001e446001880140d40c40d10040072640c4400281c141120783c0da0760403804103200d581003000b070050400035280e80024580b41c00000c6c80401414011001401000008a9901c1d41030003a403604a40007030b0710075800d01c00e42d41445218078000c1c0c0844e0600806040c0c0309409445800301c030000398050300d10400010950304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 338273246 1250 338271996 338272021
    0x3063201150504120204050a0b0a14041404031b02030123010807080102030c0a11070b0c03070213230907081608010b010503010509011205071e030c05030316080a0323 73
    0x4400700180107041c082800034a01e4000e00381d01c207503012107020440d500c80314900401040203410740d64002404031000320340d051106684190041046d2010031910215280c00c41c030301c3c2030980300280051084100740801180801d203141100380014000074515640a02c103d103c01154000001e800100760300410070101c1c1804072100a004160080d4914500101455803070311407c1c02c003106111080002070319242080200c2c0001d03144010041c1c2d0707912300d2120f495940380c0003c10304911a154900c0589a85105801071582c28102280089040121501a03a0122a009014039101c2c0318520b8006501c0e0001c020442c040c6c034004400380507560410348214255010781c0e100c141440b1003000100000e40f6401000d07811941c030622894240380f030f103245c1582400b019520085101c16211052100f0710000b4400704c040300e01c1100700e5103506603600b080c54ac890013050505a690303581452200c0118004100804c0302c00980d15000a140c9508511034035450108001081903007802020801003540c0e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 338274496 1250 338273246 338273279
    0x607061118150a0e1002150408030402091005060d1a04110705100501050a031104180803010f060806130b030a050d0504030b090f100b010203090d110906010f050403063201 75
    0x2075450350301d0014141c5014104a8100291318054480b20074007a441e80d01c24400c49000741503400c0d2580d1036040606003074115030825135003a44203c17025004100f0340c0b83c5501200d812030301c02810403424402040340c140020024070740c80300c0401441d41c3c80d0110b281c1c0c0303910a820b00594006820350b202c04007400c0c080c0c90584e540b02000320b0f245ca040010b000559030f1f52600c1c4100c0b40d00100201481c04442d000c200030700300c581d03103e143c2d610340c08150004121254006d541170342c81080b001200165510030441d05000251100ca400c42880c250105603000e19400002800b48080d04862400c26a50781e420700d89031f408a032b100c4c0000c50114092003040b8103100c505400400070030080c0850a100500c0940701d85844c4c58940c07407540d03504030031100e60340280309a5580c40e400404070301d4490306a0522203000c0342840c20182c840d00c400000a10a58080c0c40d20100b0100984d48207801d0500303569503040180400010019986040c0702c5022609580f2042c0e180411103800300c6a1340355152012803c2040400d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 338275746 1250 338274496 338274529
    0x30513081c05071b020906040912020703031206050603010302040f110d1406010f021c09050303040b0d05010b0f041401090b0703030902092a1c140108150f060607061118 74
    0x10942c03800c0001100300500e130392080d0110385118aa458080000e40188140c9070001c15000d81c2001c00a0041d0300070511800300c90094440c1506d40018040c490700300c812174001c1d680c0c8460240014005400c095101c90041c5da42d100d8001840c0d00440c01059a60f00300410344e425640d160764020300c907030b80d4407060b95403c90028204000403c2e8a0300010303403640c6600f9004800411601c3c80d00c810300b80305040240c0100b8002c0c0c1600d40d9180c035031058561542c400080ca003803890404000258500400c001c60b0002c400000603542400d0400c422201036541020701380c2d0402c038211401003180ca490760000c0400d503209840001e0300507441d10500c2040e4100600500400c040b0340c00051858032000207040c03800303030100041a03071408a40f004100e41c1e003500f1845ca1070340b45050303004030100f4080c0c001a41607568610444500790710412441250304012203110601e60511400b160007030500c0c1c4040c1825a110381780204058000d5040b00e80140c02c1054000c2d15000e10548010361424800603101c4800c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 338276996 1250 338275746 338275757
    0x30f01061b0b07121401120201030e0303011a220902030103060b030705012f03120103051b010507060c030b040912030c0203120609090a050a151d0706030513081c0507 73
    0x1600d07100d41070300e040010000070600c02c2e8540d200c24100181d61024511031105046004656111459030701c09007d0380c501240400c0c0f425000814600e400401d0340d0407210000350604040d03402d5070b040700042c0c2100b4150f078440d29a210307a805141100601a01c09460401401602c03589103042540c166111440c4850194012007002d0001da644801410040040e1000c80c2d81c0c480b82c00411000243c0d41e124100b2020b0001089210b503a041c540e00b5113041340c1c026011900c58006994111818018030807000e8042007040118400141586d084144000c489050000f074101d000c8020030300f0f07034000710021103015482c4480703140d6203070701480b4034608801c01c0e20045003001200c3d00100a41a0058080c900c1a07142d5000110001410800b041d88076621605840301150700d0301d8003a102c014100049070881707007406441c2c44c80181c1d88030031100c2c0c107903000300600c130691070120150010300c0c001c2c00c1c41e0480460039504902042035500240b546144420b40c2c038074100e0034500d00100f102c03400b801c80e104001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 338278246 1250 338276996 338277047
    0x101101020c0d1e090e0c09030703080316140a0f0e060304050703021f080c070609081c1103060303180102010b10180f03020a0b030903160614070207081504050304030503030f0106 78
    0x243e0200c6140151000014000c0e020f8841984106e401e0040e04410781c2d040c803030000040f08010043c0051800303106c480e101208519003000058503e49800050020904018440808500e104425240c0c40700b81d6410500c0c554000f40c00464141d91040791b09540952200800b0011030419031000444680c005903601d4144004400c002c003144000740c0b94845030f10000c1151400d02440350b01c050300d007603401001c80c1e640e122815401c800c03a9400881c00e4440070300d8020070410000d6200200ca1007490001c1c040c5240062682400107801d0034540601d04566880c00c040318241c03910020b25000380d000c5d464611958002000c41d046081058020040e01e559503c010401078072a941044203940e80040b14035169603075001c20034614010902c0108906030308043d4003050041e56840300d00c0d030602001c0081c000e071344c51900031399881e18103118a900a40c8200ca10f6954498841e055a070032501c40c2065034a060b580307444041c0703141c10540c1e590745400b40317043c01001210b810005d103040318000d40d01c0040741d08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 338279496 1250 338278246 338278307
    0xe132105041a1603081005010f08060103051003050d1701090c0c140309090a0608010b09101710020d1506030e06060d02010e0a080c0111030903060402101101020c0d 72
    0x180181e10a0384103a6101482a0b1a01202c40082d200e4214a400b0780307100042141c10000d14248040d9610f803261341e641c08000c29554410100040c1c800f0300f980f501d00503503d44000440090070010b000107040ea00a031300100000b1030522888070140440d554144184844140840d010740c01a40402d26280c44e05d058a4015504204a07559aa8110607510441000d01151504500c1019021644802c3c00c1c0100040240740f07600500550740d13140000c000c42a110014000c0c2040d0603505e00c541060800410044a03110601289204482d401038401c503c0c140e662200c01c1c1d030012201c80b405c403511003a94510487c4080301140040210703240c148100b201079600300c4c0d2110320161613107004603060390b20b25027564000d40d110644040c020301401851641e81c0c54041e25100e88900300390008020b043c03161a0194000184c442d0b0710781c018003800d929200c1d0360801c04648040c0e450001070011090600310044402e2010300341e51400c440c00340c404d010301031800514203401e50b41c1c4002c41e5200c444014010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 338280746 1250 338279496 338279507
    0x90602190809070e041b081b0420090d0609060c0813030504090b010e06120405010b0a181a060a020601030c0506040e060f0a0b0c01020702270c03100e1321 68
    0x100e503004d81c03000b03e181c0c0310ba003001c54a22000c00d0f1070800030a110000000e1440d00007a8605024003100c2c03c80c56160320705800c00050741c03591400c400280405181c4443d41c0e05681d0002c1601000041c0080d41d801c4880c3d44180c01e498822206507140c0f655001c0c0520702070b4020900341d45c4801d6001064401c0c140c142e8000d01140580c0c001d010080b03640d4903084925900a0800c10b01c51b0400074982902c4500080b5618507a0700112400c6681d5403d100c2d01260710701f8003400d030100b6141203804001d070701c0114039280d4001702101880380303204502d0b01ca22120300d901c5290081c444508a540580300c1581107091000c40380000b588543e00403507040104202079440d038640c007608598221500502c4d030583e000050202e040301d41181c044200d0004070010a44015402010303664425a0400041c0d10400500c0c000030742840c011155000f10f00e000104003c00c1280110340c40802003207010721482d25105001c0e40380e44102c40800f1004000c0c030014081c405205420003070304490314001021052641c0e0300404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 338281996 1250 338280746 338280749
    0x9040b0102060103080d0c0315090c020c01080c090904050304030209131a190911040e07090605030a0f0314071703070315050f010f090b0a0201150f050904110d020409060219080907 79
    0x5000f5500c0c5001c1c0b00d600c3c400c3e080007400c0c00589c1c480741116910366580000030b0903070005100262203503143d030812a50141d40c80c148101c0401e80a41d00745411207050101000c001001121980003c110100060f83c402000302c2c010542007288096815192030b101c4042d02ca10fa00c40c01004c0d5160741044a00b80e20f50012526444494a000c80e03011440c0c034240a4081c40380524a030701c9801d054400020440004a40084600d01002803003e141d07184107040e00ca04804802610602003540100d0100b0300a003540800004001e01c114548840340d02c8540a1030400c00c0c06182e01d0310000184000983d00d40141302e0700501c0c2041c2c10100c02c0c6031000192a149007484240d041c44030401c1a568101d00901981c002005d88600e4107a469409880081c000e0841c0801300e803100e0780e9083d0108445215640c0c500c10355202400d00340c410780f00d13612820000010104841da1002d054036101005841302d014010b5000d00c103030400b6031281d00900e460036109140030910341c20406480c04000025500284840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 338283246 1250 338281996 338282017
    0x703020310120302150c0901030b090103050703060506190308040e0105060c0a060b0111061617040c0501030b060d02070b0a110c151003170409150501050910020f011109040b010206010308 82
    0x2000e8942d140341c1079080041c03094144030181816400c000001c60a0f0b401000300640c00d0780c003040120340c0d500820055000a002c0075101d5444120140001440da51007107401203001410f115614400d0241e40e1503511407500100c0d0440030200c2c0400c0385c0d5a0342d03c1800e000d06000c81c0c0503030500c13070302c04241640c400c4660740180540e62280402c80342a4001e80009154418010581c1c0092034000507402c4001ca640302034500288058068080d040c0e200074925001310350118170140c1e01c0e481c1c000114054001100c2c1e060340030074200308a500ca50351b94401810054401c0001c4030080c076003400c44c90201e8150780c500232510741c4100450f248042020a480e1450f170541c49000401d80c0f42c46140302500d4003160030003005c840c0044078401404900c0800740080300c200c49010b0103500c0a4210025086a032841a540421805d00401c0c5952625041480c1035005510407079044070709400100b402d45503214445640c1e0100018a002541854050341e85100d1082c001882c1c517524556443e45640f01c0e24030b144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 338284496 1250 338283246 338283269
    0x3070b060418020936060a020306060d0c1403160f0509010912060204050913120203130302060c0f010c03020d14041707151a0906090402150c01020d021308060703020310 74
    0x14980030030301540c505d03030003048091006080b9290615010b005150382034001c2a00c5242c0000d8410180c6008880c440c0b88060f02d8035007014002c20f81a005012420219020f000104800300b01b000481e0005d140300d0303903184007400c18103440914040c00e88a800d444840030480200140c1c865640c205040d0000c54880d071030019030380c00007400c01000900841d000154403810382130a104003180385000009510303004034104901d802d60004142d075a84100400700340408803596040015240200c0507103041d205070b00030b4a503140c04907400720342100c419150788400301f0303800310b6044040c80c4c56100d41c00404100450400072420075440d002c400b400c0039640e200e20f00f8000101942000b07144a128ac1c120f08107030a061110300b02204040e2024840d240486016500c10b00c0060f605181c0103076103034003c94000c0c1c0410f60b00300200801c0c0500c0e500108104a8a46d020045145001c080d88000e190a014409440d851603040c21982c44c109440a0520401c05005005006400c400d40301d41d80200c0e5043e5540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 338285746 1250 338284496 338284501
    0x20150c090a0f03050c030d080f01050d06140103120f090f050d03090806070c0b0606070f1502070203070e04062003060f0103060306051008010608030406020a023003070b0604180209 79
    0x90307045000d60070000011882c03541c004200007000402d400407400440950f0b0a035001100c04035130300308046680411211042004100d942005c1c20400034441c0280d40c00301e283c400e410041c0503903203030a90007220701c03107401e1504544003584140c220101c1000c600e03102d0743d0f03d840d01c0741da0240c0203018082c40d4403a83d400300c0a101018012540b402c01041807a003521103600c1c003108050701c15180e0307100030380354441104009800c41c5000c90482d1915a4011041945400c1d203440f441354000150340b01d501806d50030805c2a0140e5402c004c030344020080400055400e1425181810903640c1e240c003468451080d4050314140c400006044d00c0c0d0010701510390071502c0c610000101c011380f480c1c0d4030281c1058580000e02010741c034040100000d50700100028814650707280c41403680c92090f03110307180c0142c110462900040c5040001a00406089000000000c140700558040c3e07590b1440c811a25a0002920034100301d58400502e80c00ba9044500300203001c281d050307104052040c404002c1c401c1003440700 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 338286996 1250 338285746 338285749
    0x3010b0d1e1205040e01090e0a0f03210218191224020c0d020d05070b060a08010e0a1101020114010650090d02090a020403060203040320150c09 63
    0x200c240341d02d400400038003044182600182c1164401e02036400400c500c1000843c0c2206140540e48061024070014441860341351101d20307075000a420201c08100d174813003090085525a240300540307015510401690398085074040e035024060a6030b032501556011100540340703044c0802200407647c4e0000c2c440c034800404e15203200700000450030100c0b4440401d13000103030461694058082d040084088a0810040d0321042c0c0ea0380161144039400580e041100380c0004d0005803c07071341c0000019100c0c0b481c458850014600351040074410070754551280c2283da05100c58071003800c501c0f6000b03000810041110601aa90090050041c802441401342012036a04c04012011001505028905046d200b002c0c1c2c006010f0b598003603a940c011012070140512500209040b9001c21000500940b070268050b402c1c4412a03a0040c15440542e078240700c0040818070074001144281d20a0b59042000b1101c5075003c41d115540030018141680700c92038030b500c10703001e803178126401019103080680c85d00e60080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 338288246 1250 338286996 338287043
    0x14010b04020d0923031606020c10090219050604060c02010e0909060610030b0d030c030903060c120f022b060f0306021321020d0602070b10030201080603010b0d 70
    0x514040e005403000824241c0c0032800c3d0300a42d0751621900001050701c070b0b5419a003e41131204601808107410411200742540f00340d90307440381c1d11489034402504008464010f90f00300b800c6090720f1820140c4444000301140381600d0b41403100d203640f501030207001c1d040070085075090045000e980c1c240305402c040345007507a016201a0804510081c1807002c1843c109a03079984030401918683e00a103811880514514003901441c542c1c04000fa1a12201c00c0b4542c504907100004004241d050261005022020518031b000720380c000008c40c1c84041480e101204c0310f5003120031900004055601c1404045280c0c2e0a44821022429104018000b0405e14110400081c01d41c1c0c0c2c040100c10121800c00010014940c02416503401c0702c241c841400c6564000200d1145828110103480c48052440301c001858200381d0b45405500410b07005003032410584e40d20050b084241c232080ca0380d1848840070021903900141056100c0d105034000c0c1b03c000e02c080081038829031044002003882d800340210400309261130 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 338289496 1250 338288246 338288261
    0x5150618040302210711090414060702010510050a030203030d0b041d1b010e09070309030215011409071d063406060f06051b07080f010c020118050a1401 67
    0x44111640d9801d19240c084c1d03850b00900c0110b800b44a01c15501540c2c1100142580d82e185d4001181c80c1d40c511200d4200208084010310444101d450000c01c440502030030000c0e075100f01c40304e4000184d2030405c4200000d858035240e00ca184100c3c1401e8062005840110642d15440348210010550382c241c000010054030903030403140d030140842c01c40c00c4142003000800e042c2d004544802401c1040b6070702c00441d101d2004201c1c15400c4030403c00450300143c401c2d031010060354040e1040d02d40100cbda00103030501c202400c1e4011f14a0360710360b181603d00d0b032608548281e001b04450500040b01e050001144100c030800300302d40c5200d00c0001c10b41c0513600100444143d207801c43c0380400820840d1005403d500380e000d006099030894504080815400e508600750000c2d200182c60703850600c6a990518070306d00010030740d076021a0055990006204004002c1c5100c480703400d200100d121261000d0083c00c407404842c699000074101c429410100d140481c03103401080e0829103490341036903111009405055034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 338290746 1250 338289496 338289529
    0x25030b060a02030403030e060a08010e070c0c03030818151b21010806090106060e060c01150602100b03011803030e16080a0c170c0405091603080d06060507051506 71
    0x20020725596002c0b0040050307921903207480011003d02030078031500e40a802000c4010a1100c001402100400c0040960056075480d0025807120701e50b403410308840c0250b04c01c4010400c40424041321042e4011342c041c450840c04010030f49455140910111544090010b045115845140c01d440c25010811960800910a8901d0300c03031004940e00040000244603039280c1d4000c103000f294003010103009480c1180c00990742c040300300441808008042d031055034248055942c8100341010254400182d000524098015121920b00800c80409a0300350300761080c4664901441d4031200304213000d03e10704440c1c06280c0081c4241c6034107002c03840d25035070b5001801c0651483c0c03400580c0447c00103124145038482ca49010b0801d0f40c55800c4045c082036440c54007010f40010008204a081948c406544040400d00f15821541450315030345c100d42050700f0690314080c00290400c4001d5840c0108402040d880c502107180c940f041d00c0349510707640240780c140b201e03464640106080360b95010080003a500c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 338291996 1250 338290746 338290759
    0xf0a080118170c0619090b090a05010c030902030319050f0f090a0617040b0a29090f0405070605180a061809021603030203061503270625030b 62
    0xc00128107980518100d030840790102100782c01004407420405841803004207000814007510340178080408a0109080407544654846584001c1081200031501504a40000e00b091840780c1c20013509655034001c0701c105050404810781c0050701d002084610b00c00c400a5550b44641c21618201c440384a1095040d10041e00400c042e45184400002072403260b01c12a41c01c82c100356101015120031080782d04545500c540800010003064500c60420707480105c0300c47c00243d1107803846284040010006041c600b03146400661411070a0000350360350000d0f104111498245455a038007696401d0301d01a54042090101d41c0b100e041c0a1200b810b10a5040106100c4540340c035200300921b60600d2000c4403020542011001070000e24034401c907010007411507120b80700d00e8855282a0040e42c0b000d031015800000c500d041d050041c000f4400f66005005205050307025043c400400c00104510741d40100240e04401d003072140e0300c03d41600300e00c3c0300c00a031404044a41c1c01c0d42000d40044c848081e03000e40110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 338293246 1250 338291996 338292011
    0x6090f0503040e070305060d031b0b1806090a05030f0c010624030f150515040e01090b030d081501110f06010f171b0f150c01230906060f0a0801 63
    0xc000300c0a881500d500c85000e000903030310f400044041c2c50040d903e03180c0000308544d40c01d01103807140450500000311885684443c400550b10803010100c101c51924041e685000d00d6144d00d5400e2120641102c01d08000b40080c00603a100c480d01d903c10013002c040c1c02c100001d1603000200c0c0c00c2d000b08004290022030001032950744565024615a5107441c03100192030480a009484000d10560151524910828401d14100020b00c2185c12440e20b450640400a00000079900840d0011318003070706140c400803500c480144241880c01d04042c1592090280311001c000740000300750303d500701e8100c003482c1000580703101c020181d052409907140d0b00c080703014080000c550301d000b9903100c001b169000d0245008500d010a41d075078035005170500c20042184203d51651042c80c0100f41034100e03080090141c0d0081400941e40c0c0d443d03601040d01b0001e5039468a5801c2000e03004a1180882c0e02e40d019200a4946030100b112522102c004026501c2100700c20100a030945540b110f200143c040c07030f4000c01851 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 338294496 1250 338293246 338293253
    0xf080105060108090a150507052503031803140304020d0f030f02070b071a070e0a03051b09060d020108090c0402070c08060604020a0f0f0512070e130606020a0b0406090f 74
    0x30602180c0c0c41c1d022401d0074001c00c0801da80014902c60007508401026400d288104402020340700152065040201c240005134090079850b141041c0404480d1034050642c5140c94058291b40061890300001c01c02c02d841c44021980080c08020300a0b81c8401841d034030780d21403000402d014400b1001508881a079091041016080740e00d141d4128ac04d0703001c50781100d6899041f40c14034400c810300282150700d4481c518074150030303180312203400540b1404c0c1940d546091202044007901c40398400d86940d408919035801d4220740340c1c90001c0c0060161019209403030800d002c00c0184580302d000a04005141002030140384041c080300c0070480700104155560300f59400c2280c0c81c4482405260100e019141c0841e4091515108540c480325464440c0b41c04488d907400700340d8041c4004200c010502038100700d1000605102c6c0307000d51140100f92240e00641c1014800d1200076807410511102440c901503003841000c1d00002d884400d203500c21040c2e0240d59851600e030020b490701140042080700174601c1003081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 338295746 1250 338294496 338294501
    0x70803030a0c2336010c141f06050603010308070b04060f020d0f0b06030609010608071205100810200912060103050606090f150f0415090c02120304120c0c0f0801 71
    0x1c0c81c80e00505442c0e480144480310303a0380440d51340710a80c03605a08540002e55402808110366050049143c1d082840303a105c00903017440140680341824002c52009404409154415440680070959110b1708560441c1d41c1d5080d00d00c034031074000d862100001c1c0017408104154106a0780c601d075009096448401200400cac01428070102010380090400d0840d0106007851021380744518002005c020541c6d282c504180c0300c600010700480300b00802449580c4807039005004480c003c843ca10b511180c41803400c48544d040001c104003900d1814103029100d010a01d4401400862502c60001240d8a2800d4000104041c100c00f180c81800c0c010030000009001000c41c007a4800e11064588019941c0c0d00708040c01100011525443c4500c000404120710f07040482400c040f09501900c00a080360f285c810518134501c07254412040305841c0c007450a000380d1305106002250800b03000e030a04605042e0b45120345a603071803000e5000c004485030007406000d00d54400c10000d01c0000740c5610310a49400b000c501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 338296996 1250 338295746 338295757
    0x10f150f0602060402150a0c06090309030b070c03080708060a1a03010f0e1e07140d0c02100603030212071e05160f0e070305090304090c05040f08070803030a0c23 71
    0x21103521005000803024000f245a07807055038000c000d01d02e8101c40302111241500303d5042d1400300a00344d007050f00000c100d841b500c0c210300e00949800050a255241502d02040000c019404129080700c0f0400081c0d0449d541c0341d0060107900300f0f0401561120042400b000d811351141008130310941e01001e6511244009505940d803001c40445015121300ba0104400ea0a0f01d52020700d03270424400c0060344042e121074980240180c60500c5241d05c0000100c4000e170030561002820968400f03820251980402c060100844842810b0014610b1900c0c041c1d00c1c0c00303000c0c1400d207403180c00241a40820030480c040803081310764600c00000000660401c9070b038920780d1905024207900224404101d40080c403031040c0407202410303100c00c0c00756124481140942005041d1450610081c40041001700b140d005e09010030005a840544541c607220100c00203d501d503000404641054409200640c400300c22280d10441740e034030101c1c807001039031000c85441d000194203404104188003201742d1041541e00929 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 338298246 1250 338296996 338297009
    0x308040306050108300d1a030c01210e0f01050f15030c0604050d02150408010c08130308041e050105070801060f09140d08040f06020105040c120203060c0309010f15 72
    0xc000d03078132402e1566481950500041c2c1030401044070031310701d5003820200b080c0c0d410303040300950070554001c91001c1070301c8607140c400015505400d940300303550130b042041d1280b14030246801c1da50200021440d0001c0e242c40d214500f0340c2c0e904e82c0560030401c44100b09000034001c2c60320080109151040606050304000e9901190441c01c403410986a403074001203d00002e1001090645007501e04410082698450340c4102d030001100e41a040b95101444040c1c401880c4103800410200458a0003c014000c024642c50401000b4503000c00440e500004036a44075501486a1100c1d88441030780440d502c6244000504646c00c00e030805c048142e000b50464125401a2140e00c0c6c0c0b040c00c50f00070b03030b15076204c0e000320b10300c0da410b00300d14500c4da18110b102c25031a640580702c070502d01323030315400c2c1c03420035407415008100544e44070001e01c01040b96240b0500002d003203940303803140c1e80345031071740000d0b250740c406041c0980d10007020002c64010312013948081000400300b03804000c0000d0121262003988424030519 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 338299496 1250 338298246 338298251
    0x40909030908120a081305060c03090c0307090501180e0604030302160b071805010f1e09080109060504030801170a0f0201030f09030f030e031e0a030618050105130c020c01080615040308040306 84
    0x8450211b451a00359a07584e0040162030280d441d10302a0030b1641009096944620816541e621161814040000508210328000c00d00d0360405481c0c8950240c480d4440c9000c07440c0c101081072000303010030003e400a90500e00942e0340c481000c0d400e0b41c0d01703181e100007400b442098030a10481682103586018146000300d0b030240e0f010758460064034254805009500072801d0541035541c01c191024401070950203904242104c20340301d405050848110460446500f662881407009168204070310500400d5181100c0603200044a03409849080201c002841c0071348111000f011a80260410094110300d600100304114103810002c1807142c02d40c49050100f450160340d4420b0350800710459a03c9401c50b070011001c140c090071081d0360365212044a03001c00d541e0380d202040804910351810980c802e1030001041035410001001605a41c0210380071001d4076000c03061b00351070340200300d2480629007420020100e60301c07807010504c00f0a400c2070303600c1c00520004000c0f0401c5143c0300a0001c5d2401b9240c01c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 338300746 1250 338299496 338299501
    0xa0507020717150c040f030506060a0807082503140c040f0b01092d081015030b010b090d08030c13080705030a0b0a0f02070311010b09040305040909030908120a08 71
    0x300601e5841c0e0b541c03003456640201d5480320000040c910300b103801c551085405840d0070351321007110042d045c054104450503084002486564909040e445028201c84009041482d2400e00305564034948214441007048030001502500303101c07588841c0003990068a8401c80741090504241c03510340300103000f441589405242002c0303011030300c501901d0000c10707102d401615050091800c941081ea80b01c902e14400454540c0c186030814024610042192400912000300402030030b50a441d0442c041608603140018200702140550042c607044444c000d8045640c0c1643c040030861104501c01c2c05480e1000000034444100c84040c01012094070850300a44071940740d8104a840ba4528485c040e4564403801aa0700440c2a10100942110710040002256103049181c0000d03600640015004143d44961075052180c0038050711010010031174a03520b062410303580181a80c01a809544a00c90742c41c985201058010604030021f007a01d40101c400034810041c110b0300c5a0720094003d0300261280d0003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 338301996 1250 338300746 338300759
    0x1020c0712050114150f0f040204030c030210110c010e0612010303120b0303040f06030c020a060c08060108010b090a09020a03090206270d0f03080411090f150a0303050706020f09090a05070207 84
    0x607901800c40171000318185080c803002c00c0808803402c00300e0307a40140d0344811550b29a55130320060008500c44c03100c078a0003d20710300401802e0071005aa103428010035200d0450805000719508904410908001c02a0003805002c1840741c007070303150b1406c10b03201d00708004424035800c54611a0596041502448540700303860070b240e101e004601c038194001c030b52071b00140152402038115017102062841201c030f5014903a1a107806650302201b040010030215400e00045503880780220740900440a0454030341801e101c0401c28000701c0340f250140aa50200764440114440c0c0c03c400003d5800070320498030b6081d8100c8010061206d8845c03514000100c4030800c0413820440ca00343c071259008082520300c030b20162800e59511900401c11140c041c010b803103103041c590b42c1101d00c5008600713103440500741d407400071454030b00d000c490b2040c60321580c3c1e0114100f000a51007402c80d0000c0d94412000360b03c038030300c916440155026548541d40d001410908005010090794000b6104501030780c00c131000c451350b500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 338303246 1250 338301996 338302031
    0xa021c0e0f240f0a0210020c0a14030f0f090414040302030417031902010504030e1f120617030705060c07110409170d0c02251701020c07120501 63
    0x8501074026010030003140c0c65140c4080207003101c1d001c0e80c1103200360424050a5104a5201440c00c0c8807808001c140b1401069040201504150f0405400c500d0310344c0023140250383d280ca480c401880c44542d030384034034a0001c0a00c2038880301130105503c1501c030440e4488180264011100c2c0358000e91504000240004d60700400074011901500554170306130603c074a07900b070070346001e091030581e10003003151420202c190b00042968000c65400020b00b41003034075000384096101034009224584d410850304425025610f01c140f01045420010f0405845130f00442c046c200030751203580000b1036091a00c2e0303000d102000402c03981c0e11540540c2c45960307d41640d0a401d000e000e00c05042e2481c031000c020b150781030550041c55000d025119015041d000d100c3c1d0201d4991010110f00346107070b21101e1101880b60108544240b031075840c0c101c00385c0c503003500600d409900c1075441030400306100e002c040b5010090030b604a44003141c43c102a00d4496880d030848151610655008950641c42d1000d58665011002c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 338304496 1250 338303246 338303267
    0x806090601030c0501110712150f060b2505060405060f10060504060e030109060606030e0106060302120a15080a060516050306030703021003060902121e0c03010905040f080a021c 78
    0x2c4010300b4040d06000045401b44a00301c0701c01c00711312603442d02180681c042103060205910a00c50402d6000140d144a8103036903c0307010084525044c5403052001d028480c00f5101240000c6858070003101c2c80d100c0503800082c0c5160054031034050355044c00107002012868511641074408154036580380e200b100c0000d81c0c04c83c4500742c001b4070244001d1101c103204e1394000407208002400841c1c984259101d82003100e54a0380048003280d0341c0e01c103070000001700b030041c00014149400d0440c20324009564112580c0300060003030303d145903907201c22415840c03a2808000901210740441d0340c180b107945000030040c0003c0e502e000041e4a8000c040101c0349c032130740459102e06005005440000d155500344504081e00d20f682030203154a884010410541c944040d000003c601d0361080b01d036003482d407003010078151235485010506c0c0c0610104100d0180e52030450741122004940020340366542c0c00c1100c4062480305004001e00c1d800070f5004865940095060441c018409a0b0711418281810030b40324030001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 338305746 1250 338304496 338304503
    0xc01050a080103030c08040b0313051c082205030301090c090f03031b111315061b080901031103070f2a081c0c021c0c0c0510110d09080609060103 64
    0x141c0052000a20a5000484592040300031a041a84641d003110180e001200d070081c0c0c02041111260501804005020001d02510343c640b03c03941d0b210b08000c181040080c419600c00d504030f13900904194031009034143d0b85401c5000c0d00d03101e58488200c07401520864800d80c002404411001c20206480300f00e4008680e0702d510b0b190454207004848a0b0084018070301602d61072080d030070002d00740d280c03245c0710b0000311045040003951005d060707200442da800c140c01100401071040740d070580c0039955808000c100341d017151006458812400040707001d00120b0101d040c240002200344245141c002c42901c08cc0780391034852403010b42001c2c003c0c800c0102d080c81c40c1480c000000e01d031500800c4c0c903a0024180100c01460f040405d00604d04104140d40118440d0801a4810810b41d1800d4165140c40a1003e05c82d1a01102401954541080c010380c0384c080c03544140703020000d0f28401800b81d48040c65519050043c2c0344c5c3c400c04c07010b01412a40d01481421000d00034100011030b5440c1c040b0b1030f076050f25070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 338306996 1250 338305746 338305757
    0x504060501081314070b0904060e010501091205010204050316170a0302030d090f0803040c15030605060405040e0a0218070905040209060318030403060e1006080109020901060810050607050f0c01050a 87
    0x50fa10f20403406103244240589420104d071840c101c400740144210005010341c1540036a44064040904c0700f242c61700c0e0f00c50b0f012004840c0060009a03400000b0340c0c2120340000800004400d01c4c1881402481254080740d03151046118022400862003081c00840304060fa100d84070030070751580540c9518100c08028016003080008030b0054015a00001ea8140034a860b6480710b051a80e03800c02e50351080c0c4058641e41e904c54402c000780314071b0540340850b982007403500f40040303490140411264007450140074866030b1600c500051881c010065020781540060800c80380c140c519180003c0544180c0360400002c0181e8004141400c00c0d000321070399628060b00d01da2a6a69519001c01c48020711581d604041c0804c21000003c15202d00904010505d02c0c00904952035480f90718208807085c41c0d01401c0a641008500005070395070010850442c2c440d03090441a03661180c07452007400915400590b03018001240c81418044000740840507840240c046031081c0d02504015180340c09080341d003030005007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 338308246 1250 338306996 338307001
    0x361807020a0b22080c01051303080403050d180f0203070f180c140a0201050609010e04080d0c02070b0a0809150118020f0706091a0f150919140709050406050108 70
    0x1076071009079035400003002216909101440c100b26420518080013920390101c04529191400700031306c946504040711004e091080c4901d541c1c0035001c4170004001405020000c00d0280c4030f00c203250440400ea002605c0c1801100c08186441010085180c0f0b040e8000d100d230071400b00c1e68081c0710116005440d0060140001d000340c0d60b0b040400380189500010030403a5102c006440d903948000a46841009a0000300300d80c41c0034000c1c0301d441c160591280111003111b0040c4000325041c001200c110706506c900104d008031181c0801d03860308a0580c0810351003200007070103462080c0c2c1310380700600484c103c00540305283c1d40302c4600901070801380200d0802c0d00002c2c0700074021401642c018268640d03041d45d05400c040d02e40d10340b003049501400c5c040ea119501c00d42354039204160071074660382c00000100d80174076904026040861030a41e281009008101103c0801d20001d600c2d0030b10f042c2d00080315014004540c0d841400e16071400c05581d00b1020075540f170408075041c58a8000c40341940e0040e5101005076 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 338309352 1106 338308246 338308253
    0x90611042301030513060c0e0a0603140c0c0d08100519030201080a110a1103090603041a07050a0f080a02070204050424150605361807020a 61
    0x41c68042088004a02e0b00f04c40e605c0c02e030708004001010010320400b940d40100d90350071140e0201d0b1800c0d0024400d540740d048000038040302940c11641d615501180034490040d0a00315045070008094050b102d4032508286e0341c8800e841d61f002084079a10000300d00290324034810702041e40f80d2100148255608103411941202c482c0000b0012441100174660341070165100102c01c00c152826084480c1d18100103484445000420361b070340e030707040502d030010203c0b040703050419071030680c0c10003d02154014819500a030495450304400c2c49044d403021940d44000070407040c40c082d824401040980c58910610b841148615000c08604041035001c2242038084c0e80000585030800058121404111012004440041c10100c0c1c82c2e40c0c0c141d0426500b0640c000000c00b08841090741c0160f003001d8404038a821040646902240d03c030720301180c0e030103014201d40d1600968400740760207000 = true := by decide +kernel

theorem cover : BRFrame.Cov 338129496 338309352 := by
  have h0 := BRFrame.cov_init 338129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 338129496 ≤ n) (h2 : n < 338309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
