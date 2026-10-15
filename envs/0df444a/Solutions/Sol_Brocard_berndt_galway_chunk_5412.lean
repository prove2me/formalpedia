-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5412
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:47:20.080329+00:00
-- url     : https://prove2.me/submissions/613f22ce-9b99-4e2d-9a48-a65f883b6ce3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 973201438 ≤ n < 973381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 973202688 1250 973201438 973201441
    0x61206060c0a0b070e0a08190813090509010b090f0f01060f0e0916030b010e1305090c09071713050a030e060d111c1107030503150603090c130e070b03 66
    0x1d1008004031141c0326000b00e25441c080c03c1c41200075289141000b000c0380240e4081c003001401c044c011400920700112000600a40980d55440c40d01d507500c80c501600c071540d00b40002042c00384191081600c215090000040c042e980b6204002c040300c030080243c1c4428030118108084030307040040080c11030381076040001030042c4074200ac0c4c0386144010000e6800c56654010410096182c43e17070350310620400d440c10452100080011030700701400c83c4c00c4c0c5400c00c00d0b0350052002541103921041d8811014000c0e0f509010300b840002d1000399003512420009124081c4030401001c09101413604000000c007060081d400680e2020f4441078111409000e2044034200d504203600c1e00d5085407600c40700c0c002c080040803161414043c403034201c2c00801c3c100d5200140708125815103442181c610345011180c043c245030040d54111065403009001030024060380015a689445042c040c41c00b40c1c503840d006c1c14030341c1148414090404445000e003200c040c100302c1c50f443c0c6004081406000d9903909281a941e0b03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 973203938 1250 973202688 973202707
    0x15031a0303070c0612231b040602031e160c1e05010e040c0207080d02030c06150d02190e010e0105011b030e0d02360106020c0906041d120c0c06120606 66
    0x4000c0701601e082450150350b40c505c1d00c00d071501b0072144200d0300807443e0035440348284029103e500880c041d82e009170707004211145030b000c129110b0000400e00c40b031100b40f520700390020051100924000c00c1350700340d50888040c0401c240032440442140550203101040a15050009095489107a03505000300d41c0c4690340d0035070510078843d58018080c1c01003111164030050038000e550b0390100350055080d0141e100450750080382c15040c1b21000800400e4205200115000c101010400e0360b91640c03d1022040c000905044c0d09030704500134100b16081c0c0703140e98034000000d0318115452032510015000e0348003600009030080c80100ea0f00c0800d0352000c4d003d940b20320100f5503068401da9000b0794480a260701d41a00c0102c0440c5100442c044000c11905998030300b41030743d40711404412241d118280000290b00c42c2006e50000300340c40e58100810309541112140142880390711358600c40310300c02c0043c0c1041c02c20010084103120410503a50b16282c4408082e440b40b2840c1701401c400d203d4800080e01012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 973205188 1250 973203938 973203941
    0x806030a0b0103051b0409080403080319051306050705210709090906050612030a083106050f06061809180d09030506160516030915031a0303070c0612 66
    0x340d103900c124080c1c03080d6140d08145503281c5602850203c1c140d803901000000b400e02c0d00a80c25002e070301401e00c03410142141d980d030000380c10040c0700101c01d80b40342c15000c15030304260155a000d0880410341c81d40c048060b092a0082d508000e0801d001d00004100c40d992094002858031034140340404443c0c0c646d11a00c408507a100c400360700c020798941c1010303460000d02000c0ea000b24000c0004984000185100c00c0001c0e4a0f0700403010702c080070800003000503c0d85000f050340300c0b90481c500c100460040310b0810300d03526008028130081d00c64650b51070030444003203440050941c002e441207038528201000c0b12034143c807a05651342881d02840903d8041603010300748030108200003050307405542c02030303080640c020146441340c0b2040d283d5111300e90101e42001c1d950542c14044030842d65542e07242220802d2003450400c1c01c05000c4041007910f010014102442e5030440543c552165000704042c1d802c00214a4442a981c500c0d510940040020b680029008000f0100700c51560620400001c0c14810050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 973206438 1250 973205188 973205203
    0x2040b0f06180307060905060a1101090c0315050919080c070509041203060603021204060903140406210e061b070f0308010e0711070b07060621020a0602010e0a03080603 74
    0x103401c09404661039281e14040418403050240a0f01103074405035503034a040360350f14224414990002420010f401110b4407908400030924007120010484000359996141c00b0815507000351046034060700d00c0410042c80e4080c59410000807002410440714400450100e020340d07481c0100040704c0010132902c10741c01030040c1001090300038841111460300b4180b02c1003a4100d81e1030000000e180403004214180244207a80d03d00040184100c2c2550f41c5a403500010b01088030700390f0a01c8903403030642d02e400c00b044000340050503d40d40c642081d900c2e2040850a845c41c01a11a4449401d0511039044001c0006601d44e121715104d074000216242d07500e140c1c00d40d1245040150640203042200018590888000360407118503100801e1075a559580072511041c14036a18012a0010b031010440141080007800b0824024600003030050b959001e0030a000f0a8003180c3d01c4a540d84907404015480d1140071fa60042c0b045000900c60300211004150303c441c4030101c010140010b80d80426003a40702049100b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 973207688 1250 973206438 973206469
    0x11010f1b1b0f0e0a180611090d060e070b0702131509020c07050a0e040b1611070305011a0d080306060d0f23010b07020d080711151c060b0702040b 64
    0x2000e903a500c86080c502c0051281c06404442604031020901d001da0078803030001d500c419400d0381a080a2190740715000344c48107494903144d040d010b01c5550002d40d81c4110860003c2c0c402d80e40007824402a2a8071030804203154055031b5500400c0c08840056244c03040041700034102c0410008645c00f4594421899000c540c210160042c4082006142c4a200042030400d0703071401c0300c03400c42d1680c0c4c488944540382c40498004101084502c080740114120313401003100005181010303d00c00c809584050318010903a8010394060b0345074146141c0000611191102c2a40260707018035488000d9211014203102c090103d40c002c440006103c2d4100c2000e03441000841c24200342030081c00000320a00380207900e44906010421000c000000320f4400703204c103d80c40c003030340940131400324195501c07a80347d40d4001900a84090165201e484101d50b50b05001806c2c034a000e41e01c0d42d4030b400d982c10300c48000041ca100034400840c0b40181c14404244e0724016103034a00c2d4111004584400040041040f044109079103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 973208938 1250 973207688 973207733
    0x4051e0a0c18150206180307060507021e010912050a020615150f0d060b0c0d030b040609060b0d0c0509090c160c06110c0f0d080d1e0911010f1b 63
    0x2c16090541d0f9412041a501542299155200c0049450f040b1203121501a95540104543c40020309107401482d44500d45d8016070711080c0741050f85a442111a510a41040e50340d12500c80070088105c054240306050703842c050341041102c00000c3d50b02c0704003070310204d800904441310a0440d640c1200350030205041565060f00e03021301c00c841d01010703008502000c8001d4140140811100ea0050642d02d40600c0d0000030102444c0302c8d079042c8c1c010258a0001d58200b5200c540100313508102c1c3c0110030041c4440031402c0d64a180c41034804040b07800070001501000820480070481e543c1e00c0c10080d402813924841c840c2c0d260500d083c4007100142c0e40f5001030109840700c8001402c1c9402c00417038201501c9038002c0c0e41071141c084081000700000320104d140d100b0413030f0004801003a41000641075007442c040740010300c0c580b501000c03081d1500e041ca0035170803070b510742d8260810020403c100c80d0800f8401c0c00c02101200d20121301800740e00c400120103601100c034100301d00c103000d4404800601148001e19 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 973210188 1250 973208938 973208987
    0x6092711040212070e090c041511030a05041503060521100c0e12070b16170706020403171e13210c0b03010803072310050604051e0a0c 59
    0xf1402c50f10703401121003102080000952610301d00b882c4906a11400d2280b14161620341030107545101200351401c55001c000c0d0901c80c2d035904240405c01031900340b88a4a40503125442e1840c03120111800012030000c05090004c100519150004100306d050200e01d80d1641400b40a89102e01d0302c1c11800003c0d4045040a080e0106c05400881124401d201135581022440e6804400c0381d546820f03110b00c149000c0c04203c25004545131004004c0042d11861101c03421000c106800d481c0c94115020a6403815800202002080a50160016041c8605060701d0074001c040f03680e07112400301007980c2c0e4181000091100c6001906000d854060b2440402e00d520322141010042900161120105c580c44203481010400c4014501030340d04030340804004525265882c1d407450780380f4a41340c264007180720f40030081c031840c8174082c42160055190040001110300d440410082a60005803007100f603d40ca61000d80300000e00788040030752080030b8000c00705a81200840071101c091452200c0b400a154005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 973211438 1250 973210188 973210207
    0xd0c02010e041e06030303051803090405070e09040b071803021806040b04020c0102220f060e06040f080f07060e0a300818011b0f0507080102030c0c01060927110402 72
    0xd04c140305070381c0243d400f0005d990b9a680e03c0c03804251000407160340f5074030900035034040b850181c10065100e1038920382028210143e01c0403900c811015902111348000c82c0b401c0140700b507802003c0303261103c4410303035a0786030501d15004207901c0201d0708aa40c9151074030000041c803540300d44e00b00707481c43d20340500704640e00c10420408074000e410034600142c0c1c00650320006410040320003280c5003503600c20307621804d8861808006648000a03511110703000700d418003000032031071001c0e040d040007029075101811007441c182d03e88a0415049400a80034410327001800700c01e80e00e400303c01c0c10a5801d14100095605060140e414882842c101500702c0011007148420030401c4030800351540000000c1c10300071007c0c513003005484001510002200c18494a042440842c040703100c3c41141c24041d001382c1d1035458803030080a007a0f03401201c1c803203584000082c000c1800721007403195138005c03c000d140030441e0400c0040e101000880720500c20340c1d124440300402c01400a41c107030402d21003000a00440d40d540706903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 973212688 1250 973211438 973211441
    0x90703140327090f040f0221061b04061803080406022103060d0209041415161b0206130905070c0b09061905090a050a051005090d0c02010e041e 63
    0xb6000b05044070304500c07038010740c00c41d501542e25190030010440c03801e03a500c00040c03110140000340140ca114008644180242c0c41c0c10304c40c40482502c3c0011741040005001c0007601d4200003074501d07034011a0744041d070541070b0007070001d84007a0307419440c2081620b50040702c01039070111150009443e1020000700043c0c0d903500080e88030744402d0f4900145001402c000c940c10f8860004a640c550480c2c24401c05400619007400855406842504800c042e01a42c01c91f161410140c2038035421340a054209021004102c12011243d62407203244c0511800032078110000c1c10f8002c0e00b002802200045000d40040402e05c0c1ca0001504002c2020481c2c4e240c400001408645081420344006000f100840c1c1551004a0914844d094003c407a005090710803400d1801000000c144401b075005d02c501c0c140001e442071201e00e104a0162005140c0c95010071261300072a40043d0080085601000d0650016074110f8205482d0b2602401e08042031018440802c010308004100003c9110b200354100c1c0108580307 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 973213938 1250 973212688 973212697
    0x90307050f010605240307210f091110170a1b08011410050a1d04021204060c080603102409140603010501140d020a05181e1e0907031403 60
    0x3144d2805800405e8041a01001166100b112020000700001110103000b0300400c1020b505202412107039800d0002054201d6103034405401c50f8030b45070314104090040000d0303c1100c0c807000711059111070300300302c4001c0d010298151000d114010301a000540c001101e07272006445070022070527000000481e481c000e01c41d0354240584a800e1220045030079140c100a141c042035080300e6100d90346002100202560503040015030b030a000c03001d50000d1443d64885001410b91906010724460040c1001c1c604031007074903c48410384080240c42410030529650010300c059002000c87c0c400035082100c1d00d0140c10981402d40088035000c600710001504110b00c0d03100a11030140511030301560b07117480080500383c0300d0a100760001d840c0d8105a804191400721024076030144000d1840e244196182d000c40c0d555003001548500b035030700c002c04001e0707142098116265010580e04900380300e407a003031174004610441d80d2941181d01620300d000940c0080100581c4001d103401c21003400c2518040c80001da5030780e01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 973215188 1250 973213938 973213949
    0x4061404121103180f150c0a02040e0a031403090f070b0307020d0e06030106030e101805060a06030503030a0b1810061704080a030519020403081305100e0108090307050f0106 76
    0x10484403000140c00c0200c1130322030515264100b01c00384042002005031620b165104564000509840e22002c40003a00081080c0b1f01c14001500c46812540100000c8980c90800344102d60000e0481e100025401022040c3c1c40e030510b000702c3c0e1640c41e4451480c0c0f41041d00700185203184281103001c070700079640c1c8014500c01d003407076800c890504010010803034004803802c3c12160415006e00041c0021400b9400c002c4500c16401c0840c0d401d100c0b650760b42c00580b29800f8010003410403c212000a201040c03180552142c03190500740061451507540c55981d200041c04030141a503180032090a80c3c2c2c444c0c41c0e100080103100800503180c14141003000a0004522910000c20383c050701c050910040c01c0209480365401100750703414a800741e001600a000001e001c01400c80f030640350740140900d980302030400b450003074401548506003410142490740d4240c2019100d2110302140800d200d0b030010070605100030a18000d01c59032a140d0813071b841c600401d0700040c181d004818191403540415172248003105c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 973216438 1250 973215188 973215197
    0x15070f12080f07030b0a0317070611041a0403050c0906060c0307060c0e01030c021c02010e030412030306140d060b150706200301052d0a080a031d10080406140412 71
    0x1110018113404642003c01860307004130107040b04201140c00a10020180506100039a203416026940c2c102212b140a0b01040d00740340118050008500840350201c400c54500291891b141c1503480d0340350381d60405005548150084e0740099142d441c0c0c8402c0d1211102c01c5022642c071000c1601c6c104014040c00c1c1a00740020304100d031030909640c8240070b0440301d03400c10380241a850780821058007010b40081d0000080d503495600e104131180c01040288010100790202030841105071800505440307245c1d004003100304400010021681c0c0d60002c491085511030720004041c0c0082c000700d010380f0786a02407841c410f800401d081c802c0c080c05420010341d40c00321348680d0110a040e07242145041c002030190580015070707070080781d405507100f48200301350b110011107086900115a00042d80c080180c1c01500183d04524400010182c11403840d840000b00301000840701100799001c40c40300c10607061140100300b030010200b010300000e41c0c00b060182c20700b90800c0351a4902400c1051500b51756955607000607 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 973217688 1250 973216438 973216441
    0x31f050c1c05192c0114160305100b03061003140112021207032a030836030c04020703030f060803041a030601020c0d03201e0c15070f12080f 62
    0x154840c82010b0044200d503200601e50a1820110794110304c2001c4512030a668450000d41c000d140601c1c160700c02c4012003c0d04030780c10f406e9100101074400260601c000f6850f420024031550402c40148c0c2d40c418002ea460401c8951840743c04c03005000d0211030002010404d00011590740c03028103c01c14064003d6840c1d610401c1c070303039258030340e9080355100142c05810001c60f034a00c02c19100c540600c07003200d110303070b0105c40c541ca980f20480690311607050343d540300d900644828000d2201d00031203280201903a245100c21014200829110700c50f0090080c4226400202c080415000e54080e41b8100301d503120401c105a1500c00c0656298807a010342e001300000c16000750300349000300d03040324400c007810f0340500005841801441603c1050300b10444c1401900b540030040b20900c51404102110340344024001e104800c2000594002081030310751054001010801503078555840310701c0c08100e074903030340f9548884034188180c2c080004900180000440b01d820389400e036001907100d00803c0140c01c0d080e4039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 973218938 1250 973217688 973217731
    0x1b0e061b01150b07110105070f1502090a0504090f0201030f020d1112090703031407020d1b060e01020d17090a1a060a050a03050a06050c0c030c0106080705031f050c1c05 74
    0x210b0241d0031008200505e503080382c034001d51042c00900000c82c41403481c40000e55039983c8010600c040c0341480b0044680c00f080a40d902d280c80300d030180003481c00341c2c0d0800c025074003520b499003e0000194060b05140e210307c0b180c540100303d07074103d55030400301c0e9030100031030143c190604480da400300c4000303000b4450b200c3c080354040c0d8010600c001180da041d1950f04605490808401064001e018241c0c0c0c1700b05000d4040010441000095048103003840034810f00301c0c1005405040c01c50078003c0641154009903040242540281c8040b000c182480ba80c0e0341700796100082c1500e001022203000704042c02c0f41808454140100c0a128003030102200c1d2014a16141c00038440340460f984805080f50344000445408100d840d40410380101e01001810b18081c55031030380c80e15550010700c446031113030740d0741e0740030020020300f44840320150000b1000381c1003440c00c0005c01c002119806c0004e0110540ea0790104442d0f10440044a080f8645800c0a43c0d540c020f1125540050504031042418030a510a45008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 973220188 1250 973218938 973218959
    0x8040e01060e030a0f02041b0816090501020c0f040603020d03051305030a0f0f051203150301050609130314190801090b0d17130b04090501060f031b0e061b0115 70
    0x241020140050421035020744801145d1010804142d130007540d10100041d40684141c110303001c820240d118000282003a03000c001c42291504841c000700b00141c03905010300d80e03001c60b0103008a001150b4034038100c1110760011703000340042d510081d4400000c910f01020160000041d050301316a980740044059505c00034503446500a1900816070448030410f40001031103062001111401041240e10b50300200c003442c01940e00c1600c3d141d20b07642001016445034907090003200e074080c00c00d48141c0180e041005030b128842a1461004051001818074042c80042100c1501c20740d0b180600642017038000314001800b052001c2c003450f40d5040c289582032100d0b091a4000b004003642c010040072031024035003482c4031250003031000c46490011449002076200c1a042c00380020303013044600020341d540350003c054004440c4070401d030240350a14102c0d015000c01005220064602c500b8696420411440000c419104603000103c9008295503c1074450300d0540c460001143c490400000d120b071070303c40001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 973221438 1250 973220188 973220207
    0x40b030a0b03070807030b0711100507120c0302040b0702040209010c0501090b010e0711151f0e0a0b0a08030324030604030c020f06131203031b050703030f020c340308040e0106 77
    0x400070030701940448c00031803140340342400003045413042d078040e01541a8068191202914054000346031440d840d511280c0358441d5900e41600e504045141c41d240c41070902c814060790300041c8c80b403940801c040650b82d00415807081c0036039020303000708400b00d143d107070181800300e00f8050926074480ba80001410b0030b000d0502d00611034500b1004045140b0607841a044c03100b0010420440540742c01400c2e01c544810b017002c407000c0d00520b01c581602d8070700240014122540380782c1030f9110344e4ac8904100700c036440101c2100c2e0003e2040120f090341c00c0440c4408405210003500b110340510851003000700789076000117820b0182c5c1c42201c05031441290441000348034011000084101b8169100400ca041404208c1c0200d85119003000320308142021030a0b102249180107240100740300203422410158144582d520b4150f02c00421030808800f030030310a07030310243c2e064040e0800075a040c1c0300a0b0941c2d4680000421000075400c54111501c0f41b0b0044c205410602c503405821032460300203c0c001d8080c90186 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 973222688 1250 973221438 973221443
    0x306012d0311040b1c030c05061312080c1c0903020c030319110c031212010f03030e0d0323070b060306060f091306050a050412020705010807030f02040b030a0b0307080703 75
    0xb9509081140c08210040000304e5074583d00c405140c1e200a02c40451400e1910681c0c080d459200c904082d0b070518504040000f0982880840521005400180c00c0d23020f05203200414540121035564580c070100d510b01c103091034948041c005602180d03a44050350460740500c1d210394282d0304549160003e040c1d40340201d05420a007011101d0003060b01c3d6110302210f41031041c200d01111803481089000c40d0904030700689100300d031000011500280c1021300c00c210300400c1c05d00744031800140345440081207141c022502e54031070111594079074141407240d5080041c00c081100001c0e401c5208034207140d0242d00454045542100b483c0005010703140c040341b5a803007042d0250081d03000101c40f404201c02048001e084050720641d18214101146061280e144074a41d40140010181498148140010703c0d42c0581c01c119400031600303000a907400852250410031900b0045170049010f00008081e00440d000520b40040110410900752807a81200207a01c00a0742a03500542d1944403d688070070850102 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 973223938 1250 973222688 973222703
    0x30f1305122109030709022808060d0314090a060201060602100e031b19030815030a0c210206030a02130f06141602030a050c03070902090102120f090306012d03 70
    0x32442c9020040028105800700a0684116030f8840c920801207802c004601c100703100d4582840101515405804050005281411802848c1030780003d612a510040010304010160062410030b901500580c3d954a000521007031810f521032400a00a105910402005110303140c21400541c107248a006914510080a107251003c072502c88a40c129051000c0b0516201e0001d102da80b1034580d6464140b0b0398441e03601c2c3c0c40e01d42402200d1900361404400d406200b41c0009804000040e40056128110745e4520740700c10401c000411080c0d8880d00a10300a508020000100142c240d01c580c014040e8021200c40740012940b110f584000c0d005d001e001d0100410140c800520070529a507010782807002050440e001034020540c0860f003440c603081c4e01100c0c65030111034402514a018051140540741050003181000d041d10300007035586450b200024990080010300c0303c14852110704075480214003504544403540d440e10f420b50f80c0d25501342140c100e1342484200001c051012690078044a400c03000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 973225188 1250 973223938 973223983
    0x91101090302010504210803010305011e0b0f09100510080906010f05060703081b0a03052707180e0d081006090e0a051e1303030f09170309030f130512 66
    0x1011500548044981c4079400c0300c1c2210360700050900d400440c040c1d4847c0001149106080030378030940140300303050514143c04d066035201c0945400c0041104180203c855a68a803503848100c034030b030600d82d00242c1d00414900d241c2406103030400d0089000d21120803c5458581e42c0b1070416440a80c5409203e40c000c1003085041c000c030384690041c64000c02e2401d0354105800f40140542001e40c0b0807107400e80440c0d00c60040240c00949103401401c034203075032543c511003001016115a102c030601c3c040c13000705030a4002d4407602e0900651081c02c88021000032240f0803a004100540b0700002292902400805d0346808a40c040c4100035003411209880008022074444250100281c10010103d020180502803500c6000c01c0143c1854040c18040d10050342c2d40100e41401015140030401e8074082030306003007400b0005a00300040822428907400d407c1d441c1c0e22500b03811425171207003100140290101003103c2240b481c40003418002c50700100c1d58810504005ca10507031f1101c66403020035050410014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 973226438 1250 973225188 973225199
    0x507120306080d03061a0c073c05191809110a1d0705040602060a09060b09011512021908060102030c070b030604050a1a011b020d150e0604050a0813030f030201091101090302010504 79
    0xb070101400c0310300048107501412109d55000520070b000c000b0300c41010b25281004982015a61488000c03140000281907500307280140e04882e070042038443c18181d45040380018002c128100b0780440c4401090002c8099a030700c58044905014141c3d1418007880c03102242201d4005c80071902201c1554015090300d60f500010340c4000c0001e054107483d4541c5904048003696220340b16240a40000c50280c01c03c0903110f48010004445c0310740f5070013414410091030b194a4002d0921242300101e605e801105a0b5640340104d056002d03800c7c1c001840d03c101c0c42c02040f18070300c280185200f00c038191002c100f1561540c00300400ea40c1420764003040c042149081d4041c6500c034007040c1d484640206804041e451003640403400340b4401040130359844010080300714210b0800d009480c109402c000040c041424184c030307503e4407880d0b40c440040c80780b48006900500249030309000c000a58100340702d4031340141c0a0602034040c0c2252081101c0b0000000301d4030b40e030f84d0300440701c920a903038040c0d540b54249814617 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 973227688 1250 973226438 973226459
    0x11412150f131b0e01080111030a02090118030f020f010305130f020103020408030f27010824150a0e03070b0a05131505070b0a05070507120306080d03061a0c07 70
    0x2502d690210110105000301203032140100d149042c070500c500c03403c803615042c1e44103000a0107803c50384a07a418626015000c10100302681c1d0400d130601c00040e51456580010784949038200e1002d034801c05211000418000701a11881829000303030780345201c10701e02d00300442c00c03124212404ea4400d80032103800400708900d90f2401c201c07684181001841d161311030785040d103150007030402c47d012203000090594041140c0304400c003d000960110030b040040d0200043d011520013000009208104030308043d4880344100d00441c2980040d0901c00c03a02e2a50400041c030f5800000040081441c0a54150060070005140b0049443e09039541342000035400c0101c5440e0300c5100f164900310040240414600340c1d0000f650790070081c90711130550342c0c181d5207000360f0f480d8801024040c500d0f290408000300d464002013101e85841e84422101442041520194024001d6810442c00c920500d000d44194170b0700340c0e03c2034080e80c05003100107030070115031003102e90130f40b0986103020080c0e004104204040183c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 973228938 1250 973227688 973227691
    0x40b01060e0f04020301080a0512190f050f360306070e03010b3102040602060601050a03090501090308060a0e0c07020d0c1716050904021f050909011412150f 69
    0x4021440c8006078500040a1703030800e0b00300f00c415401c1024198200b040402494006004481509051072034000e441c0d050051202918404d1001c000301c8102d25510400440e0102d074005c110054890303202c01d51070510400c6692901500c140c6140d0600e0ba01d6840e140c41d182d00038401001850182d90b119411103444100c1828550107640300e1101c1710207075540d480c84140c0c40e1252804040d1030302c003107078003681084803507104000d00c3d038810002801215030101c2c90941c40354082c00c08a070b80f11100c0204070001e0401d48001307840f0303500e4443c200d0b041660160aa030302441c01224003420154a48030400c481e1442a0f550540d907410402000005090004844c1071081c0a204211185981c801c00044040040700014007240c0020f01d03143c00324101698004050b040c281c818099518055021810203490120303a4003c00a490091000ca240309030304a80c007010018100e0005075032744400506000b081ca00d01c02d03100e900010124a0008000980808601110741020451362250740d904c401d140350 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 973230188 1250 973228938 973228967
    0x3030b01080a0e10111b0a0201080c030f3705011503060b0417010e030414011b1a0406020906210f131407030f0f05160609090e070f0602060703050609040b0106 70
    0x1041c401b40c0000d0641100c04208224508060648902c55100040220200519010f01e5240520912615940180015a001030580d0344148485413441d0030044c0f01c0c01c00c02e41c0007448a13840d0014004c1904907003125040342d4103104402c10000522005406444031401010352805081c00300308141802e100300214800b401c04000a0450348030550a4115881500300e45205e1100101400107564800c07010030310b6000c080c80542304910b0381d54840700c891004480b040d00a41155020030140100c0307074112012201e004006075500c000d80c2d46850340880103800c240d6070612030030b000107002c01c08ac1c0004c03502c102a20000c4000c0c5030502e0350b441d00d10310140c2c13038155085e01c10400040b00082e40001c003c0083d45c05480884d40d0b440ea6488d10314603003c0c00080d0a002d84255803010040b0f01e0300520a02c01b070324424003010608120104146150508030fa002d814042c00d00c110000e030658001c6680d070300603080344c0c0d004c0c4042c1da01c01c0b003800202c0c40280d5000308208000d200402c442e41c890140c040d204d04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 973231438 1250 973230188 973230221
    0x10b09061305191403010c08060910091a0a080318010c030c06053301020d05160b07030507021908040e0a020706240611060105010c0f080703030b01080a0e10 69
    0x2e80b550b001c14540c0d9848442d00105020258081c0110103400980d40c81130700e0103e0082c002c2c0008500b00420040000d001e682c054034500c40420a09280d07c0d9100b4090088040f040114096150303540b4050701c1d401c81020b00440c800200801c1e5500c01000b262403d404003040075843d06280c1004541d8089104800e804020309076805000080755070090500030742c80000c6a020380000003d0000b02e82c00c0d041c40c4906417140c20f0165050990b00403907041007030750440c00c0880d101c11100d0b0300040b9038100c200c002400e44501108101b84281c0551015000b0f1b400e50b401c4801c0125055100121540700d000040e25100d03050000f00151018400780c0340c3c0c0480381d010007500f4440c4507951442036410040c4410700003145144000384104512880354010b140501e00407188680c404030081d1114818010750741003020200d0301c4030a00c2001c62401c1c00c2c465020740c3c51951000541001002000c5008031140013450b20380105d8000300090041c5100301e01b0240142498040702c1703031208020101c6131515803100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 973232688 1250 973231438 973231477
    0x100b09090c150418050402010f020607020703080c0a0209040501020a030c14220e07021b0a060c06020f0403122309030615010e04060f0801060b070503070f05100504050109020a0b03010b0906 83
    0x50288103044d5a945094400300340c80c2041c0c400905152030611003002154001000c12107811380c0040c00f1400c913a0000034070703981c5445d810b95550804030300755800382d04502e0040a000c00c11605600602e040c040b07aa0301001003030f402110803115811600c1e500d20000c0014451100c2125482aa003041503601c3c4c1240d0440c0c40c2e8460a12402c1001140c0304409a082091180342175580501c480040c94001c032440c1402605005005c3c0a1068160b00504010350209011070400c842c0c60888025503001340f81840740c0e62450341c001303081000c41200d41c407039140442e0003074400b425014181c0311403041c0100038110700c1e40c400002c2c0c0b00710140003070558104603980200e0740c0c035a00c0380c0c071136200a0071141d00c03203090a03802c1c000b1150a4804136402221042d80070008034012420100585100e1680003c108242c0d03d03440c2401d5240c56400c424160711513280c4014841008015407100601900c25603900c000e0031340ea000c1504c9030340030074410240c40403804c0104141c00c2c0f0b071500047c60005000c25615000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 973233938 1250 973232688 973232699
    0x4060512060a0e150126071503020d0b0612180c01200106050a0b04030605010b040305030a0c030225050906222007030906110c100c030c02040905100b09090c1504 71
    0x3600c80aa10006c1c0c0c16461400003400030080e09104c50441e14503a000308026490640310700510201080e6003010954049042490760110ba005050840d900400e610703180c2c100001040207000d801d4617041d030716010755090f4040e042e80100b003052405005131100e14150341030148031901d5046528802006550b40c2030080358541e6070f026000003410f2424030a41d1540d045240c418221401a0000710f00081c0a100800000d94004111408540a890162040706c00c901d030a914014442c1005911050405109540c0301141480d542c11194115660b003526101d43c1c0511070011074210745510032422902041070000036a030000b200c0c03881d271400714103140143e8003030300c40554100320001c42c0042d012a1080001660104001060501603c0545502120100010400034021802c002804900040042494050400d061b07238182c0140c4140040714440c238000c1e484030300c50000c80342982c0c605110002c0c01d04060440b40d00c0380744520000c0104000301d00401030920f800d9a01c1229034281041701181 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 973235188 1250 973233938 973233973
    0xe0f0123101115060a05220921030c0905060a0903052a09160311071406071202090604031104020c0708070602070b070317060f180604060512060a0e 65
    0x5085140342d0b184000401c0070b0000c181402c5801402c1d01c0d40302180020300c0f201d5520110b00f0400c0b1042103034114251100b240020303605030f02c170045410b1001d280440d01c005000d159004402050808010802c0c0c2280d529002e4040351194001040001c9c0691400d000c182040340c002c1440c0f170f1a50806040050740c1c4d5a1309450700202c2c0307400130114011020300990950b00580552846a01115441414600080407130114403c01e480e8204268a800e08a00d030320000d035017180c149a4002e416a1040458484902c1c2ea40c20295100800505138212100f0706802510a40740505001000980f42c680303503458101600c00d40382109541700303908001c8006480001c1000100a080081c0549841842d080340a41030000d164441800c83d14104401070000361302100c200503030581c5000d204070b15220940450064001a403065030842030200c00da0303003010f2129500714812201214240405502d03042444681280b40d4548001303517003d0404258041103a412244030414044100d4026262202d4082c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 973236438 1250 973235188 973235209
    0x41a03010908090a0902030f0408031012210905030a020904020a170d0e04091a0907090f02040f1406030103081605070b0301320120070b130e0f0123 65
    0x20340b04800001c00c0d51a030705001e6081d00080001010450a5280c640d07400d8140701001440107010140010020b070b00e4060071400d001c0a8125010780103400340161510403211071300d0444542c107400c101d200244c1c50724072410115042d550040e000e0541c01c0407650a2000712000904101d034044000d680c0403d1031186501080500c20a401c02085e1070b0f03d6040000d0190700740701c0381460040341041e50440200c3e20081e8240043d011101e41040c0cac603524080458282807180d0030920703c4034207101070210000da02d6005001500c0d00195002c010540d03800f46240880da108a150b50091800e00c01000030440c058041d0280305000c0241c464008416603846040194580104c40483d101100511030b0204503804040c1e1410405444000c0c01c100c1c2c03041500a482c00030096040002c0d00d030300c910000d80d201685000c02c005050441c0c00c0d0503103400d080d444030303045105032800c8000108400500e001301040407a0003500c007120900c400e40d09244c005106203044600340b0000315003000104201d0707101c601060 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 973237688 1250 973236438 973236443
    0x71e0812070309060e06160f020907110c060309073606180504321504140303012904180f0501150801050607020301180302031c02031302041a030109 65
    0x40e03660340740615014002d40f8554015408010309110041040c1d11041c00301c2c1e01000012001080d0441c151501d00c0b604a50701000a41010141c000d00802d00d411400515050b6400800d4a60603c4910f05001690008035130310302e829032004108100c50318242c5180c903495041d101d401c40c01d041100d01d9580c2c44488000c00d1004003591244104200d01d11442d1070907108c8006001800b00b801c0589510715010701d10505e0040c2b100c140301e041555030b0201140b40c5510415502594041c01c005110203040341e0003103400307540f1101340a0310104583c0c0040104c0341662840060400031590b62005500b03101c0c904401c9401c83c0104100125980703080e40d40c589100d4402000118400020310601c005981c0107030710940509020040400209802a4109042d60015113103d40c690f40c40740002805080c82e0b0260702c9485c0c4c076075503115051560120081c0034030101542c00c0f1100080c032001510483c40110781c0c844208032101c1d007001c0146099001088408200b5480c001d01d410400000b90031103ca040c1d04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 973238938 1250 973237688 973237723
    0x5120f0f03060f091801050a0606050a0e03071706510a0305010c11031c050a14010303050720010c0b0601030905010204140f030f06010315143105071e08 67
    0xc040305c04424050f8591010241ea001d0101520b401c03000b8010f8004c0d100b500d01400035050502e4a2130f01c04200d18030040c03003554008004002c14849a54503040c05880c5d1005002e411050032880089400e640001303100302d843c1c0f1441213600e500308403081030002c0c2d0a13008000000c1ca00190503550b000a00c0c40a540103100019041c541d442010303140f4603d0750822062a0400c1c0211044030f40c0703050b180b0381c00320388040012525564840302c80006100209001d80c1040d0010004800d069110001d071603040d214819803900b03164000d03a80d03617424104d1241207001801a02c88400050740b100c000e250401010f0402048015491362150b003640c120760801e030813401a502e403402241c60000c0300d0900d4a6401d4024195003241014829101c1105000240007400b00900310050f03d80706d40e01c2000800c000941ca90381505100c2002e64410011800c0c0d030311140102d4189a03100c800000350960082d40c043c000f460007620308002a07035858142d0000001901049100044011040c0b201e9114201441d11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 973240188 1250 973238938 973238971
    0x71416060c05090f1818010b03120307180f05060c0a020d0b1e01231906030b120309031b01111204060206010602060702060a0906060902070c0305120f0f03060f09 71
    0x280301e44c0c9140c12440510581c46240192030750410289a542c001802141c0f021a981407021040c0c00b40800c24041605271082c0c24032880c1d0003062001650180807e6a6402c51032454015a8000f22415000e0030b603040740405410055071400400404240040e8410340790140b1203600019100e41c00b198060318154041c0c8204014242c00c446001c054150b20f264100c201c1d41004600d000e41074600c441d503c4115207095500c203041d520240340d01c19400c10300d0700413000c007038031100018043c054030340061340030f04402d05a0f1800340394003005559040c103000c0d0081441a800030b10307054121140c0c40d075450501c40e41c01c20401180900b8041c10307002c6d14020b640c4607070b51f501c2c04000910345001603200c030303086421540c14400c1c41540410040d402c21040d800215400c06ea034242440200b00547c0f120181600c00124507040003600c912103400c59001d14207031009056001c4941c21584201020a10403540401241c503003120150080c40c0c0022015001000300c1c1400d401007025040700796941a0344000004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 973241438 1250 973240188 973240207
    0x1a0d1d2e0e0703032006061905091f05040b2206150905090a060509040b0408190210060b09010e151e0304050f0c0a06230a0f020c09071416060c05 64
    0xa040200040c50750b5525980ca01e25105d0a81c0c07500000740c02d1a1080b042e00420000c82c5c0a4003c0030405010300500d8071075513041c1800382d4402030810386070f2000a04000c030303000129407600d842030401c0300d03001810314580014030a040c00c034200d5800406880e0a9a00e24000c503058144400d0010700c05029118040752a04110030440c01c090020103e410382420182c0601041e243d0300c499a82059008078143c1d0301d03840d107150242d11800345a00ca12800340d891046a01444c0d400207207215200c003d00010030049884544444480c03241401c031502045100c025602a070400b2011001425030b5042d00905101c00c00e13961118941c007503110500c1062000c0705210078054103002041d180640100200b01e003800d6000400c072032a0081c4101018407680840c81d03481c00310842084010003601c011200d95a0f924103002030007a6054011000c01803080c40d00c0c0304903a050042e43c05001c1c5940d5201c00c02c10001112020303000f544942244008200c1e14280a00001c5850207086c450682e1500c81d0780d22070090300e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 973242688 1250 973241438 973241447
    0x9020c1204050f0d030c0209070e0916141b010501090903141204020907120c051c02390307030801030605060d0f0201030b03071a0d1d2e0e070303 64
    0x902542034a00c20801c0100a183c0d20341541a20078042911043c5100d01c0506007503030920b00b0b408001c2d421041801c104101180d0001914105081c1221151515242e05040300b10000f011105940451500c1d10324081c000d240c580645a83c80702c02952411007200c4e141c450f800c0d00c0c02a40301412043d180d05404e0101500106094030001158840e14240014140e60708480b100c0908013078003601c4e170080403502c2d181c828442d50082102152040c440440c24910081c400c2d48400101511202100785101e20001e00e80201ca040b80c8580c4d0610314942e01589040021404149206540d40e5071514038141041050010781011400b039180e04c0c0c22589581401825510024a04ca110b21401c4101c2d000295004580490054084c80c0010300d03034083c036001c13174601105504042c0c9d118201840803098080c402004000075107280d0801c1c051007801240704607030352120b09140040c5400650311103013009448030200c7c40340c019000400d5a20325418500c2412a4662180500d10760403c20042c014107400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 973243938 1250 973242688 973242703
    0x10207060b03190c05010f1b0b18070302150a0203130603061a0301060c031437020a0b010317271f0909020906040b19020c011701090e0a060609020c 65
    0x70303140c194a43d8003140d8824881c003e10380152410b009405043c10030251040d01c030700b8098503144007038001116441c10050510541100c04604815926403823041e081e03000710b00d1504499025040c004e485545134200314258000c0f801d2901103100038060031000c1c080711400d00d80103180541b00099260300f04941c5d2486c0e00406c003180d851001c6c00304010402154030099a25460350540381120640f107441d05010789901c50340318400c1d0400303074021010169807a010442445440d040041034076498140320140d80300e04200602401c0d502c3d001c8010404503590f000c0c00d05080b00c80031001490500880710352040740c0728980500c1c0c9044007a260805050a1104540b00d58646010340404082c50101004200c603100380220900c841d000304041407152602c20a480103000b650400e55150104c0c100e2401a0031029009003005215545a00c40302d0750003004c11080402c1a605d10302d081d0381c00c00038484090b01051200ea036a034031a010043c00420140d01c20000a82a007200c003690303a110081406191009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 973245188 1250 973243938 973243963
    0x4030f11090411010f09030203011e1404031e05070204140f0f06100c05030c0706030b180108032502191d1303030b01050d0203150103060e06240c010207060b03 70
    0x101600740300100f85501e110192aa03000d291020700d44d501e000040340e40b051039500094040d803c00c005085000342082c440001e0907a0460200854090302c3d0416003014001d89001c0c02240c5000c080c9021064544e04807040720449041492618045134041011180c802000c41400000380050009091820f0380e900e8100d600000d0402c620b05042000072454a1407403419000d01954000b12803c003c0e0501c240c400320034540d81900c501c640d5502e000b801801c07002c0c800a04c115065107905400046080419040c2d561400040d41880ca1400b1846174401165944105440d41c0d610008010392716480c402508003141036441022501c4c2c540c10b401d120b003558800c50607408012081000d40e00412411803c8039800d890003143c018580340042e1540c1c42103250600410b8000402c000160201c00c0846500c80801e0340c0800c11035640700e0001c0b01100d001d0b640b85601440070f03038041c030124003050038100748810b02407040c91030448035603a00d50880c0d04c50001103c001d51210b8408a0300d1070103014400300c0d1070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 973246438 1250 973245188 973245199
    0x30305040e0901140f090709020408011b090308070b150402032809020609130e031602010f210b060409020c1006050a060f08100306060305030c012703110a0804030f11 73
    0x3460344c01c12541c440c10042c24200524005c00000e040c0c94010072500005003101c0d40c0842d40c2d582c40f008030a0107003416104944034400f1540301040828030586d1490f084a821904450502c04c09940da00c0e800341c405054910000202050035220b90346a200540c000c0e880500d1615422740e10580c4030440015190302084481d14280d8198050f8482d001160318144048500040c0c04854030702d03440003410000c200240703610012035440750840e8031240c11500300d8000d0306d940102c030300c04550845103240b0481011111350300300860110300400c5500400d60301d0400400903400c0c142ca4118003004c0303802400d21401940e0015030004184009072041602900003900e8082c009410484003030401840841001c08011103200001e0300c600c00f10700303108003031980984180005d03030342d034107006540c2c0e000b40a2100d450b510701803540504560b115006010400380d03500d603501c541700307640f019183c04c041944400d030789000c0e103440c0c0e000041d4020020400b85100e0a80700c450b010580c100300c80c034001c115141da8040e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 973247688 1250 973246438 973246451
    0xc0102040b041e0b030702030f071505010b04061106010510030b0f030d0e1507030f0c030e03030d020703020d03050420060723100b03100b0d020d0503031602010b0603040204150807030305040e0901 86
    0x1b00e5000c011a4840e0035405401ca903101400e00d018101110142400d00605140c84004983c141c20040104102d450b0b0340c0c1d544a41d0303a5603403203250f12083d0030321502c2c0e030009603c000c1c1154280241c2105e43d05040003001100c500f1882c0380032034200300c0d41d40e00c4000040e46c10058a040d902c1c100d40b190200c0519141c40606040c0b03281d40180944d0101c003040300a011008440100701882511440380000018054039102d6a241d181c2a010307420401084026014114411880c24860700c1042e11558112004081140b504141404c4500c2c68090880d08a0340420400020810011108030311048050308c550201017101c4205041400300080d00e00c8507800c203e40003035660b81c0020041a401c40300ca20001d070344640c001c0054490281140e0007900560b8256403030f03040c810302001552180d0081e81c0d6200b00564410800c908885041050315844401800840c1c050b0078994050135075603150100b4401c20a444204051500710f01e0f500440c0003d1000405106142800310030b00d0700880310600900c41b8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 973248938 1250 973247688 973247701
    0x20f0318150c030c0604061a01020c04020a091a1306090e01090f14040c03030807090b030a4d0322291522020c0102040b041e0b03 57
    0x4124440900e0310074000e500410300d070001448221030400c1d5003401165a2000a801c65076110070741141c041e01c42ca440c01c03000c204000d2004500844007941640a071809070303111010840250840a40c62040001c514408900f0b090000c0d00004407100420035961141105c0180b1107a181c0c00d0b03040041002281b010800c410003101813814151011114041010100b10f03c80300002c180441c1845050012081030100b030019080500090307034001e5071139044a80d00c04409642c8000140300701000240d08200296105041e0b60210840301d000c2c038400c0c1406200383d04990b94140403a0b455030382ca4aa242d0000d0882c5c80c044607245880c112000c540f0382145030207924000c1e00c6040590958100100080c5c01b8200705010482405c1420600f10024030910074443c02a000300c401c0300e442c10a14035103040c8210358641001c050201200030411007078492078005540c0c000c3d4122941600c8159024840421401401c8003c0c001070701444500000e10600919010030643c0164009041c4000c1002032020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 973250188 1250 973248938 973248967
    0xa0213200c100204061e020a06091a07020607020d08090c0904140705010309020604030803090a0219180b0607020d1e0312050739060603060912030c1e11060106020c01020f03 76
    0x1c00000080c0102c584001c441c5050b820401508c0303000701b1076032601088a08010f40c1744000d64005500c3c40581006603540503003a69100390507205117002d42d01c580c213900c008611680d50300c0c4c1d202c5810820340b003401c104a008620340d0700c02070f50201c0303107071002003800b90f0210001c000d1000200000d103070520000c0c40c3c9401180c0f0328803ca00000d4071100001000410302007040040d00702035903000d0115407142054401a4004003d58040e101c8180069130030aa28851940501ea07044c002c018003640c50b100d20703a0300b00301c0694008441207491140c217444040d40b403403120a044e25101d000b07440d42150700181e00c3e1414100e0300e008000e00144907201024100c60b04040075041c07c0142110f000c0350403a480d07260903800040d41100014121414244040100703d000c0c1c1104030312a100703265030102596005415819212480900390028400741d00c0c40c0b40c1085d40c2000c0207089065420101c1c2501803c0c8511030801c0c500743c00c90000741c0e001802020036941c2c10043e0b54a01d10800e030145046c011440401c1c0ca = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 973251438 1250 973250188 973250207
    0x902010906030207031806030f0c0c080d020304230c0406080d0909050c07020402040f050a05150306222309030414040b0319050619060302030a0213200c10020406 71
    0x1c1007607404105082058007890b1010220440c03104841c4c5c10365559000240500213010300009038a090000151a0b140500c05400240d0351141000c0e041ca6040a040c80007504002c10a40d0b0f400800c1e100c4198030f12250210f4400e122005005e0700800d02c0c04d1080c0b005442859014407515800030111041d550340c0050f03984141d47c4c025a011a89131961001a01c1c14001c559010b580a8400600098ac441c00c5002201c100c890a5038280d40303541d500c0d81000940c0303080c5030350442c111004000086003440c0c2540d816040006c6541002a8500f90202c0c3c80102d5894070403952408090711084800c0e001c4240c402ca5020f140c0c03070021440d15041000c040009640d8200c2e0502882d2a0200484159014007900e03c00c0707160100c041c10b6000980c101561b491806840d404000c2da880300a06402c808140165400e0381d40280041c811001143d0030301003408d21400402800035078548a59607070414214155a409281c0841c150701c036000b5a2085041188030160042e4040c81003000b00403180c5c010f080f21 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 973252688 1250 973251438 973251449
    0x50c0712050d030509070b040e010f05060c2e1802010905042c030c0d0f0e040603030804020906040b0310140a06030b010b0c10060909050f07350706020c011209020109 73
    0x8284c580f60194420b01e0260942c102d602001c001190204015091006a03030485120100c2e5481d20b6680f4002d20800303110b506c2880701c0540100310380e02803d1f19108201d41c80710620400c5041c000c3d5450b8545802c581005202004021242100300d084d50390006d4108003a0404a80401a21115102e013200e031441641002c1c45601300960040c1900e2024403e680e01000d4078800d0790032400c0398800c0180a901c0040d40c800c003080c580441c2407000d04281c4544001d40e94581c03210301458030755030204481228018000c6078060f4070780c41a8040760700c003801800c000003000d0501281d0040e084085045d074500040c4407080d0719240c14020070114907181c0d05541107c05e01d02160703a40740082c0c000c050a2a000078100c04a850501e0f10000b900c0c0d6996014103031190140c2c090320410104400d24a032070302c1c41c7d031090005411031016001c800100c00c0c00003002c4050740b0101102d183c050385802906180d0213a1002c0d016030010696800c55582100061041940c04801000284580d5001902214842c00f41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 973253938 1250 973252688 973252691
    0xb0711041104090e01060506030a0605090106020307020901090509030c070602010e1e120919031b0501081614070f05060a2a081305011a0102100e0a020402160b0403050c0712050d03 79
    0x104044c1d41002e505c290b018010240000c4d03520315100c094140542150312400340902e2280300001512407001c000d407007a0507801000b154980c0d18040d01038019240c00b40886100d400104440300241104002c15402095640c0004c40d0021a07100014140250098100708200840d01c001041c184003160010460300703400101900e5036019008501225490f5002d001d190314000400f1050040f550518410418241095404551610011100c0c0f0304259452070f040042a480410124040c00d8080c44000707101100c00c1c285603461726001c070115003034a0183c466801000910070145001d00a104481448041f82c0322495003030fa0240d4045059000150f0420201c000443d40c540d1054410045840d003010092143c212502401c0035502080c09205000d4417800400c8600040e1a0280351101081075025001c098180c1c1c09000181d800031028043c03030030300300345144005181c0880841c05540203640b020780350300c0d000e0205442e10b0403581000311240007401781040000e0001510aa040895150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 973255188 1250 973253938 973253951
    0x20c121011160b101202060d090809190f09091a1f0e0f102601021207090815010e15040f06080c0910081c180b071104110409 55
    0x80640b03005808424030101503401c510b1060140e580710090040c41d503030195001c03090759600c0344003062500c0780009421480c24801144035400c650311140500d03000310016854481040c0c0082c0c8540000803140c49441c90703039001070001d20070002c650400b0317282d000005c0000d0105626071804418501800003120081000001c0540292401044d404021600c0301200180c0b11120001c1801c803c444021a03800780c85c0000e4003482407140d0481c21a0983c100c0740d0412291400400c4426954100a010740c1d902004400c00e901c988003481da2080c5c61a40d20040040c1c1001c401ea42443e01c40d9451500107040c800061281400c40301e10541c100c1a1414030b80100301c02e0b50003007005000fa000034441c200d0300d01600011800000714201c2800001259007402603914094a06000c110600462040e588101d50382011902c80900020f008015824200060b5a0890b629175070540030342c115000140c0042000303020045000d803001040c002c21207040c0503140c11541c0410040c080c500c00e2100040e00c85c034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 973256438 1250 973255188 973255211
    0x2160806100b0a090506070c05130902060a110f1b01080901110d0504031b0503041701050103050606011115011503050108010c08153006180c19050603100303020c1210 73
    0x1c08014a40039040f1520303a80c081c02c00c1d00141c4210320038a4080c2441d00001d269200441c403c452f4160350042045040c28462142201c0440744c90f400c0713146620950400e07061901c4100301c8040e40004045200d502521034200041c1802e8001c4d00c203060720380c100200701c4603800c01c3e01c003550101681d03054000340554850800b102c4a02030045580c1290720084105001e021001c0004c2c800d030b44007562001d42e1a0428080d02d42207910901c00645203030099404103034150b11400007a0078104c00301d02194141100c1035014451700000b030780b010b0781002e007004a40015503018054680100400c074001c00900d541d41030042c006000062480001c030282405111243d990a80103181300002e50b00d0b80c0c03540245503402d004039003552007041c00705031042c20001450400359000d89004052694003610812819200340909148600c070450748036002140301107401d031962000703144550324041490000b03034518180a0305160a055880740502c0d17181d88058415400010301580c41491068001030714408031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 973257688 1250 973256438 973256447
    0x406081003152903120706060f080a0611070b041401021308030705100501031203110f030f06040c0f020c1e030601032603040201140a0306080d02160806100b0a 70
    0x81c0c000802d400d03400900960344214070340c03100c4010202415610b48042001c01c080a0f0180c01240b8264144d200070454001c88a0050141c40701903c12840401e005441d01445818014030303402009a43e0300944140c0c2c1440700d18010001c028520000591500080e501c941c00790880051001c0c025006168003050100b00035812142c0b208403400140c00c29030b1311155010f403254400c000c25101031191011369246081d5900c203190489a06ca50410345044000c541030303029050b001c0d006205020306018a00031000204001c41c1f01d00340404c042c40961401800300012148130f207c140c010820022031310340889400203805101400e045900200c4015040340c1210311a08140d105a0140500000002040800c8412713140b80110360152081040c0c0111a4146500007290003a0000e1140c441224020340840003c00040113546404901c041d1901185854550f888420b0f00050340b001d800c035685403168510003c00350092001900c1c240c100801d45030010700160040d5100c9800004504100c1e5029 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 973258938 1250 973257688 973257721
    0x40b070201021e0a260a111f050402041b0e0105070606051f02060c0f0a0e1c081b031908130c0909060e060615030a0204050a08010905010b03030f040608 67
    0x7664403400c1400b04480d0842d88036070510800b05d410600fa103000b4980301040c035550034011820780c02194100105550304440704406400d1482c12400b508600008248c02c41400c42c3e6a0401e0000115041c00d0a1051008440c0210901002a14280045d04010b81d01c100e048840140920b0400e4640700103003024402404540d009991011850307416070710000c1880c001c140078189a40036120284d854201110051060805500c43c505080241c1808980541d0b070001407014003800d04000e1740c4400b07000d0080c00e035003810143c071100b40102d120b50801184800d14884510402e01440c10a44d0160b1700c02191058942404203100c074030b0000440d8260030006522401c0d4100c2c111143d40e545d0f0708003400c000c1c55800001c1e102e060902c030700340401400000781c0c80c2c00707844003400402d00c41407080c001036020f4001800c549132085d000c000c0061740750307104200f84000d0710f402c2d000007a540705180f420908580d40307024541e0103500b084c00030f40c0e1003400d0314040d94105c030b203503080160a0703541c1d5045001e030309502c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 973260188 1250 973258938 973258963
    0x70c0f0222021c0510030c0506030c450108061c0506010b090307060e0117041103030706150515030117070e0702010203040b060f100e0a0302030a0311071a040b07020102 74
    0x8040f03035040209822400d10f020f10040082e0800c070701d40b43d04040c0035242040303000291899802e80380030840c50810100942e400b201400c0d01a061103180c0a42041e201045030203d851407510901c4070500f40d9a0400401d01e840e0710070071150b03041104d4000a040d007000104000d100384880e5020381000f0883c1901240e1a60b804400d80740c0070742c2c6034032142889130012102c60b03009120b001d80c041500c03401000703012036a40301611410080c0c614621042c0d800100104121001d003580c55446030aa1001c10103400307954420100410140c09014001a242501e54040c521031001c6582c0c00d49620140002c0700e054030000800f091855000302401460100c1d47d91108082c4071122042003846030f419070103540100c0c407503604010356031960f40401c00c050a42c2c40700c550f4071020810741313810224060307407076040c001d42c010707080104103940c13500003908050030b10300c080d000701301e8019640e10150300c00e0003614041c1403880d0b044155a0300f50008480755000d030707008012400d00000380b6041560300801480c0c21801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 973261438 1250 973260188 973260191
    0x2030405010f090b010905010f140910050301050720031e0c032a0c04060312030209031c03050717010605090409020112060f080c01080f0f070c1403030f070c0f0222 72
    0x8118030306142100307800d115101b161850440040782c0010103424a9080b200c40b000500b0504075003000304542000d01511015001c2160a0009016107082c000c0c0c40c0b14407003503242c2c900c1c141c0480e6681c0d01441d240d02001c1f0115001002040818240a09481c042000441c03a00b0b489648400415256216802206010301c42204a1345d104440250b42e1404c00e80d104800e50320390310014003c1c40260381050100a00b22145a42ca0a0080e48283c2c042c0c8581c6400500301c1c1c600260842c907443e0071a0011a446e00000c0d290010004c03581c1e04036012220054001000c01410b42c906a80286075005460b02e0034461a1507410600070f44e8410341300c80c00006c041e10350800c080c03075580f2952127440301e0520408000d0b0003144e20302403166006001c464030036a02200d50500548c1c03070016042042c00010440c005111462a14402003041032032844407042001004690b41e0a0100400c1c0592000400c060b0030408126145400160000700e80f9210036810303119403001c01e0342c607491b859048240403148801030303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 973262688 1250 973261438 973261451
    0x5031b13140a0e0105060a03170702040911030601051906030f02090915040b06070f0b0402030a0b040c050411070201120c0905060a030f2412050309040e0c01090e150402030405010f 79
    0x958182403518040d12107850100b204403090a102400e842e01126651f90001c000003040011906982d06068a00c41c00c580301da20b42032940d03001508030341402c031090700c000c00300c600c240e542070401b0040c69001d0310085480780c900f6045100300864000c0c46002e81b808160300c412000554001907011f645094030300520307411b6a0314056000300c01c80c00c098142ca610540c00c2191320491810407800300c03007c980d0800b10101d45a10b0988494a4052001c1c0040360948079081880b0041040d24032020301841c03040340940c1c0c00038900305c20042035072614280e25102140c02c008100050b0780024110039451902400891450b42d8030b07100759a0419554811a04280700080361100c1c80c2d030641c403c2000180e41c3c9010010400342e0041c400b0007201d8001c480450303009103c1c05000c54850710100081441c803450413649810100000b00d4142da00c0d081c4048074a40c02400c80c0419580c020036500080e05016200143e1840c01e441c44040c010358082c0300d14002c560000114013444808c0d00440000d4031a42c1091000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 973263938 1250 973262688 973262711
    0x91505090f010f091104091d070b0309071e03080403031101050907050d20030609030a14040b0f130f0b04150815150915030105100302090102070b0a200d020c04020405031b13 76
    0x4030407200b0320711411402260000304030210480250cd01502c3c1c500f0042021b43d00300700c0039039218582150410303404100448000002001c440c0100091031007607503400c40008500307003c542521409002217100d074001c5e02041c4021f0701d440745114074a6400c0420002181c01030242040c00a00e4281c14076094041c1800b00400c1100000090000c0110340e0f4034040320903841400e20400e8040c6000b0324451000410009600070440c202a000c003000d8640c030041e1655940c00c140c10620215800340350b1040c1e022504000c540261140b500c0c21122030b0402a00c0c0e4601a001040c0e001500c8a03054440c0340004110029080c02c20305480d90000041c0640c00c040c8160000c0341d85582091140c907114406194803400041e1080c02030b200e07031210603001010014280f881e10445030b04081d5045003002440d000304120a0501901c2ca406c000c4d141015004245c21410028101040400c0d00c82c0520300401c4108480d8400150700058070803501c207400e0105540a0000d0000c80c040c0d011014850f0a00e0810080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 973265188 1250 973263938 973263971
    0x1052a0303100522020f2203060c1706060c0708060a06330302033103030f0e06010509180f0c01090603050103030503060405060307091505090f010f09110409 69
    0x9186200c032480703005691401006030039004002500311405a80404110030f00c9144c014249041b03195440c0f60800b130000715000c3d48200c980e0400441c04904000400c144a0144116400c80d0001e10300140c8185402c0d19680c0c0440f0094a900e014074800902c03a000498280905005003120000b9180305040c075610301806054035005130600d01da02840300041c200c40304002c00f0a40350001001e00d00402111038290002e400081120000c207001e980c0c01070300c9041850800c0d000039842000c0d1600d02c0f98509000f8102d803440200c001800345001e03104641000002031060450700d04482d4900540e40380c002d0340c0b012031042c0611070310380d11541d0f031030218440c400300303003172000322805e83e5541419641c41300d0403000d8035028403014011400402c0441c0f12030400303401c031036070103031010b400c40300000d64900d9201d04407182400b274040703a80c00d8020700788000e1030000310854000891054160495041406e0080b40c0d04051240010340d6035604007000c039110880f416203004020300b4404001121500c2c09480 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 973266438 1250 973265188 973265191
    0x70f02030c15090f2d010914010c0f0201063b010803040e0a05060d0308100e07021612050601120c030503040609180e0c010f091701091e030e01052a0303 67
    0x40034080c104e40c06280c00c0002500d4842903ca04c1881020740300708280b40c0000c000c1c102194403e41d502da43e00407012681c80800f200c0008074200c00000c1841700220020490131442c0812030031079050801c100038a000d58000303244481400300e400da1071b460b8a1507a030280031010071041e5009108260002400d018044041c104403004010010419940d04c40480308949080701ca240d40701c456182c0602c0420310a40c0c0550f400464001d00340740c542d8507400e003602f04030350840c1c1070030060740030f00f103400d1202c0701d101040d00081114501e0a07001c1c81d44c6903111030702d031038050203103440b410881c010600c284008400010020741d000401e072907440392941c0d0000e14510032802440c00020001c03840052450051103620142411500030b40380c200d460600460f0311a0340d4120060401c015044085804030703504d00f401c0d50302440b1a00020794008103103015840c00c0e20104201c402d1008010441001c0380c1c2140410800d09c609107089552810b0480400214010017402540002007a21002c0d030041400401036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 973267688 1250 973266438 973266451
    0x163b010f08071e150e03121b0303090a0305090112020408010902100c0b0103060209010302070b0115021e031608160b0f0a0603031d120a0b1006090b03070f02030c15 72
    0x9844803500c1d0315510001c00316022012160302c140040402c004000c40089a490300b403146814030740c0d12003000006c1d14001c00f45400c0450350300002020609070740c0d030384c02e80085e0782c2908014504526001c1c03c0c5a441d030b01c020070060700f4807200103856085070b0301c11007010002c0e0a00c0030086440d103803920f66440c000c2104070000c0f400740705c800303000d44400360240500b5405140d1000980c0d074280e0031540c0d402d010b904548481d41c10f26400340418400601c13040010343c082d200080c580090701d220f89000910703007015003003519200e800c001001d11800c080841240c0c10034410051102070500c0d1450414001d100304007954508050b10105c0b84200040101d10078003400d001e641c915034a0716101d20940c101c4106100060102d48100d984904800058040c46600e940c01040100e9400ea200000390070540306940850300040501c0401000c103201085603005001680b5080c2d5025007804140106444041c00013002c1c0404d44601d55401d034401c00498896039489415150303248003141d080080f090054820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 973268938 1250 973267688 973267693
    0x2031801031d100c050421080d060803070506011202060412081605031c1e0b0a1203050324010903081c020a020a060b062d0403061d163b010f08 63
    0x900303900602c2170050383c05650f20200e400c00d00b04a18800d00c001141004421503060301c080c000c03e1095511445444000c5c1240c0c00a196988440e180441c14148140c0125007a003507110310510140c0c582d4419034081c1c5404140100240381c990400c41e03040e0294a9401c422801100051800c1100100107004000121142c0c1011541401355840c1a6401c0c1e880740300300d11044414030142543c2c150420380031214050000410580c0304c0c0b482c0c0020560b0040183e0203d0310001c1408401035482402500703100d48020f02d400144034200008250312624403000c2d040ea43d0100e0350804000841040c4c0e00d207180100c8007103503a4102d40a0107500c41d01c403080280d60701450846100d80505000013280e5000803079503c1c00781036400f00020550801641070080b90702e42020300c4003000280c803a10892540100c070740c0c0c44501d4141040455071921191140d0311000b40d511400c2003080000f100c9110780c1402d4511400c410b002241c49908807a10458040001107003125000007801188850702c0c4426035141605 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 973270188 1250 973268938 973268951
    0x9060e0601050102210c0114450c0d03180e09060f07021005011211030f0a11270129030105060a2708010507030c02031801031d10 57
    0x25464562409104081c0075030000e4840700155288031180c4256034030140300081c102000c01b2010750843e1a485d00c5070080300c425806006e4070103c40d4400720031140510240441000300201e0500100c100748240f291441243d10010040381018440007100c40f82c0035044004a1505050080414a50308200103480e24a00000b24900c51141415407048240c4001060a47c403a902107500e0f45130010145411400751108000444855014090091080c24014200381d001814110f0f000722160a07000e2080e40145100e02c280c0340040b03449234200750402c00850159410b01c02064a5410440c01c0001d0a18803580540452800342001816641c0b035115007448107c07221921540f81c0d0080c400c25221123011300041120b45008002884912180d181c05415098240301d400001507126403a4100104200c03418002e181092040d143e01c004645810301c1203106d80d0f04042d440f80f051007030441c401c020007410002d40707074001c2d0400a6605407100c0300d032401c00414650552240700e0010300700006400d100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 973271438 1250 973270188 973270211
    0x2160b160813020d1b080303091b01050c0a030e19030c0e07020a0507030b090109080d02030604110f1606090507032301060b030a15090e070f08030f09150c030304060906 74
    0x40240c0b1681d034050408064506141c941402c00500035040400241d0905804900c4a0701400510301405c0783c4402031100100a0b80c0c1612817480040b141410060140f04120000c200003032414611070705810000c6d03403002440d010404030107004240380c0c000b86d48150004100502a01100f040311700c0c4000e00b003010344031140c0898452110b2180a800c1da4840c400c14000301c2c921244aa40140210300009020541c81c3d80d0001c1c0e035086100761101d010390200c10062641028010308404d41c1c6070740d1010349808001c251402c1c1c9d901030445410b0040b08912403120402041e0b910184c6a603400208640000f42e8928014a22030010315402ca401c1c0d8841001e0320040300140a100300380c510b04d003809400c0d50781c1d03000040010200d50307644282c20030462500203030300c00c01c900c10309040b416600003910341c160420040d40c850306042d078859071255200700320039090300c0006030648480400c11a0340542c0c140b494481414103000380c1c0865490303808000103100800102c0da000d40b100710f01c660300034001a01d002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 973272688 1250 973271438 973271461
    0x109120c1b0b09090702010b040c030504020117240102010f0203041b0e0f01030605041b06020c0a0608010810020c0a150f1d1209040626060606190302160b1608 70
    0x380b1641004200600040c01c0310301e04405800d500c52518800022400203040000b42903d004801d0741e00401e036075a05100075960309c81c00f65085601c00300e0b0440d105003800c0b000030603500c000c410744e600745500520409149a200390800c40250000d40010364a9041c2410045a21820050040f950140d1503800103803011102068910511038007c588400ea0320355110203026000c0100200e580d0442055050480d1050002000151906600a02140021206000321801c19401507020f10001000401160000040400070803544450240c2c441000e4060540340107007203d8000c3c25200b1040711210416040e43c4180c004501000781407104c180071000301010000c0108504a450304421045001c600300b900042800960103040061070695030f486850303000d603000581c070342c10a160725005990000104141600306e8411140180f40200405818012404100505040c03603004514004108943c00d06404130940112440041d40b8100000c5103684001c2c090f0000420080c6000c00d80a0410b07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 973273938 1250 973272688 973272743
    0xe0a021f0e0316090c020a0f0305030a11070f030f0c0506061002121b070608010509071103090402070f050601052b0503040506030103140105010906260a08070b01060e031504080306030109120c 84
    0x100da07010b035000120b40c500321494be1000300741d0503040da100d20808007400b880c68010a0524003581d03125609e501c1c18900244191038803a104420005036049010203ea03010801d290000c404607118030305e200c0e4610090382031507a445c003540700100c80800c030301840051204042d86464559002d6a81c010b4035040181c401d24400e0203455003029000c800202d48030700454074000707910208000c81b42405890f000140c1642e2102c182141c02c45043e0101004029007088481c0c00350074101c92012510f02803c0c0c242012421b601041c120b10070100c0404018408148202c401070726010380710940da50f842c2d003088516212804c1d5894034561030b01000040c42c0360311340b01d40c0301503d141414001c0d50749400300d003084031441046406060307801900201d0001541910061800510031041000070703600d80b040250907086201c041e50b0098024403242c00542242c0c0c803905a001e0780c09103070b40341c0b241c90b5040030a004012aa60080c42d02100c50f08803021160040d81917003449204202c0000c0c4600102d6410f864041c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 973275188 1250 973273938 973273943
    0x110403020a03080904051830190e010f140d0938010311130905241605040902250303050f01090606141b0d081503123a0605040e0a021f0e0316090c020a 66
    0x1201030dd010b51100c0b10018600c6d0400d00b03c01086403a2152680082d03000c6d002c0f03585c0290301265540221201e5010001c4000e400e16946c6a170307030b1f0742c9541c8130120b5403488840580d02c20480d42c58000b076000d04c5031b801200702030340081c1202c43d030203440140c0019042c420351b140d41d40e1010032000104c02d942d54100c01001d142c61a51284c2c105440d200c010701c0613410200b05c8100711a0640e0070800b808001c4030b95010014025035011800c1d00f000c0350640700142042c5c01c08405c4900f001411710105030480402300e001c5804195060796045238041501a540589402401d075014028076601e80c00c3d402103009005106c50150074a04410410826030b0f20100382500c414441014040c00c4400340300860f48500540c92303203404400d00ca00c1e155030350303c920012160203c41d05540702414001801d092041031081c02c480740041c42d42d40d2181d0005004440309150f420002072410403500f003424400c020404030200050122440c516007038210918040060181051003072802043d00503080c40040c0f610209074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 973276438 1250 973275188 973275197
    0xf040b0109031101020a061a180702070e220516080703020901030b04111215010b030106120902030f1e0c030d080703110403020a03080904051830190e010f 68
    0x42c81c5a94501400d00d00049460650040421000109049001d944060340032603210540000c0d40302c00b04446a82e200110200b201140d03000c10049580000e005816a03030090701c01d4185d80e9681c4103150011810a03003810403007540802050400c0303400201628040588070b800c0e111591541c41c59603844c03006200c06544005450010408102c00341541600035025419600c180c0242101081c420500000c0300146603014402c080c41042410590314050700e40a04024555458690014141d440f42c0d12402d0401d0780e2a40c3c10350440d642004200ba2011480d001e0b00d00e9001c3c1c000c541030304501095110f44007070040b900312140d21300d40820a01140030940c0c48128a41e100c08000700d0060100f03d8101b0000c1804010200c0941d03100c54120300110711402c04c80da0754188600a11040d82c00180111142e07008409075170405000101d01030748813241010b4802c0c11b00032003e40000c0c0c0c07200304a81e25001d81800041415440f41c00f086508200c2082e500d82913403400f900401100c601007070040420008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 973277688 1250 973276438 973276457
    0x30b0411041a0111101e1b140a030b0a0b180402070302120c0708031216081618090e0708190b16110105091c020309060a080705071a04020f040b01 64
    0x10f40c0607000d030100e40c0792074000b03c49101c0c10800150040b105114125190300c601e42805140141c91801603200b070010006c20300070101c04009000d07000380007480305440440d2012429280c2140700794061010050000d1098100955821404045901a00400c40c08490b15040c01c6c0b9141410f00032111130a80c158014513180c0424000400307680c00202c22400c0600408000141d000c4041010f03140005942c078081d40e450030101c200b10384101c1c1e44002c400a001364002008080c41416a014942c0305143c103109040e006000030b900d40d601c481c0d80003100d0a503d041d43c0c05954040000f000410344202508076108105160fa41000020100d50300400041000001a10349841e1154074622207100381043e080d905d002e01c0009095035001c980c8100a60310014013030a45045051350107400710f500340040c601d41110ba0021510314414500f03104180581d4101003403420b4450412203841c190041c250a800c050f02207042000301800b40c4040e031089451800c9200340e8500342c42046140a0f05841c0c21454 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 973278938 1250 973277688 973277741
    0xa060611012c03120c090f031605220e03090f09151c140c031606090b090a080a06020901030501090219080910020403030e090703050c03130f0c030b041104 68
    0x300c001d02d000e1011500091190311040000f5891070360180300012911515491404103012901c02840f00852007644090540f1254441c124081004d0f1041a1005040480035005074031710000d503408007040c200d140801414241780c0200191100420071665558203003001820090040300907076081d8594241c2032542c60251401c11407070400100141c40f20340c1300c0c02c0e40f078941c1c0c2c0c0050882d11003091180c0009030b5200d06880c2c18019050070303130040100020001c1c185400100800c055024040129800103501c004135528480c0101c01800004126000700070f203460000007035007107860b450b030201b8240030020842044a0003607801200f040b0880c402181d02030301e802c6030b98080c0580018000d00030402800003d044030700007440a540072f52282c031440b16a08081c0a07542d1802029041010f1412050006841c0c172101182e40202c02040d08440c0e01000d03050110903103042140044c0803030020f010002c10002d0002e0740c9881070f070041403941d00a42c4400140000d507101c1c01010b082952248815003070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 973280188 1250 973278938 973279001
    0x16360b0a3303051603230106110f0f191b0f060e09060d2015040f172e09150b030a030e010c080904020d0506211b12060a06061101 57
    0x200346c024400d01e90364040442e07a2090855080c0c114200054114001c1444071130104100026000140011704a040740d9040c00760715080c501825060614090850106002164040b14031605c1042e40c0940e519541d540f8140b0700040070302c03524021690400c400071462808464030361040c5005440704c0f007064419a506106106450901911410800034070364042c1c8440482d1032001c1500c005241d9213a0801503c10070f00c840030b0b400303941064007003001c840c1c4082020903c04401c1d04038440f01003a41d10659900d010b01d4a80c035000c50f0302207181403060340034400c086c0e8464030b50002010081100c1240c40041c142c0f0341a841001501003500919500038951060002142d0706006044072810101c030100010261f0340007080700010310781c90350140002c0c1c0c54030440e507001881e4500f002c070341c0d03080c07000100988904110b2600c0103002c6080703251000940b40d074090303540d8142200c8241e032214070f0074851500007401e0a00840b000103038450444800c3d2a0148104582c410010a0164000004807900d01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 973281438 1250 973280188 973280201
    0x405070f031104020715360c050d03021c0e040605101d0303130810050601180b07020105070812090c032a1216360b0a3303051603 57
    0xa8800c0b0816490494000c160300c0341411000e001c203103074514600c5c00040e03c41070b00310000c61107c510207258811000200d600615100b01d1348141d07a010030040e11420183c0c10406407041c90104a900b0030301d074403505035001b140800c10000c100d4080140544a40902c54038507090440321000c2010b00b0f00803000c08032119840c2d03074107000080c00c892502d5184104000904001c0e40710459581c400d00e10800b94003154007030380740e00007400e10340aa043c10038440c1c1c0b50071100d090b11441c5c0240000182e41c105691049085600964110004a94a03a90341c00e64840c90fa104a03841d030058007401c4460001e80c6808641c07121a4074480030305c4080485110317042c142020300c51940a41c8003085200d8010802000e01c20000c20b110803030b142c412110f20303260311000740104240501c5142c1030030581e00c0721200c1c030300e85051020707254039040000c0307404084002c02c0801d4410740250003a50701d03141086070403a451000850100030300208a1032030361110030040d01030311740c2a1120503000150304111400c1d40d200e0750104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 973282688 1250 973281438 973281443
    0x90608011b3f05040b310204060302120619110a2d050406180b071509020303040f050414061c05150109020a0201140606090105130312080405070f0311040207 69
    0x600510030216030151442c00c028051070100d407100c0410060202c5025461350100d95403035003200c0000d0b8260070940c1d4072000030b40c54550140740303000c2c50b095403103a51004016603409050306a4458042e48030325034902c0210b0340c044207030724880b0303090000340701c40d00900c59100001e0007074504024460f00c00b55030040c6011210610070104181c0301a81c00e0000340c40703008044e51a00e40c20b64550520720020000008000c40f82c181448000041001001c0c5c07204440711990041e0503158505002140d040280c891030202035070501c40414045910148540c103441100c1c0105e50411850030100482019a5812198143d00003884000d4098180110051303600d1944560299180300070090b040c40d00c001002c1c0c001801c216030100b075000341c4580910440c0301d010061216020185480000034801744a021113150400801040c2200c1c101c220003031a002850f4420041d5151510b85403000b0a03183c4112000c0d02c662064a03030000e2951080d500301d10949400040d9080000f071480c0501c4040e51241104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 973283938 1250 973282688 973282757
    0xb072109030c120f1403060904080c03161103010c0309020306010e06010c08030106090e0f04050d0f03020d05010b03070912030f030203060609030a050c090108030a2007050604090608011b 82
    0xd00081c075a80103d003c602054803034400d040d81602c001000c6044041050031903440410900c4115a90308000700e52203980000800d50390349890000a0440c0103c20540f140c07c0f81c0c2890700c0041058181c132102d0a00b8040c0c00070000200005001c40694000ea40041c2d05508030000502c503e1200710f034051b03030000040c144400f42840c99600d064965200342e02600008118a1050140c09101c9c6802d58000304119542001410161101c3c1e4940000b000c0307400c00e00601040e41c854030750080d015143e954113a054204900e60f581d103000c11407a4005c45a000000351500344c041005881e0821058182d0f806550301d00c40c034082a2400d034001c0d4405442d035640b140c0c09000020f0190b42c2040503000c2c07940304a020308883c101200500029150607040203286400038401c3c0d41d10564403009480c0910280341c0c070048100078001c805810801d658111a13000340d000100400c0180d03954005030308480c00305008110700300c50180e04800c8c99180000307000006004440002103c410380480c860038120207142c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 973285188 1250 973283938 973283957
    0x170402010905130e0d0e280b0c06090d03020406090b0d02040b030106050c011514010e063109050709060c230a030801151709030c0a0f0b07210903 64
    0x1032070b80c8104051140d000e0351203040c1c44440d082e041c0280c185d28002820101429100c10b40054641e00001013000c02c0c0c81d511700380c0380004a0240364440001d0141c004120380e1400000085600c4403011140c2051a12401c0440807486100b03100f120215107455403910829418035a250034242e0041c11042075607a000c0c04041118035591b0005c3d4021314898803416540e4428140303031808d44201c0e03848644801241c8804002001010700c86c0303081c141091a044922003070840008140340510302c00c255904008825508071f08080a034200300840300b0910140c1441d84e18001c45040d81c8044541e80d00085180104000e0b550007075584101c2e241c46001d981614028180a4141ca0b600f811003100d1554491510f1506041d0440207041c0901141e42200d42800141e1401804428211845c6610502e500c1d0001d890080240160760204002c0e6059072840f25440c1000703805050941c60a40781005007a000c50700103030185212420800c03001c44045030f00800c5d001610020185103400f81c050100d40e01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 973286438 1250 973285188 973285199
    0x806010b2d0f031914130212070314100608211903020a0e0d081b150702160819170c1e070f14190308070501050f090109031704020109 59
    0x6014000030185402a65124a8829000f001d0130321013000041c6124135101250740500880001590b000741c55080e803032040b041c0c52000c900e0a00c0c0c0b981482205004848001c810800717201c0300300c1410812030003251a0611103289880440700075108200541d40036010105000c000c56040c000320601d40308a2a04240c542c0704440405003203009200006980000c8200005801c046896004203082c0e4001c542c103a659034900c0034611540303106030020201c80390024040b1800308682000800d0580c0c0007121400e100304007030360303490ba100ca15814440245501040d01040003a02c105400c200c0510f0300c0e02c902064541c210030500040181c14000e004000c0e200c008002044584418903403100248440c0c500b40b00da86081500527000002e991107420380030001440d1144640d60396440c2110304841021100c070031040c968500d54801003524001207891400d20106500c404d20a80001040c41c0f0103550340e0130706900f03c1c1d120035070003030105d079854070945441c80342c7c494520340c003610605200f90b41d40c0e00c50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 973287688 1250 973286438 973286527
    0x40804050d0b0a11041a070c03170408100b0d1203022205031b01090317040e04030c03090f120303020d0e06010b0a0e030d090e040302011b050903070806010b 69
    0x4101c15030324038a4590900624114500c1103e04540c025503009040c6030030b01d85c4100c8080886003000001201c0030500009001d14003070322100030b42c0e1084c10b0b000300d041c5100022039160400d101b60a118050498003904500d0035000700c012406004102c0306003024240d44068821220030b0074a000c0690a200e10a0140c008030319400440382e808540410031071402c4101450f10032118007010401ca090380c0018050392f002031201c01a40da0010a0301c0c00e882c0458001c281502845d40200c200d10245401e100030305402409045665001e80c2d00c0c0700002d43c982420229841c3c052091301c030086e50b40b002035008240710341d01034400191a40c50102c0c40c0500000e42a180c220280c004080c03070200028848019034100c0c40c0306481c2802600600a11410080040d20304c41d910f00c80c2e10100030000300041c0405100707503c000350141d4503ea5100c100390000034014984e400c6094401d000748100c02e0081417541d0300060702d83c121446079000d185031000c101c11803014a2000d180c2498900102d074a990400d0500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 973288938 1250 973287688 973287709
    0x50c010b0907020c03060a021305010807020a0503040b0a1e0e040207021309080c1606121e090c091409030904021608040e0417030702070b1e0c030c070518010e04080405 74
    0xa43d8001c01c035544216003018201035019001d403105a104100742c61580302c10b80e42e401c00700c4400742001c0c6800e40d18110f082e401c200701c0040c010883d000c001404104100391002500f0b90014a9482c090b265070035110106040800c0307001103000c90704c895500200e41c60a50001c000072480581007200103400c0c8103008060320000d5070101d80e010000305d0344e981850001c10481c03204d0320540e02040c8001d03240000143c1254505040c800003552a050300d490562108a400e11b40c1d03110f0b802003006000c1c92401c0192030100c0900501c1043d81c101581001e6146000d0007641c050812000a940303460750402c2004000d41c02040c00030803042400c0802408111410090b00045c101541540080d02d890300d0000c0c5c0c08580c00e44101d1a500040c800c2c4540103500058079003d54005030703030050303507004002c0d01c80c1c244d071209404100201800040403403a858001c0040c016540c0d4000131180080e844030200500c41c24070482e41242c1c03160400041015001d10a09650814041c0041a16085d00c450204640844 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 973290188 1250 973288938 973288951
    0x110613030507050f060a08070807030e031216050f03012c070e0103050f090c0405150415150e09150103110c0102030702160605041a0d0903021011071101050c010b09 72
    0xb81d0020401803e00c60200030540000310790a91901250200280a004010304100d081000003400200c40f40c0c0203034403418403d04000116030b04c0c1c002c15200ca100380241100d0701d0300c035140144d6907104100e00032019249118540d107002d90460b801e0030050740e4807105c2140d48144896841d42d2443d1017078181310203103024401d07580c1d80c0c202002d0040c0026068840181c609003c90300b0329404c102c82082c0204d040b8644140c01c03140071a003038592041c2c0c01c0c44500c080002e1030740186805c4174585000100b00082040382c403105242302c4042407008003070307541d45421408643c01422070300c00540da454846510000011050600080c00381e03201041f1401074200010219450703600109003c06d07141c04001199825554000b07507030b02c1740e0400d90700403c203000c0c6204680c08240c0441c01400001c07a8030003964101c1320081c800300000b12a40c1070003552380e1205401943c059190a01c1c40b402e0340c10040803a0b101c1c03900304004912070b08200e00112084d031f100d040010002e558620400d04142d441103c42d501820 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 973291438 1250 973290188 973290193
    0x20601060306120804030609020321040504140f060d2105040518010503031617070b041401150b0306030102072f010318030c02010504080708030307091d041106130305 73
    0x1810311601078200c400780d07041524001c01c100c004000007a9004215800c0c0c95010f01d0109020300c10780301103482d0640d0707903904182d0f0300449034440303003078150040c007420444000722802d00101c40c0030410b070016070300c00b0366515042d1200b11000542a00341801c1c1004410305c9410b801035a0004402410012007140301e95500040340040d0800c80342c940801040d00e181c0050305061880d524110010ba6a0302c10280030b1840c80355662001341c240000c50307018010440041b9600e1790340390014a810034500c081110200c4082c08281070403884010144184016580160300fa480c0b07160601d080451543c00043c140d540c51344d001c110000014000c509800e00c80c91078441041ba601d0741c0094580c02000703590304020f04040c540384005900480c0d08241100c46601820301d001c0c842040d0004855510594214000c80d21070101c00245010340000194481c41c9942c0c0ca1f04031440e00c4010304400e110000c200a0700964111000c240030a030f49410031039442000829281c904040342204240c86000355005070b80c145c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 973292688 1250 973291438 973291441
    0xb07150203010816061805090c1b0606031507210608010e161e15090e0c07060b0d0206030f070318030806090109091a1f0320030304080d050906040e070206 68
    0x6132000040640900880d0803d020109000d8440b01a24525441401d100b2454440403810f8104190101c030314038040c3d210318881580c0015000ca0352040f0603110703507000c2e01c00d0580100c00601903071031450140070103594401c05240c5c11440e90000090f0310210030400c543d19000018a02024420400003401d5030000c0c0c0154041d100b242c83e101c3c42d103035200010310000c0c65102050718040c1003440d401d45c0c0001e00000c0b601f000008007154080340710717000b00c0c40c50a10181401000700b000c001500007141b28850911240d0030343c406020100c03800d000002c0d04401c00740085200d0092807090660b10000a140004400040d503400480c1541e09503c154085012030b0240011420700f0b80d0043d014203581141071214041640d02c00c0540300309010fa40240400035000b180f24545030045103c804507800c200c1d0340d601c42e241d080c0b456561001d00d000082181803c5410501814040150390803a80904090001807840e0b5800b51901d0340007040c016486802044085491400942d0582c003500c0158000c040c6c4d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 973293938 1250 973292688 973292713
    0x1707021c12050130050102130b0c010b06190c063218030f0322060b030c0907080105010c020607020406080304150306080a2901080f0c04150b071502030108 68
    0x4884060704440c030307540c0b1303030401c445084030702c600c004481064481c2c80542502e895007000350080c010840d1040000084034400289002e1240290850020210003048014804802c025440c03051050100340e01d4540742d01d6610350744c010251101c13560b0080300b0108080000d84114074406442c42e42643c040303030381c1c400341142c1400c4c0505891307888000314000414020380184525600d0085400c0b640c0ca95000000207488142840c0300040e04d030a030060302130181103051802c24041c00a002407107021340f240e01c000900781e2034001d80c018010020340e240c8450503400c0400440d50641001026600594100203210040e1541d22481d0300500000300503640f6181007142c860200c900400d45001050304100090200010200b404141154000c41d0030084201e00b011080810f0042522005101158000041c24200108502c0740d402c0360351060740d50702000042004100c0340c02d41c101081400c034000c418441502c02c0c10081000714014014543c118110011b000141e900980184c3c1d200d8205202c043c68 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 973295188 1250 973293938 973293941
    0x21605010f0e13111c1e1d2d030702131a0603090606030c0d0c091d1b10210b0402090a030303270305121005101d030307031707021c12 59
    0xe100490180a100394148404044441000c00514070602d9907610140307d070020598090000e280460303826541070044144410701003a4140c0d0394286841921000ba0814040101c202d6116590003080300e500c0e04100540303d0002c254020101c0e031032114500311001c50b03039a110049d5100c1e600351030041801e4901603050504069004a42c01c1c000d00300c03040c1800000d00700440d9001580c19500000030300e041510040381700004409014102802001c50795001801d091022010194055880800e0109a403000b00d941c2c04000d04603400c01101d10100d801c070540a030b0008141e01c43c1c010070242c1010101000502080d80300d91003180402c1c0c4c4e071441d4400e031401050709194043e2071178045002c10b84143cac82c003400c14482c071402e450041001800282e00d1003d902041c1000c0c0038003508802c0031000010024000c079404403c0c2c0f0300d86040c0c004104100e0f190010440f040c1c1907041e51400c03403206801c40396004c03141003c0c1040d03055000700760384888070440341003c0f17190300d60380c541d24840040180c009020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 973296438 1250 973295188 973295227
    0x4030e12150103121b150b06030a1b050a0e0108040503070b0c0415030504030504331206080a0201090302150d0203040f1b05010f051e030115021605010f0e1311 70
    0x505015458406400340440340d08086005c039005014000304400340803201004102c082c4000e9031203c001f005000504c2c0c00c3d5442041d00145085a81c80790300b5542c0030549440c013411046900043c003042415106520480d034490308580b04130300302e034100465039903030484840701290321107030052000c5800c1080c4842d01300300e035a0207501e6041c200100d041c0394074010102d200d603000d6041200071403c0e401c1401c440f45921082406103000a082c000000464000c1c0200d0305401c5114111f81003000c003007404240400e000092a50584600c2540c3e45141e00340b0104000c000781e0300d940e400c41444800d9003074050b0300041d446940300f040f6008409006182455400482510095090a28950501103640c220880c1c0181c604039040060b02e450f5194482d12501c100c801710240310b400d010000240303280d05000c159000000980071307541c05094040025280100700c4c8516070009034071590314054240030740785e4901402c1c809048044021601400740b020394a1105001042e0040003503c2a110301d000000503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 973297688 1250 973296438 973296473
    0x9020a020d0504180e1c031521110114070305090a0e040c0509060d14070e090f07090c0c0204090b01090b0621060d120903050106060f0804030e12150103 67
    0x642050f013020784c880e85985805035400d4145589000140c4800020450200d00c2c10704865103201ca4482030000501504000c50308800600c0300440101d07071040e20044843e242c00400006004c920f420340c0b20695400b01420955040c00780785220141113a500b2801800d013140281c543c903a4816800090010422007607108030b40c401d041009200016481d02c614008542c1c007200e1103800d546491000818110f0032020081803500000551443c661011500b54102c801c0c11500c56081c1d13440d2203c1940301d01480d41031041d560840c5005110440d040d40c407203c00901285000402212a640860225030841c43d0984600107201c00400900d2100e02540395410001e81d0a02c1c2840340c58410703040851008032250034100113181c001002c60301c0d0840d80c0c1d888543c22070340c01c1800d040808009000904540401d031029400c00c100801c10034052011030b0035090b100d0f501c442d11a555a10100c940a080e40c0b0f400d0347c454400802040c81140c2001100a803444d0001c00782c905501d5443d00018038044450314 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 973298938 1250 973297688 973297697
    0x715020304020d031101150810052503150e241504030611122409010e0c090a0b040609090e010e07031709030604061406150a0302130503060109020a020d 67
    0x1080700507102c824107240040d61501303260074040d646400d40e50150403440305c2005440b150250018020a00145018800095100400c0301d0b44401c13440d4403900b007110f01d2036882610340d00e840c040002d12076480015100c819840f24171345c841c3c031882d450301c04450a44c0c0d41c1d0308410302071044507102060101c1c907240c00c40c02150210a50410741c0c0d00740c0c0503030059103c00f43c01c1c141c1c0e0f810402d0884003414100c690803071a01141040074a4401e0b5018895460f190703021031601c0e1244124242c41c1441c0788440c0c160703104902e840019035103c0300292602da01603e146038010640341c40016002e50080060406869140c44414003070742403855030411a02d00440541282e07040c0701e05c0c030030201004605402900c0e000365080c100031382c64104109041c496102d0041e050700c0f40d082000300744905030380100c9014440301d044400d25100c00c0d00b00030400c8a80180180c40403010006490035034003a900a095042c1e100f101000d005603160300003410407001340d03c201d00007500003451003022541401881c14280040c100f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 973300188 1250 973298938 973298941
    0x10b0a03050d0f120c020a0507060903080315010c0c09051b070b0f090a0506010b040e0f040218071817060108060c030c070206040e1003260322051207150203 69
    0x300c0c01d03540c0440c14800c00a01103030b0f41950309514801c081204607850282401d02044552002c0255900d14241c0152510700444001040341c91040c240310040701c2c1c02c164054159225501985c204d1883e590350b103818428800031070703c001440c00d2210801400f91034000165890300043c0c903901c03100d100801200351602004001c0014000381c0110740c00044d03154204c500d9a80d05010303030b071800c011190060314a11850f4000100f02c0340f0070004009480070b510684c0c0854840c0c002e910380f012429200203610003030000401d4030000d410101942d10010615200039070141941308005d100e100d5411103807604030480350485511a00300502401040c4450040015144c5240e0000030742c000509201603041c00000e00205646d04e21060314040e004020401c0303491304000801038411030781c0384804c0f24078003481d0b00d10410f1201ea6028512003d0303501c4860310700e9569a901450304070400b01242d81c2c10303051080f404038081041002030b0740c003180d2207690a640c0e480701802e00c0740c03151001400c40c500c0c0500420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 973301438 1250 973300188 973300193
    0x302030d0507020c0a0f0f05040c170606040f180e06061e0301140a0b121209041d0a0f0c301104050c0d0f02030c090d0611120405010b0a03 61
    0x400c848000c03184000010791500e610004a041038800141141d00071004100031030b50300d1462003a4422100300a01140d0440e0b034840501050b102012103010202d06003040d203036002910548816403051000700120300d85502c03040003030180300d000d40001254a40d05a02002d40c182e940c0b1170344070003a804400405692411500042110000500601c1450003a0800d84029182504044000003c0b41c01a5496207020288800200f6030509070521400d42c480317039103089460200e1030101d00890121210b2a203180d840070311025202c0101c10b41c0700e9540c0354400780c0310441300744051400309108102c4500d00c400c0714148201d1601c400c2d0408140581200c41950603001c0203800c03001c8103100101104090000e50030304000c4d9142e1120100d820500306403c000d901c0311020010808180e010008011440c003d416600c100c1c0000c031806140d02d00100121825071a107c41c0d0b0032020b92081e40c01180400d4403011035004c54001c0e0790140c804115900601c82088000e0140316403104080d42c43c0c81702140382d45c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 973302688 1250 973301438 973301443
    0x1218041d0706230a111603030f260622091109010e0105010e0411071b1701050f060d05030d090609060f09020d08030a06050607080a02120408030d050606040512010606020f01090302 79
    0x2c4e01e00040c8030020301e2000b0f84090a11205050100710b0071825107566490502900100c07a4034580c0700014860500c031b400035030f030400b2240200b4690003e54201aa1b9000c20f2180141ca807c00e5090380000e200c50b0181d80c4c500c18050750040520441042c0030105134001070080e254010b802141c000c54105d00140003030b0340c2c080d080d540449400c803004980700061500e000c1c200e1243c0c1402a054a0382a43c900801c510080152401c851400d810b44684c9101440c21600722001903400301100007a1101140c8249410b001402030113003e00181d0b0303e00000c654400080b03600001e01100c46641300c0c2100c03021300807148610604495460f60500c00d984066000444181141e9001000e882c0040b02180703994a8983c00b40c070203410040c110729912122802c11a15036005000303a00700500c6203002800810040d8030603201121800c100450401d02c04102c070002a2000505a640242080c4400a49582c03540001141420000c00004480e42080002800c00e036501d144001140e04082c060400250300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 973303938 1250 973302688 973302697
    0x20c06040b0909130f030206090607020a031d0102030c0304060c050d08061309050309130207020306060a0303020709020d200d0c020d1b0c050301021b06091218041d070623 75
    0x4a840541c00e54440c0100301c041422000094a45c00d00149008201a00094454000d000f06021541160f0f02c41e034040341e40e448c00220080c00524103403d00f03103540100c4460030341e0454050058034113250248030a94610380055012a0019901c044160300b0302c4402d01074095a60214070b404400e919114000c284080b25041c41c7e05c40b03c643c0c07039000e1824030809105440100d000141f4403d607049152044402030742083c00c05a10900038080030030301e0b900c0d01007420b0044950540140c007013549085042c2c00207400900301c088035035450f510005113102609810107c00e012400d1030342d4880508540b40821113184804040030b65100400f0f03045825001071100707064005894206408846da4907003581703a9140c5501841d0190700206400031000400d0070050f40390f049550407078085580b0340010f1680c5a039004612491460200411148240e4182c0742111030607000d0000301e81d0b0b000400c1c40340300ca507007007448401158106038018808281d0104009c2502404900031544540740f81214140303511a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 973305188 1250 973303938 973303957
    0x1608060310230702390901081f02091809010209040504240c050409020903010e010f23250e030f0607020f0c100c0203101112011e09050c0408160501020c06040b 70
    0x503512400b45c1d1441e40403500001449015202c0720041d40c1d550840da5944280c81c08009007a072716119a01c0070201c240c03090f02d0a4040050411510b40e604d40c01c0e001d00148090304500c821b5400b000903100680301d41c040d02c0c0c002c903c1200311179031019110b070742128030403000075140148500b0683d5100c0002d5121054034140d8244840040ea120340c0032000900400c00c60b030f0155829400c003200c0b0704e038021540e40156000c85441200d082d4000d2406501c161480e0704494028802040030420410b9903034080d0030f00e406148038205605c0040d00400001e10700102c01c040c10b01c0a903c40b10030090b03c250f06018000c1c0d040440c000a01400201130700162144a1012900d0100b000f00c4c1f61000655070f04024680491300400c07000c200036612006e0004541c2c0c01040501c9200d40b01c0400001c10818100c40e0b80030a80d81c0c0c2078804211400d041010029103006040c17030314031a10500010803030f02c100380410301e906064615240c6441e0702c2c140006e42050400d0082904c50304d0140410095241c10500b1221a0765 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 973306438 1250 973305188 973305253
    0x30118080a050c01060902030411190e0a2903010c09120b0916080a1a0f0a0e071508010f050a05060712140a02160e1608060310230702 59
    0x3100c1060442e8180600300e030692280d0300300075001403101c805da80290b001e43d002b000c0c12950f1402d600306102100441d0500a02d124500d0002001111012804290041e1500b107003c14142c60307064618101880a04440f240111120b030b603070004c0d140074031848120b15240c0c1040c4c180d01e440c10403840b41c0000168000f410f1252543c002468852090050000d220a4510310310340060b26a000f190341c2d2800040c088850f2030328000b2666110300006100d40c0308030054054484155229414000945075840d00442c291040810100303600ca4480e6607042e0f4281d41b50b07501f14907989001e41d80100034000b6885140100c0d101c940030b00542d2030751400c8401042d00001f080e403034007030268000c030b1724240c11101020005202142d40d10019601241815500c400d401418080fa0340f90b584800350941c00340ea9210941c0765440b440c003159400703245210360255000301640d60b5409a5503041e401d90711174000501100b042d0403440d0303100c40641c40a11740c0040c620320060034104102203072400540500c2040c0d41c00318 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 973307688 1250 973306438 973306447
    0xb25021515030616030c05091302180604090b13020a0c12140307050408100b0307060c0c170f07090b1008151807030c020c0307050d0c1203120b03011808 67
    0x6071114603060302402015046400c3c43c58461224a021000701440000180c1040c00d80341820f441071003965600c81c001480140c054228040600c000d51210300b80e071190400800d003003031640d59150060801800034000110340300b50400100090340c02e07000407140c400d41c0b0520280911542c03001c020700803180c2c0100d6100640c4000f030004d640001081c2c01c15a4101070000c00c0100ca50350020142c0202d580100c01c8800404001c0303c07500a40794102c00b0180c1507841107008101c000e1180c521548514001c0c041c089041d5220034000c6128501c0c4580323100c49074021018590051420028200140350040007002850761850000368108071000b5040c04114844004c6206410000e111140807040140030107400403a120000b8076400c8210781d681d01080c81d10916000e9240045a01c1c5030680d4024080e01c000c40c00d040800400c058100130a4418004050010403048100052072007030f5030098648061500e080d95520341641d007030204990180c1d040014050801414418044d1800d5002043c203455 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 973308938 1250 973307688 973307701
    0x303030e07030605150916020a12051c06150f0507060b0609031006151103040905100b0d09020312070209070c02031c08010e0a0606090915120b250215 66
    0xd007651500003503c154601018451401e048803129003a52000760b600b84500c0d502d0702d40c1e160060080ea2810405a0020b030181000112411714403d0410340c1070500c4c0c0d00706040014200c005000b94126003224907582c8805211746a201440c40100350304034680750281d030802c0c450081c11783c0105540244a56103a0000780250368400b8161011500b0241c100c81c1c00e0080340b1030140140105100302c03801e16101042c480002ca2086142100855001005500d803a1802c0034000041200034804510044009030106404408034001e008514203054003052424a0707004044c00d0100c60020034004010801003100140c035418520303907004040703043c28045c49445001290402035601e00010140c1102804048003d400005c001e040e030340314038016022541d8104001c01100e850b4020f00e40455103501d010000000d142c2c0003010031800044110500560301c0440c81e80701400d0441c05c8400b030342e0a40800c074940ca0f85105018008040002d00d035042000034070041e403181900141c04800c07005445c00501d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 973310188 1250 973308938 973308943
    0x60e090609010510272307030225020f090c0a1b030f0516080319050901050606031609051801060305060a230103020f0c01060e09011a010c0510050f01150201150303030e 74
    0x2c205e80014006d00103110031030160500c8000349621202d08102400125010b10b1291090300c03840c00b408445030258566151f40400c5007058546e040381d0002d44541e007881580c480500301030040504205154407002c0007000a40301060100c101001c140b403c003070903408640d0001c8800c12921a50030040c0d0354000a0ba107102c056105010040d0083d5400814490301c482080150150a0070140041006481e0010124266a4151402980806d0a001150071b0901e41448054040c81c03030b060a9040d290f4400c00b0442440a200740003904001e004010001c02e40c04d401106d90010382107a410401c82e040404003000303e903074462000603150360400108500c1c0d00942c1103802800b03295088586640300c081400380070301418040d0b501c0d500842004145000e0050244680c080c2d03800390705107401055400110b6041c21088021f8800d84583c505030018012284a007174000c1202180c00b540300c1d810502d043d000e410074141880d08581c03402c0b0460040700c2186400409807507242c540450405a01401c00d032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 973311438 1250 973310188 973310249
    0x1c0f05421308090a0803180303031323100204030b0f040c090f1113060216080a02010302250b011e0b1c0209030601120c050a15080403030f060e090609010510 69
    0x2500003044d81d5010405a0001014000141d590040820b101c901c030b40505031640030a0301c03248408100601c12100040c4420000c1c000c6500c2603048940348143c400e4031a24011500d09201c00c46507001900307006102a9400b455440b02040d042c104290425950704a00900300344a80c9401c6a030302c2e00d075441901c50a4000010070960800b00d151140c09140400c481c0c00c5c01071040f0b5001d88142000c1c0010000080d5000049850140252420500d182c0055010b90310011071108562455a84036500c686000300e42124103008014501c11581801c0ea141805224a0060b0500c540c03859820400c10300034504850006504100415144403001100d2000e0b0003140c4600307503d80102030001c24164104800c0050460144074030303910581d41c1d0814840c42003051302480f0080d4000c0c401d8040686e001c3e1500941051081c074000802001c0d400c0c1000841e03016401024043c9060000c0c0440d52400300441a0401409030081003d0f06100c0c1842c580e1b038525120305004801b8004842e06035a01044092 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 973312688 1250 973311438 973311457
    0x9090406092303040906120215131a09030f01020306100c020a0e070f0e0f0f210607120f0614090403020f151807051c0f05421308 57
    0x302610340504034070f890b6000780c003611801c24601400010382c1c001c4000c40700c60442e00a042c15030a40e00001481c085a408045240e841d58144440010819a06400301c1030040083d001c40c0c4e21408500e04050a24000510f03140c29a0300500a1004079582c145d0f0a4003a1000790500b941e10b090940b000c02c548810560156448039100c1c0c1c100609182c02480701e42c0170f09010395600d000d00d0b04090406c22446a03e03034515400c2110400001d401e801d181c00307050040d00d03964401d48003c0005004103468440c00700d40410004e9001500854041c1c0d0901548410f210800070a114180c24500040d06260071a0156441612502e022409040c000d01c1250a451804030580e0716000388401c0e601c420040554018034031080700101030b44440d0012401c68107490008050700440746040001103850020000f0980c0c10314000040d45000a90401c0a00d1a06000f011204504071801352040282d520947c0703090b4801c401000c0000d00000004c1c40c42d079108030400942d0300c540c0c98500302200c842c0a4031450703 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 973313938 1250 973312688 973312733
    0x1404090f02030f0606090c0f030c030702011d01020d0b0103090b0a05071205090a1202010e0606090901061d01050f100503130f06090b101e1406070213200909040609 72
    0x3500c3d200440d140d44141c0007910044050740f03c629a842051040d451140c1ea8a14144081404103415a0055030801e16501c0089030343e00ba5080d40d020210000305a8501c160341c0062550303000031107401000260402401c041003c410280c4402d6210076004210003800c0e0390300c00020b449107028203440050500b03c60b5007084507140000780305540349001e0809841110700800d2040c94144140200f80d0f2090309900079100340e031940c2c02804110340e005000e8203107954803017001007501035006440410000c1101e180d140154034010030720501c103446035245401000020b155901050f081021207400144003040c80b92010060704201c0d1508254a800034400d0b81404858400c0c480300d010014050b066415054200316650b50780f100390141140590499440d260301c04028806121780c2d103102906014101c0d500d081507560018039100312502d5800c40199a0310a40845d10262095202d07000455104152a0908090024048210082c802011140c46144040401c003540440b1020b10301c00c00701 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 973315188 1250 973313938 973313953
    0x1f061e170c0901080c03040809090402010516030201050a06170a17070f0b0f06010f09120503040e010803030a061d0105040e070b040803070201120c0c030507080408060705070510061404090f0203 85
    0x44040e019441402d0441c001001540400d82c80300094003113a020b1507118001a01c0c0c9001c0c401440103000000708264103101091007007184912204c03c1e80c4402c3e61084d80006803e1800100034000c8034215044201004030b03883e01c0400e000d0300000c4c260b900941101c0c6c0b5265080c80c22001d0889403082100040c0443d85068014003044206c03070055004480d842042c1032541d030303004011640c208405400b000003c02482c4200170503070480302e550b101c4502410170f0340e18090316072055088448080c3d0100700c01d548000300304009004980705040180010340e40d2110004003600621364440d10601030140302c0d541d0380102d86410503003004410001c01400340304070346a564422240b602d035080010103a000c2410450b041c1011400c51081031400e0050340c80302c841781d0700541c804685a8215000c00c44260030200400714140c28100079640c4140b00c1035440c0c43d0f6030031152505a040c40340d8a5020200182415070600c010181c280e00c0c1480001d05440000b400780700f5082824000c0d91b00e100c041d405005500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 973316438 1250 973315188 973315201
    0x40c0801090b12060a0e120328020301030506011a0c0609100f060f1509080f07150e010c030f1404030605010306050106092411030c061f061e17 63
    0x401940c100d503036901c020414003482d40c05000100210200c10460307a08203c0018484050540c05142042d02080844502640d0ba0003100c005501c03e55484000326141407502c44c42400704840b141c080c29200c5070642c1194510b40e030702c076030392030041c021001000c0b181110240240241c0d002e48180400c810300701c03203490512140c01501c0700c1801915101503420700280d540745407041d00482e800c440e20040d81031546460002500c000c0408240b040341040001e1500044101003001000150311011000d0400946801502031a0340e40001d850700c01d100103035940214070381c0c00035461611580c05d41000725030101c1101040b40c050155100045510401107400320501203268007032410303644900410400381c1d80f11030703080d607450b9120301c40d20207168101c0501e641400300d82c1ca00955080b0341350405c07000c59003c50450b84d00703540002d01e2a5130654000e03000c202e14281d0050405850904d00c00d07a600142d418504010862030140b2802901c06045540c0304c031049215410701860b5403400e40f034401c128140b55 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 973317688 1250 973316438 973316447
    0x171e1f0e130206181c170702062101060210050112020108190e060402030709020c03030c09040207140102090a05040506060405091509040302071403010b222a030509030f0a120b040c 79
    0x6100007402080490a10b041c504991001c115031a60003c4100111b00d122a5500c0768a40c0901012600300300f050124482c1c02d071800b00c00548070000b444070065551704090b07000385068043d00710b44c44442c1c14180100601131039145412100340d028a030100c4543e80d0082112a020f00d0038482c0d0f00114504030411042c1c50012440c140200c0c1b080b01038500d00380d603d01c000c006a001e00e44541403030380c0041003c124112000001422001000740c005410040d82e41c03542020102072602d91303041039400103401012032400b01d00800140038222020009401c100020030058002d60003080e0280d4141c101086801c00540305051700b448008100a40b01d1811346070081d00c41d8814441c44800d032000381d4514141c0d140601601610079000b810512003618011041510004034400c402c40144c0c1e640148612000214001500321801c00d41d0b00714503e1b04494001c00300c80b00207081c582103400a200c0032401d25080011542009428544060010003001d1064000c00001030700903802403502118400c0b540c0c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 973318938 1250 973317688 973317727
    0x12020103110c0c01170f011716030c0e100e0c0706020d0c0203090a06091401030b0f04090c05100809060402060c070e010f090506030307031e171e1f0e130206 69
    0xaa0b1014005d9000380c650740e040020550f078140990106000601030803441c0d26080083c1c100040844407041030710b00c804d41d0036441641060394503201081061004007200d4403680c3c0c1102e1031448420089240c520100c0c0d0301d450241c0744128080001440d01d0034460260140d8861803003040b4100003030a65124060f41c0d82d4843c0000a0041820314030008134540210307890401c076100006117858072000880110000c1142d011440d82c880021440c48075151034620409481c5031055200200306801d04082041401010340c441c810805100308201c80d184020852581060b4140c404980f04d410104030b0500305007440c3c02402c00c0390a0007000280208000441c9030485800e80c4003040b0903201c00090503140d104042e40034000c2240744c0c0c00c400240382019200340c0848224646110b010500708840755107000c058031007425120243c40c10640100c00c01e0f00580d007011143d540e01c041d41e00c1548000c01c04c812984148031204154900080c030300c56540030b4201c40194020100380da101504262828075010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 973320188 1250 973318938 973318963
    0xa030b0901091a100b070c090c0210110f1b1903030516110d08190603031e2a020307030206120403080105030303190f02090411041409040c12020103110c 67
    0xf0894111200503001078000b0b004055026541140900b0411104141e6010311012122030f00c00c0c01c0c0c0011091a9031003103a181c150303d580034000000d4140480b400750f4142d041a52a03140041002038230b448108030449007030f000c42d450044880b21800c0002ca00384030481070000d258030110703952102015855401303244100c80b000ca16074125206d1105c110380207241c04403000d046920a01d04241168007481019a002d0395120208082c0695001c100c0151005a80b045000c0307151500d840f614090f5814001d0b0b040500b43c5010224007041e0381c1d5030441d03200007000f00c1c0c0030490b01a440000355281031019101030341c2c001d01010f5480d00c54002070f0f000c21904403010350004c2c214030008216840d002c011203010b00e5008050041c102140b100242c001c0c640c441091592039800c0000c66600e031a94090800800302003000c40e51110301c0d005a4a107100d601a24140c401c0030756208000015231081d200d41d00f038034659001046000b080e840160000d00304859070900016002c91030070481000041c000c0010b22 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 973321438 1250 973320188 973320203
    0x12010606200705010c080306030a1410050c032701020403060203010f091d0309010f0e0d0f2001050d050604090215041502060f01120503130e010f05030d14090a030b090109 75
    0x191034481c0c40c0c1c0c965469014090000f46041c0300e5201007160f02c00a590410402030a8030b0303041c4140e40d90b0000341c1480c1701c1e10010bd90803801c1c2810b8521407512901f544810058405455403910003d82d4190101d8511504d100082c0c3d10101c00c030b242d400354140c030b010b50b5101c402156696140c480b40c44401859100f0400c209040c8010000c0e900c7c2c1880c0d40c0c2c40c1545007040154100102c0c14010b42d0287d407803200403030030828400d01d0a1119904c030381424005500450511200d40d050341808400c00104c08844264015003694801c00d41c0d038420121901b1176100000084d9540310300e400513024001c2150060b5102546540010303001000800900842d10200c06c911300481c25107034140d03140c400458802c902c0809100041203a20740c4400030b1400c240c0301d4401d5a01c2c1c0301c21000e4400e441080390301301e505034031101d50052140b12030041482c405020101c0041840740440c010041c42c40200104090307103518041041d0001e504c0c1c10f40d07290040d5a01845040213071400402e41c41c0209107000060718840d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 973322688 1250 973321438 973321487
    0x3020406090207020307230d1103070609030c05101e0e0f1005120604020f07110a120827100201050406050f01030f0f11130b2103040e0612010606 64
    0x1001c0c400c6480325a13002d406000d80c6450411464041e90001a41400c0b00c203006103071007001d90b100d140500105100c2c05d010f40d6403820b901d007410301d003e03195045070b002d0248031882440492001d0001d030b02240c82c2262005c4041c641901304581c900c01c80c0400e0074000c100048910550354000c0d054219859050f507a4000c588075001c10485803088040c407000108000300403c0540d03c0d80051034581c80000501302500d0b0030000c010560707180d4003c0d1000e80f1660346c040750b007840510300300100038000c003052000741440f14255140c070500741c45480b0b1180c4800e10100e0000c0d840005203012004100070040052100c00900100a0701800040f00d040f00c4152070311000540c2e01d1301d02c19a40307050342e400100401000140d50317240d80010040042c145d45043c0c80d588201e03e103030303252402c940311010095004a1000c50358014002c980d01120462422802e03a00ca015507404d4002040c1c600701c2d8031141e805849070b2184070126000d4a130005400c07010354248031000c42c0042d00401d4024a0032548040c007040c6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 973323938 1250 973322688 973322699
    0x7050d05030601051c0e0321010e040b0601030213030b18010f0c09031712040c06030f09020310200f09030601060f230c0a1514041e2a03020406 63
    0x90307101c2203407640c0c00f068040c0100310310300044800c004040b081a000005100c5180c0d0811450341d0400c21150140280710140f080c100e0005010ba031340103018481180d1040e041565410f010400c0c0181020304051740400c062094442d034400d80402180c001c000308401c0d042011070b07540540008042d0302450b44c01c2001880034403819102d01c50540e0561b90340c030034180d41541d58210401c068141e9203108880140301e83d00c14050390a4003140140d00c1451816034240c80c1007009410703200134401500382c8900e842d42100260f10003003003080c460300001c031000070040c0b900c3c0806180c4500115281d0f0076400089a541084070904000b0400651700301d0849055a0b6100411208000c4c80c245800000b0443c1c401c001c5240000405060315517042d14800e41403184d10461940340410b1002c00340c504142c120000d41480000340b08807000c010031041080520718041d1103801d00d601409501000c8400d2a150758001e0200d551032000541c0b0007080810500c000c4201c4004885d42d0f580070907803040c0e2030300400150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 973325188 1250 973323938 973323947
    0xf0d060507111b1908030f13140d1202010e03030f1b03071409010507050f060f2d070c0c0303030b0f09091b0418030201051f06231e07050d 61
    0x2400c01c0103d8070411060b510030500105141001d4000030031442d0b0600440e01320810301c0a041422844209142c5544850b51405400c1c4401e0340409402c410140101040740ca03400d41540074107421824412182110444c100c3c01020401003c5e0081c0c003022040c03200d444242d1103480d004403010350102130100021240d543c0240310544140c40462607582d81c0e4503400e0444005001814014149903040c0324850b00c3e41418040c011020025580002c0200200c03403041c00600e0b500a80098030b5040103140e00c1903c001d4002511445034210003404002510103807141c10325000c1d456000412008490340d9140140181002200081c4a200d07803810182c060b0425542a9104060f10b000070003400c00d070b84020741c4800200f6040e082c0c11030780701c0040400340841005203a00c00c52095000060a03d40600c408021035a0848542441800d16008210885d40311800280070492030000c030102140d441e0b14110306106692404903040540d8061020305001040a01041030040c0180c0b00203024408080300c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 973326438 1250 973325188 973325203
    0x1810290a270c0806102d030212010b04180b031006080709060b03040309060804030e09070210150e061009051807081812090a031406011502060609070e0f0d06050711 72
    0x9401410300c00e54105c13030600c0b543c020f00ba0107058500c0242d08400034140310761001d42e00d8240c00c0120360000750f201c400540c40180f4034011300c001e0245904107801c05c14140800e03c0d9090140c11090345411054115030380074882c006890121240402640e44e2b10300026840307880900c151001c0d145040c0c0005a00d44242040ba48a81e42c03654400319850b013041c20581e510400580300380c003000511005100c0b16100c80e510301c0e0051501c1d4009060464400c4c17016020b803607074610000c80d01c07051050b0802851203e00704054000c407040b43c0da40300c840c0058404507669079195000b19070181021120106183c1d04401c0680070740300b0b507a540c854a0341d5151440c40c01c8550707008240c0386503101c1c0c81c112641c160b0f80320144c030b60b0400042002400c0307030752134a400306030340d62400b00c5140e03a80000c00100608008440c2d201e15070402400502000d250010004400e031720028102c40c10300c81048000e503295922100000748229005109009136826030901200610b4110780c42000703d084c0f603160001c0b83c2000164013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 973327688 1250 973326438 973326451
    0xa140724020702011b081e0316090b070b1b07111513182315270408040302060310170a0b130503040503061810290a270c08 54
    0x105c1d040300c0e00d1522100d942091030000e0760800d0b42800448114980400c000f03a087e004200003d032203052100320290900300e100903c0e018410400000c000c5a10f40c0c00680703910540009508030203a45ea2405550311412401e0606900d081c0001c1c090100300910428030304290003640c4000c400d5515659031b0b000d91250b815490382d01501d0388000c0142414401001c5035440b068400824010000c200a030440703445020a0300e81420074100700101a40b80990304032411004035030302a109040c4955501102d071840d818030707104022103c00102440710310000c0700d004580c0940f06e00d6030703441d00005002c207481e214000c180b07514001403c03206c1ca24a0005075039000703070b03007000302000c00e07440e241012541240380d1882143c0381d00060000103160b5509000d038601c111040780f450010741056241044c10318407405121996a0b150030200b114811550407084001151b184203400e803485020001040b1680382e5100ca030010504070003140080020402c04100045030b454180140600013034291842c0000700c03000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 973328938 1250 973327688 973327697
    0x11091312050f0d1e06120204051605251a070905010e0303040603150b0408071a13120c2706150203030705070c0f0608090606090f0105060a14072402070201 68
    0x11986011140d07201d201c07030520749000c0013080401110128185d0312941e01520049094250400640c1043d02485511400382d0f400769015800301c0700003911501841c00001104904641c624002c002c01c24010380751190002123a0070503400011080503000421200b001c0040c0b80c4100026155000b20341c010743d280001800b40d03042c981020422402031072844401c0400c010102400070700b0008140c01000074041c4080a4000035041a0007190080b0106800b441801000c201450030903030042c80003c1620319105c5000c200c2850f9041c0f1803c09c2d6266002100a203100e185101c03020802c100f17619450582c1e2074030a1054a940d4050144828100200480960401c000040000d84a107000f0440b2030321a00d40c0003000350f103680780f0f40701070b103a160442c83c04107450a0034010340031420059558807030011661103e491400482003404900188501381c01090089103000c11103000741c6007400a0054500340f9030311a415814800c084420b1a9441c40d201060510003030044a0240225518650103854 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 973330188 1250 973328938 973328947
    0x309030a080405100816271d0c070c050f01020a061b0906020f03120c1309090605091915020c12040e01080607080705070f08210a1406090411091312050f 67
    0x401e41f50400c103600c51607001c05a400361422008907515580d000782400040b40070321081190000c54aa40024010520800041c05444002010382c0e440205490040d40d003c4260a09000180c3c0f4101d60300348014066030501d07080d074100c5842e040040307a0042c8155103010324156103c000b0703600c505032035460000300d40007040380006100d81e80301030702c1d0488481000c2c03a1502a50184586100350142c000f420341c5502d416183c0240315041c01010b401900c040060b001080c0446814151081c14280040015a14802d252200b5000740d05540b0740068002c00c0c0c601e01c0c11804190091584a8080c540c1c11342d100800200d18004d00061403881030742103850300011900d0b01e810070f85294000f850308827409904500031000190070744014100c880380090a00c070348454460222a800358008044082c0d403440d001c514000e91503800701c195007001e030075106040682c8890a1030f8408001c0440c0554202d040d200601000e00035013408114000e010300400003007103901c1da0040720710340304540c4019283e801c18031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 973331438 1250 973330188 973330231
    0x102071202031b06070503040b090a05040b091b0c0a050304091d0a0b10170102130603021306050d0e0f0303100807030c1707080d020d090e0c0f0307020309030a0804051008 75
    0x40f5030096084000346018103258140c0e442d5072541e80641c0250510381e1740460140310b0350401c150300da00904000c40f01802f5058240d4045071a4102c000c000c0c0b144040301c141e0802c180c810342c03070460346c5d004044000d5072165141350800b80d40d00c0d44240701e80d8139607507c1c0c8520320a00c806901e04000c805020f0300007034801500d10340c580f5034110b040544081c84182144000080b110ba0110070141c410074020005611001d07001d542801003002984507509150041213801e4200711a08400e41c00e41d0b0080c01c1c4a0745507400048410003c125806040034a803061101301d903207042c00000654401ea200c490441c0714191600041034403441c8603c8000d11a0803464410b0110403644000c0070604051601190b015559910006240c03281880da03010140c2c0040315208203c6030701a02d0800070303140384090840e081c140881810f18512a00d00c080c609004040040b4850710f10070b100303d6440d40c400070f04403002d21025042480a907807041c440e0310720800352030950441090040581a03c100303081b0401485001d40c2c036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 973332688 1250 973331438 973331473
    0x705060307021005040b0106020f0a0b0a1e050106020c1201060501080103080313050d050c070911042d03031e080f0609062101020a0207121e0c12060902010207120203 73
    0xd890700056000310004030302854640d1140c144142c0c0164400d81d09035240030304c00303400c01034000001030a60308000c507041e02107202e00e1100758201242102c00a00720080350f40300b041c9100e90541c4090540d0810000042ca194001100d005200f07045400b02002c1c502d080d01d4500b03c40b00740c0b044502003000003004101140c0040e01940c0c1c050214500c10300200c0703142e5101c0e03080800101c025008a0800b14034005501d000300b0004008c3d140c3c25004029400080c200c11119005502c20318400d99410b10032202200f0300d552a0f44202d20841c080f0b59100c81d264580688038000d402d0102085010750054600c200b8070801640d80640701c1988071034020744501b8240000364030000c044176048100030300801c2d003c0200d40c400c640d01030244000143c852072000070080c14a20160712101c0310310701c0300141a01141c2c811120a1001d0407036190503000c100d00b4600551049410b5000041200c0c51505043c18001c5540001070918800d0382034410346910303000c1c0e243d0086500440030307400d0fa110580d00442c00742103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 973333938 1250 973332688 973332691
    0x1051315090f0f061a030c03150c1b06010503010b0603060d06050603011506030f0c090303021c0207090e0a03170106230708030702030d05330a0b0406171807050603 72
    0x4050862031a4a552180c414102008000701c44c00c0b0360382d5030020004004504606603241085016168802e40200082c2d038954051300c800012594480200c1c41400044085924030059400d03043c140c10031600d4469215002442024020350030110466418601001201d108102c010b140b2900741f0202d03120040100001030038113806660700d142560707140003401403210080000d40e8021400840c5506010241d82184008005109074501b0600c002a00802c0e1280040700004041d4000c0050f108201d24203aa142d1003090001d1a00b844100642408103001242601a4503107030086111080c01c4500e03508240b00e44400a014140d60354109a4401440c210b4050049045428400381c3e4481c0c51456000360750300c1000d6400000c440c400514580035003035221340d04803411b50000c62142aa46480108403a90802220420030f0498a0341e076403070140406071660303c04a544568446601070643c01421600120b0030403100f0010381410740b4a1880e5407462700760005002a02e24100511010f07800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 973335188 1250 973333938 973333943
    0x712050d1d0109060e030a05040b160c15110f03031803040302060412171e0c190b1504060302060405060705120c1c0c02010806330901020105131509 65
    0x40740c2085400328141d0040e848062250034000141e092401e03c1c03d50200c8450740940a2140c20a01c42c41d2985600007045c2e80440d140e40700050780c0c0c2c17008202184041101d1000003860300701449004540714402c0380d45034860308180c1c2c4075a141c00c0d405605456550f03900d0031001c10315900070400030380004a907203001a0428000401c0301d003400d03101d500180e201d4225801c881c1c2c07038034211655207080c0581c00c6005800c044210350801d29041034400c102034420f0100d0075030482e4283c006964100460100051500500700c900e021600c040a450898101c2100351450202d4444241c03296641b0304e858419441225801040235140034030700030501c14103400a102c15036050003100042400c03a000744004003142000180645030740e9403223625040b41009900080c0d8200a01c6100160050340c108212641141c0120307a0300d0204101819912015030780040071b044000b42c0402440300381122100608400f0800740c00901a5640e28410304803808245840a011002c40c002c000c1c0e10101240d02c42183d031030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 973336438 1250 973335188 973335191
    0x9040b04080d11040b1809100603021605010f090204051b04032604060203040f120b0a0e25050a06080603060a02030a0b0a0308070218010506120606131502120712050d 73
    0x1d90024a001e1341c00c0341c0e20032811880006013a90450142414050f040d040448003001d03d0300740300c840d10700000d4090285070241030f030000d0003e5504c0b034030f550400c0101c2c0d40304000b40180c0301540c00c0381020305a0000c04134003550810380490022907404407c0e85400059000c0e80341841c0c80c0d40c5031a03040c00c1a03a0420200d4030980142040b01402c500c0007031020f008150000e59850b0301d8050701ca00b113003800c1d41c45101c003d01c0104810f000140081c8481d07801034800d410200d040512100e80508003c203140c0c50011140702c1d034510b40524070b180c0d40d5000071160308480c0ca110481e40e6140c25504e00004407600b0340e040c0c020100140c6050038075070155402464020b40040c00100310740214400f402c00f50415504a00f01081600442c540120324240514100e810780065502d080c0c0440c00c2805401c00c0d00c00f4030032a907000601c4d162241426191010301340246c0544007071380c0b070740c2803248010521044030043c0103031526070790800341d0801110a190380c070041c155000315103c00102e800740c1141d0544038805 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 973337688 1250 973336438 973336451
    0x1104080d120608030d15030512030f0907050f0d0615060309110f150a030603080d1d0f070b0f0d1a03060a1109040c020c100f02010b19141c05071409040b04080d 70
    0x23580410000b210341a030132584641d40d080000d5107402156004241112541c8824414026a1a00d030a5000381c40010758509194404914020000c0c04807026444452400c3c9107001a071164190001a1001c2c0508212089194001d0a00c49034403c0d0440c0340d42c1007011104014503526144000741440082803a0000c1c0301038583c2e071001c0302940003500e20140252501c00c0c5000a40904090f409001040e030020a105524445065145c40e404e110b40ca01020001c00c03000344001c0182e0032114140198042000b807581d005c82e60383d000440801100d40244124000501d120502c1d1207000d1020036400c0c0103d00340240ad0003084050100d44030006e0440c09108036820050b02c034020217556650454031030f01400e0075401002400c4034100f60700c05116810200e002040419034400c984146d89110044580081e140c0c030204100f8800704000c805850f90105200040c858042401400e40c1e400f04231843c40f00c01c100381000040c0c0b400f40d9000e40181d941d007001c540001c40440c02007800040d500408a0030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 973338938 1250 973337688 973337693
    0x30203070b49050907210614060a090b0a0e07020705040204080d03110a091206090b131101020c01140a050f0f0304020907030501031a06030c030a0615060203040e191104080d120608030d1503 83
    0x1956202386002d4100e1403248144034140c940b0b041c032038014019921042090140802c009841600244030360b20031701c00a00007090a180c4280302c6100605400752003550340f20364600b5400d9a0354826076404000070301d40203202440d0130100044503080e00c029541d26000c0f505180800f29140e800c0c000495207182c1c0c90581200003000824520711440310454411182d2030b1500786031450690010000d0304541000100d42c0940e0380140551052100d100800d176241c2c00c1c0c00700107035002d100d0304409580781e00300480d08d0210351801c240203500c035a1013074039601c9998407001e030f05505449080c04014040c0024040c2c2d403d4038100b0009042c1e00560080480e4050144000805c0c10700355000d60540d021900d44494164807c1000c015000410651004514044c07401e20b40c0c0b0500203000d40351281c0840b40400c13100f110070454020400a1503c2d600d4a56107030368400f01e05950b0000440e0185c0840c50884d40c44460ba400c80c03040718200e0301240302451034032031801e00310b00c0200302002e15581ca6401c100307000f00c007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 973340188 1250 973338938 973338941
    0x9020913020414160c020d08040e0a0b1c0809030a0c0f090b060c0d08090a06110c0f07290d0f06030b0907030203070b490509072106 58
    0x2108011948914041180148426503003603103c80c1d0144140e290034000e8050b484c440011102030149840550000c0510002d04112a000005400e4500110b8041114040502c0b03c038046d650141c420801d08401000384800c204d441c44401c460061801c00020100328080c0040044540080581d4007419a682e25000300c24241d401141007540e01600a04c20400607200798004548200d0306941402e0500c1440c903a2550048050403c0015007008542d00c1e81c001c1141c3c111080e806502071024603540c85150b0b20780d070404441c2c1c0c680da00c101c2c440d405034540082014020348040f03d100c0302240e8030004e6414032910307021f005c0c02410a03040021903070001c86442501d194200460012980f2851810000c00c1100050300e09851350700300e14001c00c0180ea0029540c0c0c1140e04541782c01d52035412200c1a22000017002c500036101085010745030210b100320404c0d102d85030f21020719044010250088407401c40c0c5049130100300c03d5100340014040d0b450003000241858040b80c00302d81003615569910780 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 973341438 1250 973340188 973340191
    0x7060f020c010f0608240a09021c060b04180c2105010e0c0a0b03090a320604050607180902070c0b0a08150d0210030c03061d0402120c0a03060f090209 66
    0x83c0031507502c0000f0f21941006220701160820f0611403e015200c40e060b01040001d000361900e8100e0f5642d6403850b0464585215400c2440114000760720000903034200711001e4850080700074466450b02460300c1c2840951003540e03c04c560060040a0120b06140c0c180340c410346d00042841c1207500c10007041c00012030074060160303052101006001c0300c0b201d0901f8403950002540148030302840034000c100e080303000001c015240f103400c840e09030307034140c5038641c0c0040c000c000c3d0390b80c80c481342d0520b41c03084072614001035480e0040c6e10030310480d11207a0b0342c4402142c00c00031140c0100160b0104100c10840030146401900c5043d005605500e001646c0d000ea2080d55440b500c015070100d1070382020880007850101252800130342c155840303441111a603000a02480f0000b0149c001d1559442c07c0c2070113288a58802e9020f0310002e0100d000703c10820100303424466040b01d00f240b040b400c10074500c6843d900820800384030314001d0082d40c1c100c2e045641d0700001e441c192481c02e1205030b0702e09802001d41e86808255 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 973342688 1250 973341438 973341461
    0x6040b100807091418150a0b040e0610230d0203100c080912040e04020603042a180204081531032c060d1e021b1207060f020c01 56
    0x101c1d01d44001d031380b03064040001d0660705032406040241c1d410300e0001c1400340c0211900044c0e039160303070b0390300340d0303040081c204451400d07002440e15920000003000094000d00034009080c241c2c44242e075400605c400b4072520113002c08900d911940740042030a10082c608041c0c2e2008094880004070200003404880c02d0100b43c0001401c0d103001c0c8034500d001801101e4070010b1340b0b600c0030b14080c02c0503100e45070b581c00544002c1c00b5100c000300050a00c56120343d400044901e40b1040c914081c0c15002102c183e2400d40030302d0541c203002508451041060f4030889040710810303001313003461a00200703ca51402d1401858030035003403180c0c2c2c040803c0c0544100040d041034000042e0f4540c01358a403e00512002d02c80848038008013019000542038041041101c1c0d1452040f01c15944d11400d80a0f8207000e0710020f200804051201200710030310074440d8000c0c00c954002425910a80301842400d2070b40e54144500e954582c21080080c10007140007a0041c0311003114200c805407501001c142138500b1034552003000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 973343938 1250 973342688 973342691
    0x3050114063a05030a09060207050915030c04060b04090b040614010c020102030c0d030c0e010305100e150a0f0e090a0c1a160f060f200d0917091c030206040b10080709 73
    0x201c5401c103400044100140c5280c8c40103088007418840403c655480140c981c2c103c45107403503092400d030740d801c01120010110240050160310760364402c40e20320b40c015004036107900c1c0c02c0c2082d4104a080c0382c4158022079409015040c3d00c518180015520382482d58020f904601040105407100c403030801c00d444010609640018100d4117150b4010022440c1c1042141010305100a1084240030030100b40240c440303403046400070341c507903201c1444026101c034029034104041900000d00100c10340030b054211a400d208030451a6248100e4030b0f102c01030200000d0210103000350074401500b03483c10302e141009141d10f00d035190607259054424055550b1800b10398a55000b030100b001c2000500894200c41507991081c40441a010328245c60005081025250a01c011a0040140144e5004040625040702d440e405030f18071034070641100d6000e56a0640290207286261100c108800550100160580d000e8081a115a9a000c60020014001440702840c1090208584006000c04401842d0740c520 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 973345188 1250 973343938 973343947
    0x1050405060c0c0120030711130f020c070b040b0a080c071401050601110c0d140a06050718060905010c1e0b150102011a01080c0304060e031303050114063a0503 70
    0x40c00700c040240c20803040e141c2e4076450001050004182c820f61035008044c01c03c9600360401291001d01050703e01d2745e0075800e203150321084910039802045000070100943d940141c4035a0140306510880c480d0038103891040001440303070b0b84500d00300b580010130810740516050345c58450030701c0d050315a0203c004503555402402b000303680241030b13003000c000181c018103107030005840000e0201c6000400a070980700e50010016500d032042c018040721721b034003100030000d60030440c4000b0031a181102c14803c483e0308003007000c58607a000d07500744400c660313050350345418680041d82c1e20341c00392900081d0203200300003850311600018140c51105208141c01403140c55890000c000090a6440c0800600034030304090035014644e03680020380c1644a580215403a80c1ca4580385004001400e10031051503e0f03000108004882c0d840d50070000046034043c00091240942101d14130a0070b5400b540ea02d40d1004241c41c60160030448501d40001201260101d80615000c012400c0b19030701b6103005c1100c00c1e810014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 973346438 1250 973345188 973345213
    0x60b0a0f03060e0106030c0e0604090504021003020f0a05090f040c120f02090a12020d050a0b04020117061f030e160317040305030904020d2309010b101d01050405060c 73
    0x40d524550300c040c0303018404203180805069950206001320b404040d140e40414000d9402440100d0400c1009054aa0b40e00d03a148040340041000f80c03802c074800c0f42d001000a0b0181e00c640240c5081c0041001c00078a0450340c200140c81ea54401108160003510b03034000000c1d96030799841407110340c2d03580c2d4444100002018058900729a902c0546641e102d206000b50303541c80c0c803a01e11038802e40d0121442c01326100d815000103801c5c4142c00078010158486c5000380c20810880c03202007802280300381ca0b0104011428448028464022144d43e41c02c60a5690003001d0a5041d40c500e003955460340c01c000950141400616042210440bc2903002125038103041042009480300d01d04200962420035043c1402c6130b0340c6c0c3c0d49030f20410508502c600c0d00420b0351034000d802580a0521031890700b031501c040c1910145603d0f00e000c001ca96580300e0b5440c0c82501001402c007880d030140940f42658402845000e04903103018003501c0da90b13489040082c144004121601d840005144132107191b07000306060304092 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 973347688 1250 973346438 973346447
    0x3120e0a0504180f020a050303070c05010e0108220320010e0c10050706020c1e0c03060901180b0c04090501180e0a150e0a020622080309150319060b0a 66
    0x552005000e1031401c11541018010400008106503010b01c903844484013a000161000042e07402c1154107003c00900402040701c181c6130038003142c200381c0740c0401c41c421150040d900e110007201c070700d0085a041c0da51680564460f20050f41040d20a00b4844076860f000c201d28079401040500b005401c0e0766400030003c07490010003803a44400341c1202d002c680041244001041401803080060000703401041c0428220010b000140c01249410484040c10044001e000e0b038628070010114007a004002c08140e8a40040c0a03001011092000c101c00b00c114a94802c4e02c00c0500411049101000384404a240412801194020104d00300c0034840c1d0b6040070301e12021103200403601901c1d41d0080840400240714000741c0e400c4140c03540f8000501d009407a42c05401c100310940c0080d803200c4c3c005a9000201e0050004070088101007e88200064403115410350741d1040b0065070b60311801460f41002407804110003580c0c402d100011350011041203401030400d841c4190060416103202144c0801c0c03082d0700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 973348938 1250 973347688 973347709
    0x11030105101103270a24030f020d06050f0d0803070c0821090d050c100e1c180803040803070f0320072414160b01080c040c0f05030a09020a03120e 64
    0x110703105c0c2e6010f0314003c1d081074254501c1002840340e0344100c05440c0054000d41c450040617102c45400d41d03503104003a9000000740454050103200c0c800d000316201c60350401c4402e1005a5611500c558550b454454060380d0715064000120354201080042e0500d500d5003c2c03c450481d04a01d04000450401000f264100b1a895404004111080c0b0468080c40c80c001a0b80d11801c40e04c0c100090130b8103481d10814180210034020300c40f140ca40202c0c00a12507802505001c4152901c00c48803403494844000700e44034429842000c802d54000c2c010540826520104164028860304152094082100c0c4040703c056120f05010300c00d4014010030000075240300182d55031241901104540c00d000030030040c0c0a101c000342040c80031013012492120b00f000440402405e0f5412810303400d903540c0e641c0891941c840d4510201c0d80958140107980707841c00d00510721880501016100c45003140d403038484a0000304400c10044c0d0780540221000000b14804103040700b03960030169164008859042c0900c00080c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 973350188 1250 973348938 973349017
    0x5010501060f0c120e04020f181e0d140123041109070507061a030a050f120708070813030b091e0606031f0b040e030c1011030105101103 60
    0x10761400f1807002030014010026441e4090600c4c1d07070030342c1c1e0302c0000c10001e00034940e034000e41c102c0020748000300b0514841ca080d0f1010048a81c5511034894040000d02905071040d1150810040b00d0701c0e10000e01c01c00202200c04801c13a00018400c0f6404a107603500c03410100001521201a0082c04244106089000e071910000e4801c50316501704400010a14440c0344005082c1a640380001f000d4004118410880c50f0b40c02800c41d151882c1500306551291081d2003030410501c50004611400411f202c1580e19180c0c000b41d00c3c034240403294030380404a61101c5030301e40c0788211040300400091507100095004410702e200038107410014054074040d0b80c00c046001940c550140f0200411a54001148045120101503880b072181459150744068505502c0c082d40c0181046e4a6010b03038400000580f190382c908000726980d00d90540d8100c0100e402c810f019a14807181007005100354200748004100c00034491400405070b2030640081030864000e20b1405580081c4048008032031031104c503068a4204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 973351438 1250 973350188 973350197
    0x3031611040c09090507090e0c0d1a0a050105070809100504080d0215070e120a1a1605040603020f071403030702100e06010608060604090e0309010816090e060406090905010501060f 79
    0x70b60b4040a0b080e00032521030a00c6098403100051829849621144000c24040410009604103034079090002d4015070820341e4030a140c03500020751040e041d400d110030884041d05602055003407030700444160307020040071340f200300041201403226194a0318410040c002655060744441c1044001030500004001700011544260002e800c2c402c00c4001c1c20750040c0311401c010340d441d042140402e46105c0d004000c1c08007405064143d0041c030a10000b9015070513951461003c540d940d103882020a402c40c40b46a10018500740001d20446010b0342c0207104207150801c96905082c0180c0c0c4009100b5085200003903a40c2000c4240011603130100030f80090314045000c144004640b01d4156507445205118840411805402150460300c0b050101c40c068081a0000d000715820020703020340c1d0b580f096000b00d00040603840050b1400c0307401e040c00b4004d0b4281c0e9a03001d2800c0e103003000c0d000c00c1c080c020308241d074415551040010604c0b2030348110440c55210b1ba0020a0a40c5032035405400e09813080640c00510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 973352688 1250 973351438 973351451
    0x40c0201140c1c090f050c0a14090a24030c0b0405010c0609020a0e0f010806064c0e0906040509060412020109020a060e030606030106080d0302030a0b0303161104 71
    0xc1c1d1801810701e5124440c48200d9440301c0e8406852080340303100c200e107402142d142c81000c5080c4003240da030426a00b40680304480003d0702c03c0741449114001842407860380759040101c0f01e1540392600c07502d60410680007000ca41d400c03030822490050900c21110403030704029113000708100100445500c0c0204040212941014038210018041043d0720100504c0a0b0356100b0080855840440c9000684070386409000545002c0301c50115028081c000c25101f44200c0c00010303030510386071507040c00030070010715a0150004400c42d03202c20a080150580c5080901e4800410362404c0b0075150800d520a43d030380d85100740d48160034008003241c003070f00040c000c2d07042008211144000291280e00903a00c51000041c80d48221412801030400d9840294400110341d00050000e0f8030114100c3d05680071015582940c80b814101400c980c1c16110712a40390700620200c0c0261030180c3e0155902c442008004100c51058800003030035075202d804503443c1c81150808000c140404111001c400712401d6408000a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 973353938 1250 973352688 973352711
    0xf030f0501050105090d1713031e0807140f0d0302040609080c030309010804110411040815070815030705090f0115030603030206010e06040f0509010203090115030c1a07051506040c0201 81
    0x81e01c84c1004142c081c0b81421000810018050160304454a500200a44541000803041e07900802d41c0300a07132b54690314540325a0300074a6544004c02d19540090358924241c000c1d41c8003c000c1c103d40d03401103180e001d2140306ca0f500c0d00b000c1c4010303981450b00c1c1d60010b0f540d03030901001611704245c68000b10300c50743c0004005583c42d20000708990742c0d20000d003807120082d500c525000f0384840c0016881500310f8141003c0c0316445000c180900181d80c0000151491090000c2c9015000f080071140200000c207250302280e2902001074900700c01c0c0340f0260a903803100d512007010841030101502d000c68000c0307011004104d0817140b02d807108142082450244030807455a00c00035540c15043c0140051030f546100401c00c1551203a120f01c40d11c0040710000d001519091000c5070003900211001c03601542403680e104c11343c0d0030121a800c240c0f94880740c034011007814108209104030800d618005242020001c1c000803540800500310403150308810301d041c0345496002e120590783c2d40543d107802d6a0521800004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 973355188 1250 973353938 973353947
    0x27040f0e0a06091b030c051e09040651080703082b06050901120506010e091f0504051204240513030602040f0506030c030a050619060f030f05010501 65
    0x103542008001c2244602401e000380001500c000d0b010103019880d07130020421002140000032507008403041c0c2c00e40c600d60307528401d071700c91900ca545501628040c005000501c8aa02c101030501e0100c6000544c0c00e4041d08120700e800013400d6002c0b9890912440c800c103e6006085c0d072081c180303a2410326041914018942d42c0c0e03400180230041c1490f00200d00c1038880b0310000700d0710341d0100e054a04400e0014a0940752001000140a04c03030094000c00300110380e2000c0e211a5420460380000107140703d80c60071a01d071258003400340106038030b4000e41851080030f045916804221035407554001a040c01c06103001843c0091150034101d2071007050004201080744108035103013442c0d00700400c2021900181c81244c19224a5400036410442044040240300696014206907803881c0d034521816030b102c1c020801180001c40720b40200c5c52040000807a0381e01642c1003241c1119000d40501c98540310700c1d40600c40071625400c02000aa605039010034800c0d4035000d08002c0c400b030a1700800265051600091 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 973356438 1250 973355188 973355203
    0x5070206030c0702180403050c010f060f170a021206150904080a080601020a050123132609060a1e0327141209100e030d08040827040f0e 60
    0x24500c00c0c086412015174581d1126a0a118204030201c0c00b146428034005d0300c00d4001212884156203800d85001d4200018400c64041d80c0200c0142414a442c00541143c011071904051549008605521005032200040c01c0c045813030000150000345011488418100050f41407039100340503400500c008070f9001c8049450079415842c107101155280d4006030700c0c0501c03003800140150700e00b80b10504c4040120001c50708d00303421061801c0540d01c400c00c0c3c81402e014601c202070103039541c4840c0c4540a4541030110710018800c000400c0c00c04130b902c40000c0741da400281c0210b000c246058885a00464504d6200d100301006080402080d0b14032a20500f6500345010811007080d10300c0c1e4190144000f100080304a0031406d8215408032010800e640003c1d00308910450107040301900e000302250064400811340b1502400030103a00342440d0040700c2281c6c4c05802030f21a80001c01000c20140303000140c100380700001c5564900f2401c620020b11044444448480c44180d00e8005692141c40000c920903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 973357688 1250 973356438 973356451
    0x152024010b09091e07020c01020d020a05060a151a03042306040312090c03231212071403041113020708092710060215070c2004090803040c060507020603 67
    0x2207010790f44c1800b904c031200d0503548401924201581013044a51b40002c490b030180c0800e03802c2e504514103e800130380e070311091681c00078036913085900001c2c0101d140380d0105140c0002c000010042503661040c02d001d08280010f100b240d1400001004180404401c02020801c135640010850b262041e180548404002e00010f0401106500d01080c1613001d400c00070f9001d8019094012896581c907000c410110800d0880b01d00c2c01200a000c9281000814064000c12404400500e8206601d030380d407002d2140100000c050081000404620b0102d43c00510b03c168400c034450040301070008108076142603483c4104401c0b41c010091480029a000d0507203501071001e0306c020a0400f844007241203d0580c614005894981907002c11803803111009000c41260500d40a40c1c0800002804400c1c03580b00c1210b43e400401e50780d90b1132100240c00c10aa103034915880d64070030301c80c00b0705050020b4144c905000d426103407140b020003840140002c13a04460020a0a42021807404030190f002c20454040200300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 973358938 1250 973357688 973357699
    0x105010605070228051903120e1008130b040506061509100311040302090c07030807030c0e1909021303021206070c08070807060c030e010b0a0609152024010b09 70
    0xf5595181111a2070380500301c02800c0007011201c94203a1706e04440c60344010360b010700c0351400c1c10b50b0312805024540300000d006401102611201e0900383e2715010082d00880c072a01c207000383c000103c0c0c2c80f0350541e80541e1080700a0012030038600108100402c02183d400450003007005542d00790f940d0513480c2c03155410030303080105100d4411071555400c0d00407544003130340119102c410080c1c6002c8034401840c5c0d0703c2c0b00351621315440d111880202d0490303461a1440300803800c501c1d0401c2451801c003c40e004406075441070f02488580b00c030700c450140e03042420880701c01e45901400740118940030400c0310356004450010f05035860106001000101e1204024001c440002292010f000061041310901e507007081052100c07500444c0b000740202482e40c03900c00c03e540703070082d04005440c1802c1c4d40b90072650550b4924040900740b00d100807a88161100450030b1042219a00220502c2a07100340d00350340c1650301030003c401c1d050807480212030030720718119150070706540140701500149040d43d040c45d0040e03d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 973360188 1250 973358938 973358989
    0x2070b1b0a051209010f110a24091220032203080711040605100f0806040212040f12021501030f020d1a0910090201020606120c0d0807030201050106050702 68
    0x12150801c4003000016000e402203d281d02444800c80b0002c010032002a1b03280b03050540802000ca4401c600304180d00c00c0390b00001d01396070128540b4600e050071000e40410714010381603954680c6040780d4116008a80c0105043c0c0300b03100b525000814800d6668016040e10104000c50701c10b10340f40c0c4180308a6602207070003283c0d162040445145c1a1014650002031185c2d83c0d0414200850003000c4016600e1107107050240118503401d081c07140f0b03c4442c1450700c0d030600505d0682c0b0103032450305001b080a0703000b503800d01200d038011010250190245002d401c0240ca644824200703071411007001c480d104155805500c0a103107041c01040c039281102d8100090041e00c500b00d1000460300341c6100400f820b462580840c100312031081d4040c240c080c5044404490341039840384440019035020a070041d01507009800080d516007410681020140100170590301201180d0000400b4121107040584d290500030a003c010150244286405040103041c504c1c2010210f0f80015094111006007601c1e00384002c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 973361438 1250 973360188 973360237
    0x90601081f1a03030c01060503010b100f0c210e030f030703020a03081b0408100617030702090a0e0703200d1203020c0106050405010602161505070209070c05120d0c02070b 75
    0x30b85161440c40c0040540707564200406000e40685040d0180ca0710951800001850501e080c0d10800c00a440c10346603490146100b05017559109503410b02030f50302c0048903102c0030400711a85540c00d5604065201c1b20b621440241c02d040c40c04d10860f09000d03541c0d00c1000b0402c00310340c00144042245500d85001a41c1c1d03a5405000d891491403c4035100358101c010402140c4248040b03407200c4008501e060420080c2c2c0d440c030f03603104500b05007460201c01c0d400030060380d800360800d5100c0a501c000c649201094691640481724a00075070341d401901c52651628a182c042c050b03000c400c1018050864400d0144281911703401103540600042e0b405059000820407800318081d00804000d04000700200b00c2583e40781c0e40a500c8008282c01c603282003050250104098420300700c3c800b40307200c06a441030b080103002d0b030912040c41e02c060940428000160360322130018000304016144041c1c10401641c9070310510106005560410b01c01100b0f540103502c0500292603620143c034641c24910606030b04407030414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 973362688 1250 973361438 973361471
    0x20a02191a1302210d140442090e0601050f0a02010b030f0c03072102060f0f0f07020a0905060d0210031104030804150203161712040506090601081f 65
    0x8880003500701204e030300c800c1d03d50140c1c500c2c0310500a03040d5050f0b905544011104460b240354459140400726810f000911010f40308030740c80100c903a00381580030059070f280d80480d800e140d040c00d41c4500c10344006080d1710117103500c0242d10b0001c2c2500d080701101c600b450700c0007038214092100e010701d104401040701400d00d4801d4021b41d440407805010344511041012050782c58000f40324140d80a40300b041400111000f001e03030440c510144400303c0040034100c0381c3c02c011682e400141030400003a4217000022080d0011001807800f08622940940e40b0032541c4184a01c004c166440068400c4ca0b000c100b000a0302e03031642540031141d046514510f40711048105500522500442406044002c1004802c00152400810685400703140d014030044042c4801c0341e407449088052a0411410400c0708000f44d01d04140d010155002e20b1046d0528003d41e00e0320b0f4080500b1541500e5a60020042c806032207428800ea0380941400350182c03016030146030244540e186251414a03003a0b949040408810940 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 973363938 1250 973362688 973362721
    0x619030602120f0c040f03152c19030c1704211401200711040c050909010f1a0d022101030309052e03060f060201020a02191a 55
    0x100c00e0441d1181c02690700a9280c0c078040359804000c08102010440d120780c0401520200d651400440301d0300c1e400c5944d014000400ea00c0c066001c20303100c4079281d10300b00c0c28125918105ca1507a10380044584541026440c11030080c54505000703072940900c00109900980d80111160052108075480d089185803001902c02c55001d40301c0100700e9102d003005105400c8107a600d041c040c2d6041c841c007030b44d08419a422030701ea4200240d030486207038003c41c110f50807000250900d0340c0111000381072400041e01150075034014210150005500242210051405142041c05052288164259203040a601170a04902d60584040340030011503491286407080d012503e546c1c0680c03507101b510440180e60901c3e0104280000c6010030f000c0c0308042050f0509070a43da03003a41d000c1040d25004203070001d401e001304c45554006810152181d5020030141003480d8100001c01c415400142d50f902c0711100203090a00304900d035494004003080c40c3c2c01240e507403c600c241c1d814040441224503107580410180d40b019 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 973365188 1250 973363938 973363943
    0x105070213051005040b03010203010e010302010f02030729070305070917070f0e061011030d0e0114010803040812180906060409060306060302210a110d0b0c0306040b1206061903 78
    0x600701000150300f40c2c5034000c3c080720401e0b2001e00442c0b61807420103090b404240a034009036414100104050743c03284140401000260042d42d103441900e480365000180305291144401440114403200142c041c02c1c0c1c50703401902450100450700300000010b100401511a8410301400845d509980210501c03001004010745003001c905180e686801186800048a44921030290101e80c02d40c0180188046507481c886034003d145428007808810b0020080040202e601703640c0c500c58042000e40304c9580c00c2c040e00c001c10095403074030b1070414100c0c5010311006038190034100501c00c0b20701d440800c0301c81c0182039900301c4d8500126500d80c00400c111f4050f5922034843c441c100b480010902105502c843c06030b9000703440c50701603441141d000d180e10381951203004038982e00100d170724008078400c1580490016401004007800c5203c585510750521010740701085101400018040140760901c290050110180d5074502114080c03414591912001401140902d210740307071880c0010141c3e8000c0c0081c0d607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 973366438 1250 973365188 973365191
    0x8091606051b0f0d0f080103030903200d0506090d0918110f0409140a0606080a0b01030e0d021507020a050715030b06310803091212031305190b060105070213 69
    0x814401100e1307620259a0b07084800304a4060000c13015520a0424034103030781d0180ca6103000c040c5580c1e2103c00340320142c0110540300202108a500b103980e5841210320080c003a030001d110300e04040400340e0918000d4030180040c032640080403c0b00702554110030205100401000a441c07100000302c0344103200d0a440d00080e40720001c1c01191000780c40d407082081d0ac111030761130030341941c1d00000001129200e00602c4c01103154140020312001e1250050010b4070030616000c500d1103501c2d456241f5044100e0404009a0055044c0700583c0c440002000d0f440b4500784002c02e002a0030382c4a444d16881c10b40a0440d2445018626810541c02900b1128602002820b01035482d6100c51041300d0a501601c0782d01090035141d146030b40760040003902c0302c06035040c80c4051858480201c0401c06c1040d100d103c42d000c0c5000300d007103610307080c50280301461003091018a510a0b40145141c01d6042601c21100c851800b040c0450b28000301d00084c1d000c50b440802803c0c01540c4035881d000048454441545840006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 973367688 1250 973366438 973366453
    0x120203130c0f0806070504050904120201200c012304230a030f18080304140117010e0405070b03040b060409030c020d0309180603050606010302030712020c010c08091606051b 76
    0x65451106031421182003c00f0b42c0c03c02c0c0c0303a60504640c644620701c120f660041c03010300807070041020340d0b2503030904108a000018250f00003250070a100950b50f1b034400342e101c0003c921040105020300402020320780403070601d45c541074280040703400400c2c00703000500b00f13a1003540034039140c0e55946600ba4150700c2010844002d00c0c0e040c0f40c004e0107a00d0214070030001070000e220741ca410300d64001e48001526481d1001d141014100358600180940124003035040105071648007007140418078115000e0040045000094a00703030800d1460040d86a1000c10b40303510400c1000045181109084e802c00070032503010440030920300302180d84081008002e0b61240c01d03403548104140d007081000c5d003194909802400c00407401c504140840b502031002030803542040c000107100d503100754020742e0305c0b0b0041d080210304217141c0e0748581c007280c12030847c40e00f1a81d0b4034602c81c980c40d80c00c2a01d0903400000c1c400101641092020b003c8507030f001605c9507800380400450422007200c501c41300000780c10002030403035000e1f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 973368938 1250 973367688 973367699
    0x304080a11031e18030f0a06020c0129010e060a080103020d02300d050c12030709150206040213060503033f0609060103090b1501020304120b040b01090507120203130c 73
    0x3c5502c84150b056040481c051000c0017414082000a41c52010101905040c020b984880c4040d42c400b58404405560304c10030800c02688460080300c0085038528040c0c0035101c014005403903a40c039103d54a108800070710081c441a9481ba50031819a6815200b0407940f50092000c90344004171019070415103ca011909000c803001c6040140c00c1c001800b08454000301e100c2c00586161003002202c00f019005851106420301c0880c4c001c41c0c202610b40b501081c555542c403080140850301050380c1c0c0041e0401c0b0141700035450010890310720200c0d40781c01040481d15200000b0b540e88201440012000d0b0007280341c62180f5594180c504c1c0403440840c28007100c0b12611184107043c1411500584180014070219010754440d100310a180c9522141d105d899883d000b442e030581111b4550124114841004003203403600610840d803503264450000e80406061910b44509010b6058111004452500041084050b070200c40c3d83c130705c1c1030030f16001a84d0b43c8418074002d01c3d1801912010386504201e0100144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 973370188 1250 973368938 973368997
    0x20a0b0d09110a06020c0103021305060a091406030705070b09100f0207020112141b160c09052a091206090a030f08041211030d1406030709020304080a1103 68
    0x29034030b115100915207040803004003c41070f0781c24018400164845851b4800c15402a801005003500004045010554882c00544180d0211960100056a100d402c0002c04022030407200a075404441d500c0c1141340030400100140070740207002d810401050b0108501c40c2c014855500003000e298004e02c001311500d003680340030b544803900403400204161044071000e01d85109690300d014070090354090a4480024001103948020291441003408000801403840701080c0d004910b44a2421045e041c0d1900c1d10040c04c50313000030551a02c0913070014181814000505807011841540d550b40c9441e541c914001c02c072072640100380c940952041c4000e021005100144802c50240b09507034203500c088020b10201d4146a065400501c00341240c12000c0d40c46015100d512080401841181e081c0314501402e1000c0e80e142c80c1e00b00014100e03450070f00208c0d0505011884c060900d0ba0742c150310354100356070f5411072441292400ba00f00800a0704030f1130280d10a00c115450840d0300c01d0346001c3c07034022074007208 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 973371438 1250 973370188 973370201
    0xa110d0e2107061d010c02060301030f0512030f060a0b031306020a02030405060c0c04200304121101141006020f1c030204030212010c0306050406060203091e03010c050903070b25020a0b0d 82
    0x1403003010320902c134480750310541d400301d8113960251000381142d1a59944440d0040ea41c00c0850b81d81c001d500b803a140c010a448091803249030f102062506d40c2c2040d5023800b03d0b44901d500403462000c1c08208005c5401c804800e104166a0310040050b9285d01307441040381140110707000940e1286000070441d0341c0200008048440000445040051440340c4c082819003162400d44010301d080305000240114020000c1055028080c0c280351441c960840740282c01c482c0302d0084454071140740c00c144001004000307030000180c03a040c0000c0c04000c2241c5c081da6500e4104030028041c81e00c0200d20051914401d8054500446c3d020f8903541c141003800b26403a000e04121b5541100081ca0b1010000d0301e40f60900030f11084481d01d402540c501060f4805020b002c2c1d03408510342d80320b0217822007050b0740350b1800d1207601c603020059513403c2c5d11981800304150078604240d101d40e5000c4024800e00140354841341c0d000c0304200ba801825a002880d40c40802c03207408840d401041e0034140450000a460440d4200740d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 973372688 1250 973371438 973371467
    0xe071206050a0606020d050309010209040204031a15030712020d02030106060f031a0a06050304020d080c0703030216030512071a070e0f0a030b0c250501020a110d0e210706 75
    0x40c8802d030b07906150b0004450700341c40b411006900550882c0700440c05900151b40010b041000035243c9444c060102d4266401940102c1d8199502601140d0304c1200308030158100c0706c0f402c031000c02c0c040300800103a5030340180d00407104400c040c0c2c0707480f100319030326688841ea8180c0d000d070080c070500f6601e02024154140321105400864100042c1d117200211400b02004a044010716a88090341001d1044807160801042213030020702030302a010100e01458042c18030b8800041c01002c0e110708510b402818403030f4142040c00620400541400042d4012a0300242c2001c0d00d4043d90322001d00b402d2250003951040108143c0040680521800d9a44001b8000720700c2401c1c0c036034614801c05c00c01400094243c038030010b0403100d054408642003020420050000304072884070070300703825490140000d0562004500b01c445070760010305200840d4116000c101202160304c080e003042c1c088840c2c00342200080a82041c4100009020401c1916202440b5020041940100c4208680b2810040d24809010000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 973373938 1250 973372688 973372691
    0x120903020306100b0315040b041509060b040305072c0f0717090c01030b0609180a050f0915071e0f02060c0c03040b0c03040b120f010608090c01120e071206 68
    0x200d0f0480090600400c484100f00c41034036541e40c140a107415100c0381040240d00caa115001403d035541c030f03030060540c010044c4200f010300520f085080d0080b90802d0b404100d240d04284030410200f403000c0741d09070485a440c0710904e81c01001500040805080c4468612005c0c000390038444050140c0c28858454689900c0d1228610b0051111602d00361046071100c50700d03804000420b900303500c280c101c0d00313104001030405070a191072200000c0404d074000843d4420702e1304070341c100302c000c0c6214040c450300b1a06e5900e003003440341842228140c484095a809003030840c0203c02017003101e07201c2c4251070304d100301c411103060318150031140081c2100040c840000c0180704030030101d441d00d00084111116102c440c0c0046141500c0c28007407011b0740c2c128100212080c0014000010b0440c0014010079554411030590000ca1070841c8000d002d0741d00682100d07040100300810441006c20005443c654624242400349164002c0e0000c840600802e094581042c081d50030001060000c0001d8902100c0c0704220 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 973375188 1250 973373938 973373941
    0x317281505040209100e030f03040803270306010306110f0f0c011103011d0c0c030424030209060a200106120b060301091e0314040f14040504022b120903020306 70
    0x10041a4000c00e001303030f0b900500c42035180e4071a82c05145610f650810243c1034400c450114080141140c115034030a82e0076403c00111740180d411603454041c5c951000c0001d01428140d01404255621014000101440c0d901c0c001e412104a00ca002d0701c100302c1b100780010340c2c0c410780c401490526400415a200c16907080600e80c4545001d110103a1341a106200800703000c0426200087c14811009004404461410098070561202c140003d0026080d10a45c0103083c0f038002da001702c0b01d20f0488000c40300309881803204072240c0d42c91504450013080b0514120284034506c04882513420044101c1100c00e40c80c107400014282d84207001960b82d1070080d026030203607176036010038503080c1c8d5000c010060101004040f520620000c41c180c24031103d00030714110900c4004000d40c04400d62103070f08858102c2c12201d8081103118a0a4140e003058002500c091025081c150f0108400242249a00f0008901c005016152549941d02c1d484280d8106043c0d420440b40c0f8040980000c03654041030b0301038041c0c1030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 973376438 1250 973375188 973375199
    0xe12300a1e0e060d09020d060219090e160509010e09090723130c0516051501090c090504180f0602031f030506040f140a1a060d03172815 60
    0x1111450305502c0681640c0c507064903403120000601001000301c3e4000d11030b0400d400421010700c05040c800f0307840f510402412035000406000251290f202c2e003071f44404030b8100071000752a1410040c00b02d40e00e0030410344a043c0c040c0180c2d42240040c00c840c1d005480d100800c00807a00002d4070b0000c888041d03815100f5065907085440c002441a400070360082c14075910700204000b0380d40b0049030303459145041e50414109001c01080c040c1c00300c0081d100307680104004001945c602a1141c01811425000c22204541880241c030285892180c47c0c812540c1c1d40d443da07208200d0183c01c1c400141c1c05600028800e84a1070700c40029081582d0400c9980c0c40504000e0f40d48440c144c03030400382c94118005082d50780c1c96940301c0c0c3d03c1242c441c0040b00c1e60b0210480c1044a408208400c124151150b032665804590303100d10074801c50f4004117480c1c42902c3c22541030700400e40026000051802e0203014410540d590034061036981c1400c00001640f08000d0503040740e0105650000b20704845204101218540c1c40c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 973377688 1250 973376438 973376447
    0x18050a030305120403050408060103030914042306060d060e0103060f0b1c050703060c030f0b03011b081008190c0515220e07030c0e12300a1e 62
    0x1804001c021400811a80c1c412242180d581c0354094803e18000b85066201c41ca4941400000e80c02100400c5c0720080a010401c5500d070400440007040d1030801010b4511040c00040c282d0413141c0500b0340c00c01e40081115034940ca000c60720300c020f10000911603580d44415011800c4000d00c8240d96035440c01080c81c3c0301c05814003c110100100528401d20130134810483c401801e0710ba00220303030130301c190320700000001c03124010703607261540355180060a40d0404505000b40c0d0710400c80c4910991602c01034900070b045462041c0840d41e15441c1c05041d0b5920f450381081000d40d00c0e00309603010700c0b5000e000d02410740074504917450580b2615440040c0340c1c0e5802405618801d810b100b254001d020320002a54624130710a41c5140b50f0302c501c0c00c03204a0b94441030f000c6060b6040d03c2500000e40c42395450301500ea004081e0280e00e00090322049114055592034546901545c0030400310752695a400201710048a680660010011103500d6602c0402c1c203009440191210074501c8901c8050b111b000030135008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 973378938 1250 973377688 973377709
    0xc1205180f030a0918060315020d180201050a051b060108160801060e0c07080910030209031504200111160e010803071208190911010813050304090c0c06020a1805 71
    0x184e0b21410700c01800d090a60310711200c041000c0517407aa9405001010490100181c846940004030050b0388200c10b4405506840f0440c480d02010305428000c140144d81c4036003101d0444c8a6490720f16211038400702c01010407a1558103100641c420301c00082440c1502081c40c10012210142c2200550390701c2d03d00c0b038241c580d107101e81d0b04a003806100085034020b072840103084a034464a03400d85458049800607011114204a480000e5808501160300e070400b0041450101450900100980350903918404406c403920400f6840ba407000c003078007140364040e0112003d1201e103001a920119500b4406180109803886861224440640002801e402c00b000b180d00f0242c100f424407550740d84001060b07075040c10281c96101485405100d62076085218030410f9400b920900000c03003a40c1e5184001490490081c00007403004012490701000290300000b207608036140e4100c0480c0781080c44c801510b810104c0000501081d00014640200c141e10506241580c82c0405940c1c062513192010700030035608 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 973380188 1250 973378938 973378957
    0x60f020f061306110a031a01140d09050a0c030b070f0306080a121b0c1401050a120c120f0e011104050d0b1005120604060506090f01090c1205180f03 65
    0x550301003607880c064040941e840501440e00450041d44c0c1c280d0314005071707010107070800c0080d0b03031180c1d9603400c0c0c2d07504181030341c40000901c3d0000c20704409000c840c10354402c0c62811040079076104540c100300071050020122817600400c144001503501d00700501200030403075010300082d140c00c8190048078000e10414080d03440480041c56081c9007540d914640174020303200308040c41680c008181d07102c0851400d0011040c440c007040d1044a00d000343c030405406514000314103004051040b1114158400d20031055010300540102e1182688075095a0f100000d4a0404819040030415010302016401c4400c0c000700070802000020203542507a103030380c0903034054940c0c000c0004441c2804105007607115900310441c141c40707081e2540e5401c0042e1210400f0b0403c104c8c1038200008000c20303c034140c40b0317984d0300640c15030b114101460103030145c4032410014010281c2c0c0981c0c41d81c00c2c0500c580301d10307800c40350615035600802c1581010380700706180d28001e0b036100d001d0303100e050401c0d0b400d0000802568203150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 973381294 1106 973380188 973380193
    0xd020a0212010b0f10030212100509090114070e0102010b03150f0a0504020303072012010f1a0609040e34170a0602161407060f020f 58
    0x80c6007954035003243d260151054054440724000300c1001ca080704c4409101c40368200640007401000041030902c00640104042c00b03003501c81d03520a403a008c65501ea0145e23180025103098030b0a141c00c0d1fa0b92600a440454447c9000d4910f1001e0240305000100380310440e480883d1078190200d2401d806100c0311402d020794148503840341d0382c100c05070000c02d100514080d0082a5a4442d10b0b0000b00070485404034080c104007820140c1041d400010001000c02d81c40030003d60182581404400c01c1074940240c40281c803029045030b115241000d04603500b0994000208402001d41c1d0521440c24083c1d1484003140c1c0c642c248800c0d0a0b40c0d0112545a201d5142a030180c10b50942a0032812031000d00c0141d560030a80b001400580c4036178054405a951104000300c403026403201d1074001d0800c41c5010b0030b40109100451914190717502551920142e210240049a5555010f032401c0b6054 = true := by decide +kernel

theorem cover : BRFrame.Cov 973201438 973381294 := by
  have h0 := BRFrame.cov_init 973201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 973201438 ≤ n) (h2 : n < 973381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
