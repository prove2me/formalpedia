-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2817
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:49:45.377519+00:00
-- url     : https://prove2.me/submissions/a8bd54b4-b696-455f-8d9a-456720c90b31

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 506474820 ≤ n < 506654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 506476070 1250 506474820 506474827
    0x1206030a03020723060703090f05040c080a20030c0a03060e0103020603040b07090807080604060506040501030b0f040f02090405160603110f030a0e0304060203041a03011d0601110118060f02 83
    0x5401079a510f81502402c81d07015500312aa00091940d050110410b1030041c22041e2510714620f000b40c41650180103400502500d56800300e181d00700782c40758a1b000e000665440b05103440d4620204001c1810b8407020800c0060407001500503120302000f14041c000a00756155103810080d4010104c0f01e0507040f40c403036182d501004002598070fa0382581c0d0465001038520a0310b80311004d054072030300d1065100344400d01840c080014400300200750907101c3e600a81d8107100550b51203040004840090000600e0340241c1300114101c1d000c001d804662151160030543c025240343d0700090003002084508407030a9002844c40c0700d0a800d40000d00c0c004100500b4140080440e1818030a401c0c0100524025440000320000b10000d40d00c4e004094402503035019242d840c0c0c3c8540000f92290722500a0351031400b42203500904490003481201c1c100c0f852040480803031088990012000c0d039014103d20304200785003026080c070110078400d011701007103006a1004142c209213000001c4d1000c504001c0748461050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 506477320 1250 506476070 506476073
    0x60e01031104110d2a1206140312030a0906092d0b06040b03030417060105030706021203161133040b0c07080d0609060315020c0a03030b06040b0d021206030a 69
    0x3c405490314130039080e0b40420012021606010369801004d07105407002c40c3c0040f08064640c02031031420515510440602c1103548920806072544817207071a10360154803844090350302c000310740007458011103c0440890449507540714902070310460441640d071444000c0d20000c001a20301c3e910103107500544c40100b007121681d242d6504441000748442d02894030380d41cbc1401a075405004490140603009252050703405001c1901c2d81da076409000c0d55000307100300180490846c1c0005201c5030410b140c00780c10380c50341e074410113003004041201c1c408500b4480d00e000704c14040300007440401600c0d07000150200d07001614121101d45060348152400709140c1c030300184008a481c18558550118100088580d99007651800d2507507440f8803094080464035000c0f000c174540c00640c014a003103030302920070a9403404900d0126002c900c07909042c3d1011754000501500068000d401c02985658014001420f0a80d03507a40c0740000c1d8003c60301c40c1c0c40b450380050800e50160001403a075802003010380c000c000e402e20a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 506478570 1250 506477320 506477351
    0x302070e010e131e02030102030405070303030b120a111f0c030305060f0904020405070c080a09031101031a040f150306021201240e03011b181403030414060c01060e01031104 76
    0x3c800081d04501d00210300010144180b004408101e5002e80210b42e82c0c941030601d0ba0300c0b40241d00007100020b00f0650503402501c0c10001c4400407440c10030180c21083c441d561030030340040d0f01b146903a4002c84004842a00803030f13126400080b241d420b440703100c8000b0749460010220394000f8940b0703100d494022140807250701d600510b103030f00c15415900000c4507100c0080030707110000d0000f402840d01c24006001000c0c168050b090300700300da00c202200c200109020700194155405e04c242e8114102607403c003034045290a402034011100d102100003612800c0102614030000e03d80c1042e103500345c0003e11909002d50785000940100f03400381443c0444200c0400803441c0c000e00045103c00c2058030311009205541c203610130140e854001310708540d8200400700240c000e844000a00001ca000c4100018000d2903101c07480c0020000107010b50300d058142600540404481c0100f107400c0074052006013081142403241e90054020042d20851640c90751600e4007030001c00d4003241e0300560030080191800c01c01d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 506479820 1250 506478570 506478601
    0x1060b0f0309070e100e09061e060a032a0f0308090915090403030c110a050c0d060905010212100f03020a0b18180604181505041506030302070e010e 65
    0x610301025560b51201040ca0340b8240f01034101d02000b4a102085c46800b0900315003000445520000500c0c10f65664110780c2e840d001c0c12a02d841200810901c45144040003103641c4c0d40c8502c005201c01101901d0703446010242111701509076014400740007000900d92041c0d07811000b000007000ca40c3c412030031942c406110707010351074103580140c0c1c465001c1a0b0140704038003074030401c41024220200c45d250605008020300001150040410038601d06210403c801003606422030303400078001c08117201c8c40c0080c400d03c1c0030f504000365003007580c682980c4001827007130000b0000207541d80040511400e00c20240c1b50400b49592000c0c0d00028501802c00060725a1003801c8100d4003400e6030310f40c84400340d0701c0241c0c0d085150f1900941c400030421140c0e00e0200300b258018007584003500c08200c551250280449407880e1102c01a151080300c4001c51458280c44c9c12445e4000e109850306080100034008a40a03900b541e002100942c10407581841607015100f1800d004002101c00540241082201c42c0000c20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 506481070 1250 506479820 506479837
    0xc03141603240308032805190b0d0b3d0501020a030e0907110d08040b0a09030503011202040917091504060f0c02030712030e040b0406030816050a0c0b03070e0301060b 73
    0x1004400281040c4a045101d8200f034604542c205800e11007907040b06c01410206d41400c1000b85441003021012424031400b0004100640b29900c0f8200310389600c10179440007130230303001c04114408001141c40c0705030b4000c0c03d90308076201c1c0820b00c000c401035084040c5038a41e00300a04550010b0f200c54013182d804030fc071900c2518152520f4240b5203550600f140c005206804000c2903216030a00720740b9169000480f54480d5001d1040d400050b15940030346015a561208090005801400180300a420720310040490500c01400014110203c1c1d4950001e07440d44118444240c5011440390140e007404280611000c40e0070003090700d03050501101605050108001404001070300200e48110b4500b00604000750100043d8140c02203094038000380100440541c490140d4184104ca18007410240244002d9a43c0660510f0030041d02704201c0090404030481030741c0504c66007298902003900e21040d00301030302c401c1c2411031ba00c0c40c040f00003602000c0409100c40c000d03850140d0800010307003084156220070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 506482320 1250 506481070 506481083
    0x40b01020d12051e15040b0a0b071106120103050303071209030804120225090f0204062001060e13050c011403011205070504020d1d03090901090c031416032403 70
    0xe4540c0c401130490304a0100d0b14403201c2a40d1400c0c801142406841c20084400031070341440020503880c140910000300d8401c402d500030b402c0c01b5200005201107100940d404001d03029905006005014101076282a8000c0d03541e600700106000699510040300d001107d80345109108405459070010f02c0c03401c3c01400981504c100b01d0988800b03900c280030710183d8040035107041010b00f401440b00600b44a42d41314801e00c0b030303103018101080d03803800e802610111341031511030400c13007032320548038500c04400141c11a866550300d460100301000c0320303421207004450122032009485240e00e091454130300a030f400f407418400307072000381c0c5015820f28081381c0c1075584460130648080b0740d1340b4202d0302c0c054098019079030090004c15411100b2602e50701038419064a42403c3c941c061628110395102c1c810020ba031504524500014085400035800074040000e0314900052003029144001e100300d40190781038062002000002c00d905c951502880640307003103d00a40c070003100c0804080e44030111900c0000d054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 506483570 1250 506482320 506482331
    0x501140304110904020424050109060311090907090e010f0617040b010b0a090305061e0709080c01050a050405040f05011a0c061311030703050a05010c05071e02040623040b01020d12 79
    0x4544a41c0c2020300c0c040e129440c0300c40c9101a41c1c7c8070300500ca0741401010b00085c100c2000241c0e051290284a181c0850150034a02e004003c20034062000b40083c002420320002850005240c44805070007802401d0f8031400005241c180b04004000001021131628403c09007018030002c1103500c900341b811164984002c1ea5181d10b513150585800d00303254405003440c0140410091b030443c3e0328401140768088003101181c00d698169055440c070482e80100c0710103070700c044805103c55000d640180303004025802c015007482e03a10300004007901c8988441100380e503221401000704415121206200005c042a10707410480500e00c81c90790b4a4009000491402c2140d003c0030520030342c01c1500c0900c2c400078061360000d58603820015074408c1c0035041100c0e1503107400c147c065003034800c0c0250341c4030b107a205542d002c804115582c00a00c102c1046030a99000366160400598600c1c4107103890020240000c0b50401154520104001c8420011605055421401e035054040fa40000341c0c44104095030400190b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 506484820 1250 506483570 506483573
    0x41d1b010905030a060515060c1b0d0c0902090f040507050a0c021207030b1008150f04060f0509010e060906040b04021309060921020708060a0c1107030305040501140304110904 77
    0x40c031030740ca41c0c04a901405001c94600c140b1800750800303441405a09100c6411074040d00034004248500c0b01c803541a80c02041d191404c0300e85c0038a942403d1100104007854054098039085101d5a00343c7c4800c00865001846102c0c82c2440540495071080c204c904001c186802d1002500910401860004200b80d0340c41c0d44085644202c4c4c0e0310319440f1500c04588480752245070007071b800c01c4213648254101c80c1c403c0c40000d003403800040307114010031100354002003911211400260080d000c1d20031206580ca40c0c0ea41941141c5620506220b4210440040740d0100509802400c10b18080e01d80045508031004010209801681c0160800c1e41990703040c50040301441070308000d06500c40300030400c5051404003010304c5500d00e9808100841c03110100a1000e0360a4141c3e520921846038084641108000814103c0c2d07590281240c01e00c2410802e4289259851141c2011140c0e002200842d0f00410140102c1d680035982010300c0803117444451650805848003d826552280014820000c6800040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 506486070 1250 506484820 506484827
    0x405060a0c060204060203090a0801480503060a0b0313030c150f050a0c030e1213050603090a05071509030f03050d0e010506010305060102031204060b0f0603070e041d1b01 75
    0x781494100004540301e5444500003512a80124503191181d10008008115024103210700d4a15105c0211300c201c419815032029134480c070a20600c04100009034a541d04060700c00e800c07003201c1c0c84055a405070342c2d25191040250b4922030350000582d40c6400d100f0090b007210f64003100b185982e0141841c0340035aa46250074104000c01104128482d400c24229140c1280385400442c047d99100a09000e80e0b524414114200c0341080ca0050070342e4002c0982000e2881944014a0300760340c4445441683c54540c0c021921991007034860b400780d9403000e12a1b105011080c080b1401400d00c0c0c07500842803a031182d100a1017600f650001a04444650050600f0140144e046403604400715106100c400d902900c058001c2204482850100e820807000840940c03001c4200c070500b411440c8214580c0c2c40c1e41c0c80f15401410840c402580000d081080c1118035991040514803d041a5480880e1220b05030144001d944181c00b520700c640e07030440c0110341d9003c000310b001c0130040b121031410030800e0000d50048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 506487320 1250 506486070 506486087
    0x130f0c122003040f14010203062b020915040c080a060501030b010203070b07021603060c1206060903110a08030f130e01050a0b0306130f0b031e12030a0f020d0b10140405060a 76
    0x805201c10145c000e2540407040d00554440c0e14111901c1c0c158060300884003e440fa130303505400d54410400030b41600140303030900300b858000c40342001440000f4603080210303044070010317007044c03022a40c00801c1195503007080c0900406040286404e015403105800041c2d980d0282010003040504c600002582080c4204981288884803110900f4030342e6a07401d200000b49401c400000c00585200c4500c7c0342311205005041c126222941c40d2107213540307151122240909884815903000c104864001003d013010405820f003050020310b0550307602140a001c0948800070740c4241281110600108199900d2039620301c101c503003150b000355403a0385420010b003258207088243e0321104d01e48003154021421645c00101b01e190294200c0c0d0489040c80030551f403000d0001c1d015115640a41e0900f000c00300800301031500418000d8011400d200303150a0a403d07030304440b030fa6595480c0ea403c2c1000b060300d0300351901c1c102c1010380c1c20895800403a01e1506011442075001d02e5010f03010000300c40000f0791080204 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 506488570 1250 506487320 506487323
    0x904061d0118090f030e09100e070f17040b24010c110f090103080408011104031203090203030f0c0a0c23040e030903061608091c0e130f0c122003040f 66
    0xd85484603011318001d4011100300c0079060091f410200082d912840100b141e0058521940c010249951aaa011107050507000040300400288119401d820414031a042d4000c0748200c103c07180514140703031200d00c91341c0c1040c0c01e4504a04504807811300c0d0398000c469441a0f98120300b0301e40c1002103d00c04128840c4c441455150001c52110000041c0001c04016000340c0e28418002e020201156031032215602071804080c2401c0e401d01c996400c1240240d00050181d403014090700c5c107100ca5910241c40c0e0350002c0c0e000c04c805401020708082004403500c003640c050000312003040d03002c01d401030441083c2c00714840d8140c02140e80361800103101c0c10800a0b034544070f00c02011203107203203000c83c03201d0b0001c0b4614060308041560380b00490101080800d02000c0baa00761072050314a040d4082d4220b451554041105401410046000107140024001c1c0419481001070100e444004801e00034001c840a611800b182450011113042000c400008500c0504401c020643c59880b103080201401003540780 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 506489820 1250 506488570 506488583
    0x6090b130512010e07090903120903031b0f0e0d03051b19050708010b06040b07110402090418020f060c0307030c080912060906010915120303090b0c0904061d011809 72
    0x101500310505400c001d6030000704c00d094858942d551364241055503a000030003004550100322181c25804aa402170703d259000703281c0400d0b1a0711840020640064103000320000808055880004942040940000c036a0070b941c110700700681610010054014400e41c0c0d40c0a900060401341c69400400c004480101c0d11040d126004030f841c40e009030360304098460254a5400c04420741e02524007030003540c00311001503043c546480c4481d60b456100081c0000c020707620075400c1c0528412619030b442920300f4a0410740225104108600420508a102042c510301c2000200210044454040192124568075091600c02003040e0701c2e10309840c0c0103206000d50000e81074034088070200400280340b0300400b21142925101e0740c0ba0b0f03015105440304915821b0000c05071060420520380c81003c5010618041c0c07030000340c00c1d01e207503480c1200907105480b48001070f00081280f98003072801e8492280200501c0e012913060303801d01401d40c11810310510803010500c0010072800e5044440ea080000d400b0350262 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 506491070 1250 506489820 506489839
    0x1050706090602210a020a0c3009030302060a060302030c04020904020f0c07030b0c0f0306010807050c06160e0414010e0403090e0a02031506161104021201170f0706090b1305 76
    0x30544002c8407403d4056000e21414480811019141c0d40708480400701c19503138012041101e45c4034565054500701040b4407541a5149042741c4a42001c20301080107a00d968040801d842c1d030070002c0c40c2c00d5025241d820700783e203052001c00040c0e900145441c040da42c00c3c5d81c05a03c030b4403000c0024000780601a06007005410001e140c00c15440042104410349210342961070b12038440210408080c01814082c88842404001250380d0790302801413180e120b903061408520f04001c40c1c0a290a00209880c5c0c5200e4220200140782480d40021105581c4e01c7c040c0ea04026024040d0b40c1500075041c1031143c14540d8040c2801b00d82410b1240704190041c0020400500050405070600303402075004841c50002c40c45c0303036588040c00d4a851800c844010440032134107010b2092a807543c2c11401c5c00c01e11601d40c400d81c00c108051a1410141078140200212a041115204c0085201d810b1120681c0d034100305400c80d03102806241c0e0820643c10903102401669030729551041d0082c0c1c0242000d8002d20391101038003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 506492320 1250 506491070 506491087
    0x71406060a05040f140a020c061014040203060a08030a090303020606010f0804061a031605090601050708120a0216030801080c150d0504020303040504050c0720030c0d020409020d03110f160501050706090602 90
    0x9030010016803480c01d08880322039135503900982910003207000380720841d0bd05c2c0c038000080c0d00d01078000d5a00f04100500b10344251355104030b00741c9158010b188560100d00d20724003c10505406000480d8422000c3c01c24a1184940c1c4000804540e4010401400c0329601d21070481c20a080070481254480041c0491b400c1d0204061401f1040c443c030f200d1a4440d181107000111154858019108003981c031510705420301c800140100358003031000b04060040c0c0d509001c800d0300700304510300007292640070391190021075042c00c7e2024205050b030224540900d40307404c40000242106012107910303500403c000074042d12280f002a08607c03441c0d0009610500f440103000074041008020040c05103e1705c2c01c202c0c84103499103d042e4900442660f81c0d455013000c941440c0906181030828400d0344020300010f4000d0141d03000a0b8202c0c10031a0075400035010050700365034600d0400c0000414045072005000442c44080da1042b4902540180c604104011401d841000717016004030729030315407020301551282400e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 506493570 1250 506492320 506492341
    0x30c0c03081b03252303070c0c12261e0c010f0c1e02061303030b0301020a08010501020d091a1617090114040e13021212071406060a05040f14 62
    0x1c44090129401d54404804c81045c090310712814280c4d1605d450600c061220300440200b90001000e80f03003840303003000d14040000c0c803078400ea002070300c5000c812500c01105410041c1300000750031429468440a0406c940b584138450059036034a0403442d483c4c29049803501e80145060158410414003503081048401a24016070003220030240d06588041d80000d20080d211104010b015090001da040800800c8412010442c0d08a459009060100b00c40140d40e0109007240d0200000200103139003c00103100c203607414041403150510074a40046014284200e05034110040d800b5034000e1400010201400300c0c1d031401040c4100d4000c103004044684281e40b155040e400210000e00140403045000e01c042c1c40141074506503100082202c246079034107900c103000080c50b50000c0ea0b100204900b2001c0b40d0703801b00b20381e0003294418401152500503e00d84000540c0c07400c0b0700302203260050000c01072961106807448080f2030084402103040c10000d8044030003481d40591448042c1600c800708402c0c0c004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 506494820 1250 506493570 506493601
    0xa150c0c080307120e0d1e02010e07090911010503010b0306040504110310052e181b0306050405060a0b0306040507120903050403050709140a090206040902120f07030c0c03081b03 78
    0x3002c03c083c017160040b00710aa40316a08510080041041c01d88003203d0b2104280c4a9a20200903000004500f050000964a05855a40888100354a60b240b1100b0014603039488100c0c00402c0c2007030340c01c0d541001603080a500000b00702c50300480e40d402c001014030100e100130b1704d40390307e0243c10707038080043e41c41a003c0502030846020010038141200020200c03291403d0414510400410000c406e04111501240c0c80425010307069541c0c8440404000c8460560070460b00300c095107000039014500014401601c8004151920030301d0304843c100300741d10702542107943c480d00495000840b5564a10162051401031103102409032a0401600c00c250304180240103a0740035034201c44039543e41d002d01d41c1c2034528000500c0710004046c000714030b2483e002d03044a01100d01c001c00b81030500f5160040d1408036041080c0e04c501c41000d050130700c03607203030090a0300b0f640064007850b003800035101c1da240c0500480300c0c2e410b0043c10440c41d18001414540120003482c41099010903c95480c182490241002c0d034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 506496070 1250 506494820 506494847
    0x5190612080d060512300d05060f040c120e070e0408030a090c06020f010f02130b070609051506010e032806020d050f100806130f1b0611010e0a150c0c080307 69
    0x46c54010b050710b034031070315034624612040e40c8035500d440e4440c2003820150401416098001c0c03200c0c10350444968560240c1390b000f5011b9962185d464489201050503504030750001c240f190852181030150444400c00207078010b821551b015542e480d1013803403074020800c03083d014182880c3c150000c0740700c0760b02252000204900030000e001408021802d013007248988032044e0058542c02c1c4080100380c00382005000700c80d00601000401c06e005444050403d0300710741050341d1803014a410401603617040b4102a2500d00190020852008410010543c503403640e0a0940c2000c07000380420f08114154044400080c2401428030860602a810006582c3e081c3c49031803201d14500c101050300d2038000750541c88ac15880101001c003100355103a45225107071051382515815501103841007240500403000300200081e030307200c0a002d1000c1c0748507400c40d00603600400644c0c01c00c1e100c540202c0e84150342001c00044013500055551140d4905592440410030003e0100e1408402c0052051b0007140803100720 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 506497320 1250 506496070 506496103
    0x90a11130f1a0909011a1207180e0907060503060f04140f0c0a0206011406070515071d010509040c11061906050604031a181005190612080d060512 64
    0x4400c031801964140030312143c02c0e40014074040100502031001d0743c055210310143e2140d520300960303000010010b9008036a581d011411009c100400c550390300c1500740c003d254030340158030b0a0411402c11038541859100d01001c000c0c01002041082d80c601103040000c0f28002c01c10803040c1180247c00c034484900311000c800c116020340000e400c0144590446904022903400303444107030700348503d20040724100e031003640c0c001e1014400c680014a0802081030250f041d1820629286050356004100107000600303a842c020030402400c1a5980040943e6010201201c3c003140d5030403001703001c0300c1030291245010b10a124050a204032203005c10148081119694014860540c07034605102152280780f0000b4032101c4c00d2805030000b5000e80142681000c0050b882c1440140c104040d0b038030705050020664140fa40c1c0d0020301809040400c9880d103040c1d007519040c0581b500c1e0011018440010709400780c9422000a138040c2e2140744c1c0d0344068090403000b80030440310508031b400a59a6881c16020244c078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 506498570 1250 506497320 506497349
    0xf010609051605040f061d04090501020c2a090a200a1803080403080c0a050d0512100501090b030c1611011209170c070306020304030c120806090a11130f 67
    0x1d10b11543c102e5003607603020301e034040e9224a403880031244030300c9122050340b00100000f0240c4181d91680107520415014034000340e02d89280d00e24080c1000d007460100800c2000c903601030600e214201d00c480144000c101c0745041c00743daa86465901912100c4034940c5e05521360001001c1144040c800360401340f1042c1d841d1800381c1301c6503106550100d8640006010024140010800144003400a00a0030b02c40000ea1f41c25021276528145421019040304020a101003106480c103000c020302c20b030703000c6200c2c10041e1140d0318060019103030f4841405120340707110380000046c0b40c0d800d0700c06c01c88800110900c0300005695060400907140b4208000381800115a2444644104d8a6000b460103072034204035811840345192040400d00d40c03124400b241a80241140000483c000c1e02c0607511950007601e80c030344403c06503e0652138039608001d29006001414041c815682c40d030789412a030000c13402c0400100c40d16800070301880f42c018000188c213485840403003c030b08086222520012554440311160303c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 506499820 1250 506498570 506498611
    0x1020712180f0b0c031e03010618030804061107030506070c140606131a0607111005192006041b0504110f130506030f090c01030207081b0f01060905 65
    0x201d0708075a1240322082e0340c51070024801080c064006010111074a81228a8089000800c003800740007500180100d00001c401040230503004a6001c3e024000368401c0c1c60350a0440c4c1d50030940340282e0084204000711080c90703208845040100c440136503041070480b6658681a08000c201000004080b100141c0301815502c880d800015414020600104240d280e440c60500c014003c00c203050020220020000802c0c5841d00c44400511620703000d50b40000c2c0300b6001c44d007405441841c18103e101002810045050205200110010020520700d403100900b180030346c45c0103001001003513200650041c00d050004000d40014540b4001d441083c051052540d02c2c01004210751800c014040350450070030610707000006070b000905200c0b5607640c401c0d58041d1200d01080064004440006100041c2e07414001000c0d0100003880c0c0500003407a0640c0307002c07001c0d9078035079040c01403082d4110102c16901c6001a464002c2c019681000c001500800c102035035000808007070401031300c0360301c8245104565000b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 506501070 1250 506499820 506499857
    0x2009030c0d02181b0d0e16150c020a030c0905091b1008041505040f060b06030421030906020a200307050d232701030b09180a0501020712 60
    0x50840d002800550f50f044603c8080c10303100c10052400c409241c1031401c42c0b24400d00070029026680d014000024602d1048200c2ea281c00714211011302900c1280b50300f001315140099510003081d0070b41c0741078029502d29101140e604501078200400e9190442808940804d0651040740319802020440c4c0d010f200c51040c801e50040307001042600403d9404943d000076005d0080c29811520905810445000030b03280c5ca0111101640c0807100d010044c140d2070b0900881d4012030030002402c540b568614101503070399007009618030480302854a01d00388001c101d42c2c00303a400030050541040301950b90b60642200101541d01e4154911010f1804090703e002e0341d440001990070a43c0e00c88001d250020811000382e87c40f845000c607450b8103248601072054880c540c40040c0841000700b41c890072904641c0c03004521142c0410481c281054909029a0407a90315880101e402400d00d82c03099018558580307074a410880c11440c054290b41c0002660010050a501051440c0c0159030780d20142050303010600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 506502320 1250 506501070 506501089
    0x9030e040606090b07032007060f080105030706030b1306320f040203090f101d0105100b16020a0e0601020d0216030308060f10020601050301151212032009030c 70
    0x4100083d40c0c22000e0252441e0540140940b034000d040c0b9a407070480120a0340e4500b220050a01c00580102508012258000100700503250150908003070540c10140401da454540344600f03001c041d1100310280180c0c807191b0841d0b203c00c4c078000d000c0c800030341c80d1560445e00814810a1285500c1100c3c001d184400b240307249098030f010002c02a0100c04038000820020350009089020140241d490395192554108880403076082d6200c004107503080c41990601c0e100d00c2e21014070360503904042c10000644980003504065a40001c201c075102c3c4901581e902141e1941c020094100402e50808a5038619412045100d110240c0c00c076468032a019200703d03190140f1944045007615000c1061000074019085164000c3d000740c12040b6100d082c4c000505900d204483d24005a040b10005011074202030162a030800700c1420000031071361511b10300c16614110a0b0001e0a07014402807110358040c07003500001144500b00b2503800c0200d0005640081079808041d40612034402c0364001000ca04144201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 506503570 1250 506502320 506502329
    0x5030a111201141c11060c0f060f01050d020f040c03061e090501060318111c06140f09120c070504020705100f06051c02010311030108010614181b040302100309030e0406 74
    0xe41071a40340f40e5a0f105c41c54045240625070240c01403000c06003103403041080c4021144088000c2c6004d05107000c2e040007244041c0c020901440c11500c0300809070701c6c1d0b1031b40b501c040340042d9000142100c0c5030104900a02b401d811500c1c481400d2203102604122042403807060344c040c110100f015903038a040076400c50b10728000c094000c2440c40c00840c00716401c140c000200c050081c18900e000c00c140d040d0700c010012240411902103545264031051142074800315a07002e41c50031100c40c086c1c1465441d5aa965100c84100e50700003c00140b1042190b03800c0c410b5200920018200350b4842056190841d140e41e40b048059064a19048a200e20580240284801c5a5015020f41d150446d01005480030320780c544801d84c1456101c0421101d1055144011802419540000161a800e2981411138540e0303c2101034496108440d8100310a44516055030304000c0184c181140301d40725801c045801c7c0201e0340080d500003c0140c104000325007603001411514881d40d03901300500c4400c0e00304001c90305107029 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 506504820 1250 506503570 506503609
    0xa1a0406030518330a0203090f1216020301150801091e0314030703020702130203061003110405091b0406050909010506161112070f150c1205030a11120114 68
    0x201241880b00b4404d075642040d03100d05074900060128106115400800e0702c1d4001d050b9400810881d440303d041c0b0841c0150941e00e0007400070880002e52010382406040910703040300203152840411907409500c00b08035000440543c081641c0ea030b04165009210541c4240c03059034100c0000c0369101212680516160341c151614000c0004c55000c0321001d4200418050500d907007000003a0140c7d5442c1e0686a811002d400c002d41c1c0c070300d0641c092008145241540320281420a51980c0c8400386450688050354000d440d00d03c403076516500d500030b45d600a04a42038450b14005000f1a030302d54050000d0205805c01c0e1402c4903181d0b07071501401030034490751098010400c15a4400d00000d4428011141041801007100010150032070501d07040c04999403000f01c80500407481080030650340c541da82910406401c224681c020261180341c110440c800c5044204503000001a440180710b6205070b03802211041c10179110403c0c107400c860740c00c4080c060708002c0c0255142c0f01455103410300e0022180455030741c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 506506070 1250 506504820 506504833
    0xc0b0106051b0a110102010606230904020f0c0f070f080a150b0301060b04140a031e0503130306050906160207271803080c03040206030c090a1a0406030518 68
    0x2088070315400040e10200541c4000c01559224601008059102c0d40a21001030300741e00e903000064211680c5510241c04d1201d04001c1e1819401e1862660802ca406061025034621051700010024400c565410350340319404190400700041c0052180081d8031540105e41c0910b46903000300704007004501c20680240d02c4945504001150017008841c40c125080c0702041c0038035240d00007400c1d9a9140c01210006a011804108059005040242200c01a60302c074026038119266000060300c07aa610101c0d02c8c49d601c144008000c070800443d681046170700c00001001d5140d19000016010a49080390103101c0c801c0410780c1d80c4140403100d0310405032500140301c1d0b5031a04446d0350400d0f00e10080146107111202d00036180911501030813030300d0303034903c1002c54081050f454040c00030000540074803107200e4140300300001a02c981d02100c0e00036030a10211a01c0394201400139204200036002001003002803201c9585940d100350140081d501d9540381071000390355114200354074103061000204031b603000f007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 506507320 1250 506506070 506506079
    0x1005030103060f05151e100507060b09070e0108090a060504080706050f0c090f010215160f03060b25141011070209010605030c041e091406010914030703020909010504060c0c0b01 78
    0x2441007a012160301e4400c100070400c00002520807c100c40280000c6000000c940007000b4840c0301c0e048070400d00300c1d030800796070801d80001000000006c0a2905000751100860541c090410541e1000d641c8848180a00d203040c1c034052246402040c0219038041c00c1c1790125004500c00755010340b003002e40c00d00d014141218602040380344a01407a03c0c2d8103501a5035402da00300b00415280c0d03441500991511058004085ca004004c5038030084480b007003500e031480070b11200568004840d20200003c110000008880c566070849266142c40103150111040d820321080c003010604411820b0b1420041050780305440f80406036102e4480000d600000308001880305500900141d90049191030010b0304050312080c061402c81040f2000908104000c94100f10090f03090040e040050354816510445007820400038144102d14010300000020340f500400361a10208040001950028050708890905490f13940c024a005c3d01c068a44a08004e0051800342c000c010032034a903035015419403071070b0b0f281 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 506508570 1250 506507320 506507329
    0x9260d05070f1205191b1404060906050a03021b06060a12020a030215131e0f080607030f020c12131203020d0c0303090b010608060901080606060412020a051005030103060f0515 77
    0xa00800e64090b40c445e54648210840c8551091020403003450103411501d04c0000d8002c481c0302c1505c2104003010481400041e0380500403400300d51441c14503031b07180d1400e04030070b5000e8040c4c540d03510a800180150014022400500e2038002c42054607401c1c480c54844860395604806924060340001c0c040ca01000181000030892a60b050001c401c5c0303081c00484440014281c2c0507504c5440303101601051540302080d080311981c010494107a00c03c100c940f03011042501c8205c010a07050505030f0354180303110a802c403034040303601c208061419220182411140c440d500d4101d003042060b502d090721400704100c441d0030b0080d0a0103030560010700c0c6d5a200104100e6960302c00c85021010551180ca42c400000c9081c40401d0281c0320940f503520241c039243e0140854010141c0c81021207521800922605d0b88a07841220103558000c0d440c103510307020500201c1c510101541c40f658001a13800f803100c0056a0040285060300d01c141030602c0488000d52005003a103005440c103024520f0314040241d1107140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 506509820 1250 506508570 506508581
    0x3040501022104170708100504030e012102030c1b0f1518010c0c0203011a1507051c020a14011e05060f041b02070909050d0309260d05070f12 62
    0x120b0381c00301481d182d2196007503c4031080940d0f1440c425400b150080c80809800c1c41016003d8115003c100658075064500810f035501c201f4a035418044602c0304254a0301c50031580d100803445030803040d17640782801d65451813241d000c08517407800c040034039140c80305002003c600c01c1c0e011400400180609000107490382d180d100b0103061807148040049491900784270078003441400c10b00702c4d15003075805c481e03030b006160a45110110326096031101d0a40841c6540d119030401e28081c58031ba440b82d450740c070302d0f140883c9000249080303280013049041c2903080b12640090090903e500c074403901500f09510b2281c076030170f84059a803400340400c140b111088628401e80d20441d44114024000c01c00503071341d840450304403a8103501101008079826000c160807a010040c5100802a181040100002540f94180c807000070785040c008150b101c86000e0280b02d81c14418000882440b208803c2040f007240b448d80b02c0c0d5111715500005541808002441c01e0300651003500025100e17223683c00c46007001d0a4540041c40d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 506511070 1250 506509820 506509873
    0x1e120b030f0312100305010903180504200a0210090c0510022113050607050d030b10020307080d14070206041a070c06200a030209040b15071e0803070f110304050102 72
    0x82c0c8403c4d000011400900130340142e14002d4a5403403c10001c01551200e154581e04050b0085044c08000401108220f90501020070414140c40e21040c0c090412420104414001c6c5100740c100b6072072200b445102c0764510100d900031106448401041c0310149c3c2c461a024001080186004c1816802402a10020301500f91000c4284540503291b04c0060740c50b8100c21425116544500e00c0341840b186c03d4031654580840440d140701507681c01d410025541d205442c401420003401040f01d08030a0400e4000f10800c3c2d00d40c0da222462403410800080d5a034a08071810758055290000c1d500c1c1d01c00c880c40b0502c0c0039100540e200714500055441d807034060040a40583c444540761501d494149070a440038060f0b0030310584d00542d440828408010555104143c0c01e0b1181e103028400d44280d00e42c0b402103d2006601c0440301000b10001c005100c0d802e6480b4001401601d00002001080da5100402c542010039644510b0392501108080d565240280d02400780540e000e503030f0f038102c102903034000e800042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 506512320 1250 506511070 506511091
    0x9040f050f130302150406021c022b090803090d0305060a05010c0308071413051908060414010b0a03030c0b1008060c0c2109030d0e01140702011e120b030f0312 70
    0x6045d070906021241084806490060780812010444c0d0340c07a03006004541c100030ba080d030611640d0705d555016101c0001028880c104190350000c506c4405420407070780190008076007071312450091511910f03034420388018400a860f0100151842c50320412500540d20706075a401d0700700d882c2da5010b0352900e07809401c1609000040c038140c6170305003840000b09144e00d480d140218840e8540401d20041d81c600d100d06000015900a083c00084800141c1c50390094001074507071444d00c0c07844522401040002851a0010b07441d020200030f154020010a08041c401c0701842d01ca6503540070b10340001009406114001d40000f030100305040200409410120603a60959003003180509501205002d06407003000d104001240c6640c4d5860103004425821403241020303001001c90000082c00000004410f1a03e82d1000c6100401c1d07910402144d5103280c0c1da400c000740003e400210103040110481d4049090508001c800b200602f004108194050015001541051b14405042040920040644130311 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 506513570 1250 506512320 506512333
    0x71b12030509010212070e0a051518060417160819030e010e040501171c020709020a030e0105040312230f180618010b0a0303120c022109040f050f130302 67
    0x14050f0030880b10b40030782070b540c880c001031f10700400505c08900b0309036008511070800c04102d040c0451448044402c200031082d0010304142025000586c40d0003103800420f140000c8902c044008000061211842c2d8091184550542d59a40036140e1707401044c2a6181c15580701e14003079000074011146042c1940301410241e00c0c0d01c82c0100814100c84c1e0903840100b56440b0413103000740f8140240003070082c84281e80d500c0b50b100c44940102a5a480940c403803221400c2d40001c44100c01c03403007a800f40e0720603050780000744054101400d005007074024105840101c00e28180f40d0010f17000c0b10701702410841e4810141d421f00794ad42c0e8035201400d1400100480403954194a4413100810140a020301c03803400d1000b0000590510034800d803c5501c40280c0b070740145088102480130a4001c00041c408070121140881c6183e1080422420800c1014009030244e00d81e610100c04200c150016000c048420307202000f00c030128421400030380d001660740708100035291000c1a0314548403842804814020f0044441 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 506514820 1250 506513570 506513587
    0x90303190e040f0b120c1c061401090c09051f11010603020301050c0d0c030b0607020603100504050a060303031104030b011502030c030a09080613200a05030a03030203071b120305090102 81
    0x50f1402900c40a2015a5415004d28a40340c141e1604d12540305c030200402581e44420089130001e02c45c41866501c0d4080e101000040111036005506600e00c480207420055035030303192420190980048290201310490000b00342820a00e05011038400395000c80c03512044481025288c034005e64a0940555407248004005030310240205c600030850030311042d5640c40310000e0709040f651000c80e070004260030711410850703c1e038984050b6a01c00e0780441d050341c3d582e150b4882004e81c00149901c5181c1207030408d01000f4000d401039000c5011280291030038880d861116403a207040d0b1080380002000500303500014801495400790104182500d03004413845c02c000904e000b85140c03c40c50031140011f07001501402a504280003940d001801010304603030216003a5100c5841520b088203e41e5008015901860305544005c0c0000c018100941500e10609150900401950088030094041040c9404000900c0d001900888050343c04c145550451201110708034050031010f0800c2d403071036409000145 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 506516070 1250 506514820 506514829
    0x61005041a0409050c0112060b030109051909080306120303390d0f0b030c0f1003240303020d08090307060507051b070918051b030f060405030909010b090303190e 71
    0x2034426000303000405c010340140000401505503031b6011320704a818400100b21000312001036030305580002c040490555151071040801c0000c00001c0d05200d4240540381c020310403104019405003c0a40701e00040700310b6540400c1d076900c401e0321405413654001d080b01940d20304086c1d243c4003240c10340c9402c4554154162403124550016000744000715a09c01e00e1103841925481140101d4005401519001841c000094030f031455150a2f2070060400c450340d40314591007076218003c18a40c56148070440a0b490000740307000e04030342c00101d015100301d070f080380c0300b40c3d0007080c0251080b10800e0055251028030350326140a07103409041c0c107092110a100704c0682280f10002e101c0311074a0310000f800000d20f85118202502d0085aa0166840001c0d0b01d08003c04c0001c05d610f610103103080031091240301144003180c40c0030340c50b44c034031815402608148400c01074007100401010b08116004003081e601c40d00b1060b4030744211486039505500c2005800c0006100700c0582860340c0080c00c0600c1114110408074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 506517320 1250 506516070 506516081
    0x30a0b0702070918120c020307181d010506132007050a0302070b090109030b06030a0b040b15030c100e0a150f0305010e0f011703070203150711061005041a04 69
    0x11001d80c0050909200d540c0c0380d03100b0496a049400c210b100300d2a11502c4600f85c9003899030b00031040240c10907820701952410050360b802800b544034504203060707413101706100500401100c40070600310381001590700d0805005a40c000d04005109255000007020450b000b8044110f00800c003290030060b44110311042006001e2007402040508032584291600a080140c50340001d1134503030701842180b929933803094181d010f580d8032507100061611281700213032401590362030040851100e181000104108444414058042e0400c42e240168092040644600a807008550090300d00000303800614842e403070342148008040c051180d2039031104105c0c3c0e00c110100d00b4010100310203c0c81c0da20865490f114080c010804696801382c50704002031000c049180c1072040d100c100880c0c200380ca556100610896001550080c111135100000c5814040c1e80304c002c94000e40400e910304842024000085182c034420b00c2c06070304030001d5070300300710811009001c50710302980e03c280c090300c03aa00c10351603600c00c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 506518570 1250 506517320 506517331
    0x603061f03021818061b0901030b09070519030612020603131209180203040203210f0c0d0f0309020f1002240a0501080d02060103030e060f1902190201021b030a0b 71
    0x4000e01440c1c0306400042c64113469100206507031080c8108100141c0038504107504800b4840496070782c112000c01240030740300c6e0042c42035004800d44203202415030007034010982da241070507400001401014065040b22002c0c490345010200d0318141c0d0f40149400001594440302542c00c040d400d0989413240d200d41d9200300b03a90408920b1014040c8a0b041c50440c03041c00d0070041c00000d52a500c2c140e401700752251004640748441003494411400d00d80c8840c0c083d02c0c00000041c20468488100580b1140c4e901a002c8060b4042400e8070514080c0c00c1c4680150003d01360090071190105080300309014080b4070b2a8406000c6002c2d9036030703150009075400003456040c02406a0002da506240307041c00112101130340140b9013540000d400d80321558001c0b45181c11617402d820714040b1011a1004a00c1c20720510409009604000407811030700c0000303882e0070b120340361507508a90451082c0d1b6031060300510710040c060f0159010807034012180e88055000311840e0f4014068959000c516074444c0000300341902d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 506519820 1250 506518570 506518609
    0x71409130602191d0d021003061512060614070f0507090e0a1109010e04030305150604090c03291c1b1d04080f1305030d03140f0603061f0302 62
    0x81c507103070660f2142c1682d83c2d000a904941d20101125800100c0054000c24000d0044844540c0d41101234040e0380004010909019144014944c2c9040281410034040004a00910348000442c0c0070340701e03c031801200000c0400071403414604e92a02c0280000f1840e0458042c803400d200410ba0303441500894078002640d000800040109140c610b000c110f17409035142c040c1698100412460320100001ca4025805040010b0951180e140400509003040ba900741c11113800240028440d0441d40079052802e010341e02000407441c00c0c0258100461141444803030611303005000c85840ca40500c441d5018449a41182d0098140d982c0381a020358050f411009107500c20741c0304010261540f40944011000702c0c113000401d241913603414542c0e004944c8901090180400c400380ca0500c242c4490002c0d150040c03c641b4251440c50005001d050060b10b864481f45140300814001a521201c1a001d540300030003134565555140184114072004200a9a4640d0755040000168460707040c01d80c00c041342c803c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 506521070 1250 506519820 506519857
    0x6040605070b0105100e09130203030f19020109020f01180e010815070e100c0f2301060b07080a03021c0c0903021e01020a0215040915080708071409130602 68
    0xb021410588144d210301e000d102c0d2407403074251075540120044160300048807100400c0c4c0360a0003c5241c0b50207048002c1d0113100000d84480a42800d0026094420980b190600d00080d002402c90070307541c40060003500300710000007051407503001d02000c640c14013175446003401c1c180d0b80c1c045083c04500203034400440c0350440d99610300c2d4000d80c4003155a1095041c00c0543c085008480030500030000711200000300030580c1c0d65442003101800e00c110300036401442980d2242144154210003083d08045582290318124000444062030401c3c1c0d071070550041103850038242e2480c8260080d41c403541400c60300454107031030001c0070816071080f07090310f900a81e81c1070511806d620601c4034a8480105500956820081d40c1500340e90000e440c0c5c28659060710312040160382d400b03040c0c0c614012a00500780c40c90825000d001c40c003151303c0c103030411224144122a90280e8440b40c10341c13260032900400404107200181719049003041660a40c11108441c0701e80018a07480e01c492049801501c2500080f08002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 506522320 1250 506521070 506521073
    0xc0e190504060605030f01050405060d0212010c09140303030115021e0606010e04050c090d020f030a03081f060215072606040b0a08191b0b0304030809030412080d0b0604060507 77
    0x2846000b01410341800c1c0a4a0b600704000482c032424014401c0c248101e40711000640281c99131012030040326405440945280310380a403081c040e0800040744070000d0020100000c80d40600401c03007e40080242c0910700e56400c1a40c80c46500b45c010152006612076070413443c4030741000510743c03141021070700003524413410100c000403c014400491144200d04200900501682000466284003400c56130142801c4480c804151603000796802694903000b1922044117050b00041424403880768000c90380b2035000360200709000342182d80504001644400191049908041e000581040c201e0800d8600118106400d00c04124510403c9241c21583c00c10301045040601403038485c220211050406642400c41700d56494600343c6050000400324074044040c020840a140001e403641038280307031403645a0700a400c155005683c1140040d002c2400100300384c0003c010b403000d4440103807000d4160341c17051325442815041500e080c4801540c801404407070f6503516006000520355500c034207450301d445 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 506523570 1250 506522320 506522329
    0x11030412030612020a050d03020115140306063007090606170702010c0206060d03051204030c02100504050d15020d0608010e010c0518060f0f070b0412021903030c0e1905 74
    0x16940540d038060342c10f040000050356200c00b0b8100b0360382e05441c003060704611800c080b400b420303130100d800c402c40700f030301c00c1c0441c540c8034284d44042003a40c150b048441d6230301c0d0303501840300803208012110350102c50041c0300720320903203059480f0312503d413200308070741c403842d201c410700c100702c403555031101000c0344040e40c5014100510f8441181d102045000800240076034400117034842800524541c814600d0814660030540500c00744d403050030608260a16a00d0300e071402400d142240001603200740c500391807240d41e00e0720450482d001d5a0300648450baa14540c0e503248043ca90340c0c1403025a9017078003401190701c00c8525128917802002c91074000714072803181c8010b280c00c60354520554030400c8010401c0600c2001e425100c5c0c94808025510a07540b203801d02c104400701d000303500556031580b100217900d41c24001070f210709034040e600a8911001c0a010580f0980c1c0d0340c0c0804055004100e040c54036a004640245d0144907025403d003040050742c2d0762040000c100300701c40782006c6444c0354002e801340041e052 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 506524820 1250 506523570 506523581
    0xb1e070f0602130e09030901080a020c0a060f050703050612071a070605090a03091a030f0402040e030301080a170307080f06030c12070305010c030b2b080f19050301060e0402030a1103041203 83
    0x80d0000c0c521f04600b01d40000d1014170010810421241c0000c0e040d01140c0741044038014681d004041045079902d0400200060041a80c00350000380c140000701d0003925043d16000725603400c91004001042c9841c07100382c2e029240c07a0010031500c40a0013134601142c082d000340e501c82c0c0014406003190342d020b803401420140302508110a402107512050482d10f40304011203400c1011012112503540d80d900c00100540300814180b40d0354000030000052107000000e400d40411b215911350002c1c5100702c90312503131301d00080311664000390003c4040f03600e11606540643e04540c0c050280cac0e01c80fa2440010902000d8600d1007e0441e900a034001c105102080c894800c0e1820140b03001d110581009002030180144491a01c2c180c05003810601d0b5000d0042184114080d841400302e6110325141083c01170b241c01001c1c1e07017543e680c0100c0d510a40d039449801100c0c1a90250380341c04800e000b9007c244002500002d08841e1602d581d807814403a0714201d20b01861040b4421402c2c20020309080d80014140c68 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 506526070 1250 506524820 506524831
    0x402090703050c0a0e0a080a1506060e0105070b0411030f0304170a11060a092103031d060a020702120102031f1d070302210403180b1e070f0602130e 65
    0x185090180f00f010a0f4100450302000254078212482041a00010740c1190903941f000310706110b50007007403040201005808907400418102004196507541c0c0950f114035070140c20030300085040021800080700180010b410034003c000b1140400340f4500031174a89590f107070490707016600102e010400003e8004130203000d5060170307029000750042aa9020b41c0c0d62501410240700c4c2c0004100d80504a20913112400200107203003002205c08406510740c080600c107520181e00103410075803207403504007200b0315189003002584014a1903560b841c4100c4020740180504a91103040e21800e4003080d0801d00166008035541110441d4104810a00848907140755024800912441420014507130102c1e00c1198032000509000d80da41c400341c0c00d40407a00c0e8035951019003a40141d0103003c281644080c2404406240300070183d030107030300c500407030004e401003442c1c0c01920341c4501c038890340000394400500740742c0b8415001403400d0040c90340d80000b60b03008014681500d0319038290401504203049402038008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 506527320 1250 506526070 506526077
    0x5040906050d0f060506012a030f08070f080606070611041e0b0403110d05011d160b090609010504080703080c010c0806010206040b1b1b010b0103020a0903060b151204020907 76
    0x92040e0f0791140390500521101a200b103683d20000b58159019000c01580d0200743d4208042c1c10080c600c40b4960014010070540000c0c0504000e480118001c4c03041f82e01034110703511000c4c0305e00e4000000f203905a50042c21a5000710b0709108407400a030040c0103a90a041495002540715410554101140d00180da00d003800340b14810810006260b91038201c40c1600d4001b0740007589100b500d00850300c1040164001030181d864146000d031802040285081e800101c0c0003520b04920340740108080200c028010620880000c100f20780c13082c03500c10000c015607081030401c03600303156690700c516040181c40d52040c1c0707455500003151f4490f00820700c14050300d003800e0705007500b0710f040101c0000d60790b2000800091080003000d001c00e03842c5082c404100d8600800302a036503a90383d081e6001e403071201c0e590b0f100052036600b031200750159903009000b51000300005540305060a8555201c08000c4c0844a4010360454045410301501d9481c450040002118100e4072100e179042034814071000080051000040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 506528570 1250 506527320 506527339
    0x90305221503140c03070516060902010f0203090a0605071b080706181815080105090f07050312091327140d09090905010204081b1008040c03060c03090606060504090605 74
    0x103200040d06900c3d00201350303c8105481c0c0d0340d1510140c4503482410040b25140d15500f091104101840d000510350520070fa0704e1915400c46072009981d00c0c051606803541c015004a000d02100744104040c01c40c0a00070f0605034046007052480e410100c0141d009010fa0340c0180c04180311441d0000c0c1e050070400b50311a0310b4103500f4070384950950402035550000070b44684490180ca0038101140415000e000c0060082005050900c0003035a6000444e220702c185000e002c0f8000b8581c58045001010742d5402181c151500f50001c0400440c0c0c5104496120303d25a250110004080f0321001080214000b8540b018062080d00b4142407660084070540555805a00c02420050b4008409800c46d0184000816400864544240a80942e400caa540740c0b080e88101400360302c86143d0781c0c2c207408050b0340114110a40302021038008104581c040e15603400150200000b40b11a0f110a9841da0345140010322544241d803008255259540444002070011400307001003400391281d1320003040119045c122 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 506529820 1250 506528570 506528591
    0x6020604031115151f031508070806010b071a0403050403061a032a04140a060f060c0f061407020105150102030a1d0a0302060301030c03050d050f0904090305221503 72
    0xc5022008010710b46602d43c2d8411326500c0c0e00d56580c2078550f8100180c3c403c01014441d20002d005110540c851030318080c1040000032082c4003c250715007035070f0f522005881141c0c01d00e51382c940168050002101c01c25100c40c01090b00c0d4481082c964000d51087c0d031040c1e911880c40c1002400c3d44d03040016000301b4001e4140b503050310341d00050305a1400341d440c1e103141c44001b80d00c1176904514020411240c1c000e8182401e8030001a80b0a032101e10036a41c0e1070040140944502e600d510000c814040d43c004100d850340100c01060701070b410300c0c504520440000c0f5618042c1110750164071000c1d21401d015039100c8c401c0c405880d181007641c140c125028030055051900044e03000304030b407002c84414110141181d40310200b503100d21071860040c6802078802550b0356580d20744045134002510058a050140307480103008244110102d49511009551403400c1c18510004c0200800e4041e00480c18484108007103203032100f01d000c20403400301d1054188585030b03207440d000c018100404845801058a05005000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 506531070 1250 506529820 506529853
    0x151a090f070c03031b0c0212010c141818070f02061504020f0f0a0923010507150b1309030e090906040b0910150503150f0601051c06060206040311 64
    0x1c0e800762280c9005002c007001c07803c0135402800d0341c44072400100e10801c01e40c0d01700b982210180245c05c0c03003602c094040c44003803812a402ca508140200001450104582084d040348002030502c068412460501e0308411800041d005c1c6000c0c40301740d2040410401300b051050300f1502c000718282140c000b8200714982843d0034000c103c0503d0f01c5034462640481d41502c11178840c41038890049503000c0c519582d00055001030b124824521603001c545855901c4608155020580c02d010100107840e45400c0003c25912a40c10b01c0e140d01c0c03400b0f0059074407040c04030b207551003803c8401d80512000000454280a003001003501d55030031910f80c02601100300b070103400d81e00024490392194002801a119445c0c481040d8207003100c00300c10001c1c06007024a24080340285140080458100701c04690042404803000d0b0741c0802c0403a040b41e0100c40010002c1c0055018000400d003500b0108209900004480c0000c0b00b111041e800c1100140d10000801040607000300154201c000700c0801040c0b0016200b00a9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 506532320 1250 506531070 506531101
    0xc030f060303121d01090f05070f05011202090d020301091110020c0306060418050d03021908090703060c030b121506030307050607030b06070209070e030705010f050f16151a09 77
    0x959001c1e030b4800d505415411091320030b00d0f0b04107406009110700350860500302d20750115118140d9a60040c81000140c8062851040c1c049070410b0b12030b4002158514000c83c001c2d001000c04580006810905030700580c2c1c284100e10075140b154821040b00c0a44806106100d02e4185400307040d540016665a4a50f600188969002e1401c81e4085203020503100c40d20158008088000c1071885010180c0d20041d4064000c0d200c940150744440c050000000c038120303140300d4284d9900c1c1c02c43d003003c0c5040c40404c00c00e8000691009190502040c2071041e88049008501103124041241c0c1002903915501d815442201d60480070450040d810084c9545482d0745a0001405000c240745c3d6440701d0640640340c54095441240d0024511090b520f000c807070103004143c4801c0e0340b6119000381d00000c5019802885001000959940c0381401c10721000c00881d429031219082d40354914100e00341d600012005560340303100e13182c4a0b001281c8030b146080c6a40c041d43c1e50340c40355403044103002e041103010364801010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 506533570 1250 506532320 506532347
    0x9180d021c090612020702040b0a090504061512061d0703080403140a020603130507120302010912142a07151403040f120c0c080a0308010b0f040e070e0301050a0c030f060303 76
    0x6035540301d103100142c000c100c2650192b411040310b90300000c00003020b5010601c242d01444003400440091407002103040d0882c0240d62200b01c40c540071001040899204403541811802e04040521103056690b01d05032403540112606600098184104a1800503140042074a000207040c903a62a1780042d2190100406082e100307681e0501070b4051210400c9a400106001040804c001455050084c06420b0350003058510031101068203440b5403040603802100e45045003400d0512041d9210700c5514181b02400c41041e23503045a003441140410300c440f00c01440141e668800c2c42c50441c6000c0e000c82000500704400210500c2004081006c07009030300d0075030b41c0c0031900c50021101120203640c643d0b00300c4005400e211a42c6804205a040000c0c45000c0314000e42780d9602c10303a81d0380c049900c00c1c030072211500c18800082c80308000c4041411080340e04103680b810151806c1c2407000200342100d10480f16044072640301c52050700859014440c0d1445440024010b00c08181140c802802c20342d1091407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 506534820 1250 506533570 506533607
    0x515030f162904030f0506180c0d0201020a0203070e1e101815090c0e060c0d08070c14100609020a0807050f1e040303020105060d0b0609180d021c0906 66
    0xd40c60300c1d0002c040b04640481c50a81089521140c0302d05008107803496503403084480e40f08020100f201550346135032011260020400a22200c0e00030024885040c2c6003820413810352050490320300c0103031741c103208410180070422011603c500c1c043c010f203010300c2500000308044032104001e002e404055442d890b41550b000b800e251015440300c070090001000c0440e4a0050401c41c4880804c00800c2501b00f80d184000079a541810f81c3c024004000040c400e42e240100d41e640309001c41e8000501500c2c8150f4031070918107050300380d0b0f0034584921001d80d800320415003494100304150854110b1500c20000035040c400811401c2401d0050090641c200c060640f03000d1280c00b00b8020600c1011108642d03404d10141c1c00002c00e000c401c170383c241140e00180800c9000d9420b24001803440e040c1500040600f58201500e040c0d6512001c0501602c2c07000074002882204403c810302640a0301000000405890b90340101900d503101d03004031103400b1100b0f00b6501000007403001040460343c04245000411b51505 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 506536070 1250 506534820 506534849
    0x3040f080405030d020f1002090109050907051b210a0c03200f030409050609060a091802270a060621090f0302030a0e0303120403050c0a0203010515030f16 68
    0x3000e00040c00303964400d0b40e26104d14104c1c5102c165020480c0500c8600d0081115244100c070f070a210280c0c02001c4280d03001624030581044903140c51080240c208000307041c950314080c04d055075017000180c001d00010b86980981001103415a04d0804008445089052541401d60035036000300300d28242800541000385458019100f1452680d29840c80300c818400c46691592501040e910380e00b01e8801c0c159511310380320000f5980d043c5200054813840b401420306180c1420304504800404800041c0c070404604915960010303111912809280e41c1e0110703035180380c2003190320508031a4070000c1c1141d0005007400000c0141d40d0704180d0012003c0c2c103d0b02402d0190f010302841e04010022144094094440c074450b1405064011005203102846035a803002c0380c9603908141a500c9c443e41540c0d083c0901700200150200c1c0c400e1014000c1c2210364015140107048640000c3c0c01d61f4400d40d501541e0300102c00f102d41c1649030802502c01604002409029441d100344450001c079a0644141c1920000c3d40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 506537320 1250 506536070 506536073
    0x303140c0c1306140303030405030906130e0109020405031b030d140705150118090201050901050912010906020d0c030e1b01211506021605010509040f02160b130803040f 74
    0xe000c078805010000d05030403050b01e801041c0d107015044502c646104000500b1142026080100449200784d42010081d490141c080d02440a01c1e1301c4940e0704006500060b40101c0c41042603e81c60380208000d003005621107042c02e00300750400026440e07900000081001c020384130789000c90548400c8049040c80c500c154031640e14044948100c4800908a01503590301d041c1902c1d80c0629203040e908141c48012426038581d242001f29190b07084040d011800a010390116584110010200c0403400f4005806034004a89100c3c00e40b00340f40e404460307154000c1800445124640324005049810b440d0610906d0030f620110340d16082c2d2003448103801505a12490390070390090006c0b0f101203281880308074640c40c201002070002c256058a141e0301e010800300004000d480065100031049403103082d1501941b81000648039030303000380070307594005403100507000d06009548040c1100c0441c912100c10600014584003110110040c107c04082c0c01d00d4642e0008180e0180949500c2039004194a0300110f1f103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 506538570 1250 506537320 506537323
    0x5011101150e0c0c011503032a0605070e180601030b011404050409050c0316050108010b0307321305090c07050601090c0201090204060815010b03011a070807021504030506060a0303140c 81
    0x4c200700b20380300d507003003102065032940320b111240c003100d000317a4031510901e210201c0004008501080b0400300c0c00f00031144008100b041c3d200a8011146007046074002c41000041004004000c4105c610908014200007041d41c250141c60444a800d281900003a045580c5001a43c0114019503024503a603000181c2040003c2003111111007004080703800122044003142081225806260300050902000203500c8140c582507034000ca00c0d91b204c0c0e80758407110900e00c0114240308914460b81402481c00d11051116040041402030b000204000c04641010103000721041d0251a4403580344080007014042070303001c14114107444c500c5002286505000381d080780540313242c95001e540070b4500140005e9050300096042e1074500300c450039100b01d03a40d4802d14a1140800d1080c401c50003d9600341d407440101c00002401d000c1d1185080504003011900800e0340400540200202c0312000981801402000c011a0f03500c860f0440380000709904680e00100344804c5568045400d5030003040704500c9000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 506539820 1250 506538570 506538577
    0xb100804020d0602030f041106070803160e10020106140a03050706050f0405031e060a0509120904021c0b0109080105010b0a120b030f0633120f0f0705011101150e0c 72
    0x801c03c01c159104e08003400740d40c4c4440c2d030985040750070000070f92001500e81400700a40f003956400079015815903075592000c0c0c0c1062070340380c07035403081160800c40700b01c0c29aa40344041c0ba025055500005c4c88a082289880780c0b008a95441071154520520030800900001a01402e960562401e10344807802105000001c0c040c50f000154980101c5c002a00d0540107200042065590482168803035199140031104542040d00c18a0468219035201c40c50421054000d100801000d0001442d150b21900c460b154031003202035030949280c44442e0308210750303445035549020f4160003000300714951601c000401c1c981304a2003854144070050390340149800c103940c8800c02d43c00300942913071160340c80c0e001c3c1c0c03681b500c60445010003d2415401c1d00d4080c102161000748285a030400c003411040100c030304102a0700750081e40d03040d80748500182d4001e0403106011042e0451411001032640c64101000903120400c00314100300a42c5c90407145540c4401c2d580120030443d40c404c0340b0a0003d8982442c03c2c56a4407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 506541070 1250 506539820 506539823
    0xb060405130b120a0b220f0605130204060305060f1f090b04020f0d0f0612021810152c010e13020c0102040e040c0905042003150a020c010f0b100804020d 67
    0x403213407181d01740805040c1c070602c20003164410051052030110f5420280e554000e0181018024402810008480b540001c3d00410300d4000d00c0d003240302d15800034040c2ca41d241c008640c6c80e0002410320200c02c200315180c58100c19a01115510b440343c403444403003d01e0b06807164a64050700d039402c034080d540f41e03036048a40903420003040c3c0780e44404141c0088090011242d410031054500301c03001a03944103090880314140e03801001120604074a0189107a0160058902c0881281c0e0000003c0c0c00d121400c002c00c0300c2d03150b503250b400790604006030342011130341c07454401206040006140000ca80e0300440301440303204c0c00c59502a032507403140032440c001c0c015038000b015150720010f4003089031020401c003544124030511040424a8036518107405444084e24020f0080742c08000740180a049a8403111449801400310b40381d0b2070007454140100001558481502540021080304c021028040c46400091440c801e001c00503444010510118030588078104001080c0042011503550065505605 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 506542320 1250 506541070 506541073
    0xa0c02010912030201020c100209060d09061805070801110a091503090803090c1e0603042303040e0613060510030c090b04030c170613060209060c0f0c03010b060405130b12 75
    0x2c81d458040c1c000d40c0240880302041c0704411a5054880f0305000b1a81c0c0214060a400d062820500c00080a451500411690070345c0f107021420740c001b55143c904204600540040030030f079103081c1045003103448201001084402c104035058440e07800c401d64000315050055a0640b140b15060110000c151480300200034030000028010080d800145a03c046a01141c00c200c1d240720040d100001001c0ca041010340194040c13001501003152000031b0251103001c2c25201e1466000c00700040e042d548150400b800310942e280c1404800d0a011041446080b00010108010390502c000124098210743c26007040589400b20b1f00ca400f442901918001d10340326000070b80301c51700c03454050b9080400e0b000b05440102c00c3c125441001c0030007d400d0b80642e030f550911001d03003001501e48401035840004680d4110104010322000054104240b0012840550241000600510070982511411040341d4410030007030105024582d01c00c6031003c1088500540055404111b074040340c184481032a01c2c9076035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 506543570 1250 506542320 506542349
    0x8151510090609060305090705011115010e071707170c040906030c05011103190c06110304031101050c0705030f0307030e030d051504020f220f170c06090102030a0c020109 75
    0x4094015265005659468032100da580340c66004c118100c80080340c0352030050f4001c10013002154022614103d0410030f10040d215515001450f420440c0300070b03400210801c02c0b280c200b1000c1544014107268825032807403002082d04000000511100a841020461210307a5001c81c3e003440e409400c0702d0003030410034414080c1550341e0902d0445084d2a2061502040740407030201081e01c004000c45e0504901c0c40344100c0f10443c0c40c142103c1c40ca1b102c071411184580da031960b0882c20125a00558822807107030350303500c9049610822060940d50041d1442e10710000900c8020001080402525007054040c0c9415459942c5d64904801a0940062228030382c000000e10050700112030f08000c2c42900d0168441004210441c1070208900c00d02102d403178034400c00d012280030802c40380a101d80e4400003c9140006948442c4d80c9240259254400e81a0180d010800b00601400307101c134002d4800101c8080c2d00b01819400040d40342c0c86405007400c10131030701014140c01c40e8011910700b400380c071044445040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 506544820 1250 506543570 506543599
    0x31e03150807230a0308070c0f0920040b0405011407060c170601080c0d05150a0602010b0906180105060d060806040f020f09010609170c100215070504081515 69
    0x4851440f406680b16402c520a030300c141e1100c0b2014a1074200c038002d0b020030b80701c910795110018190071081d81261f09100d004c0340010b40c113031098241c2d0b015140e5000005540d00400480c4251510a104600350544050000300500b03049001520201c80c02030a000c100034200e1056144584a03800006241d10b29000003403036a41c0c2d03c41d8401c01e00c034412300f103400640d40701c1c0300c0152038610040318448140102000308994102854000309c0d00709489111890641003040c00043c0700408542007440182c0d501c8421101918102c0031046d0400e80942e81442081c0c111403551f00707085014000c0c240030300340000319164070380354550008006091940c10f80359603061a16007400800c0c04010300380c2c46158440d4101415142c0004014101c3c4c40503122203020758540b40d4600070b586035944e400d900340d002e01850803041e0b8980d401043c0c1c0744003450f4060448291000f540418a00c00a800141048002c2c070050240990010f4001c1040310718022003007c41d0303070f25441031940c051810085170304005446003076103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 506546070 1250 506544820 506544823
    0x601061b0b070203130b030f0711100c0f0306060e06030c0a050708041806141305070905090412020706050f0d0b282105101a061b07060c031e031508 65
    0x600f841e514960545c51035481c03a48003980d000543e03050420f120180003141172640a203643d00c29543c41c01c41070301d185002d1b80760003404441295110ba00401d5035005802c81c155850f1007a00058126170605003607200504000c1042400028007081c080300c00040d40703a036418002c82c1500c3c00c0316071094482d65619214108111848880c5d00b19803901402c0041c0459002c0c01102c07064000c2001400000340f50b845201a030005d0103001d0b03e80c400f8843c0503000403c2a850b0f105459106070b00640d1545180740310070900a20303018069100c1e07030802c541445081c002c8442c1804a0300304c101256408181c004403100022030441142e1511104102141442c1042c4801d40402404542d06000386100c80007010340005560150100002c1080e04041031058507101d03942d220351300844000c1c41c0d0704408101040880e0351580102d00e01b03052000000c2d030700c2c800d81c0c200b084044003800039803810342421060395501501d800c40c23032034809440d5802900b9510400d440b1340c2c0901c1c0d05000f62040100c543e590b5440342c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 506547320 1250 506546070 506546077
    0xe0c04031a06030c01080406021b030306130903090b250609060e0c150d020702060a0903060b06040302090109050a090606120c0f0305150a0216061d0607020601061b0b070203 76
    0x4031140c4104034590a006441c80880d18031600c005400b40144039020801120f4101c00284101c460a50134400368111041250700c1c0102804414000d540e00c0c280281081140060880c01001c11800e25443ca0002030b0b0103035440089940d1004500d40707410301956402d20350340e6203107661240a01d15100318018044250000c20310b00e400741c4410441e440c0e001070466203602540420b590001c80143c80c0403003020262004110b11b0f000f0310001400d10149500140e0744d81d010041c00f40004400100038810311100748101c110307100048800390700e030928650208849000512501c5a00b035654030000d150400980c00034045035a010780100300181d104c000c0300388840140c00c0192000600088081000d1003c2804641541d03000b0f0b00070480807500400f40421280010b15800d0501c1d0244001210000c605408100842c443e0380c0108140c20032046400d4540124070200089074409018050000d40101e50681500e40b03d1074000311510200001b2a4040840704000b042003810000f0464840c0e408400b6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 506548570 1250 506547320 506547323
    0x41104051e10050f010509042c06240907020a020d0c061103030415020705100e010903030b01020a1101080603161410021c03180807060606110f071208040e0c0403 71
    0x8419592100100714140500c00c2c042c258100340c1d00d82c130349486980500007400d0300600050010506000490881e4881204440c4000e460b000100300c50404002c00c0c406680d119a00e60300c44610b0300300c5c0865a08002c1c407a5030303c10380511200800304442034800c0c40345061440d0050104130301e00d00d0501e07040b03440c0d0340b0364421a400101c0700d0b00501c0110b000441140e02a0b5001003103250f0748035000d62a4802903004040840c1c03503200340301c0384000b41401401000d8042500c4000001e0000341410301a058889103e409811034200525510015003103a02c41303d081c031020f00e800081030350380d00007092030700003942c00388914090002c500041e070050170455141e5100c002c0e101540c6031012040145d030340711407080f4042610a521040354542c184681d00c000000c403192000916154955258820f2540c0040b4003911119120031007400360321f402003c4008041e600c10002c010718440c1c0c0010702d407145030034011100c000754403140e01001d1040c40f5060380d02400718140840d445042860982d0610303030041c8030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 506549820 1250 506548570 506548621
    0x509060f060103090c030210110d02011e02090d060504140109080d0b01140d0b1f020109020a2111060903030324040c08130c03050303270601030503070b04110405 71
    0x801e15480381c054162150341c8802001d121506607400c206100409820400402c4259650704030a074408224a4008000302d400006a10304240d9501403500104012401c003107004005480e41e80c5c803401c501c1840d00d80c101800003800c1e1035503d420030344210b41e020b0b14071a960070190a4800d01c020b550090421174022a81000406c80580056854451005139215040740038800a0f8482c00c40342c11460190000501d2081e00c005111201080c11400404400c0180e549510303d40071401e2404172030010b0b0441603030b00c0d291110b00400003001a428640c0080c020081487d2904080c1c407042c007076820351800102984e407a403030242103007021891007001c44411000c410800018074101803041102c0710200750350f04c01d482c1d03854080c002c40804800b01c0895803100c0d03001c0001f020a10903c0954028100c11808400402503801c0080c0182480c80300c42d402500010f00410016100100b1690760741d500c01001000d031303501e90510310500038518801941041c2054100440da22450b000c1c0e2611903801c45 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 506551070 1250 506549820 506549851
    0x2030a06140d0809060c12040b03090607030b0303092709060f130f0f02010c02030a0302061605090a151803032f0c061308010e0a020a0e0c0724050906 66
    0x40400454803075400c0040e05000f010031002c001803c124005000109005013212100c00102c801030b201c5500640c0254407541010051102003003081c02010341005039858280212504c000000b40c81e445030318609882043e00c3e54081c80c4003a0513580140382009540d102c40300502d412007010351a40e40882d26803c0001840001840e0111494460303180d540d003040034080f21044d0740d40c2e90103441d80d003c94182d0603c502000804c005a400700704680a0301c0c8254007404141c10140c0000980c1d401c50b0220030280310003840306210f00e0710380d00c04180480380c00500d030501d40004000161200d0700c40125050304d00300510404402d050300411310a480c0424a0600c11216442002042e031109501064100c40d03085107007840050310b411405050040c000714420007020303aa4134141d5007101c800b06a40005900b08001100940c644110214003c1c0f070b01e80d0b1864042d19000e20740200322321801c0300091003c00382501d42208048000d80b4074101c001180c0003040982410906182da030342d0116180481c04d82e100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 506552320 1250 506551070 506551109
    0xc0d1509020702151c091103010203070906020c0a060c06020d110703020f0c0402040509071d0406121103150106050a0c020907050711030c1e040207062d1b0e030a0602030a06 76
    0x103c99401800c0541c014503d103130265a400544040c0c24141e8081003808011111a9003e200842c003131001073711801081d51130501e019040501842106202c0d840610040041c0c5403c04000104181e20003001640e502483d00c0c480c0042108050038101c480d40400c00b042096000250742000441c404100e41005000908020603807240d4002c043e00003014001244035240030700030308404040c0c02001260310721021004101116441c0c2d00c400358804000f4948414010407a00007000c3c0c071029805042c850104005001410074103101d400200f00d000503002028034460400c140d200c5138010000704050628100c001c005400c400707425200c000340c2c64459003840c41c00003a050041c0358081c0c1042d0f2150b02c1072003000190021014032580040e001c001860010316948284140e0342c0010343c030507000c91381101516500302800950010304a103005e10f401c0a402c24142c00030a4001d0a1401c003d0208481021030701b0207180c0000100309900100c00d0011050003a0441c606840da0360a40022144c41b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 506553570 1250 506552320 506552359
    0xa1406060405060d020409060915020418021201171501060302041806030201121a04020a0c140a110f040905060c0912060c0703050c03130815010603140c0d1509020702 73
    0x143c441550000140000c00b00500745a000b1450030360140c0d0780000c504040d81c076000d0000d00c211095044003a80014144803452031481c08411038100c500c800c604220390203403460000d42040c09420540e1040c410415000b42040102c043d541120b1100c1070700d07559660102801039000b5018503004903010880a01400c00548580c100f100d805170360705513484010724910302c0100400b1744036980e180403980c0300e11004c1c0c9503400100429210ba0b51199010003003400e00d0944100e5188070140c1d103800c007860200c041841e85203c9264010100d400801d15242e800c0080d009041c4218018601e026503030401c001c00381000050700ca4108150b54210010b541d88501c15101c100843e011144018107011901c046445480034141440059080b130340350252405c89401d600300c1d568000a003903407160040e8012465a608094014030144c10148004401c81c0d400700216007008000da01040d002044007880d40d1045e401207092210886402101142c1321030f0070002075132118005030f000d2441c050880b00740707002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 506554820 1250 506553570 506553581
    0x6090a1e090c020307021503060402040f0e062403160c0f0302070e0105191205010221012c0402090403020c18061e150d060e150a0806010b09060304050f0a14060604 72
    0xb4000c00041242d40070b000307e900142c002405560300242d00b030001203101511200c090001d03004041603810107241840c100500c410b004156200100c4d4519001d1803682c0d524800e4035004004050004014000100221000c410014002d014032160071829020b242e000b155800075120920310401c026030303c80c03003070001d01040303d9a000d181d0b9840c40d204000c003104521985540c1d034443e00000d40303004070040b04610081040c00006440103103500040015009106204005104800b02d400b40340e070207000d001c08021001040a406140d5480010b010907200b480441c1000000811200302d54400c010a500e404c00112800c60281d011540740d4102d004500340c0350301c0311000040003480e51a4801100b14095080121071181041d244c080118102105001c464440d1207400c05400c06101c54508104130548194846880ca8114600502c60002144c0840d0380504084e078105560380c4403032511528000d6545c200648038007410119800704211048400704451007941241d015495a004002c100c86 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 506556070 1250 506554820 506554823
    0x10902030c070b040c0803040f090c03060b0405010c031403091e06090d0c08070506010e040213090c140d17070c170d0807120617010c14030606090a1e090c020307 71
    0x4400b40300c80800581c41c043c03155403141c491640b0b00307005a0b4440b62240307990880c0c2c00846000b40c0c4440c0520003881d1034803640f004884203250900000b481c0c07500780e500310b01c1503010782410400746070202818140515a002004032003000002d90340d18083d03c42c55141da1007071050b1000c107004d00c0201b011100c00000d41c0b60003084014041c0480e0070704000d00343c9101c0640c8104854041c0240402d50120304140700d03190080a4042e6040181e142900c10403507112100c90718880d40030b28061005002c100035100c41c40c00e40314241c0403086240e900c3c80004201c0755021a009100328040c1d81030800c02c28113600503014240c444c0c0d894401450321200088004003034600d00012642c016900101040e12a810140e088202418504d503418102c0f00d00400b42c6801f07403c0780c0620309840b82541101e010912404c1c1c5034964502d045139055a203250500001d20020305407621806001c81d0307680705642d0307002c03489009000072602221500d2020b03080020012061007498003142c81e07c4100501c0e14000f00407102c0f6075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 506557320 1250 506556070 506556091
    0x7021021020c030a1b0605010806071205240a05030109080d050903070503160305040509250f081b0c03070b0105040c0c080a080406060f06050d060807050a0311030a02131401090203 79
    0x1100f0304048804581c1d50500d40c51540716179004e803000c140c2600c1502d02802c0350a000d400c0c18034298501078080310181041f142d40d0351814040148030716103001c0d82c10028110a90804d003c204000c0015449030f103903005180d1652a10103030404000020001b00b000180e00c0c0c00a010995883d014640c990044042c0501903030020021000c010350540001c09406100c1d00700542400d032104042194001c049a4001400303025a49080000c044070030380c40349000180c41d11100104850b84e0040440d040507022696940b501c004541a03c010002662246031400040f80d0b16600c0500b09000704100a02c01d6600a0740f402e6400701c00b1a00c1505c00180284d000002030f032400f00c07000c60841d02039a00400a4440a91301c10f000301d0800d00e1107011000420540c0d44468951260314a0482100e05a511840040d40131050811103601c490001070200d035045015074000e8140c6c840820308003a10f50000075406100c4043d4800d001c00d80f6481460460a1201c41e81c42030303171b02d50341c0c6082240b0040d9030210700b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 506558570 1250 506557320 506557327
    0x50d11040f0905011e03020612130c0b0c0105090c0a061803060e07060e04290a0302041e0b09010e16020316080a020f07061e020106050310050609090d1409010507021021020c03 77
    0x40d190070f020301504100309008043c8400c8ac9501c40d42440c0c0780e180c214a49011001074411040c5070b09020701c680200650009e000c1090b400400640d03e00050f01c0ba01042c400301614503103621841c0403216001350f421510901c000800d0210158441196006405c0400c4107000141c000b81806e02c03409442d21709661170042c0b0880c031640303000901030004c1596648104107000100040c1c9640c02002110f01212601d81d820b1880e01d15800281d4503c1d10000c0c4c01948850010828400d0300450141c008020942d403c50801d51040201e08600c20304040e9148040400f101804011010004240c684202d40c29101b2001210f420591154001d10a010029100907003190b45008408282c0869141c00c0c0000540b83d035031000424205001c17501e10301c810390707070311402c0025a0800d0b00c512503001c0086009171a280d4000740014021052060f140414070202145842aa90003541280e1490750010000c8140c010100c0004111041900400c00324803003811640150644078002d90f9207030300c84900514217 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 506559820 1250 506558570 506558587
    0x605030a05042a090e0102030f0c03090f07030309060822030e0402090918060708160c020103090f1515030f0210050f040e061807050d11040f0905011e030206 69
    0x1424010b07000b540c40158400c0314414200600000000c2c843c1403020303400c01545801c203440202c40c03201c0501d00141c0d00400030402e204440e514000c0e032040305604040e8482d240c0607201860603024088400d0b1a20441002006240d044821031702200c0e00d40c1d48018403503880358604c01c003915020007460390344064410882c1c0024060246000c80c204c000d44014141070f89040041c003002002d80f0706d4800030b05040030706410598117120343c5901c00c003541020581ca0a0030521546003009840448041254000d010000c40e8400c0d08444013040d00840000c41e42c004a040135640b00700b4540301c00c8105880d00c809040c1d0034081e40c081a0072a908070b202182d501c0c519401b44004d8010302e800308000c1140030019000340c43c0307044029101038030080c0c803c00c58904e44942481507200603070200c215044054030400403a20f0380407007125072040c19044007040301c03580214060302c2405603070000380040d900c1440200300c1805580c0168101c8000c0e0400f0b04518030b00c0ea00b07200c0421043d00020350050010001c404c13 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 506561070 1250 506559820 506559841
    0x1308061515121b0c010c0305040c0b0705070b070c050a03150f052205030904060308131208040b0a030b03061603060b0333030a0308090606010329040b030307050f1006060503 76
    0x918030500904080d180c00045844d20342110011110800400c0d624410301040c0300000600002800b031036041c042c9015003075120300340d842406120f4080310f80310008000c01080485e40c5218001c05029003056022130300d92408126208014051b83c80c801e150020f180929030035405510f0281c9004903600020041d140100d05102c3d020709000d50b03280c44204000381e407035212442241d006502450b4071503110100c500c007070445a4401d0340b00101481801001c0000308003081c088a0444003801c03c401e96815035000309601410054203100d80c1401030301e003040280765505201010420385130750104402b40d1200381079119400180d07072034501c1c0c0c2e11402d6045212020902c03243d4030244066010410000c1c4003001034501032400d101280000e03061018880809401c105a94211a090030140402603c6800800c4040c0c4808260101d41c030540904900c540c566038084803540d8070150680782d9842260800a0340c801c042000e4170a2071040381c0c1c130702441d4445841408191f86103652072a1540d01c404440c2d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 506562320 1250 506561070 506561101
    0xc0d020702030a0f080306190b03010b071a0c040f05180a0b01180b07030908010504200118090203010e01150c060b1f08010f15020303010308130806151512 68
    0x1c0340c05208503066100031440d03906070080d002d44030300100c03030340c3e85099024800c129985494580202000110a208100600c0d040c3c90545841d111441e441e0100b40c101591f0b044130203198070f16051913050034000410000e000420945404801c0c0403e4150342c1c00511158503169100d41320240080c0c1c0109002c1c064031303004800f0040c0145800031380c48520300081c06250480d9844080e10300c40001e0076001300754005c03c01c03400906100d002003115151030380742c1200d801100130000c014400540d0000d00f59030700850380d014507a50440083e0f0980ca881c0c0c600c2600951080c0a000010f40e00c8000000301800284000f1500b0000c6030398000c02c00e42a0355a01c4040c1c654600310b140e108068012040c40d50600b412a40000026681c2d0035490b5450441c1c1103500e101590000098410650003031100c840d000002c490440760b0104060380c1d588600089544030500035000400740d80035040070b000b234001c01c2c92461140c020044601c42e04504400c5a07200360b0340304000d00350024030083c00006a00400c2d8958a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 506563570 1250 506562320 506562323
    0x2e0b030a02160b0712050106030b030d080702030c030406090e09060403170915130b01060f05040611100c2c10110a050304231e060a030f0c0c030e090c0d0207 69
    0x1100b0003030355581c0340102e000d8100d403404000303580420780222101c07860042c14010400c03428204000010800420388030244400f03450107110111f07000c1080e00d842007080319100c0e14280f0aa0b900c654030350701e008009407060700c01c0d802441404004201404404154a40030305c1c0c1c0340d280d0882c0d88145464001c0719000080c140981e50056512100030401030310b11091094006d545002208a2140303400e1742c50354410781092081102400ba1a031146410004850036506982042e0380711a000ba50300d20710b03040204403049009070a0142c146c0106400c84504e00c040321401342900d00321600e0400841d10054031246041d8080d40314030703040301814040c7d40310b05a6003901c3e1007901e001400f1511258a95846984403d80b403412410595012006d504908162200126840010000003401100521748100c00e46071141800203001d0784407600961181c2d9040102a00c148002d00d01c7d8100a0315619030020203801054025040c203400b403400e01580392080c1c0304c24400b5402c19801018200094000460 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 506564820 1250 506563570 506563597
    0xf090203060a030f0c0b07240504080313020f0a090501060f02030922090b15010306061b021c050105010b040f09140406022209020417030a08070e0d08032e0b030a02 72
    0x117000c603e00302960001e064031070080440146580c039034039591002c904034031000890189000c00b0711000454000c1160b40004888050854520481c0001200f041e0609062a8002a408000520145290081ca049400c0f5444100700701b2000c2c00203076140d00c50b0541041e84004d103c0d20801d04050f07003442c6004c0840d081c02c1c00044800d01540e401c1e105050507190400c8090074440c900c400b035070b414040c16000c0d1086140004900d015408400154042c05400a11807500700b0500e10f961050154642c0440c0e802c10000e00155039210b003541052390050284411100c18070101003290090b0780610440700ca14501c0680180d40d594617100000e41040c11040281400c5444c40b41d20810502d1848000d0034110100581e200e1400000320040c0c0005071400301940c0086c4041c044041d00510580d80c040c0890620512030f200c2100098040b52007604010711550021040c4840740303021079002c0070555400c481d450300c1e454105114900040319440340c80000c1e00b0400002d52100701c00e402402d1242c0c44100c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 506566070 1250 506564820 506564843
    0x61e21010e0d090504020a1e09080c0109180902061603080106020105060d020105030f0c040f1e050f09010603020c010f0501060c110102210702030f03030910150b0703181e0f090203060a030f 83
    0x40300d00304c2288c0003100103800205050070500410b0700603c06c241401c642400c00d0b00300c02c0e01e010b107500c40d80b991005e170340b84590340e86d26101c0d029515251b0895403c90880c03404891007541c28a005051740000307014500040d1b28140000d192030800f20410030140350161103031420750ba01c1600e44845007000034800c490030001800006440b505601e907001c050302226250042c04200032030031714000e51155119500c1452449624695038881103800742c1902c01074900540d840520191036800f5082c542c03092207a840c90000005511503116004988043c4103088038080000184012660b0380281e41002854011000a00f200000c0120007041d12620240036101104008a6180e00b9030708121007040964000d080d03000782c905403030321900d030b0300040d0789284107401d80c2096910303005401071040c01800d000a0f450074001625142c2d05860003031020b40dd40d24180c135607020980d14011003a03c10204031104a00c804960001207009581c4180c50190241205038603540301e0040071100f8880c01d80c0ca00038000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 506567320 1250 506566070 506566097
    0x60507020705060a120e190b040305040308070c090c110613170309010e0709090305040315142505040503121b01110712020c0108061e21010e0d090504020a 68
    0x101c000d0014a0202d031a200680c1101d8800c860a1b9000f0300c1000085400c044075101070f9420324040c0c50884d6400201c5440103a0303036803905031410f1042c0d0300041c2071800c01042d4001000040011031055912000081c00f560411100983e43c140e94042482d0703581d00000001400e80524496080043c1d001c1c40c00b844504000040c84559640140e8031440180d44680407000300990401840c4004d01c00c10303070100721900203500d0060140c000c0d4000209400b0320f01041d2a0704c132041d500807000d10000c400c85189281003a0f1800300d850b050702400000c18940014405c080b160043c8143ca00311030001d0090407413161001e80342d000d00e44c001901c1b44230303104240031101d034210400d100c0c2604000341c075014213668281078104058040c107554110402c66201007080000c59900881c4590010b0341640c00c585002c00140c0d40d44807050310310020782e400003071540128503240c0401c440c96001803c010001c00c4051014410b1640f101c00940c010380220f111401c080181e410a54000e000041083c50710305001120b6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 506568570 1250 506567320 506567329
    0x40f090602130501030c020a1a06040905010c02010b0405010f0b040302090403030e07090501051c081c18080702130204031a150d080910050a0f1b020901060c0506010819060507020705 80
    0x2125141c000c04200e850184144d5815129a110128090000b4454201150b4403901000607908001c8480781d07522000c0344240d00d49420401002d58000c0c000d00c84942c0c0c48000074020301001c2100c500c00c41c140b8000081c0280000240c4043d20782c1c034010b0600d0706086400b0f100c6150b6001d40300301e08140d44c520962034a0303c01400100d025001c505400303d83c1e545480100412008098948050200b85c514000d001038011001c4403801c5921403400702c0456403103d4508003e040c491509900c4c010010604020010701400410310b5a02c00c1381d0080c1c445004041080c22802940001044415400c2d80c1c0344404c0c40b141d40340f9500c008058501907001c01c2d1a00840c910528030302c0d045440900c01f0420910504e00780d00800000704c07080c03410904161201000a00e540520b450400c01c0c09040c044001c10ba4102c40303c4154640c0c0c0240041055503580c000c003c001960703007e1b050720180a06c00c00814101c0002c00d60608150b9040d01690160446844007402842e02509a0742507205a1200082175100c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 506569820 1250 506568570 506568577
    0x504111f0e061315090b120a0911120c0301180c03170c1507110a0c0605130b160c0b0906030106052b02190804080406030203100b0409020d0606030203040c05040f090602 74
    0xf0a80c000380c6145280b00d0005d062440c00c0d030000e50b0900c10910000181c141c8628026900400600d404543c61003541805400c03161b42102c541d81217040107136407580c0f04070005036001940c01c00b94020440400d0070b400551041154500c0100f0f9010515000c0010840c0405002e0b441c00c009400c0e0343c03030140011065842e00c034a1842c00081c104001003005081904021403107280810200905415107032944c0780044008140100d20511002081c2011496451010a070280000740c0005070342d80351402e501c010055100300c003200d0704444d000740801c1025050303003a1000500003406450469092003c142c503103421090301241505140c0e02803d414030f181d1204004551013260f40140e8a84859010006104500c201e2400f800741010900001410780011901240d01c10700d00143c580d11510310403400f03050542e002c01030004c03010402140c2d6040d035500030803010010300e600704541e9903182000d809901048401802034811010204101c0c1800c1d0008036005022010000b0030345c8052303640e14105c2c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 506571070 1250 506569820 506569829
    0x11060f0a0305040303180f0b0a090506180601062118020613051215010b07060603020d0506101d0a0c1b150c0905060a0c0501060512010504111f0e0613 66
    0x39159803d0005140d0140302d8032107203a124116215040f0050786894071100c0c0c002070700901c012001400a080d8040550000036060350000a443d124144420b6426600c480a064040d090107900d00001e6141d00500702050588411051401002800320f83d0710300a141c09542c5030201130007108003a005a4450005050300740d0302c4034101c034034a41054144030180070500407294140c0d020031005840c180904001c10b0440308030007403055036648285081405800c090740000d4110820700850b804002010904a200ea421028180d050350350b07482c0c4610024100c45e0302502448030f81e801040300560b8070381182d02d4400302428410100d03120b4020341d5103d00700d0b180b000d03200414a104080342c1560030b8007460003490701926041b41210308040010b50507101314059003041c001d0707200250080080c02c0d0020001000014055030144904e448180c1c0648001c81d0b0445000032050752801052502181450194507510f03007940c0d9480700403505440030307038800c4640360303024006003d01c411078a80f6074440d0b400f80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 506572320 1250 506571070 506571077
    0xb10030b0d0209240f06040302090604020717031608070801030f02120d030c09051e1309060216020111212d040302100302031306053d0807080a11060f0a 67
    0x10183c55645400c04400091154490710009140c12010b41c3d54031b05640c107a0f0740445801c1c10a40362030b40007130003c1c03081c440000c010080d41c4206441c5002400081c2d4883c0c0104031920345009040072045031400c0703045130003502040c001c600500c04559a0030701d20029510281200071110000c110040ca0160305513001340000c0d03124000f030241203520617056401010305503170408200c85040051081a005100110f02460300f02ca40304213040426040300132859003282e001c565a07035825090040c40d0304441c3c7c050340801c2c440c00b50081070b01c800041610184105105030f10030609100c3315151290b1007040302d516a1640c59070f44924013001010a0540c022007440101c3c2c0c0d4500d1403041c000c0f07d101110242c01854414820041c1042c80e2115050307580b984803c0000700e603907a94011280983c00707800d8441080c03c1000400c000300e004001c1100c1c1c146803000360400204e9550000c3c994481050044d114260070041a540003e60b01a4000070308550052086040042c13684100c03042e50016030400002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 506573570 1250 506572320 506572351
    0x18090501081905150c1c05071409010c08030c07021207050103110307080604090312150305061617060d02091e0a06080c091b0c06190b10030b0d0209 65
    0x41241007250080040380044400800302d8a51251921035445240981c2c00c40e6030500040d82d110b0040c0105c44c10000820703180704410400c0c600c040d0040204950020200d01e01160003120588008155030b0b12510513581c00b041900c80d90350300340007904050070010b5039000910600c40140e980c3c03184c840407001e0190051607402c2ca401c0005080d03440c024510140c000c020000e01906c1d60b0b000854a900002c25500402c0308407a03403404451800c02c8422180380c1c0d510300312410700da00c544c84203a1030450340108221000c075102c5e20b522181c1241001860b4010407a02560300c12034483c840c1900340c0c0018000c104581000c2280c02142c080c0000f10b40d02aa050319185032002045009800c07a50414040c8808000c01428010400d50711a50001001d101c1d0443e040083c2501c518503104003860a12960140d40b2130b0751103121240d560006448840003100d4400c40e11580c4c140038454140c01c0307039004090400804044106400a150f691407a41c0c01c030424103000e1000d03842d140c611034015803c2444070703180f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 506574820 1250 506573570 506573579
    0xc0809060403110f040b0d030e012d0f0513031506050301020c15090601030f150b040f021b12070803150d03120525030209030a0609030504060215060a03080a18090501 73
    0x70710036489042c0c588151b24003c3c030480e0030346460445002c7d4030390508041d07107800006c0c801601c080d40202c00c442c5864101107003c81c0910703e800224404805283c42d0207911243c1584141d803a4003a14029181c008888802003022030103010003e880088011000075110780c03580e01080c203a0344400c4945a0715404282540030f240caa9034a91540640c1c103402501903541541d03240c0f0f070b184141101c0508004010041104078501e65805582102c44c001c00c104001d0003a0700c09107000e50001511002a032501041c0c5000302480801c1c1001050031400d8402d10380481c980c0c4030b003150740010b000d40c2517405585215412035104c3c0003084c5a202c1c040d880c2c0010803990507490078180d4500070009034504104a02074840400b0950380307201c4030f00281c00c0145c7c503104c0d400301003440c0c042240f9020b44050f04110740c1e001410f400c00018005c0d98a40c3d400d483c0d51503444401059901002d440d50341e0002d0303440c0c6042012030101009040407414524000d000c0464645c1440768119071508101982030365200100b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 506576070 1250 506574820 506574829
    0x105040308010f06090303050f2a070b03093708040510050a020a1e1e0c060503150907050d050f24030c0d030905090702030909060409050c010c080906040311 69
    0xb80140038a1103100d1005081c8031000744805d100344801028480c002c1038240da030641d0b050a903000b1921344800c010980d0301240c4820550122408480d40c103018190000c68408076110031644500310b044002c10108501030414400421031f86200552080c604e40c03030403506d0305a2103415160600901819450307d040004202402d8a0b40c8400301c04e001c800c01492001da600803420005850b00a800c01c000c0f5907017410700910002e00d2641c01084109030400190300208202e10b006c44260264440f20101500e40c2025a624401610900d21140d098890306032203240c02c0307813070561100c0d0a2a0a0b8200709084007200d05a4100b650030080c015148130400c21201b0200615148010b0b01610141c4030070843c0300841c1d210201004c455018501180c005410715000f114420003e00c4040c10104880c507003050000d490340c000309100d82c45034641c140401c40d246014054214240d4000000d440b81c5840a001528000d222010440303013040c0c2032051440aa8407900540020b600406105036541742070030130003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 506577320 1250 506576070 506576087
    0x1c030b01120506100809070f0815092d010b100f020f0303070e090a060b1b0d020a150b0f151804022d43030815120304030501050403 58
    0x2180080c2c640402c01255039540044844026250b003070102098a4010165040c484e450b04242c03051010b80308001000d0f0000100c070347e40d62404110300ca85503214140c00d0340c2c82d0310303500c040308484184500b9010000803111104401240c80600005408000003000c6150f00482000840122303500d40d4062504613018040e0048015110026500d10324094001038801d224050400703014101c1d03100003440240b110341c00034018240d411031003903c072401d0004000c0d802d010280011400e000d00c001e0701108600015400e02103a902c20360150043c04007495050003041d68699559010142c800d12180c40c1e1181010079528004001d1940da1b250751440003601c0517141c600c50b05d4082d51040001005100200c220140307040c0304203402c2000040b090030050014020408074000c02c811700c1d100b8801209040b030380c81c2594040c400903940d80b260030120702904029407030409004281620000b400303ca04202c4541d0040c040105103100d04261520309030310355000354004482c03c1e036580003408185134110080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 506578570 1250 506577320 506577347
    0x903020307170607080f1f050402040b19090602060606070303090b010e10050102070b0d09020a03080f03151c0210020a0b010f0906050a0609090510120b01050f030102070203120703021c030b01 84
    0x34407054140502d1b0b00482c400020518511911500791002e140049540201e00500f0011300541d00d03242c4520040009500418524100480f020301d0005054003d4140c0c100310f4070f05401400840d40e820781406510761085500714205a500c0144000084041c0f1185018066650410320300c0d291145400c041d2071800e4100c28195801b0a00812420881a0884144039880b130703c0860152250701c00714840c182c43d500300a080b9a008150035800d600180040d40c4208144c2c81c0c15010710b4141030501c044a00d8040d002c0382c0500382d40c140c000c0503040201d0050f40c138000501c1202d5100ba856104e2a668006c2a0000c000803000c05804000c0340041c0e00400d0090704040f549600481e1400780c021700000aa4401d0076911501c0d03078001521030400510b5200140300302c2ca444900450341d4070b0481c024031804d003d043c0c440c807a040c800c0078040c10140f09882c0041c0c1c8c0640142680e0103070b2020307800389800c1007004504621540a68520094070041e000c90343c218030f501c02003132000c1100009440304e881c01d45d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 506579820 1250 506578570 506578577
    0x60905070f03021f140403050a02131404120509210d05041d0903040b0a02010c09091b05030a09060903020f120717031911090a0b0403050d0f0903020307170607 70
    0xe2015035070301d100c40c81034011116554210000071326401d44410907550491030350a04007280c00424003c4c0880e000d08083e1080f16034201c4900c1100c11502112550240031020020f40c10024000496090200120001031b080c503609220b40703d4005412100742d001440b180841440000706184810448802040c80a0800702d00742810142028034030442282102240e26202010500b40c0c0014021075000d08441c100c8035940320740d0594068040c2010401010019005003000510320b40d5a1249050004a020141b03d420320040c2085441d504040c00c00442240e0717811120000407100c0c13280710f65051098024151036402986c0d06c60410ba600529060300c468100203440c00207002c2c02d6a0701101d9010180f0a84139261403a520804031061040345c0c051a01d491050b24001a0b07800c082e02903240b08030341c1c9a802c952a401c01c1c504030300039840010191703401040b69040e45800b80c5a080078071803040c80d0a50403a552500003030710300031241e440f14803c10b9a4903000e003da41030502040390310000909 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 506581070 1250 506579820 506579849
    0x203060609040b2e060305010e070c020303040b2212140f06010e070c02030a0c09150e01050105161a04110301141503150907080c010c0c0902070c1206090507 69
    0x450f4003410050060024134100300c0c407424102c034019810815040d180e8140c02048165848840150041c8000c0c0104000303035850300c0029001900c50a40ca0060fa0341c043c01460038546085c801c21303d50b4001c0c070744c0d0320b1810a841e0744440350a07a1150303003d0010400b107201030040c1c001e541849450007040304c0c11600300b604651244999413000191640c112055442c54040c16a222181121246000080258140501d0614206010108200c5400d40301382407001c010500380300f001103c490f40c40d8403d24003c6034012004224541c0140054154984404002044544280c4d030712604503e030068034402e80c02000040c002849440701d403045031346000350020840c080b80c1d6480301d4801c09006000080301c0e040301428aa03580c5007400304d51a04c03110140c0b401d0311030800c542c025840e00d02c02d0080d0750062141ca0303044070081d841568480250b84c0c00c84012500503041207100800381d07002500030781c0c2404104100040e1080e84907502c8000d14011140007904859601c0c0650902800e039101c10301030b900a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 506582320 1250 506581070 506581073
    0x1409010b03130317100f06051c051302061201030c05060405030a060902190609170303010b04090b0d0f030f12060510030b040902041b0809030316030903020f07060c020306060904 78
    0x68080342c0d040301c070304207041d41411518035045451285180b03074040da16000d98180030003614201030798030070b41c4c2204082032081621007030b0465075409035501303480f05904a40c0c04e400c141521079210a40114003038240b4103121543d60042003070f690282c40084d01c8028000300401c14040c10301501d0000d442c040b940549410314110000303a46401001000d070820340e0b510001003c41d590343d016012600c0e45070344a481c060f50745000240080445100c1c91600209400340c0784544e0001004581c141c41c16050114100b60030426414000c2c911690703241c0d08100540c00480114022860340b9192910941c0c414100064944000780500e4050801c2e0103520300f030280a0055986a4403110b000b049241360020348400d0380030005026240b5610040d400c1498040005080146081c002d03940c041281c440008035214220000c6e5680f004a41882425040c401d1051a01e40329401c840d4819000344101c8148551054010f4102035081c0e100d8801300325000d43c20000c5003030074404150300c04030031140d0071201e1805 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 506583570 1250 506582320 506582339
    0x1103011206020c0a290915042a0906060e0102010915270f050d0908152a03060a1205121318051909020f10170907140901 53
    0x40300c0018806600400c840311141002c021945000d5080800030ba848080e40c1c4c0e150f40f129501042500042c1131042c0021807800d0002002c1c54041325080c0b07a40721503520358a49204101c2d9840100c07021101c2204020850b0f0300e010a41c101600c1e40300c50000c0d901e85480d03000384c40520340644890559050041100220710018100007403c1d83e50315002c01c800ca501151840c04c0362200d2200c01031000801403080a201414004006461041c0d04450403c0c40501054400c1500d5110380f00c0c041e40708029010a0301b10003001c040c6c010782400ba004c0940190403001d0404561600c4608901007400b01c2003140ea8034244080c1802450038100d1002e200c3c1407500c80036200d480d15001c00c81c401500260790380200201a80100040c0000c414407294018a01001c0c400b80000741e400e03150304101d400301e260309003459115918a0f594000e0469045000040a201d040061880000240414180d60401c00207500b108941b04100c2d41000c0d14545080c604000d90a01c032005045004002003001400701201c0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 506584820 1250 506583570 506583599
    0x5310c021b12150a110d05010602121204111c0609030e01181a09181e0708040605060303190809070b03010605180604030c061805040c0c020d14060f0703110301 70
    0x20071101c600741d5a1555480c4d80944058030190ba100d03040012283d4405c296a40824103980c0c0781c2c1e003941c00355110803903001c649001e8050181910005040030a0001e41c02e180c080c040701034003415600c0b40300c4012600707000300505d0200a031007070383e2a03101c080c007003503404140d00c00c0500c02400c083c02e080c03e001c4c481c15004010b500904901244403407110b03142c400f14034241d1344814001001c0c0d2540c0d0507040010824120f0039121905448000c80e44400500f081c4019907205003581c0c2c1d9170241d00c0e42c854032110050503001e05126018002006041c022260700c1001015000443d198200617007000b42500e442e01c8074a0f8000480544144010711034141d00c64200c490302c80306603640c1050014988001041440746d9071005194082080000824642020302881c8450fa6802d2501280781d0700c0c003d100070350b100070041a0000321545045401440d08909061200e03000c0c184d041545a0038003145071a00500ba10041100c4401d1400c0103542a41801010381015030310128906651500880322094036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 506586070 1250 506584820 506584843
    0x110c0c040b0f030105040c090b010309020f010507030311040b090906063c040906090b030a0b18070e072f0604030818010518100605310c021b12 63
    0x207448490390212079480b000003515207003000b0000c02442c10a481c06201c02521032055000003420014403130910741c000d201c0c0b490101d8000e80510030b82c1401d80011035203540107480c100e003070580e00d2030440c00b09149103001c1c00c007504143c034070160340308120002c000e12200020800b41c460841003003500701d000450002c4d10090101c420400c0c401400307600d82c042e0480b5400310003004001c03010400051100300c6410900c03c856010a040051411000130b06840c0e148031034001e8402484040840c5400d08509401d00f0540c0b034003030a0714030b120b0b00c030171400c480103c080d1003810000e002c00407080d00588400c0b000c01e00340c00e20038048100003800501110f403144401000a0140510309000400032811102c2501d0143c125500801041c9448654424184400341c4164044e03c10811341200310b500e6841804140ca100601d10060030800c8560814011000d03141c0100c51480460f58890700b40c02c60060711781c60001c54018000d40380701501e11140b90360640d1070340c5115100c20100c078040504085550030744003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 506587320 1250 506586070 506586079
    0x10c171e0c120a0c110f06060f0a050a030c0906081603120c051e06070f0c0219050303071103010c0807080f070201150906080708030f18030c06030108010c03110c0c 72
    0x103a80381c0ca419012402142c180710a1103000c1000c0000c525031035401100b8001d025210707808400700c0069800d036a0514482d124015501100211341140350031000100700510050000c14403c1c2c699001c81d07401c00090388212803207001e0030010300c4081e010307000c0c2e1780113045e80c1c03070050054800b95030011075115094400a88038a01c44c412200106110b2684580f840d60000f045441008040300c031201075007000590310300309005130404913102910031344880721008803a90b555403050a05030200309150140400b00420f52603540030005d030f00d40381400a469107602444450103d0003100702458250703000c00d1105010011200f04000807107400c01c0341c8540146090782c9440c040d03035070344006030300500311205007500b600d005007400034144845401840030b4520010640381001e58035800c8a54900800351921401c00060044002203a50278002103850360005086a5054000078081483c6501c280c00c40c1403540d445800c1c0d2100c242d0140551390300d0401502040f440c0005201e8000d856050141099204 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 506588570 1250 506587320 506587381
    0x123060105090913060b0103060807060806030f060f0a0606080408180a0902180a0e0103020d030804050c0a0303050703020c0102070620030d0e062a030103032a05010c17 74
    0x16449a000d5900202c0058032009071820031068014003d80d02c001c046441c107017092120101b551090140070200c444e013000a10300242052015560380c0d070010a0203806100750010300d802a00308114442c001c02a040c405110740c140b4401000584d845500070006000c6020280310005a042003210102e200c40340205040865150014108040d10741c0035070109800840d800340b4500400040b0110944211a04d602c05582c1360b00b0f092842e00c2c00d10010390301480610301500031a00030041c2ea41d11500c034a050303848030342160000030b015001903002070f000102c01080c80820140c0400a43e441035009000900f4414901607000700381104588801040c0c116422811071201010400d40d454582000010710501150911061b601c403c01c5132407030703541100e00c0d144032403101d44e030000ca0070403220f4601c50381d14503801d5031416035082c40d4243c550009004d00504140241c05200e506035403640c46940041043c005010004201c0641c1c2ca543c1080810b10b50f091010781e242d03078041201c485c0b2050030440c88 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 506589820 1250 506588570 506588581
    0x61401140f0901140d0f211e0c031704051b1507120c3e03061902040b03040809090606030103030507030309020f0909070306051b04230a270506010804110f0d0c15020123 74
    0x102d12f0352481c0e800004500310b40030b0108010000c0b602410784078a60560714482d4000c001006003101e501080509044801c20902d004036141d081e200c48205240d04011184941c5030751841c9001036062401c1c8100c41807a010030154800c42c1c1b0042c1d5101c1c510128200d04c01750b032040000d48804014118032250401c100711050800322507010355000305a00e07072040da12440c2906009420358004003606105540307910000f030315480d16a0559058035015035605040c0015550b003580140314000301641d2000240680c85c2081d0785001c01c003445220810080c01c41d20740b441c03500c82c0c00d8400243c080352081c0305003846440d10b0540c84083c0c404540140005c1d59084541e918042c410b84a00501c032600603110b054040384a03001071012040809441040303003664000b2841c42c1b0304582c3c1c01d8072440e001940400100300030a07480c0c2c181c400c0320382d03000b400103032034002030f00000b07520550f0707240c0c201c0b03110112640c1003000c0c0c4e0000c48100b1164810b400240080c20f2180c0758015810310030140401e8808900c0301044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 506591070 1250 506589820 506589827
    0x3030108100515010f0e150a080a0c0206130b0c0d06062619110d020a020d121406040b01171006090807050102030a0f0c061401140f0901140d0f211e0c03 67
    0x80c003091f90312138451b9441821180003050000d084078240e040604016200d440d2900c009040c42c40b0300d80314054003103c0341c601c2d5160812400060003501c2500000c0c84561501100c0c4e01c505001880e8a0700c07000e8a10200c2d14400000c0c8221301d41881003010400c04010300d13040c01610307001002801c1c01000525000310309441c0300c580500020702c540e052002c24400000c640005881e0758018007902c07034181c0c00900c6030002083e80c040c907528490070340100d03010581c0790802e60041030004205052410160708095038085100d90119884410808503180410006401481f02406014004040c101c035504102c0041c2d40c0f172183c600c052042003140d5000391142407181694054a541c0a401449020310351400c0c81c0b55540d0a02804003140a007028542080c600207800f24521000a80342c1d140b107a107403415000600d081d000c985a04804400d0754000000d02040b031003014244540c0c040c030303c804001c4443c813111200c948060810f200040041d40040080c0d8014044010030030301c1c2107030480780d0525048 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 506592320 1250 506591070 506591089
    0x5010c03051e09010801080616050705010b0927010b09040305090d0f030c0606170d03050a0209130c0905030a0309260312070f09211403030108100515010f0e 69
    0x842106030869a154240c602c2c200090015010980e18994130381d8980112540300c00c0f040c3d5014030740d083e001a85441c681e010344040c0c21500c0c061000011154040e50200b02034a1086442220b03203204d60005c4400c241100d00548585180c8200802c6806040d101007400e5810281010301401804189090a5500d0743c07026030985910001b202c217103022a180c0a046209451421030b0f1213803c21401150b110070301c00d103c038000c403001c0b4010000e01c50481800d80007020090038160815808101c015860b49030450000c5d80d50807000340003c0d820764580c00c01480d2021941100d8403075081aa04640172990000d085070a580041801d45c4400b03024080310400b40080c13421080160002185d001141c06036482c1161148059440308a01e680c60b484084652082c0781c081c0c50300c0101151545800b80c1d52100c002d2401d40c0c801c0c180f40701c5810720020003a00d540c100368081c0034130b64000c01c000780b5404418003407182c2040009440d50060840306c4006040d58621540700740c10400c4140d900380ea55543e03403200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 506593570 1250 506592320 506592337
    0x4090204020f04080c040f09050a030f0306050d1103010b03010506060d0b06040312020105060f0f130e012304050d0c0803060136030b1e0115030908030f190903020705010c0305 77
    0x4036590749942d00d50080d110140381c6145ca00c02c43c604640422201003034050030090341c0c0e1080c080c1041c102240d4003a16081120720b072038070406594101c040f8440c3c80b40c5000c1c0c800d16014208200313032440100c04260a596030824a54000d90600003403081e19100c410586204114541c80070417070072000401714186014a44c07000c4c1242001e034002d0303c01190191300090081d5001d6030301928500000c000c0c031401c90303401c1e180d09802c070211840410f9030b400c45610801c0c0085526001154200320a5660200c8020b8010192000841c0a080c80100801000032540e01d280d80c2c28038400060f125160075499020062541d414022409074811030480503040c40000d100903440704582c0c404c41c440008031903401d640001c68504481c9000f01c0c920a11440c240a90305040400382407050b82084844100c24800704c80300340506885201c030340002aa00d002462045801516507601d41c0b82c1780b40d504004070810044030b4005031400859402080c0d01040c403006480e001c0c21b0044689203203140880385403094140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 506594820 1250 506593570 506593597
    0xa02030c0d0302030609060916032a26041505041514010603110c0d2102030a02090a090b1807090308121609080a0f060609051f060507030903020409020402 68
    0x800300c040c2e010b9000d10b0044105480070011552030030140440f45d4416101580701403a9644280c0e2000c0c802d802014110454030b80c24459202030400b40100c0366140f21000022032140c0210340c081c03030400c2202c0413007100351106c07107095130529494403407090841c401800103030358440380040c3c1440304000450310001e000c03090801100300001008054208280901e000081c1450742000c0ea0b1a0000c06071039030580d2900c09010000c50008d4185c401ca06002d80c80150840309100607030181c29030388003941c4290207518015903a012244200007142400d908110084c628007600d0701e0340361b140c4040e00c40503c003400b44101c0e200d855124066400000a40c0700402210300081c144a00880350600c0501500d00540300082d2240103402c00c0d580c203c2e2034090300c2030700d61088a0a07004514900b0310365241c503020740c01c002000d03500c4600030300950310112210544804c074600410102d01c110040440204640c0c40e25904103a4a550000c103510740c0b51001912641e2503180d03020640d130b15981114540504e044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 506596070 1250 506594820 506594833
    0x406110c0d0c03080a0b06031f080f0109020108060901080318220603150e0604081608030a090209070201020c030405011110021c1803050910230c010e160b0a02030c 72
    0x350010440b016121003103002900d2000883e8441c500d0340509028060000c01e2241159980d111a02c100040000c1038140e0b4081c0410000312090140071100c80c14038043c00100c0c2592a81c00090b00091024100c0b90045504000400ca4418088107403141500038000c0310756240c11000000744510713026809004594045090000018140d5210a0403688101880000303a98400c490720212000ca02d00c00340e440d0480e10000c0c002560100081c8824020295201100f11064403a0100b5400032141e52006641c0d881c4030006500d8280400f903400710091000358a007184a0b0902500e9008502c119411f020b0402d02c06034920340c040c0182884070345a6981152561031402500c50611030081c2480f00c141e2421074580c3c059001100008081c039055159549015011410b1182488003a203810301046101508582500d01c40d0b10200800c1c03410440c42c507240d0440241f25801c4a411151000c440d911002e958001e40e0039406446080f03848506440c1d8440c0060203050b4150b00c40e034402207895000b5407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 506597320 1250 506596070 506596093
    0x21305100909050a09080703080702070f0e0601020f0f0330040302030a1214060d0f061b0201150305060610050d05010816080a031715030a0f030305100e0406110c 71
    0x3010001102d80390b410600054980034a64812683c00e071501401d1410100543d80220f07015a11081d00940588102c803112541c5e040c454280044c02c0d003000210010000500c40d40c2d40c1d04200114482680324054240c1c40c8180da80581e80b032140420315200d0940c00703c161052a03400c02c0b208000c40300095290400c80c40c003460005d40b0b9611010070303c004a005074001414a480501c6190128a02e01198559503142d400422034502590442180c50105064151000980f01d0040c00045a0410001e0818071616000030303080d200d0310004480035411070320341000495000184079030405400c0c1c0e410007056006880441d040d2203400c461b003036079500703090001a021000143ca15030701e0090b031501e40021070b2200c41d12501c507070405c030b00903000400968000340190142580c842d0080c05507958841c22008540c0803070300f051240c4c0c07016180c5002c0d41c0283e40a147e054010303141e108002c807100880b154241a0340d802c00000144c009000300d03a0354100b0403030b07204441c8d0454100100308000c80e400404038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 506598570 1250 506597320 506597327
    0x1021c09031b050d0806040f0f0c091e0302040e0a230705100503060f0a050d0b04021c03050a0e13050c1e0a09030813091122030209070302130510 64
    0x50382088000640300d8030080e1016082c00001400305078407001600e8100c02040040f14500c00180c2210391203580c80100d215400240e01c900000844801e0000c0340c1c0e104824400f0b400322000b035020250701c0c40d4110800c41b02110700b210403401d0741c0d4100c40001d4401200f220031481c0500d50900145680c410040240c4400f4008080c6081d0440c210200c0f1314003074a90007403040c0100b81c101101c010034400d02c0031440034900100745864400d800b8000c0c1000d1595800010416503403000280c80c5a1580c00a001c2981096000402800600b9030861070481150764010800d2250300700000070407040c0c83c00007405a48440398201502c413983c02c140054140741c040c0031410748c05100c0707001c0c070068120401005100a00191001e648071501c4140100340f0f103450322411680240114160302200803c041140ca015116000d0f2600e04100c016480712007200c0d0130080d42032140d440c07240c3c44030500810001a03844100c85644222640f07005a02c900c4c1104014502c402a40c20055000c1040110301510a07030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 506599820 1250 506598570 506598581
    0x30c030b060121091502033c071d06181008010807150c080c0304052b1514010602060a06050d1101210203040c03060605062106010201021c 61
    0x15a00d003103400e4603450010340d408101030308003c19a8108400b80703403007041194000c80b40c060090300203960110f1510940003c036801101c486c105c0750400030710007001c2120745e48000707210340c0380c11201d08900b950034225002e0420300401140400400e84242c5810f02541e818100240b900070303100c252034000c0012052018914560306500503080b4202c3c0108003031041e04814100d0343d100001d000300504040040281461802c614024403a905903a103000030b22250040400780301c0300e405151600d00701070800860000502e0496041c40d004400113602408a40c0c0c00e89103144d100d0000c86040e071035030102a01034013034078140c0f142d41318001d000060500e4002c12120305c954036032041089810340314404c201964881d0207000c2e02c0951515141c0440e54010181480506844480140d690400f040044240c0c1e008880450307041d42008010010000d81e07000d03080240c10704403182410813011b106401c02056440d0801c800070400180800c089900039030464000c0b0001c159240004205070b441d1401410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 506601070 1250 506599820 506599823
    0x803011e031b05281715010e150108040c05040c031b02060f130b190608250f140411090a03060218010c03081906050a081c03020f070215070606030c03 66
    0x72050414061020542e0502d24138100840000e2042405c003c408150101d40c5440e4500d10700c10a803802100640705481640208600340748002c2070b06c1c058100050500e500403109040c080760000b0b01001481e038030300b141e0644100b9035000a05480318030f01100035001500100c1d05180e000c1014a408a5021640b1841501400700410b401d4841d1405508140c48405014001031051342c0828088000300b144c1078610080c0c5000802e106448030401418805651641948001c44c1c003080342c803904078804150300400d0440240004540303011849401da100a034503082c400c80e0b0b6408980303500c140c800141c48080d44064100c268135600c2e0714220009500c04580042c02c0080038014081c9584100150000158155203505540e114500c8031410641d40c08d408800d403d8454401245940326850303c0340050407600010130070303100c42c0304050649280780010321040600402c05801c002d0002411074102c1a4180c40008000340302c90740700e03c43e038001c1c0240180f506042c40000400e0002c01c988031030599 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 506602320 1250 506601070 506601079
    0xa0e1b0d0c0810270e030406020d0216050d1104110a020d03150f031403040b1903050f1b18150909070f09141c06020c010e0a0803011e031b05 62
    0x54541009401c444a40c501c2400d0804280f6100b0001040c40b10711030b50860f04c0802400310b20010400d0440c3d042d034000e82c04c81001a8400040602111303810014000341c2d4851840c1c4030b0245051001061141c00c0d03040000d06021000341501e00305440c0e0781e0080c4c00345026405d10948490303600070006d440d2000150741600103400c018506e1000300c14202c44104483d04e80c05204c5003c9d01e1030741ca4100801c910445445140028080040d4051288005081381d0440e44123006848207144070160413103602501450a420400c010444a2103016050540400b40404015103502c1c0c51058404521341d404030150b004403585110021405060b0050011118226111207141e5200042200c801c80040201d000141c038001040102d03540e44224100c0600002e0000041c06103007100300e405000070750000b2201d96034009001075090704207200b0050030b20102000b812002826440e020490300041c090101d01e00400c1300031440c071945c1800c0d444011944407085010754a03000d4281607a02c0d0007031181c24001d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 506603570 1250 506602320 506602337
    0x4031b0b060a050103110a080c0c0f06040c1d0408090406051c06061a031f0915030b0901090f15150603020c01060603020406120e0c13050105031b0a0e1b0d0c 69
    0xc1d58080e0040c108900700f881e46c40d074140018400111403500b4041c001c0c0c5000c6004000310f80a5000034046042c581a9200080c100d80c01e2600e800c9940b103446a03c04a5000c12030114158231510703004041c2e400503044884d058407050260b0000d4002e12075039100d00d9100122180928610f400c0d000072401d014000da60030454240c0e80ea800d40c2d000720001d5414681d4020400c00551009440c2018500003012100c511a03840d84902111040b02c400d901560148a074452042042060b40d0034043c0c0d1107014003000340b10300081e41d42c60003510020010010200e43c03c1d09512844104150300003101071040b40c2c4445151591020054025440a500306c1d906500b04000801c0a60290007110111041c0765541240b24103c1e030359039030040c0031011550095010740d881c901c250b5640c5400c40c84000d001c103c00060b02c0c0d45003404252170020402c0c0c0c0c01036095902c1c88030291a41d03038144c00d24122440140312600302c3d50f4084801488025040c1120034101340868041030134134981d8019141c1240c03c1d15680b80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 506604820 1250 506603570 506603579
    0x12061d0f07020a030f050307090f09091b050f01030b0402090a18050a15092a02010b0103060f061e09050904030f08100f090209060d02040305030901020709110301090504031b0b060a 79
    0x8403403d00303081c080d000c110148020303c0d14030711a070011350b80a40d0529142e0503068464580e186c900b001640042d95083c2c440a01300244a904102501d00441401040d03203940d107000c000c980c1c001004084076052503a00c0300000e0742c40c1c51b08d8040781c0001c0d4000303080c1002561a82e6a40d240310014106400e10185410001401a2100d110725240c5400c1000807441442c600a2224003030144054840d40304217005601c08036060401c0001e900d00b01c0103800100c0c0c99003a0034001030803900140c0c00f1103405071500008000c0c2c0c1e5003003259541403010b4020340e4410080e01010584d0002d91641c015600408401c0405c0281a84a22641e4003029266079001c0d040c1c40d014500c00701102140100d140340c5030740300300c2044900410b6008092100300a40103038104802045404100e030050340c01510b07680c000041c1c805c07096a05010400140042c1d03c0f080001400308020803565000501131203c216984001060a02d070007455aa292408500c1010103611083c0c6040c5645020503100c003030144c11016070114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 506606070 1250 506604820 506604823
    0x1e2a05071a091c111e15090a0b130e10030b010803030702100b150d05070306051e060307030603061503030201050703090b0f040c08150f1506070312061d0f0702 70
    0x2407419100030304802c0e51010070b40e00b00e03d004a070385400721074508003040d0201054a4566079059204103152070340650300c644000344015030100d01411310b0910800c100c1c04849a4900c0b0444041d0b440c4074200a4899540341f0300203042d14600d41015514001000400c000202e240f00700009072032080d0034842c51030342d03a1321a0643d82d0105907202000761300141c460014001083e4082038031054000c003040903e864052901e28260b00101383d01403a1030700d9508010710b030341c0c15005210050406894120090385500c04a0b07c0e0303c080070031220300c100300010208245912a030482405190410701c10841e6107100c0f401081884010b01c011405035080600103078015001e44100300665800165289081e600c0080505015034014400c03202c0d070114603404a081c410401a42c52030030194507460b0401d007080080700b030742540c0003800301000d031450101440305601c400c01a02c545640c103041140d00d10101c12610390182145410146140000b4016882c0303c5c461604218055403601d03080440586500354102d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 506607320 1250 506606070 506606077
    0x203090d080c0a08190c08041103060402030604030f0215280c090512030403050607020a0b060a05060d0f0617070306140405060f090a21020d1e2a05071a 67
    0x8039440300700307003e00342400c0d005140780c0394000c1041d100406000c5200810404035030720003550704000784c540d00c108002c209d103504000d1000c003000c0b4001c28070381c5000d50000c1d0380d5000081c401010800c1c0b007164400c405008200104451070f41d854120036070300d4082c80c41a0215901075220070020302c800d907046260907007803141444061090707441da00000e00780014007000c00c440740150390851108000002c045803091240742c0c00740d11994040e1140c040e00f420981c0076010040c140380d12541040308100520360341c82c0c0480e101015031003030110b92400360f0390709000104130035070000345000300ca940107002845020404c1400d681c031641c000c200c20b214108091f02c250070304480c0144203602c100d011403e400c0b050ba600e540e2155806084901002d0345a0703921100d99010b0350841d28000403450000303280c580600c480c101c05145440d140507400c6101000d41e41f158480c03010042071011042c6140340120501e0842c1c020b003100e1440c6500090103503d001a541d05262207443d560707880381103150301d2010900f002c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 506608570 1250 506607320 506607331
    0x3061406100e030316150504060204030b1e1909050609161a070f05120414090610020c010e030f012313050c0f120f1b0604050901180e0304090203090d08 67
    0x4c41c1810340d020251103001c1c21000e41500d40c0d0380c40a003080c0341c81155020340c40c841e0b4803d0101503108c0c6e28520f8844030785035007c0c0c4916412000250a05203071006280c189030302503031f05c2042c402103110045c0303000018009210050018043c50f800c00605180001e0f044106a01d81036411011a545201c50011150001600446004c0810441002c125420320420105004809913030790741e25410490404d40d44030781d0086011141e1072220180e00d01d8402c0c103040d0721540950300084098000030300207440d030301b5914600781070200c800383c965007a441c100008251004000003c020041e50311308203080d101f07040c5c81c05699008051000504404600c035000001551020040464240074820801a0100001d4180e0080038002050421038802c1241103000c100000151014007484110250302660842d240c1e070160034108400c200d60784900207654111541c60f11469198140948104081c1c10441c1c10082c00744404a00842c4d003200c1503000754051b400728030071903c00d00c000b210250f4035100d00300c45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 506609820 1250 506608570 506608573
    0x20f061b0c01031e05090304080d0e0f040207020d0b040c1805090f0c03070e150a0e090106171207081b24100b09040608030c0a15020708160c03061406100e03 69
    0x9400c01c0f91345608020340210500c07040d2810f203902d5818040c507007040c016200300001c4003250240118104a5000e030280041558190329003851a004965206072212000b052901c030f07103001900340014106180040c148641000b80100201c000d0280074180030b0300d03c03415038080d0208201c0280000520105490300c050040d01c1d0ba1450400c03503445036280103004841c011032040702c104c4165a101469000341a0740300d0000d4040c107000f52181c0c01c441c540c1d0810441c0f06000d03121400352620005092029103050901150b441c1542e02d051380b01c1e80074410601c512280c60b120440c1f007040303001c41c00c008075050207501c0e41c1c42e080800156000c0c144056502c1c800038002e40c41c00340b2154a21200900c03150002610206299039184a0b003481c0d603010500c1c0342d800d500603004000030011031032500130b807448034031405604142c1075487d182082d120304a40b03210150703521041c0c5401c101820705240001d43d0021010840050000b0030702c02011000c0b03030514821400364461407103c50250410060406003e030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 506611070 1250 506609820 506609861
    0x40e0c0f0d06090c060302070516030c0b0a020a081b06070206270a021207050f011809020901110105100312020607170c0f19090503120a0507020f061b0c0103 69
    0x141448070480580e541a900c03252103425080200b0040c0c420740c401003c00e65070040e61824903040c8075082007010485001d002600901c1080404c0b840c0c203e21090300c01e0542c84c181d403007021035400e902d8134803103a0000b080d6510200710b8011464078555501c1e039100d100001d444007540c0b000c030201d840e50011110380a804c201c94111691090200c04d183c03801c1c0c400c01c1c04031707080c00e022500001c200c4903043d044440264001c080c00d00039030034036400703484401c0b00a003850381000d003001202104100c440d000b80c06485502180b0200329a1044010a000034805002007041d4108000701c03940c4030142c0e00080d15100c01000c072108001e03100150300d034880d000302da85074038020340d12111140f070a010150013020032144c18441820200e020000401c01c400fa6035406400c00c0c1440d070006084054954086031094109245081c40d40108278111100c0c42e8040c40d105a0b50441c6100144003160300f2161a5003003003011480324041000702011000101c4103004440c03955085134011415141c001880c181c5246100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 506612320 1250 506611070 506611099
    0x513171c1d06091206071e1d0402070206040303020f210d0b040f1503120f090909051006060203030f01050a080c060d020405151e040e070e0f031902040e0c 68
    0x8031091685000c001c242ca464502c0e910005215443ca4215041d11508401c09100e696a0001c00c0003a210911401010120048000240c520341c0c40030040d0320084020302400385d03582c0c0c0d65070440703204550042c1070549594403424025541c50002075003034400c0c4220501d0041044012061488441ea4072042d20700d00407000002c031000d400250549030b0032640b511001541ca4156009810140c401d00c41080c02e40340c070394240740080400f1207071a5403c1c842405000908298440d07510402c1d1105a400400d4881161411500c0d01040001d9502d10b80d20b032900106a140d03000c0005e40c0203140c0754800b400c060342c13038600300b00c44030860f032003001216400007508071234504011000c3c0920302150320b00103041c1a51200840c100303014049810300f110000145030b01c80813031858140188655000007080c10b280c20400d054120003c017070403210a12800c40480201a51401c4030702d0801500501590f403885120500018a80d0040d80100e101c0d41c10a040486034040001e403200308004010108070042903c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 506613570 1250 506612320 506612357
    0x6050d06020c0c04230c0c280503130603051503250503010c262701150b0c0c09100302040203061207030b0f010801050f0f070513171c 59
    0xd5014403500d0040c280d030310400d540c3d584101601000780540e40140c00015020840c84c1200041c034101485200b1f0040c640140c0703000a18a0f0620524600700780030070307880d603062000401d219030010450f120000d40d062402514022a4040781d40e6510244020344035105050307101c0504191083d05503100355890101d100f280e08109424040d0390308842c0e9165214400305e801d41c0c3c0340b00813074008a4071281c0708020708110741c4405502450611101e52841c2081c842244100c00c00700d1074003040c141700c0110102c031080298444420070749407071180c0040a6680403614251b41098104120f2802041400c040034101039a030319101d8011150007044c0c80341154200002504080c05079604480203c2034040300c90360412034900607600814910401d45420001421190016000402564184024030480003c0003003030907008200e0f5507100d03046545085d01140e1030700900c04d14150342600d42c00c0008800340a003412071149001c440c03e84d002c03030310b1a40d071100103205052564000202c5070314941140501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 506614820 1250 506613570 506613577
    0x50a08070813050111210405100218090a050414031c0e190c031110020303070c02010e03120403121107030f05150a0e010605090106050d0b031e070e090106050d0602 72
    0x5600300786440e921043d1200760031902070001d001140da00004a0344026140340300517a901710100c4100455604c0e143d03440e40e8440c004111507444117600803031000d6162a070310303580e0164404042c05403179a0745017204113440900015501942c0f078040713815000040e000d01000f16007040d9030180601c1c081c05035801c9000001c0454002c3d4a001d8000d01038140e40322000909500d10180c096910f480c0c2060440c01c0c00311282c802140b40d50300c0346100060700800700790040306490f401043e5041c6006800d05d18001612805903041c4060b50601903000209929103001e07025005480c040e0441c9488000b00040580e510100024101072035800201d00b0000903405001c48455988900d096403400491880582104103050314028966500c6040e0a2140302e001d202e4500208000c85d000701c00c139454000003903d20303c582c002d1447c00c2503d070103203145241c9040101000caa92055440060303100300c0d80c003e54403074031030740142409404031002007092034905000e03082c143c900c000e02c0544e50342081c4d61020300951 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 506616070 1250 506614820 506614831
    0x110901050a0e030a17030907080d09090b1813031214190212070e010e03070506220b040b0a02071d010603020c100e030409060905040819020a150c0906050a080708 71
    0x10a213240d940006002c450300f00340c0c200170365219a44904010b0300ca40d0410700150010605030740b10f02c482c0c1c01c103e548603c540040340c03565040003400c98203680c045040c803440c008001a051400718184801507a804a800416900aa07150030040081c08142c4055174500c0100c02030030403900700492400d0466144048034402070500041c40c0c030700f019105541d0580c00300c40c80c401050482c11060307825600001001d1010307008602800c0d4040c100710016240c0c2c003600f2107000c4040403e00811501d40c58580e4168054800c040110ba25243e460341c00c80030039842440300e400140030300000003e10b20300525001c9401401d040c2c400301c82da0b084c40c000310025041581040924410401001d2040f0074500c00c0c0010003481101860f5a40e091200f80da054800c50340c02040400c1c501000c020219580c0b0702951610350401c241c2e05458100404228903014a0303000242c0640d00980c1903402c1c0458690020041c0b0700c8a0315604e00d000d0b03655005542074060307c2603010114904c81c0c0020034140c868510300d075000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 506617320 1250 506616070 506616073
    0x2030a030f11370b0c0a050c0106080307020a0b0301120807020105090907020d1e0801091a03030325030504050a0f0204180c091104050a0608040609060f090204110901050a0e03 77
    0x204803034042520300b41070212003040300101508100340c440c200720f03610340d580d110040c024000402c10380d0b500325000710018012600310402103000c082c00d030301c01c804440c034400c00300b00288180d5403140b4001e03849038000c040072032194000f03480000c2c0000302a000e0b01e04940e2a0640c40c45503800a48070b881460b44540012410030004118041d0151b44051656008107600d80c01444402c8900d08041d046c070050150070001491030304e84400e5641da02c8818507056940c1030300301144843c170f1074407000040141600d443e68103000c04010800c0e42d421144281c22451942c0c08400c14610741e045041d01102c005480c042d10301e401541c44031000c5011088050701e8944054000560340a0007450818140368045c000c07601420108410008003009000e03100003000311048451a151401c400078260718214030817a0140042400060f0610100d5480341200a400a4052102400c918200402001d041030100e103e589055000d094080c0008103540300c251040c0c56851030001000010707103104220032000c5030715 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 506618570 1250 506617320 506617337
    0x3070303080705040e01030302010f0510140118030501110a030b06030103020f0d0219150e04060f060f030e01050c04051f0e0607060e0f030307110a050318030c040c080703110702030a030f 82
    0x282d45d021740300f600950090780000741e40440142054251130b40036080c42644d40c1d0030f0300180016203000022007846034090030a1041c00d05070091510020b8032036030010f01035510705a210090484104002e1000c03e61954003040100c0749a41046400d000a0201a4000007945081485d030b091210070010a203000a12801d0440b4485052948604140d0003140100005a80c44072420b500201807440d00c20080b81c043c0a141d080011182c90341c82144642c504001c44e0602030940103010703070b003c0768010150000a0000303141c40c0c0c840650680c4184101c900480660b41c0041040c10034252a540702501a600c0c459010700680810100360003038041610001c1e40d0721100c0140c00b20401c607010b01c20081074043c64492400c0310008d050300e195a40ca103140c80c0c020104503000220044129044e2030800c441280240c0501004680f80508166207141c10500c0c1070145803045401c4400307940f050055507410700c20303004a02d03442544ca0180e40c10094060b03000c6d07584a00040e0103401d9042c401f000d9440c00941 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 506619820 1250 506618570 506618579
    0x4090206090a0b130b0f030f06120d08010302090a0510090c0207050a1d0c191b1203060e0a0b13020d110f0304030f14030f0c0c0f030c0106140307030308070504 70
    0xb04030709500c40400745000041c40d00d0b6000900b1075000050480402c1c1c1070a044040d154040d4510000f030140801105000009201c0e030703500112040e4144810f000c907025184289005044007100b8002a44500b2001001907800c051754060300d4803070b1520981205001d4540074040703000d000211805015070090b0318000c10141c07105040706c8010040364110080b4001b00180001c81000041c1505085070720030800c0300c10200742404100b18800d120701d07051480e1006408064120180c0c0c1c80000c2129100107000354045600d0382003002650040125800c1c292603562450044030341c41c0031000d40283c181442c240801d00f265001d810300c03911024003c20000c88845000032240d101c400310088100303000c0244003e0550044001000c410340c3d060850f2040c2811001d04541c0c0001000c031100b4075a205c0000301030681c134506a603500381c481021280c01c8181c5030241a1660403581a100042d0302c7c00c5400100703582001c10110b10100044e010f0001241192003c491034100281040d0030300100b0000040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 506621070 1250 506619820 506619829
    0x5090a11060c19110a0305210409020c030903010e010509070902071b06050a081509040b040c0b0d060e090309061b0c130c0305060409241107030f18030c050409020609 73
    0x401d00f95980c100e081d114102031030302003420b02c00c001c00b460141c5480c10040c00014400194048a105002188500c4800000348440280b04030f81200200c03e001148640c60010004003038070132401c1c101d0080c4070313030040140d000342218805c0f038240701a54080007040003036418690082580601624582244c22044501a40704e000d10303a000000040b00001d0b1001c2d101d50009c0c240742c000d0380382c501251380c060114000030b102820141015011175410000308007009070210310350008141c0c4006068070f4100c0c0c5c000e54001060345105090880841e0300001c2c2d81c000011007100c0740440001d100c10b040903603001e1040404068200c0046451040301c500c0da80a0b81c0b82101d010301d07195080e0007c1942c4680800c0202503580141406000d01c0c00e040c0100c00140d00f00c096684404100b0a0a03003d4504060340b00010b044951162501400001284014103074400a560100f446607201d98000380940c10410030302d00e07141c4c8000b80c00004000414070252030181c005061683c002022103007031a041c100040d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 506622320 1250 506621070 506621083
    0x201030b040903181406031506190509030d08010b0a180b0316030b09091f06090e0c040c080702030910090b190f0309050c1309150603021305090a11060c 67
    0x3d60200d0548400102c0a0142a142202900f00100d801c012205080003088890001500e0408019000345c0320351056140c0c0015242c1c1d5805802055240c264203141c0034001e58000001c4901034000d010107814894001c0300300d94100c0e80c1400d6040d180c003000322811101020031391000c00302c095420200295280386803000e140689500720028600405040300603085910b04030301c0030300501198040140288000c100c40000906850403503820181c604450802000c00c1c1d080315200a140119046040900141c6033b46c0a00099801b0003041445050a640074201181c1c04001a40304110b1942d00e170418881e044414034060904004903500d4075000e040681000070130b1781c600f80b80c4043c29010141d01050240c00c854043c20300300480002d41d11282d80328540000c1190054450b482019041d070195440358040301c0d04501c3c0f40000d5801c4400c04000f5154034401030303120b07103880f0040c07a0503c2041c0c0301d101e0080800c00003c001c15107042d030703490060048810200794010414080ca0049a50a0111 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 506623570 1250 506622320 506622323
    0x204021608030a0c1d090411220e070b04091119020105150901080d0305091e06010e060405160c060b040606110f07080c01051c06030605010e0f09030f070201030b0409 73
    0x30315100c3c5801070401089072002d0b4010400c1254000032001301103000c559007400c0e003d081d101c801240c0c1d104c1c02c0c103c00354065005d5958011103509451400d119110b50600101d03940071a06019510000808507034401c41c50040860034101040b0030801031007503501815001400a80e441d0900d080c84811000c0d545200c070a07030026035101d4041140c007405c840300004444504441d207031001e50400244075900e6003901300c040c0034035603a42c5c040b030070b112000c110f01c07001d00c51614510b40c1c8140d00d078807529840c3d87d03080c400c610080c8500c00200b0b070140360a024092082003510111542c03160365040407202106c06417400e442c44e41da0780f50701c480180c6940c000c0034003038046510381c0718001d00440f0034540780030380702e4020049540003844140100c141c0071400d00000074003441c04d26180d40904056030f140f103450b114814401450002e0000420400e03030003081c101e0700c10080f040304035510403c440b400140e00f280e04003240d400401008408540f58009042a54011701d400550300c0e195a000c2000c50b44071440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 506624820 1250 506623570 506623583
    0x130c0e2103030f010314010e0c060a09031202012403051f020904050a02180f0f0d150e0c0a0603020a080f1023030f03070506070c060f0f0605040612020a1202040216 72
    0x14000e06c0145101100752840b554001c100990f0b4a01d0015150600c4552480c414803000603035804051154280c68080c0d0f0f0407601e16694904081c4000e402040c003500d840203807014002d10b4032500014141c49008481d0020042c01c5d0501c1c81036101c00507445c83c1d81c03003018131a5082c02030318540d86540c0300e030900c503420f40180181c0d101040030b140d0803403104614080f032050f480014400c00c5c0d074a401d40750400010040c1c032344052019203850a44c80035009058202c0c403161401015411100d000140c03560000c0e0b00f0b0b14240f20b03854880310124164800c00c1d4050f00800c1008020420491111003400e03480086101c408111a031901750340341c00360900c064020700d080d02c05000e01d1b045160070712104500784605801945000743d9a40c0c1c440d180d06004090782c1c144258400d104003403145980040583c00c0801c1d400b0070038000f8071032101c0c00400c0d0751f00070300707008070310307002c0d000c140000301d00300c10114503400400c8060040d14264411080d0541c1c6581260400c1d001c4c080440035074a00341d13511443c1c40c030455 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 506626070 1250 506624820 506624851
    0x31003020f030c0d0b0702070b070501020d0c080103020d1104020c070605030a0606030204081e3901111207020a050d0b01090b0613090e0f0d020a02130c0e210303 71
    0x10084500ca40034100c1d4426082210300c410107656150756462440d80c0200101035990f40d41d00182d04250342c0e40e202c500030240c00203808080003010b5005009448100d02c0400c04d123500072204030359140e400d01000790030281010f000004501d0080880460b040000c20142c908008400e00b28100350350369010b134010400100601820350590300880c00a040f41e45011420b1070b14080405903500c0c0c0f07103a002807072031100d04640c981921051249184811000f054029164140c5844191440b204203d8403020643c401c8044040d40c403601201c0b0128050900a155640703044020490981c0200c0c02240e10000b0111f00007902e03103078031040d00015070090544900e158906000c04c420743d24201d46031031040c0c400304200314102103044021001c7e10703c0f1020002d06030b80986506071509803441d01130702551141d0411a070951b0fa000511008040c400d4030000d10f81000d00d40da90042d41c8220742100040303007005080a402c3c3c14070300c14005e00c1285006c1902d8040060b1419107045500c04c0e10070b88040d00070075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 506627320 1250 506626070 506626073
    0x903031b070f05070611010b120a12140f0d0e0a230a0c0306060608100605070f110301090803150301180210050d0c090303110c010e040f06030b010803180a1a030703060803031003 78
    0x80c408d03507003007001c183c85414020106044058170b840340b044000708000d008000421145108441049078030319803190003556814a030b80081441e40040703640115890800303c694407280c00100e0300d071030125403240d5102c00c501e01c00f41403843c070281000001052071041203440400b007400700d500000118040d070000204642031400040554200408116400d00386860808c10140e000003124222600300d810b90490650920344103044002a00070039525600b440c0c51101803221960055008010980c06240404822000e06090764403141004800d0182e809880c130260504c0401e51031416054540a45840e80b030800c91011915426040c100107442c01c1010f00805d600800a105d182651000038100354800c440000d080c06101c940403401070303483d54203501d80030020385c006202844c2e200102ca649980c44600740341e035030303000990281c10070003100700502c540d4145406480143c0e150500d00b5117031501c81101d1414641c0c000341c00c03101015a96000000c16000520155001d0f2840350000c50300795256 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 506628570 1250 506627320 506627323
    0x1180b090f090f120a03020a030e150a0609090c0b0906070210030e060a02180f010504090e210f031308090a06110f03271c030c0b0903031b070f05070611 67
    0x7007103d207030700301c0c0e00014031029004600302c141d44400308546400b580d52400070f1030440c040d02440c91507032414800c001107100d0f150030035600745106a00760001000f0595071580f030682540c4100e203007d407900c1400c3d9014000303071040c10000c004a50002c1c082c280703003008603404610070301210001203001070381c0e881c2d10725060902884020381004903218158105120f4007030404803412425011881201402c0815210740d001d001954000c103c04502045512913201c840358030340c410b0040d200802010b80385403000314125101690030031440038100d10304550714001c0c031260340070403103006035120201031207032400c2c9943d158007450280c00c0c00d60300c446101c0b2007480031502c0d00c1c008407002035035600184215145942d0003200d50f0800d004152040e9a40108100030422003619000b0101c41c0d5494070300c4034014035402c03100d15061144103140344410b5569620202d5103d01041d10032100318842c0b1001c01c00103000c01405000024080d20800e272603520b10b6034a2514045040e030111000c9000c0c5403018155800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 506629820 1250 506628570 506628583
    0x20606010311030a1d011508071d042a0b210106020d0c03030e0d090810090b15180a0e100614040c14161e02010801180b090f09 56
    0x10282002e02600c1d804181c1c002040c040149403092203942c40610003101c400d010701030302e2400c5a640080280d01b4580d44038010780c0e0300030b008440ca54450040c2c00512100d8400003403141250351340c0840c1072900c9644d01c62a05c01d0152104040075a00b5035400e00f01d402999007510000d0116150183c0e4842d6809240c0380301c076802c0407081642d190148010490303c0e8020a41042c1036450f441c04ca583d0701040d240a400030300c13401915101c584580c078a01142c0642109040c1d06275a404000c44450704c03406c00c0700c001568020348008110300340280209070700b2070a0443e07200307403440c006101607061200c215074030400c40d90440310000700c15218010306514020500814099154041c418024641010084c4050304001032041e4000d46e981c01111101502c15405017070b03000c0b040301c2c02c540e035103400d91003841448540000c20344400c0d5940c0c241d80e1503184840c03208200340d40d06840702e4410303a10305100300744e10101c444600c0d10910784442e901c040c1b50342c0b000001c9115281c1c98101a0300e40c18984946c910b40803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 506631070 1250 506629820 506629831
    0xc080a060501090e0d121104030b0702060906010602030a05030703060513200a1e0309020d0b070215070c020d030203090a06110d08070c0803060a030f05030a021204060509091e04080403030206 84
    0x1031130702440700101000802c40720241c41c03280c200342d940900080c407698006c3c65101c0500c401c0000205002c0100141900e80c103024034440c0c0d089030307207589030f40385840e407a0742080c469200907034800c0110f1103e440c0200080c41d44101c0f2800e000565a42d02c10105440c011a10800310030250740c0c001c06d004030303202c043c000c2c2030b20150042198208182000c01801c0d020703032124000c030304881c61208070900620a40006d040260f01528404240c40e5034a00054070f200252911409030085040c0c5003070816141c101a4403500d0250344115903006d2a400703106030a02c2d80c0c1da050b01140000c021120b03203070301c1d003010113001030910780d0346c092111440c41e0f2440d08120400c012601000821401d005031142c0c8490029102ca40181183c5d0352900c0e050001056111a5400180b40d00c1c1002403010902c40040003038140200e01d41c098450076016a26481c141d803141e800380d01b0120b01c0500c0309a400d400d061a003964410065000c00b241c0200444500407000006c550807201410001800e208240d4140100c54104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 506632320 1250 506631070 506631089
    0xa301d011d03041a09041d15040320010905160311060c0601030215070209070512060405042f03100b010f020a020d2907050a02011103061018030c080a060501 69
    0x201d100030425807640b04a21400c03409060049420b03450304014812180c40b6071004100b082500345522104103a48008804400c03540550000030005002ca5401140f19039403640d5445030584008040080b03286010741081d0566580307142e0000009c0c4100540801111003140294500b03103103142101c0180400c40250780600018030035800800c0c40044d03942d05481d811181070030040d0507600320311414003504d400603500042030014001d182e5007000040503c0b640381c21001580c2c0d03482c00c0034081600d80a50380201000d41003a50203001002c0c8900c05111a14032910f4200d01006100009103040140a210000c26a40d1a0029100d6801c8a20f40c0d60b940781171b00240a55600b80d40004280d282c40c00006003400c941c4641040041c4518080c103030300d0450032580c0300d0740ba080c12a0020035a030001c4000d0000341d031a2100b000180b00001043c0c9105400042c80c2e80d11108054408a0703006107031006000110000040c040005a58082c0070405001c0850081a06201c01d00745001503e40c10381c46005030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 506633570 1250 506632320 506632361
    0x10311030f032508070f1109090307030909020d0e060f101505030a18050a0b09010f020c1b031507051201150e0937060603020a301d01 59
    0x3c40b0202c0380007020a039014031800d00d01e040c9410b260403a13124000b07004064514908180080049140451901000036101100079035a04001c0d95502d10036850043c021501c0441d0410103102d554006000f13080c2c50000c007060306040084214506030342900d080306002c000d602002410260a5121401411810744c07581c61002c40001c050040e1102408403803a4507110b02c2c2c414800f112500020310b0482d071205c211909001c01e070030004103000301130340d12880c0c65091940180200001b4003d44070002c501b14050b10340d0741c5018906038104103d000031160940504040e00b210511081c50640c807405140e1111b0ba0359100794881403440c031105030004070380840001c1080144580c403c10280b075211090b580ea071427540383c10b07001010081880310a15002c0144221014148414080401d02c19030740090038001d007500d803141a016406649850b10000d9441c1084a240300c0000c0e10700c0e0300300c085507600b8800c0c4040311070400003501da40c01031480300f101c00784402c2d0000341030900c07526240c182c1e0b00040b5103e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 506634820 1250 506633570 506633587
    0x503010f12020a17060a0f0c050f03060f060307201212090c0907050d0e03090d0b0703090b07050414090c0301091e020a08061305090a0314070605010311030f03 70
    0x206902203028602500700d035088400c0864840a02d41400752161140100d4680d0809041c80d03940c4004958044140d820608080d4901c2100d0040011a0b02c080d242d450514181440402c1d20fa08014041c9901c03071030a4044100c15191030b401140030303402c00d83d40c110b01c0d85001d0420501c0a0028182e00c026039100e800401410654034080d034600c11316000035000a0344441da070492800d00a13030705d001e511251400a124a59401800400540c08151001d01451218905d0349803240244005079401080803095003001030160003410b80c0c0040c0a00703000504003002e0300e40070703400a8101e901d880400d01c006410301860780c0c25040c5031002901110101040e140014407460f00b804188a003620190307c0d144921044000f580821400b200250300446d200d004140c2d00a001e000c094031446e004604480c0d00303503803145003805807520440719400206090412590308440030140800019040282400745000281490146038000c40c09003900c041c0c800c95000c00c0606004a034202d5403502c1d80100821907 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 506636070 1250 506634820 506634839
    0x1b0304030e090a0b030601060206010f081605330409050610020a03030e0a0f050a1b03030519033801110a020409080c100c030605011b02040f11040b04030501050601050301 75
    0x100010a8900e50b100303450701c50200016040c04070724158180540300001c561190b0003c1c443c1d0484100c1464104525594221980c44210204205010002e0814280100e041120011640384101c0360031000001400114540d801501028150f04c54000101004400110701400e03030003684c02c9a4400613032400c808041e41c0c1d00e40d0350100406041d103550914a5a03030b421710039130203120380016036201070303203180d240003031b200e00034440304031518500f40b03803000b40c0a10314620035019a035042e1150391900c10b42100381c1081c00c0781240501d08054640c2800f284512041e0112001903608140c0050700a80d484001c005a850b040c0700581000406540f041c045030001030310703001958050354001814189801e210320309200390800d6420307074494a006810360030442d600203000240156001c110a9403500c00444080c044101c006929903c5170058001618281c0d201507c0310b005a000012101000c85c844090b54105500941603117a0210741001444003c0c01040c0d8001c0003440c1603032540d8104407015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 506637320 1250 506636070 506636087
    0x3020d060f140f060d060e04120c080406080405030f040305010905120a120209060f0f18240d1e020d1401050603010e0912070b091011030628030b1b030403 68
    0x42c480c0b00102c280f0a21a11000704590b00404840d1090040a4480b0f400c00c181c58402e44003140c400881d94410840d06100c1c0b5500d00b00c40e517000969030b103841c1c03030014100c403607800c0544140c5aa0104000760f40500666070014001548640c0000c03520300c500d41403050074501c07036119480c0d94004c200204c040e059482180080c444050583c01600d030040318001c1101801403c003a00c01825000645140348078081c006002c0c4a4000e12120058040c48018040c030000070505e200c180945254401c290005030402411442c10f02880000340000c90340d0240801d5120b20503040c03491580007613968045441409000e090003001400d0103404d52522010032904c0c032051040207503880d028070208420260610000f8000d0030440c0000c0d40303c241a05141460103020b4415031600d00ca456420f80c0d29201d54020300c41401c2c084681d1383d003140d603440c060140240c00d010410352400c5000f50042401d201202c00440a9801254140d60b5844e000900c0380400100b8160b00c501c2800a2040200007507102050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 506638570 1250 506637320 506637359
    0x61e0e0f010f090c020c060d0e06090309011209060b1012141302010806011b060b0a050f03100e070b030a02040e130c120f2906060711060a090305070603020d060f 71
    0x1e5141c150136022401d00601801442c0d00c814001000306041035140c00003c0341c140c40e10300395000c9481e0b4080f015601e2080342070715800b040041c0c01503c9601442e41c001050107000c2d030781c041602591280000c140d105050b01c440c001c544039490003984403000b0701c83e0182c01000d4407982483c0d410004402000740550344002130410400d0000525581d200d1780c08490070f00b20040401c1c082401500d8201c000d0404e0b502200d0040c6012a400034440c6401d888040390494007034090a40c41000c00c2607030029010700004120b9910500d88005144c9214100842c4256607074140140c60701d0404140706150324000e0b10750b014103810000000c000c203406208210031600307001030400110030381d0b00d07203c400440400c00182050150080400d48800c4600c02c039030b004989400058880d65488080140301e000c1c03202c0c0500b140c10f245c01c400308075051400c0280320504146c2004003940795203075511860415031350000300000b0b4021a141032520898050f00000e040c040307040d4040c22703040098504451518408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 506639820 1250 506638570 506638589
    0x3090f02090a14180c0f1305071e05072a0b031003020a031b05241602042a080417090a0f150e09101701061e0e0f010f 52
    0x402d110507410b502080c425000d0854840540c589101c0307a04401d88105419180d03409024a016000e2600100c006441c0704000d0a2610200074120140000c0ca002880700041c081840c0080140c0d001d1414448502d1080e80d0b10b0f03e541e0740c807a03c1d080e00c2c10b4445414160340c418408a1181d520300700c82c02c026083d190704501a90312940c4120003003440110903071020350000c3d21940f000c414403002d014801e54041c0383d06109075803180e840b411b00180c10340030954800c80b800c80028a0808035650001030907601c0002c0d00d0f00200c404160000741c00c950f04a60202c0c007100381c01084100005420101c000c0c0b61030f643c1000c1025181c10340b50600d0001c82c20381c401075140000141c0606560761036500402405c0c041c150000c209440d401c02030000821034172130401003083c00781d0023146460605000c0340705a0850f4060103503c1d14201c045000d4800c090403040342552110400708601d060303082074030822000d80b4105c4103500d1400719050160103014003501e401481c1c5400500054981a032100100c0b8040340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 506641070 1250 506639820 506639839
    0x30705060f07080a1407230a0804060e03070906080a031709060a050c1b01050106110a150b010512091507020a200117090a1101050703090302010806060c01090b1603090f02 75
    0x30000c0300c10450380545c100000d00d002c1500000d1204a0490b501c40449144420225602e0f02e25001d64400215000806681e8104000d1040b030f8403646210400b881e0203401c4942a58030b511210041c0c60180d000312000b903100c2200407041c9030384616a14100750480840c2202820242551901c0f61401000b14141c01c0c0ca45022502035201c0d44212007450814800c1c5092a44032482c1c0607010340b0003803048800090003440444041c01c80441e55a040700d41c840d103013000f80390440c22050040c000c190100360612201f40b00c040a083c000103149403140300c4010240804200e500441290002c0c080c080300c0455000da0300e80800903d101241d620301503000c0c101e805061400e800100c1e00141d071509031000040c4001d081c0045c03a6000103502d1840f40c4101901e2038481d04850044030140a03500d80600069071000c41040035500580759282c01c00d20241c4054941707010201c4c440d0950f10400411a22100a0b008200ca803000381e000c500c1070100d01c0d250910190300b0a48407640340e060303000000391089680d035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 506642320 1250 506641070 506641087
    0xc0f02010908010212010f0803120f100b0408011b032d1b0810150f030f140705030403030615021002030c0c0a0c300609060b06030114030705060f0708 66
    0x1c840020050080800a56650400d10b4940c40e18200078426020f802c44104400703d20b510740401650b00000510a030b481c502d40d034240c0071403800d200250046182d00c041d98000700380550704074000d001400700c100000c42c882c0341480780c0c4080781d51130107024020580342c0701511005011260486c1c5000800d070040b0420703d60080d65510003420000700002d000c10445e250703404040e0f0020340103807180141017040f448403565416a0140003070454404000580c01c002800b40039402540800d42c02000742c2c50008060f052607000c03000c0c03004c069815038041403011042004050781401007102401c0b0b407141c00441b01813a8000030399500c0c0c00113082c101154001c000105844030368801c0d5444140d012040310304d84030482c10000c0a0000502070a2040080e0701244100002d803018424030000d00724105101152444d11040024a11901c080382c0f000e4881c942064035968920266000c2d00803840c0d408504684a010146080a19030100b4011801889a44288459101030f2655280c01440c4690390f6980c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 506643570 1250 506642320 506642327
    0x1030905010b040204092003060a0303080405211c0905030412030c02040c031b0905010f051606051612061508100e0a0b040c02011b030e010204050307150e010f0c0f0201 74
    0xb80303540051010600003081c48994000d003607924041c0090300301c02c0c1c008400c0400540f004503001034100350790700010030000348110445648540100c09036101680712443c0a000e644030840c0800e28400c01103010b858020310040d440d03642e0703490000100802c03092070751b80c80e86038010740c89076030072400d44078440300280341c0100d2141c188550300a00c10048142000b1000d00101b8124076100d16042c1c0070607880351118050303250a0f054078016182c000304820740030400c0318683c3c4181107150041c002002c80500040a40c099903000343d03080f00c400e00303804003040030003842002004c03401c4944904101041015203411144005000d1503803034600d109554103000d5008941155101030030141808041100d083c00503440000c0b41130f0704450a00154150420813426180e01c10302204c80d036000294810501d90090f070040801542c1c45002604050382e0700300017030408449521001002c1683c1c85503150142d8406840016580c09080c000d4000361100b10040000c000c8400044c150a100c0f21080290380c003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 506644820 1250 506643570 506643581
    0x71701020f070b0403091d04020402090f060c01140a2f09030a05060f151003051f08060f0a020f0301030602160b0103320c090a06170718020a0c020103090501 69
    0xa521400795458590349001e0000501c221800c0e00050000b5034080b03804c42055091b00b00700d400035011000b0340d445607000c200080d03011113680baa100141c4200b410842e241c05000d404c00744509000042c01592210340304800d010001d0046441520307018000700c030600c400a1124031503410b5156050b01c102804440b0720740d0310a69403410b5151040c02c03000700070030000141640c40313180c0754000d510103070f1a2a080b00d685010010b001c0c0d40e0113181d649030101101e100740e00040d030040040c4141ca400e900d09208941480c031190708030b0701c4160001c0041180c0050340005003a000049142d04600d07150340302c1841382042c041070000401c691f400040c0c0400804400040048003a0070803c202065652861704050110104200d81184291341c034040c81d03074103510381203210f00290150140c443c04842404001880c100106941c1d1001e948120104d0301c0b41102001e800c804920070014800e01c1d0a1403d0039804102000e20384004070300421030300c4c0c9082e600610b14000307158282404100d07540c2a1418a01406 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 506646070 1250 506644820 506644837
    0x3060b03090714060d06150207060f0c0b04020a030206030907060e06070c0b070606030b01060e0118050310091b030303050711011802130e0d030c11010b1c03110114040204140907170102 81
    0x11b0500a01140001c50f4a6266814a44503003c4a483d1a0740d8a400c4d0340f1041c3c0e00c2c1104000c21000d000343d10114041c0361420b82c3c0302d48010144c0d03031260313125400a426900203036100481d6600850080c0040e0742c02c111300d0388100c4000c0fa000c0e4140440385c3c0d0b076580740c00e030540908001c49001150710020001e054100802955200c54400010344e19540014806091101c820380000c1c0c850611121412019450708103552024000d00882030003c640040501015402129012079168400071400c2c100041c1c2400345200f540d0110741401c1c0070400404081541c00c041300c1070703454203111841d0300c00c00020002c1900d5040da070450900342c203019140000e0100716010a4140500c0030030740360030303a41580710311030a0000d52201d2282c0c28842d040c40382220402c00c08190000701d01c0c1b5500d50101003422228510b0f610910b032a91001c0d4802c8611425204036241d041c4503000b1901c2030104510f03140c010300a40300c145058440c540e18219941a40c0c9407068421030802e444401400c01c0710107003c2d01203c0321507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 506647320 1250 506646070 506646097
    0xc1813030318120c23061b0c03030a0c081b090d0309031e020301110a0c080708070210050904110c100e160602100507020307030518010309060504060c03060b0309071406 74
    0x40e4803161000d8070803003040004560b001548218508003031580e45c0048802858140145211b82d561088a55200303161100111886000c1c00702e150710000c20001540304500905001ca00003681324000741c41c0e42070103825800c040e9280800712603c00c180000f03807444018100e841c0e001e10091410140d40d983c645030000f5040b02c02030390203200d459442d002c55000c1141b09800030050300c58070035010a10b5011300030340b0b00005032600b20200013040c14032001d000058050000a80340c0002c81c4d0005041c03002d4480580301059021944850310328041c480d50902d1405103042038a016100d4030030a4450103480c00554195a48591681c62007404001e00030b620960f600b003040c442601c802000e90b413080130035010308170b5a05140c00945094804402d5a00a41d41500c900303040010030032444081864000311203040503130340ca9900011614900550380101d01076030000880301c1a450005060b281240c100d4948c0180400900481c0c0f040001c2c1c290881d048a00414542151000012031030f00c2a0010080e48 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 506648570 1250 506647320 506647343
    0x1815110d14061008071b0215041e0b0703050a050d0b15120105030703120804030e130b0f010207180216060203070306210b190213080c1813030318 64
    0x1800c1180080703401607004844055440780d40000803510b034a411121080007031a2010201c50a404070b400300c00c5c0192004103800c031129541c030f15801c0c013504143e000c800c0600c03060315981106c04c0c00300c20000c06005001d01c000d1400800ba1000b802d07078456201024100080020b401003400103581c0028480603000b040e04c1001c2484100303420181d002066000c1d02c50180d180001400c2c0f4000410004980d030041c00b200c8100074518080d42c504030000c1c415800c0c0901c0400031a41c0d903035409004500e10450110000d000c142c1c040a105841c1400d00d1180d0640d40a13400900048850040c114041142c4035009640c07010301000c0c1e00a40143c03a24010421400807040c04070f00d40d0503800501c15030b0385415505c803402c0326001402c1c40240403030300042c01c1c03c40c900d0f0124180201b880b0310b0038240300c400d02002d898181c0003500c0002850242d03002c040642c1050214008030301c4c01c050000740c1c2c0c0030301d00c030450414203005652507042c0c4c4551000805040d582e030000007080c2c6101551a010340e800a000414 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 506649820 1250 506648570 506648591
    0x903010b15030a0f020c21070615030605010e06130c05040503150105030613110105280917120f0a020c06040807030510020c0316020105041511011815110d 68
    0x729007040e5607003103150741424903480813207685209a50301019004020015103400c00ca201d10003800182c00a0000d15041260b2000b281581c0202140c24000050f0800d4841c6076013051412154180c00114552159105005c420f07030782c284001040c9492504002001c15982c27100b81c50b184039076030003241c01d4000d15a400c48040308024005040305d13000e4040c1c4d400d580d0b804a860907480f1615100400cad11158541c10821948510081c146615140b0316500c2001c41100c03040340405c08030071401c0c1c0041e08480301031001650b28680505030380011002084038001080a9a03054081c0c07a410388007960340401c640d500144200038908407810054800e0b9031380c5c3e842e144c060740c9800c40d901003581c080c8604400f10314060882d00c200e42803111101d010358240700c0c0d003c080d500780d00756070b5400b0b90401070180320128804282c403c102c03000d045a62600701a01840241140c00e4403050110450b500105410403804150010340302840c600e00d200d00064040307091035090f41d85000764081c40040510b040a00c11 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 506651070 1250 506649820 506649859
    0x90702030d1a0307150c060f150b0306031507020d1d0901062610050603060d06021603020c030c01170c04080d0c031704150905010902030a111201060b0f0903010b 71
    0x1c04200990961380e200707484180480e284c2d85695010b400052215120070b02040c102d60140c10841000748003c20080440114042041c20300d401001078481d0000a200381403030704000c00c0c43c1c0e20089034208201840d100d07402946402044444800b409940c0d04031145c24504044803155407800141070b103900e561070b40e0008010340141448400c2042000c40000c00d0317004a215410711460300b280040344041c1c00e000520842e41c2026010542000440f208440012800d0020f860691200c8034031480040031424000d141249502d041030094105500500507031340c2c880c4a024080c28041e045141641355107014452502c80c9500c9506240104090513030803d03801f07021400700b035000307903a40c8150b510440d00542c1c455206403001007076410b482c2c58031065604a034102d03810882c010800001c1002c190340129050010003041140c036448016508881c03032030103001280b8402c41040080001d00d0510a00c0c0c1c0140c0f0a2600121251401003042c400300d94003504043d18000d8040e006464111166002d079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 506652320 1250 506651070 506651111
    0x21209181302191401051b0a1b05060301030f02010c031e031e0b0a061b140706260423010e0d0809190b0406020909070f020105060a0302030606090702030d 68
    0xc921401800600315010050f0821040c2a1203c8241e2104a403643e08015a0554481c540384035503291a0340d91008050014840822024011602008030b010b100c2031600c0c08915942009128150500040c00030a10303859020750401d0342030030410317103581844c20166844c99001505992000c61800f00020180e0302d80c12683c0404841c41d1a01040030301042904291202c0c0d4030030a070098807000040003e580300d0190031384080500a1030099250540d00d40080700005801c0d06803003940441700421800358400d90704d440380c58030340d25080c0f18070350b070b40d5040380c601f200190014081140071041d11440c3e004e400a00040000a0f8008200d568a00100075495000c44101030300840c03154000220f10040104280c0c186140755901d110708040d00781e9a1550b00718000e00260b43e80c0741d0030301940c402138550182c0c203401200c887e20b407480c4110610400a0a40d03c0040c0300070301415140f102040162000120150013400483d0300244507511010100d1840c00f6001c5032181c0e0381c2c180469a900880316003001e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 506653570 1250 506652320 506652323
    0x120a11160203070f060806210f03090a06020c151c020a0f020d0f02030d18051204030519020a05010f030b030706030603020a053115091e09030212091813 67
    0x5a071103c0d0360750501603075003410900c0782101240ca900002812450000100d102e40b0010640e202aa503000400741031511100707413400b0081e5400001e160b0403c0c80d1001c09400107080b41d10040c00014805800300b0032603409194100100d40007c2000c1c0b9801c80c107402d510a090500c100c0454032906080c3c0010700482e2090f0401d0098083d80c07240c008954412440300205150b140c00035482d00d400009410000d0420f406207200c03000e0244841000980c017070004403850071074015400d031960305500300203041548581c1030b80d1123040c540503903400503150300017984121002400c00641c146001001507001d800c252941e11b51600030304101241c45900b540c418030940c6c1c02a00c01d04030498640c401c0c0301d000d1800303009000400c00d40340c1d802580c49584e1441800040300238600030030346401c0481e4150741c44210b07802480c42c450b2100c40c0c1c0c8030101500c03900d00a0120390484107105442103a2401303902c03446e1028181c0440140000c0102c556116031224104060040e4407084140c0b07000c82c100e58818084140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 506654676 1106 506653570 506653573
    0x8070c030f03120c0215180123010f1203090603020c15010f090c0c0b040609080c03070b07080c12010303120e0a0503070201030b032a0d0b160e1203120a11160203 71
    0xc8075030744844012603c82e850350411204a10810f40cd0300040502024482d804001c0b03a403210001084030914140180d540c90004041410007c040c4a4412440c22840000404c91000541c840868086800403c40205148000c60380400e000e0005011060840d0115012407015072021300518403480304140340030602c42109045d600180020f60b500d03140b4078200071f08103820481c015401415002c40c640741c044540b0780f00c03000c000e06000280401c00c0c0c2c003c004505c28102d60000c1d20801d0410704481c6d440d4107500e001640c0b54070094040b070000b401d09440c0d20841c01c0000d981d84c00076034000c91041c1d01b01c030030850031605608000c07265a07119a83c0c0c403483c80402e040840482c0140e62050340303000b60810309140a04203400c034400302401501c03005030800e03521350302005690410140d64001c42d01506c400481c0c034050b2188500880103502d00141681c81c0200013004080041e200b0380 = true := by decide +kernel

theorem cover : BRFrame.Cov 506474820 506654676 := by
  have h0 := BRFrame.cov_init 506474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 506474820 ≤ n) (h2 : n < 506654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
