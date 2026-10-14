-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2210
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:00:11.626489+00:00
-- url     : https://prove2.me/submissions/f8207ca1-b211-4986-9225-94aabc558c60

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 397302158 ≤ n < 397482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 397303408 1250 397302158 397302167
    0xc040506090f04021905090103120905030610150e030105040f14032701140f070507050d020906040b010e0d0b01080601090606140a1206080a0308090d02031215120d 72
    0x104514064960001041041c10650007810f4005406607098110341040ca0111050140c040c1c0050341c00a254000000c00c00000c43e8540fa82408181c2d110241c02e911030041540782e01d42654540501c504900e0184511000d04010015040440c100f41486100e80004039081d107400f01c1c0c0940c0c1039410203d04005018000d43c101c0f08140700d01d400396291901c8002c0b89206069034017814120440462504449a4052036005030f04d10b81e158010740d02c41c100103030f00305650340c0480c20440b041d018404c0006218103140322010071856005220311195613881e82840010054800031504210154845107481c2e1101a000a1a1401124484a55810400c20618003901030b4004c0000500e8000204003e59010151400542d0f0313070f1203000d50340d00018074210b6614442e0905105100c0c540344c000901e035800083c95150305407003525902c04580d91071135034580b1030307920340c540c41c0c0980c0042000d0410110300c3d0100d294803903400c040192101c119100803ca2585070007c1c103110540c0150030851025800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 397304658 1250 397303408 397303411
    0x191e0c12050d020d020d080a0905030c06160206010302010c020409050a1403120603120a1d040f020406030c02010605010203090f21010b1318030f03240906090608070b071b06020c0405 80
    0xb60005041030025103000070758911800204204000c000310216a031a01c440c1c10880a043d04601100d440d0030003a65041c0d1241415680ca00388070019040e624003090010541e18100d0740c0503102c42d80704030030302d400340005401d074448100e8490080a40341000155903c01c03062003441050025030f00c4000b103c040350303106a4040e1103184030380c2c044001851802121000c42e1032441151074081c6842c640c040c1107464600c80c1030506075105040503075844000e00958094012166943d50601c243c1d0780710a0207900701c43c12400380c540140c0042000125908040c20f080c030410700c0240c0344141150604c4ca0710310307607900d0f8980b01440c547d44801e500c050f1890180b030308007600a45280c5c104071041a08a41050425200c40020b0a0081c8100460340c0c00d4040da010f10b0f065905644240b0134103c0350f49110008550070f00848030b20514203035000c2404441072043c00290303529040240f4003e0704044c1040740d607410100013226050900003500c10f41421502c102030081140d40c00400c0344104402c204402d5640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 397305908 1250 397304658 397304683
    0x60309260d0e01061d040f0609260d05130302060423010608010203043309110303070606030b1305030409110f0d0c03050f060906101b0b040b09191e0c1205 68
    0x485c40910012512004600700701a17880400003e5018080c6813004201000d8454142d82103400c00a01900144800042000b210b062030204102d648100c015031040e488180c002c0c0040e0b020b1000240001c00c90110a00b541200c8080800d0058082a030726017580d504c0e800c0602a0b9402001b0300c801c11581c054078210f0203143c40b04487c1c080c1d841c402e820880203142803a644903242c860401c8000d1000a445003060b10030058186c0e41c0e00c01050800001070310f03c61100302c070a80c9614001410b201040166600d419611074060340c6450700c0d200591000d005407449200034a281080503c80301c0c000ea000410f03903624002c3d00401e24010b4000b01900302d8600034043c0c0102c0c03031410100201c0b69a900075a03544090201e03040c210030f07420b5032002c54200740000e45260050500110307400c10311806207401c910581c030400b4071300321940e9404002d680382c4035040c5078292400100f8680b00300060044441c221100c0302140195603820f03054850500c000d14170f071711468a100c1104900cc09000d814405d5041112 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 397307158 1250 397305908 397305959
    0xf0209150307030615271802130e0708010c0e01031d0a0b0a0e030a0f030507120c05041a1305060a020f060f0403030f09030503011202030c03010c0206060901060309260d0e0106 77
    0x21901075030913080b906c1d0703000c005080f17075450900d050310700ca0344030b1011034240e00603003021522110222400f0082510082d141004e1040c0c400008141c1814010709a5a5800d640e540c294130390304c42d0043d00541898101d400b0303032101c00000000e8080d001c010303851840303004001d540c00074113001c000481150080071510710386800410000789695000111f01002c8511854000350650310404110340c230444a01440e8045403e00c100c001c51164490040e00a886c0c2140b50100f40345509050460a44642c602c180e110150444042000f440d0000140c4484c503007a005582440410340000d604200c4211001c0740e43d89038104c01e1000b0b040c0e05116140707403822060307401c010045850300d0140903400148110002d40c2011141442151020300c100012050b0180080c017408420007006034544138111017507401101c407103000060b2580709010302082550400ca013070000c03062055a81000f20b11408484450305800c00c0285e10181c45442005070014680c4000106681440442c8075405000400341d05035a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 397308408 1250 397307158 397307189
    0x40212041a0c07080306040e1002040906050901030209010b0a02030f0c0d0e0111060609060a03020411070218040803010902090a170a0501060b1c09020f03161404090f0209150307030615 81
    0x3442c890048440b45a00040115229543d9500103406009003040010722030158011480300e00203160054015607021040c240302694852091001542003440040d6103c0704000040010600340c00041200130078070b1040da450140c000c5100c0170b29a00c010140e400380e500a4074900c90340c9600c000c0310a0800d41c01d28003184142680069555684000780685200300035007404501c8a6071020a1003009603400780003444100002c00d0100042d8100240680c0207001c000c81c000c4080381442c0b1000c0c403841c3c0c00003d081c04d5901380ba194800940002c4111600b04101c01d401044d040a031262181c59856140024086141c0c280340c15400d41d4003980c402c49684100317002d611100113007e0900a03040a520030001050300c5c40d400080c0581007150400358040c02113483d9582c3c1440d460310f1540940c2d007185a41403840540c40240000c4481011021b400324442c040400300500d0880181c0d604507200d07605501c96400d10400080c10402c00c2d5104480d1280d45180d0303c2800542d48407139000508003050b85d051070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 397309658 1250 397308408 397308421
    0x60c0c0d1b05102f1b0906060906070602030a0908040306021905041d0c0403230c030c09041e060f0e160807060807020304080111040806090109081903060302040212041a 74
    0xc03910342900803000409070f4125104403421034241c0340c4605104c400c56000203c100c1003100d0b48400b01e40c0301401000070300000340140c1404411600006000340507549403c2494561000a40025241092980e16922080041030ba254054400740d8081d48006903224a484020a611100c0341140c0050000501c01080080c50165204207802407035441100e16903619816a045882a030308000c3c8640d4030b01742d5105803118200f8807502c81082c20411901400710700400c260759510030b0321405038808078200016001561840300100c00400740c003203891140040b651494155140301c13560502ca02e54829004412503402c0001000300d0308041c00c0580b10343d00701583c082d19207105008103014010500c0c0494482c1c0e108204a070002c0882c0c900030010030200340c02103c175035441446100c04504c00c0c1000709003030700e1042c032405103000d80c8480080c0c44c0408803241031404000282072102850b95401d00000540c9a030300050140d080e08a842108502c0d052810031900180c01c0244400c0203600c1c07042212 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 397310908 1250 397309658 397309667
    0x916050303040504020f0c0102030403031e1b0e0d0b0a0b270604090309030b04111e01091806120605160906140d23072a02060c0c0d1b0510 61
    0x242d583c107030740160b619100105a041d1030f118140000e0324561000082000f40355156100c0202c0740405403800f02d440e0800c03105941a01c80000500e00750070341c0c41d02c111006074051100d0561000c006130003032110180f561184003920300100c5454500b9600c2e10b10544180c0b4248505c0160b48801403858034803418010b101d40a83c1c0801400540607540d1500200141401040c0c840001c50344901c104490340f1f07252a0a9421002c0000441d02444210310440300d13608100703e80c407854960680d02c454003039140071040700019031241040e80003143d585001003600882e101c01914a240980c80104240c10b01e0020002c2138050020500200200c000042c48041e502000e01000c2c01414580c0da5121148c81c10301400415010030764090a43c06512084410010b0940040c801c003e02c5e207802c120380c49c40407440080c0c00a0540c00c1703212483c41300c417418018035198019020154070541103804510195022070a6001070340300585110713004420510700c42125280410140c6003d80c0c0703500c0d81c1c2d030f0126400390 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 397312158 1250 397310908 397310917
    0x11a0301141c030f02100203010e0613061505040503101104171e0d02060603010b01020a0b1b0c1b010c030e100c0503030709090615090e100b0a03050916050303 70
    0x1c62154400c160790109a844051203010076038140e02c0004141924580944100d00710080719015002d544807401d8120181d2080e24100d40c10b0001c0015144c1d00da90401200100150340c041005a86400115820800d1401c0038002003041d1106992581080e00705454240902342001d10141040d00f0380c0c540c40426401c1d642210646100c40d48a480750300300c00b0b8200203014032a613190140d000b44860400c030307000600003410040c580035144241c8441d03087c0f5007690b44880c100c50241c0d00001d00000022880f8450f2507001103400c003002d69201010040d104c065002c1c06c560710159102c81142038914201e05400d641e00d01007400c100c4444441542c02402881d115a01c161045125840b04100980a8540d0b647d08584c4041500e580385010080585080319501561000500d40342000c60000d4818800c1c1e111080140c0362045141e15100803801482802420004c61501e440d00c0003910704d0940015001000e859200490303d85005601d66240c26a030701d500c000c82090110040045440120445 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 397313408 1250 397312158 397312169
    0x3121a09010e011a0c0c03030a0903141b0d020604030b0c03070807020c01140702130c0504170f031801021f1a090709030201110304050d140c120c041e020c010c020105011a0301 77
    0x20b0b40c8917244138142905000240300c0c044c2d0540400a521030388942c0c000c4525094911403111520700c0045144d600f643d03034540002d04007644c41d4801d015200c505d440f0f040340e500e880c4010036440c03425403640d0310440000c000707540c072800d002da01006000c581038000041640c8007515100402c1506581c2000038544050915003482640c00050b103c415919035125002c003500c10480c0500820b0107030300d001441c2c0da01c54420701001c42c0075280b00d641c440c1c00101d070701e000c03180d9040e00a50802d0407622480018415000300a0f055100b15880058501a400d02e070a0a41c920f9140005107210601541c02804044d0010305200da9400300400c4015500705031b018081c0e0742c080ca0990550389403196400d1640c0300d44d4000f580c0c080c10a080c86005c022854454040317180c07201064441c1500d050090200007000410003080c01d801000000c14142000d5102106400c08580190700e07154a00342c60030120f0b4000300c45030b03ca41e5111b5444010303158090290600404112010810200c500b100e982c4242c001805030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 397314658 1250 397313408 397313459
    0x317070903320a140309030303060603060402121f24140c07271401150903080703050901080105010e031b0a0906060c1e11040903121a09010e01 63
    0x2c0901201032000d084488809507142c440e60001621240d541e81080304811a40c04600c500c00c64015140071003601d0052601070300842c2587c48030f000f00141b40d00020106600a5820b100c3c020f81d26901016050054440d0702c42c101004286503c0d50040d031949410880d8a0310455400100030740c51416118290b41c2c0514001040302081c15018000e413103500e040488512030b10760f010410400c016200700e008100041150f6030b004298612100703503401031038108200d01d911801005040041001d08540041610b850000c950f01ca03a50405580c11407001503000403c0811041081d50304800c0741405440c0c00d080110804141c0d00c0001d0741c0308607485200b8801034410031a00c0c02038454100c0d440c0500b9441f4010b101040d2111001000503952800036600d940e152071103c0c5101150081811039142c1040c241074440c4880014030010f0a00c500048007004082340705800d405045101349400001c100941c200381030900340c1041000801a044070b2100d42c0d070240104400c100300030110302c03c4c0828014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 397315908 1250 397314658 397314683
    0x60901080103080a020a14030d1a1c0507080d080a0c0c02060d0b0a1a1e0405030706082e0f0602030c0307030c02010203040906182d0f02040807120317070903 69
    0x7001c0b4280807a02c60011f026000c2d03001020040e200c0030001d000408840b090401079540034040da0b41610164121058011640f40d141c1c80c5076800d1842c2511041d4090001ca0320340941ea40c420603d8800031964180001d1800030034401c0348a034a0203464643c01b41032800000408064000070340031700c211180319000684d40c031030350411030300da031400070004004044003e0480000202d040340c0e0340e1b0028a41d0300c000c00310440c0f4038600d81070000a036000d9440c050018072186017030860170345074420b001d0b04140d40c0c42c180700003900e1f4400d032204130201b803840010808100d99180440182d42c030181900304038150f402c18071070a10340500c004144c0b0550307501854889075161203800180e055101c2c640010207410b08041020270070307415200c8041c2e0202c800b40e0040100011044006161206400c424040108405040d08005545801c00c00c00b00d500c60360014580f03642c815800345010040c0d4000700503400407280c40720030305030071011902010103002444045c2e440c2c2424010018005400002c154004c00340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 397317158 1250 397315908 397315927
    0xb010e120c040f0f020c0c03010e07061202070c05040f0c0e01030c171302030f0c0315091f060f0303020703021302040e0118021303030201050f060a0b0a030509031608041406090108010308 82
    0x401c01d00504d40094401c43d0f840f04601d185548806071075014034025070804209406c0004d0008482d400c8403510f59a020b88510850b084001a41c080307c0306441c030f0216000d010800d0340d038500c52000c0b0b0702c3e107000000441c14292000070340880d07407910b40380381403501d454200c00413150032840e811608603401c40c4c0040940d4403c0d4281200402004002e5010f03c101074012000805c00203184925443c11011510420248001e0719240d80044030340d05100d4106030041e114400e0056603d01d03402510890100700c0945428030510351801544c000c0d40140e010794020415420494071007050144484020340c1f0301414107181541506061046e07900d151203c95403041086040d40c1518108000c0281207840e01e640d07420008d010300b40585d1070038240c1c0c8480c00452110701e02507110104035031144030700703d0601c120507006800910001302910100cac04100b02c1c044401c0d99400c5200c003500d2081c040743e03031600e0410b400e1604075403070b41000c1405180b0411992035645e801c04074041c11654004030980da600c0720350 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 397318408 1250 397317158 397317161
    0xf0604060911090d0206070b180c030c1e0a1a13080304030f0201080406060e01030f0b06041415192711091c0b070f0e010e0d020d05150a0b010e120c040f 67
    0x21f02504940c00742c8180000780e92142580c800c6040700104590314900d40408040e1103000c0c080c2615400002606c040c40001c070940075150750401c00400400c40b05682e0810940004051f079800510701500191840680d10741841d45806404c00200544c1884e04503a1112001c14001c10081c1c1809940350000d030410200ea0422000307407410514440140d656483c4c6420344002415040f142c2c1106880020100c1c01d140c401c103828840c141c41c02407440e8880c00c210380490645944c6a61b0807940b120490107103156115001001400c8400714514644114080c00da0010308203180094003d04050b0032103a10818074040d40e00007441280e100c1c854000501f491411910035050042c1141e400b00304110303581c1d4001409019140503a150b062101c091540110780365050b4910701540807640d12203178000744c14802003010200c1c0c0301e002102d10f40d00d00911204c00c0b8560464042c1a0743d41c0307910305203025590120300c0b03000d600c805440281c00110b2611a5a84030030454040b0750049540d8000710280700d209 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 397319658 1250 397318408 397318417
    0x3092103010e042607120825020109240e031e0a0c062306010c05070b07030e0604030501060302010207090606020303131104020406080a06121a060d0b0f0604060911090d0206 76
    0x1c0200014851141c00b00400c06500100c2c8151b070f0040c0f0030107162052901410307034144104510408416401c074090844d405000d10541000d0031076698041010028000001013031655001802071040e000856590405540c400d0580403000d40040c880701d110000c07072000403040d1004e42846951120284101243c141e8231043e0090f101c0e07810301884420070845002850742c8032014a511030103d039511401910003c08081c1e0003004d603405508100002d201071400b611004c1d1107854070307200648041001800c0d5030001c2d00103803032a954944c000c004668040210f0801041d50410a001081c9030000103901e80c00001c03d480c41c031840003a01e042c108807502c2110074802e04028011504d698031044010004030b0f00300c6800d0b18803480c101c800309041003c4840310860702ea01504403076a20010101180312018050f0800d0b800c20025855900010341c5061001d1145004410808007850100c3c2044284c40d8240d1020340b015180a950300c2c00782050100321000b5080039030341912010418800304195204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 397320908 1250 397319658 397319693
    0x516030e1003050f1f1403120c07170a420606080a0e060103030c1b12051501060f180b03010b031f080d0e03010e01090803092103010e04 60
    0x1c104075140303880e09640520302401070000c0307141d407903950b800d08050369030210100340e4080a8038010810000107114034003465060702030107a468540d81da8031241c90303d8010b4506040300e13030000c04081c02501b1a0007a80c415200304c6400a00690985841d8041c4948030711042424080c002040c1940d861400b440d81c40e2002c05004441c0c0c2940c04045110700105584d0040d9400075a5040200e01120900d0040c580000560006030642d40d00c0c503501905c00d20510712040711420f02c0d2520400200880140d25402441010038a240c103400c2e0b841d040303003450b03218100400c00911190040c001168403403034161021420f402c04044010b268039891600722900e40c050411500c0000011034026800c0b0051070081005050b0404801619101040c0084145c000c03aa229403100d8101c0114601c02c82c964280018003070000146440c0f0130502c2e5096130380f0b0040690b16501c0020900000620400c10100c445003d010074092500115282d07043d035110610078407088101c8603020906000340b40e070440c80040c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 397322158 1250 397320908 397320919
    0x2404020702041d010b040b01170106051308010e0123090c0103050a1d0a0b01050d1e060f0f0617070b030a020d060f060207060306170a1205190503060a0909030516030e 73
    0x80e45030383d54003030502d0041d014000da041a0391307949030754014044842c5c04441000540950382c02c1940846080d0807031640c940c040c3c81c03454000240320a00f0300c2240456544000081000c40400310080d0103010210640c0041c0788213281004000d05000c00d0904180c8404d00e00446c25490341c0f040e030006480782d0014000900c0039219800060f0900103a16003c03544103500f400c0b81680e84130100b1209403546140504a040c3c21003205000c03045200407445c010b84a074100007480c800200200b0101c82c0003034036902109649080a211510a40d8000724031a034103c402811240d0504c0c01022903404080c026500454003c91404040d80540d000358001d0220390305c0f0607100e56914030000355681851f1290202203490002c011a2119000010002c0c440007100208400341032a039980d07180b1000d41c80c09c0c4003003103010300c035644074007012500d032a611120380c0c0c1e01c0503145d050020030009110b078184d03c1030101c2c1c0e25010644000a4200c070503561060405504001c416840e030a085c0c80c5400503052055001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 397323408 1250 397322158 397322201
    0x190f09060f09050f0a0902030307150f060f0501020a030503060d1b0e0f070c080c15160306090b030c151c091a0403050904090c050303041706240402070204 68
    0x150300c940211164000d40c0340400740d4811600b002c0b1007090f2a09000311182ca0001405036445801505030144013070304592500003180c84d1210b801d90312204507a80341d61144114958680300b8040c110180140d00c16206600b441c01d80040e5607038a4028004051020220004406640d010f104003040c5400c100303480e0343c0300504201000d01c0360460050017200040740c00811702c9540c0c092803440c46212a0389034412191020703154504070b40c0044101654a100d00b0710920501141048000d0007617464903100c00c1c512004c0b05014081e62026007140200d54500062501035640c001250503a40701c0954540d2029006540e61009a203d00c00000e03c20f50781038034007010040000d50016101c14010001c041c00340a42e4450066201000d0b0f070050000750061201400c0c61801307500403007031248501c400100d070640c0d5402203403d41e0450b07880804415110b9080c100c1c451800d000d03131035001c41c8a25808141036030840403440000b0b0f102c010316010700d90200347c5e00110345070365000b003c51080415450141 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 397324658 1250 397323408 397323419
    0x608011104031b0513050606130f080d0503040b1b0712020d08060618091911030601140310030609030c0204050a09060b010914060c070e0106020a1704030809190f 71
    0x503a801403100b107a041d0500001d1140f50030b0340301d40c040140d900003481100764031000040c150280c0806000c166120300c0402c9a280e8001c91a11480000e151400d1181031845c0b400c19850b041130b0140310702c202440380c20401c010010312004400c81d400800e0030440305000c0c2d0000300e500540d00076120002c00e000d000c14103010110380c001a5800c1c00914650380c0c41050780c2c59105000301805400c101040060400d58402014503141c0d00d02680010141003004550031014440800d8030001d45980c40c2c140000000e008455a1210181d9480d58451104a16508000f21040c0030b448061001074010343e590b103204000c02d881040302209958000b007080c049410055800c2c0001e11102c98112501031602840b404254011070b84070003181c1c0000c400c051124a200301303003d6554040b00d904801c500686c0404240c070050140003e000c0c0c82513900805120401e4640100030050030700c58645016800d000810018ac000b10444041850644940c0d900d20848080c0b2152850180c1004401d140007600200c2c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 397325908 1250 397324658 397324691
    0x203090120120f030f0703090b0720030f04050906030d0c0321020a030219090b0901030e0c03190b0105150403080d0b030102030711061005210c100314090609061801060801 75
    0x600480704000310f03e1b15401c0303050b0101c0300100801006080031800090486004480c03e580b0b049607015403800c102c0310080524110350085d5010f007210039003c50b00380541e040210303c013503100c0740507002000e0f03e02c00750f031004d0203c0c010b8050090420403580c40d4264103c40c0b07020b114414508098055498681070702001e0040d41283e546174104000e1114107030a200d115103031700360807924080d0f4000c0ca0604c040c8011000f03000c04c01e04038801440790303960311902a2402c000d0300c03030301c401085420860012980b800b9401c01d80d0681c0031510881030b4012040f002c0100d0000c4a00702e81d8031074103031903030b50b4000e0107098054910002c1c6540c0c11352001c0100f00c0d89680191016002d2100341094400076510740200281300c0100d0f0103007a40014041c40f1040e810320030480e1030300a0981d1001214414400c0c02d000469041852403500c4c002604d96820842034060441266040407209000d8920340c81c280a20316641c01000b01282c040e00c8000280c0b410a0a0a605c4107000c3c003510300c0244401a175904030f426 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 397327158 1250 397325908 397325911
    0x60301030b181216020112060b04061103040308030901050601080a0c050a050c010f050108210f070210090b0a09090c0509010c0803060a03050f010c0905030f03120601030612050a050d0203090120120f03 88
    0xa0200b94800220b581b54032648c4070b07110a03101100070031703800c041c20440c0c22105c90ba0341110313021062000b044040301145c500c01c007540c030500001e40003144918043d070004109c5000135113402e607040e0810000843c2c0c80d800005a401105461170b141d9103481105d843e9034050030b10f0352001c2e10600d01c0d000020900d07031400f080b1a440300090019540c042c030303440c0102141501c10480d215044501c1400020700501c0c0c1034203409541c1000d0b10302200740c41c0d2102e00d5170307406500c806196404100d14400c1006410014060b000d001c42480c18000c0c1000502c0340064070088403801e00030454000000010020303500c81c8103681c017540d08241141e154842c1a030100740204904580c41005c50032560000925150010f920309028103030300d0207141000b61203a07004001c5030000d89091306060f211038000c40c1e59200000310528403401000184855550350030250300b44005491000215041045455a90f980040c8404030f0707546142150402c80b80b01c0d4138034078241940540040340c4524002203004801600300082e5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 397328408 1250 397327158 397327163
    0x801030605060d0b06100203040324060b091c081c0906060f0503150403031b02160905010614090307030503210f01060903080c0c04110a0e060301030b181216 69
    0x2044203441d0302c000c10003402042c03d40100300c4070708580003c040b070400d421118041c09040c01141e00303040d181c2e82c0744e01070140d43d4141640540d075084009180359466004042c000c220941005181103407981c08030710440141214001500d2094251408000d40300b0102c0f14204119540c0118802ca007500a03805081d10306001c0c1c0341c00e401d0120226052081c6031100d811650020000c28044644241000360b40340018419014581c3c0c071a1080c00011000307282c1005c849096000c0c0a5a100324840d4444000a0360001d06442d481d0000611416802c00810000800415800c2d07454500c1c51002074582009900028028000403e0345900c000969074080401c10052902d28120782c0e45050307100c0a10001d10420340010702200d003c00c0071800201c0104003001140068840510320400864141c1c7e203600705141c26284005043d4003050ba01c1144002d81120484480f8955403468403610340009015010101c11004012003540c506010802810415191003125854002c0c2c902f90740b03030086400106 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 397329658 1250 397328408 397328411
    0x3040f0311040225080c011401060809010c080a0f090c0e06090a1e1a180702010c03231e0c0702013e0723040b0a1503020904060b030708010306 63
    0x91050b40341c00c1c002da854100d040300c25a601c804040d409218006904042500c040c001080039006100e000c4c0140c03a40c3c9000003860078907031352400000074194040240b0450069140c9110340071500e90200d4800d42289444402080041200c00060000c20004000a1000c20000320002d0544289200e1922420301111018251342d01c80440302d041c1c6000c2410760821111304c031448100c2000d5940411000c4038215046841850190007203a005904401c0705040784e00340000f000035a583c240038120a0403d249014440450703003500c03422043c044168080320b0082d0480008038009141c50440e01c590001c00c802000e41e041034400d000b0503910901090380010566205441c045404c14201e003030f0441c0f090004d0144201c0a81c4924402c400b04c2c413005c0e4140158080054025580465481420720200100503c62950700c00c010032144451400e5010391410b400420501c0007450300320241d22001d09026a07070301203040c0042c0081c48103800c800001c54020051001481c2d015004a050340d204590 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 397330908 1250 397329658 397329683
    0x106080114010807050d06020d020a110f0a0f12030e0a03030b01090e04111509060d021218060f0703020403020d03080708010e060f0607020d080408060708070f0e0f1203040f03 77
    0x560703000001c000d0081c441e2030391003140204100e09202c12100f84440c012000103007803020307445c43c00007684e00600135480013914140600d0000f400174000d045154500c440246007001d09540c50f0056500b0000c0c01030042000c8411100300c440c003903080714007082d4011040d070f44411024a40a80104004017040d400180040408034031000b00d4403590b40503c0d0005109080d001c0345a0803c107294132000c034110a4013a007402021515207c54000e80003801c0300307000244e21505141e0500c109464014800d03401500014200800340c0070124505812411110402c3c000d0380cbe8004042d8064807a550000703410541403e40070703051660221400380a40c00590303c003c0142d90314110780045103026240650f0180c0106100d402900d40000102104c902c05400301d2200c824a8a515000307800c603038000c082e5500494200b0401a900045156020a0303c0c100500c03440402d400051501900644035402055a407640582564520722043c1303c107007156040381d59480e05c0700c41980a418040c8000c070b8a00c1014017 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 397332158 1250 397330908 397330931
    0x714030306060415031116050c030d0e1e060a080a0c0804020307060c030314090705281203110f101a0907030c050c0a0c03020f1c110105041701060801 66
    0x10403a03000e01070080c1958142400c24402203d821240c1c0c030300109050b41c03841c850380002c00650103402070340076800c9258010300c0349080050602c800140282d200340c1048038601d0b2102d400003400c184100043c1c0d010070031000d9000d82090341c0148038079010741c001000309425400650211020b48100c2c00c200b028005607140e04e5041d54864170a03100298160013100e01803001901c64000e41e40c02e18080e2a0200b1040350b080c600020161069400c0000c40c1c108940034000340c00c0500c180c007440b01407c00352592074050750301844800180b40c0500031000c5400c4600030241403207500500070002d0010b003541c0d8444100b00c801c9503102c401540c5c29103002d04249810040010044161003103000260103da19680c0d404411401008001d414000703004040c4020401d050f0100601c0e10344621441c15480180c2c1036004200305404850310942c8945c4400340f070907441e5488800c1c0907041650001001120f0b51301c400060302c0c0c90046030401c07a0b40281c40d0342c040d801803005400031000c0742c00a1008000498045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 397333408 1250 397332158 397332163
    0x100603050d09060806240412050714011713080910020c0307060207050d081614060a0510150f031b03051e010605040608060a09090609110f030718060306110714 70
    0x40705c144e94010003d088401020398510320303c2d020311030f100d04210b01d00b640f580e504000118910505a4480c1d221603000c1c80121280b03100420740240c24200300b00c4c8005040004002c00c0402480541212903041c0c1070810000500103841120318018180360740001080310003940e848002d20303554406d1184031f80016259002060349010349801030114100004c144e2541e1001c0d501c415008810840c3c02114003000c035140d800c0f05c0200460301400340c0bc0d2030501c400300700c040e154054112441041384802c100200806244011000441030902c0c004290712400240c004200400762031800100d071701c140700300c025450340c0020310841d048801230f0701c091a10a07610410001c24082c810203e10100070a1103520b010341d22039603001c64010b001410311a1200000825141e0030b80c42120810349411034402085039100720803070811015104150103001000020740ea40c1480d105505a900c003042e11034080348481e40148010b550808014420f43c0c03001c6070b8014559200c1c40c0141d0340c9044034010f010503a14003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 397334658 1250 397333408 397333411
    0x130b150d021606020d050a020f070b04020d1b1502030306010f030e160810110a050405011103281b02010e04020706090206030906061e09010315090b011e0b0301030b010611100603050d090608 83
    0x1001c01c3c80c0c02c3c801c2d02d650303208200700080c2041ea4020480d202010004250b0081e9072000c4a54fc1c0d41c080050b4500142030241c4007646032806c05541041c0104803090b41d011500c402402c0440c41c020845281035000281000c7d081c001400c01180240d030b01117104034001501502149031100c04100110180c007004446015900900b000200c04102c10070145d8440c806900400300e0000513079103014004550800100d410012010408a00d01304825a241d000b0b030945948a40070381c240100c030240b59000815102c09212800c0c483c80e40170076890f0501c0b880d07900c001003e40e0301900480e603270708080190658482042320301501c0741c104041d01204006220300c002c00c04010140038508030380d0a582e10399001003ca10303550541d00303682d0001c0d4004140c00c0407a1500a19070205051106402d140004441082c0c0c0e82050b03118501c100300400016139500a040d044841c03615050713240d0764040a01c241440c10340c103480c01e1024200721001c810b00101280141103108070741c0740d01603401d80e00d003000c1e54241070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 397335908 1250 397334658 397334677
    0x1218080c0c010311030423010203040c140906030a140a081b190503041809150e0610061d040216030905010e0f030a0605040212120405130b150d021606020d050a02 71
    0x4d081c00810002030f0b4940401c40506c8141c00c00000103480c000701503003241c104a50944d4041014441008902046d4480007001c07142510311500e20b14201c008a0381d00e6087d8600181110900c000852140c94140010742c2820352081d0416542c00740c500824030704111805262406024071001001714050500308030000f1039010002c3e5040500c0c04204010041009184021081d251840782d00004c104103694a01c40f14014030000c1c0c42d082030440d45252400007083d00c442e58150307180600415400456640c00d5550a51020b4280014900414080e000e5400203041000c0306210010425411007000c9042d038234280d90b0b140c0020a4801003000031050511045e405030030880300c20000c01c0a540000e03903c03a0001d001202074131840840b06140c950003000c520342c401070100c1c080c401841c000b940b62401c203100c500140985003c4d00b002655082c4000d1206201d881d0005000740014016015150f0120001290300090f48145c14500080c0d0300c003101c0494030030300d8480000c1e400c09007403003654420032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 397337158 1250 397335908 397335941
    0x30c1e07030210120f020409021201090e0309040926041a040303170709050603100512010204052214010e01060f0809030a2d0f0207060c0203030306011218080c0c0103 73
    0x16001401503030200e40071104d00c48941d445010000e10b08550340010300043c500700e080183d607070141041c0d0711a03010060700801580c9083c0091641d00d1a0000199100124203c0b8005294150f500d0182d5441ca0810340c11040b1040b1141120043c500d100c01410449650005100d000301c0441420302da24815408000d002c03071800d500d00305550880c040d12a42c4600b86050031105e00791500c00148190b00200c0e6101e00207090050700740b02600b80416150600640500203505050400d0b000501c5103016500540341c50700003024a000c010402c0c0c01410300c44582c11740a14803942c64605070345120609001e82c801258103204800c003698400d2117514450080c8070040c5d4280302015500320703007200d80d010303070303120800a0716101ca02500444103810401d011036071200c060000310080b000e81018201e52200c82485021006903015842c04800c481c0d000070b0918140c0501705a6140d840000c0c0300241c10040903400d540420001c12500c0340040940380c801070111030b17540001300c0046069407003400341c030b50852 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 397338408 1250 397337158 397337179
    0x304030507030e0f1509030111040f120305070f1a1e01050108060d0803010803040501080603030a08072604111e010903020d02030f1006030c0501030e0c1908030c1e070302 75
    0x2c0d00c11850328281000050201d501001042c0000719110a842e80807038521400041d458031504d402d2243c0981e07880500c10090030240307042030b41d21a4505910412a0461542034558205071003401125039040e4803a482481480803414000340041041c080c2002c1c6007a140b01203411001e541e1001615000d207540ca400c11603081800448410030082c09003900320340d9252420f40024605000303036028108000045842d5460003000400000019150500030381041142c81340c659407000220b5030180307050a003e88d554082ca02e601e001c40c580c451341c2c65400812101840104840841c03c0200d01c0c3c0202d03440c1400741080c00e0004a180f000d0004a4041000c1140170401800c2400401015500003425550501c6540603980e041c0070041c0d2241420a545140c18010084074240d100041d04c002c0c038040004510100034603036a907c4030030b0013a12070702c052101c42d222140c0d2146440042d1211030207807074507500c0400c01155143e592810001c20444906d001020300100052500c040700c1d0000d00c1955034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 397339658 1250 397338408 397338413
    0xe190b010507080a030b0a0b070302060609101a0304020607060f1406030303070c140304031209030507060f1209050c03100906050a0b060f0703050904180501180c0b0d020d1409120304030507 83
    0x10008206c1158001148400c001107a0a11001030203046000750042c0c4000d151010802019260052070790341e030000a0303081801052820103e0713000320200e0402440d50790301c41c1d0000a090f402140c40051510342007210b849800c1380365070425400c1c00c1c80124844169100c1108164590000b00e4400000038902d0303d20802145542504200c0344140d141601c1c034041c0c59468540e11500c00c00481c0d0003180f6010410010004c081100100900b0140f904050078101c0000c02011104040b505031421610398014105000041c0406684014010200c45000c500d0301c1d1a0805410f00100a0b2280b6107000001611100c0324014034102c4d0000030301107132814080c8441a07505400281050301048000d015004480d199442107101ca5804005200d40f0184c41e0b150076400c1d10000d01e8982d1344d403401213820800280114000070280d0303a003800761035115184102d070399000f4041c2000c0181030600b041c0c00b00340b040340c1001e18a800361302020300355041007070b07041d200d02d010744000d0f80c00800040c000c1116802 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 397340908 1250 397339658 397339661
    0x1020d060e250c0317040605100609060516110307091505030102030c190c050f0604061a0a091e0908181e091b030f071215030f0302070e190b010507080a03 68
    0x40c403078480c0c100f0041c040180c1511100c5c0c40d908807411079900343d071201804040a4141c1044c070040a4900c0c08850071400c1c842d0040c10b5004481045130f0030703884035000d207081101c00800408101e40c06404c556100c4d60f64449140036152030094003400c0e00016a0128003803c043c004c41c0d10580940a00f0740c50071005141c05445050142d03016401c02024101000c0003900c21300c585694035032806c00410705406e190900c4411a85810008941c0c3c8202c1480f00c02c3d036446e5401d82900310341d070768000020351990004c0d08641d0240007200720201e00d868181d4040c100400719010389404a00e01100825080340c1d9001d100c40058208080d190649207156460b06030b24004446980c0304110300d0550f40303981210800d10000d5041562825900c950090400502d180e01c002ca182c81e03110b0b03040091141464014544200c1202800084d140818444a61090600801c00c0000400ea051800c0e0700c107203000d2600b81054210340c021085002d040c0b04240d0780c5503101e8815240940c1c2c0000159280c044014010703030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 397342158 1250 397340908 397340927
    0x9060e06070305070c0306020a14040509070c020a0810091101020106031703041e11030f24042d0309150801290307020a0308090616080a02040801020d060e25 69
    0x1001c020003000104c000501c1e28013244003d61040801680b00c0391401c1c405408201500403519040d20103110800c500e6603400c80040d0004402d0030070ba0002c08681c000b10f081c91125800c507451900c2150901c07020b9410541c8245007050140c0985121019800012402d0300c52a00c809051186c201c00a450103410100c010350300940315079107525031a018001d0031480020010815284080c078000c10000c00e080a1001c4411114003034060440c10a0391113040d420a14030007040410080f14200040803c200c1c003049070240f1119601c040d080e40c108840d005000121110308030300107500c0c00400901c0503030490504001402d5510f070101c0c240c0c00c100b0210032490340b44a2a0800410201c000b40c1405400c000070340c0610108d0340902500d40700303400c000d031001c940a042c540d401d038821020418a40e00c41e9039038450420180c0b80181007030315018100c50207400380d50008211544002000d600065156011008558041000e0120341d561030505103410b081ea07101030058020203001a000c62031180b030044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 397343408 1250 397342158 397342163
    0x151109100e1306091a09070311090d0c05010f020303090a06180b071d09220507150f0905060a020a17070f0831061d062101050109060e0607 61
    0x8005804078000060103900364401c1d08503031a907101c00500c5226030f1070042c8002c1c43c0020340b52000e48405013010801c00c0900415400c1059070b24068968061103200448601000003054200c55811034208442560824071600d0f001ca40850000c10302907002105907445540e1000150204140ba61220b402a0030000b880d141039418105244000079540c0d0001401000d01d581c485081d0744982d520000060341e6440440c1c490b814005c1080608185144201c146901d4055803c038030045602d4124980fa2040c1c00c1440c07030110b40403906070816809151100c21030403644d2078809250380d17101444035505c00e01e0100070041c0c00850082c008175090340809140250383c400c1c59031801140c0c0d100d41d9820440c402c01210b000d1000200340e5034004154011030200c0a1011800840c240c00c221404042c00c1540b06d51410700110792983c040395020400003c41720764014000f17990712180850400c00ca010480c54840002c0c0e0392a0011400354890000c4405545c9581c551091180c1c0c2e607410801302e9000383c00304 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 397344658 1250 397343408 397343417
    0x15032d130b07141605010b0105090a09020c01060e01090c02060f060d0b07140a021c02060c040e06040618090c0812040612180807030210021c0c0314011215110910 71
    0x5090308400a600400500d407451001032044001417801d682076845130b815490400c8800d02003d805980c178104968200c03801840010f03514003000241c18007401c0c081d40a03c0b1940b001c04000181c00005405c12600c9215135820b5070120765403180c00e9809854151307900c503005580d00f690507000030304015448da0440c40794200103116640f0107911510551143c0754810058102007600411581906c01c07035003202100d40044d01c001e2400b401b210b18280900c0c49542d520204200108006454039880000a031142c80f43c908075080300210000080d02030140c0031034202c4541d200000b4100c1d0082502e02c0001c2900305030304e207040d140c44002c980318480b003500b1808459544145100c0195003005240170a4810352405455054506001c0e0400200024040d40c8a004104200300052442085040100305140000d003034003841c43c00318010885035044131040c030104400801c2c030f08060304030082214455180401c01c0c40c0b181c1610303415519507010f0081e81c070805002085252410b04081c00c00105140742 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 397345908 1250 397344658 397344677
    0x5091504050702070510090609081506130902040501030c050f03061909061e05040308090d02031905160c05270a0905101506030c030e0d080615032d130b07 68
    0x600c4841418101d200495887d0a041181c940c0042c16040100703003a0002e0080d41203e0050100940c200502a0784900d0741088614075071223003030f841061080c1d0060010440d85d0785138070f0100d011907000e00810303110b01040305103d2114540015100d110b0340d07900300003078141040ca05220002d40007882d022100c064446d51492002e10100822025110030840007003918100ba04024044100203031001416800c40c42c0480000e0f90000219208500706044800d180980620111000d0040c522800700c40211b40c20390f02e080c4081c12080360181c0e58215081403040b001c0f030300021000720300b160b844100d003100c0c24009604681e0950041c40194000c0041d074207840804000ca00032030304d640d130000c4000c1d0300c5184103000c50381d414801d081c11407909080030008564022445036541492034042c3c0d0411201c2800500140c56031040b1080e455501d02c04a922070810030090250b11400780b403000030901c9010071103084101b0704940c04e0f0041c0c5103074115070300d6000144c0710707140b840130300400c824140085500c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 397347158 1250 397345908 397345919
    0xb040603080d0b040b01020a050a231009030305010b07031211120907030303061d370b0907080f160c02130507020c010f020d03090f2a0509150405070207 67
    0xc1c010811088070b40381c00a400c16000781004110781c03001001d40c1c119404491004d00007607001800076507079600400c44d130510340c08040d80712040b0400d12602148901405810340361030002038000d0f9141601ca070710140800d81c3c03a8100070003c4d0007510f0001d400a08a030f030500c3d6010005901800342c100706050107030300d0b20388107a0460500c810262000009a072100400b0024543d05100d17500290080f000709184150200ca42d22029840c0a4000b03000f01000d6443c0c804010000740b43c1c03841000c15262080c0b6801c2044804500500c4207910310340c040d052403000110f11500c500d5240f071051902c5080b8142d652100304209618a2004010350180880e840c174800c09030f56501000501d40010351004103c3c2c1c901218002d0038a0141e0320f07018140454081c0c0280441d8000c6405040e003001d45c85c000569140c54101444900c04404025007180c0140d107428014600b910010355003813079501150b00041d81d4903414484401801c460090f12810601790089a074685038000325040f070160b1049a03662910f52 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 397348408 1250 397347158 397347173
    0xa03140118030903050c030c152a10150302150703120207060221150f01120c0503100605090a0312050705060123030303060306010b0a05190206180a05100b040603 71
    0x724180d01240355404100704108081281c801441c0741039001c2d001a0713440001281c99403282e0240300501050201c0c1c0c503242038001609805602e00d44c00d01030101d00c00d98107103560b21224003041c10300c02107017403210b141000d0344d819905504a035030103842c0c00e040381049442e525039508070302c0e001c800300070340d4041c42c0e86110490300140c1400ca000b142d006039a01c2c003901ca5484214003101c000070f5000101420000f0591445010b500d0300e04040e1001d0314001e0001c001201c0380420075400c01201807400c2100940b90341e01c400603600c18040030720000360054980d04207031900e0098a8031aa403103440d5074000e2002407104103000ca80c07091541811402c1c8401550740301d0400009810040c038404000341200d22080c0b500c0008503608909801031481c505103600441e88034001405070460040300011301051180c880c0003211080000c5e0500108603100050300291110425207040580d00710a840d02c2c03205001c0031030821080d03548100205118082a81100064103007102d480d5481503a0301d00000106124 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 397349658 1250 397348408 397348451
    0x30403031e0504030509041a130506060f180a05190b0a030207080a030e1006050d110102030705030c07083f040906030b06040f0e060c2a0f06150a031401 67
    0x7175110ba40e250b182c0c038001c0c401110780c3d0320829a00400c0c02d102c00b08054032020031107041a2101c140204199035941d001c90468816000180b5040c00000340e140c491089030b0155401803001111616945642c6804014480086038020302011086800070440a003c40307005081003c0b46080150801c882515100d44540003a8640c2000c40e0f203521929407005418845070b0140791000108200190070440850050403000c60018203020182c01020920f030300800903035101e943d018007103d0341e80c2840703008940c40c0c1d0312901c50f4241c41e2103911002c038100700d1201c030f1240c1c4070710359031803040380c8110b26100d4500d4969403500d1070310541c4410000803480800502800c00a140281417191440c1001b074180012101c04c01d1090038801d00e0301c42c0d4030450410206001d50468518400640c85894a079140c0d0454500c0c00003d801d0303d4000d0000784881200031400b6200e041021050318981c0d0381e4240c2281c05240d8000c61290701c03411401c2c003400020101d6050b0144482c1d510000504500150141440e1501c2d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 397350908 1250 397349658 397349663
    0x405150408120630010605270606070312090c151709070506161a0f01051201141b0c010c0c020a090b0d06050c070b150f010212030403031e0504 63
    0x90ba41c90382068079040103400500541c0c080c0b1032030710541c40107201503d000300742e41204890f00c0043e200f0380000b504100e015180080050b04081e0748109200003807070640c1d10794117213100540001089890700400b611901c64054440d003e0021102c240c42004040b0304004441d6940450408150398207840d0901070011a203031181c207044214489017101c000300c014140f04076a4000c00c1c0603c000d444880a07105150708441181c3e04291652800c4400301a488081280c19104403003009611240301036042e0407140160b4210f40c80c422825007043c2078a14100303044004d1031809011502591032060305601e40d0410120b0282807d907100e01d070500351101d003c141d00000e0101040502940f6110845d02c00802034803808022018181021585620102d1406050b02c1c0e99540040c05402c020070840d14065444142d0800781c1c030b81100c0c2800221081d20040d0700900c08412081415400000d03a504c1708401c000c01541503036560358046018005854002c3d480c03298101c3e925400c3c00380ca0181601862 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 397352158 1250 397350908 397350923
    0x30d05090303150604080a080c0a050d0c030906110606060c0c120a02100f0806010e0604120b010924180b030a050607021b0108150a0519080d020309130504051504 71
    0x5080140d50030700c1040f107800074070a10013000108a1200001102903580d84d0003040b250321907025030101780c1000100d02015000e8090003176024a2540d0102d0021036403031003621603030342190320380c00c044a001d040c071180003080c2d0707028502007012490044054590307801e0174000c8458500e4212f0108110440d8084500051f0380302103d8a402c5180070141d41d00390840d18580800c01810580b801401c6480c0a45501d062001950104885454400484024080700081c02500303c20524252401240900c01c41241c07034a4401084032022103090310280445010b124590211f040024850034041810442d401d0a50741c1c0c0500280350b03d05024486100307000f9009030405180480740642000701040c1c007880048041400e01a60380e804c040c2c420340116801900c400400012804107924090a0300000c1e031000759600400041201c1c13101c402c0584031645c0943e21900c600c5a0160f1303503402210451a805840b00742c03a81c10b102d5442c3d0109030310902603070072a0124a0760542c401d030400750507502030300e851 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 397353408 1250 397352158 397352161
    0x120b0a020f0c011a03010516030e03120f060406081204060e0a0f0b0a1e1704021815010905040606080f040c05180402031507050901050f09030d0306030b0a0603020d0b0603030d05090303 81
    0x40d00700c2c020401302c44200780c00034440d5160407007204501c0800c2c41e46001c141661114460300c0c6a40401c10b0b18184851009004001d09050049505c15141200c0a83c82581410303004601b00002045840d158004000039900b41814042d003658204071402203030ba000340030504001055801d050000e001820341c070001c05d645820300c100041082810f0f1450102c6a580c400750442d140380d02c1b10550b04404a2a0341c00c54264131a84001042041e0886400d412032200b08103000d000c401c2520b500c40c1c0b1101c00d80b5142045d0b40e80c4e0302800151515071042002040e0500000b03000030811815495100d1303c0750355900310b21915440081d440020a524000700d10354100d041208600701001041800c07422007500c0b958a01e0100c900811621829400354100240410707102d081d941c1641c10340d035080100400759041b549807150004c00822880c402a01d4460003040881d42211140c46034805903a0060301d0b486114466444030035002030060841c1c0d806110822901c80c8141d850701c112070159421901441ea40e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 397354658 1250 397353408 397353431
    0x914011e030219050c07051c12200f0303070804030c08031306050108031e0912120c24011a040503060420010504050303070b040f17070c060306120b0a020f0c01 70
    0x1004a0080d044c081c0400808100034070008645003210021900a400720820320020402d00404d0380008141c000c0c4006002e00351f0b0740000301e1715200e902080303c210403010a41e04050b43c540201c0400096500200042198941310b1002d655207d8000c1c148040e03090420740e21003a040d0b20440310040c1d1184134800250030881c05009040c01402ea01000f907040c80e0344602041480d0043c150b403a03861000c0024050711503290701c0555004a0740800640b05003840c0b800c1102110ba0042070151903900803609046c00b08148102c4a00071500c80740b0803445280c0c00d02d043e10000e02260741241851100c1800009000e6504002d02d41c4114800e80e1500601207000c4401034a182c0c1c4102e80c2c03410700809000900154500006a40040d0340100007005181c440e8101500e030000c0305100540342c2c00ca00195252811214001014810310480030041b20642c1c07640100c0844915004074100d0b0501103641001203620381ca00b29400c2040a60300515003800c1851400c40341d03104244502441c0d4592501029 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 397355908 1250 397354658 397354687
    0x70201060504150605030f1017010f111303121e0f020f061308031909140d030c0905010c03210c140a05031305070308070f060515010914011e0302 64
    0x9151510f40c4050020f08143d009800390000400d40056006440e00082a015154030301314001c100e001121812230991003c030300d01030b1080072141c0020b241000358079081c4001d0340040f41c0d020a01c526480221a045a0316120700240c25014007003084243c514803d030703812036100c044c160910581c03110a0036021440020342022401d0f18540e103a0b4106004110854049d01e40100b513042d0b0100d80b4a6880da1010360b581c001a640151001d42d4078500800241000b001c3c505051184d0500b03411182c800880490071026a11441c40c03d42c00503841c14010040c030750198904080c058400e0400700a404621100f152820861840f00411a622180001078841e0003101101d8110380c904042884d15500d9a0050090700c0f001c0d202c0d01082c08090010024030500344240c0f405141c1c0718400caa5618942e0520404404a4500c181e43e1640340a002c15021409074400a49400e4103845040b10117181000c0b9a620203201011503050020328407010003400c074461250b031810009034a00503150f646030440c1c81c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 397357158 1250 397355908 397355921
    0x1b0601170d030522030908030c010b0a170a0602071119051002070b04170708070b130b091e030a0206030108011a0a060e0f01050d02122a0403060b060c06070201060504 73
    0xc00b4580b0700014041030310360102420042c201c501003540a000514681141d00c0901584149214000820f0710f000c040c506400501402600300c640c12819a11340c4401d4914550360300009071151300110b51000002e90300e0300a07120355030140c00064109464000404c801d20070690b190494507440a03014850384c0391501c106403445540c0e00c02080705508000e250502407186000d205075070b038401c00c00440f01e21030800032440681000c40035540b00c01d40c0c0ea80281010b03044106400c1c4076042062001c5050701482041d1100540000c0c007090655a045600c00c00c10311100190035014010341041c0703405a21640002c0d4024201e18000003400c104d1a428024280000d0076032a00c2100306007000c10180780c0c08184117440c103108998600c503a421820060b00c1c1d52086000310402503001180a00c0310104080c07010f0f02c0790340341d440c01000c5902000c0311282841400801070305280d0040c0814400702c1c0c4298007520700690043d00e502e02d083721a911903443d1900407501e08006039103030071007031105007007500408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 397358408 1250 397357158 397357183
    0x3200102070c0317041e08330406020412030503090601080a080f03150409060c120b06180f030f100b010206010308030103110d02040f0605150f0901051b060117 70
    0x21418040e4594684001003070b5403001a040c4032400d8602d4581c8600142100c00600c0d000095002c040000a07044c905600280300350103043c02004808400540346c640d400804080c020302c2c815440380e032004c800c28284400740044c0c4104e54284030204082d80e804014404050090300e599407a49000c9544034500407050b00481703240c0d000600744500182c183c03002e0700e103c152484000e80d10303540c0303000181101500849216900500b088113410903c00030703900c071048203c115922061031845081c00f282c207a400110100d82c01036001c10840a401d4032860100d800507070010109111440300d80300203407501c4286000341c5240c0c1c015255000303c00040c1d2055000084080c006030072158915160340c0014001440042d00415841907015074990710f0100d05160300ba0b005004200d0700d01f04103841e4005001c5070046074007070340700403141c4c001c0c401488041c1d60310024000007507403404901c0e000446880e04100d8241c1034075188103110a81100c03040c81503501a000d1039002e044600e01c0111a945000e0704130000307 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 397359658 1250 397358408 397358411
    0x3111c0b1512040f20090a20070c050d060b0307080a032a0506160e030616030b03070b03010308090a0b0901020705010e0109050402030406060e01060f0804120e0d032001 74
    0x55000d981e81810b5649084101ea40b0b0340541ea21810040650042c16000a10000d000c85803c54034800000c0700c42088a02a00e59071206d81e1603101d1035084649882c0c203d0030700d0b4000c0c41c008980d46100c3e0b0040028500c20001c141c12540e41d04042841c1d072001000498a070ba8480500400b903040800c20b07540240f14420040c18074098584001c2c00381c2040c00003803100c5034500a940c4000480850215203000c4e40802160340f01c0c5004640d4402c01d44c69030520100161500c10403145d1071600203147d90140ca0f07a059503d40305c448441d400e038014112002617036014018000005001f8442c5400b0b9802103000b42c40ca59078486555042224902c00c2d44c0148010f24003d001c01d00103a40c5c00981e000c00d80380b080c01e14254003019070005a440c84440d03800164842e000108000411030103402c00c200b2070b0300d000c0410450381d0722a50259109000200d0030000074410800050203e40e4040c41003c1d02003603401c040d81d4113010744012650845103104203502291a91516500c2c03048803080405008950100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 397360908 1250 397359658 397359679
    0x6010e0711011d19170d0902100201140601090b04180b03071d01051027050d0f060b01021c050901050f0705030307080609190b0612010e01030c09050f011503111c0b 72
    0x55490481c40540001545217034080341485000b0800c2c1e0101000c00d400a00101d0100b840d40c100074081c00343c094441c0d0603143d4050104041d5401201224160350702d051400d8101400c00e903449618071004113030404010703200c507185000c0b5203050042d070002c0d00b40210620382d11500c0b039403032841281040e40454051125030404c1510300d584030340c011040390403a00f00a644141e1094513840d4079101d64103c96070215001c40003400b0824001d0a650b4074501c200070074071007070206900583e1150313801e80c020001c40840d40d00d4180030a11610007040c001005050090503c180206101015044401c04a40c50760000090100f00c903000070341039500100c02c40742c900040c40c00b20011503a42d601403c564540d00d13101d045249141e0385000949104d01030f0b21900c0849980d44041c030320305c0c0700800c3c8001e039500814140049140c04103405520311a1031940d829800e45e9280091541620502e20781d40b0b003c25960320824101ea9a0120040441d61000800c03032006002800140d01268440400c09109043d500d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 397362158 1250 397360908 397360913
    0x1022101151e120f2306030a0f020d030314072012040b0f0f16020a170d08090f121905040e070c0309080d020703150e06010e0711011d19 60
    0x12405009101d89441144007012070740b0b1401501c1c404070349503079030360800c490720b201ca02140002240345007941142030111b0720303003030305140c0c54000301100500345c0582115154054180b441d980d036500d510074540025840e440800640c2c5030f80c1c0503201ca5000460703086850b00440141c010a203250742c0d08002a0145403015810100644138511a100c3c0c0a00300bc500c03499030b001d0640175500c10b08440c0b070346c550341c40d00c05a24081542c2c1301c120f0200c0c49180c4a1306e0115240100d00350302c481c2c9000440c011304400d1464101a5414440100808207604c642c2c0c00c0a0004441400074841c0581c0c02640551a035280b9841400c05201034000102007001c107110801c9003152140d40c80d0b80015040c200200f082025040c102c44440301c42c0c21541403445141030039800c03a235000070304504a90107440c500d480300742c00d0f0320440d0030382e400d00305a1200d940c404ae00501c021503841c55016003020b51428203445418a001116003074a46140c41c100d040b120b10300c000f240c170701010720a51403e20440d154102c40340105a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 397363408 1250 397362158 397362197
    0x3070c021206100315110f0919030b01140a080129010c0213050606090d030e0301050604060806071116030501060503060106232d0306150307120b030102210115 70
    0x502c406881901c100c0d0f081001c0081d80e41c002d90000c0c07078200c6c03216500c1107040045051a0702c032100d240c0c01000403884a040c06c101e403110350f00c00d0302c0e400441036540d6440d005100480c03610f018922980300290a00002d42401c01b480313501030002000e5454070710714003034a00c811070200d21500468140b10717528804200503501e042e007901c030062a5810001d01c40d200d0703801042a074010100700c90707002a102e001d030b40180b507008003e000010758102e00a02a9a4900c3e00744000d55416100310034075a07000c0d1012032403441c050001d44031404c00c04c0c000c036140b820014405900041d03241c1d10a4174030b40d658950a20560070107101d420b014014900b40915001d1414002c01c0340813800404468000102244003488803005800e100c4230680d00e640030304445041c00b840668654402d4440610a80380c50000380c010703610038806d4a1283c1344a440e803041038403248281c840981020084954195030811001c43c941d1030081c3e0003904c1d034074049502a240c0d81011501c020710403c102a80043c4841c2c41c7d0942054240e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 397364658 1250 397363408 397363441
    0x190605090f041a09190c0509070c06060f0f0302060c0a060516080606090604060807050f040303030f1802011d28053d110f01020a03060b031608040503070803070c021206 74
    0x103d600c900f04803a10706108506100c036400c40742c0d101d04e01c2400c0c0045072ba0300002d5103119a0156038204025541c452014160842c0c501c221540d0944c0d0300e508001614000c400303840910100b00588070750a0f4159180c1003260310442c1c5074071440178580c0708035404c10390100225034014030580307007540341c21354160004400c1d00640c8244010000b2003400911800d2046007680d0141108008440c0c5464481c80c0190203420511140103015240c110300d00c600100078900d486c54a0b4041c0c40d02d141104401c204400c003680e0300480c094012400811a1804e000c070f03109141c220f5514074140750b000c18245820807001c00c03040e803482c10182140300800d0340c0c00c0401c50700596110950001e400e41035080714200380c40300c0150314201c0b61140a003a0200034508410340050100d8440d580d800c000b61a02c4060403109400700b17882040c0460821500321640902030150650014061821603040022903070302e010017a4401ca502c0e40001d000500460f0450400ca07902c62031102c41c14015015500e0f098440203941c1c0305 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 397365908 1250 397364658 397364683
    0x130f0f03080a1101020c01021b2410031e060b2d0d0b0f04140106030b010504050406020906031003030e0603060603130c050325080705030303190605090f041a09 70
    0x5001a4a802243c02007205030a01c078101d1000b5511102c01c409154002e401401c202071004802e0343c0d03c4843d11a0108881d602640d02e54405180c0061624201903e07801c000d104064007545801c0100228144609400403411203014140300500e080c41c081d81a1048246600e020711450703200340d20885003408072400404400030841d9070340fa212100043e660030f00390901030700d244407400038440400101c8000382d01c507074082c0b018802c9413207441110030300700c50a034400504240c00c010010701c00c0b07280c035402803900701e030140c0005410074a90b000028250360080d109000081100a010010550080c0d00e0300758a80e02294100d0031450030304086407081c40024100113030410300c00b441c3c85c01c00c2014403001c0094100a41140c490000105103041c01c00c1d9a42e00c00040740320280d0000600400016144007078802c06400303182151101ca005c0240d01d0401d0f2004444071b52500000305050f194422400d11600304180c0036151402d0a0814003102020184074690001501c0d08105903100002803c040200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 397367158 1250 397365908 397365923
    0x1c050903010b06030a050402030105160f0c1104060e0f0606040e0103060213080f010e010b0f03070b130b120403110106050907050906070804030602030f0703200f1905130f0f03 77
    0x8400a8010244903000592101022050200196444d88142c5c812482039008122689030100741e070320690b0504000340000b60b1540c070f428104071311400203c0c001520400b000c0c1c0d0701c507110034001802c1e281c0c0e9400c482c9210301d0b100100301d908440001060340003402994914a49400c041081d010074405002c06042d10b60002a858951000c4100b01d000400c4030038243c60140c042011040d019042420304681c940d800c002002030300b8a00904140c01b035640040007402020316080c900394454201c0c00142c2c45403001040002100040c56005181052408500d41918909480c0240602c205000d180c22035030302d0481c040c0055141d0700821500040349082c40c5031601480c3c40061850f00c00c030b0341c0003400c001003c14000200841d80d00954002c1c14032b420581410382d11440100d040f01c18480070a031b000300c03000e0000003001030a08001d0045800340c88074503281440328060116031501e010401000508001505101c11440300c280302d01a0084005003036100d0301d05440b400a41509000151040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 397368408 1250 397367158 397367167
    0x30c03050a050c2e0e0604140a06021914070c090b121204030c050306070f1d030604050f010f0e10110408070314060c07051005090f1e07081c05 63
    0x40740240d040c1c850301d2a030f000841380e0340c4a0b00300250340309420042c10002e182c10f01c64102400546030740690740703813240240014612699261981c0042c424001c0d00c051650041f40300c280081000350000746005a00145039550388241400020103c085281c5601720824090008030001003084e103105044401e10b10300480c2001c0300400280701d41c081d0030840c0d2128850550460a0903548170081d0007240d004441008801c0e80d07500070315131a441c0450b406800944d20036a0b00540c1400ba55419110107031113100d502041d80c2540c042443c1101c265400d0b503032a070200c04c122904850034080c0c58000500c1003c1800042c0520244aa40c0c2080840f07250b0348070744402c070841440c0e07800f00a58000300140b07c01c0f5070102d81c1d40e041c480b08052031000154a00d01600700000c4090041104440455034024028040200840c8079030b002040088c0820f41c250081a890f030642c0c00e020040307001040141f0b148582d5842080781305900c1c260090340943c1d041e4000b000951440034a501c03a0304109151410000e584 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 397369658 1250 397368408 397368427
    0x6011d0f0c0f040f080705150a030c120905150a0b030a0213110a0c0c080c0a12020f0402041401030b030607050f18040603140c181302010e0301020c0c0913030c0305 72
    0x1d900a0b44002003800102007000035014150300703040e6046540e00b80645085544800038000c0c9403412101c03401a0b508104a2180d005100703070702081c6d03030b1080b501d459200c40c0c0d05034034281c0c2610340c0000143d800d075000074105200a0b40640902360850010b0340b00300480c01c072050120740c40310a000800b03446a4190701e0780d0f039070f64003040d00108020b02d1300080c82a0f035151000030140103041644d009444d1800c071102c0200307000e034002a840302c3d24070005221900b200d281c21800c10121603400000c07030b0000c003084c81405040d00c40380040d202a00210054031694006400010211441031250510a03480741042c0311040740c02200321181031003030120082c0c0c0c6e040161b620001d60100075000c2500185060000420302030a441d8280d503540b94001a01c110310b038082c04000c00c40e814803c0c06c4c00714514080100f900c1044810140d900e0910604140315128180d000003070881c0c1001042c5005a00000c0700d03540b03039240900041e41d101881000c1c02c42c9007045910024000c0540d820000e041c040005a603182c1d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 397370908 1250 397369658 397369681
    0x615030e03090603090a0c0b030f0c18030d0e040e0105060f060f1308030405040f0212010512210d0b0a060206070528020f0601050109180c050714030702010206011d0f 73
    0x42c03010b000341845540f03040c44201140c0c1c07010100c4094900390000c1d940400e000c240c41040724050805c403002501c0613145d00c04181030a078000004200d002c0f9036941c212255881c24485030038030440f980c85400850b0000400c1c882034030b900840c1c216259140c04100440c59a507402802c0b05850241c804945560751a42e03010114415007000e5012041051400142000000028019140181d40c20b010700d5400b54658001e0303000e485070105c0f40310303c1040140060f0410441866001c04039208960b1142d5071007425011444c440900c104003154002801b811800c00d90007544581c00e0180c0d80c4032131040c41c0c13140c02520781c00d02411050411000140b10b1070806908407160700c1142070710200303410a40c0b2085c00a5a81c03203540c90780f6860303802003800004a0b07600850440084902d1245c222100100011614008107103000c1d8101c00d00009118038000710b2460a0000c045480e40e00045a07145110300000e403414405a2009211240e902c161106101030400480d40101c0200b008440f640c0700c11000a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 397372158 1250 397370908 397370917
    0x80c030615030a090614070c0210140c0a05011104050a0303030b030a06020c0604020906040e031c0e01020a02031b0601180911060a0e0405090607090e10050a17060a0615030e03 77
    0x107659400201c1401540b800a6210700c0343c0500c5a0010031480d2a001c020075003151040341c40f00f02045110b400f10000d41403201403110300310498600241c403407106888000254026499070004d0b82d01070310352001001024400c124600c01e4605000c0e08040c1762100089480c2401d0000804254503141e8a004507202004160345032540100259200e01d0254412650ba42049505a100e00c8000000c00d400c1c0c03d1503c0303292a007141001c0650300e02100e05400c801690115940103c01d59655403400400c528284054403060304142d0207140c0d100d41032030750110698004408017489410400042140c5102d0941101240000580c0800e0360b500300c0c10404868400e81c05e030560003a200080c0d014a00c0e5000d50b80000c2504112001c008507100c1c020070f195140001c80d0030401003281c05106200c1681d000d5040ca03400b003070245904104545601c007003036100500da4883d424a626000309070020341d20500295a204800360700400000d4549001078800c102500404002e00d1b550f140744992600c030070300884 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 397373408 1250 397372158 397372189
    0x10b0711010f020f0a200405011a07050c1c021806100c051609020d1503230a0c0303080a0b030138040203011707122a03050604030f030f0606080c0306 66
    0x250044005411b0091907002c0070340000305110700072079041503a46802d2040b60306881c1c50000710501c1c030b4002c2d509801c240d400058103950300d10892703030213150f6503440240d0007000c0e01405070f0200b401d804c240b051280903980c041200300c4540340b1004000c5103484507059030742c0ea030b041c600d0080c074024181d0030003500b040d40409241c01185012107020440c003507980c00801104144900c1000554042050380c01e50102602000b80007201d0341030540b500c1040361848011078071182080d9001c00c1c2d015078a030300510b0f105a204070042601d801c03c04c04007a8039803003000120102a0003d103c90181c00c4032180c1c00b4090a511600c0903980a441401541c00941100c0800c1c1c0c8007600440d41c0f96124001c001682c8003020142c0b100344514180491600c150a44510b44203030700c154140c80c43c2011100c542c0c030702e42002e100c07892200c407980c0c4008003007682004054011402501c0b8002845e00302000241618800b45802e11420700300f020030002070386c0c455442940310040001081e02c1c0d40700c03000090a281c0e03440100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 397374658 1250 397373408 397373413
    0x1e070c0b1201051315031b08070e09070e06030c0d03021002040b13091103130302190303050403110619110c0f0f0606041506050304020d020901060f08010b0711010f020f 74
    0x71040007804070300e0505035007049440700021460b444600c410b4860040b5590395202009a0070030008104021000500640c2c4420800d80c42d101c1c2c0c0b220346042c401d07500c0b07040f01c94400000d04c04141230500546010b0042e8054151181c90300201107982c0310460060a070141040c0c1d40020141842402241a0154100e40a41d0f6656403000640859003180b40c100c1c60001d01c0d03040000f2494101d22079050030140ba004e501d0b00b036a4403d0710000b11601a01402d03425030040e0319000c01c190f80d01c0d00788503560714400e4500040781d0505080051420742c030f0320450982c40d8841801d0088010045440c503081541c00c040100f41c0b01d5044032441914058800e40c24154852a4166000c00380041200c0d1011001c0b0f60446a1907910720b0100010754840201d04030208420705414000c2611650084d40e1040c009000325800b207425501050a03c03800b60b00590000d40c1e01d040100c031061f4403565081c018000c21981604040c202c0e16900c3c05086450b10581c1881082100301f151070b80240314840550364040e05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 397375908 1250 397374658 397374667
    0x5160615080304170d081609120f15050f06040b0301060f080a03080a1a09040519050c010306050d021e01020708010c030b012601060e0f03060412080603031e070c0b 72
    0x152955280c01900507210b0b82c4c51a10855641c1d840d0029139a103120b50b10790b0b43c00100d5101c2c01700c600810111090403a04201d4400303c041109145480d03c0c6000e03d00c24540c1e0361040e0f038542000601a250707204095200d03400c22041c0040d0401d110040f54200700128ad00240054049000a0040c0010760115100f85100c2c500090200004650103d680340662a0100107541d540d640808455600c85c49804901013480e01c50b00c181090403000740c0c014440d10403500e602811913841141e048900d0303000c949a61205840407281d5030f01d03006110080806640c031201c604256800140c420a111040c002c007503460041c880c0107a80308200f003600030400c1100030800309501103402000f41c2012178485002c10b045902c2c60100c080045c4a00b409816480611811a4202002100c2545120200b5a8001d40c103004029044d0790501c01a4026445407148002e50a4844009840b000008002d20320030340051180e02042c101d2130f80b02101031042c103411155242c00c20f16000010304002d03005981c01103004113 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 397377158 1250 397375908 397375919
    0x31401090308070915030c03020c100c0f0f14070303090b070203030108010c0c051c120c120501060309051b040912020d02100501060905090604090b040507030303060803040605160615 80
    0x600c449550390090380c41c01465500c08900b5074144100740300c4c1c01540150945400812031007548542c0a1880e07916001d40340c111400600d521740000c0f0160300c0c014075a181c14107154281c200254480140782810110428048100c01500703e8036800403055580200050035410540b0991054150541c08699001c2609021100a503240c200b402030944030f61910500d02400c5010f4190404555400f030010040003d00100c0c000340c1c64070f80c500800c180f0100c0785c004500aa047d010b81c99201780d06d95244e80541e5940a0070500b990011f0348030300149450903005c0c038003003000850328000d80ba900b1000f005401821601040040c00180d00c00b502d03144821100416003a4046000c5610001039800c070352a18035a484440d0490b4000e120314008200319200802090601400c0e403503100200070400912080a9141ca040341e80b4100c0d0112102d400201c82801090341500c186006491014002d5003800c0c00e10f0000b40242c41541c0c1409041d000440f4440304012581e00504a105e00080c104125140d899 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 397378408 1250 397377158 397377161
    0x90804120c08011802060a0c080301170613050c090702070f09140619060e0102030c0d270501050d0902061308010f180507060c0219060801090c080405061906031401 72
    0x822079103407952100008070807a05018000000c2c0710380400c0102a401a030030002503601c0310000344103114040b01e465000c41d0300f40020354001c0c15689540710552102c0030b10181060801800940907000c400b0410000c543c0018079014505820755a02e481500c40c02c1c0300360700c0c080850780000404280918003103019409500724015032104264114255100c49041144000b0000c0070600c01107a008410028940701d58101441341c1c83c180103032403a000c1103100640c102482c02c80d1040c0880e80004aa0641d02115506608996034080c0b00303080f95803c001c0004c1803441030003100f5004a880744040004c0d582e9030400c03074819841d08c00320381072650b036a1007160b4060400140070b880f00501c0c010030350000408160880f07401940c4000500802c030300703044060342c0011903040141d801c811108200b203603094918542c0741c0038043c0ca4442032101c1d072520394140e003500c102c000b10004002c40041030000003140081c8281e00208450b0b980600c6040c0f00014030010107103644050700d0407000070503900109406 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 397379658 1250 397378408 397378439
    0x10207050c04060603141614161110050d02030601030608010e0705040c05090d080a181e09060b1b030c0114010f0b0304021003020f130314060108010b06041404090804 73
    0x40c0e50074405240c0e10181601100e0740345510400c3c1d50403610000c3e419800c40b51409607c0881405d000c00f0910400505c85020740182c1c44510008001c01c1c0c1c031a0078480451315001c1000411a0040700440404074010301070700642102c2214280c012003c00c040380e019401c0300000c0e00a000c000c01020240036601035580d00f140c0305442c0198642580110f415114104840300c1a0700688040d140c4803207560382502c103500814209040100317164140410b1912040c3d000010020f540201c80e018412041c125070b48400c90748409040351420360b0811402c0110826179240c11800510480240600300c1c200e42140b01c7c00c44455065464107000e1001c2c00108a10b09058800314a82c54102d1503c4040c41680d5110075100a90f005841610070410103209800074500c00c0150b0b1f000504110b004201c079441c616140e002111420345100346110f407980b041040e1801015a0b074000e01c4000031410101c1da10384502e008819140d001c00d54400b5540e225030b001080d40aa20880c25592107075160f968281030842c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 397380908 1250 397379658 397379683
    0x2121f05090a0b07050711033009040203010308071716020f120303070315050d03050910110d031b09030b010501050d0905150108070f0303080c0d0e0105010303030f20030a02031801020705 82
    0x44101f03c840b098140000c07400c2e1840c04903c030541c03022206501d260301c00ca00181160b40085d5007000b00308403e071102d0014500a51040c0d84070f40d2241c0782860b1410340d9841c2c1500403a24008140401140c0118500c00c110b04290183c40341c28001031048049051303c034200c009580b0f20f01c03001051004d800c0d40741d4400f06103c034001c8140410180c40c0d40030400c0d0121841000b23000a0740031310410078207150960317001e03a42441504200300000f8880030b0840c01d0920190303000010a64400310030020b03003010115000c03200c0b440d1401d40d113264110f50b1503d9161006018481c1000008603012242c00c442c0c0c2d001031402c076001070842d0840e800d0812608070321202409410b502c0d008501c0700007011100d81c030f030003401e40340d1640b598102035807541201003c03a00100c2070303441c01c55120540c1d107070480401c0c4a031902a50207581d021031000007190880c01540c941c0c0360701030003100c114012006542e4003001500d070802e00e1441c0160ba261110a1511021240070600c1990380d48009a001d04118000554000003003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 397382158 1250 397380908 397380923
    0xe030a0804080d0e061206030316050a030801050603130605060103020d090606140307030809240c1e07031104110c1b04050f060907110102160b0402121f05090a0b070507 74
    0x41c1c544404440f010f081301e070641d0b000041409070010322240c045109038001d402504480c1001b17191034600c403110416102c255001d4014540002c281075101ca00a400340000356851851070811140711655014030303542c050003c80c0e440000c554079078440c3d012986600b8440100380a440198203024006180a00c42c0c401041e007029540071050401141160440b0b0300400d015080c0350800c410300c0a80f80c00d64014070f40004104040c1603495840784060403120380040001c1840d4400d0302541ca24030311b0001d00d0101d86a02040e810400100e0086100c44800c0064402050040301b13108403109a00410aa4404501800c00d07a40c41410049a02c4a514202100e0511203501d030391010001408083c1c2d5200d4002c1c0302d0030000b0742858041d04154008a00040005180019001e102c44110f1042e4070110f40c620080020b000951070424000d149242c21403014140416103402203c00d2003a40101400740540c5a0001880d043c2d400d1200720701540d0440c40c928010318001400901550281d981200e005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 397383408 1250 397382158 397382173
    0x8070f0f0216031a33060d0c030f0b0406151b0b010b07061a010804030e0111010e030403110301051003200604170114160309060b0301020a0201020406020601060302070804050f010e030a080408 84
    0x2541c1690b05c85d10070301c59490004410030480003001d4200c80d055066822030350400441c14001018890150b203008a80e40000d0344040d5918030b50305542c49050004d201c0d90502105009200180039422010354180c00c0070307032404503401c8000c02c0032030a0361405420040380900014450388104003c0c03a41d00d114040400005401c0c016110b00c2c0102040ca46001030360001c00100001d0054981c1102d80fa8141040010b01e02c844100b5820350b00c0340c444030042c60b04040703800c0081180400442c4041c0200f10000c0c803c5180403058003600b0340c3c1c3d41c40003800003c00c001061296a00c115510940350a0140c44150349584814113002000092020310400750f1a0285203c1816440081e2034090040f80740750020802d00180b045000d8240180140c03107407035403048085503641e4248020080d5041d035800268503a40360030740c041e04014059200d1014940100000000649603004440503124120394400600000d9001200c10034040304c042a054801c008030103090109100c06001159848011079940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 397384658 1250 397383408 397383421
    0x314060f07090e0f060f1917060c0d0b0d08130501120902010c0b1806010e010e070906090b1b01020d090203010c090b070b06030c090708010602070608070f0f0216031a 73
    0x90361001d10030111000d101001044c2d06404411680d81c01200c01032803405070700d002c2070004508007150340d008a80c034039440008004032400d01070078000b40e90304d90010b00b25520344109110640d124814a8402c043d98541803900b85a9440040068198001000c2c030749405951a201001d00603500985010846a07940c02e011081d5a0003284145681a9102c0741481c0319941c90b83c0d020207000d064802100c10a6801014a2204200d4980200716070301130002a545032513080301c0a802d015044104005500b50148030864000e1a1042220340840c0180d5a51410b403c50411200e400400500c00c0e50000800d00200c00f2240c20008640c0e000300c00802c400000103c1c1074032a24140c0c0300d540b0501c40140442008254491a165030003007024080c0c3d1000084c44c0c00040e069001100e02c0c1022a8040d8010b1102d943d04124103000f4003a141000d489a092401d8054004808110a030080080075108511207500c00e000e40742e144103510300000d07080d5460b4a809000e0401c0d0303c000d9948844400d001442 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 397385908 1250 397384658 397384667
    0x200301110f1204170708040e060102030301120f020a03152a0f080a090203011e06050a032a150c0b0f130f08281b080d0b04060314060f07 60
    0x300032a000d980b8a4541200128110b0301001030040e60103101c0078218040d03040745070b4010285248280c8011303030f445041183c610f81178400500100c2c1154401c0c00140613180d58040b000103029001401180700b50450710010310340315501c1e04000c00c90410580c0c880c900003a035800c213044c001222160441030010659400c0c121380302804090740001c03141c801080445000c1c030f02d841d410941d0240040f80b02c4a650f00803a00391207106000760300c1d0521000e11218080858801d1601134082195031009452444d00c6080703500010b400403103418004411400788004096030440018550390720b41a82ea201e03900c2d406000084010f50030351711280c2c0c11000409405a440d0018401c440d010343c2c14080c0fa00c80c0d00c0c0d101d44400c003030200315444041000300110300d003486091b9103444c6282181c0f002c0700069a06000b40400380e0081000424a52140c1c4640010040300684521643e255800a200100040000c010305036990000e84904020504216444c10216001d03100c0c034502490712616484802d011217 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 397387158 1250 397385908 397385917
    0xf030c0912030c0506040807021504051302030705130e01262532031f0506040b0d08041502061302010509040b1201140a0902010509040507090320030111 67
    0x50000d54520000c1c40154510000008014003910300042140119500d03249048020f0300c0644140f10041038450851804100c3d05c40140400320003d420301d403503d00400c848079151903102d0207098001c800942c19078441c005433040130854601000b40507594070b00c10310460b1f10a0040081b901402c20708020a0300c500c03080c040000c0c190038014111003d1006c64211403501003510794038404140f000c0001daa40540c2800c550041c51502e0301e00d141c8103172241e8100d203420611080d5000c6d82000d040c240400c0c49003003c00b81e48841c444404115560381c40002801025601c41243d84100382d4074910003440701441c00742080d642c81c549403402d40024010140e0340c60000f01c9054000c0f045001c1c4600055110301c02800081e10041d001156083d180000921104020a41c2c2c2010ba9034a200900442198441e1030390440c5100c142000840c11640000f02184250700080c0d00454560001c103100502c613078480070080d500850240383c84a210322505107007609c100c244078130035800c001a81c00c49d00500811034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 397388408 1250 397387158 397387181
    0x402031017071a160c14040f060b07020409050319020609160f03150605040608161a1b1207080c0d0906360803070b0c04120f080c0304090b010f03 64
    0x3408007103103422000f2403e50100d24052010740605480c6400905404205c001030b248101691b4075411400c030a02044420b000180e10059081010400540040400311f800164059074045a50886820114070710f00c103d2103031340602c1060081200c002540441c8407802010003000703403917440c60008843d4896001500500ca04180180c408000140c00111003840c034011040010604564403c001421601e00e03501542240c0c010a0074800880310000318503010f07181c81d00e017100489003071816071a50341c001c1d05440030095581c0b2900034a9541c041007032203d90200d440019640394014a45070000380c11140031641e01e44501609080b80b10b00543c000c1098030683c1e964640210b04e0301c91000080c03030142c1000400b003840c05101000410094440c03e01070031111005580d81c40e007034509481ca602c0c009061855900040c131003440040c1004414030320454000b00e1a66401e20345050045003482420180da086110010f40014400c0ca290080c0413448000d0b03d0b00c4020001941c410b40983d950580c42c1c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 397389658 1250 397388408 397388429
    0x120603050c0904061b1e031a010e0d02031204180b1003180212210c030403020103020a023406030b010e1210110405040615090e0a020702040203101707 66
    0x14800582404400303564000d000e101301040c41180b203400d40c00c4141518404500103112010985c42c0c6401d25801441e03640250324040005001746170008907819070402d0f4184c10002c410f004a480340e174400c8a00050240c000701503648601020b0710408050344036100c2c0380c029100c2d03101400740e0420b503407060f1286048042c00d00c181c400c0c07228104600904010003070600700f400711207154001d40c5a150540b480d46a20800500828062140e00030002c1102030003001c207200700304000d0080310790100617101103a50a003400750329205140003c0c0d0400c0700242420070b0403144610546c018801b1034812040c00c0607208020a142a200d5904605a9a8690000d40402c05550340520542050300f001d20403c00e0300300c05e943c01c10101c0e200d240f06643c4904c6101d01d141c01d001c9420b110900d01885088000c0c01541c4180c00034141e150303c0540102c83d1880f9403840300d0410380c0002d07081c1102c0e270129452543d005004541e0703450103030711911050b0ad103400b488402240c180000107040703c0000f021410307030301c030f2602 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 397390908 1250 397389658 397389673
    0x305031515070506071803020604173f030c031b04080115050307120c0b0307031d030a1d03030904020c01090605011514030705090103020d060506030c04030312060305 73
    0x141000e11600344024540189100c0c1c0200c042460380e50140507070a2180002d05240d00b061907006102001c5401140c01800070400c081006076928400c51b000c03600140d0b000d120301c801c5046124201103c8040405140c2051541a052401200003040703841c4a8201d56541180d9106950b0300980011900c0d85c41124017000821600c080c00a01040d00301d80702ca059074541a2280e5030582900c860b19168040244060f009000718603040c0f02e004041c14800d501c540940415803101160300b4224851440300307040010100341c407d4800d81081c0023003201b1382a01a0f402101c48801d070350340d038040120300c000103d0200124441400c00c00311840b480034018020f6060820a00801009501091070420a99070310075101c00000e45a008440c001c00c248540707296070784144000500341894000752044125000c1081200300742c2c03c41d0a407550810b0a00c0c0c0140c4458420160b10700038045a0412a032007070700401001030781c01c40f0300010300c29244a0b569070309840750b51036402d07010b65942d40401812900f084030f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 397392158 1250 397390908 397390921
    0x506070216140d1b0f1505030c0c0109050d050301080c101202091c0b1902090307090e1005040c080705060f090f060d09050303060f010206090a03050a0201060f0b1e0304030503 77
    0x2800d11218080040050051030202d07030b500000c40d0388038000e0341014401400c003005101101c5d201c15000f4249225401e0b00030b0f8a80d10010218440185004071004010400c0c06407180254000a41654001d01b00d9881546111025000390400d01c6a0341c2d207440340c0705485105040001106200081540781c0705284400144030502a4014500700340d00b040803d0326030703000b042000d03d60440c103e000c3c0841000c50b0811003064840d90880c00c5007020041c1c01000303489055100050301204a8482960026161024190703c60910640b03a500c0003106082c8418002403000c0003074400200c400602c100c82d0f1140c1c4d5030b818048940134000b0a401d100c3c6060002d4201400e007940c40301444900189072502c2c29100b42201d10880703041d04c105541650001c4200701440c1014034941e0f00c1e4060900017010185848040113940d40c00c0e10500404101012540c034a2260003500b12101600503410300311251600da4001802541041e001070710059504103940d0244000307041182c0c0100d400d6684d5610f1039440c203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 397393408 1250 397392158 397392179
    0x3050309090108150a0c1809020706150e0f1509041506080703020a0b03070c020a09060e0f13060f0b0a090b0f2418061c1406010203070b060f0306040f0506070216 71
    0x1319040c8913200c0802040c7c0040c0c0c12130b50300a041e42d90303c01a1241054280201110101a41c0ca20b0b15800b01000b0b00500d54042c10041d80308204080c109803583e1181c2c092150701800c1c0c1101c6400c551480140b20400c080314400ba0310034804d001e0304200b41d03503035149007a960380301500c8060f403c084205070074003110000700d00031603003e942030600d032030240ca0780e5001c610b480c00603a00c455655640c0d8541880030301c02d90f849a5411405170102184039061031258104414600003005005c241c0da030283c01003140f4160003c50030500c004100315846a6215014000341035042d0002d88030311482c5500690070301d4480d00518040c2c4180003a141a03000303d8030500040d50120040e102d100585442d06002036441c0c400806000350b01517020703024403550302818030a8641400a00604414060401071580d13030010985483e140c00c203019440584500d4003088039600c4000c00340b078042c000e6008004c18001520b00c88040746202e101104c0b5a0350f95482c0c200e840360f200d041d4412860454503020000882c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 397394658 1250 397393408 397393421
    0xe030606101b020a0503030c030408060604051915051e090f1302010c03020c0301050411011b111e0a06030b1302034b01050a060207050303032a030103050309090108150a 74
    0xba0080c0e48140d142c400207442c2d0b4010003908c7c07102e80d100140a000420f4180030f41078000c0c006843c14809401c1101410120500120303180780060742d11511424811041c01e00440141030280040c0342034042080354200310348802036640d000b04007500c0820016130303061350050300c20301d54282c244400e80c8182d0300454003502e001e90141c0451103202000344180c0d801f80b164900440c452088000725100c030100141000d0100c2852000e01c020560b854008543c00d80c04100302d0400c116008242d00b101040310050b201800004140c1000d6501000b0810710f4055200141c9110101c6610020303140309840d07242a0702c81211501e504030342900400c112030200b0b00e00e503e00da5110031008115282c59141c4010780c5c0c421010b132b044900840c98010400b5042448100004d40000e1001c0c00b00b00781080c01082d60383c40007500d070043c16541e0300c40701b00842142c0588003a04034000c0490603525607603400c207656290015100300b4401c004840c000202c4c07500010303038107440082c85401070302c00b03a842d0324242c0010540c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 397395908 1250 397394658 397394663
    0xc0311010909020c0304330f0c05100504020405010e01030f0b19020c0d201b06090d05010c031406130f020d06060c0c06050406021b1302030103030e030606101b 70
    0x1403510102c2e81100c10300181800e03140581c0196110707440c1426003a41404c0da0b28000b01c680c0d42c0d841c03004001c6514070024180c02542400d00728078042400c0011640000c5840b005081402032400c00c50a49600340c201c280540d00803142440b00e81d807a58030800e801c8000384002803000b1091702d0704500181c03010000b103511094070301e0422034680e442d42034001030380e002240c0c602c8170790403180505203000c2d04034000314030b0b6000000d000080b4084016206a903840e0380d44110380c1c441054001421150380700d004840380402c000d02050040340c40e40c60500d0180c5039940c8583d0200303080145105100c41d031400c0c0b0600c01c2c440101121007201000c540c04000b81061001c1720440d603020001c1d00000d080c94026a07008043e540d4a032030310f020305810010036524140d0898410080100320070801c0583c000740900e0008640d2682801240c1102c0005190401111000180303d0001c8000000d050300710703a4003811200306074143d520541d541030030803c01903400f6000b980400e080c00002c2d41d2010140074104901031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 397397158 1250 397395908 397395917
    0xa03090309050d0b04230307020d080408120c0c1c020f0a0b030702070603140115050a020a0c14030c0f030709022b1b080606072d0606080115030c031101 67
    0x1038031003010031040715281c681138405201c4001484104640b900c159000c4d4840000e1003506103800754a82901c921494201901c1025141d007200d040c06200b80c101c5001309044403c841440407482c0ca6072a4a410800c03a141c018003d94800b0f02c010704110b00344880405000219100e2100540c0c200280300c100030b0242508000e0038040810b112401d900118000d01440d00200708841c94443e006080d1814009250314014807000101302c0030891414594605000381000307510341c0c4162030101c1c42c0c000c0c8003070081c04507520400300040540840800442c03901084d015100000001818400c1c503044415290b44c250f802504104032952580e80500510000c2d0100b6101e1402018040d122002d600040c17610803c0d0340d8801141840f9400d209160303100381c1410f00c03d11900d40b06000440c903000d41d4402528014403409442660003014406107150144003448120620759814500c009025502448904d580b074000261740e9500041020307400c580c0c2c004010f481071030a60f80c496554112515104d414031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 397398408 1250 397397158 397397177
    0x1090603020322211110020a1106040f020f120d080c2803140708040b060d0210020c010f140d0f09150e1204050108060d17070b010306051b0a030903 65
    0x1810711200200a07140104d600e000410030503260308420491601880040c000742c0d01c40740d1007104011841001403000d0180050b01c40c0400107003900c0034040c100c0c0483c5240208401c00042102142201070458001c1d03441d03c3c1c9403a410350a03c500b809012600a202c1e48c007041d01c01c69068426003400e540880159403243c2400d129804400400c2da80e980f480c00d00c66040307920f030700390103038940b0dc0c4c100700f4241032500e41d9050030000030181c41411f0280025100303030031080c00548030b03440784400f9004980d40070300703a10303121840000000d4072454400d00e00303400608025000c00881e481560300d640c440c2d2040301030900e0554051400340003014645202411140c03170b4030f540740105410f40f00c1c0d02180b011000000c503014178604227640c00c0c1103c002411104620034401444242d81c0400c0d03095010000b030b10b010030360300c03920b09000e850780180c541c00000c1a20000346400030000b4424555040f81c1c4207031020301c12502c0350103034000c00b514001661888403a092000301600391180d00700c4c0302260300904101005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 397399658 1250 397398408 397398451
    0x1505090a020d02011202120105100903030504140105041d0f07020f070b1e040602030a030612031202030405100f09020906100c0f0c1e1d0105061803150a29010906030203 74
    0x1070f80c0004101e0901f20820400410490030701e042c3d202ca030f0030401e1134803501c29411075a0250240c0503d001c0c445458403070603911941a40180102c0d006801ca1190b500031601c226143d0300d210341710455080c155089003001040d0b030320380001030300908009003901030955541460182c1c88903400c6a42d05800e015000011501d9120307240c4001c00203844194091a6101e0403184050705465450340010701c521800600c1102003030b44600084103490712440d0140e52074450b03080003494084040c01c0160701c0e40c601b12707804640380d006501000000b4800d031110380507591102d0030020100c00f9407203c3c1340030640c01002c040000702c44084102d1854842c10100a02c1303520781c1c0c412a26441c040030032407009084408117000c066014689502038100480854060398144000304909001e0b900030b20200d030101e440d41d260259014041c070840c8046d08080c184d40b61902403506c40c00b0385022440c00801100303607100e07491140d008120344a820745040e1100400145003000450007540000d09190b40d030848800d64030726 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 397400908 1250 397399658 397399661
    0x302011805060a0c031b0f0206010e0106020c011d09100f05030303040b0105010f0c05060903133203070305010207060504061104030f020d03030902060a17060f1507020a0b0310031505090a020d020112 87
    0x800c108540d444256221f5480406443d0007410b8000c04c202003034200041040d41c0c0c2c000350000d00a90281303001d039050100340100c5620820210388095001c0200d04c04c203d0309401c030a015a048403907020740f82e0001580e807424192244819500a0324481c0035034010300165008624904821440d40b030030380040d0001d511210700b040380581c1d00d031801d07070400211003c90820034003041029144000f0038441d0f040c03410f10300007180e141c064241750041001c1a000e0f00140ea00340180d500442c2c100b8000e554581c01850302e440180012201103510919018900c208105100e0a81d02030365800100e10318648080c1d000c000309200c207400308608042d110b114400042e00c924001c1c01e0410b815031550707003003843c04000300c4c2a041e4004110602803842a140a90a0f80e1a80603442c01c1c41e41c0d07410215926003040c00407a2100c0b21a4000502c040000014071440940c41d03640c0008036802045400c920003e05200b050640b030003030305c55a04552014480e180036191620340d0315121441410019150384a1002080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 397402158 1250 397400908 397400951
    0x19022104020a03150204140f010f0825020610060201060e0c03060613060203120a180b09010b0306100e0a0207030801180905010f09021e0303072d06090302011805060a0c03 75
    0x62150046000c00a028100c8400008201c0444442450b590503000080080c81c2c4503000d0410400bc036004120f9240c4031035103075001460050701e401502e040c218130180d03694006490312801c0f00c1c040100042d001c2c1c4180316407000d440038505101403036128546d40c4078980c1c00141c07100d64000c0301001052403640600039010000c0400c2e401464903260090400300c049034000704001c240c0d5003010019086c1d010040a04183c2551004d050303103031512074550460042403920709241d054828070083c4010050300c10030007422102d40c041341444075601c0301c0c80b0000740d0080380390003004036170217200500ca000d08840c0c4000d8101c452050000384584c85071030316402e45080e41c0c42405120b41d1120050103509008503051442c0004190407105030034080c020035030368840c14078043c164200700c0440e0054030105c05128030f201c0e0700000584600081e03072300f4100000c4c01400720480141d8a4418229510480840600250358004010308801c0e61b841203c00064001183c15004041d9584103282c1c07451194070500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 397403408 1250 397402158 397402193
    0x230f1803131413090506010b0c010b0406030b180304080705040209120607050d112502010c0c0807090e010b0a0302063001030501110f03150604090e0619022104020a03 73
    0x3254200222010303c031200b042d400401403010300b08980440402d20005085044500c7c170b00c0700319038914444855a0062501007115603000c0e0401c103000061020702e100c201e01807034552488000d003040c100f807100c0e5030f44103502c5005002c0e000980100003030300e043c1c0d01404e06d082019102c400c0160410a03280e04011080741c0440220350007145c1202040000e00c110060141880ca016103040008900340082c189802c00c05440d03040b45140340803c5900c20040d040c07030290b02031400b03a80191504540f64481c45035009400109180070079503401c032a41401040f09070380300985581e4409065400f408801d507c00901d0554400000f00c006880b81142a00c20034503c070b00b04001c0d11194154500039003502c4000b800110142e0b4144805c0f03440d10001c204481e08050002900d1880007582404103a29000b00d41c46012000e00c1d001c1c0c40b80e02c040002c100f4500c512000c140c0b080e406a8214003190880c0550030070340c81d2540d0072003010600c689041c900c05800c64001400c1d914800e40d0303503407001000c08a002c1d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 397404658 1250 397403408 397403429
    0x1709010c081c0606050c0312040609020d030824181b072006070201091202150a03020d11190e06070f05100c081302062b230f180313 58
    0x2c00111850610030a0f0140a640c5056450565a9040c0c03503500d0180c1d8801c21300b0f0111003408142048680c1c1d110070460769014207403c40005080c1170190040000300c402c60045000680692072a056080f00d01d03800e000001c164003038280d900c04030a00392400c0240420980b12521031812040c1d9015806000401e21410468800320401c5036114040201c200d6501d001f50000e102da00e00507030b00041c031072044c2c84065025140c440514000030381c5c28040ca0440300f403400b200003020724030703145e042e0020a58408a1002400107130f0f141d88804680344180080c80001101d048240b48003903104110640407080018401ca0600d081d584800040c0c1000380000c0f580d1354000031551070030714018001c040301130b11141070080d01440c11081c000308554500340000c0c0f0905000482c6040c916002400e4024040b442002e156030f106528607800c02411070018611800d032901d0b2240a119100580c603d200300802c0140038050f171100c00b1640c804c00c0f82040308644602090002c041c000040c1a005001401c00845 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 397405908 1250 397404658 397404697
    0x1802070f02031e15060d0305070602120c03150f131d030a110f07030201050a0f020a061a0f060304020d0303110403080d141e0610030f0204080303040201020f0a1709010c08 75
    0x24542c3c6060742c0480c072658012412000c01c115644d82424a111b141c1c0c050800660328000751804100901c9010b079002c282e074040800b8498001400c13005148140001c45810480301c1d680300810086145410660358003002032080c041c940401608610095400310802d203852620484203141141c00244102c0d00144091140c40c000d001c081101310a02c1c00501c025101d040d00f5600001c2452103403161b00c40c01c2c443c140001e581d0042c420048070000726040f00c4d080010b590f05040d0180d80f9940f124a07648500211010b114062600104590040f50300900d005003d00040d03030143e02810b500c1d00c203420106010300c40040452034040c010464a05405400100c8254105038284c40060213040314a0703c0c44060744031504100c41038052034000b601118130542d81d86421400310080c00c069042008140e001040010780e5202c00000766024034230076000c4c0d803440815488815a60419440023600b401c200c00441201c404080008040760721042c981300b2070510044d1514401c030741c00031070041c030446403108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 397407158 1250 397405908 397405963
    0x20d0e011109030c0a060906200303040c05030c061c05040201020a05100204031e030c110303040801020f0c01060e1b180604060c0506010b190e030106030501290a1802070f0203 77
    0x111030b05441c20103c0311030345520f040a00c000d045c021603004003028000e402c15580c40031079041860b0009c5806c40030031a0340d02e00e0a443d1927481c0c0d15051080030300170704c240d04200e00c0c24500681a19a0740c503030075403225042e400e070082c203038007411001e041603040d0b0041e904080c000c6038080c06541c00c904584100969183c2c5145055120030020900c0c46040c0110003e22000003548011a81102c540020f9080752528071900000e041d4441c9611120350b540c80000c10100030040c241c00341c034100070442c008120789592099000300304103003241c03001d01070410000c084580c690000f01612504201c1c0051140304407004002c01c0c902c2c1c3c0503400000125040039207900c1000800c102c4580505000b1141c1c9041840001c040b11001c4a025058000d1010502d2011000d8a00754814001160040020702070003a502002503045032136240034044003040d0715103890950818104010403941c00e107003400081030754000704a000350841c110482d140d0540480d40000b5a0303042000001e86100000c4e0380207106443d2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 397408408 1250 397407158 397407163
    0x313140105060f0f041104090e0f070503030f0a0c0f08071e0305030a110c160618080c061605010c030608102307020703050114060a12020f04020d0e01110903 69
    0x888120110380c104020080706445407400007141c5641582d1000400c075000001030054000d00c14181000c900205000078082c0468015896810440e4145d806903a00107078150344a110a001d00c9425500c00c2042180411541004050700406440c010f07268414039520f1680d0305000010566003288003041140500c000100c4040071040036801c2c0359058000d554028196000090140c00c81954038140391030070000f00c004072082d5054213030903204448ac03010600c001c2d10280c0d0055000241001c928603180d480810b2200040e5507050000742a03a80c601820051554800f0280c50180759241406600007803007402203500400403603c000c40c040b403c00d40d40030320b400780c40703e5202199030404060824104400e00c2c1036010000c1e214842100d941e8091059103000b16a500c003d00c590319044a0300c9107207841c80c007032900440342112540052503840000000251150402940c804095585d100307003890103500512030300c4050b04c00440c0c404890a032650031508501110100a88d00081000062405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 397409658 1250 397408408 397408433
    0xd020d090501030203070e19050916140c10050c07140601090b010905060702040c050c0607081f03050312040620120a0501080d08040516061e0203030108032506020313 73
    0x3e107011070540c541514010403134140c0b1032801e4000c1000c0090744510b58038601c0140302500b80a1300340c1809040001070442c20817610b42c0b40390700180c2070b0000060b000070498202c810f188002c40040c00b880c4840c40c03280c0d004107400b40400742000710030072481c0001503c51240310007100b80f1790050030042d80341030701e034000f600c0500300f0b4241001180f46041c48650390b00340c141c1d1132464042d0740020710b501c5026400e0f1814400c0f481200f2a61180c5030400059540c410046442090020810390995100012001c061144e40c0030040c22074006000a00c01222001207140c0d1280c000c0d0404101c1c07000c56a41028618900d01a500e00440000b034490001ca001c00c803000c1e0420551442040a50700d0210380ba03031910b440e0000c990411a140300482c090000811040619090407156030404640c1d07130a02034000b11a0070b12203903203405c500c40c040c41c2060010090760b041304c0c001c80165107019003211480d0400a54000c80881e4556a80000c82c08a40f086c4003462043d02c80030b924800c4003019003016540c0d10340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 397410908 1250 397409658 397409669
    0x6083709060f0e0d0806030309060310060908030a1d1809010b0306131101140c03031302040f09021c03110102040b0408330903070605240f0a05010c080c0d020d09 71
    0x10300140c3c00c0720400004800906003451304d090300250b1a941d00180c114801c0a824540c030400110a009402d03902e80c0b8001e0072a400ba44440c4040f541d111503094407406020038610110700030b0303042d02c00c102c0100c5c1c503c010420001001d8504032000c0840c4014480816204100309a40d9441c4070043d50604104041d0005c50401c04203030700c00c03429980c0350b5401480b1030031181008009048040c004846000b41c60090448005894580c64001c501c080c1e0880000d43c1030748180d04214014440750b0151080d40702d1240c000d03180c44407402c403050032503854442c182400c508000032001076078003400c020700c0600041c0c505500c1095840781f41100303a03486c1807628403121141c0c2002c0051042c1c600101b03103100c00303190007000340303500155503031001203055008502000c0c002500706010441c20708440c44008024040b4402c040300b1181094060294208601c0e01040e003000100b1424403096005402100313443c0d105001c11443c020303108070154149419164807170050b900c12801040d86a4208200307002412 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 397412158 1250 397410908 397410911
    0x61512060c1909080715090b0705070311010e040513140303070509011b0807030206040c090605010203030f040c080f0a020a060e010210090203010e030a050c010b0103050106083709060f 81
    0x18540030315049845407200026440c0c1e000d03822100c00314021a40080189440004d03603c1d01c0e66540c106d5580c1088403039080b4002480800e000c01c8800100307045e182080d4000d0001c01d440c41c25940c412914030380c10700c062414400c0d0301e44043d24a51701ca008891140c40444807010b034122061070404e41104220b0130744021134006100308044190300c04d0582e80d402c6000d00c0c0c0580d40c0901c7e40801e069960000c0e901a041420025240c014190002182c5018a12030301c00b07000c9a9580d50110340840b02c0714000c0d540180c00410200314403129403808282c015002d985901c00c855900c408003460101641401130381078128480300d10644c0b8240301e900004207400d0810045042c1c0500000751600110809407003040ea17183d05100c103544095000c2d80070007c2c2001220341c1c8606100c0c0181031074001101040b80c035824030311207481c5948207004483c100c8105d0f0f120b01d4003c1c0c40311310002c030b02c00d201c2ca40f02500d0ba1841041030020f03200300c108015003444210000113103054003070030004d098903440910040400d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 397413408 1250 397412158 397412161
    0x5040e0109020d030f0e0414150a060906050310080706080f10030b34020129090601051c1d0c030a05060c180405040311151003120201090506151206 65
    0x50711101084003e059040c60448007403540017030203441c146040078900c3d410030301d008140409078110031003190041c40106416901010030508002e111149406030701c0018108403001c00003980140051f40d00500103a5034880010b40b2118860b1405200385e00007000501d6010601c0b0011044d1003140784c22103458600d5003c100e003540c40e034034401d04019217100c95841d04480340303065601c0941c0c543e81728a02111240c42d00d148405000901800a111640d030b0015079010b04200d0880c2c0061841001000c041d003000b0069903110300550b800c0d0041c002c0c00015000180013004141c2c018403da2600f40f00b00e00c5c0c0c5070b1a8268022001d86402d202001150003030b8404000100070840010348580c0c0505540b4205a4130303011490785141d40302c041550740313801c03a00308001c0c4401c040c3c1203442080c010b0103000440d005681020054a40007006586810807254018001e2000c00d6034641c1016546803580000306221166684041c80d0800488020002140c9000c1c041c015261040003c1c013244248001807005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 397414658 1250 397413408 397413413
    0xc180909050601050d020303160b10051e0904020112020301090906050c03060a0e15031b012303070309020604030209040b150d020f040e1e0a031403071b17070c05040e0109 75
    0x110ba4043c0182072081c035040b000c41c811541c041048408280211442c2d8000491030318000100e09400e950684200a8131b22000c145410308a510040e5038028010707081b03800740c1c1c0bc1c052002d64040070304186d04210041b0590718a848003400118000c06011500140d2030300e075410a40d048a00c041c16115002400b081440403c0d43c59800e000b06540381d103002380d065a129070510140d110900180180c02d4050a101c07a820710703a09080c1a005c880007030320394900d90400c8180295001124400207820003d0600100d1202846a4443d42c0540c0c8040c280030b1a158403500042c0c085003003154119010b0082c0c000f00300c1240135144c5800c041000c1900c4034894801540c0c006045c844c111240d1600030307643d490703250f0710190b8100709181c1c62000840e86100c10901030702d0b1040d100d961043c41038001c5001001845241d80450048034802d45c0142d0701e82006165245030506043c1d000e81d41520541007412040c120700702d02d000188006403240003401042d07450281800140c41032110032420592400b05600302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 397415908 1250 397414658 397414663
    0x318060c21040f0e1e010501091224050411150906070807080307020a030323010e090f010204060e0a0b04060c14031e040e1302060409020f0d0c18090905 67
    0x14004809111841d1040036460a060300850344240300654154800160030b0008050181c000c1c142103205000c4000d2080c009010202c085c0720f0305001922402c0100036071101c81e91014a020b100f00081110701c44e965450b242070410300504e030500c80c2d07690700c00d21007005044d056401c08400242c5200d0341c000c41c820940e100314007030294581e0048000040300810851000120b50b18103600038805906c0b03080c5000c0080d500d4070449404c90129241164400e2403c448108012108200600d0b581c016801c0900300840540040c0412442d84203008003040b400000780050f00c06401590f48000d048110901044240c0c001c65000b406ca540d420441070000b10340c80b03c40c5000494220300b4099000007102c107560700d1031240d420310219080bc120120112003c4c1c2d80700601c01c481811064003816150188144240c05c48100025444102004104002c4126801800a00100d2450700b41448640c0101030706540d1650130b000d0014800d00303400b1032117034040f0903e44040d2500d040200700c01d10960f950940d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 397417158 1250 397415908 397415923
    0x2160510110d0201060e090105010b0d020901050c0f1609050c030606091824060a02061504202203030f2a06050105030c10080f07110607020318060c 65
    0x9029220352100419064060100074180c0014203003280d00c4410a204000d00074000c900505182c20012008104030b448140217a9050300c007900c2030704d0710b040420b0807420001d50003164035a050080c1070241c0e40d00080d0500c411492002c00d100682031210401d00380294200440e0003444a41e85040c3c140003140302048140d951101c002c0c3c62460307440a040c0000341c0c02e140640000024441c0010806c01c94191404449a980b0642c1030780c0742c2000c8451041000c50b00500281500603445600000e0040000d01c000c54602c460252000680030b4a00414681380c02254010000070100017403a02500b00c02d200204503201e00b0300c201c00c04400d04595008240c0303091094081e0070841040301018a200e10303243d40c00d0b1200c000840302100350b00c007481d021001d00000d1043c03c2c8280107103415401c2500706524002c00042c00c035a1144515654012075602500002c7d000e0010010320301b0a000011500b002802d01500b12a0015a2070301c08105600d140056a500e04901404040c000704080010010b02c14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 397418408 1250 397417158 397417169
    0x10c140a091503020c12040303021204050607020915120303160306050303030c0703021507030f0c050f07060f02071a01030c051008010303110a0804060c052a09071403040308060906010216 82
    0x80881e880c0b0008a002e405000e1941e07131140104a201c0220340d02001c02401240e12135000e0300d040c9075a00148010500440c070400342c000300d0402c100301c01443c21075021980003205e1860b1508141d035440100304135881884845200e54000020f0100341c011000041d202c0c5403091600b801307100e090401203501d9020280191440e49408560b031402c0500920020340780905688140e1803a1906940050240010203c1a05031500c0d00d0f0040c0e002501c03c204840d020b210f2800103520300350040c0e031000c00401c240440803e2881e4240a144001081803200f81902e082c484c01d0005154194204100500e200380c0c030407481440321421240200343c0003660706045a0701800d040b080882e0352000d041c01c140c6c1100005200e5140080d01040c0690003031b000c42c20103806801151207041c00745125403d8250400000c000107a28090701886500d4102c0c00c59500007600e01d4454841081d110004c0400d0700191822004110300c0c00800801d401c0c40d2170080d5201c04244000c0501c0f85800b244265905070710300a6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 397419658 1250 397418408 397418429
    0x803162109060f020109050111030f07080f1504020f03040803090d0305010e0f06030a020307031203111c05060d150207110103090c170f1b090903071110090503030309010c140a09 78
    0x1030440701c500070b42c8506d404a40140087c000c0081c0c0381a107034a15030003141e250040c240f490000c03482c20742c803a10059102d6032044440714003a85a50303040004070740070480002c3e400344d0200101040f801240024500480c854265241c0740e0034090440e0381070084030402035041526000041014107594640c10b90801c1d080c01508a09413191008207003010070b40c141c0a90148508a000802c01c0040c0c0744607030181c072665404100f16034500b41e220403584540829a425801c00d00c09420031131440b41c3c043da41243d402020f5050f52200c0d503a0341c800d03403910207114108241d408948c1c0400d02002c0b660444010009107030400c00e40580755a420181412400381c6402c407006a42c050010131000c00c080502c6005540403107592402400c0c0044032090f8100e109400f419081000c203104050003c10303035010304d80c0003000d10303410442a4140b102c40c0759080c1c1c80703900704604041d0005441d18140015401920144004074a000b040c030009419855200e4014031700c180c080010054480d40640354805685038101c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 397420908 1250 397419658 397419677
    0xf0403030e062a0c030d02060604020c0118080a080a021204110a0504111e071a1306061203021e0c040b180f0114031507030203060a080316210906 64
    0xc07a88a000303258202610000010020840a9140c039503403011031184004c5440d41c103001c10500d52540018198680560f2244001c980390349040c0e000707488240c00500000035000084484001c180c0310469080d610028000340f0000302d5075219000c1e036030010f4208402d6152483c0c100601580940042c00900311a20006041040343c0d100400240101001030040c000c12200f035208054070f41c4000b2512070f40c50f500a45199900191000b5a0f80c40d41e0030600003e00c8526545202c51103060042c40f8001911007503036008000b4071144071b000060315a80032070020340d60042c03034003914000c0e010480c8060384a0712100044a0500040c260480010646000c11a000c09402160800c4800d02c59200c5400303d00080181401079140c1c0c0328125214803a00300c5804d070510060584695295032801f00c0d20114100203002c2d103002e03400a541080000c0c01050085940b5581c26066410211144c56507081c080d9405044c000d402c42e030910480040f000100c0000348515016020748421703c0384000340400d508 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 397422158 1250 397420908 397420937
    0x801020306010c1401140c0912010e190606050901170607020109080405010c080417010903080106050903191103010501090b010e040608030301060f05120901050a0c0507033609020904110f040303 85
    0x10000300d001c60042c020a1421f0401101c2c10f1001d41040c02340c2030043d42a41c1d614100c5500502400501405000107001003420008111109031901c00040e500c1d103444040c0001d050b00c03a080282c1c024600020207004800f102e000e60781c02c005015105004584c104480d510200380e0303140854007106e109007001911441d09141c40f02650145a001e450310004030454280750b01010b41181c08c681c1e20075a40c00e0010f80e294841174031540071b0001c00b1505507100100641040d1a580da0954400e8003643d030048105a076140002c0c2941d07400d80050000a07140c000004465810418501d40d0710b2080301c0500c4405e00b003981156586c0070512400040141e80174070055003034040c40455201d00414903414895180042980740030340740a0f20111146407820943c15803881c4500103845041d80e0560b17031910080c0066605d142000c0e10b480c2080503040503101c0714201452003800c0b14009005d069800343c0c40f04645070811041398202018101d032000c0400c907000448003008110380c1500d0741400d1420001d460b02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 397423408 1250 397422158 397422161
    0xf080604021e03100305060106020d050306060723010b0301050c04030506390c0d0c08070f03020c0d050606130204030c121509060209040608120418090c030b010f0801020306010c1401 80
    0x10a0b14407610700c000070a01000c01c440d00e12081c207030390080040314450799a491080742e07130751480d03081000040c1c1c0504c0881d03202c3c50440014039002c0d0060703140803015204508020f080003205007a600450303540d18061041800c00380a4150b020700c3c01008541414030750b440f659112080203114030600c414200c1c0304500c16510401c100845a50024180b6080307092802411a0741d0100010250505c102e09480d02c62520610481d25500e41c88040b51742802c078540d035034403090001444114254000d0514001e082c1d00c64541441d1114056001451542455000c1c051800361000c0710700308541c01044280701191100e58010111740d015000044010524140f02c110740500c40300d1050020308020341142440031640141008503012034040003120f560b10030455403034003140e80590700d810042c40100325025200410f070502842100c00440c0c03451481c1c1c2d41500c02c0080350070403140c02c14503900601c90b03250045c20301009440c20368000c6140d42400e20029029116481c1c0080616030504022a07806900703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 397424658 1250 397423408 397423447
    0x60702030a080703120b0a14010e0102011e0204050f030303130b1e01170f0c011b080c070b030103170a020703080a2304140103150905090a080304080304030305070f08060402 76
    0x101d10700350f8aa08035403400900c038040050b8201d00381c2d401c0454802807441d100c0902421540e0381c01c815020400d4242c010b48422442200040c155503a60002c00400c000d000c2517101865841c40c0c005031303214105010885100000408140a0352080c010400f451980c03042c094000350308052042001d03a20788590b980c404208034240e1010198510001800c0b1300e1400043da0704446100607107041d8400e9204556644c1c078426400c40c00a0405007030040c031412507200e12009075009041003072506540ba03041c6450200c49a100c02c801c1000003004009204450344039500c40c281350a5090701c1c12000d1035000b950342c1c0030f40c08007070403400d00000c00c2818607010350000030050f060113240c400c445010a41904141d000f0b44145c541c07042a030210b0480a41c840e205000d038299101c80c082c41c3c414100794090b40203040040c1548031601c100c54120012806000156114501c14040340b507991a0914004043c2c2c0d002503e00d00c02e00619210300800d9540000f42c066020109a500580700c851401080d0100c088 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 397425908 1250 397424658 397424663
    0x140a09090f0f050d0807050328020408010204030803010302010f180501030b060d0510060801050a0608150d02280f05030303040609061508210903030f0a0504150309052a060702030a 79
    0x2450030a02c0c08001002c10300010744030300c944400c00b40390f55600043d0703545d10080741c5884460304e910f907000c902200900103440d48480107500048c28a61a0344206003240d0013030b04295003000010004000715a445941100000054980f05401300880c0807000a010400d000f11418184c60310304004085d02c8820507501046540c1600341f005003080681e2620ba20610700800c00040c03200000400d003030400c1d640320022a521a44c0d03015540e42c4200c14400c0502c0040004d50b40100c006086201581e600040c0c180c0d48002000c0c07001150040d142c600310741e104d0303503880b40c031280d850b1110812a560f00842900d90203a00308901148c9104e80386011802400340d500b091081c24200034010a51000004210300005288413054640f0312000341d00c800507024100c0303040e0381a84104003880801064101415079103809083c118200347d00e40c0c202071400c020301c0e041c0310300107540c828558091110400541c0441030400d5440c060111384414040d10b5120644686400345a0000e40c0c20210340707041040700401034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 397427158 1250 397425908 397425923
    0x106120b22060219020c0a0317040902070308100f06050d091b08010603111903020114280f18121406010803130f060801090c031e020a09140a09090f 65
    0x162a490008000c0d0844841400103404c001401c50075940001403150f5402d000625591125180d542d0b1094004516610f0004005003030100003030600f082d0001e803011034403940700c01000389401c111307428240d01603900205080a0042c410401160010115070420401101c04141c0c5807150130b000c3c50b810400c00e0780350307224240400002130014046d80854240c034403c0010b120144244410010354498600a1071210300c40c40e0360420040d070090b5078101c1c0d0303401200c0f012030509144d0300c00c424034010100390742c02c144034002800070310b5150b2185204200a140d414000c20700328100b004100850402e00503015030000c0d00e6a00300034000310a01c01c0c08241e80040072241550784440380c0e10f859030865090b1583e151124503010070740f81c440300359074804e031a041d07510004141c0c0381c4070a000207002d20001900525607200488103003210b80064684c44642c2588000d40d84144414008041e0152940440344640e8070410b2640d2a43d20080080d0490b407a2503000303d1031401505019050022584e401440c01d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 397428408 1250 397427158 397427221
    0x30f1203160c020a0332070e060102100903030504021302070309060e03010b0301050a09060501050a030b0c090d0f12110111030c07170a030b040605060f031303021c020616020106120b 80
    0x10011005040e051511280410b0046280e021120145003240388051b044d0480c2c0f801707210441c00c0940c0203502060510481c0c01c43d8420404000840d40541c20550000e501c035010041582031080413258203211141085240004c1030b1002041c42e10f06001d82020000000c0180040e40d41c250800d50700c05000030005c0190342400c09182c0b00034a418441100e40c1c90a0000000d0075203049000b0804072504088030491036a0f50b00812480c9510900c115680b00c81c140024201203001e100105d007101c0d1081c50341d020041980c00002d0010500d0740f03d00d10709a070401507407502c22030302102902e8200a5901407240c45e0300305072500c800326500d40d017105080e140c00400d80c184e07c1030340b5400c01c042c035420545080203020b86800038032400b4454040e02603895481080468400000c034403410f4002c03402172054070403240c48000d040d24141c2c21017400c1401640840305102054038400003001008103103000800c070191030490000300c19405400b0203004800007000058080360b1300c2018020343c40d05449000f484 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 397429658 1250 397428408 397428413
    0x204091b08031e0f0307050d021204050c03011401150c0206071a0a0608010b060306060c12031609080a05060f041406180607030501290403150209030f1203160c020a03 73
    0xda40000f9404001c50076450000c001101c801000c6561050a0076401d629664a8803c103070782550040d0450901a542045000b1705004000c0260b070040d0b100c4d001a28030368074007404041c00e41d8120745070100e0500c440e80041001c102d5144080343e481041e4240780c40c4a40d0700d0b000041d0540210507014042008a181d500721045158240d21710410f11100c007084001e4036101007501301c62a12050b07507080502000450290f16003203004e40700c0d1005a80444000c80025208030388039070030a0326607400d403503441c41e0505d28444d00507440c00301400d031b00c074001d0400901d10749030a40d441d00050001c030301051011010809105002c58408500b844010442c2e04c130381002c0c0d07800940007100c54140b0720301c1e000b41000314021500c2030064504030741c000c001e60490710b4510b07078910071500d04817004d20070181350801001002a072500d0810140c82c0c007030307200140c898030790710185030170441c2c0440d80008075007110720380e0700080031a81c0689401c8000d0300d4000c011325220303800039590501402e4000e54441c0020200004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 397430908 1250 397429658 397429663
    0x60606110d03020c060f0603100c080601090b16030f051201030b040b15010e010e0613030b01030c0e090a061508060f09100207210e0d0602030906061005070204091b08 73
    0x15250801800c8030301c00c004070001101213000750041d080164100b14042080b000034141d0b0071f60440b000030181d4903125840c4041c4421154000b2280f000b00c1d120030100100c0f036070808180401425480200c915100c5805041281e00503044402020301c140e0003201c258083c4500140c0d09010540d0765113442c5540c590500f0546107100304d400312100c0c5c51007400110381f02030bc00d180c51803c50040e1900c44503a03040341c00640e10148683d1039240c1040c0180100c0b07501c008072901480040d0301400c141d070100d5041d41008101390000360000010582074005000340c004000901c5800300d50062800200800c1e5030f021720b07000303c0303041d845511244901014002c200c0380b1603031039600030292102110024030381d82100f102030b4000c3d14000341c04070350700000c86625460b24002000000070380703280c4880c0d914818000140110004541600c04950100030440000010045150880b8007210210441203540070010102d10400780001d000d207454170700860400189610b103001040e180c40d5805211900e500c00d16a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 397432158 1250 397430908 397430927
    0x20d060b0f010915110f16170a02010206150604050607140d030b01020d110c0913050114010e010936060605270c07020409061e140a18060606 62
    0x3407141418120712aa10341c0210100401c440700c55a0a5440c00c0c0143d00c280c40700c4c02c4401818040d8040c485403624007101c203024883d4100c2620620000c80c0303092980b0f060503440104900e20301c1d64410409080581e0300000c0c0e2507072021442c5511800101560041036003401203510950308014041140c0c000c000c80c54050040322514542102c05841e403054040f0103640340c000000b80035820507201d080e6080e2140104800d40c5540b14222011880c500c0089118000304480d004001ea403002c1c924010440b080c090100845c03104002e804603541003c0e11511801d10601c6046042962409440450b2418550120195030805c581c1c014a450041d01400590403a4404440407864440007052520380440e00170751144c01d000c160f00036200001e48280b803202d00a0000021050306000381001a6900d008030041c01e40f103000c0110307002203001e1010480c4411620007103140c0b4100b101001c6916008480c21781e0160703050780d010604440c0411080400e1600c0d402c064003442c28154089581500005c0d400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 397433408 1250 397432158 397432181
    0x30827060d24270212090c19060519180b090a0f030506040605040311120a0305010501110d0302090117090303041101051908100b0d0f05060d0804050907030207020d06 73
    0xb460003407503208100716055850301402c801505007a40c0455401c0700c808080000480050f4014a0041c4c001803801303881d1021140310100343e203d1018105036041030410182c502d10051850202e00b400e11b10b002d4094012000d0808000c40348540c1010301e14410302c01c05240a4540c82c02ca40080e4840102d140260f01082105026180c41d4400046104850841c0802c503a001005003c85449a68503540035081c003a2040d803c106c0f00754940c04501c042842082c0c02039000c25549130351a11801e0020741640d005901c16418030800e980c00140f02e40000c03c4ac0d450b501c00e940381c010b0351103a04000580d0b007040845000c03c5107418201c20401100360010066003d6400341440d008039025890044485101e0441081680101c0b0101889124020511181c2200c00310bc0e980c140143c4422402d07580790030001200940c5070301c424200c955900796200d02600300708180c43c1072042e4066522500e40e030384280d114841c052841b038000641d06d1071081d419228460b6005000b2800001ea40c140388000d807c070528803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 397434658 1250 397433408 397433441
    0x81e04030b010e100b1909080a030c110f030d0e030d03050601020c01030f110f040f080a08340b070801080705010917031b1c0816120902060a0207170304030827060d 72
    0x80b601500c0027031a0012aa45a500c00031f0400e090303903a03010f8900e814555603410038500000014140e4080c801e9036a41c4031903039078215039101c1c0207041600d0515580310450a1600d84004e00c81c150b40d020070082c5500f442801d0104078044071020000050480041030b4519000c0803890b4808200182d00500072908117802c88900680c41f0b2014a44070a00303201d0080c00000100981d030a4082c00d2880482c0b518080b0841000940c00c0d16400111340d0a069001c03980c202c0230004010b00d403600b000800380505068002819030b50f0614001070281030b15400380b81c1e0310070207158400549000c1001210411480203503902414a09404019500c072103409480d01c1d0841c003078242d20500c9100b02c000c02c0c07084034a100310141854020700180e9900380c0c6a5030b100112610b4100010160b201c2900402d00604140d00400700301c0d1030043c242c500c807131b1b8002070004d40b500f0420007000861020304c20348004a21286043d01c44e51150060359140303940303a8813481c2e0071100210b10b9400540e03d030b50060340c43d03a010302403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 397435908 1250 397434658 397434677
    0xe07150c0b1b090d050f0106060908011407021f0603050a050a050607050309120901030f150501030c0206040804090b01210f0e0a1a0606090904081e04030b010e100b19 73
    0xd40099540b24400b900841c15018492400c044c60416003101000d03020b20166880807146011340390a598443d0420008074100c40b034100150402445070803400080e0070b005003c141071440d030094940180c601c150140c900c0300c1c565003440031500d81c0101d00440d80402103600142440c0b81c0152548402d83c1c096805008403c00209094001d05c1141d2081c0742c0c2c0c40c003814800c41e040d42407a00582089002134105a51000156007175203042c411088401c102083c1c1c85841c0e460040010300b80c480e582003502c11504000133004c0060b441342c003510140e8511030300c04245510400012030740c121500d050001581410b2070a010014403d510440c81d81580c211b00b40402112089403581e01c070001c2c940205002e488407800c0241600030400720342c110b00001d00c1149084441c200041a980e41a2801e86060000040d9601030018124240001c0030925940c0c90806156843e8000d80140500c1440f22820304100018402c0c8105242350015100c0b240702d2a80302d0402001c17201000d0031040409011a11800c2c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 397437158 1250 397435908 397435921
    0x4031b080324010c112101020c2d0715140315090603070e0a05040303091e02030c090105030d080a060b07050601140a0b07140102070807050a0b010608160e1302030106170f0403080105040e07150c0b 86
    0x242b411141340c00390802801c000d490001300132402e0700d030082848200103000c0440215801d20500550007184010407000ea4a01285c0421419003800f420f030034400c1d03100040810400748403220707055119440b03000000b0349a4490034142c2c00f4001d01c81c401000c041c212543c211280020100e1030940754029000c584d4003480c240d0a000c9115800e0058a9041d800b4114036280544a80c6803c5c0d03014580350341c04280c0c0c036500c04400c442174009100854094101d400148020011450146c1c040e03441241e1002e081d80c5403214010f46440b8010b400303405032210b040000e0b4010801d404948801c0c0d0b01008040e80c0e910720741001030700c41900030f0003100e5105900000003000e510585250340100106180746c0120601400165010f07480d20f00740580250301c4454401001c14144017075402400300d03455021090200e1320200c1c1d100c4000401c0340c001500e8800c20300000c40d621286150660700152000960b030b0001b21401890315055902200120416441201c1d003946d002c0103c1c450240b242800d5905602c07401e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 397438408 1250 397437158 397437223
    0x5060d02010e0613031401020a0809010911090c04050a0b0c0606010f080a09050717010e0d0201021623010606020d02100603050604031b080324010c112101020c 70
    0x214041d0000b002c1d841c1e60032a51a00301d00610a000c142c00803000301642c1ea56441081e654210502d10150f503000c500c1d42a89a00001203d40c003100c500020031680c00e0a82d43c4450700850304c81003a004542c6000000c1d1204170300000c5078094a0020410030446550f0b040120041d4803407004103804e4043c0101081c419402108196200d2900392030703035036040e5101d4411000078070000c041a10b042c4900c42000942e03440786c05070594096148800820800c000341485071520504c00c0c03840d81160b204004460001c0880b42c202003016070320840b061658001e003550005072100c8801480741c1c139480e100e0b000810307a40000b540405442c3d141c0a641185005c09410303411243c00e44405002a0400c0c0d00285c00244074203220070101c90001e040c3c25400c1100d0300e500985810449840103894a0301070702c0120000c0c610101501e107203091800b990020196600e2220442605584500907400150400021000e180701c89044c0b4150307200864641405c40d58541e91484401e049520b105801d0f10010b401e80041c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 397439658 1250 397438408 397438429
    0xc05030f01090c02070513090b010b0705150709091e0605150301360c0801050603070e040b060c010908070b010b0301050a0e04080415050c1612021509040507090305010506 75
    0x540303030040c0090b8a00b48289020740f0007000d18504500075082d012881da0ba0301828500860701034000000e01c4a110300d0a10180141a0400c19050005005500003c0c100003904184482103030301041040d1240502035800d03921640001880f9400c2c068412405100312003542c034841c8501c0000c0c449695294240b081d001d648044e40304d807400c070401c014080c00c4080000e88040c0c47c44030400c8001c81420358030411082d8001003440000c5519003883d00841948601c000e40542004c0b12418903504252202601070074250906500840d04d030140758070550f40711410b81b608010f01f500203002c81111032606000d00e52104004480c440301d900000b0810300d00400517203040e62009041e41320b81c01d08160000c101c840d001402164a02000c0102140c0f0074008100401920100d0721101c0c2c0744e80383d02d10114100842c40e0210a201d42c15003108115100c0c81402d2802d026806651031520018403605c240228441d1074450303034019041c2424004c0e41c50344540302d1800c81e40a640200480c3c1c9030501008600c0c0c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 397440908 1250 397439658 397439671
    0x92607150501230d02091006021b010c0b04020109052809020703020c060315030109030806040f051501050c030403080a09170a0b040213150b030a06050102060108061f0906090903030c0503 82
    0x101206681400d080003000009808000d103180422102d545c009601c2940c01c9030792298020701003404002164040200f050b000708003486034000310110100081c00355051280280c641c0b40340d00302003010f590242500f031010340310142807510080c100241341102d10300c1400c040c135010b510005c000544140e152003601c0f140c980c583d000d480a1203484081200d1600701400540801c00808207a041c01e035030904c40c1e030a41c144640c40343c4140346031050800086403c0c141d407020f0003030300b400d0030007041405050b03031100d05100c242095502c502c2c18458440ca54011600010081100001d80780642500000740c4022075014072032004a910250070b059031607080310034009082c1d030946804907005262160f5880d41c244021100041c01244c2c01c40003c4001e00142d11607402c0c510000144048545036015182c003070042800200000d51402d80000e9980701c008091300d240383c001002041002c24403030200801060b03551014050281c90b00725041c000c20400104034042483c1c8110399404a019005031f038032551 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 397442158 1250 397440908 397440929
    0xf16060b0d060510120215092e03061d071d030a0605100807060504120201050705010f05060906030703050705040b0f09010b0405040c09050303030721060f1503090f0303092607150501 80
    0x340742587c03188180c00000320190f000d1000d841101e540c0382c42031006440c03100e9131400b4628061030807002904580c03441d040640c42000c0c200c4045000e812010a440d000a850b25104603040f0b4680781403481c1d40c1014142c2503040c000d405000040c030451303410180c040d00d2182402042159240607039580c89500d4400c500204d5000c2c841040344a50004220004a006041c002e24011941c1d035624219003051200052099803582801906d042081d0401d138850300c181c0003005098115100c041d42c4603030314031485229648a01d4140242c0c0c0f5014071001030070201804200065855014030300d03ca8006014050060740b808031144c22a0b4400d13400d1004440c8090091860b548038880c040301c0510b4a800e811b01c1e0562040e01c0d6002604062080d600101580401010504d08012400e00c810b810300c201c0c241090b04045840e00411034070480100140d81c50300f0001200703a6140f4208035140b190112161003600e0301307000c0c02d0b40000e564000b41540352182c6054174a8011000c442021560b0038064042002d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 397443408 1250 397442158 397442179
    0xc0303030b0a03060221010603020901020a350307080c03150105070201020a120c170c1e0f070905040312050708060d080903010204030f03080c0f16060b0d0605101202 73
    0x1a010754410035041c5005000401030680341e4035000280c0c0e1200d02d10414001801d541a4194800904018050001403409500e003c22080000750f940b100044040c2c20310b4130801c0b0400313403144868030300c10802400c04500003a09560209000083e00110303100804190700e4400281141030031303011030703124000c0c1d0043c221102941c40011100e0b5040460101d0542c0f040c0d6400b000494004040226000c0300e5a0b201c1820300040d1501440b140c0b82070742c42004026060190307140b8000301240000030240c1068824151210481c070845c03070050600c00c0701c0c845004218002c10601155041144554020749807080315462342014041202c000301d0300e9000054081012030042d1400526101da040d00030603501d0b00306000c0e04006422680282c1c0308403400180303108440704043e00301160943c8034581c16165410b10510300702d001a20700c195005584200c2c0010310190410045602a0040c8207005c1c0c4030a12000030f601e00900180401d6480003a8400d5030312002410069000c40309040641c09014100d04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 397444658 1250 397443408 397443413
    0x90504121b0308090a060e06011503050103080318070e011e21200a080d02060f0c0301050f1503040b1b070314070c080a05071a160f06110f030402090a02070c03 70
    0xa80c1c0207081301800d4058000b5601c0400c205000700250b0f1a0100080d00081d454003001180c03500d02140d00d4010326040070b00420120702d80c28141d9620020714040300803031610b02401d6a00300901d60704909100e28914001081c940800500954246000c0141c6540103440c0c0012642c00258403400d1428401951303006800507800442c000003e210b04040e1640c41c640c1c0800040c0818619003008150b81e00421818032219410401d00750000940c92024800c0c0c1400480c484a80c0700500030036000b0b12002185056540b591140040450b00c0300b40c00640780c0c2071074602800180c2003528078112004011100280c524500004c4480855064807075000701039410751040c115070010710301071b40da81620030000641c0e010240000c0c00300d01c0c45100545409130801c0200700205c0140000b09542e0081400708441c03580c0d140c1c03d1807501941001240c280342030940341a5000d0201950601c20f450b07008280c0380301c81c07400d000182d4001c0d442103801c940182d550a08050407402100c101034841c01003207104002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 397445908 1250 397444658 397444667
    0x12110409060b0d050a05190b04240501060e1207060905090c040902072a0e040b15190501110a020105091201090b070926070b0d090c090504121b03 64
    0x5209225040204856060b240020107180103400280c2e503981017858a070040110921039944594024011502800503176160403c030410010801072030080200c0b0300c800c007140b40540d400c22603262440e007480150b0310760b6402020f603e0a07040042c000c600010941803108800b14000055414558035400030914041c100203032040058406800c1c070000b003001041a84d2a80014500c050042280c0442d2320702c85d0104451541c4880c0d81000e14036501002448a580414a40d54106411141c20b00140d25500c0514130001e001000303960b0700440007041c18896181804040080305e401b42c0355210500e201320007c0d5241c44001030000e0002c0c901b0090030606191041000c249110040d00010b4004119030f03805084082c241d80b5880800c40358a000c000242d141000d500000500e4040f60303052003401d00607140e5508075802144e0700b07040301180c00403002c03400754040c055080d0803044d541d0103180d45500f07003002004156015a0b078030388906605407400307008070b4418811640c42824800001410b440448 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 397447158 1250 397445908 397445921
    0xf020c1009080f01230906190b1f030e1204090c09090221060414061311190908120f03070504051e01020d0c0816080f04150207121104 59
    0x10601c00ca1000c0840d1900040066264a1201000000308820b0403c070340d80b0b010800c01401c0701142440030030000c0e0004041015038101d030f50b80785125071a48400c500000500814040c0e1070300500c038401266000340402000011032503003603d0400c9888030309800380d03454402c020040110100c0401c002c00061641e83c0c45502d5104140c038003404582d8403070409809903032001e40c510030f05800401850082c02500200d407030301702500311030403c0310104a213145540d03000010010f91180c104069101402d070060342002c0041c0c040000150380d50344505452f0300310805011140e90014a030410080f8500200003801510003402021560403d900c49035074044a510041c110f104021040c070001986845038038182d1108a040c0d072030140901e034003200082ca03003890300d05120b040122556118000c40c0c410401c5480341005128141601d200702d0800c41504d12400c204186000d000050002c0d0300e40990401e00d800041c1e9600355418103a51311980f01c00500622805001e20a01c014100624074142c0d2014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 397448408 1250 397447158 397447189
    0x9150c0a1404080609101b1103040b0406120b09060303030c131a0c0d0905063f09010e16090b1522120b07050c01090605250f020c 57
    0x4a010381d80704040601c54100d03074001040f5034050414401d01340020b1102443c05004900d04200c04100c000145048003017980141e0309100002d581c1002e8207c0130b00488014011720704070035030749660300c4030010200d0040340440c09101e03241000c8411945001144076020300401801903085449180180400303030711140621005c2076240c0f00004d500c5c214185822611541c51980d80d0700c0760745440d03030182843d403c088030500304070650105100ca60307120b2064600c00c00441004402c04151041d0521107401d45101003e410f958039850714044c1d40c41c400d01c2911403403aa01c003d00010300611010742c0e9402004a80c1441401003034005c4c0300341d03226540080600301d4010700c0941e0041520f114240340d40c1c05441003110102d10f160005e00d41350502c0c64000c0c024041d02c441c8444101c03098960012106c005053381040020010b0711000c040e2094024112090f0050310030085030410480710050285862070b0005012140c800040360340340100d013064900d150725006405003440b8101084049140c42480d07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 397449658 1250 397448408 397448417
    0x3080a02030708040308100f06080115080610050f220f361b05030a060503030f0706090804271118120717070806091c080408090616020909150c0a 64
    0x2485141c1d0790a10005084942b00d420055040a0102e0249811540c61a00b40100701c0c06201c0d058072810a406074405140c60301544403544900c8007815071040100824084000740001c421684104140c28200ca455041041d9100da13035103901c0801c1d07e400f24820901c059032441c00540d129200c030140310340e0300350302000241d03c800c0702000c0042d442e01d41182e000001e0001c0700b007150b900300a20a40001e0007045009504041d00b00501d01c00c1d6200301d050050401c1d40b034624000403c0070400a0301c010303010040290180f181038090039111844020060b08c191804c0c00300211204d80000102d46400051320001e00f0400510002c1c403995030f41001c0c1030030321482001000074030b108003c808c595850002d080038001142c98015150315100c4050010001d07500300c0129000c0c800066800c0d502e64030200c1c14400b5195a0b41d050070340c0309016614219402032000550920258482040b00c0712051085134814015250214100d03600c01700d250b000e184030030281e40403640300038298018003c450040d00d030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 397450908 1250 397449658 397449691
    0x90c03072706030b0f18010605061e16050c01080a06030221030f2a03030613050604180f0203120c070512010908070f0b06041103070e0315070c03080a02030708040308 73
    0x50780c0001410446a900c5c14045a4040c0240380240281c410661001c000007448964206400a5440e02c82c0c80a2220303424181d0b0104518400e00b44180d4414400f1250100b4038008a41041502e84a040360002d000900074000034001d0b4203d44580c3c03080e40c2d005040d26544004415010415141d0400610000d2105110914007118900d0050410034000190204260031014000110715103540319850950014010088203858020040400d6485204007103042d0700c0c0e1001003030041001c45004005d8010100340c150612503904801e10b0294400d600b240c81200b9012000135440c0540c3e000b41485820100701009185408004a0300d9482440d00020f041c106036940c1d44802c0c0e000c000b003160404040945e003030034417202c070341500c4e80110103660a001c9038007400e240707801c1448004c00f00d8040c01401d0b030b158000354604019480e44648001c100b48580d050408015018030005a8100c0000d484040003452001060080c0d90103440203481d12801034580b60740640c2c11070801445404049080003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 397452158 1250 397450908 397450913
    0x2010e0d02061c0b1512100806010b0a0e090405070501051305040501171b0d0f031e030203010801060f0b0f07020d05060708040b06010e01090e0c1b06090c0307270603 73
    0x4000c00d01c0c50081e034503d40148500c4103410f010f654115203018491610551030860300411501154450381c0c0c00c060201240c2d692014001c44220300350403048031403091200200f0320b46080402444a800300c0e840d2050310741058070400440070012200144160081942044503501501c05401c01403040c4020b5000740d82c40360042001c82d03009900440510250180c1441c19000a02141c80802c5000d80c040b800d000d170180c003260451200b000b004090000d40c035103080070705100d4000d040d03e0040707980340192012041c0000401940080c003402100f54607200000400310343ca9000c0c03504039154810058100004d103e6074940303640050206076006204035807414000340d42405124800c003226100c4015500301401c0034444030702d0040400d0306011540c9030100301680c02224400c1120060b0145d581c45a452100d1644103004090f100a40c44405288003502c610380414450311075101c1e0b03011550b01030529020551744406900c607034113204c054107202201c20b4080d80064002030840f8200402c605590750b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 397453408 1250 397452158 397452169
    0x90518031603030c0206100509040627060c050406021507051606020a0206010509061c1119140a0b0d0c0504030f08090f0307060e01210c02070312051602010e0d02 71
    0xd141007141c441c0060007282059014442c580c4403103d43c0c401403155141c2002d4005110000d800380602c220442e00c0004d00304080e03034200c0b508000580703001c405150b08140b80b03024010314000c400c982090608004118451003842a2002c4800f10303401009a112180001d40702c500000e846142001001c00603141c8481d0b641070108a100c0c0b08034001a074607203036048000d007010303010381041d0320804100b02407103403503a100b001ca16180c1c1c01720020000c60302c003d86000c1240c03426030360032103402071021200c00c1900c0e060b1002c0f84086540c0e88600d020b4415903202040915000750142030890384c004d2051101c50501540700c9120900203042c8240b038552a0b0302e55603c0d04140c6002140c20f00b1000610103150304160742600d15200003038008020ba00c1c00c191019080c440e074980758604204042d4a02460400d1900b080700d0701006041080003414480c403c001e40314101804180d68400140b504181e060b4802e0044550254441441c008004c919600440c0c080d1b0280310003036031200503580c202d005a0b541 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 397454658 1250 397453408 397453417
    0x1003050313170c01050d24120303051503060f0711070b1c15051c0602040801020301060f0e010207053309101812050f031602090a051009051803 63
    0x100c8030307060310515116800124442200031884541c00802070038100d030742c00105954a5004002d408201c848008011390003496069141403604d143c00e502c00508054289030540174140240e0b4240070981d0f135403000b04111142c000c6210340660000c1c0002c1e80540c84091440d42200151406040c08504417145504d005590f800603840740c4c20003d03c50054496020b001c4225400c00c9809200d0346440c0c40900c0403110061050a0250000d0906403440101c610a002006a4400f00c219120707074803620407d001f900309020300004104400f0560751003d00070944000d04150581c000c01002e400c2c0010702c06001c403010b600d41242500303042c0c06100020000c00e0300703006004403009280c0b07448105080110181700e00840c501442810364080c12400800410f1074140c0312148080e81c407800c201c3c5801441d090807844025500e00010070000c0810391002c07c00c5c071040e0b00071502c50780700c1c0c0c9410003000111130741911202940c040b101c81c1041941155006641d220b40420002090700c500101c6950643d0300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 397455908 1250 397454658 397454677
    0x201020703140709180b041704090921050f0304032105070807090603201b0d02030d1b020303060405060105041a090406060f0c030e030a08071b0501052110030503 71
    0x5400f080c400c1c44010f03c070b07591044500d0007a5998001d500d4581034004400500058665040400010306000c070800c200d9008020340c040421806115041040c103000d5981c944100c0d4500305005540d48500c01c0302139074803a5020a011600d1500e40d40d40942e04020251544c0b8602964100e07144412501e900c18940b06e0041601c800c1040d2804402c000c04464140c1c0000c0c040c545080c1d110348240c881505044c0c1500e42d40302038242e461329504859040802e810000d00e07014482c103c4011011980070000e494000c050400621511000140f6441c10312510010600141c2c4180009841032405030040303a080f04d01810120300d401d4851f019103035046440d41d0b201070411030004098106040900c00d1030000e21192038030780044400000000d21000501c003016041160716140c5049075a018484545041d51003c035083c2c0d030f40e184c0d140c1142e030701344401c00e4402e075120710000c005000c1d40100c0445150702100d0a42401c0624a8460700e08541e40207030a510004d280740c41e0100c001042040100394072103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 397457158 1250 397455908 397455913
    0x304080d05070f0207030f0507120c170102070f060f0609181a0105010e010807050f030112020418050607140f03010e040209130317190f0c0e04020f030c07020102070314 74
    0x4035880d00d40159000585008100300488180e92035450b800701c0c030b00d000c1c2ca5105454800e0f200080c14054035055081d04494074885849031a80300b0000c0100301141110110750403100300c00961945d89080340241c10b0003030419501042c030080004c0b65940f010420320951030700081d000c1c1c0c40700700d030004560352508004100704105680105024448a00385005c1103101420380c8558180000200000c000c6c0c045a418002c9040100b440711380120f06485000034950b858a0700c030340e5101c1e211444203400300030590103185042080c00ca102d00c60f510180f0401e402c180102110b4031900800c480d00341c240e030740b0039040400c24031107803091040090040d070003403d00b10f100129070b09190040004200000d0003045100700c8007044040000d030040f488016140580c0141d0101c0d5990703411400c441e5842e007400c00c150500d80240c4040768101544029070b00080f40d03032910300c0d10248500b4030049101d140303a6155020424000190124524002408401d10620580d4046a034031364800c05d5150004401502d41d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 397458408 1250 397457158 397457167
    0x114030c0a0e120f061e061507081c0c2006010506030c0706050408030402270f04060b03191412040306020904021309020301080c040b060a08060a0510110f07030c090e1002030408 78
    0x500c00c0040851b031025844021120b0030400c0010369003035010440c800781400c001c902ca40c2402441c80a0398a4107144640d44d5610003104040f0340003e24501040c0701c0403c081c15506080001032041445246400342e004280603401d040800030141c10040901e003202c90f08000c804001952401182d0003184100c586c1c54072800c041c410464442c401400280005000c40000300c81417100070300ca19040300c002022901903890b02d060510181c6688003080e034051289540c2480080500d00d00e001c031540c003d60703540881031042c00c10f617510359811019100d4440c205210503c04201964018040100e00801c01403400820796001801e025595000c0c071700b103e42c007000400c0101003d0054274034800301100c04010394506040041e015004501c200320400540344000f038529240d44030b0b400041c0c44010b202d40f962058004004222040c15154a83c2c2402131401e0411000c10008080e81541e82c040940300001c1d091121690007050329503080320302c074070548610421000eaa84000c44c040d0b4081c84c55903545 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 397459658 1250 397458408 397458421
    0x3030d0501080c01230a12050702100506010801080a1b0914190605010507080d0e0708010b0f090402031f0f0c0306051f0921060e0c0114030c0a0e120f06 67
    0xa1900029a0f030303042c0090b08000344010480031034561420000302c040700752600c1c0d040e601118041c5c0300318090100b051401080c01a000e400040300c0440001940c010700103950b40d0801180c06030020310480400d40d00001c00007001600d10400c0c00c001807400c01c0d55403085e035600c20011013135422050722000004070f07500a01c040680b03890b021200d00e050410b402e006071464040000c00c42d1203102805820490040391b002c1032145039400003c0c00105180495030720a403620325080c002d085401e441d9110702e004200500c21410441c201510603900100a042040042c0030503444904030441d200d901266211400c41e02d0076424418010128000e80e8005941420003092289100e500d814410341268402d50b5000312a0344110401c040d1450203111455400e0003003620f0f401c1c1940d07590000c00443c100780c080301c80c40134001170024454000b641c800404000c0026104940c0c48107a070115101c41c030801001841c42e000c0d01c8014103400028086c504c001c1e41c6071610317500344035011124030001e404c20824043c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 397460908 1250 397459658 397459663
    0x52401031a0d0b1602160e040302010207140102093307020612070e0907020105131106090a0905060406060801030807300309031404080a020f030a0803010305010e120307080609090c03030d050108 85
    0xb134442c4030b00061002e4401044154000c140d0391281c01600c44c41000000c1c1018800e40584200d13039800206000c17000a04d0014a01035000f0404041c0a4070703000c0b400d02041c0d000b0094014098100300a00c190b0218400c9091410740c0c002c0d00300740e0300300b9000c00c0b40415444205d40d6840c41200d2943c0c0c0d90103107081d5542040140103024003400b046a042005200c1e2042904003480b0030a54043d2000920055800100c1c07514052807001950008480e1030006405080d60001c901c50001107504011040d1034000940c3c0e03a05081c0006001c0c0c107014480000040e0415120f0020721940c8054407501c9840700d1380f020004890080a140000d40300e40f01d81c02010703040700390208166003d0002d2800c107810941c0d081d41d079051410029101d031229441000745a281809000c501542002102e9034940c1c580c1071580c0039001c4103008902a02c0751010948801d039600054074003c04442d135490070b081d01c2d014200030b81e164018100704294000ca421100c1d29950800c010078003010b6045022401b985080701c03060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 397462158 1250 397460908 397460941
    0x3030405030a1407110d061e0b0f0103090b012c13020103142a0d020304120905040b010c14120c012f19210f052401031a0d0b 55
    0x2542c40005018250020744070b0039040f05c442d801646c0741082e8081d40d0800314044c0070050750b010f081a080140003451070120b60007404240c681602c906450f00c0da19401182200c107007485c040c040d0740300040140405030320320310311400c24848d0070b40e4861480800b00c046588000203465450b44071081001d500c04658250041c4010402c0c0d5410748010fa1905d84070109a25062405000d43d00d103c802281d0303039040015003956400280240110344070301c0e103454081413009850600c40041041c0c0c41000616161600408001310410781d00c042100400d90350711010000000c82c00074040c014130642da1014100c90f0007401c401e805450021400c6400c15151001243d0701043d803800045101002803041c91b112030884a50b41e040c00e513281d41c0015407140c211440d9465281f11113801d0710350280c050008545030401106212003a000708560f40307844202c50800c0600101c0720b42c03101405038190941c0d60103580179400000c1c402100c2c42800744494001600c03101c2100c01202c0e4010420184900303181700b42c8500703 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 397463408 1250 397462158 397462187
    0x8070e0a060e060a0203040306150314280203030c010f021e09100e031203010e0f15132f0a1b08030a090c090c1106070e010905041d03030405030a 64
    0x302100d007407510062449180341085800f030040003500481051080003214011a0420340c100520202c0403811940000e652100342c030b43c0f40e96929aa002507002181c0512201c000c0301c1d2032840e000001d0a04805c0b6050740400360383c540400d000440343e5810038054410384080c5403c0c0103903900716021141208a4030325006000000061200c0b00e00e60f15903a82c80803015406080c06007516084c80000780ca8165021070b41c500c00e20020000040c94840c0307420ba607000b010702020048040d41d81a0806140d41c070790300d0b03541e0f44c400c640710162740003008654071000d4041d046054211522022440400500d229075544e81104100000d014428035441a20f00c131020340541115142c2d00541d07118501e9500018108000e07440c0e0312300040040001c0a600b603801082d503500305201040941c403000d0140e0380615034840701e034000c0e200010403040c461030070b00512a40c141c44c0e202040d81844180720040108000c11440804103c0d4502008402040690712891156008554641d40ca18008040c00032480c0790 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 397464658 1250 397463408 397463419
    0x20c0d0f090f080303040b2503050f011205060412090f06110d090b0d151508040611210606040528060e06040605032509080c03160b07050a060c08070e 66
    0xc1c08100000b00c205e07504250000c00704100ca80701c9075200404d40f244030201c1e00c401c200b03449070410360b61b40540156208240800181700b490380e80b10f4041d21304030701a1030000c220390001c50000b40082c0c03c0c49101040b9099070326064811f141c41da001940d00005640005001c5040046003c2c0a0202003141422450443c900380620500c2c0940e0107d040c000c01542d00e640c15240e03520800484940342500d0020108015040044e616071100030301030000650b41038031000c0c00c1c800c100842c4003c5004449614451020504803154006030081d03400b030028010907801881040001400d964246148514200c0c3d2009800d504540b10303814803a010a03030740400c080c00829950010242e1f0782c0d0303044d0790440351a4200355983c0e594568400c0c2c0f441035040c4200c030441c1c2052940551056000a07184162130f00041110031360210b04040590302d5500b004500110b08916105000b03030751008000d4040c0c02c1c0f165007101c00f0204c103a640c110546581c00c0c4c0310000290b11004101c2607540c012104480c442040d6403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 397465908 1250 397464658 397464689
    0x1503011d0303011211040f020d0f0c1407031b03020d08010806190b0d0c0f0807060e090735060a0920031512060106030e06150d0303020c0d0f09 63
    0x10419107900052041d050b001074070300c4065040c04034184c204540514024002c010854024100c40025000004d00240b014603000013903604611354032689858101c9900e0701030046101d0b601c0d2015690204804408000c89a007105003d0203c103410703a041c092203074001d000f50100c0d94400401004059000c01c04e15400b020501c146c3c0781c0d103021540003808840d03030089000c00d40040484d103c40296140200046564a800507910b05248040825214403801782d0746007507515034044034044032007200907512080c0c00700030540d071034007a80c26074049402d40c0700d6203800242e9111340c04888403040d040340b5185c80300601c200401883e1241d60a00600102601001000010390002c0f0a80520100202e54107400202060039a0300b92071020420707034002420700c180242c0580506071074000038401d90f8003090418003804070034140440d040e4403405511020b102d0f003130102c90401c04810056201502855801c2188000d02c004c00d11883c442041c0c242c0780d841d80300f51034101c0201180f60325400142d600c000280c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 397467158 1250 397465908 397465961
    0x10b01091d0a1803090e01080d09180b0315070f05030915070e0409050a150608030a0c02040f020a02060601020c031c2001090302150f0411060d06050405150301 70
    0x180704600341c0070104034001c500da0751820900300404805451022100320441c142c001c250f48a580c51083d40d030001c011040590b0b9561038547c0d200d880d0603c1c0004180103840a0000400c41d1a800d041c0c0407001401003428a41e040219003018188008520078005560400c81100d4118a403800040c2182c6071003407451600140142c3c8a03a83c9100c2454109078450101c3d050500c24000741194101c001c004210003082c0d460300f00d541d800f62003012244001030800071a4401c00030310032101203650740701c00f8610b485079842084074600d42d00c0b88101d0380580d6602c210b40411100707102070004420340790000d040304e0512800181c50400c0440205100760b001440840504502180103d031815041c10324001002089061180050701030251820540c80c2500d004141031380000c0038003613040d005c440c0c1c1c44035448805100840220455001d0050300c8910440809414440020140415014000600103031680000f0301039800c141d682c14100c0c4400c00d5518664038080c40b9007121744070f4280c01a8018101a1f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 397468408 1250 397467158 397467179
    0x30b0412050f1b01090203030c1605030a020a05131404110103050a15061808030c0d1e021209040e060403091a0903070b031b12010609050f0315060315130302010b0109 73
    0x1c3d000f1491082c45001040310025040150150707802810f4036111020149141d81c3e5110b0301e018220030000e50000020141808a01102d0807070b0041d14030380c410b80c105000d104507007000c0200d82003001da460100d04e074250607a124082c003440c03007621a442c0c5a8490030004041e0b403030103400c0e520460718100762603240500702c42d5031313404440c01400d03e01d1808480382d48a251000c07190f4405030040c0030006540c14604004140c1d0542d106641e1101800045a0003408002c07204100fa1800540d010054161001d18444044c0550f107400800100b440704218401900303203801501c04601094820406008071103c520761006c46d002040380c0c0c07506003004100060b6441000c0d10410503042d0000000c905c120f07005443d1544140d007610340d013990300d50740700a0341d51f00703600d0902c00d05000a031303426008100d41c9002d801010a04500500420f91030702000360200355820068070250707240c81207038180300c8005d03018040b9911444400f02c1b400c2082009041c06030a443c848400303c0d0401c6032000d000c3c003155802 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 397469658 1250 397468408 397468417
    0x6030105060f09180102030c072d17040b0c0c0307090b06070b060301270210050309372003010e10020a2a0c09110a050708070804030b0412050f 63
    0x110b8000a044d00c81c50030504a6000d007003005000b55000008001520309407000422400d882400c1d03c02c200483c00700071030070b07207441e002c0303001c0c440c40d030020020b4041600340040d41c8a030504d502c040c500e8a40e0302c8980410f1380d44008107146954025551148042c0703424080400106003070307602800009901000500c0d503200f0380e0f0004120340080b40100b803603030318254030280c00508018807a0b4030320307500c1e4180182e5112000008034801e5110084103024284500c0c152409580c001e07005000c82040361400d10b030321406170000100da0800401100340141d43d00d44030440494014502000d112007c0301150090780c0d43c0880c0b55000381c0c14088000c020410020342248080107054005846405865080751041c24009001612800000300d11828400c0c00c80180340b810f20401c5904855542e0f1030403c0203540c8078902c401c48410f418002c0094180c003038002001c106114440c158503201081e41c0703c548a030402c0e0400e55400c2007017400c00040104c89400d5442180c8142002414081003681421143c0302e03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 397470908 1250 397469658 397469689
    0x1024030303050f0708010f05060d200c010e0a030903060902010210050a0f0e0d141c060308250c12080403050708010e10061a07061806020306030106090b0609040c020f0a080a080603010506 82
    0xb0b001c0c20050700700d0348569503c4c01c08412f031856500340148100441d80100d07040d030b4500c0d460401000e4500c100090344d081c6070b6506032500490103141d0344544009004000040c2c0c15802810f50210300795101c2d200760340c8105146500040e482d80750b000000c2c2181e030804500c07152030703016100c1100300b01c4e0422821451215071030006951070340201d1503858405034880d2816442d50030b02038040104481c82014001020b0a103e12010780c9108006103d48990072501c0586052404201407010001154249084034084d2242c40c0c82d041e035176030320140707005003550003205642d5481e03a003d1510b80b014084070b100c1a207030503418466142012844010424014480780345c000300005d00f1001c02820b07401c030790b41102c10745035043c40d213a030a41418400f81d4030444415200754a0980046407054440c8503070f41e4070010203030900d4103121008003404001c066aa510320127510600b041c04030208030402050131302901c500007103a10703016034a001400b19600500701c540b00764100801c212071920388180020300802c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 397472158 1250 397470908 397470919
    0x301030812130c0e0604180b0402040f02090603090a050c010c05070e0411030102030712061a0405090907030f030203190905030616110313210201021024030303050f0708010f05 77
    0x1160120708800200107000014200e19100d03c00103002640301c0a200d10641003950248621003040203441500600e03c074005100b04e0001c00810007500b0168001c9060041d240001441c05c0003010000d2a0f0b604200c412000643c004030002c0d0402409100348604090282014804912243d0b40d05403100340304d002f025900300c800c1000400f4060b01c1032001c0011f620180086546c0d04220340018030703841124424590740c0d800c11070009600c40607440d12401940c8610300a5007003d081008004207190081c2810030184511003020010608090600d84a1440794000b90365900d07203980d40c2441149100c0c0e0140a0103407210b0200802d85010941e994041385d11480200041b0402c40f00f5114034009200c5905d842c4408200910840c00c40c04a00095843c2c000d170600125540300340741c0403c5009004001c0c0140c00c0303800c0428580126801c501c6007411000e94080100210404210507200c00b82c0c0164006500d98080c0701d84448404075a035044140f40c5025031466040c90043c401c07107078040c8100d40c000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 397473408 1250 397472158 397472161
    0x180a05031e040905012d1d1305010203070918020405010e1c1b06020114130b0a0f11030a0b03070503121c020703090501020708010504031b031b05031305060301030812 73
    0x340742807045402070003c078101005907584482c0703500059000c002d002d2004048044032180c001c0700700d0b0b21103812555421610154001445030030160780b00c2c0504002c80913180450413000203a030a002451042e9015502c0c0082e889c03a0603808800d4041c5030720034510f164810030050040b85d91002150364000c9003500d200d0100d0404951141c0c14600883c1d0240c0750301d03003a0300d2a8040300c0345040b20908a840b035600078800642064407050fa13582e0b056545003035055440e900320f0b001500885925501440d100c2000030511403084a070001d8818016407464000400401c000048499105400e0400000e40081c1245414040070907920501c0c009180780615012a016a00b180d01d52000408084070070803e6440b05c0136490003411200712402294050301a0320004100381c4c50512801d48a20f1b010ba9503004407155141c0340f030503054000070059080007609072040102242624800604509c124000c654400c0c01058402e0480301c40d03000310340305420400040003c03413203500c20f55910141001414900703 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 397474658 1250 397473408 397473457
    0x1306050c03091003060807051f1809020403050109031706010c060b19030803010806011508040303020d020c24010b18041d0d080a1b0512190212180a0503 67
    0x5600031014031591014500f000d6802e00d5a01da005802256100c1c011200166261002c001c460364021400c0450540c800740c08580c1584221100c1d090360a0750b000c1c8141058031081914180d90044d0001c0d50141c0d1151903040400d94802100383c007107400040c4510b11400d0200c0001c2039050b6012001d8007450315400c48440319920050314400c01840c481a000701c41c1d03900c3c50410103940091094007c14001e0600001d5104681706c01031a21406030f648200b03240d6a2a42d0a80003500031036001820b030ba50071711103c0d1540e50100b103810319224001007030f400410801c0c421a107a014050b000b01c2221081401030444902c941078029101c00000c660100f0300c14000b85031002c7c0c14031110700c41c60980c892045001e50583c2c212510f90b0280e1a082024001e42c226a4a2603981c01c030402c0c81c0c00001401040010a00e00ca081c044941001d64101e2448011030030704a660141c0e0000190b0301d2131240d500c014003021490316120300f00b4840118020f0850442280c50f8243c0720b000385080e10004544c0008101c46 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 397475908 1250 397474658 397474663
    0x30908090a030507031101050c060408030702070f0b030411010315170a0501140702060f010b030106032c03181903020d05030403060c050406081f140301020927010b1306050c 76
    0x1101440a031400360708a581c1d08080e80c1e10200362005030390804104c5144240f651164080310041c0046500800c1039468680ea4104c2941c4006c0c48032045008921003c5020940d54900308000c148aa400d513031070341010704025209080890203241814030705042c1c0c581c06140890103108030785002885000d02401d82c281c4905107000001d0042c119444c156285002c89501458240140480e40c2151690750352004c8440545100780240740c000c2d8801e100410511380300380c01c1040f050252446003c07401c03c0000240030798109a00d0008042d070000300707072908800200c1e058089144403c59090750b01e1400e608420710282044d00000e4000d40b9211001814000b081044500031a408841007218048803100240780b908207025140004036950701103445500e6001045407021000741901d110356107401256514404080303030964043d5001e10059001d95502504000444070b074031030311030540d182c5191891030201c4c16003010101400034000d03060306051440410007540c1c12818569a44c2c0315000d00d162 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 397477158 1250 397475908 397475917
    0x10030b1306020729090c062a0d0801080d03050c041401051309090209150f060a021e0f0f070b07030c06140a0e1c0e101b031d0402040312030908 63
    0x41c4070100d52815880a1040300a140c40c2c1c13061080301c0703481c41351100301c0015202c081c22082c007903110500703220a40412040c1d01d5043c6601e810134140749003c480c051117603820404c200300780c2008242110300420620300140188051160b5920f42040380d460041c200755034a0041c0e0095203036940960304051604d13405002252442c0d0002c0510400300c0307581f1011039003c1c2140d0b5500728043e403044d002080102e900000380400c15040144008080c800c0170041c818980c0241c28280114030626012010b43c0ba00c80c0140e41001c0e070841d02800c003c12899801920713000105100e51019403264508000c5070301c81d032061340c0d103e90f45440d120203100e90500b01030300030302030107465a40b1811504080c00705800c06030740404800815039081d11400f00c0b12140301b40703856440943c600c005ca40080080354203072500e01d00d0303280202e81ca03090202000151112840000d800142c04401240c0440611303040c84903e4407601c0594401100d0a514150442d980d000c0e0603007541503000185500e5517000c0081052040a60303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 397478408 1250 397477158 397477163
    0x13030212180411070503030604090804180f050106080903040608040303062403050601090f0902071505131b0521010f15140d08032706011d10030b13060207 68
    0x86881d949415112000307852640411403041d850400c0c034220110a1200307441a080d045005036003140d03156428000940f80d1600c0480300740408000120741e09155032400c010205404000140000c1e48041900c00c0b0365044c3c20600034401d6400c108a101c040c0002164243d8a41e0302e41141203881d6460280d0240c00c0743c0d0010042210848100b41689841d035820890801056a0134041e54450100549448000d8040c203402c0b003100a9060040405940042203824442c1c210b4075203081c51070366880c08440d02902d100230328180011300042441400c1c0b15103404c00e41c0450a101c0c2007498800020000b40b0503100d044001004688044000305080d4800146485850424030888966201c41c02184801d80600a9060140c0780300c0c00403410010042200d2540c0035428915540303a00b1044401d44010745000c2e212004460720b410080030047c080907009002c00c00c0d22500c0710408014080301014001c0c111440d0032440c2804101042072422038540204e22000203080d00c411070b042a2001c1e100d40ca001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 397479658 1250 397478408 397478443
    0xa02030c36061305070203091c050303130b0c0315040b192405041206020702060f0d0f111306031505150406080c040b0f0f160501090605090312130302 66
    0x5026080c0240881c180b042408540e40c40884240c0a180011100190f900300d0041c0c2c0280b00b4284c041c00c196404807400101d041e003d244c9034501d0394407e85140c0c03084500080323949074141c03800204031402d03100b5500100c1c140c8580d030440c6802e4030340444045114011a01c80c0c0d4403041048803640311550041f03a00741c00401240c0b4500d80343c4000790041803c1c3e824600c180d90120312a00c2c0700c80d1240d000d41d8103844814622a8a00c40191510001703904124416a40140d041182940303110380c1c440180148407114501203000d40f80c00c14a00100c80748407032509000c0008202c5181c80c05017000d016410b5450500b030000780c0f90074403200e104010f00b941d00216000b6900000c1d00c0f0401910f03401070021078032103a5414107961703241912043e15001d01c1c4100c426210041c081120b013070380f00401030015081f581c5162402e03d440c04000c010700ca2804403040d14140d5540201c46e05025403401015400001c6500840c278104901501908240340205070b0142554800d002d281003502c24800c840034072520000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 397480908 1250 397479658 397479739
    0x20109060c1101050f0702090a2f0d09080f04120b06040903051e19090e13030c1103100f020702030106090b210a050f062208040509060a0b0c030a110a02030c 69
    0xc0d008000c00b02c1c8101c0508001281000e0032040701c612025400c3d082b42c40f5411800d001f1440c2244003d80801c08044403185d0042c0001070101e26550090401806038001455814040b0f0400c01034020740601803900490400d02c082022a41140c200d62081c0b1b02c00e4000059560036401480460081181d481a01000034100080c40c5074800040426070b03114a1011056032101210115540141c6078014007182503008908045218403030b500e52030083c00390036107070301d10041c1d1601c01c101c410301c4186242e000da0104856040d07090074032075240030f014644000c2001245850000c0c0c41c081307500d2804609200c010851702c16800d000d000f1b140c0700c0340c0d01c0000c03508044500303858140c42d0001141d602c0c1880304031210342c0562001200d050200c143e00050b10501d094105010301407031140082c00603800461074680000d001181c03900821514440b000070319110003c103100142150351644a004e0154040460800035a6000c902030140d0101200d42d02000c40c0c0c900403c0070494615650080c42000303543d0f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 397482014 1106 397480908 397480921
    0x50108041e050303042003010e1002070309051509010807020d05070f021f02030301050f0f0f09060d0c080102040509090109031d03160909020109060c1101050f070209 73
    0x1595003120712181d294a407841e40196001c8079450182501c0300300c030340c502c090f030344481001c100c0084c8036100010301d549544440c001c0540c0540e96002800c481003600440c04103004000103009403070041d0324004408031a4005411003400705c1e2410001945507840401c0004c1981105d03210203007810402c1d00d80d54a003010114040ba0810300c48078161800f0700e015455182c0e0201194020359072076041c601840b02c0700c400d01d58114090500c1c030340200195640d82061031403e2500340c91f03010507683c0d03003400036074400013018001c1c1807000c14040100c0e4240c010340050080e14401d03142964075403200c0291508031100b041c0003400040007800c4004104284425150781e4080040440d03014000c0000c50201000380d42e48181c085540e5100e4000171541c100c9401002030005040c25283d022440c0c8070b0f140c480561040080c10000005241004180d10305c040d04d5529030003034a40d40b280d25141 = true := by decide +kernel

theorem cover : BRFrame.Cov 397302158 397482014 := by
  have h0 := BRFrame.cov_init 397302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 397302158 ≤ n) (h2 : n < 397482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
