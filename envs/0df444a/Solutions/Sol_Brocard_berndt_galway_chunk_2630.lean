-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2630
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:16:26.866976+00:00
-- url     : https://prove2.me/submissions/9752ce55-24ce-4144-9aaf-83a61989ea76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 472841726 ≤ n < 473021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 472842976 1250 472841726 472841731
    0x1c0204060b041e0e040b06060708040905100e0601081801061703031f060e04050a27110409080405120a08070503030907051f230708090a0501031401121505 68
    0x1503810a840e10300302480140014504001404a0f110003142080780088081019521907044601c46015654000101302644665013005080d83c02c0001c01007040002d0342d200f40d00600524141c0140c0b152034100c222459032064038030a02040382103000504440d1520403103070b00d80b61510b00201d00c140d66128038000181201005001c541c0000c000c100000c01d488a1102140002840005640d440d00d9400b44c0069042c40301c19001c0c589a400040d403100c1d05070054005402d00208640d83e0305e15007a01c6202e40383c00c0b40300c100c810006008c2107100c40e1070325005004107250030087c084c3c13500d8900340400c0703c0c449500401411038060080b461010036100d4018141c05030080d00910399070300d055425242085400d81007513110701450040c0c480f40c5004400490a41d1056040020b451090f110100c080c04901038050140f1b02c07000503414040000e060042c04040b0401e031020058140c6400040d425110b40621488941044e00d00412003c2049003140d2031440c0520032540303003104004600e6054503004c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 472844226 1250 472842976 472842989
    0x9060f02041211031c0f021c0c03141306050c070914090616080f0907050a06031e050c0a120902041404150b060d0e030c01020c011b020118021c020406 66
    0x3000d02c50024001103290b02900e020044000d0500f01e02051244511280c0c1c100620041145201070050300a000b0090b0074803158842c60354030b0064400c400300900211410108600007451000c100b11104460800e48101095428000b156030382040822950750300550401001486940c0c0300148d00329180c0300d819144940303070103200840e217010041c2624120000c0e054a141c42c0e01d201b42c80c1c0300b83d035200fa075113608059905080010740e00d039400c10b9403400030b903500300b190700c00c02100001481c1a0541d110307203800c101045c3c0c1d80f01c3e0440355001900c202c0f0303400c9940c0d8441c1003040003111259881801c2404000340c088000161481d06900414119000c41c0126040c9580541c1400180300210384d240810361000e500030306c6044100401b1401c42d00a0040100d6076580300c048480d5282418030590b58180d510703034002c40d01c406c0e08222550103420819604095440c0840405141c1d9106004240c411076010507045007040055080c004c030141110080c05905400c01ca0745401030b5114050880103024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 472845476 1250 472844226 472844249
    0x212040906030210020604080f090d0b090f1509030a0807090b070c0501031107170d0915020706060503150412050405030d020a11010c0c030209090c0d060c0e04020f0d09060f0204 78
    0x1103106010103413141d4402070303040d580107800704400100700508032000000c80817030464580d54000b0102e03040f0205000001c5c55000300e0402c001840c02d0028200c0f504240300d43c1180c0411241c40300341d5080c0c0c80e00b600c1100aa810401a041580d4021599942c10007103034075244d85c0480d600c014200094001d0b600c1120340503201c3c6820050383d0703030501400d0008158406428500450382d56951944105c4da0115a40380c0d5010510f5088100a0b030310045140350401198611624520981c3c0700031750028000319080d500e45100071039a800e0000b00d0b0612500b240440c0407207030301d540e2102ca4200000201540400c00b00300008501a01c1c00d020706d9911500740d030014030f280c030820310f060000007812922150404c5101400440481c12869840040702d4040d9841c80040c1c941700d1905013407483c10801c490b000102c9603050070402c500d951184030b080215580e0220324601203003c0006034402e82e406403904190900c500c0d003c1012650040348070714418900024008401e000050903070700035900c00f40c000300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 472846726 1250 472845476 472845479
    0x60111060f010302240d0903020f030a0c0203010515010c0305031f0308130603020c0703020909010f1d070801093f0f030e030a0503010b030c0412200405061c030212040906 75
    0x804401c0680407820503000800194040c9824805c0e60140b2926a400203031500003410a06000344218500400e0900541c0e5036a01142c001030007844480000301d01962a080010b504880c07010b02844040005a41d0b07204006d200e0740f000c94141d04050400180541508141c4070220021025540214810480030303440343d20181800f04070a00c1e540c410802e040c01004541c000d01c0c40410700606483d41128030808584822206a0041c1801584113060600d4005039414501080710091444070000f01240c19140d2607154071401c1c2c0d00c0100c0f0003851500800b40d100c00b00e00c026a500c0e00700d082e1103a000e01d80c000340c1d07e42d0314450031903400040d404140c0d1007100b1400160b0500034035006d4184140250314140030541c0040084c40140b0510311151030200100e00000f0080d01140e00600b24103405508039561800e203504607600c50146403130540f009403a444031905090140505c5100010194100000c001c1c038180e103282c292a1048085008800c0d48029007400341c000b0700301034030180200003102d6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 472847976 1250 472846726 472846729
    0x6010303110c040501080c04020c0717010605031614150d0516170c040b0901021c03020405040b0d21050c01090c0e090303040c1e0e1f0b0403020d0605060111060f010302 74
    0x20501e000440d014909040c01400b90140c0018145001f0704190b41c01070790303040321850310f6043c04015044468103015612201c0002c0c13005401010559400710203503403c842e041c401d410318900c8148107502d1042c0c142604011240740510400f036a001c080c10019207003840c04a8603900b01e640807144070414141c0022400840340d44040c0e80101c201140c1d009003241d01b0180c51002c05800b0710322560561440005a00b641c591007801155141d4040d0f6103090b40905034400050041d40140c01668001c0b031412500c075102e450204420b0f404c10f608024003800711403400c0c0c140c52240303070440c0030300303050220810904003582401d00c01c0c401d156000c3c036800ca50380703410718a001101c0c04015002d50200c0d441401800041021681001d003202c8400c4032401100c820888802e0079402d0907805034882014402c1041a00500070414665801004030124209610303090491070034007a0303000181d00541404a840002003c982c01580c100c181410038030401e0540c01d82d4540780c40b6088031003108003c40341c030041045 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 472849226 1250 472847976 472847983
    0x9021308071202030303040605040501060527061f0f02070f0b0d060806040c090506010207121a180a083f15010f0f031b020c0a08030307050f03180601030311 69
    0x5400c050b01d4020070041c858001954a010142001d01481d554401040030480700350b1020b0003c100c0901405900c8401034005050b00e4102c0700240301e040b590100041c2c141c5010052550007000740e10700d844d0020036800081359000300c5020960154824040080385091030b1408a500501e0b142c01c00968401003124680c094402c0c03640800c0c10b56003d84140710000381e02d2070203101910507000c0009202c3d6103e0740100c1c03400010303030700c640c0e0340d01ca0315440c0ba0b052080c3e0007000603858100c516800581d8803480301d00e44045150700c007640c50b40e0300842441000640c5503001004803407000d0150607103909000b038003291054080d184040810000d100ac00c00030140440304980d2000483d040e007119142000d002820100e0035840301c8040011604110718614002e5001021081309020400c0024010200c003035991481202c0a52041c40c41000016005c00000216031141c10b490742d440d410701c4040340711860140c1014003040c40c0d889600d102c459801104000060096001e552a150440c01c103151007801c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 472850476 1250 472849226 472849229
    0x609071d1504090b24160605070f0813150b01020c040e1c030e070504022206080603070b0304050d1b12020d081e040809010e0307181d0d03020708040902130807 70
    0x2440030506101480100581700e49044004042100d50b150b40a07443e16a105546840084c20302d0720b0142030000e1305500c0b010682080980c0c0d05c400e5030503240d0036007100c46d41c2507003040101122810104600544102d40000041940c18012034000440d4074002800781c4070b400d4006081580202c409888010003504103006000c6141402c000695500341e45a803a00d0725401b4082c0a650002480c0d00030060100e194090300f03201500f43c0c0015034442d200201005c02c181c42891091041c050045100c014010440340100e51003c01040c6d2100406001e070303800006525070000d146101c405550214400702e46c00785a5845c2a8080c0600741040c1e071001c1e10b07445000e08945c40365075400892915045028005a410540049a05845141000048500141c00000309416003d903480c0026495081e14135104482030f0080c040c44a01d646205950301c0b130300d85a0580b0b98590080c0b8200092501030760061040c2401048454546600d48003441c09030b0b07216001e05600108100020840070601f44603100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 472851726 1250 472850476 472850479
    0x1f03050f040f06022520030d051801020f070305010608010c0906020c220e06060301240e06010302040f08060a0c020d0f11030c07030b04030e090609071d1504090b 71
    0x50615868a040b000c4001030300400d115030000b4114000b80304805298030500004100e06445042841c0c1807290304146044c211142c201600822224038022a4684c1c941d044e6503200c1c1d092010f80e06034420182c0c3c014020605600401e26400c104940070301c18040550b0041c1c0c008155203103000c0300389084549640507a020040c0302407081c4001a070101d40008240401c90f1550b6142d4280f48107207400c808091142900203103018980d150b0000d02090041c41f03420110000c0042c03880d190300d04e98201e04001e03031b0f014620001c4102441240d91040c51542c0003001894010308281d155200c2a03001540c0d030300a90126840102000101e43c071500400d10b003809130b4400b4014175440c045019042030140c001e8071082c45002051242c2400e17081050b20301005007801103a0300180d0340d04204803207a1040c2c1d015070005000070719511160500c0180d99008541c0a02000640d986100d01250000d48070300c0c035491050100241400950788409080d9883c60315400040c0e9920b00d021700840c101d070f2151081d00d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 472852976 1250 472851726 472851751
    0x206072105041508090c120a020a05151b01090f2a060e0d170a03020421050307060c030b04091101090614030103030f020703050307060209120102270d021f0305 70
    0x103000003c8001401d455440c4203092800c056120b1403505c60030142601086074002001d807100c00001ca10010b0b040d00014020f4406091241c0c036002800184205000700c410804d204204034244481c0c0d2010352280d40c1c002c8000054001440d98030000751840141c020386401414036245003504014a221000f0207403040b901882c000d02c0c1010181c441961602c4144c400d4800007056011b1051403c1c11648210ba0149101d5451041210140003908030b40180901040c2c405140404403c0c065404a0705642040095040400503601d01cac020705006002c1004068a81003500b20503140c50107004141849440c09183c3d440070780c0f0004180840c1507011004201a4121080b60344500300101c2c0e0542e5090f242001c20240c0206003a880c00d50705a200803c04d100004962041c002c00c0d90142203c10342c121441c01902c02c0100d0100e01380d006a040080040790703c80074000b881000a009458040f00240c51030301fa00c2850f800003025000107031400c1401c0a142880155080d0307040c815507a00c0320307445910 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 472854226 1250 472852976 472852979
    0x5040b1002070314031b070f2c061513030311011404081b0d0207051f050a0315080109060212010e042a05040c020307020306090705010c061503020607210504 69
    0x25521512480007070014014004d040030442000d00480c1d038910700070041050310780b806056444da15481ea202c0d40412032210a004540c0c070301c0c610170f803048400301d280d001d0181d00780c050780c40b01d034885000d007440e60702000740441034078000e024001a00f500000d80742c2d059070035031440c280030708005042c03000361009034904280b018607104006651500903400401e030a46421000c0c8500784010210150a0910301c9403000c90191549c2c00903500090391001d40700c0c2d0300c01610f20704e28900c01e00700c1501c404000c500b06201c60b5240500c00e49c010038a071801071401c0ca146d103644000050071165462415503d19400280280444820030010f41c01810800c104140b07070b01d4103849148003484610408801d19000c00f1030555030b40e02c0c118044001d07020013441005800c1141101035603075402510124028020303034000502440c00032904000b208d00603150080b082c00d19a1310300e001491690100000e407010207002002507200d0b03e0103071902e240300f440180d2004500c141001110344c441c880305801c01108100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 472855476 1250 472854226 472854259
    0x506010302040819050a1a090f1204170a0c090b180c09010807020f120a020f06151012020706091406070c150b031f0605040e0c12100e060105040b 64
    0x881102c0300d02d0101200c81418003d18003d814006520720251041c030f082418007448400c00842240608c544c3c00c125030055000500c1d1540714494034000007000c050070300042065000740030311000b40e040004e0a0710801981c5980312102403109402044406580d940c500c001800d18507440d402079a84691142d4031440c1034100702271180301c0c090762141000f51050100300d00d14020170801c04102d8038002500c040040e032040d0803806030046160080148200d003040742c2150404181e81d409605c5103c0c07400941806074080c044c182500580c90020414107004042d06c10340c0780d2014040380d6208840110b221081c42c2000c04507148142c0301c2c50169000003090014144c0c00c1160356601a500c002c44440300790501900d031004000d0038650076058040c0c1614080c0844145019580c004400c60007000a242c50300107000444000042104040c4e000780ca000c1200d152140c0b081020441940880300d08e1030b80101681c007620810800d80d1030551114005000c00e14182c0603801055006596031000142c2240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 472856726 1250 472855476 472855483
    0x1f1e0306030c0306110c0d050a0e0d260d051014011704060902060708030f0f070309030c061d03040f090507030b0f040b01050f0a090807060206010503100e01020d061401020105060103020408 83
    0x100c01000c13070340d8035440e48054012500aa80c00c2031102d01c1036400344080000d015083d91b000002c2078001810881050600d840c0184034641c1d4140c1040340a00813000c081c81e80d50440c5054088800c1c1104280101d6a4090b07660241521a40740e045005520078030b4200c500b503002c0342210b0014144419010101d54401e504100d080c0d003d0f40000c00030a0440041c0045050ba20a04402400c0c5032030020800036500e9075155a1405403002074880304c13903036958500c21400c90b01280030040c00144000001004a4901e400426821000501e04002036982440c1e05280d81e0080d070110f403000d01c414108011201e0b4034071400d64403008070308080c00784191200c006154500885802e520469403580e5141060f4491030649980b4500d840ba0150744001c03052010f062500c02e442000d8413842000000320b21544082031090499201500400d480804001d01e440078060030582489190b50a124903644000f03d0300442000340507081c070a4520b41042c0c0002400e44000410a07818580100701c100025103001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 472857976 1250 472856726 472856729
    0x6080c150403120e0612010902030711011b080c13170709201308101505030d0e010507031404180f05040503090f0301020906030c0a09080a120e1f1e0306030c 69
    0x11324045156001e0200010310318001c001589a1500600e4008558143c1d15401540100c030f954440395084110304e1416400c1ea44c10542001718980f5110240c24403d024100e026002030b08040d600703040c246402050300d0b80300c01380d510100c40c0c40c5480b4042c080181083c8811006005a00301c01c2c8041003801c88070020141d404580325400550000d5290040103d016581f000b0f080c1078401d44801110420001010703007a181c001c2c1c2c0c0c0010744c0000020b90740c03900080c1c000742c1c10b005850701441103036103800550b2140c00c1190140c06000014000308070f145421001030010740340c680c40000000311002214000c9070503001d070011046142000344400310700000140c40144508540c5a0750803000800440c0c068054107105a82081d00130082c400914541d101400c01c081c030b1360381c400d0740195590011680d6903112a0024100b00c620448030125680709406010712000b02030038202c0304d051031390310145100e50041c020700d0005150b1440f501480f8407404401d12205035524040c0301d41c1d415521070030741f2203035103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 472859226 1250 472857976 472858013
    0xa02150a0510030311030c01060602010c1206050a0927030309030e01020d090302041a0d06060303021c0903020f150d06051e090f0a18080901171302040504060f06080c150403 76
    0x41c02c5c0341542c0320310030404c41d0640c0d900c0e00d00900c41d40303a032100081c0c060b1044400b1030000c9491841c0b0301007031000c1ca1184004644004001201135850942c100e4020a5000840150001841c2440706026040c00d44040782e580300340c0d000104d40a41c2e06000f400c00c0e4116112a045401c6803c24030141548882854262038040310006400c050780d0b201110036451481c00c0c5030f0044820000d64043c80f2047d030001c0c046a02a40075114186045005140940140c44440010507000700040c00941070920154030701141c040c2202d400d01c0303884484084207030400b200c0c50b1102a21100d087c04503040440764140c4d03450348210314184c0c2d00d02150000f5883d040040c07914605901c5030001440c0294250000300389d0101c020b400e04004525810108840da00c5182a00d01003220320300b0704c030346402c2c0941d00c03648a03840c00b5607010a148919402c002c09020040c03c00e072007903526040302842c00138061203140300400c1404018081c0001d08800d102c050000842072160210301404104041036000c494030083d41c05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 472860476 1250 472859226 472859237
    0xc2301021b03010f091505090c0102061b070816020a080106060203092403070809060106020303060607020906010c0602041409061c02100903060c08070201050604090c060e06070204020a02150a05100303 88
    0x900401003401800010741a01e1074504003402c40b0140b24540d400081b203c01003030000e1100d40da80c544069542c0003d0403800d80141d01c03a82c005100b03044050001c0002c8501c13180007518109154580701d51980180c4507500c1c0840005842400710300d408081400142041402030100b0340c0f0b04400070b5140d0088040e032038011389000c1e4038410602c003240042c4080e245202046038586c20940310040c006501100d4070340d12b5108400000c2407440c0004150b80c805c850090155241208076428000505006400c03141800b0700ca00c034a0000800700d0002e0005040342e5880d0f40701403200482003007100c560190525018541c0c000303144804498001c0701010250301514040c40411007201d0071140e48101d03500c0544000d242602c1d0b200410b0340061280d00a014690007444180c55038410070080715030300c800041406003030300e03800c0044c1402126280605080100b42e10b040042a0300450140e900c22030010780142c0000d03a40502c2d03041c0c01d0601503000740010004120624003285c00e0009541d85000107002d010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 472861726 1250 472860476 472860523
    0xa0302130e070b07050a0b010f0e0c071104050103050c0102010c1704240c0801150f09090c03020c010e0d0207060c051203061c0b1504020a081603090f0c230102 70
    0x804101210080143c3d10b0102c0c3d40f503025050040d11810808400c44800c40c404000083c02001c032003180f400d0f0381c50044513414503124190380511561121104481c180350201c048038142d95540b040600075070043d005441c0b034030400000242103c440d83c003510140700283c40000002518040c2c5150700903840310b80d8140c4000003010800540400c0003500100d141421040da00d05503201d03150711304880c40840c0481070911015020b42c0c040b283c0100b1203002940e0316408000101d8142c021201745421170400510700800e006140b400d4845103450700c200c1d030b40040c0205c01c80d60350422001c0010308a500c1c045d1848801751742c0c0c0c40d4468040035142c20714031780080302007002560380903070344100340d09880e038414024a200d20303004080d4207080b6001d00319941c4012245490341090700807600f28541075a00c2c02a284c0d0f840200c0c11042080300790f040c0170140e95002102c00a4079241504d420180144030510100307140208840340340c0c114402048046084a00c0049c403030b40c0001c0c0c180240005400b1500018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 472862976 1250 472861726 472861751
    0x110303120a060306110c0303070806040608030408030403110301021c0c0e0d050d0801150c03200a0b090c06041d15030313090506120d08131a150a030213 67
    0x180604440c80348854265020300a0000316a440300701168400c2c203042c815083e080c401c40300300b409104101c0400ea0010000508581d200d0120141e108400400018180752286952451034100780c04c00039440d4000101401404440d14a1446a000c210700075407078924100c07120010701b050240c440d00e415449104120119000701f005045045001c0c000080c0d40c1c07403909201c0d5803a400001200040780c903090010450070a80d4074a0030414029407a9a000018150307800c8882141c0c80d111414080e40201640810720824004101030900554403102c450900c00801c60800b02e00303440813440340340c1c108400c100113214810002448900030100b1215aa1481c403141e02149010707110aa250000190091040550301c41c241d080d20714200301046a96510310900c1190110440010001d43c85a1200c003c043d00c83c410b426445103104003203a1020006a881d4000006000e81c030320500c00c0210700f0030610256501d510610b1890482c0c1c0f005a90745181c000c2400c20003804000070b15542c5480700801c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 472864226 1250 472862976 472862983
    0x3150703020c12091f1407031b03020a020a060e03071a0c070e01091a060306060717030708070e06190e010507020d0c030605090f07061d041b180f031103 67
    0x42035400d020f41e110b903500101e0f440242d03030000e02440d10849000e0740d6108030085400307140345080c1d042d8039040b50a02000c254503e95400c120b00807810088441a40d0455840c1c0071291a85039201383c00800030107a95204000300802c1c56044141006a02c101d4044640d800003119422070300c10604547c4407a46141e0702c2c20161003091202020b610a40a0025040c00b054403050704a507a00d090801c40200d2503a071008204405201090b8418000c0c80414080d18005005010061156864030801c0304000880c8585400c2200c40c50b0125025504100411f500090341c4540320400b25413181c603004584180c10322409101000d001005001c0e00000c0c01d03640120201c42a550f00204070301c00001c8071746000030720f4401ea0f01007241c805003401e021130107410000a008800d030041c140540310351800c050b01101c103a041004480c15491102d0111041c40d1651303c40c005003500d40c60010703a0007101014014007241e007201114011032031500400c000020f0700380003210540341d1040207a074202e0004c1001914 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 472865476 1250 472864226 472864237
    0x908030f091f020a6e1303050105010504050109090b040f03122903010207050d0c0c090501060305070e06160803090a061401060207060804020a0608180609010b040b0d020315070302 79
    0x1901079842480846440c419000c265850f00074400c1c0001103600100814660340c100815280d244a40f0f080e070410022000302201504142e0011420199217005200400c06d080d8001d4400e07035900e00041c01141000d00906d0701404e201ca209003c120410b5540d003400340c2d4001c20240181000c0c3d00e14208040c41049100c0071901465030a014402807040030080e0181007001d169505240b405040c0018101802524080b1f80c00a0180017001068042a6800c022200c1d048908404494002c66a0b6405218041c0a041d1a076000219480c2815010b0048044010700610651703003408060401c1c45c1c402d000d1103d403039008050a8503912020071242c6031000451004007010700300b162140c4071680400005040b6540c50382220f4185507280002d464400c020f440c0130703402c000b10360360a00602d40190040358200c00c103006038885007441c00700442c2c213000007500ca40c44140d4660001201c03074a0280a01607500c40c046441c01207810711680041c1e51991107a0008010801210014500501941c15101e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 472866726 1250 472865476 472865507
    0x12030806060c0c2107050306010503031b1c1d090606031501050d060305160f0815061f0201150e1504090201020a0605070c03090603050613020903100908030f091f020a 73
    0x42d0720f001022a40b000094180c4c210080078854100001807e1600060050403908060050751400d10310200c0c1c440414010041d0480b41c0c0714201941c6d4100c030004850010703008181e41e88103010001d13500c4244910180b1002d01d44540e0b549028420141d41d90011a604060815520408804d40e40010385280c0160400d50240615110f000428040081075004864070040c071842e014a0329a460084801c03824016000d10b80d00242d030861b440401c2e003c4484d0049070041c251001035507100451804107080004020060b511040c0b1054000c620650b03010280c0004030724070b100703860442d0f0f04464002407032004911035a1a80c1e150390959000340540100e550704650b0074400c2d4948580b02a10b04140030000304c0025981d6240010f401c3e200b03100703c1d4050003006245006d28245030410034040d400048000f0f07811702500900780040d0041d0b205d42118148034215060301c81c640580c180010803001054240160008101b04621380141c4007004080d1900440068941a01c0e003000c9071021740703a210f440d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 472867976 1250 472866726 472866739
    0x8130209090f010b01110d0e010e030d121503030219060b0d111305040f0b190e1f090206042d0e0a150b120c0c071e12030806060c0c 58
    0x441c8514020a1031006951200000c0c00b2400c2074030011142d803c2d80c182160341300d41024102c0800719201c2c80795190504014901814010041000a0309040c209034402010848a2545025035912802003001c0000e0036289400d227146951800b039210150192030380522549139400c20100045030b4090390002d2006071003202840c1d49403400603014036800c44020322410400c0080407040320540225885568070002148007103803e0703a250790407540054409200810041c01228950500d0f01c01d1750780d8000d0381401424285041c504804034000317907032401e0352024204408000940c17541400c44084034404512500800508403058000c0100e5621094100540000004070824401c070058015140600d081107452012589852914480c0c4540c05018000703106000a9515200c880c0754001104500c2910b40a01200300a007490810782041c010005202841d103402d429000001d8083c004a0310b0410b03210382140c0b1f0107003600a0003013486100780e6000440d41c00900301408411512200036004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 472869226 1250 472867976 472867981
    0xc01141c06121b03150c0c080c07030312060e0601050d0605040f02090f0a0e0c0c0f06010803030412050306010207050d0503090d03111b0d030f17010e041e020a0608130209 75
    0x81c0c00400c102d50358141c0304004070454810010000b241e450040341c1e800ba007000e00b00240a9109405000c0d416414001d2101c0f0746450004160340c00c3c01401042e5142010b41203d07400c0d0b10700a03218641071681d040ca083e161410a1000c0c1c01002440d5401083c2400e010b41c5076030351051303090050402a001b03650028100303041c0f59800c7d80227401030100080700b1100b1030b035a9900442070282c24a80d900c1110600d0400d0030100f6411002e5000078101e01e503031102507441c52034030100940d182c0071080c0c2c0090341c0c0d80e00c0002040140012208041c25001483c68141e24500785040001c1d42c803031582c0205803140c6c0280c40300c1d0342001800c2040b203c20141c05415030104616905010788014940e00074509580210044d00a980d1503c419200040c44001e20711440c56909450407141c2d000034103074100500281078041d00041d81200b81d024001d1038000844800340c503052130498412102d44400c082c030728581c2040d110040e600e16603078100361481880c160620340e58094110080505140000e908900c0c00c005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 472870476 1250 472869226 472869239
    0x9091f090905030a030b060c101d030f071b030b0f0c0d0c110f0c0a09020c0705030a081309050705030f09031902161505072010050a030506030c01141c06 67
    0x98413020409840c10406c5140c20760a01c00d00344581100d40700a80c003c140c0b8444801010b41c04180307079038002c40315001d1100110300914a5170788106020050b010000c0360307480400a41580440da0341c15808104402c1501c0c0d55610317591401d001d40301490100c0b0400000e0150510f59050320001e00300340d802481900c50001001c0c000084035001e4031602c0c0104a19500590000603a07900c0b45040a0800ca000528008402d0f00940000e07042c040c441c0241100007805580c01c1082600c0395000d030b803200e81c5e45c0012880c0030a2810030399012462041c00c00c0301f089281504401a81d0303120403482c542040598400c0452411442035543e03800d80404130441c0b0b4480640d0000300304001512100c4000e0241c5d44880200c0c1c617600c004034000002400400000000034500d0480c0c2400301410269500c1c1800301000084060000d0b011000029101003a280785065250060603040602036000d840007590200c002000c07a01916a50b0041440000d8140c00381c0700c0c50f07151010b161000c1901049659114003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 472871726 1250 472870476 472870483
    0xd0501090e0d0f05090f150403081c11040b030402030a24060b0903120a030b03060a0e0d0806012a050d08090d0228110d210509091f090905 61
    0x600000c03461044030b246100c00c9020388481011004942c42d11810103080900b04901c0c2c0c280804501d03085103d81c02c3c1498080e03989005400030354400c1500c00d86071942c1c40082031f0001045400f80381c0d0942001000c03279031260f4800480303041e124952242c0d41c0c0d81e907443c00828a0302103000c00003070000c404211440008407445400381c80c0302541c00000e00010340c0e10042c2c7c4d5083d008500c170155158000ca8140c8001840070700c028074400030300381408550301c8141c10000b42019030850314142040d45898220740c610710700b40068003182c4240d0034805040c1c00c2030340c002010b03140e01440300560000c03200200548141c03110354040f941e40d0312070b0803240061003041d030040072008181d4174a440c0d4410740c070b0319040309400407800541c100c056a0f01100600c0c00d60940901c80c0c11200380581d0507907115020f105003a2100b4000c603502d9801031340e2041024154106100d080c0c1d44c0592000100801444600669510344062a420185010030b041c0e1001912800010801c0b0b103500024109240507851000c220303022 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 472872976 1250 472871726 472871741
    0x30513180b010903123c030b0105210a09020901080307021c080a0309060f090501060510020a080304060e0c1009030314040324020f0a120b061207050a050d050109 71
    0x3000240449034100c4019100001c0c5070100406042c0c01d03544911072248070304245c000c10204509101403000c0184203180b590950030425581c803da078000c1c000840c03a094042c6590800342841c000e4501810146d4900140c4000c102205400d140000801c8030000c2c65007096842980044c910f040c9540e40d00340780390b502d501c160401c0f0301850244102110051580002603062038206238228a0708020110840c010f00d07990b2002c45901c2d503500380303464441d5401d01c5200c03801071003075000050391428001008488030304c6036481c1c002c562004405500044540081d40d0300958400700104050604815403420915114280d0f60003050b8844112801136000e148201200d0007a1100b941080d0703201c004040d0361045020280c1326503c40307a18103d12078462101160103c1f003042d401424180e601c482d181c104c2d4440d20354140002c1101c040c00303180040c20300c520400254100d6a083c64550400c1041c60611001000e400500c48003094a5001d140100708442420322212800c20203903840316100001400103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 472874226 1250 472872976 472873019
    0x201c09270605180c0702010207091103100f2d030602030f040606152a02030303100801060807050f15040e04060204061116210503040f0e0a0209060d09030513 69
    0x500c0000505801c028400300c910b0b69a1440f0310855954400c00c0903100c0d030003810200d04501c04c1a80000c1c090419100d1075400954004419940341001007840415031003682162035440400c0d0010400c600c00151070b40c081c842074000e81c140002c0000004c0c2011106507102a15450000040144030700080602c1d610840c842c0b441001242c0d12441d5429030b854801e40c0490100d0354400250001402d4a0106a10000124001d181c20245a800f1a007590803d4507181581c40160005000700002800356501404208001f44030079403a00d0000f9641c01d803075010b00b90154640440160300464070004644c041e110204616010f0b09003440c1140082d40036108000000b581005603c0081c900480c002c07841940c0124902400e60a0810756102c0c214a03c1c24810a02d0400348c0a000182091000d0710042c04800c0650720a145005840d281e070103c000d0854010f076204015101e0541d9a040603980141515140011100720030324059589100b00c003203d1503503e081190024400c02e8218980244105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 472875476 1250 472874226 472874231
    0x180e0d0309030207170a06090501020310080105090a03050a090e040c0306050601030b0904110301060302040f02031807030305030c0921010b01020c060c0325150507201c0927 76
    0x1114a084084840c015802001a000150f01304204a821400b5171030301c1d07031041c007a1248054190fa52800b00c4070856400c407070310394001c0200100304400994010040c904800240170078a04249001d8680d44554801024018040386d550304452003282c50708050a41814144014242410611700031003c038442110503c1c203110008060394800c0c054580d01c0c046c00307414000c0544940e40e07603030b640d8a018482c09405640e01c000000c00f5035180c3c040c0ca940014210401a80c0c0d040508110005024506204070240d00503542040013230380c04400c403503201c421611a01e480701c160100203203e000c08810a941d04c044240192810110194405006004e00f60201c60050000d9014012507000700e03400483d203500f090018020540c00700640400c012034403000003866001c10340e66041c8045240c1c0090000d55940e0042003082d0740c20207001c41d03448410f50000711420121610b610341d18002440112101e0051540d082c0c8130601800008029100c1d60b6070140480c4181c10304001800c1003219003100250 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 472876726 1250 472875476 472875493
    0x702101119120213090204230102030a030f140103201e13020906030c0304031112030103030f02120d02180409083c04090f050105101107180e 62
    0x1103800c01292080741458007180e40c4031004401c10350340440d071903540c2e204154080055540310650f1590b510090500341d50010380b03850401c0700a5030513004490a802141c00c0c08000150039a030004192050b038a200e11340400c103107184180c160007074071954220301403480d0283c00200410030b5207860f20441003058840110502c120400b04002212000c1121100c403035174408108072070070b02603e03000c100c000e42d070b001511704600030010400c40d1340100d84003900b154010090004056000580d102c021218400070010000d044c001d00d0380521040c0300040a010304801035504880c028468813a84468500406440d04040e804901c0654040d821010307580b411030003a42070318507003449020307099604032040a040c1b100040c100c403040c442040403468442001101101d2000c3d40e4180700318104040140c203034885180c0801c480c25034109240c1c5c441000c0c100030050006031181c00078968080b2031454a00c0451011410b0a800c082858118480000308488030410030029074102c04000152482100c1d490f6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 472877976 1250 472876726 472876751
    0xc030c0201141303030b150a02100c080a090f060905010203150a030c140312130f050d020d02040b010c0219060906020708060f100819060509030f160614070210 70
    0x80d55280700c15045050b0480100b2102c996151920140d00e02c00c1c100040c0008450000420503141c0003e00818607800203100024140e040c003d102090800714411f11000e6070044000d4046840100000106640c407101e02c414041c4070039440d500c0c141c014408105d04103403810b00d14041e600850703510380d403220519121038807800c12041060459070802500c110352405c015540c1e421540d403429240d0f05100351820300c1c01070391740000105201c03541410840d02c42458082d0104444c0310b5648010b1040c0c0e81a010000907880340a90050a40e0b412900022841219001601c043d024020007a41040c1c12240c109258042602d203c02566440d80300c0381a0310b55141022692900980101e8190740c0012012460f031401076a00c42c1e402264200441038100c2d181d02d55580390403070035949200c140c3c1c811056001405081c1c40b410350409045400b039460031000c07043e08841031240141070211541040034040c00d10165500001d050a840980d103005030604250003560f56628070301c0d00010600c1c150180303001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 472879226 1250 472877976 472877981
    0x40e0307030c022707020d080c0403050c090903130914010515040e1909031e1d13090204020307051c0207030f08061f120e03090307030807060e100c030c0201 69
    0x21592590b01d542110ba40d5a00b405401d420409118011926030b441c0d0b48182010000c41520a9280740d0003000c07840d415240050081e50060701d0205a84010003080c808181c0c0401d01c045078240c2904c2001d056120901c1c3c15103148100808841c1003112510080368841a50304500090b14181d200700070680d0300c5908008409410b2400f002d2012400c000800c13442e01d521210b030360f0107400482104410315510300580f0554544141c201c002444c65003900d080c56030444030640d440c103130382d05d008062040f9100d05044200303941d42e1038910920708200074042c0850300c0d4111040d5130b41e01800030b54580c01d0440c0c003d022604080301c00941025143c510401041091007600c107040d0701551389108801e142c040507610124054a01500b001c1c4d40b203651130010b00c900e844110340c624550f450908d2242c600003100c040307a01e0713604500f50300d40013040b08940c2542c0000e030320402c0e00c0c1c000013071580c1d0b1500d9140801c0100054813060140740140e03201c005000440c0c2e40146c03542d5075a0385080c04540b5404100721308 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 472880476 1250 472879226 472879237
    0x71502030117102705010e061603050f070906120e03070b040c0b070218270c0a060804050c040c020307170301030c080c010f080604022a0d1407030e06070f11040e03 72
    0x710641d0b50420f0113244000d07410000c00480c0203000029406206280641c14054116800c0c0d11b030b2026003511a140c10b515100303071503000d4900e5803242040c2c28180c5004001400612170394042182108940110851030351011640f1020601180d81e42c4a052030181c88600c401c46050f80d107401c0340000001c0c0c1203800000c444801e0741c001d008610001c2d007490418034030100034007410304d04000c1c2146002408000b0040304c41a000c401c0c01022a03030300744401c03c8618041904418100014881440002240060202d003a1001154045a56407103650103d107903020702c03800a40070f14500303141a01032641440041d4182c9005000244810b83c58054140e921250042e1150015000320035805815200b000410380242e001880545404100318030007404122600720503001c0000d40941c0c5118600401c0341040120301c41c28004081c0d0160034103008503014152010b4144030f01e00040e03000320750780d01c0c080b80c002682c041d500c0304405000c0d040400d001055020340703038000d41c13502d0410841120000250350 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 472881726 1250 472880476 472880501
    0x60328060c02060c0d05071205040c05032512030519081909051b061303050303062b032102030901020d0608070b04051c0f03021006091506030207150203011710 70
    0x1480c10030781100c03080080c60014045001c120410301e41d0405803c0758082c3c9d83c0100c1c0100280e500441c200030030182040001c0809001c80003000c07008136041c140a0340303d0011604c044001c6c482c11800b608059806118020b0340813001d030411019031800030f0300308822500500e01020004503250342c8121b030340125410214058120380c455a02c0740180ba03409000003040f10740143c0002d080080e40c030700d801c0780c481960b001114150404002c00c2480d0816245007031240040010b0b001e1012003000c410701000c01c040b00041c1c1004210291320114800c080060550000702140443d40c9140c1060228002e401c000b0307100c641c560400d4000200c0038000581041503034141c24220345414030f014204140b03030b6195081296080742aa0440021070100040c5c001c05500030740182502c1222032039624100c80710750700701910341450007000400e82141859410195400d90600503500c4070b0f0f5040c50040000d030104580140c5000100105440030a40d1a0b40e00344852001260800101c0141040540e403001c1504e2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 472882976 1250 472881726 472881751
    0xa080d20060c043807030230071e060b010e1002070b0a03060b0c0309090a1b14070c03110a0e010e0c07020d0c0b1b15060603060328060c0206 62
    0x5000c1006012070680c00136100c030040310f052070840c0103100d2a2100c1e070f40020b4084030011446038107040c5c041c0200241456000c0341e0502c00c95070b8807003520312110741094118000201107580c0702002481c071250185018a000c1c800c2862800385810806800d55540c11800143c9030003480b44181028640d4546030300e03807030f0085c10b80d060401141e8001c50b007040f4594420152100e40010350398582e100108a041c0c5100060755541403900140309500f00003600100c3c070907140151f40804031807005031280802c8160300e001c1c042d04100c1184515180202200605034840c0300c10700004110b086520b50145400558843d0801581c0d180300040307500d030911846001000c10300001d07419030300d888024202184001c00944401440e0f4450b419000100e0b04100000200010086001c01c2001c04284810000000921880b42c01790a0301c101c0c940040c004900403040403000c0b031160750341070118486140050200a010010100303001c030384000c400c1c41c02e031030507032034245140b51003440480d1451003042d810442 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 472884226 1250 472882976 472882979
    0x3060b0909011505270109060908060a02030406090203150a0c1b0f080c0304140f0a05030a1b05060a0e0405070809070b030405010b0d05010f0b03070f0509060a080d20060c04 76
    0x4503028084030781c5840f04001003000600c2d541081c000ba0320103e00c2d01c003482900c14410200001d04a6101c540040080c002440070812207403200040c134a03807003030a010000d41c60b51030b545410009000c0c0c000000f503050007101044400010b0501c0c44030f200d80482c480c18418403030928002ea4000c400242c00342d40703512203200c01602041c00700109002c0c0c0c520800d092445d001010300c4040c2180c110b900300181e00c6483e4040b003505483c0001e080c0850801c215109441c09241c00002580c03008000c0000300b4030400980070700c00300442c0c108090000d02c0050700f0b070f82e0342e03007502c0070014501c800200d000c0380320341d150034045803c040c4201e0b0241e104440c2e07040206203203820301800384141d800081048645640b1052203200a0301c0c1c40b5099105a4425400410203039502c1806500303840d0801e18217400796201d444100646641c1003030000c200d0b1429a81c0060588410005c0345d0541c4403a00038100340d114800c80d080748d00f648000a06d11039086401140070750aa0310300d8681d11039009580d01c000314401800b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 472885476 1250 472884226 472884239
    0xf1b030512010f050a23060301030b160807082a030703060306140705040b070c03020d08040302090912090607060605041a0909030307080601030c0e0a17100204031a0405030d020310050103060b090901 87
    0x150742420102c0b1b590351403030002d60b039000504c00c3d070300036081150b0100703040c414003070200c01195281802007111b092035102032400d1440100340303041c001e0507981a05083c515003084a82c1040c182c801106c0c055a03c85e9480c64084c03006030240000e440111805031800702c40c545c02d9040601d020740201c5255551500d404e14007600300f0150380142c0b10a5410b00d201c810008016561600082e1015219126840d1920300d54010407018003401444460250401d102d4207013994448411118511030854010b45c491115003884c00003811075422464125140882c602c02141f025604046052421154103a01b580d414182c661039000907101c2c100423031210404520700c1d41c00380e007000c1307034200c50b0b4548800710b281240002020340410b035001e00c03207046254281c03004000e02030000c00e1001344846003e500c1c0510310341ea48600d4010100d0412030b14801390300418200001482251054280c2c51829074581c10041c003480c03030300b1600f03110341c6020030720300348000036400c42144c03d60b41c249400030900a0141e03c0c055 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 472886726 1250 472885476 472885499
    0x7050f0f10050d0c03050613020a0e01050307090e090705030d110c041e0207120815030303061504120507050a23040906020408030a050706050f040b070f1b030512010f050a 75
    0x64001442801e00a1002510b618411103a802c4e00300d0391301040c1400c281302800314040705d806050012500401480a0752600008010300580080c0f0780141e43c0c0e03407442e408451090140c1c1060006030160028090302700c50004101007512400c40c01d031641940344d60780075a141c800725403680000d07411a080c0c0300164a800c2c0e10554441514240034085c1010b0000c514080340c2c0203101c11074030003808d04032000500e68058461580100c0580c0003651003c032450000795030b40401441c05114040f1766415510307010182041d14010b016840c94a000c054040c078255803184107501400e401440d4012002582841e003503001c1d01111120314003c0c20002e0680180400b50000315804c0c0ea00903000c0100281d144d0040004085030505a134601c4d03143d400720b152401c103650003e491759003200710141c10f10000c501120310b110f80242d881c1c03c03c01910b00117201c0640780c40c04c500103c10711a0580507400c0b8203040e0800001c0054241d4540c44040c5a0380b10000c0800d4541c0d0360046503080700400205000f0200140d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 472887976 1250 472886726 472886749
    0xe0603030309281e030e03190624080f2b1b020a0f0e01090e030901050a0c0807061428020c010b0402210f0f070305040219090e07050f0f 60
    0x40451100340c0034a444d03801515080050040341882a5881102810b5200c050100013039812000b034036800a62020f108e45034440640058803060f80e54005000f5015580300c00c0d1203480090216920701c3c4c0e6251500c1e80c8a884041020101d80030302e0921040d04100c0300348010042d00c000700b11000d28140b100342101d0092103080c00f0700c03a103401040260096600e0452490090046040a020903414175100b90030265040e402040a2400c190041000c6240407007a00d101d2002840c2c9035807a201c0721802100d42103403001c4040c000b00c01c0060143d041c00852b40003c1402c401000b404070040e164242c904500712500101700011500e1a61041c182d0030b002e400521000701c900c0000305484441c1c000240490780001c820f0300301103070407c605907400309840b441e55074000c1d101007448019142040310031103030395002440042091f0307850b0002400c550710342c0d0b208103220588000500003c1e1701e807a034650061240024100c11485100d200160501c1c00400142c0b420901501c0542c0c20349908007806200c0300c80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 472889226 1250 472887976 472888033
    0xc02030d05070b04170d0e1e0c0f0d020a031e03080106020a1a0a020408060a0903030c0206100506030705040e13110a03080d050c070f050309010e040504020d03140c0709060e0603030309 81
    0x70000850106c910b4045c00756140b100c00b0103402d500e182c0140c5401c204505074000d00caa5042800c0c801d8155440c032031441213400c000c0d95084e08081c0350f803000a0640c049a000145425402030307072261036408150030f40d005c540c0301c0d480302980340c1d0300d41405030303a188101c2d800102800c0101c00540a00b0800b09410380c1c010300034600c05401e260329120307401d00307140c1c0858002240c2c6e580c40c6800f400340750745401442006201030010f015142841122929641805e0103680d004900c00008100380902c500200c500030031402072824140e0900c0c0d16410f00c07848035584181c90f014042d0f52072864a01c0e000c044682165480780d08503141000010488000d0500204102451102030200c64003181820b07146480311032150700a03550b122031641c005000034640386085401985440304000050304c07206960023043d60181400d042c0c4000c15010600c0318850091f0180c124001d540d00001c00032001d40046040d182403400a01d29603591805140d580e020403074120311300758083c5840d901c41030f00f0b181203684925035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 472890476 1250 472889226 472889273
    0x902010201230a051e0a0b1c03050d0c0516020d210801091a0f130908160c0b09030d08100b03010608461b0c02030d05070b04 55
    0x3800b10500d5100c40740601c00510441020811140c007500d031140d00d0340890190301840100303080f580b8100b09014002e2144051750ba0300d00e120035040e030322543c8002103250b4400704c0e010025540c2c50014a590444100b51903007904002000401900a03c150398a0080c010003425a0020356020404401140e000986a01480c0da09a82e1411160720050362040004d40b200d901c02d514007101d500484485030100c20410b803422090f000c583e41c400608441e858800c032040c00c003400c0c0b07607400354000380700070900100b07032410000e01102080819603980d04250f00801000a03500c1d034030404219507100f46160301da81038200b2614003c04600552002e43c1100400c80040031441d01d480303260038550300a03084140841c9203101085940f04680c4496100c558030107682c0900c11031080704055000400401c0142a0400c480302c1c0c0d030480140d980820b07610310b00140d103a03464910402c4054010324841708262300900407100301d080d00d240500200e55003154040140b044960741d90f2512890840400000801d084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 472891726 1250 472890476 472890491
    0x306011209060c170702070302010c02040c031e0c0315030f020d14030a03060f080309100503070c1b06230708030a0b0d06060f06020d170903040e0103050601050f06030f07030902010201 81
    0x16010f200390942e0840c2911640c010034913031501c0c0a51050010b00001c1103600940f070038030050b41d11002c4031141d0f0354140d401207102e5010040650203424000814896080d0110340409001400e0304404a0340165071000c003d00d00c41c54001c00029955400098103030722820740e070f4500506004c224101d5090148042d0741030045804003c0c0c4c2180d100741030810002c1c1d1075600c10321880c000ca52440008040303190041d446c2a201c1c10204079805c4c2180307541c4080c000c000c000101c6080c012540300e10341c5544000c0c400c503c0b45030154a0b01804560b4003500300040c0d01c80210340300c26000c030b42203000510f0008158504041103943c50800e154002014001c17096107442001c070094884044c440b640f1440b03145d011507240d003002412201c41c03034254401c2d03007150711101110202e43d800480d514100005002108500d55400040601e148100d91000051031030400000042c01004504281079490444201c40c08089039410014140401d1300d000c4181c40c086400329140f03e000790b02030164244180000304016 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 472892976 1250 472891726 472891733
    0xc032f10020312150f0f10181503020c0105070302131206060e090a021315050f06090a060f0207120b06011d03010216020405060d120507030c170406030e010506060306011209 76
    0x2060b080d210849000c001500303950311841c00d035800712081c00d4140c500e0303810f2007210301c005001e105200d1f80380c006220591450b601820001c415001c09403210306440145100c0003800200258020030080b040e075480d0801045a20b0b20a00031116003031940c0b8983c1c0c08460803c0700c0d2081211102c3c6e4211042560790000140c110100b000f4148264050400782014001900510000c507e01c070310100b05071440d021700018120700b00080c6409540c01501c1c0c5001c0b00c0f040740c000c00c0040c41103100e815442803040343c0000d01d543d4002c0d4042d000e036100764281c03070308281c2d194903044a01e59a003038014001c0900100117112544a443c80c1a00072241c5201c182d52601d030304c0702003400c9a200c2e027000301c4102403501c800c10560034940034a40d080034064410380b100d80f04548440035004e80c0c0700400c2080180000303041050512608030741d031207240c2008a00340403030844059491036170302c103200314001300c1d082c100003100005040c42180e10580b0301405441c6156030340001143e031038a0314140010b04079900d10001010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 472894226 1250 472892976 472893007
    0x50c100203040e04080c060601020705012a05010906060614120412030b04090c05040b150406030e030d1815051014030102040b040306060f0b070c1a04030f0c032f100203 74
    0x28501500500e41c6d10100000002d00f05840104a00c0c103640c1b003d1410403559034800740c0a4030001020798a02d6440345c95042c1c1c62891940700d04050070942c202440481803020a900500856141d62500c1580080c41c1140c224103004410b215440e50fa0060000780208403140c42203000940c0514000607201e14881c00075080780d901520644014a01c104140610300340382c41a041d800034101c82c100d690340c5021442c401c8500c03840c01414201501c03185000700480c03040081c0c65440c0302e81c207814009130009000044801c50640010703103012800906100c0384041d0303403250358025800440c1601c0b401381000002012001003450b007640540d4200070000311102144e010744050351080d040404d4280c43c0000f0041e851400d900314510710b85080141400051040c50000100d5517003450700383e542c48484020050314062640081e140c2c0340765109100805c0300d0a4690000d903440340a030044010340d0003034480da41042e07a100e0a200c0044400b4414071900e040780003400040c85a10440b843d0680b2190140c49 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 472895476 1250 472894226 472894231
    0x4110f04110c0a1103010603170f091c0b0f25120c031a1210111b0a05010e30041d181501031415070c020319050c100203040e 55
    0x5458100d840f00c41c0400010483e000032010084000b07105860640c1c071001c0ca507152520190303011003030009200e000101504241c4904d40c2d402440d20444114402420a01c2d51280c0c10440d26241d41c900059a40c00c044071602e4010009401844e01d03141d5906248e01d5a503940100c400207000d01d000c00304560301c0036401001141013007170340d002c0760900200252101d5800d1410b29907114071000c03110040d40c4000065180c0529280c020041844c0749441207000c0d03a40300d40c030f14003020340c0200907070f08240350000a45509038034400e0303008100d42e14a1940d003644941e59401d0165480c450f28500340d50340d00d80394615401c01c504c01d00301d0500e01942d51300056000d030707400c44021100c4049076041182e0714420407003c800c00928400034018021410b00c80c0c031047d1105010081590101c8103c0515513030081200302002407440503508190f06100c203000d0407040440c007081b44a485410044490f501c150b000a00c1d82c99030060003051080018010840c20043c80703644c4000b188000d102c00100f00c0b0030304544d0790 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 472896726 1250 472895476 472895497
    0x22210504030c140409151524140405130501030b1e0c071406010303020f1207120f0c06061419080c10050c15040201030e1606031806050f0a1404110f0411 67
    0x50201165018004001181d6105141c0c103061413031380c4056500d00c0300c04162030300d10270700e4141c00d0104e8282c50003c0350700654104a400c83ca801011914260080d0310003070580b40600852071640c0e40b00100500d0300c0aa154124403000c50b61000700b00c4402007907028028840c41641b45046000002c01070380d140c80700c01d038020350040c5e0282c0e503a0b00c440d9600340480c2c2010b0003e040f80510380a15900c482e1155a110300402d402c1216011103507000601c0f4100c08140258410703c140000b6075141d1650010380c00c003803107042c402c50f10000c0810207000404080021916603001411400c40301e402004030958100030b4100501004108410303041c80d0030701080050385811426207485080c5030000404540d80440c1194883d400840f02e01034400340c6030050000c86120b445c01040a80509201c50f443c03508103030000700032074202020b111403081ca81009605c154610751040043c5c13402010071706d00b0760b40290b60140c0b00a0002b46420140d003020401a943c4d040302900100d212071102003011110b0788401d0090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 472897976 1250 472896726 472896731
    0x602071208130309030b071b0308060102120406090e0402010c050f010507021005040b040212120409020301050f09070804080f040f03060203330922210504030c14040915 74
    0xc0da154100348407503000001140900b01e1960541d0b4082d12248803400040c004610b11130005008600c2504500c1005c5081c2000040100c01c40c40c025100e01d6094800f0b80c0940201c125400c0d000010005650440d10340f40d681510207440d00200e400ca5140c0074009038108121406100049101081b40514040280e00001400d103020034000741003280c1001110405401d00003840045500d10400541158044880038080840500c0e5a85406051a10440030010115000968a40c1e5034003a41c121541039501c10f40b4000309108102500e0740403114500410015004180402c0005002d400b03039811010180745801c0d00d8002402c613200e0540c0c403c5408c5030b0008108010040d9083c1040406418980032200354010189030300c90703c00141840c5801038180f8800100c00800e54241d0190b2042c0c040c00e0303070f440802d10313003002c00c3d0982e010700c6c02400c01d0403508d0076901da01e4454000c0b03800700c81d000560800500d08003c011407007040e11500c5180e0142c1c50300090300c0850917020b5030604010080000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 472899226 1250 472897976 472898003
    0x1b0f070e0a0c030207080910020a05011521050303070516020301112203020f0d020f040e030c070b0f0901050d0b101e030209030303070f09120c06300513060207 70
    0x115003038031000703042c0008250041c81800d000540003015200c5003401191403001d0309010010403481d20302000406805582040200c1c841c0c1000210144103544864044d42c00f1500ba0008042c0140c060600081465108000240c00c2902c148080d050b10911055410003100391500001d0035515007550703515040c0c074001040c011260071183c119840301d410800002c882c0340b0b1034002404056003414241e0081380054880d10440d503600d400c1d0b1807904401841000f001e10110a0580c0e65041140b80b08800d2003a1070001c1000ca58000a1b40d6a105044890619040b695001125550401002d000e510760b10742107040c0182d5159490f129442450fa500d0101001c80c9000c00143c4605822114007454070401c40a1145c1d1404001c40c0d5006800d0f00b0320840040c95080102c074440066806504400c00b80b81040e410444003d044c1e000312685030385c419040d00f2000c3c016055002044040c170343c140008600e5032019441070f03080a03a10100f4024412241c070780603285e601c16030344802400c40b84241c1c4c100f42c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 472900476 1250 472899226 472899241
    0x314030909010801090302070306020f0d0f0c0e1e10031d0a0606150903061109060301030b0a05070e061903060503030d020706061401051602060702150a030606050f1b0f070e 76
    0x36050040690000070b0055505d1600c000e52103140d075010141200f5000120301414404c088120340b0901c0300c004040014070850700b00f5400802011203000000340318451a04c015150481d1030b0140b0780b000340c402c1c10707440c064603040094980e80e001070f6005064075030a024031480c54030315800a1704a00c05004d4107580f116403805c3d4080740ca4603000b0780000500221500d02c2030b07500205043c10746c0d500040c0001c0700c18440c150314245010780f24042d50b00c60800000403080110364070740e0303d01903882010280003d0702c03402c1c000d60380d0b850443e0f03006800c000180900c0001c481d0810340540c514a0909000038403d0302c1e480404d080d036000307640290455400040605c2004103502c1582e004004034074003841201082e40008140d88034407501f000003014140c1010056580b00c41c1250f07a00e541c010004d04802c001c10320070712000e401c00c069590200b4034101c1c000644a00540844043d09040401d140ca8560000398001c0341d40382c2080c00700c0c428407907031800c072103460010042d5401510342c0224131031140c50042c0c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 472901726 1250 472900476 472900489
    0x1802220306051e1603021b010c09060e0d08070201052215090e06010c15020906030f010905100b0306010c0f08040306050108060c040b0415020a0b04120e0f0901030f0c03140309 77
    0x44494001e40408214a0b0b4404002c8003503084c03010316001d40e40d04580180d41815120b140320b840115480c10350010340ca150454004812075070385468100f924001c020070000916001d14001c1e0040c203003000340d82e00540c03140000344000e8100d4a040b0940003c03480c139001c0c010601d50000200240180342c80c204858000101c00010019444040106d182040000384552151740e801000707101039010114a41c4404e4044d2040c40c070010f000c0b2502c03854101c2c0e851001070028400c0004040c54800828402096081c041041c3d80d0034103056441e5480e0703280111030b0300c07156090503a40701c054149008001030590340108011400f0f100c0110762941800c42c40c070700301030001d020450004420401007200250301025501165100c481120b04901e05d0b0101b80c4c01d0806007503006008030080d004100070440c1c41800349883c00e40340e503a80d161400101c002c0c410311241c00461140d0101400f40104002031135500a00d40840c4640e141811880d41e9640301d40184410a0b40031486410110f0940d14508041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 472902976 1250 472901726 472901761
    0x1c030906170103110108041505090a1e17130807181b0801050d03030f0509150615091c1205120c03010308030a05060406051302040509060a180222030605 67
    0x2a841d400352549140d460810030140364030040d060098450024060140d41010203110450050381070205180c00c8078500d846400380e00080341d4110012003241240380c85000400c44440d48001240742c020512100440281c102e507284240f012030465002c01d000e103091111600400110030141018a80e142c1c18400340c6203113015182e80d41c1d40011200b4851940000c41c2811034805540c0384070b03807442d2421304030058020078046081c07013821b0405000d5000070000b800d0040030b111010001c85500c1d484e0070000400031984038440400c40c00e10428a50340b400460f400351b55508110108551400c03595401e541c42d02000c00b600c045000030440346407851010710082d40c0701c8030400c2550301e503604643d0b40c560f1034040075001c60b100139a1800042c2e116280ca174401c4029241c010640d12180d06102480d0010350b00030300070301c2e0083d2881400300b445e6040115201e8251004c40f03000f4024028003a903600000d401c03079941d0440360910340c200480708100d546201e070f020b54043c40e0702003080d140c24034103981541800e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 472904226 1250 472902976 472903007
    0xd0c03060f0203070c060509100603081905040b0403141507051b0a080d020711090903070c09060b1c110f030105010f17070e221b020102160209061c030906 68
    0x40040103504c2d40e00c1010040810f5202c00e0000d116207581915900c0d10801d01c044440f500d2400c0008000e105170038001d01f0a03142010a200e03403107148078108860070700442c45840c0840358240000d2001404810300b115168a11404443c0d10740301d100380b000b00071a000d9410201082001500d040000d9086030030068107038009d0005c055030415580c0d0700c10184601c2c0203903150507602240304420042c0442541034100801400c4040750300382451120340340c0d4032200049510880180c07000817540034501a103011120811039107400c100810b071045502c00d007041e44403400903a5070000c1341d20000500003d020388100d000c0f00e0381e4a0350305000c00903080c65041d21300d10060040a00f81c101c40c68100400290703008c2c0b0a881c00d81d8098138603c0101d10340b11100031055440c50404003d03201c0500f41c40c0c1c02016449902c0100200c041003840c01607080b4850510040c00f19070312079820401504015a019400680c0607011480e000d603a10003902c118180c228007180001c425407410001c1d194011914501c0051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 472905476 1250 472904226 472904231
    0x150703140310260304060509120a03020c0103061202060d0c11030304060c030c2d02030c060a020702010e06121b16030e04050a060b0301050d0503070203030c06040b070305010602030a030b030304050d0c03060f 91
    0x1003510a6580303010300e01c9020100900044d0070315a03501d4103000c00e22410900d2080b150740410398940a5100c0381618480cdd03000a00e0400d00044120a00f0350040c0340c00e1f009071010f0715083c0c0004048005d450032520700c000b07015007504001d4441000700f00071840b031030103400e000074802880000181581c41c02c55030031040221014404105c111034404c40107600120300d0780e04091001c111026400d40c000d03e6180b1846009900411015034000e030020880306100341d843c11141c07911903080220a010b108507900b584a1801c0002d40d0100401d4050201942e07488035490415258141b00403001c407049404a00182042c1402d440c542014080d203904018044414440c40e41043e0300e42c03145000c1449468820b01c200c89040e42408400c6c4102d40d981070700070b41941d82d03940343c0c400d42d50742d201c2c3d05803412540c188000c0000b864071442403142e0380c141c0b0311940c0a941740a921b103008601030490900c07000d6050008110004195960200c0341540c00e00c03840c1542c480c0e07851030501900701c9800440c1c0701d00303060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 472906726 1250 472905476 472905539
    0xb04060509130b0307060503100905091e0c270f13080904090602040e010608070f0e04091112280519060b0904060506120705150703140310 61
    0x140c100e020703614000d2040c0d0380d080198010302030b000d001c0c107540b00b040d9415000e03820000c00e03038030381c807000940c850040c031400fa0a416070347c1ca011138112082141c0f242081d4015a5030200032180408a45110001c00d81c00c0303c0c03012480d880001d5181c031114510308218040341c00c0415800d610810080c7d840b01504c10215640e20305050007115044404400070011080041c00302101d07601d550010302440c0e000305007151207d0311451407a07400c01c428001c1002044031500007616062040080100101081e034440104442140901000d800144000c4448080b1740d001000c050310354680035200020010000c0518826002540c0801040e10110400c1c2c10420380c08580801c20006801500c00701c13610720389605400c1410507000502250072056403080300e8005002c01d014080c1c00c094040c001c200c40131100f0205a51403596102300b50302c1075640140d0002c88100d45020047c1c042c18030540207081c00d6000343c1030800d0800341e55000300c64110010714108001c0c1f160030f22511070354245049000041070000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 472907976 1250 472906726 472906739
    0xd0b0112050c040b210109231e042105131a0307050f1303050706090e0405120a020a02090a050907060507080910090506030a0605120703020616060b030d080403090b04 73
    0x140304500540350389010001700c511803c03d04013010740c5407000790041c090183d41c44181850180808000e441d03095245203411040d01e408074040315009180c01ea000000040064054060342140100f05031a5005242500b80c044400c02c00410001080ca90315a41e40c1c0d482c1559146d1045c15a400401860741452078280c40803881c1c10407240c02a80c02d00f425504ca03859041211306621410010b218801180c41d400400c0000005018043e00e405403540c6146584a10800c3e02c01c40d02103902030000d030b00c540010401d0803503c2004200d80340403031043c0c1e49004001d8000ca5444101a00c4111607a941c4500b0442c0b60a0144280806020740b4500646403c880c0d40b115a490701420030000d200d140c2c1088500e4003d40100d070b040c802800b014117400d88034903113200303d03e00400180c403480c5c0c0201c0304405100c6c5860000b184513804c5d6980100751a041003000700071541c8170f10200c8411600140d0340e4950401c1d6503020401c0074001c80556a510203545024500100144035581c042488140144010b2001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 472909226 1250 472907976 472908001
    0x90320120708091f03020c01060b0901020d031a0a08070f05010c051005060a0e070806130c05070b150a0b18010810060e032e061203091a0705030d0b011205 68
    0x2a5908086119281d81c04000044da81d00c0c00304044001118001da0b641900e00d070180c0281c0542503000d402044030603511400c02c902d40c4103c800c4540140c00014000c84054003a0788540901710720308a10307060140400011660200032900110354a03404000100100c0c0c1104000e20058030083c40e2030100c2c80103da490b0381e035407419803400468007070300d07040080c0490315000604c40c010300c80194540d84074101140003a0030003d003a5040b60060381450603d4100d038145020300c65103011144e807202d01d45a450303211800b0660000d03142084c540000d0f55040780725603e54000801803c0040c3c084e541e910041c610806034052486c0800d4180140032003009251000c1f16105c004882c03950401e40100f030f14590000b410700d5581d001440d0141c80c0c440700c0c2c1801c12071400b502c0702d513980500070070411152a110380180100242c0401400a90703442c0e414000040d50910a03240d24500521440c18003d0903038800b81143c00440c0f80b201c0041e603a080e281c050f9a4440b01407914000c445400b04100d04000150820 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 472910476 1250 472909226 472909237
    0x21e0405010c1e051203160f2a1a010f0603140a050411030706020c122d0304180212180a20090c030103170c071a0d09032012 55
    0x40795040362070f0054400b031000c007020310070344e802415500260784581c05451302c0d4006951101c240310422010f110418092006544855910744685140f291206002c0200c02d1140c089682d45e4102c81c800400000d290702c181144000340c070309a180d010743c142202d0007500341e09a8041001c0504003000c091032058080002504a1010040411140da50703041400780d510004201c01d0b007520540030006403440e80800e4140b00050212054010030b485c0b802c036540d80314140f642035a426106030301c40300041440400d03003c0c006d0258109582c10f250707481c40408505c8500d00303001280307d03800003003010402e1130340c1d5003440e0700550300e45950761000000c0d00d12998404610030010203002c2c9840009001590b103000706440d0130001407203140140b50035030100a158100b80b000f11810788907070588012885149090b04d440f142e0001c010684146428001100d41d19040d600d080f00c40010000444003100314020042c519010b41c0310102260710800603000c420280c828200c0b003a0f08200c2d042e511240c07105084a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 472911726 1250 472910476 472910483
    0x150307020105060d0804030f060b12060412032304113d051e0d02041202031228050d020301240207141e03010504030206090d0801050a090f0f02040801021e0405010c 72
    0x1400e0740627840c006000f40b005500f11640075072200102d070b6001c400025094030440c070070247c01030301200d65801031307040c2e031418190a409481d41d0124545840d04051003582d1090042c0b800782104032058022030b4892440a201082400b0b0340c0d5201e00d074603c0d04e9080c800013000c003000424140c00d01d140000706580515031100351900c810802100010f0f00903000d440c15400c0f146411942d840d55100342641e00d5201e140100c0c024000c18444449803803800080d184120001022002082e01c7c4800c0e4840b0052100c0054050003c10700c0120301004682c8065800707458110042525100003213211401c0080c4040000c0c2158451a17040c070004207081420648000e00b5a000d80c2d407e4952030841100020914400340c0646c60300d005c2005155000680074003d2504106407446007144a4049400540c00d01a05400c00c15048080042e103c040c0d00044200000d49000100d0650a0210344180d0307000354001140e580d00490741c0143d44815488040140301c184160750f140c5450320002a01950000c800034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 472912976 1250 472911726 472911743
    0x6060f0903110d020319020a0b040b030c0f12040609050f01060b04140609031c09080a110904140106060504090e010506030c0f0619031409060702100218150307020105060d080403 78
    0xc601030f02c40a03048099642d00030152480d80740c5030620841c80304000c800a0b4440e80010000044503e45081210140c5034030f51461441c40c0e903070074881e0034543d11021940d0350742a41004800800c00320070945501552050001042080c0942042403030800c1810701030382c407640b410300100403580404d000c0301c003155144103038031100098420001b9860b000d8440116054059030031200c01c0a98103a096481c03008483d202c150038030383c580036001c3d919801400010000ca209030319032a19032034281a820360162040d4058150340e00d6440c111801d684a41c1c1c030038000b0980c0072806001d40d29080c0108141180715100801007450040d0010780d407251410501070203240503032414203264540e401202c85440160344a84074030000344100400502100d40849640340d0f0350004142c44060104410b80202a02e900034030b141640e02c2c6d104002540140e004403400d10309802d907940651107035050748403041e06000450340ca914025401070300f5140020703c114424030002c50345400240f040003da1b0203072030b00160113 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 472914226 1250 472912976 472913003
    0x130c080601140c1b0306090d1b0f0812090111070507030213060b0f0315040c0206071107050307030b0a0608010902010804080a020106170a020a06142b14070306060f0903 74
    0x1c1503a1150201159044c05030b45440c1820704e845941e80c8503041d00a404aa4070399654030211515148080460400100540b9072030035080c610030340c3c250409003d400c00711003c00305a550140d03a0b920002c2e980150408d03010030014440c50030310404141d104020380082c60511543c1d43c09442d0715407408024422000d06003480840417040e401071016269000c0d489980d4404811501010b07081141d541c050200240c1504106040034046d40d01000c40540081107e511a501d0a991200000b01d00c44041d00c03410100048980d820000b003c01540564010030103818918103120688080740c2121486070306044242c401030340c2c04034825a10907080152940c9810f0405000ca02400e00d80d070042421058a2207841011103011400a840c94400c42e19070342815640c00042d661988407440813412014103102c03004a10162032202c06520108a01140c0d0415408615004480180940190001c0703007000700081a43c052060700046d00355410720f441c0c243c803500b00043c100c110600005110039410b501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 472915476 1250 472914226 472914257
    0x905100522030506100f0e01060f030915090c0803161e02090f0f0a0510060e0d02090f01080609030f07081b121c0e0309010f0c0f0c05130c080601 64
    0x403034003444401072401500d03a035074a040072565201c0544410f03030840c03c0d402e00091640f4441200c84100c1c1c1091419240c01e030728040e0191203044551400c0428182c0703c0180178000703030300c4100360400c045404200085034805814009101e0540b6005440380c1d0380200300900c00741c6002070684132016409000b20305941e40c00d1404002009175070b40300030b401ca2800c07c06d0003031200840400724407c110f92009054035036512402034081e0b4406440454107100c842500b40119845152034000040028103851140e040581c080f50740d8010450b407445104174000d005201264051040300e0701308070b009008508054481c15410300c0c5200d074075801004e460001401c1c1600e18805010480a0034450b42550301c1c0c0a40740701510041d40c008420044085046405400c002d0400c0c4556141040e0210066003004001c138010755036581001e10328400e00007440a0031000441d900703041450140f00d0b54950704041d140074103103c612001c00d00807034002420f002074402002d500a2840342d1007402464110081600c281 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 472916726 1250 472915476 472915507
    0x140f0928060b0307031103061e0406031703010503070608040b0f1504050a090c1a040e07021204030302010606090504230406021c14010819030509060415030b04060609051005 76
    0x40a244000c1c1c145080003035124400c1c009075118000c0b0782c034180300d0100c4042585170340740b01c11148680e101c00080c0c221007105440040640d541000940006100c5480782c4540010241c480024500c0d68800001485242014803103a0024822414460218185a65a5507802500030140c2c0400c490034400641c0054001016010201d00074004010310300300078251030080e0001e240b041d920354200c0c91001401d4640c48443c0040e504080250900f040d080c52040f04801d44007074195006c503c200c3d01e00d4400c043d214ac0003000158420340002641c0ca140107000b0344103590950180c0d100e00e143c46e03e01d26550030840102c03c5105070050100621b43c2c0c03a4503186000b0b004214415100c58465280c40190508580c402d01042044600346403c60ba40c8900311569620028007165601c18003901e154002401003016041c0481d0042c40c0c1414075840c3d041e40402c01c1480032a4500098950040c212181880d00c582405804586003003000e0508180200d0076815258401c00200040050b0f468800708050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 472917976 1250 472916726 472916791
    0x90209060f0a0e0a1e0311030f07060503070f0302040f0308070212010c05070618032c2d0d05190303020d0e03250f11060c0115140f09 59
    0x140e40079500d519407000001c007059800801c460044805100100d10012120825064010304411a000c681d00316a98652681440c40c012909803003541520b81010b54144002006000c46075203960302c0b454a00b00c01805c0e1040b100c052028548104030512074500c00448030400c3d0394102d8600c5a0f989198804030703070b0308618800c20014a510300720300c81c94950751081c02000103d0085e03105010b075200c001b816461010207824014040b80341d0100d41e180f0f62500001114000512710420032840c1c82c10004202080301d01051028100c1c2c142c1c40388001c0c2c0c26400c3c802c1608131403d0324441c60030b5600e0b9850302d03540c0002181902e58400758240c00410140f0a030115241e036010100b00340030064403482c0440c5e44c1d401c1100c07106401c210031810b05c1c041082000c82190815041822040c4032075043d2560040c142c40c11100301c2d0016001c0100980e0001c0034000c5048800851282d2070341540352204142c001d200c034601d000e11580101c40d400381d043d60360394802500000d4003003070070348011800e07101101e82c05c00e131 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 472919226 1250 472917976 472917997
    0x50703240321020f06010e011401110a11060c0f010f0e0a12030e0c03101401270504020109030b151f080a05130f03050a0f05040b030a0e030d1503120c050709020906 72
    0x5440001c0f40b914061a1f960303040715403604220081c07040c84001510300440d50102c80789640c0c801488040490140d05540c000410042e10f06454880305007406800c008006003503a15981d1103080780c50408a040c410703070700a900701c80007512941040380e9510040692301806d44040507102c200846c0710780410300000011080050469070044043d554070001742c4481a200541403600c1d400000304000310070f401c1c0f000d555141c4003610445018411050007400040c1c401c2c0d042204810001c400900341b10b0002c2c1c06010085594403051090008200300714007000c4e40c40700360b030342103071003600085070050102034000c0001e06007c10301d9610a0012500718448000c0a040307401182d291a040c141c00400900030b2012a6861003408103a80c04241c44502c00d0f48105000b50100f04000b503c404032513489403041041001c1500c6c9000c010311440d4090340c161050f91035a00c0c840ca80b040041107160009461008241d0900b0032407a2165220652120038a02c40d002c58107400244501d080e130f48000445418242 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 472920476 1250 472919226 472919233
    0x90a0f06080a1a3d1d0108010612061d030a08100503011a01050a090b0d021b0609060117030408030a0906082406071104050703240321020f 61
    0x40d03841d03440755541000300c01950015115800035500503080e0003640c0c410801028290705050000001c00f100000c41203070000f00c030002d03050b180300e0031020980c414020045d12400043c9640d907400381508024043e40f1908841c0c0c501030b02084004503003a0100b50498202a00252500b41022072100e0302000d00c1048203e40400207041c4900ca0300310444038090342d0300c103e1000020780c488003810700321900075002c030286a500954000066209500130035025a107460b10326440c0d60368038854480c6820400380d000e031264000c9010307031080e0102000c0f50b0360305007004024546800c0054030180c4801c41030054001c402d400346140c4a08950820171900203000d44403c0320356505050070014420802c0c0d0065400145200010400c804441c17540051600c80d040f05004000c0c54100401c41240d11003074044961281c0036205178120b81d514420706100d44c0312910301040480c001890045030a4100341a440c0d074000b80030007072001c00e0111b4010100100e201445403601c850038a02039141440c0e0805c0d0008910 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 472921726 1250 472920476 472920479
    0x130e010303031d150406330801110f040902210c030a050705120f10030c0e09062a0a030b12070501020706020d020c0607030525020901050a060e090a0f06 67
    0x42e80356006114814400340801da503151040083e07512105610b2502c0e400e11507050125012403a242d02c44c9000c154090040241c1030203003102c003083d00040d1840c030341c0c009100c00b800308803e19081c016580d01d0041c0e0031601d8500105019201c815000700c0c000c0014003035002c12440849003010604611004204c0e0040c000e618010501011a03032080341c1e0041d125040c04c005c01c0700b00f80500160f501e0080041d0f2070040b580c0e6050bd40c02c40500300180f5a0010310021200080411814a05c01001d06801801c0e01450710704001554030b0008054840b40402c54a0b400101142c14280a1604490b446c0d210140d9a8900c0030001c41c040c190406400c0d40c0149a0004007205007030000b65801114000e070241d070f20955440109a84920044242c9005038000e04501051ba103402e20003021003a11a0610381d0500b030001e8618031554607901d60486081d081c00c0c0208095140401c0c05900411048581f40405800c000c002000304071500403040c0540520030100e02d40c40000d404c4100054a4984104101e9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 472922976 1250 472921726 472921733
    0x1e01020304030b0123120a032d0c050d0906021e0307060608010c020c100e0415170f070b070f060b13050c0909090d0c240f06060219030e06130e0103 65
    0x4d41480d503299176820b003141030303441d240c209003280c001141040c030050200a041518242e038603040002e03080d541e40044105d2282c0116100400c180c01c400317641da0746908000c0c240f07490b914080c001408882031290b581e40030420240d00142c42c0d50119588801200081080c1000c5490360090100081405042c4000498400d01c15482241c0118031503080b104000c00540a100e0511001074030b040008031820189049420107410018105007400101e5491a94901207640034990f040301c13807419031700004910001c0d818100001805411144c1303900d3b191106690340e0785902071901c6002001c86031181d400301d10340d03075030002d03c00402040d81c1001c1c04586400540608140d00c1180994401d2550401080c111304c0b000441900022071134440310041c120700e0b2591104041400c1c51010301c10281240014041414000c004c5030008464000c192141822000b90901101110a000c1014440c00c4100460743c001141080c103c0d060300c01c2c2d40d4801e0381d040712401019240d00a00c031800c22000000081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 472924226 1250 472922976 472922999
    0x73501020c03030130031b050307021c0b0708060306160521010618050303180d080c0601030b0702011e020306040b06071a010b0a0207150504050306180708010b1e01020304030b01 78
    0x2241c0b0317018150043d041108172844619024540d0140020b071171540001c81024001c540e83c4030050103802200c0c10491103500082c0a8a46113080400c800444110310301002120541182c21008031b0804443ca840d2044c00301e55140c00c0104241d42c0d0460720007000455500502c02c4845c6040b030702c0c2e0080a864176440b40310490301000c0c8507a100207144085104201104541004144d540c002d01451a0200c80c1007030290340001c1200b465403103a116210500082c00031801003c40a0081c009808950f146040070080d010005020100356410700740480420600294030061064800c2c6005860380c80d0040803500405c4020344141e04040700003503407401d001d03608032401d03503075820340c0d070010204d80e21280041d059000c0d600c48440075070310004003445000c00c43d0740c080c0031441c6241741103410595100e00207460503409491266140c400c00c4404400c04c9024084040a13000c0b04000b80001c0300140c022074981072441a05417200303c80310f0021411688284100c0d0000e40e044000d16215584805d803111a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 472925476 1250 472924226 472924259
    0xc0105031b0723010c0809030711101b050604020f10050304030818070e0f01090209010c12030f02030c0a11010204050a06081f0e09010b01180308070f080c0a0203073501020c030301 79
    0x1041e0003800047c2841c4001003102c45540e402407a1400c0700360f0180a01c1201c0a05a14040505c015034180c2d44030b01f102d15040c410b5450180000705102e060074018000d42254002140c3d008000100609248a41205c110781e001917041c07501440395592000002c08541540400c000c450140c400005504000d80e1091802201c0c03003201082c0503681e45094070304034410021030070b01084203442910081140e580303903694042c1d5141400300e040c0c010100140308980c002c860b60481c0f283c000c14600d5010380c0c000782440c24459103100861919003007600203584c10b8501e219110030040d03900000b448030b020000b0040e540714150b02000c0085134594442d205c2c42001220041c0c999841c00c05e141c5d04031b612803a244200c43d880d00d6000c04459056403507580c06176018040995415450300c00c4107002130f901000030840d1803203003005864000c140744101420300807290f208100400e240751603158400e020065071451810000b1004a00c40c03034400040d406030040c0700618216000200001840d4841001c1004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 472926726 1250 472925476 472925501
    0x703140a021b030604020a18090c2705091b120a03020a03080f040c06050306040e0627030403110603060a03060e0c0a091514010207081006080c0105031b072301 70
    0xb074200d480a402d03d03946030030490303010754400c1c1460350030030a00c01105c013405c0700880c001c43e021034101c0c2980c48a0001c0003131079102110302c41c3e20060805105401182501c02508042c0b018005410003050007a90f41800c0311020354624444400e1220304c5d40c41400050046014000b0341d50b0301800c80c180a52030b02580e078410b401003420000014180c2c6a08040e01d485543c0c40752081091030300b0310340c4c1280d00707800027040182c005940d62601c3e03020703001c10000d02d4440c0081c03c107500703c050842c0800c1c014a075100b02c0034a81540c030500c020300000b04903c0c01b159035554151a41510399a420001510b070456607132015003450301d82000910400804603003841c000c0d000351904860196583c1c3d00108503071400b4090306186189500620149241a4540c2d007001c01c144100c0e400261291320290500c85801a2800c9455840c541000402c02c1170001b54076910302402c0050075854910b140024112400282c0c40803200d001441c01c00b000400101003030180b224820044198803030301c00365070003441c0c040c0c1000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 472927976 1250 472926726 472926763
    0x303060608040b131103062509051305060a030c08010501140901050d0f0c0f061e0f08130609060906020c0f0115091a0603190b030c090c0703140a02 65
    0x4221907008005060065501405910a580c0c03a003010041c1c00c2a4150308983c02c0c043c2845500955900308203440c021109801540c540300c401030030140701c1c0c2c2d031021031450a20151140411403583c80560030020000e108801290960b00c403c0020303e503112642000b03003004036859000c100303400b0541c0241d06842070340d0300a4090580340300c200546032000b4400c095024400100b9030000403880d8034164520b501c61060364a006486101c07025104a282d045040050030224241003401d1451280c0d1000710850b0030403144c0d4054500e0000c2c804a8020210224002ea080f200000c12102d50b000300380084d000340082120440e184ae20402070f6003c0200c4500703a114283d4401c418140610400044190300242007c4080c5028503001c05042000e541d6040c2440740c40e11074500340c4980004510900940150400c24510000d148040350744000c2c1c014013a512481d00d440c0d141d19120f100941100c025040140c54012a00c0d00b143e580a180d0180400400042545030084c0d8000500a00700303401c4607a00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 472929226 1250 472927976 472927979
    0x1104050a120501050c070f060b151803060a0c0206011e182c0601090e0a0524010e150d060b03070311150c0c0f030f2b020606220f0501080109030306 65
    0x19040d11b004100b00680003410102c00a000281c2075804881e0300030028201e121980e10382c0c64454095041030350f05a00903141103407411001d2805000060780541c0784d82c0100903201306014025924801400350b800c0318440c01c0c0302c881c1c2142e12540c001d80100101d070181003842a80f420201b016200e2000c0da105540c20000664440300c40202100d061400e00c00f0041071141c2c039006610f800350828001c0d014103400703100c07156000300d0300030f10002c11518210349100c1c245201607401180da00905034000c6409154500c240070a4100c00d0041000c0500e003141c0f02c030010803207030914200508500940c1545849404400002c0025403481000800c5046622a40d40561410388034034520030070740301c509550042070704603039a880c010300030034500701025046440700681001e44626010301003108000b9202201d2000d4a10340c0150015101c40301a0f2015001c9802c02d40007141c850000350b0394038a90200002c00c3c809d580d036419401600c428890982c20f000d070396034503002680200305451040e030020b42004070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 472930476 1250 472929226 472929241
    0x20406030c0f02120d0b03030d09050607111507090915090f0e0c060711060703020102030a06060c020d0201120e01060f050a0b0306060f090a0302060703050d141006031104050a12050105 81
    0x8a002c6480560050480261100303a0043c1030340c89128010340c01a914446100c1a4034100040c1c400d00701c2c421000902110302e4185685440c07001421002004851044010000404030700705000d07070105402500641c0ba0100b080d541e9201075040b072103e00e40761070710000341c400c00281700004441046104001d0b0006200b071180c1504d00d0140b15258aa2025038140042d040040c01032009a0103150900c0401c0906400181ca60b44120403e0300181c3d000b005125105401d0f1240b800200303000c6c146450542d800380d000c944458003071000681849545170b4600000190358104001095200d4002c100d695100e54054804030460701805000d00a40f520114081031504220390040d40000c0c942410709145011494980e800000455007150408100100503200c01c0c0247c1203442c440c2d00d61544820084409034226107001c5071a00c00e01d0710700400d110707000e00040b5805090f520304d841e020a403034101d180b104410b0721855000071f03040408044002003c54668841a00b242d1080000380305035143c601 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 472931726 1250 472930476 472930487
    0x603010f0b0d020706050f150a05090c070606031403040e09030c030304170c060408070b09010c0e060d0b180108060702010203010513050726090f0a08070615030b0a020406030c 77
    0x84141264016a040c485607503084041c1030158081c000152a00c40d0310758500d17050741da00f5210081c0d01640711060100c00070540c51002c01c08d200640c1c04840b04c520f40b02c0040c2c8083c40c05001e500185c1d0700000e0000a11806030080310245401444030390701c844802e0400340e80c03039005114200c2230ba442600400d00503140401150a0444010001c50071505d0320b80741ca411280c406d240e40279681c035040284404020052142a103d113000d0030140d51580e4141c00d000c0740c2660010490b00e1180d26100480100b1a08140c40d0052460140c030f007107403900d00c03001704880205030003509941d0088102d402c10812101d903c1901c5d047e100010196107072511200002e80c00c0c5d01003030017402d90051042d0010b40401802d5800540c1c001860f281c218201c00002c3c40b042c2000710740385d481c2000c4564210400032106810041042407a10441c01401c02c102c42d512600303070340d00031400c00901c1c4603200e074414803000c501d08890b90041c50300034181030081c1c1040c2001a00a40c0280324a01c04a4180303c01145040d0080c0e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 472932976 1250 472931726 472931729
    0x301140601020d051303080903030c01050a0605040b0d03080106110c0909010912090e010e1009020a1821080702040207080a020f0d171503030c0f010b0a09022802120c010b0f060301 79
    0x703a403d0700005e81180c1c1c0701403254208000164141c881804500c13018442400380a00402c43c1403c00145c2d142030105001c01c0e12500c101c501d015211030042000000c3d8400b8115045880d030f4a82562403a1418040500b040c0d8001d016603400301c2154213010300182c065210781e0110344110000840080c0341d44047d1a80003c0d449441142c01e0800010401d00c08003185495001c1014090903c415403242080000c83e0889259000000c0042c4503003240c155402c01c00300040c21021030005d400e0507071640510341c80c81d41a40700601001c030100782c0d0811511150156256540e201c0c0700c45032604d01d440b40085da01c1b01c05e2040c2c401c01c0d1003502d21a001c0c40d40204040b5607151039071801a0200e035207074a040b890007070407240465014803040003c900c02c80c0090080104080c00e00c4004601d241030001082002c040942000c06a94410800c041942c1140d075a002034289620341c00c0402801000e805a003017040c0b01c4826944000d00043d400d907202c01c103600407424140c08440b8204181c3c0d0a81c240450750009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 472934226 1250 472932976 472932997
    0x100506180402100806010c0b0405030a121e021b03070b1009020306010806101e030603150e0a0b0714040b030f090c10030e0c0a0605090306011a0306010507060b0301140601020d05 78
    0x2903014403e1010321940320541c2c011410706282d006134070503a554240b00340c4111426211a04041510320050b83e01c20200070301260344000034032401040d1007148100041c4429074850281d8001499041200c01c050743c03044045940c4180e940720f41c081e040c2032501090407100404414030302e590100b00d803001031007928042e01c41a526920f850703843e6014418060040d90b908000d0017401051800c41162881003003d0100352980c0102c2c042d465841d140703507400354400e8144865820000c020900712000103002640300d030464011604ca4641081c151780035a107203292008607040020300811a42d40d082d0095000c0e0003041c451a03107d643d00c5403142d40f00c0d00b0480710036601400c82c070043d8544034465080405c24044c017609840c03006041c180091108200d950081e4041900460000010f26003442841e00412000180d00810b030500b0103d110140300c000d0105050001c08941ca000340201d075030221003000c0c40a00200003005820800d100904000c4904e5401480352503c0b40c030b86640b09000342c61040c0360 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 472935476 1250 472934226 472934239
    0x6080903090f031905100b030105040f080f0c01052523030a0e161a040602030d0f06030515040b01050109050312070212100e1e06150f03100506180402 66
    0x1000420801c0d007848001c0c0240c1d1500c110041c5070410803081c201100c010b4444c0001b004624600c5a15030199044c59080a100e64544801c003c04a411161103840352a07014500a0f41c0744d00b040544201801150b134651030941c40e190811038400390000300000c5124001c40d00065529822604036102c60078000b18014026101107280365444290b406550001420400482e040c4e03d0101a06c3ca0000341d9511b038100131068000c104441c0400c0040001109160442c05142500b0140041d580c1e10584056580c0c26a9034035105149503d154044c002455204064818141504500025240d825541540c21914500000410758041c01d03100d400c60301b01070050503142400952000407900141d04c20783c2c0000e403001d450340a40344280314150301c2e20346010780021140c48007981d440c0740c008031400002c284c01950b68620a503c0c0c0c001011139100b034880007100403c800c6480420746201408240d190144905043c00c080f40d56150821449a1030a5412020319240c610942415007410703038002c0c0d003202 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 472936726 1250 472935476 472935487
    0x80111090f0d0501020c0d080f0a1107121b081801030501081e0a0f0507090c0e0f04051e010602010b190e0c03040c12032106030203060105120111030f07020706080903 73
    0x3002400102e0560040c000142000c80c0c04100c1800c120440340e403100010001010004002541c1da241504900610810800d410031622174100c0d501c51a8409008510b140b805100b150b03110b00c60051140c0c00a168444040c0750514004284d5000181640c0070019400c513001590351080c407030f643c1210098401001118080703015241540c0c14404a10280e00072014400041b850740411100c11a103c0c03401040c03551703e0050035900300e54480c901042044020540c2c4203caa4400000c00286c1400f01e5000450340c8035626880301c0786198461450400c01c2c510000261150194404070801406036904071031008104c040135255080e50103202c1074041241c01003188042003034003441c2d21034400d600c0326088607240c410740600d40c02d2500c42100011443c1400c01e2075400001d00d4064400720100040c1303c014196800a5112041401178074080c005400d8086010582500003d0701c112040380000c0c0e90f8102000d2a920f2410708031850740240c030074034600141c0d003481104200e00ca104070b10050350910 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 472937976 1250 472936726 472936729
    0x20a080306041515090609080c0a0e060f040f0e07060203040f0902030903070f1214070f080a260906070c080906030c0d0f050402013009050a05070e01080111090f 71
    0x100f0705443c4580000340004008141a1102c100d480e074201059210740301550300e40007000340004c2844c1c201c4d034407039001103803951000d407116524503043d10311001301c0461b180e076054003148842c060407000750341c09030801c0280c2038a002a50b1045c4260a4920150b41640303848000a0741d40c1c1c031951140359060b607200d0340204448545603002d181c21103240800c0d6890192581c0350b108171040f0016080e10f0307440b00310030f000400e503030842000d92007284480300381424050551a0600354280b010700182c002d482c0010107500040c841c0c41c00039070b00103d04406852000b140080c103070210030201c1d01d49206114100104541c0f40c0525100361003c3c1e406001c2618025a81e000e0104a4002420310114042e0074010f42c0c142c43c54501072035034021011400007640345800e000041c0020051218407031220315902e9980624041000c9480d21a956084085001c2800303107005441e02c0c4140d100a07004e4001c1c101e001c0341002c07080c808107040f00e01c084024020f0954004035010284143c80b1501ea1000c030000c0c407265103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 472939226 1250 472937976 472937981
    0xb0d0f0f170a0c020f0f0901091e06030f150b0a03060b0f090609040f0201090e090607020c01050a05090105210106020706110d08150103060b031603140903030438090d020a08030604 79
    0x4130031000d000c0c2500030a121020507c130810a8200c01c0c2256200c2101c0c0b0107c511581c25183c410645800c140301080c80d50326402d02450003068081e05a1110704d03a24030a030b44181d00b104039402006010581c0b02a84c1c2c0c1049002004003050a40c0300d20f0036136120400b50b1410500392402808000c14052294645954820004441040c04c038140001184006411440844018803921040e40540250301c4d00c4c40009081000702d00e02681801000e0202c040c08990210555041e0030007800c20660310804482c003200409442c85030b040c080c0518200214406a02203107403000c5817200c1d1901140658115421912038a1400c0c2c80d8001070b0309940011050310301207000070a41601810000b030f141e40c651030040c10680c0304031504001a03c44d403081300b03032895040c03081800b4145000c41d0760f1480c0c10801c04064036840003510190004050520180801c0c0c81c0c0707105a441c1c2500d44002d168031044c42d031907609610108541c1d07580c4a000781500c500d40d80303001080740b10740709a02403e031300e2450386e900041000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 472940476 1250 472939226 472939249
    0x806090411040203151903080a05090307030203030403060c0206180c041d060906060f04020408060109050417070c03021320030703090501060b0702210a060b0d0f0f170a0c02 76
    0x81c4005500c1d000038031510385100650040700e920f00c80c03460341d03203980003402212881c0244c0d04041000c2c1c84800c10204a04406030341d0f0441d4103240440d9503401560000340342203001d41022b0f40c1800000340010400c1010b41c012074440c4030319026910296107040da0a00a07080d982541402c81c1c100c0c08482180d841d142e4080405090000e00d640038001d201610a4603200c030480d555402c86d486942030007103e21b04102507203203a41040f00c0540c81c00303041640c00c540b5038030188205034403c0d403501c000c1800c100401450f07801250500512603101c0c0d00c1814004c00c040b07400c3c8400d0b0300900752201404034155450083c40c01210103503e03032a403c1c0040c460f04841d42d5000810340010990f40b5982c03180008c03400c7c005c0340002d0400006454942d011801000302c0b0f500020701c80020b003080c070406c25001746004a080ca0b82c5903080340300029446040408502c202108210040071021114034190401200081c40140940182041294070301c441c1c079001c00e14840c14089501003042034400a00601d000500f541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 472941726 1250 472940476 472940483
    0x60305010f03150b150d2a0504090b010c0b07050306091003050604020d0201140c0a020f100906182103020d020c010c17040b0403120806011e261e010806040308060904 73
    0x400c4285402030810190440c40c0030342001a01c40302c01c0084600c00d82c00116612800007032003074021f120124040d02c3c500c1280b2800d0b000f262500b0103d801a1b010f950321151441c2c00000c0310400d4a040c28000b003540d841111214480c51442c3c020460311001450680140c0341d0080040c001078071540c082003070301204481d04a04001203038810042d881024005080f0004513000200360060b80b03441000002c881400c5401d0290781d81090744d1414a41c0032048000b00c80440c185050b01303d0001d599450f41d1407e6030810351404034441d025461840b50b80040090280c020b900f5a114a0841c507002c0f40c58072846035003980014403006286010440714034440d55541c06801c5000d26103a035848036600705802c6079100769601420285c00004080d0003040f030b19800007017440d0000e100c940c000b000602c0040e40078151070070800206094020040403460644a602c0341080c1c013017062615a000034040f5a5104815818140c24000025440c6c000502140159815210701d182c0d5554001400602c0d1001401034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 472942976 1250 472941726 472941739
    0xd090609170a052e15050907020102070501092a081b120d020102030601110c150901030f0905060907141018030c230f032802031204060305010f03150b 66
    0x34000a04104540200b9904c2000c0d90803480c40305000252006808075030100c4142c0c208204031103c580100b00400a6030307030448142510380c0b100c50b4102e00901800200801e60742c0790005070014043c4001084807003031460007224a440c141d40030740c0e1180040d10f10403841daaa102d018502c810000d094000c2001c204007a00d221105000070220700c1c90100d402da200800f50358008240007407946e1000481000b2070b0352600a00c20f541c2e140d40400c1c600ca400c1c0c0b81d882400e16001c0f801c10b105038402d40010b881240d80c2c8005000440081c101261920002c0e64150391900c02c1d030000050040001000c0a00004010b122104010500c401a00d0301606035168450502e4100d20210002e043ca400e410080c200c150741140c14004a01035048620700020b4040d8852103881a07100340396600022001c0400d0703447c04242140e03010404000c1040040e09200070740c10b009810080300045d0341b00340500b0455182e9942442541d07650200701d0b14400c1d4900000e80300c2c05004503006014002d6030419130110324003a061 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 472944226 1250 472942976 472942993
    0x5010e0d0209060303160c050a0f060c0204090305070b0a06090e0a0b040219030c1403070b070807231002070b070305010305030708180409110f010f05180d0501090803090d09060917 79
    0x402d1940b401c0c891302118031f0442001c0c01c0c80701e410603200d0300020300109440030700030340c1c18100090009441c4140c0288219155294501003512960540304155071000520146080c01c41e402009050580644000c06103401301a46034917900103912030103d81c100e0440c0c401134642d80c00348001c29441c070340d0b08010045400000400901001c41c8400100501102d800c04030007204100750500e0301c0c550104001c0c03c03050003100d0208000208480802c1e6110a8594810f00c00e2005144191051030750811680561031000c414071130590014900940308900c8680c10b41c0c1d034004194100d030b500b800064100e80c000c1c412400040c0360000101050400c0d41580841050000d00180c19a0242c0004440000c070403501580d02e41045588000350742401d08201e00d09841517a4010b09a0044800c3e0b030410441101e180e1880c0e41f035000d03140c030000d80c0000090182203403a04100d10305074004e407140c2285104210403054568070488801c8152010b99850b20402480d000500d000c258426242c0b06441c040c0003013 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 472945476 1250 472944226 472944247
    0x110f1f031a030330070e010f02010b06040b040e0a0c02060417090907090905150906100c17040e0117030d0209011704060e1015060f0909230105010e0d0209060303 71
    0x40e008020303c18028049a42c1c2c0f013004402c44030341c03680c020110301c0192818045090b070081c880302c904260030f1070b0003000401c006504a001d0904503440c00d801890002d404211a6280c80041c010388400020482c1151075036400d201c01c0f5034626054800507080000800c0000c1d0f580b6007100d4100b414580c01e207003420540d0000a81596060302d9000200354001001c000104c00342c000c1075070140300d0705080c1001d2040c61010441e40304001700101d11403100240002c60180c003616004210b50341200500c0c00100e690f056201d03181e4401e014050a081c2c5d520000114240c130408ea403180c1f122054059401c1170201c0343e00601039045a480541481001d000309030781c00441500d52803196016000204240500300c064501b0410f4a01c102290641091b0448078128031a4003050222500d070710380558690050780e0f044403a0b8040d5001842c1d0749080c03000c00041e0304a100400303900098510701c0754045036a43c10043d1150300d0740c03070711080c0c000968805603405440c151443c01d501000c00350680385420000398 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 472946726 1250 472945476 472945483
    0x5070f170412140406020d080717010e0601180e0402181003060924052703191112070203060c0412020f01140c06011a0306090a02180a03110f1f031a03 66
    0x1000040141c3c8440b40181c1141e502042a81d08800d05091952b001d030761040d111b11021a0500501045502c1e0001207811a40b18418182c0e0380c40141c01e0391078080380c9582d410381c4608401d4070107038882d408803502110032a144060342c900442115840030303001c51442d500e510241080c00425101c0002c65104054001008281d00c0344800d88a080094103180040321000010220701098034443c81441540380d144000100316a510100111900241640c00f00c0032220070b1040070f45901e2030b0151801c4c82980032180340242031100c0c030071800e9814540d03628407646120b000b90300c0385282c04103103840350300050708050f40d0030601550103141c44144110b80300703500d043e40d6103d03039241c40c2c181e03111a00401c8005101d40d4040c1500c6805181640796051050002c0c100c698007900e944200c2e5400601c4882007000c440c40030303007541c001030966514959a070400302c1d0721418022040d80030300d80e66084c40b07035185845000d292030610701170206000041c0c0c5079421030081c80c001880200800d940300c210081581c082 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 472947976 1250 472946726 472946729
    0x9142d011e02120a0203480c010509031306050703140310090b0406120b15150c010b01090605160c0918051c020a03030b0d0b040605070f1704121404 65
    0x1a00141e43c41d4280340140040c560014256803046206006101310a55451128100702150f04802c0f0242c1d010080d0b81c21806003080e200321030a010500900d501041d140001c0c1c40203218040003048165102c0189946074440d2440352036a0204420060200781e01800c09003000300c2c084e1502d02c21440070700683d910f05900030f8542030210301c2d12803010020f00c1a0303801503010b144000d44051150300c1c030f0401c1d8040e8081b11000011701280141002030860b22a01d02c840b00110301c02403102140640b00704060550364450340c0b920300c0c4c5500b07210520005500590861040780d00a81d105031405400c400000e00d4140c40392340481d400c407440c01e00044c00481c036011b6501459140c0004c07510381050341c94500d140030f0300700030b415a0040010b10b81600d66600030510000e40b41d01800c000c03c01d06200400900ba1001d4200e000300300103810b000b4402448000c1d84001d11420490700d0342d2a55561525003511031a898907550b018661301071002500046218001020710420350800a2548084103548403264219 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 472949226 1250 472947976 472948031
    0x2010b13091113150f053c121b01090909050705100302040e01090e060106090609120212010504050a0209072d050c030d0c0206010611060723040909142d01 68
    0x5c105090105240402e400c1130586284000340b43c20881c1299082c1070141c0300301c00c40b904506a00458200341d1940a007158506000401392401c2211907000c0048080322905000d00040d0124408108c00c403d9120b554955078220f002003960300c2c46c0c43d04111480da451040caa0030103409100009040352050340d298041c12218402181c844d2224942a1814905900040411102680400801e80c0100c52541910021444060000712030700120703082c0000085207445661a00c01004203101001c203281d1002c920841d4000d03000e45030600100d800180c040700620b81f2085010300d4145000306201c1c4544200c2d8281002e40c01c10300070007500c5040d5008500c1d003003806900c0f1011070031011b506000c62405014181050402507202406c0381d5982c5000503d0070003403098404030140c04c0503401007500645900c08201e56500c036120f8640e24050216140110388500000b0710700281080046a51a55074074090002c050541c507030001e20001d11110724100b420344d542e5121140c014502031040018440c00d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 472950476 1250 472949226 472949249
    0x60503090d020309060f0a090e0a15090e1f0e06010e040b01062a03141b060c03060906012307110321032409010602010b1309111315 58
    0x30480501810030340740c0100e103030842d00704001c00b89099540301d09982646000a00e0280c40b00765000d8142d502c8551600021100401001003000210303083e005400d40e00700f0f906100c140590390750034580546803031203640a001e420490910f0403e900d1000010402c0c1c40891000c911003900013003142c00d21000303810050315140d1000400c0240090100c11500604880c6403150106154917545034070004990111010080006200001d0501c102d10503010f0b00c00c610007281d80d03104042d40b100296007000c4d40c102140d008403800603080260b84420380344900c101070b00c2c03010035945c1c8400445e07142c0b5410360306000c2e0002111001c00482d0481c07002d0509588948510980c107100c8104040c9016030039542c0d540c85928220785070409801c80c0d002ea0307421400d000100209803490b8842c2d44182060a5003040e04200b03500000130304607a05401c02d16614800780c40000800301c0c1c2e0b20342001a1012800050101c680c00340c082c40940c206440303e9401074a480c1400a40340004041d50406001c05500140ea1804d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 472951726 1250 472950476 472950481
    0x70f0b0901151a070b0a0e010525031e0203091203070207030b01080d02120a0c06020c0a0b010f030c15051b0604030810030308060409020109030c091406151e090a060503 74
    0x1001c1c00044400b82402c4281c0341c0faa4485003010850130311858800900030f000480101b507582141d5000002a08039103c0207010524000444200d00006540c2202c0b003111404045030100340244111040304001070160b40c1c0112030600414041e510240101019200d2508940307403460320b64001e0b50244c03003191702414070103285040c4088901810382050b4401d801600201d00300b103030002642c01d422000000c4803901c4201c0c5c0507007541c52086001c406004140000765580140300003245403002103128165110345070b40c81da65801d01c0a04140401082800001014002900e1200ca17a0115040c14500f50f460302e92003d104030000c3c1d030b240f600c02202e40e014105220826410800d4a5030000d42038000c490202e185841c020070465000c8c181c180642c1da11105002564420311a20300034641108014020710b9445071b020000700038480c9102e10a5941502141483c600380c03c010341c26800d03503032200b41044118048004119109002c02e40c082c1010070007108aa122101448000c22150f22202d4592 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 472952976 1250 472951726 472951751
    0xc1b080a032c100c060b061315030204060518031905010c080c250f020402030c040806091207020f0a051306030506090303160c1502040f090b090603030f070f0b0901 72
    0x20100960041007540003401d0300c0071643c0b40c102c801d030100310240c44d04015a031150300b4200000d14a903510a90000d50004e03180f6401c80c20f5220b00700489440100200382ca582e076240c200c04a0080e070181000240081016a1241c00702e050b070a66090f00080951b20781f000308540e002e0382c4000e0307890116240e075140d041a9030883d80121002d58001c02d080c2c40c00c0d2809a8241e40c400072030781103070316000c0c2000c00008074409011207480b004040319070141c01117599050040c117118040d0040c0c452507485105100000310b4160010400340307240409400740e00c0c181403565081000c0c0074a4521099082003400d0310000f242e580d4114440380a40703009400103100e40c15401c4c964100310000341509076a42c020414481510a541c031121040e10051900862582c5245412400320880c014408540d80c00400c001c1000c1c020400307a032044a600490421401c60100244030f40c04000700c4002d5070540050013460f596411400082000724421303500088010004d80d2045450001a2100d03500c0c1da550b081000e114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 472954226 1250 472952976 472953017
    0xa060903030b09040209130c0b0f030103021011030f0309031e0307020c010c02090a020a0c0b010e0f070809060f0912040b130f030803070f030e0a03080709150c1b080a03 74
    0x1a0202519000300f03600e40350300424100c10020342038420405114848209112102000030003421100c0c0301d482d522160002c04200c0d9810030b000c1a48925010b1205101131400b03aa0320b0344000c031405014606000e02e1041c45a1260402001d4481c0c500042100c02024540c400e43e091501101d02261a200e0400c036000910305030f68a034505044c0040300c0c40003000340e07840211041e071201a1500245e41d41e15101400c51329200040402000042c01400106d00386403451642e03407040d280782d84480520b95442e03400300e40140c0155a24000c1d904484003142c2c4035401c0707003a032039446222903048405090565010603256130003640401070340b420200c5d4440c01c1a401242e24001406c0ca21045208142161100340c01c511003d808001800301c000c0c12a40e02e50302a8001407841007440c0180e03000340707a035814094000403040380c1c00d02c001100d02002090b0707102000070002e00108250b965242c00242c4d65910240b502001880c0b6200d4640380d40000b801180c10010b05800d9031082d40c1e401201c80403007406108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 472955476 1250 472954226 472954241
    0x6130308150102250308030a0b0301050a090809090601140403080904050a3c0c0c030327110612010b071e0f0206070f02031e07080d0f110705030a06090303 68
    0xa441c0a800340e8000300d0703a0000f03084003604860300c04904c1c0909424003405640700303076920003810705401000b00480c017807060380810381c545002e0f4001c0c0a0380d42c3c1c40c171034501201c1c0d00c1c01d4020400c403410310102029040c00400c280e40028181030010f1701491140c03101700c039038100d94011074840c0340006503812241824000c40e41c1066202c1001d116102a14900c40c40c041091180b40d02101078951440070124240f50002510117120304023000300310a010f400901074420b4280c1500440c2c01c7c0100e0031302c00d5500300c2d441d0703102400e0181d00c1d01d480c500540d6a01002812448c0140c2d1100c028040c0b8103011071b603820124024003003c5e041d80c1d44c80304140790220028019601418402c01d503100601c0c00301340414a0801201c0e03046920320b40d508180e2910480b004000d601c081e4040c401c100c0010380035242c1c0308100300c4c0c1c01c110504850754241c1c8d54040c541e0710868519144e00140d0040b5424280501a8206022450041064075031668403440824509115480d00741e40c280e454004070420705426108451 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 472956726 1250 472955476 472955491
    0x1050903130f03170f090d0303052d010612020c0303091c0f1b02060c1f0f050c0412020622060f03140103032019060e0321060406050306130308 63
    0x10403245151543e4a04c504441c0010120130300c00a001300b01c03405801c0484d440d04600400480005110f410300800400c000c98150559070010025080c0201004929921307145240ca0071440c1c5030f007840b0040310036240c0a20039407082e0350244003540d0389080c1440070b144150b10000050015010402c110000d06000146ca0803d000d041018520361039480b081c102c902e40b01c80700c200040500513201180c4a0f1040e44020080c40c01100c284040c050081095690302200054007032180c074100d02c203007208030f46064900307582c4080104010004524040c903402d80070340c0002e204504190000ca50350100780000c2c082030074190a0443d0034480250040f071002c000c10490328040142c400b01141c104418032040c040901480344100034a0f0700c0301c489030103282c0790003c0c013410b6640741074000e0503803440d160a1300011203e0a0502c45039824405000080d50b0758269074140d188000c0080c4640c5a0130900d000d0b060a03082038a807800890f080e182000303094003c9131700e2141100d8102590400600120000e090340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 472957976 1250 472956726 472956749
    0x70f080c070e04150903110f010b03010b0f0d171e1903021603181706060a210f0809060f121605040315140702160801141609080105090313 61
    0x21003c079120012000e007001c0341c500001003440c02c0e810142c60240007400300950520482380c1c409003012040d044038449000503002442a519000100034420300c945200c0f9412030000c150b803201007914003603651024100b011809140c10070046550085440013407000f00f410300c000032410069010a044550018640e00d01141041d441221504060040c00b0700a8100041d00405034601180c0095030710042071041d09684a00c910640e50a44494049420034030940c1d120380001841400c180450501c0c2402030301c44008400700c0e81d560b41c100c0010480035a650f4100b0b00000d42e45031110300007804882907015003151110580c4c00503400018000740303689480c070401084a070525130080156000d0300c0d4001c01034041c010030400d0502c01083e030200c0007600188020184806150046101c1d14400c0c518110b569000f900d80c6811420380b501203000c95204429400020400030b0482c0d8940c0e05c81c0c80030729285c7da803e03560303013402c50070740d0019102c0030141d4000103540d181020a01c11000020030200c04031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 472959226 1250 472957976 472957981
    0x5040609050d110918010608010b09180d11030c060a0504021f050405040b0102030903070e010305120406050901140d0603080c012a05032502030304030e040b0f01050d02070f080c070e 80
    0x41c031501080800300d450084030250041031800600b4002e2998116000000701f09490ba01c00d0480d0107403060034440d078020341401e8081003000c1c0034401f054509050310710060241d501447d4040311407003050880360305a804144111f6180c54401d00c07911b070148500b0756011410b428580100081403a03030f185090304c5c070301e200807240f10503640040c103a808803101142c001641c103070402d0040c1c3c1944504080f080d45400b0b40d05010030102c0070071040341d060b280107008407220000c0d80e80511895110341e0050801082003070000a406611a83c0c00306000000211a20304100c043c0c811030040d10b50a804c11908200c0c0070035202e89002003485070700b601a50760b401480e00c44000c0141240400c0102c8500001c214001000503c42c8104d40382030010b087c8400b030000700080900500035181d4205980c2100024401140500315261901507280c0311507000703258080c22200c150065131542c2c4900000c1503216024080726021611202c2050b042c02d000b03540140d50b400a01084500300045d60300509141000380c401d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 472960476 1250 472959226 472959233
    0xf0d0b1905070e0901034d0d0c050f0d050303070f0e030d23250c05100219140a050a060501080312010b0a0903080313031e050a0e0a09090305040609050d 67
    0x2c44d0781180e4020380b07140c03000000403a0b6a4020741d102c0d2840214600303850058a60014241c450480700340b01e840280c152021440c00700615204100d1000d00b030300344c1443d4107105500c0c1418801a901c1c070001c015180040c555502d09045410880c0e6010200d164190043d4025401c03600801c46e40390103c028151050442401030070700c524030341422620711181110510451255402c5405041d09959031040e42c00040021310a0704c10f87da0000c0700d0703030200c0040008042c200040c14042a03a10341e000703480700421050040d106110441000d480d65904200310747c81c103107428131641c00358038098030107451400ca080c200b590a40d0810f83c081c40c41903000f04404103000481c20301450640b03400c0440c5654070b022840b0201d0309502250809081c4220000502c2000080c80c1100e110491080c0c03104901305410024440040620905240100b4400c0042c5521203218507114003250100600c014a040e454401c0d041c120b4011400c21004034000040502c046a0004d445600a2004135822600d644403a07a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 472961726 1250 472960476 472960489
    0x305090c06211003170d0b0307030b0a1e150305012304020111070504020a09050319020906061b06010b030106080f10030209060102190803061014090f0d0b1905070e 72
    0x21401492812000086800c0703000000700320f0011a04000750008407080008071400985c000f00c20076440b5440c05090010360304000c11300c80304507a009044000300daa00c05a11902410038280302d00c00400c036149250203c50203510800da06040c08446148402c1d0442c50000e0842c1e904e0481049056100b49994540d180c0d00d1413041d034826428a4074908031100003c1281c0f6001e400d80055900500102e45800156400a4800e04582c421002c0358440c0d55103515140d40700f00c9030507019403c09135130300c00075000741031000c001c12800310501c0c1d028420407000b41d0110b003825070070b8104034003540c40080100400c0d0b07440310841d604002c08907020b250908140c181c19101da0701c03620000f0300a4103082c0001c2c0461b030003444408607408440e049c907003c0044920b8108076560045940354803901511014081c56403181c0161240c86c00300c00500d031304d0169014108442400d00b000080c0c1e22a0b21092800c00088042e1842c500840390001c2c0c104203011000304803019200d008200303008004151100d03503a02d03910b20 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 472962976 1250 472961726 472961767
    0x108100c020304050a271803031406090109050c09060c010f1b0219060605190602071a030c13030f06091a07020a0b07021207031106010f0503070b0a0c0c060305090c06 73
    0x60308a02e5044081906d42001600650111441d0710b103058a0792036040c0d01000c2c21003001d0b209039006c05c040c00148601c541c0c0214255403040d041030204e00140f01e152001e50050303410a040c1640b1a08000600700054aa036000549030034082c0d450b90030815035200f0a004131450b079540d4444000c0f0101000354001d40e00c89001c0300c905c1042400240c5403003484603d5101d1005003d0144c0001007108940e4a08035072220903204402c01486103140004030142e2410f0307218403031040e01411504e1078907038003203048040e003094030b000c00c0c10a21502c3c0000001c1b11040b503100a10302c40d00c00456440000c0c04e00d4007620241c00280008440200200031601380e0109000509640c441c1030a4081d803500d403002c038500303680815002081400010b00c5010301da0481c4100d804004090102d4043c1ea07207072078107000417070700c584901ea41540c0b003038400780036000340360f07014042c00706052500540c8000c040d110084403224503489000801d94400038403420400a200044c800c0300300350342c85071800108801138245544403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 472964226 1250 472962976 472962989
    0xe0a02030c160602070c061e080c0a3f0b010e01080609040c15030e0115031a190519050a1e0b0609190f060306081b0f04050108100c020304050a 63
    0x29402c401c01000388940c151005140c002545001d095140c3d0b034082d08080340e0b90a41c0c01104002e181a01c015449002c11a2244841c1611142004010070080d07403c807000c3e02c8105550300503003600d0325044000d0300d0701c3c402c0b05103403000d01c0c0e0942451742c1d811030031600500f44160402c501052002c0260741c00050240e045102603c42651954441c1007001d68566103400009403c0c404d000851a2680e064101540202a000c02089609070800b03a103942800b05107c0100205008801001071104104005034426180815100600341b0300440f481220780c1100d125501010400c41e51440c11482d00c941c540c4901c840100b007055030440d00d030300c005000c00040078403801034981a24541d291122810386074200300c054103910444400040c50801141540614254504075100005900713100e405030808452111703000d44412840e40c00e0902e06a9041d03201c1131b4115401001409680e220b91003154000c1800801a0410303451400600c0c065801c8290400c0c02c640c8140400e00c4159141d1a0300c6044602 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 472965476 1250 472964226 472964257
    0x301080703320d020c03060105090601030c0912120e03010c0c060b060702030609010e0d0503070503011809080d050f0a0204180506040e1b0310110a0f0201060f0603060e0a02030c 78
    0x40154103603241101d0b001001140e41c00301040036002d680c00509140e0104160302070b11001c854000625550715070905c10580c4c0158a4008030f0b6495000303a100a040c04600c3c90801500e98560401c0d078004940ca01080b203c0034504004640308642c03115200f18428800c800a201c4e010b0282e00080101000160181c282c56444c460a12281d543d0001c8607407080c0e018040d0385040c07400400041c020708020461070005d018010101c0c00c001e12030012a0710965a540b03c5034156420080c4042c211075009410907078040d910030100b130101d075010004d0070703030301c5803081020446181c01c0b03451034580388018103202109401444180440780001d990308400c450407000001d050390300d0f0000140604640b224102490146401c2c0302c8451501540d00c1c00c500074150121445c070030188541c8802c9400c24100c41c0744646080c8400e14040380b007500c03000194041480045219911007080720407a1074282c6c0210003007959080d04109404c00405025444560090214210728190500b102c4510401100440019 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 472966726 1250 472965476 472965503
    0x4050607061a040c090801050f0903030711190b1005011d060c10090818090c1603110f070f0801090c050d0f150212060301060302100509040609020307081b0301080703 73
    0x2d03901d07504408104001003091108440d03018001d0f00c2a602409207407541d50810f00017400c80c0820298a0f0700070701000c0c0c021031441da94180c084904200d0b840480c00c035809007815200c0211801180b8081c1c4034041c414a0845040c885c3c100011120143c1c4542d050054103000c0c1c00b000300402c03c802c00214000e84c1c06030f0ba00c0e4031200406080070754501741c400d00d0510300508042404400700c0508641e0015100340859500c00070b08204400c0f0044840111402040100c0c0c0701d07007a5518002101b0300d00c00c0c1806280103200d4120302d030900d6010616511103501a0b101080080810074081d802000d852008011050b215140c1ea5180401030080d070b4014000741ca4820100b095030080e105045404c072104007030605003104410302950042544c0000740200c2c001180c5a443e0620412040b264003d20608803021041f0b425512034128a1111740c5c0195110701c005901c0329a400103501c21921641c40e030403981340c07081010741e44000607250881020410300060140c440001407280540342c100c003d41c135100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 472967976 1250 472966726 472966751
    0xa050d062717030f0a020f07051b190503060411030a0614310b13020603150a0b21040c08030a0e040b0f030a06020d06050a08210405060706 61
    0x9004198650320329401c2080c503001c15546010511401a108889042e05a840c072400c0a4180c002036656212a15070300022800280e1035a000b01041c0c45064101420000c41c0d403140ca05006107908444011100c03143c01c40100d02d090040d80c4031030b07030756141c3da040c00e0360601000c2581c40c0b02c0100014107508042d242c607503043c2d80401c184102260f0100052001c00c603404841e2200c0720007075a0200d06800300c0406840403409840544102a04040302500141c2990309c90080340c00300a00030081c2c0b00384150890000d0b8580320011881f60321469110502a004c0c0d800b44030180c001c50740000c4003000705011400c540c1e1041c10707941185060011f03500c001c94a50b410503e04803142680640003074440094103201803034101c161907008040881d81007103d8031a8405006400c0c90b40c03070701140c3c507030400054a0300007642c0c1d502030701c20207080034000220280c03210086000340b032030b81d0403c1c1c486900150740c8010700c1c021f908a10703600458240105003010b151601048840c000d5540040105032107602d00c107282c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 472969226 1250 472967976 472967981
    0x30109030219020415080d0813050d12021b07230d03111009060507090602070609060302160209270309010806010804020d060f09050c060705030403020118030c30020a050d06 76
    0x80c20f140c0c0402c420200d58500c001647c60902ca6007000100c0d45480024a140c44030340c0c40403084a030850080c00b81400c03141c1c0100c843d14100c1c0441490194244440340802002a0b9500845000c010003480d4041c1808090301d030403400031003031004820101e510010107485442d010700402e68103090441c40300c104801d1301810910740c0a0040c0c0f01c640b4120880c0c4c01e0107590f4000340d01442c1c0940741c240c1d020b502c81038200c0c2c68181c81d000304008104101d0041065903c01da005011501c100c095107002c14140e6800500f01c00010b8038800c040c88203071040106140c0103101c0c0c02c5a240e40d004011071416609600207060302400170a03040c10311140d200045c00b951215140821015031001d410080c918a440d4108000c0c1100308054486120704c1611240a04003101180c0c03029401400642c01c0c2407030340e07004441c0c80f490b10400a80b00e168200002002503190414031307018158517180541c0556011412407040d05400c1024032001d07516641c5000540c44800c0c21109075002500c8030502e011190034034101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 472970476 1250 472969226 472969241
    0x10311061b011d16120f080d051504201c0906020c060f01060302030103050a0308091005162606060c16030507090f0513060203130507120b01151409010c1b050901050301090302190204 80
    0x322a08140030000ac0e40e22541d0b4100502904603000c00c640003080c00007815050302d0f16000c040581c0c04114036481544c0c00c00c80c41c4441c01001b000800d04603200c2c3c0e503400c20b076082428000920345c000401e10202d820203214160240400c0d24003181150b2440e10303001d82c3c401c105607000d02030282000200d03452000601c21403404c41c994900c14482c0d4100340d80301075990a010550038000424040c040c6d150010b0b000d1280007401c19034881542c06494440c2004030035449290381d05014400c00c030003010446460007241d0001e43c0144043d004052500da00e040035200c0a24000707804078548810400100c525100e0003002c00c2d009400180c59554072094081c040c038413128050100d10408500080759200d6a94255401c0d20070710384c084a41c0da80c0c0d07401d4040003002c0001c59000c070700b0091449000d61011009810906ca0501d080c2103482d42540310382c1c0c0d140d04082c0c101c0110304510f4000b0710607070624401090040c401030b002007183c200039481c001d440308030b401290b00e0011324000d0048190741c0c85801c54031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 472971726 1250 472970476 472970497
    0xb01080318060a26010807050d111c0b0106090915051008060105130b0c010c020304060c1b0f06020307020307050303270409050f061905010311061b011d16120f08 71
    0x85400e40700440c100c580c4d04003445102c8061041c25800300307203414404264034042da48051b462024501007030030480d108400c49051142c1845442d0000007058404074094000d0805440e600202400d100ca054140c8510f035254144c81003d41d07134100026214000304410030319141c03620040b161121030040b01c81380304400e0200e203071007155500032494800079402001602041c000030450481401c8050340c60b401a88180401716840c40d89110104050464104441d04124645580552140449042d0600c0c9822000c01a8008150301c42142000c01c462400381404400231410103003584010032400c026a01120421440814011a41c1d10380d0b400c84550181d02c08240d8100400b07044429130f84a400712100a201072200641521500d21485594183d0b5040402501d20280c01820301c2016841601400700509a05058600c2440c082c1b0078404204009d0860100300380c00d40e01707414503011302c0c03000c4e81a1070403031685c2c10080c00503c4640e01c48496842401880f01d0350490409103500d004a10845 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 472972976 1250 472971726 472971767
    0x5090406050303040f0915030f03050703170a0e0d020f0c2106091f060501080c091c05060105030d0203040e07031806050406200913270b040b01080318060a 68
    0x40340d00c2c11703019049410f03200042010041203040912280c61008240b1000d009800151b080030701080c801e400411450703000e41404003601c0700480c640205900b00301c0b8407220250340d41911400d2988180001100c1000d1480200031611080b15540d854915805ca01e9100b01400040312080d414601d2030342d0805281001a0b0360039182c00c5142c0d603102e00c41c10030280c144403c101c1000503810000c3c4590010349006a407074041075503646c3c01c00c0c80c10354410403d981c0c1c0318441421100400d00d808050030001e5118901800c12545400c0a15140070680d0318998155001844181304941c9a80701180e4007002e079180c04108400040104c61b540c000c462406800d0744d08000410040c400c207500b02500c1d0003028404c40d41301c400d2241c00084c181c0100703035030103520003114240480309845070f4200e440d4120030a0031030411115040d1306145040041c1030b040317920140749030812083c003c4c0f069240b80127060300c802951070840c041040034201c0c40c80c00e941342e200e018003049817135400344079241e44421458504031b003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 472974226 1250 472972976 472972979
    0xa030f0e101b240501061e08071b2604030201080430020616030612060f0b1c11030f0d030203070e06031305071e1a0f12040302010c080f01060509040605030304 70
    0x8485043d0510f1400441681460000901d01c0d210b00d40c200b5501840d4075004c4000072401d5030840f03410030301038043c1c001c00400f410300865a0540d00582030010740700c3d003428411501d40a003400f000c81750803030a05540e408248000c00250342c0203509298496803124520750780340090b01c0c108807920a000142001c1e242046007441399160005200d9024a6000c05032540c0700011010403130688485008400c0c031110003c0388a00050030300d800c00c410f00440b00c4404903e080c20100400c42140d000140105603001c0b50415000f40450f40c40301105040060b005026480300103143c142d5241d405041c604200f5500100243c03417903100e0129240e03850001041160b603420080000383d110250010141d40d03d00030000300040c0000d15501c010040410079104840d9203152074042d800e80e40a0049101c030b0385c2c7c820050091050421801000500001c444580c20303814241002030031500076000c10302c10300c0411402d10127903081c0000c0302c6045480629082c2c4e80c0740451800700380030349040d81c011605480007050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 472975476 1250 472974226 472974263
    0xd02031806100b1b100f0c080603070305060f0a0204050a14040f0b01120e0c04090606080f070302010203031306231b03041a06060403080403050a030f0e101b 69
    0x49200940c8104400c5944030b8441401c500381c207416a124903083c0400801c11103002150030941c0294528028040e210f0710241c40007144203031502654071031410380d540c2d0070301440030360090411034102000360024030600d03003599074007a41c8080282108000050440000302d01d911560100d0340a8903002c0c0100003407131b030765195070803180c1d5892841c1403042e802c103800315100e01820310411450800c140d4400100c505c01c880414020032131102d00c140e140c00b4040b40d4006548480c003407112142c3c0301c0c00b0b001611500e81803590b801c110b2011041d0500e41c010440800250382c2c0041030700e030001c600e0404060170407600d00e8804020400079110804544031214014070304070b00c032515244100384200525225005090086050388030440e401020280c0749011103140d1003801d44e646900c20005002e07649066101c0d216289103420590048a0320f038040044e40702095403000c4d1020091006041c203441010070a0000f03540d49824072585000c01c04d94060742d1300c0322030980602070081e6030442e1210000b00035042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 472976726 1250 472975476 472975501
    0x418050103120c0201090510121b03180c09020d020903010e0d270e0411130204031b0b07060c050d0c022404081b0a0c060804020301200a03110d0203 65
    0xc800c2d07403508a80c2085042c100e0285a0702d05803075505944030700c049400c0004211007981c1c0207220004003c426403034268140114400c0000002c400c444000c85c800603408014150790070240821250780149522a0000d604141c0403025203040c1c0c02c0150b1614140d20940c0020702411039075503803560030b16216800c000b901180358500e60300070755105000c801e003010300703103802825105000701d2400d01e0820410001800c800d0480d0010311a907070300501d002030030300010003601401c030b00e4004c5558000303401c008002e41062190750614880100c000100e04e0182c09500500400001034000390b21500d200b1182403054044446602910303200308021813161000031b5503104005002041800f951100c1088082080041c901c11a8411442490f1050601d00c00e070390003229401d04d41644c03268040c018001018030403c00301a0209980301007075032602e4010182501c000080c3c401c8070052181d52213492106a600b2620091103030704012420128450126550303200b00c1040c51280c1e4408018070481504c2c2c40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 472977976 1250 472976726 472976729
    0xd09030507020f06042607080f03030a060e070e01050c010605040510090509010e0d180e07080a0b0a150f120504050604020a0b030c0a0c030c0b010f150203040e1b04180501 75
    0x80d200300d103000d20800e0600c444d610540c0100d404499245901c0030b4610078450b1548107680c544003d0b03c140f140d807803060074a496030074030b0b1440c00790f0004401c00c48840c607540300d104001c0141c644030400e9070600c1c44014020618919100e81001030000e143d104090307003504079900a10001c0c00420480c5002025130a0782d208030701994281d9410b00707000c1003186c00305014030f0004407851005400318284d5a141654400140c8020000c3d08200c0e9100081d5820681e000c1846105151035400c0b180c50103407105400c5500d01141ca42c450301d5201014000503010004204d180240f0f401c056045409011042d82d1089800c0310103200c2c61b040c0304c200010008013052641c0100d1003030700c000b10300c90b44a2695120500007250b01140c07404003404400c4030b0034812008064814004e0500105500140e103859514100c00d0f080300d00200c0b2164010041c90a414020201d40200e52000c7e43c02c00e41403002d080d00700400502021106440c0c02d0b008154100403000f202d0080804821064101d94001e400c3d00250509 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 472979226 1250 472977976 472977979
    0x31b0b0c072105042c06060304050a17070b0612100f060b16120801060806041802090a06030b010f0b0417030405030a0507050415050303030f0702010e0f010b090711070b09060d0903050702 82
    0xf01d0b00b5841e50311818140d240c2d00403c550f8171801c020b9480d0000c0c881c0729040200b0070fa49910901103060003051032401c035640300c0080000550754440b11414480300484010349243d01802404225404880001c0340481380140801008074005080c0040d080c090607654000500b00003002403a03200d00c1a46014450207540b26084001000d140c00b0030a0340c619500340300c3d5038046074082000409503d0310b54072200e041641410044c00a90f840d0b004200100307000c0354607988003690b480d024400d000d0340010359801414190801404141001c6211000c0e000d14400d1285422000608951402042c41514003918001c1e04444980025081c559030b510706502c1041d001e5840c000402104e80440040c140a440c0c024004510716207a5801e112800900101141300b155030307610072044052000d100202101100800114030002c0120410039003990141001c0c052008803000180a0103020880c0e504507050901790b10303218100c00000c11030610413007191001003460890741404054000c006007202500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 472980476 1250 472979226 472979249
    0x806012a06050a05270a080706050414120f03090a0b1303120b1e21011a1c02150c030301060302030901051e06100509060a0c031b0b0c07210504 63
    0x1c950b12480f080b1842610324081c6549014030311003500c0c1240c41844203c4805404940c80e21050b501c40e0080b9402000c0c1c01c0703d01036124030a21061012448000340d01405c0c0760007608042528400f10051841030703c51400ca411000300003d8101c07103050102214580e040448001d061a0844030b0912102c0503000403000300c1c003041d48200142199101702c1a004102404400c0a0100a074181911540481c01c1c00c1c0d002c0701c1040182000c446c410510f241902d400000820010000307001d05a42500c0302108a0150090503d11800401107503468012581c040d06c12001071641d2410904191081241450041c13000000009070180e06500952041c2c01c2c401c02004240c40e5401319003002c3d032050f507070581520781d00c1020441c180f0781055410301d41722043c01c1031441c2501080205044c1d41050107100046880707081d0190900d9000b0395000b10103008041e01103a242d010303559101c56260041c0440240e190086240d04c104400c5003030030400d01c1c40380f0203005040303e0b0b00c181c0284158003a004805030b080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 472981726 1250 472980476 472980481
    0x50f030a0809070303080f0a021c0b030c010c020a0b0a27030b25050a030605040e0105010603060522110d0212070f02121b15101a0403080306010806012a0605 69
    0x40b40440d20800390fa605544000035900d80c81d0703072028a20000f4000c2d5003008c2c2d007004604400c0080800d102c001103000240810302c1d0070003004050800054042d031a050018151440c00103a1741c0002d100240c1d680c00b100191100e0b8800c3c0111820007114040060b20b17070345881c00340701541d020140d42044138031600b5810039070f0ba0b9400c40954503079010302c01e074884030070302c0259031104c3c034060300241922610602d000140503564000180c1a1810058035007000e035510301c0180583d03075040c0214030142c24144c0b640d00c20080b540c884045840d0401d8a8060210fa551861950a0f8081c10868003211014081552200692041948941d20607039403003020410b00010203044031300104000210600318604541010500101c6403109410b9005002c06406960300c0c01542e031044100b21400764602d00290354200c1c0c10700b003000d40986507642c42c24070301c02e02c11f00003040051714501c101ca130b22000a18050480352503840040e81c12541e850b0500080d0a03100540c01100209001043d58641c0540000d001e43d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 472982976 1250 472981726 472981741
    0x70f1404090f060c020f150406050a1808090a0e0405010c0e010f0c021216030c150e060a0509010905040f09060b1002060f10080d050405030f280f050f030a08 69
    0x1c80c441c010050500c1441002c950210345654007101080340c00740180d500303805480a505081c03126402d040d844502004051109000203441340550200242c50f04000500340381084514180c1500402001c001001a00003040d4481c6001c8070003c1060544000040c2002d180c144d02800c081d0304688000781d9440c050360703810742c0b2401039598000015200e00074642d02030380078081180d80000d2603111b03a20980d1007220f80801c1c4543c0800046010b036104001c02420440f9540020060030447e40c208480c111a4200791303a1802c003100c07224802c40c102a65510315000050301c400150783c9c002540646403000886003d00b498106500482c46a40c0401003002c8220800c04d0717003405055010010f03802000090a0384c20341d4174180b50040801004000e0740e44c1d0710311206240c0304540415800065012404001c6414104036070390244c80c4034030107008412005c0310031140000015600000c2c039010464185c0c00d01c0950381409400603000780c182c9031504024900181d0704c0d8030142e05000000e00c007400054a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 472984226 1250 472982976 472982981
    0x6130b21060f0408030612030903030a0201020703020f0d08160c020a14040b010c080f22030c0e090604050c0f040204050924030a120305060414041b080d050405120c03070f1404 77
    0x3213030702181650441c0c81d114144854099410604034191200f00b198450503a030800c064454481c5ea503001580d544041d140082c100404007071040345a81c00103101d400d8103900f10514680c413140280c107030038510f04c04a0703048913855006034000e13402124551011808140f03c074140c002041c002d5409000580b1528011121011030b1075018201c1c801c2880341041041c481002050420041c045261420004c220403014503809544211000b141c00c140400220303400c0c84040f54801c03441780c003410103864680c83c0c40d0b880380c51300e4040c035210307206040c00000c56a8580e8150381c05400f016102403450315002c00c81210300114111450b1980d182280d50300824a00002d45502d066480100c0349114a107815083d009084040c0085a02030b0301d42501e400d540c4d08507040d50384110302880300310249140501072103c000302e02d5008040d040d0000b81480c00010b42001c04c40d0201c420070780c0c4000300701c440703402ca05050001010083d0340c18010740c0d0340019441d5505405c20241c070181041c11030440c0d00c030401c1108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 472985476 1250 472984226 472984231
    0x1a010609080321270114010e071b031809020414032b0c021005091201050105210f06160905060715020c010e010501120b0109090b06130b21060f 63
    0x152880341480c0c0700c003419503c0407080e040040748500801d264842c583c8424914152030030304207070340c0d92001031025006064000900505003030758519454200024011f1158214030082c600440b52084007000309031065070383c2c03011020b000040f041c1a80e1580341c010060340c0640719030b4008582d107030020f0020f803070080b07040c40c8148204a29600d03801c1070b00407c03440c2d0f07036042501103040c80020a031010241c3c42e0000c404018030940da581c11741e40c44801701002043c100641698400b07030b15000042c001a00c40001c440380a4210f25200d04041d02d00a6800f450401c183c11602c3d03850107030720b05001aa00c00103c502800b090103441f858112170f1680c0602c01e450044030000b8100c2c0c5007202c540b5019110950051464480b814004034101000024075404d41e0401e0340994080000210f040d4207202e21a080305000d000c00c40b100380909030320794a50f0144200c015103081e10428100d4001c52010f0099842201124030250a518440800e406005020440c41d500f03614035000b0340703002468007a001c0d07030720b2407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 472986726 1250 472985476 472985497
    0x6010e130e0c0a0e010608151009060305360c0d030c030f03020f0a260c040504060f080d0e0303070b01060206061002012f040305071e0f15030203131a0106090803 71
    0x1501380c1e01e03040d000c440c1c0200142a9a5010312650281c03034094482007441514440d0b82e456868045240c50300c01011150014104d2020704868032060b00c0c40b03080101a54414510400c45600d00d0f804540514241008a15040d03482807501d0540020940c100201868450081e10303080070013040e2940c00c0d0145e10a04510301070038281000503250050081c0c2e0008900b52103034940e01691240071500070220601a079091080c1400270408101e40e1429004000c040e08134400088859407504100603075030081e03a5402c00c18080b074400342d90744607202082910700e000d8111442e0340b03103565079400180d00c0d84800d95400e03009001c404600b00c2454014000c02144040000800c18080304010254218814001001640c80800c200000c08681c0410640d0b014208000104054402d0911450500c1a4130f501081d01c0008008080290a14815101313002d10311034200503a99a0700e0156081d0401d0103400000d010032080341e800100d40c05200c0c01ca0f816600343d0f172119840c440c2c507089210342e82d01444a694 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 472987976 1250 472986726 472986749
    0xc0e07020a020d03050d020309060115050403020a230907030903080705030f070c0204152c1909060603080301090b0102060105031c120f050c0d0b01050418020306010e130e0c0a 77
    0x103005041c08030700050454020701d80242403802551180050b03030703c182c0c9c441032150b01c0070006001340f00700b03916034420f4900c4505016281c985180c0c0410940e801d80d00ca00c043c20004200041005010301c01841d58140000f040401203182c4924080c004008030708050f00007802c01000101c1301c600440c1200d00070950091500d9280da1140c00132500079914084c226082a06d03880c4c081e50015007941d0390400f0301669010080301c4030001203410754460b024002407400320104801c0c04185540b641080803240181c0801103240e5083d420305c2409007455500007030040f400000000350281c040e520880d0850400d0f401e4800d180d83e940c04065484d0316510103100c0703214000200d904840e020b008070902400c40ba10f80492000e83e0341d10243c044441c2100c1841c0350410008082c94015500d104007038000b802400e00c130381414242850085200f007030039402105aa40003003c103c032613000d000c401950701c0000f040c07100312a5032400c0c0306d8083e201d5403201c00440d01c07501425070361070710702031301c488083e1841000384c2c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 472989226 1250 472987976 472987993
    0x140118090201020f030307021509010903080f0a1401090c1209030923030114071107150f0c020312093a0f08030915060108060a05060904020f0310030c0e0702 69
    0x19480144400e04049040d48540040308000800900103148a1180c0350090004801c650480720b0803040014640561645001048030000c0d400400407900035844501440103030b41c5105040000344a002c819800070760858000064a84d0aa000a49550700594820031007421a0340903805403881e008000700441c0302c6130300510198890f00310340b240c400030040070b0788510f200f1540440d0031036801c146c40f800720004c441d04004410350032450004940074130b400140390f0240381207044080c0c03085101c000f0081201e0040c20440c0541b1504032104000c0d00181900c001501d10001810341d0f620840d00940145804112844107004802d41050f4a455019105080b400148a001c0504801100446480e41100e140c0c0780481c5800c4099032286010000506070308400702000e0b42000001400503040114074010000c2c9030b101d01d500c0c00121001910342c5a146d40007000020302902510086443d105d03408410440360f040541d880c441264041d0040c0c048079900c46c004808003d0b400c451143c0903900ca40074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 472990476 1250 472989226 472989269
    0x102030c0d140d0e06090c100c0813031509170703080a020f07050613050105060409032c0d080d0506060403020a171002220f05130b1504181401 63
    0x10001c0000140c2402c60b1030400000600000c5400c400c1015000354418410050886010058142101000c40c3c8900c014140707070a00401c1540071081c018030b10396010624043e01d100c4114900c01441d80840c005810040c0821000002c1800c000d05462040c15280c0103440100500121a0300c10303010394540b0350319503030004c0040184d8402e412844440b9010403d1202040d0107101c1d80380155081205180b0000b10b5080003401c0d500c001e408544102c0c90903c104c4006a00000360203101d1821b0900001c1d00e174603010040e04080910012140c100140120301c0c07003084140402010580762030f010403c0991a014103102e0640181c0c00001e400480f125014459400b0031600002040220802c8441900989001c1c0c5c003a030b04400d0481c0c9640d50030300324480d03541c003444d0b01032000303030060040f00f003061850400014600008802a681d84940ea4007106809449900070341020000039000c555a40755100d8030804d5150b81040d42102c00740c60719001024034405403400c28122a0302c1d0301d1006c2c03800b02007007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 472991726 1250 472990476 472990487
    0x9080c041503020a0b0301031106120a09020a030615030b010f0e040206181011100c0f050d061e0e070810060806010e090a1d030304080706090c08010204030602180102030c0d 76
    0x205200815007500380007006030303074044040340504442038405481e5407540c030745030380304598030812a0b06c114810302003a80805170b80001e155016401c48004140c6a480c4c1c004103404075210380000d4180c84c11312a400707940041d40700c10082141e03c54005c07460140e0361620400002c00c0306000f02c884030003031040030401520308400030303041c000d4141c00c0d40e480401220000409080c59245641c0110307004118075000300340700f4481000700d03000024041c40010002c51005102c0c40f01c10325403905001020448040e041c000d0340c0300101a21081c01000519900c00319600034020071072156401250340b0100045040d8803842c000e5025090700c10111302c4203030402d402929080c0c40108090704120740c24444984c182da034001c0b218099502031000061924003094040444c603001840c060340790740300300309100000c0c080004450409800c05000680d8049514005001c55990340c0202c400c0d41c008a004024001294003c0075400c05100300f00341610403000059803280503415100b030f0244c100c0300d444400c80307000d007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 472992976 1250 472991726 472991741
    0x20c0a0b09010504211e0c030803100b1209070f0b030106211e0606052b0b09090105070924110f0109050f010f060e0414030d02190801050109080c04 65
    0x5051482c201074650402000d40f881717641220038404503035503102c010300000361443d6920001801e0030001098140e02c03103240020f000d100091280000100061480441e0001c0ea40542404040240d5583c001c200c800d02040040d50040e889018920703000031181e92040c00300d4111094030305020b045a1a045040d1200d00e04480000b540c94903854403641c2503174041c0b040e03c4040e4025000d601c82101030b805020200e6003990007001c14010b042042055140d0750000c10182a80c0c00300110003400b505c050080003500d1a00b048c2d0390003514400c02c0c0445e05c5019040140710324035556800d0005680c1e000c039030380c41c411145071821042c0c590f0441d81c503e50b0700c901c0e1030540c40780601040324000d040201034942142c4c8030000c01c0d0f4070b035005805040320b042c0081c0034014200010007414020035040080640c5851006000102801403820760900c5c81c900900075199242440d00085440d01c11441c614005c18092110020000e10401d002149940c0104001030030340d08607100400c440d9480806001c01000034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 472994226 1250 472992976 472992979
    0x609010212072108041205180f04020f030709031502030408030a051f090606030518070506160c0b0415020a050706140409020c03090108090d0c1203020c1204080d020c0a0b09 76
    0x1a03c10f1003c480c02102c040c0b90071003041d545298a40c03400341064684820780c1424a41004001c02c400c034120303084031001d5110346000f207522030045826140010000e1090701020310400101004000405801240c49002c5902458040f02030327502400240040340310441d00140303824424004103550301310b10790000743c1c004d1400400e40148010309840b00d20351000c683c400c001803611100d040c40b1341c1d079140c00b41d141c02800011080c4695500c40d09003d440d4051401214021040481c040c00c030301314907800880c0040e8004c081c8009003921242001c03460b40c4503000c0e0001980320110312201061001414454540d04000a800c010741081c404890750129100010342811040c400840c03800c80780e10081c2540d558860085d41e4808085001400550000f40042103e800014800310300c290030040c00d02c0c0d80c540c040001031b039117012104160001d005408285c0598420051803500c0900c41c4402001980c2c3e81904a40209240d8003040740c0c3d40e420900c4480d0402c11800341080040028000352404950 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 472995476 1250 472994226 472994243
    0x8090109021806010e0913030c230a030807050a08011e0503060c03180a05070621020d09020301201606090f0b010e070c050c1002010f06061d060901021207 68
    0x18250005408030b1100d90040c4400c011910500810b503802404148800f8026076250780185001c00b00041c1003003080002070300703001701d8082100c01c209450f11401c003403655544070716418521141c40955075a4920b141240490b01c1903012401302c6019074240c90b4200c81d169a400e0150f0300b025a4814142c1e04140c00801006c0300032004031341d1f680e06101d028030944544078040d449240070f03240e480701041031061800752900624003110100f500450030200b41c1d84c40741003401c42c60380d161141120f20440380b0b141011140c4007081c00c03c042031b041e81100308061700841c001e00c41d1100c0c0450480321854900402c0c6011402004082001ca180e20301c2d80c0303a090300a03940001c130a6030985a0043d0341300707403400441d910140200140300e1124411001500200c5901d41001b801c401e03903840564544001181c0c0384500c07a61541d036a1458400d40003540740340440e180500246e80d8945001d002d5260010001c4403c0d0080c904403c030b10300302103054865908050740103000d100e0404c8004501a80400c0041c0d90760034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 472996726 1250 472995476 472995491
    0x9041d1b03070801020d0506100e010f030506013c1b0303151a0c070b030403171906080c01030612030c0213090203060103080715050403021e010212010e040c1212080901 74
    0x3d01c28800307031035400d92448000c2400d00c0d1000801c80540404007103017084c80b046c0e00c2c6441450760b1100301c43c00400f10354200060503480709001030ba00c1040318003c1c900c0e102c0c0b60001e801c001d0b50540b43d004542100e0441c0d210f034441a004805d80d0302d610b00380c503881e05a4091811603400310b031190f08031707009110344201101142034844420050784c1c40c041000036041400002c0c140c2c1e00e80c2c010007601004022038120182141445d64004001c00704980d030500144244101042c4041084405044550b500a908102c02982c4241164031808400b81c081d0119103000710010b03140507140b1201010a9055031030008000c3c0d0b507400c01c8102d5092000301d4444075621011361700141c03000c1154038069401a480300351603071003a24004a0709032800c5041c0c0c003054200300c2800002500003564405418a8a4914807002c80b29600d00c0c2c0280680300c2114158800b400002411007405020280500d000e01001c404880d02e5400f0704101555001e4001c04044142c904000c05074810049030340c003e0364900010900740c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 472997976 1250 472996726 472996739
    0x80706320c1b06151305060a09050603031c0c02070806090604060203090a060c080a0605040213030305091912050c030601140f01120c0f0e030f0705131401060509041d1b0307 76
    0x121040310001810041101030207103505e040b00e0f01d459000030101e4203105900c0c1800c00320f12903030f00d207216802c560f030340340d1020031030076a428400d49540405040000c0c030000d4540c13001e4805040400c400b94058083c2c03541c082240c520205800344510700740002025652103a81c1d40c0740003544010071140850003000303c1140002c2060141030404481980c2c5c0c0b00050800c010068121411540414400c0f4410401342003051014003040c01240c0d09410001e8840c1c0c0d5440200c0e286020a12040c51301c56070609001c54030070b141c44400380a2501610866124120940615a85003020300a40b0415003400f8102041c0d40342c01459454441010324001a051044411840c00e8032001213842020078001c502d1340541603031102c2c004000340411401050910403184a86803100250701605000c1c00c18100c660015007043d800145400740400070700c0480d0f60b59200300a0150f000f10311a83d2146d401d0001c0414100310400342459003c1461001d01940f07445201804256052408042e805002d1750000040c072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 472999226 1250 472997976 472997983
    0x71d13021005130e01080a020d080d0905030d11070312110d0c1707031a090a0207020d0302030409050f060f100c120c020a0807081203040f080706320c1b 67
    0x1100301c81d4a4440d141d10b4203496180400c06180c0021010440e840e0040000080006000d100c507501540c012a110785541021040703840307004048100981002c60355010044000014440342c0340e8000200802803d046403043c6500c200380c805000103065090348160307046560300501c0c510003000301e03035031410b0842c0404074191441a20360401082100c4ca000302c8140040c2005644403a90345010401c1c1094518040d01d100400003155015004403c00101440c0d0f41d0350454503496002010645024140d20b4025501d030701501490180b40e082102003003452403502c0c900c0d030207210010866112428481b051001c107044280041081220b2001d010010804000d54801070140c541d03900303090040c05006218220b0120b901104c100e81c8402001c0003040c0020819911800642800303035500c2e2501d04204541a681c4640905060400100b18003004903030352204000d402000300041d4011440c441c10800c04114002c81d044d0002d10000040c01d06401c00700514185071500e6000710f90710b4030350800614 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 473000476 1250 472999226 472999249
    0x7060509090a200a021912231b070f030503070602071104050a2004030c1203180602030a0305090a02030a030f02070824090f030d1a10120e071d1302 65
    0x4943d0001d61440307000c2c1d0510104c0f0000e440b40720f036409500c0440d629071540f9140c81615800700205c1542480100c9142e0412403100c6141c0e8083caa1181030341c0b02c0400c1c24407002c0e40700d8003c074802c1c0c400c0001e035040409440e004803504a00a036081039081d442e600042d40c416a02110910b081181d0854642e5551080c01d0041d0b103440c20000716a03001d0040d20000c004a450744082c8220140010400510080ea40ca8180c4140c09a00c07050058a890700303641d000c1c030384109065403010800d404154960300001602d02c40d10107035002c4c8584d45445541c1d58954100040280d010b81155602902180c020441800b034110b841c4101c0c0d010f19a02c003c81810b00d6001145002d0203940d440b14901001960582660400b1503070000d004102c0315052490341d6403050380b884d440003035181ea17400f005c443d08c0c0d030581d04a490760107407034102c0054022a0052100d55003c0901d807604d850242d00030802030002801c203080e506078904902040a060074001c1407034400070000c01d50969100c50134001611402c1c141302 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 473001726 1250 473000476 473000531
    0x50610050f0d110714060c070b04120e09010b0309120a02030d1508070f0e09150115050f031305010e0313061d0a0608070206010911040b031819021207060509090a 71
    0x11750700b082001c2c80341e041c820301814924175140240640c0c0003140d5001410b9400c149c0c440507031441a02c5280d400e0325005003140255901c8012000005400703280030000314817a1040c802035070002e2016030040f143d54024680c420006170f0061048a41c101c0056202c0e07008030300c500c0e4803a210709503170701d01c43c07407071300f45107800ca4001c20340c1e281c904018402c000c0d68080d4000d14a4405030014084007041480001d505110741240324403011500c40c0400d0252040b41c1011204c220666640d213480803440c0407091600f00121669843c0403802d15034150084240c4060820070b032500f13a1240e14104049419044040c410080c0b20b1030f051180d4466601c103401540103003a2915107030000c0c0307807044020b404d1010581c00700a0040c00c084000f9002ca04500454099580190072592240c0f6804011503610781540003884051284120b0191440000c0f8415a0110320032925401031014001201d603d4040038400c00012842c10300c03940515240803141d19074815144440080c0c0d11520484107011154000c4060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 473002976 1250 473001726 473001743
    0x10050a060914060408150c0c010c0e010807081504020703050f03090a0b0121021002010902030d120c030e0616120203040f0c05040207120509032b03050610050f0d1107 73
    0x411000354050088800c4882c11030325142410325069800f07459194010482044080e181d00140310090001c05842148281d00020406000b202c9400307811a0308100b1114049450503000465507485840c0162081280c8200070022601d0780c0c0a210294100d12011000c1c08018041c041400c0c02c0070000d580300c1ca00391030003004012000d0520310b030115010f07000481041203d610090000da15185074100f0940c1c1910305c02001500d51904900503c018000250300d802800151441c0030f07809400c403541d01d100140200700e9080441390a5003150800d000c0741038030703400110009a0202031800001c2c000513031802c1c51400c50a640b580d5030304a81c002c4404a82c2c01801c142d0304810301502c0d0302c9500160800352001c519001903a224074106054807078036a010000001a800c0041d10140113101d42401c04441c184543c6500041c3ca0840d002c4542160000030b05d030400181e041c0c0351002d88200c5000b004c6c1c8925190905001b0074040c680c2c4101d2080c2091522200030f001103007040001400c80c1400f59205 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 473004226 1250 473002976 473002979
    0x3070812030f061206130804090e0a02011407030c020f0111030409090c0512211903090b0a14010303111203070e010f030501210f060905060901050601020d140310050a0609 75
    0x60300c10b030308064070702402400e404005030145540080d1039504088102e4401c2440d5610f49030a040e284155040150250305290104140c808000b0b00a900940b00341c0b140c541940d1071984d154164000c4400140001d5aa009050050300b840400c82002c0301c0b0600d0024468231441005520b503a025a0000c0d09143d601d205201c00d210071450104090a42196036582044581c4146036880446080010b000b031009460503e2841012007125000c02e1a44a4002210450500a80181015a800e0701c90028100016428140034480d010b441001c030303d1800134903420340d2000c035040301141c2181506489000440f5400d0342010001e54400c00e05551344040d00046207000510307054a01c40140c00340b40c100001402a00c042840f400c0c61389003019601d0040da103d50504000110700d00308043d001d04d140108442c140a8003048181c8200e494000a00c0551106801260744282820b14800003d008201d407510004007800195004000b407602d010400d501c500000703c0040547d4003890214810707500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 473005476 1250 473004226 473004241
    0x120c050c0301051b090d020a2312070b0f0c060c070302150c04060311210103050601060503091b0f09091b0301060513020a210b09090105070e010e0307081203 69
    0xe02400302106034024451414400000104da10701c00c0083c0b91380c18004564122103840e80300010306155001402c0d44040d55488440d003814200f0b449088030b40e51003182e41e1200508040c00150044008034009002c0e103440e10024040ba074026001c019040c12040081c5030100e0001c021040c00349500380c60050313480307115150103498080b41c1c01580104403078250070000c1c0a100c0506850842c2c0c80c0f410042003100f540c0d4241e01541c4141035408848402e986821a0b40c42d00b131426941c1a41d01c15011240395980b6680c3c01c1e11240411900e0224560026085181d400000d026150900102919010388085034100003810104115120394840c0c0c080e150003181c100c40c46070b0254401009400800c0000d0604022844052040c04251021a0006400400d15101c1c0c3c04000e2862100b4801400219642c0032400252100410300c61140042c41d0105964103410700c078082c01942c01e0b880d90850780302c0b0407005480e91004421080c0e0305018007100022078a5090180c06c543c40c04070408190b0380e01d172102 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 473006726 1250 473005476 473005483
    0x2007030605070323190e0f010606091d0a0207060b0603090a021f080c0304050f25090606080a0b040e0f0f0f07050105030f09030405100e0306010618030f0609120c05 72
    0x9011a0b00b0744d11100d409105100d111885600884e2040d22200b007089801401c00242c10600740c40c55042c8a00104070611410650008060300c0b05641c0e4070041030f0365410080c050241c1c220315109101c1c880004101c00c81106c1c0d004103412489080c011441c41030000000d0829002183c59030700c19040000941d04610b07100c8131040c40c4a680b0500401c0032040014000c0c910100184000d1030104008007103024840108000000c518140c411540803647d00b100c0c0f4400c4801c40381d4101c000380244100492201d000c2c0c00749a0941d80c141e5292001c40c0d844d2030004001d8140301c000f0941051f135641040345825402e11070304d569a02c802c0000c0846034150004680390580c801110555501304540920807a07038083c04403600240200c1e400300040d151111400e08600c99907001c107901031b82d140700c000c10040e00044100b00042088003500e0b035aa80e1101c056032012408806ca8140306c00f15181440001d20401010850300c0c05442c2c00030740c030200c81c0e880c0c0155440b001c000700007145811160340304021041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 473007976 1250 473006726 473006741
    0xd0225060212060a0f030611160c03030f02010212040204090c03020604060513121211070b0301090903020d090303140a02010603080c0a0512070812190c0302030a0f0e070620070306050703 82
    0x20707140002d116142070000190132801c3d01000384050b03100c0204200817203000b0f02781e070340c5a510b40150510100700b44ca443e07642c020003840210049074251036100003247c018420b9034019001603086501903034469003003000a0030034a008850600c165000400075844070005440500159120320760b0380c40402a0890390003106500600e03060f540c4401d9800010311a001c0703e0a58401410a500c080798100d003100c0c00c052254004000e2602c01000029100801d5040421580d0082d000c0d250941d8035400101c130f914000340000b4010030f2007442c100c40c0400228004241d1030620b4030002404070341f00c1e51b6001050b03002401050381a44a10b4100090020a01281894071440d212552528420756100c51a50084010100c10b802401d80000d1a01d042d07241c0e481c1c22000803400400c0f6500301c2480180003500280d603039590306450030044101c03280d02440359520482100c4004c11005281110440b00d841020b00a080280d8015003032030418041001241d000c1d40c400c00b0007203003d103003644d401030407100b09 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 473009226 1250 473007976 473007979
    0x806121218151b120723060f041502250203060c2805090301090c060306050d150b040605180403030b1c0201030c02010b0319020913080d022506021206 66
    0x202924038450311400000c5401c02da00c107480840f05028400c00c06414400e0804900ca119100094082d0402ca1285c09030010b28803001986441c080b141c0d2462580c030007040310031702c0b10304010801240100341c0d10012101070340d0f10780b078015203032141d000303d5120081070106442c03007004e02c0c0350449021440c09020480d881a040d10381d450a003100060520300c1c60740000103000464001d005102040761003502101e042030070240007440790300f10f40e01c1c6c100c01c4800d040c414800000c2c9810f03408522440c1081120302c21903004604620813821441400d0020081c4412039036000d079440c00000707030340e45a018807441c0001c01c0c20020b403698079190030050250354180300c4031f602c2545a04418a44001e8040c1240511034080c80c0000312110208000c0e030050000e10011903052103400039a40c150780759101b01c003848501c00e613440c000c0390300c0d03807144000041c1c1080700c020a2040d0600c00141c04a41d2607001c0c0c4455092524112440c060f15a409002d01c0005a01550354580000d900c01c030200040782c070690010710 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 473010476 1250 473009226 473009239
    0x180a050c1207050c070e0c0705010f0b0d0204052a070606120c09020a14030c0a030f02070201171003060204090204050915010905060a14030f0103030228030806121218 73
    0x550942024a520042c01c000074494007083d080b0110718204144c1000c0c100e54101c040351030800030700307207100c5402c800b1007120741d50708090407030150709940d0040c134016101c064918240d1200a41c2084003920004108030f1aa070020707014038061032001d208068620010081c07190362800c503800c00e90280c44194200d04c06d101c03c20030440e000505406400011600300110060315a10840402c4681e0f0303c0544015991040c08000c1c089003201500040442c110039403000c0184000c882d4407881a4003900801034042105035030604e860700315002110390310000c0c658019400d1a00d035500c00c01241c00541112501d00c3e404141404981040030090b5000345100390202d003201c1c04d2200007410800703203000d00e600591000c507042107540d000709e81c1c109080310b4420020340c41f403402800c0407175404c2302440f00341d0041c41480c8554a071b41c02d00c60700c92641d010f040f8a03980c0b082803094409850a001c00380106070418403047c070401580c071040c40b820702010305019072586d88100782802a010807030340c1100648503c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 473011726 1250 473010476 473010487
    0x20a03230c060403020915030a08300f130605090102180d05101512050102180604030503031501050c1e0705120705120c06040f091103090303060405090309180a050c 72
    0x90b40d0400b52400c40f5811108185107541341c200c907102c174143c40241c02d5090710815007030724204034000000e00302016031401d103d824149501e151646000400c08001441002031010402414201c28015400301c02a000482282c1c425600c410850702c00311580e580c0b80c0d43c0807955100c100a118103c011f540811140c030540c046050300e0303c1c0d0b100c00e0684401c100c02640da180500c59041c2c404114001061207030146000700d92b0900700140130354060040390442c1d244062002c02685044001d0790241c5e500b00b0300031030550b6282d03881440d003000546900c50601005000c48442c40d5000c020080942080403102e1170182441c001d82071608a03150402441440159028030303414100103038640484d0400c542400c82d4075500340c0c0311410030b20840c0c1c0c40d0740c01100001d408a0034104800608003240c0c6074160820540c101480c0e40cae80c450005440c40501c03608100081501d5103800d07007049400c80550340c02da0f860855a01c00042036a00d407546500401c04980302040b080d031245104082d40400d64886003442c05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 473012976 1250 473011726 473011729
    0xf0a0b060a02101505060d0e06011e030b070c06050c070201020601060f051206060c0706080f13150b0a0f0f1404061d180118021e100c0f020a03230c 65
    0x3c402000c2c540100302c1d501da250342c000e40c0403828504010720002e0318503136484045000c401c028100c0300000340c5051003040c000250b0080c5517141d0034079002840446d80000c81c06c607558210600e101905035070400110410f0708005c540e052095a00400c503420f0b883d40d54810318400a401c2c160142d2040040c042c500821901550b004802c07145082540d400b49001e564130540081c6850007150b1510303550307106051000c01c0e0a0b40124546000d8200c000000d03845a0b18400700a007012003138400200340300701e1081a118142540e03040306480000040140000c103454800001d80d03001d06074442d070400182c4000810000e1404192901040c4060302c0c103203c07003801c0c5810036107041d42d50301d070340e10801c2c40c0c10000691208480d40e0000540445000038408083c100782c9509410440e104203911840309040c141c2144061204400c001c0c2201900c0d002040c56103542c02c0e0b40c42d4030740840549910301c0003800040160707903015030b02c005184102c0700c944d03204d01c0e481409a0100358014100d529688410f0f030190f001d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 473014226 1250 473012976 473012983
    0x106050a170d09050109120507030f080c070b090a0e070309061b0e04141315020403061a0301090c17030f03040804030b0f040b0f1003021c0b09210c070503060f0a0b060a02 75
    0x1382d8226141c0c1602409048c6041c900d400035542c005800d54007542d024a0800c010381004100c0040c20004035642e80d602d922444201e40321b1101425440002c0c2d45081004080b12441e040d401100c42c00d0018504140d42c40362400d68402c40c0c440c0c0c181184d0351641501c0103801c440160702a6205031000c020260309405403179958003010304500b44010507808031208000c803080d004a481c0400240a54403660b1300c0c60101d0140102c4420140011160680c1909500701480740342c6450340c100b00c050a200d481c040103440c1c1c5020794401e480c1c541c003040000003842810000214041d910483c541944c1d2865418940316400000c0e20b480041605030041c8004980302015840e0006030085450659840c0c400480e5540300803680000d410150128007600074689442c0301150603801030318000c1291303940700c80c2c40e41c1b0740c83c43c1400650585c51030107030751403900d40350000f501c10313188810104c520341616071000034580882140c080422044590420000c1816401188903820040d19042e052003102755000e500c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 473015476 1250 473014226 473014229
    0x1103070201240f3b07091401050306040e0c19050907030c080718050901061e02010528062103110a03050414040f0509010218030a031e020106050a170d09050109 70
    0x2030300000d00399803003840f1a04c1d40010555480f00941d265041d2151801e0494480813100107002c58254840000d0391003607000009003c0303178165200c40c91a0303552801c00000f4515056aa0001d02c02c0721041c104a460b840a00b592084c04c0c82d95560009243c40b081080049c0000c1200b8101030901c09504562900001c21580015070740c2014054565030a032a031a500c42145d1110340d02c2001c80700001001504400c0500c100400000c0842030b51000c0802607090301c40c1030f00e02402e2255030802050400c1400405160780c42d42c5004003040b032a9132508001c8040c450443c862184610404d480010190040c40b0300e41c0d4800c0b0351000d0001400c00d0744024200f4012489070511100e01101501c0040d07131154000004010498420000d509040b8032040c003e420604000519070103c0480340003600d00010b0343d40d4095807640d160441d036505a20f20409130240e80f03a40c4000e40d03494410102c1d00f17a0750944100081c1105583c181d0643c409a6109881e104c1c40c0002c2d0000e1080140b000d01944e43c0c0640a01d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 473016726 1250 473015476 473015489
    0xe031e0c0d12090804150e01170a0b04020d0507110708070308030c030601032417060c03310f060507030e06011a0c0303011214030c030702040f1103070201240f 70
    0xc0d02692681d00c1100500b01c0c4900050070b107580010007107030007000810018900c1080f40c0c7d0350140c1841c114010340e01c42504071403d0000c5901400020303044141500000007404004d000541490040007401d0103071807090320b510b00031526202c11080111410000c0d4802020008003c2440b82c0c656210a181480082d1405929020020019880f81d029802c01e50301180c0008000004800c901c07090415802e46000c2e070740680b000d050550140980014585010380d072402500c40c51078a8003c14000d40f0f402d000c001420301c0c4000c020020a04900014502003180103510740c02c0d00008901c1c04100300d94009002405141c03500d4510110707050000703211415504501280610800120402c05c020f00410320f030b010251000200110b804858002c1c844103082c80382030455004414840101d0b01c0340035100e01081e0a82c400d01103800980380a400010022040c1140000c24200703a010001c1283d10446185000d40e4450018100a0004402c070307412072100c514803580d02c0c504003030740703100860f41c0e80c8a0344 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 473017976 1250 473016726 473016737
    0x131e120e0a1707080c010504051302030718141804051c360806011a07080d0e01020a1701060918020c0303040302070305060105011d060304150e031e0c0d 67
    0x8030410703128403451001074218100b04201c00b40003400302c9550389255014605280c0541440c90034503500840a0b0f138140c6100605c800900841b00c0e50700002500300409240c1040345191104103071441846000c8060803141042694101d0002d00340040e1f0607201e0b42e400740500425040002040010900d001050350b0036845141d0103a05000840e003480e440c051081c9080008c00c1c3e844a00010040c1040440010f44441d01545644100054450109109400c0803194207074450850328007100052002612680c059400d10701c881030101c084803085415040365071f600090001240f030700910300c650001e4540006509540c14414020302440e110b1003482a5a400b200da0b4a081410903015252100c0d1164226900c3e8940350400965544646c4416075540c042c00d80041070300d5105580c0800c140000c80c00030032001d0306450034010702e5400140107a032290b880e2076085111210b14000c4280b0820805c00546c0c0b10803492041046501556640600c41d1000b084500721851000c90403080700304a50405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 473019226 1250 473017976 473017997
    0x41e080a0320040f030507080a03080721020a05040905090714010e0a0302040c1709160302010f0e0301050a06090b060712050903120a050304030306090c020c040c0c060203131e12 78
    0x701c9102079242d02800540c1c020208010840e0285503110030f0440f8041c00403039540a40e40c40d072098030b80c0c4508002400080c0945c1c009400103000d41d045c1d44018030000b08101e03006002075035110898214400000004a001030200040030b264080c0c150020384010190035064602072900802140e068600360500115820000407551030101c01e80c02140c000c2c0090205043c0140020300303294211821103500035a04001c583d400ca4000758003900c100c0c10081c0d1501d12810740e00150303146200c52529804011040c0ca480140352000c2c014640649660840842c04504290418085e503000104003030103094184007107000f0895216001d0f80c9000b090402a6842401101103405d1002100c207102100c800000c0c80c103106544040154429030080d40c003042081e4a900070300c02a0f980103070701300c4016480031390724000610f465441429107005608014260764050756541099800403a54042d010a010450505000d0b0000240c25a00c6000307101801c80345181d03445401400514041c501000020042c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 473020476 1250 473019226 473019251
    0x9240f040b090108060a1512020f0406080f0106140f031e0c0913030206060409050303040210180b07061104050d0b0c07020916090503061308161703041e080a03 70
    0x884034641ea030150900b000c960311600b40c0c5550b084151840d030324aa00c0e044032900c0809804008409681c1e0313125440d008039070180c00300110800910b50701a8020b90ba41030005100c84104081581c3d428400c0020030349502d450f0b00f8800e82001034060340d0060045600c80d41040e500418070350300c10b030340c80c1090918400190ba8100d261004512503030303400a03140c0301405070740c00904c1d402c00082403180d070132640b1543d07804041c401924020310004009510510102d00140f810152a1084011619011943d1038001514000b505a51781c00280c606100246d200706210359401042d004448416540c0c1c545468180820000340c0151001303003500e05540041100600c00310701301d0300102c1c0c0003410810b4a0416104800c1c811499128940200320190000109800e0101d85984180c0190040000c107004076107890540354071800c01008a84041c1c42c6890000b07030b0901c2690031400019808540ba45000d1030b00040c2c1c1020400b50302c81c500706078030f449000101080101c8201c10018035001c5410081c488 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 473021582 1106 473020476 473020481
    0xf1a070f0c18090f120c12090305010609051b07080705240901061406091f05031006020604051c050909160f180501030e0708120909240f04 61
    0x40410002c17686115001c2c041d11142e041540c00c91069039a448600082c0407070407404110000000c2c03080c00824420707040a400060700800c40d07818603048103029586080398128401c0b03000100e9008005244080e500c0803a4002c040324040e040c1c5000503030021f101000414800f0030302d84000b51003410140510002c440e600c00c920040001884140030b059800418420740040340300414661184003040c18840c2100384d5a9500d803a800c1c00c244030b412066542c3d00c0502154085802e02012410102d0b5582c040e15582c2e03000c0c40d4401c0d0703098040d00d8900032401c95560021400e810840c000c8100480b4000c81c1c0b113140d46a00340c0c0102c80030141c9403e0035848525070380c1c5e084110144210750007a400760000b0810802141d4106940c3d006d001c1c0780881c003032012541c4d00341c007048604050800c04003490704001c0c41d000038a2480100d282e0410200e01141c0c40700e1203070a507010384801c2c07a00e40d503 = true := by decide +kernel

theorem cover : BRFrame.Cov 472841726 473021582 := by
  have h0 := BRFrame.cov_init 472841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 472841726 ≤ n) (h2 : n < 473021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
