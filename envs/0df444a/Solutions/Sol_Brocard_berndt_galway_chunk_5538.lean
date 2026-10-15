-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5538
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:11:33.435737+00:00
-- url     : https://prove2.me/submissions/c6543319-8a30-41f0-937c-6ed47d8adfb0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 995863309 ≤ n < 996043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 995864559 1250 995863309 995863331
    0x60a081302130510080f031303021306030501020a0309110d0210120207020603010b0c0f150403030225060b0a050906150703020a1a0f0711070b09040608151b0717030c0d 74
    0x43c0c81301214176200c00d9808100409050584034402c0c04842c00031900f1141003000142081700f1041c4090000003400581c0701d880f5520340c0e0aa078440308054000035103a05d03448007400181505000d0551040742c281020044590226072401802c0300711105201002c0c6194900d0b0a00f50102c40e5103550050540b40c3d00d6171500a10611030b002515a0f01d03d030321501d401260514400a800001c5d000f4814410702c2695940d5401c9029601003802019102104150403945980301900700c10003600c141c03c041600c4420340d084c00521181d50340590312030b41c2c0c41014002591a5414806590240e0002860380d13049075040076403034074022140c02402140b1000b22000c10781c460307c0d1424043c1d425110600c0e02511490707001c032081501110f14003200c0d042000104078044604000b8156030350090004641343d030380d541d503e50901c80048040b071118014070301000322150000020f0750301100000c0740282401e03520f4880800314020b8101c0000f07006000400719104400250a550141c1241003051096181074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 995865809 1250 995864559 995864581
    0x20a1a0a0b0a092406050418060e10151b150e0703111f081317070c0810020408070e070201060902031e010e06060d051b030123060a0813021305 63
    0x13a0708883c14150007002602c55032030080301d504102c0301c050359114142810403403585c43c00b00c00e84c42000c9619a42c0e120015004a9500d20144030307a2024100425041c541a800c1035901075001d5408200804000400102076004440f151540d40004a807160807801149410003012960035049062040010000c100017900d51582c05030342054070241410480e56038942001d503080024680407400d01030008910301035580da0300d0780590150380d055001100180c00300701c241d031150300145da0340380070341c0c4040c490302100300880b985006110380d0851070945403082c17043d02c030300765070060400511411700031a12003031003500540c0c080d0000361011562030070300d400480d4001c2e12110a0103500c00e002400043d59000c6084414801c0c800500100d207000c0c1c0b013200601c024500200103400c3e11072140e01d41d0340f05a0640c009180600300860303c542012603207a014040e22082c040c03006200700c008100c0503100d41d50144205401203810510540d001701d0910020f14015002e00145003211300e85010040ac00001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 995867059 1250 995865809 995865821
    0x8031b0d05030708070c0f060203010b1206031603080d0608031309050702011103061908010507030209030f0601030305540414151f030b010f020a1a0a0b0a09 69
    0x10411500d0301420880141d6980c0001c464981c00714604000003000c080c015030a4144880c0710300025690743c42d0782c1c0d0322001260820382029698000c0411070492030b100c0d4180702900140101e000b040024a918600d400b1640d55000c01003c00d0808202204003069541264020b000644203070790b01c9035601d00306d01d48081c08501c503240e1310714140b0303000c01e42c82c070f0062049174200007161004500e5543c0d10003c1c8411400104205014145020800140b00d81d0030300c92940121015a405a9203441e80c0040616110315080c1d035550542141004100003070b000400c542d1801c07110010300c0011305c0c1c0c075007080351281c00075038034844402c8448204140d0000f0300c00c0c07030750348900c0811504070344400d0325418402103d0071030051208111039680820481020312070307240340d101c5004000f1a250f1040058003200d05010350b0040c00403a880c0c0003020241c1d80c000481c0c4034045954401041c2264003030310341680c4c0c00c4004031101e482c042044041905c0d201d40e500805a40d4101410f080943c40d55a8510350080c48 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 995868309 1250 995867059 995867107
    0x702120c2407120207081b01200601090c0203040e101505160303050604060503060907080d052b0b13020a0f0305060d0308070216080f010c0f0903060b0109031709010305060102010b030d12060803 85
    0x8051a0b2000442c9c500007a0511420350200003172070325a082c1203010000740121083c6406600c800d200c00540c2c80f040300c2040388201014070300a049a890300d009034080c1000086201c060000074480301e0180400c0c2d03010340c1c182c130350145808980350326044042001003800b504442d40502a2204114030f500d000158042250815001c07120048206a022149401599103c621000449640c0361021a0a003114025900350304030002e80d02c600c1600050010b098000c112085607008268000b08641050802c3c42c280c0b100e041c103110500d0000002059002d803242e005003845050720108034668404c02060035102c401c0c030305e00566152140e101c2950340d03424400c0d201c003540c2400c1150b01068030502c888a07110303980703880d0029103034119521500230349010380c8d030b20b81003020b091400400b04a0740b114240310168400c407026504e081d130701300043c10384800510060640e81481280e10040d180040e115643c04004c0ca420f080c00c070341442c2020040d0032035074442c144a120100c0e0188948503820a0410180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 995869559 1250 995868309 995868317
    0x50915041403160f0603090809030a030c0b0109090803010504020d0b1e03010e0f0a030818010c0c06050a0b06031902130305012403030207060c080702120c2407120207081b01 76
    0x420307990449400940e580507400c12126211310411184e4040e4001c002c100380704403a420b050800581c0868503000140c402134000800f281c4c0c00c42c003801044216103000d02699503041c0100c800c6c54642220a10041c440c540c012980024a0462801c103a400b05000e000020a468411503090f60024440400d5504039071081d4a000161880c11500003080c01c40d010b83c82014149907401c41e1000e40711100010a0b03005000c501d1000d146200b5070038800c030080c1510303584070304c411b0b0300d0282000800c50341d00130007100409103840119401c994500081d0b9030304c00d600080c07007480700c2ca07504904070103409050b01840c1041094240030040000641200c1d21400c154680c0c80408402c05003410341840d024030011300036030485030781402a24440c88040000900882e07c40e460f050b100e40c0800d01e115405000c008242e0800f070700c8d0023460325240c005206060782c0c00c00d4115400c00b07180610302e458441ca42004050700365204200b0300ca14000e005100c001d01e0103000391006405074542e460039100803e000b0900003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 995870809 1250 995869559 995869573
    0x70b09031501150c05150405150114130b13050a05040302280204090f141c0f020637091e0308070e241909030f03050915041403 56
    0xe140548150488903000303c41081c111100109507848003409406507518025172111030007001500c0300c254050787c0304d44020001c116038507281c1800f02d101a000f031104210500351900c010f41d41d81c0b511f094487c0441000044041d110700c0002d006100600000c1003207420902041195030f000d45c843c84c03141d8060f8003503c0c5011505c86201c844c0c480034000d0102005a4030308a00050b00b8658003110b1241c2c42400f0176100400d0350b45444156005d208030780d0741b1941c442005441c0030a845202d0702006e074000d0500038040310200c0c2019440e03100c02070424034108050307910031442c09041940d10410342000c03040c5040b14400680c1d40c0340544800c1c00107032000300300e016550300c1b80e40082000019070b03601580c41550540340d8500450341c5203c4094107a0380315042003505040da41c00b008072001809409960185d580054003912142045003450440c2401400350b01040450151544103540551620340141d171040600005814680a182c10240d414008a404a0412032400c00400c690304124121009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 995872059 1250 995870809 995870833
    0x91002100e0d050715020d0f090201170702430e06011d120a05010510050f240304050f0d050406030b0a0f14010504080604120801090e030403170903070b0903 69
    0xb807080da4010740000200104044004602003c07010394241045a002601d40382c2814501c10507542510f84410304d25a039090460119a000703004454001c69641c06065a8540420041e445298580c2e070440c1d02002246254202c07920780030031100f0002c4680d800f010207020881c5a484141d01070040c0034100d65403001043d00c0b58054410300c0b01817410410000c1c202035400d001d12041c8000610003c10b03500c0b030681c0800005400b0300600e0301c6101c1c1c0c1d01c00482030910b007200700a8142560b010075400b4405900c1340c43c400c4c410030b107a41c6100800d500240c66483e00d403446d0061030f00d407000818901074040e1501e0000460350000003002150501e54081c0010410389007042601e507424404c1e0350b070b11102244100b03d010800001a020721005040c2a81442d503182005401c2c000101c40032901c0001005080d040039402689085c050b0120410400800a800c0e011940d684910b000140c110710030750707a1404c50000340070221040200c000d0300303991003e580d0f00746600d0035170403515409129011f05800525 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 995873309 1250 995872059 995872063
    0x618030903072c04120f18030f030207030503040605030a0614010e090a020706050108010c2c3f010c0507050304090b040615020a02011706090a0c0302091002100e 71
    0x420361004000d01203a5107084050f5040d00c0f81c80c2c180074003801c1458401c100003500d000c0303124852801403c510702840d103014002481040178103a15400d205900303071071a8032922601d60340b0055951142c090311400306142801e80ca010001d5200402c0ca02c00001c0110310070f030f8400041c41c09107c0700ea00c00d0000d0b549030442e0000060b142c11105002404003820f4003490301d026403682d0f40110a4650040c9050010f88490080d07072801d0b0800d1030541e45071846140f040d9800062092030040241401b581c4007034080c0380410060001305071500caa0003442009810104d030800303421500700c160208020103000c954101a1550600c480601c080d4030348460840071a0142080302d98555110b406103142c5810300746031710001d2098508003508595140d50205440b6035090081d03420b00e80315001400191458800144858912541c412600580f4001d000043c1c0b58841301c0c03504001e00400100d10706070342c014110000d01a00c24550751010854181c0c01420b0b4020a010030489420700d0140910002e401c0055 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 995874559 1250 995873309 995873317
    0x30813030f0f030e0304090212010e16081b0705010b030d09061418120a3008041515030521070f0c050a030c090e010b06030a0e0114040302061803 64
    0x603012645820344422010b00c26440711051071000d003400901003084a010034034640003508007001c540d500090640300b542c2031517150303401014010548950f903c1c0c910702081d11004a00c40e03039414805103001180c80c0840114010f22135588045400361a810705041c0140640100003c0d18024080c04800e1540c0502c03403c0b82905903210ba480d5100e88040000b00410740d640310040440d02c0002140c00c4042d20f503983c4644400101c4014010b0045903494101031164500180f05409d00fa04403036603461a40c0030070304801c406150a42030100295036207042071f5003103c201e4220401080d20700160803070702e05204030440b01501c0c004e07402c9903141c483c0d951005030307515139800c41004070300c1c014030907140024031600007101400d00c110441803804d0707521404590f00310103e810450720700c685010b0611440e516481501007001218000744a2080b492021130003a11014144c0210162241141d5040440940002041d0381100b521082c240c40d203414003c3d281c500c250381072030340c0c402242981c42014000106031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 995875809 1250 995874559 995874563
    0xd111803010b06091c02060a0503010515041a0a030e010e071502010509120c0f070b0301090f0207030c200616050d2318101206050301060b0d09020402040e090a030813 73
    0x701389400f204500700008404500600405440384110321030042c3c98400242601d00841d807a12a12941007100304081c444000c88600440c000071300081003002081c01e22101c103500320707100c019915506044102d000e8081642030415540c24240d00003890700300040c4100484049008285180c00c001d24128281d0300251035011450f40b0020b40c50040c11a140001d004c1ca032044400c0750580075240f103203103040824070790060b454101c0110041048e80294002c0c2ea00013489110110324201d001e5a014014208124001e4003407039490800c00040d10100400030301e00e44e4004c00301d40d00c4215a117049903070035500c0d5404503964050750706c659400500030034880f02c0341081c50b00003008000d04024141e45540002c0c7d48014480300210100d000c030703110140348015540b0340340d8480c400885000341500541c1c240f81d01450090385490400c100c04980c0c0307001d442c618541250f000c280c022031400068081c0c021500b006401b068800700b4001130340300003d03440d2a180c1c4252a68a520340c0e40c07140a0752805642140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 995877059 1250 995875809 995875819
    0x3050604020f0d0b0303120a0603020f010c05060a0b221e050906150f0a0806040507061d0f030307020306010e180c06071b0803040602010221010f1a0d111803010b 71
    0x4040351602660007140050401800b06da04104082c0c000c84480f41c02501c07803900a90381c500d070a00541c20481d0080c03181e40401c9c01c00c1480030920b07a0700c2d5955040010b000060711a5603034a02c2c040c1e0391310304d490b4612818014028000b92180c0901d4000100903038849000c40c000010580041c1761100d014061240788d00002034042030341e07014408001c0582c0450000d034004500f100c01a59982d0b1201442c019100080041460b450f06161540c6040303240d0704203505004143c507040c03122480380310480740c100d4020fa800013503600003480480c0c030314052040001e5043c05000c0001c04c1f869000381910344100550b0500fa050381c03a0401a5986541e01c48100d55000141040764402060040381d4040010b14003440004990b17554100c42030641c0c10581010700144d40004014100074120b04d100c0111125000c0303070808551402c1d140d02c0c4026241e00c52820360081640c00c2c1400708550206407013020188131010300524402907401c8600d41d0007202ca40c0c400e507420019200300c0307060502c1000d41080780544 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 995878309 1250 995877059 995877067
    0xf03010e03091315150e03060103152a051b011d1002071509020315181e0604020d1a0702010b0103050c07030918020c1501030c0506070309150504031a040303050604020f 74
    0x4401c0121445c442c042001e0001310182c241c210f4601300041c034000d40c011114185240c4980c10200151192205808000e1224500054070f40803c2c03016036504000ca400e04982d142c881d60000140c40910214101382c07546410000d01c041000641d03000e50481806040d19140d44800745448124012114050b00082c2d50704071500252509500880400340014212018200400340300c601510085a170400da0760301d1b410310301000c40d0013041070500d40e0306c0340d201c0101850311503d21290795800c0140081c1c421a040d110348414040400e00c0308014040e04070300065140f500005c0030740a4841c005000f400240340c00b000803030505085060784c00d050b40c15035402c0811440c1c005802c500c500c01d982009016a4200514040200100000344c0d87c2040b07209140925851414804902c030b5039a40401e01500d070070403002c1c001952040c00041070f5034204c50840c0c881c00014004031440d015075040100580c0149440e030301c03800c405040051040b440780c2d905110130741e1580700307000590040111140280c40180 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 995879559 1250 995878309 995878319
    0x1b0907080a090c09181103030f160f0c0303050301080d0e0102100b1201020d09060c020c010c1e0c08030d1113030204092904030807021b0f0f03010e03091315 69
    0x50000300b0720a00468a40c007000344c989030040212150f0102001c50202145000710405c0076010034811019002c40146050021568007800c0a120f055103982140b20b081d501c0c0020070500001d10451142c110482c9001b0341d0712840d000d01194401c0c000d0500501c00c10900b00303881445100307103c80901d01030b0301424440d04401e0790000580f80c500c0c400c50f4001c100100500009400b44040c4c880c142034590302094071100b031304118040350406e620403021500000010100c50741c000322035401c05e50f03003c0c503103800c1010a51a00003a088008030001c04540b14070000040850b0300001070260104074800801c0164003103112486144510405d07005204100d050403c0949032a81c0038000c1d540c01100e9540242e22201e00350380350301203980d901240e01500c500c140014544c0c0403403040e42c8411140000e1061221401050070400e1003428124441c5007210000080c9842c0d030b0214085065000d00240305c2101c0d826540341d141e40021203c2405841c2d0341400c11403600e11401040d403207907252540c6003002030900c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 995880809 1250 995879559 995879561
    0x150112022205070c020112050c040e0405071a18100f120e010c0306360528270c03080309190804090c0323070309060207051b0907080a 59
    0x10030440c41c901140c030008864100305000d40d62154100d59648510a0aa0301c000f40010039481a4010120714000170440f2003285201204c1c141d40244140c112199203e05d8520306d025115040501c3c4e03462440320704482060700802074a02840d0428820110300840380604c00145030301100704000070940102c0d41000e42c0900030b44501865400b001207140c5103c05115801e581ca0b0385880000641c0d9100c00f082480030400303402e801e0f600d00b4282ca0040341c0d140050005002400041e403503045640f400424071803d486103060b03864036041d03960920f40c102050141c43c018810700388100c01369107a10415003002075542045903d080d6010680f03900b038900b140c48844a035003004080142030b00c29070000c0e92072080315000c803d012510804020799510704260f2a01d0039900f01c200c1c51002d160400025510b50610820040c010b0041c01d0301004441e510343c80100d0161005080c003034101c2d032000403805e05002001c1808070343c28100c0f140010400080100f804041c00c4112140000550424003140348100c0c1c0d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 995882059 1250 995880809 995880829
    0x60606090a03020a140108010e0c2505060f09060c09010503040f0c12081c0204030302030a110c1215010b13120f0b09010e010e03090d030e190e0915011202 68
    0x500700c8154107403a540803a840900540091010b0602178600036602e69204141601401071858850801d041c0f030b0100440500400d40c41008006040e0360311341c035a000055140000c02d070480700300d81c00da0030300d181c18005104040d40c41555500607040000e0088446600300d44001c10103a41b00c51440d078868440c0c40401114a10132108051000030025204070003c403004a054082c0c04a10383d2003107110302145100a224403260402c178014001000403a4020095a882c0f11207030400448028102c0706160804200c1d0100b66032100741e01d00848106000005d100c054100307080c0164040d43d8071783c055128980100d260b0304c00c101032664000e00075180c2d0044034200740c92140316140b8203401c85030340710b0801a504a8400d1301c0b6a5443d150780d0302c440c209000340503080f107480300078618165114000c40c0d490354401c2d0000e002d11100d03140c031080381c3d280c80e0500162105a101118003039500e0310021040f8520a60b01a5040d10a00c08034800b601c0c403846000b4101c4800b944800102040340c0c1c2884402d0078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 995883309 1250 995882059 995882077
    0x21e031b07030203070303020d0207050d0b0c0307170c0c3007030e0603150102061501050d0c093b0f1b0c161701051909080c0312060f12060606 63
    0x1140700002c010b0f1000c10601c40618403e8001d42950209404000d1508680e580411301c00d0740c094586001013529014241c0c1c004000d0000c49642c1d8ac3d50040c240d40e41540c070056001c080040b60100111119124041c00c0b281c0410015100e0440d411141582e1000200300740318004100c4c1c01c0075040244500700100030003131290800307003d400760900000e82113400c1140c60f240c912101c514400342ca5a414451942d200b000c00500303c560510341c4e40020014018014504620395403024050320703041c0281c05810060412251214001810388181311400c00c0e802e210010000e0310581c400a4058000d203101d1251042000c1601c00355108a994941d180598031510f2010764204030000c58036205100c05a0102440d1448048840c544007240100042503030414800340d14180a00400d5082d020074544502e82050000c50400384500300704c12144244141074485200019001e2000400170040da80300380801c403450404507141174240140990001c0c081c207104d030420000a03030989410005024100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 995884559 1250 995883309 995883313
    0x20310060f02280b09010c2c0904050717070303230d020304050d0e01050f0315011806090f05040e06061011030a080405010c090503150603010f020a0807021e031b 71
    0x498000c2c004450820009090b1000e811003407407800601c4141306031310f500200c840008016946201100921241990344c5141d40c000c030500d0310f0340c2520a8140440c119941c0105a100c00303040918203aa0f40d21940d100303400003a40748070344020112101007a54070840b41c0503103514800b98680708100750051589016a060000c05002c200c414002d60310146105901c1800140214603014001405280c500284541000001c00c0b10640b86400041684d030000e80d928004411a208000142c0e5410040503846001d10048200085c0d2507078080c3c1038000f00c50541c841c22500c29107940602094810307801945425902010200300941071007000c6455010403850451203c8544015003800c550040e480900000d468206020070300000b0321410348056110b04142e02030324a081701080d2180c800a10001d48541d000e000643c00b51400c1d0070607039590352604801c5513594070321003000d41642400d5400c60300620036500340314603504440350110114190071009500740882c00e50300122004020301210014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 995885809 1250 995884559 995884573
    0x20d06050417030c1b1204030212010608030307021c02190b071e02070e010b191d06070f050606240705161d1e07030e0118050705010210020310060f02 66
    0x414482c0050b42c0605855204142e591990b90200400da8001000300ca40d982c100e220505914440038040343c08807030b07040c0d480c84105040420704600414255204251501001080003400e50380810300c5031640350418070090000802540480c2c3e00d000d0310801c40b0005400c180c405000c9190500300faa8880564075060f1559070320410308090074981c0c0c2103081d004da800300105004071800724110a02609010036151300b000d006214103406c10f0741801a04051014184d000d91a0104100c2042c0031101c0280c0b4250b522145454807007020b5003005070a03182c5000b1540400c0061811451078010080c00e5030403c000d00c110250121680d6001c1142158035209101064000400c40074003400103006100001c0c5014003032600d0741e050b409000300845540b480c8601e00700076a181e0542406d41007d030610300040d01d1310b05c110300140105880d130044290f8400c08111981007000000fa8a8182c1c0c0083c1d081d5088180c000c0041c4060b800241c5002c160008031324800d2124500c40d50b400c284a1100d40704443d10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 995887059 1250 995885809 995885843
    0x120f0111281d030109050a06021308010525090306020304050a02040515090a0c050912030301090b030a05060a050a091a0402040c090501021917041202010e0109030206090d0222230103020d060504 85
    0x1134040903100445100f60041060728000503442b5040f001041400c00a111600c1d02c229070102100b000c070591034985e04030004100348a0b20071000c0b000510340c02a0210740d6030400d410420381e50305248508a108904040014036075800f050701c120420341d000b0700844896103900100c8405419641185405c004d41031021841f0355980301b03c42048031580c90301456807541000482c00640d030301041898007d502410390080040c034002071140e4480e645e08000101500e8503802c080161000700f10103003503181c244080302d0714107030b00b800300701e008902c225010402801c0c0e48805543c03040c598451240980c03c610031854004064600d0000103920521501d403101e00840e0041c0b90030307002078102131070011002440408650f00040c41000c180000d08113008030780d107941d000a10303605c50703003c8490003082034101d94030441d01c1c0d0241c1c1e0140190098201c544003001502240020400310a08040070005070042e55030b41404481d40134184e0350060a003607950041c584541014240107042211981107804000384 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 995888309 1250 995887059 995887063
    0xc02090c0d0c080103060b09010b0d150f0303050307020d091d061906110f1203070e04090611280c02150d060b220f05120f0111281d03010905 62
    0x4602c4190b5202c0d89115410340c103182c000c07540101d11b59402845c000005012040105041e184142c92013400450700000daa0404141141c09a001d0a10003002070030100416411030041d51040381c0d164201c8903d00304841c01101c01c0702080c03155050b03811114420520003a101e48405501100203001d441e81058801450380481402d03512080010b0b041031441c488820701480204c07540703070711035000303040c0d0007007034920200188400740c4410b00744203010320040b07100d0301ca03900540c9109410a4003004042d41d03000142c042a80b0041503085031a10505060f41420901b07402040405200c1d0354400c854080b560034044d046e10303d51060010140107002560405100d4043da401401d05540700d01d4907401e001c86800d507030051b0040c0902d40881ca00300d0511440301c4403207802d412280100d651141b5140703466149410300c0345032a54050b10f5401d06103c03500b030b039001d2001414244071a014242000c0300710202c04d808903d0519803080012000400038a482c1401006000e40a10003400005c4046045d03540c0c0b8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 995889559 1250 995888309 995888321
    0xd0f050a0506042108040c12083f09070e060d14030a030b04022d0705070f050108060603060d032019020f0d08090d06020904090f050d020123180601082104060c02090c0d 74
    0x80c1080e0706001c000600f0083c86150310ac14100d00c000e40703505070030118045519002a4040c1e00c9088030490300150a039500c00b210f008016420a401000e0800005050f07501c81d0300521050000c00e05144240303500b0305151080b5040078229a24482d2a2b040101340c4801100981055034211181403200d14007041041c0034440017041c000e074603400c42510300310005d4507000005040c04d01c42c00303003031042241d070341c031200010350205d0380c58503001036580c00700a4100c5400c1155200a5840d11491248030b200008103c030034283c040c02120121070081e01801040001c1040b50300040280409104031189800c001b0000c2d040103200307034000350421300d1800101d82184e40d1154291050b2918800d11010b2000602225a2500c25403000344039403907400029640c2c1a10300301c10421600407940010b40d246da030b1080c81d16650804802510040e5a48085a90352011851200048945000c0341c1c844c44415940855046039081d482d03022106045400b0003150360002400b20002c1d00d420410301391510820700c510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 995890809 1250 995889559 995889607
    0x30b0916090c021e071e051c08130e0603250605090d02090c13080304080304051e030f06070306090218040e01090204050c070c080c0d0f050a0506042108040c1208 71
    0x10b0000619003e800306400046002c070100184040605000c0b50308d0740c24441010020721201114040554541070a551041c2c03850111100480030002c10014064403030a4000c036021000c0300c5600400c005500c883c07410884a0409140d00748200300207450050005d89500c0c2d00051110b40d40c20b10580110300074100443d01c004d8503000000305401c02100b4480543c0290403048001e50426003001e4146a491040b0f008140c0301e000c03041d15000c50301d2146210409124400b4080c0c03405890b03180130084c0d45101c25581200031a003008004145802c10b0b209580c02041042056144001940c0030302c4010041c1c060462043e540f41c05980b00580c485002c0d1501510644482c83e0b9500e40904141c080b4840c2e41d001344030140c0003400002055a507444550802a801c0101028600302c0b9160543c9010007403003009006018201c03c00c018801c1801181d40709200c480e07900003501450880884e40d040d0201c8000b000803a080d034051000e48040c2440c41035540c4175903000791401d10f0b40d0074024100b815550310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 995892059 1250 995890809 995890813
    0x405100504210209061e0a060306050111010506090103020907031b1809020408030421050a0803040b0603160e0903090a0f080d0203070f0b0703060b070b01030b0916090c021e 76
    0x40102ca0840a441040206966109000c41d645980080c034078200c00b5140501c16006071030340400f200407044410408203401014005569a078190203405000c0070701c1514040754510815200103034041c041e062080c1e0004240b038001343c2c03d40d400c00c225091f02404040c02c01d42e695080608580c0c500c0d85071280c00d6415111181612640d5040143d58403c640000d1107090051100700301c4d00070000203480588000c84080d0342d04414020305185000100200a0001d02c19280a0818070510400550080d405482d0515459580605150303070f895140b5520840b8811140341004400c04003e400c5800c004101d040e1791400c5841d0000695907021908100c8008040f0541000308000401c906c0c1500c0115002071402d00200c0d0b190b6030a0041b4040303000e040030100b070b00010701c654480e510202c09001281e1308a900c0f0151801d01c40d201c82c40034003044030180002e4001c980142c000203803800801c00d00c503480c20030b07032810300f0302c94405851488211400d51040070400d0f01d1443c0501102c9034000300f4000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 995893309 1250 995892059 995892067
    0x60708030f180a2d0803160201020c10020304031202040e0609191103100e2202010c020a0605090405010b190c02030c06030403020a060b01030b0d02011b060f06140f0109061404051005 80
    0x84c4110030300c402d542c03900c10b5480c2c1c3d0303901500181d18003054070341c4143c16105001d482091540168003a10a45400780b03240e0045070200800000598061805a0301070b541e94003d6010260030141244124003036043c0e003914500004005140040c0700130b5001046105072440c000c0d03d1151032043e950910741184c0085808000c1200c205035101c0c80c40010b242d1840c01c0500c1d0701340307414801121002040700100310803658a035942964000c0398000031099001c0c160652940c0d5800740100716401001c0701500c01c9003442c000003101c1203e001036400141c1420940400061102000d072120ba0000c1422a058020400d80301017139075440010750701c2a4001c2c3c000e0100c2c44624a0031004031401950418141403402030140c10944600d003040b10341d1036080c00c006024246464803008001654140288200d0802c04c0c50003801d0303400d8202c8000c0744c44588080e450764184c07008200030b00a10b41051070028801d0301042202611640035101140c41b00405030303213006c0d100c03004201103a0b00822a0404140f00003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 995894559 1250 995893309 995893343
    0x9020913020c010b030f0a0210050a0908030d0608100501050307271d07060c08120403030e1b01030c26060d0605093a12060f081b060708030f180a 64
    0x40306c029514001031020f0001c11501d68001104045401400300c108140460715008082c022403002d0046c8c40070608490726401c001e003d4201070600d60180582d50b0040c0000e01c2480400d500825068810040180002500b01500110b40841c10304801c502c40591400101c0c0043c19407140000482c16819000e0f03060701900219031410030141c0c400c50801018094003004101000300782d0f205982c55440c01032003031300c132820200c0140c03078100d50002c041e00612140e00441c2240c2e9030400f46001007038805000340c64038124280c9180303013820728500f0320001110100c111955041015030748604010815400d1013000c0d201d400486404032034100007170b07000c07280e4100c0c62a0441d056042c1c0f9003c2004544090f015503124480d025401d04407901407048402210b413081d6031f41c0c2c006001401201980e004c0d8035654001c4103a8421100038040e00201109a103c0194103044c81240c05e1150000107192443e203a41d134054001000003010a95441c2217208403525189050001c7c04529000710801c0004500c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 995895809 1250 995894559 995894563
    0x21305180f070306020904060e130209150f0f0114040e150a03320f0106170304080a080f0904060e040b090102031012020d0602071416060909020913020c010b03 70
    0x3500400c1080d440460400c00a00c0002000b0003629030151025807105400800310300034005e607800480c2c03241450020080c0f2400d00d4903003001030038002c03114403005031180e11401c0a03c100342c2c00d55540200703940517904c00505000d044100d1114041c9071078440740103400d44104a40d0015044550441e545009001c03c06465400c0b500070242c00300c0d0400c0d821469683e9403c000c0940310390500e40d5641111001ca510026048041c540759130200c251a00c0481ca00800350081c00c583c040e280f40a114181c031b4003072400001050710180c40181004046c448410385584503c2d40001c400480200c104010025071034641d07000d030900400000c400c0b400b03d403e141c03034010a004402000c507021603106008000c0303150b803803440010072504546081001e146140c004901c80d195114009041280009141d50400611602000c0d04184680036550070a6101660b81e203a1400d603c1010300088482e034060200f4050303603004260b040801030440325030700d21a1040c44243c1e0481300d01c401050359117501c80358440c102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 995897059 1250 995895809 995895841
    0xb07020303150a050d06090f02060c0a14012c030f040f060e04151703040b031312020606060a14070f03030e2401090e0f030d0c1716050f07021305 64
    0x44881201e403c1c146001700d40315103640ca001a0065444850784000d0052420308186120b801a2000e41d840c00c401160b0b07940c80301000c1c81211403c5188806102102041c812401084201d215280c07920300c2c02104865201581d10301d0707007060b000800c0a000e490060200030700080030740b0041c00c09140e00d0400d0291181c03003428070b80b500550410f081510391454403d1080240c80d0740d16107000d02641a00b4416203540107507000081903040001c2400302c1c0c0502c052601c192540b117100c40600b06200c09404070f84840065138102e410100521484031028081c01220403650620007120742411010307113558051032803006059000c00d0b07860505104c00c440601040c80b840e89425a40351081c82801c04160aa038014411102c0141d81c0d03604e503c100c24401c0c0085540444240122921260f0011080307000300065082c51021503105020b044002c1c3c20201050b124400442405c0903400b062902034489a1001e009452060001c110356001a03944040020202101460005440c601080601c000c620 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 995898309 1250 995897059 995897101
    0x18130213140c0d0204180e06011208031311182a1e0403080712080a090812040c0504020f130515161a070309022805060c07030b07020303 60
    0x200780740c41001c19100410780d040e00070701d1070410a80d55001c0003903104000d024a800000c88006000b4410805a80b41d130024002c0c0001035007502e4150341d80b84000d20488800050040030003400348002001c805038441d40c0e00586010320f20528400760700d440001c40244402013402100c1e002c41051080c8120b42a459441c0303c8034881d203000522848026030710b9076003c0c03441280848502850039100040b02a426100190703803040041d900c80c4003500d80007a456680406820004007504000b412108072030061221140d080b50301c251a0002404400c04030300c00040c01680c003169940d100062503100c0388000d10346c60004c0c2c40840d8a906055207040b40100e499030009226003100c0380104144641c6504907080140c200700071070006400740c9040003500310f03440d120b000da03403011404106020303800d6000420361070702c00c460084040f0f00d2409040101100102d09410304130403003909010500741000103080c80e1482c0780c100d903484d950f0399071003091400c42103a0f00c000580020046c840350a0b112907040d15096 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 995899559 1250 995898309 995898311
    0xc09090506030a23060415050f010b070609060605121b060931090f060506041b0e01020c100e011e0210111c0b130203101418130213 58
    0x2080441c0000d90303502292201500e0309141a60b4a07140840d6640560342184c184001d5400b14038203420281d060000075444800303150700f40781c0002c2c610310b40001e09078180d44c5034558042c100302140d20f40f0402002034410440c1d041e99100c8012901e40d42c0c104140030201107160041103440105056000512030700b101d41e074020b05051100b030343c07035980d039000941c1c521101c0ba007121443d500085400106814100c04001d0041c6080a2403080c0407503500c800d06014001c46003400765849001c00d0004840e1171a80e50307041495029489000e152050002241d99041441158002d86611000071103000b00e102d000300128803112260081543c10202c810401d20b901d00108403000380070724001c0d440715004d6809103561a0307550a0344100600d4281550707603241100d10b2005100c110070070190028101c945643d4030400c964214050f00c0700071070080301d104852038888150b07403d18224032944460304040b1196408100d084a41c041c441c40d000c0168491031001036000d0010b1114014844000d041010fa12809 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 995900809 1250 995899559 995899561
    0x5030c01090e310b0708010b0304170c0c091009050108030703120b0d290a09020a12110919050c030f0f190e011a03010507020601062d030c090905 64
    0x103000c2d060882c0b540b0104124520b429840c40d55a0080035605260b402155442d09400090620600201c40d5200d00b00a40b140c3d4020f980f1048003144c3c1e030008032030060200d80b12414019003041c5c900702502c40e400c52941159070703240c00940010007100c41240c1c0b4140381038059208000c940c005000f49801869240c1c081e6251501c5500d00030900c2c4910401c00d4100c503191700180390b4913110707406c0e1600030075040f0461b0600480101001448003a1440d090701d4003104120201d03000b25001c0c81072412203079009103c004002d10700300c0000091248080141d40c0071001082c40c108076129501014868581911881e6055401c80400011240c0140500400020a00c1002880c054942840c0e810551803c5240361554480d003a070300502c0524007140380c1076410400c100341d281105402500c05414102c0c00781000000d42300030b242c00c80340704495030b200589c00140100f1030140030751001c024240d00da0340c0c05030704070036103041a429140c0e4840704480025030b50540090040d034400c102c4009061103c50601507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 995902059 1250 995900809 995900819
    0x705070213110904050c0a0207051906110a0c030804180b0607030e0d0c0815060411091c0602030f180a0b1915080610080606030304140d0605010f05030c0109 69
    0x3150708450451540d0386498074480720104105907010210024800d2102c0c0c0341c043d001d40d03401d400c03084a42d009482520400310b16440c0c0008082c0e01d00010101c034048451601c00201c2d0b82980c1c4001da015580075042c0a40080f545540200d4080c5000b00b45959541c0e180c00324010210341d048100a810628040c181c41c810350b211412a034055415250040d00d000010001500d440d84d5140e00605000c401d060000f10b11102180c000c20300030f115440e208075541c960003440103551045140c9a40002c08212511081ca040302070000100c42000c3c2c0c051034880c1d150344c0e0748100c0c0c0c0b065580340303501c1503c20700f040107a00507160052554034540002e8003101880c1c1d900c64292000282040840001000300c0002d5800300b03030304c82c4280700711b1160809013555852210b181c03288820b940031585610410000300701040d0001e0809c4c041e0f600507004500e040d19208030340690318600c0e0390459118002105180c0400c1003400b9190103444080300b034902c4249403004051500151b820342e2811301c11480030400c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 995903309 1250 995902059 995902069
    0x503091009020118080f07080f070510050c0102040e010e06010f021c120510030201170f07050a05121f120f0807020402130b0705010c030608031b031e1207050702 71
    0x100c00303010110081648a0035100594102000800c624401c2072002800100200002070810700301c140d04064841c1703d5214800c19481305200d0740c1c2c001c01d551040c4010401c03800c000740c803682864090314140341082c444204803800e903803059014400503860b0300010700448500580c003d42004003400c1c04200060310a0001c1c0d20b4004103049806440704955200d4400750040d0713124540880c668804000c02d2074905c8000081c2d141c02e00050f03000414014010b090340701c808010501480c6401d150600d2036403094801c0b83c03607a01c1004280c0c10130105001050340805203200d2203004100303034401602c08030741089588070660110b9002030f1164aa03040000085100c1884070360016030480c40e016139414803400820080c2c82468001030100441080015100700c0c001c007d4424944100000d0000221241084059400d1030280e0200781d0000c02130b190070111108406000b022120742500d05101b040032460020380c18401c03a00089030000545041e08100c80c0c6900d99015141d030030040e080400c03030740200d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 995904559 1250 995903309 995903323
    0x3030b06070f1502040503010e010f0f060302180a0212040b18011a06070c080703050604170304120c1109091e07060f0f091a041401030917090a030c0312020d050309 72
    0x6080d2080035003010700400021340441700500806002844541035500c13483d0b0081c03807624902c040700d600c0e1409501c07a0543c01d02900040301d40090400e01e1072610b0050940301080f02404521a19608202888602ca41e60b076289126601640c0c030000c0c1d914100f50b80604048983c40312501e164508410190070320303040d032000c16000f0300944000b5210001e42c9000640c803911074110302c0d60380c8078405000041040000f0403521a502c070300c0c248413040d08128207004882c00144d600a00e441d4500c01c0410325180324040c5001b0440c0104a00000d03481c0b03041c0407640800781652884038503080f14201c0799111600200200c00c264490004004080c5824001402c1d05141c00d910010041d0a84207001020b11540041c0054507007500c001101c014407020b00b060fa0f0b402031080c86141d2207514070b20803540d8041d116030005182c01140c80725074450b4165140d0056030000780c100354050a808000320106141003031140c0510320403600e0000701032550f440a490626407101110030030030100100109045c01280352 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 995905809 1250 995904559 995904563
    0x2010507080a0b0a030c0b0405100c03020304031e061a041104050d0209190515010f1b0204022203060527030f0f09100306170d080c0901020a02060d050403030b06070f 73
    0x4000d1503c90019220400310b40c030240c40c101140c10041030000b00e0100500c2101e004807000141d041640c1e1040c0c507520724207800139002d03030014081000072404002d60403803046403041c100da24451503552070b8003c5500c5001d4801d5144007591250700d00e42080c2c800c10003110300c801051400c151514001172002e10b2440d00090141c4048008580e500010884050001442d10310501c00b0b4a00008440c140b65004100c090000e80030603480401c16001e01201200001002c40384e030b2080344289c0901020754002940822030b00010b00841001c0300d450035040c1c01961007601c0208140c08e10400c600e1030a030b6103140040719405d02007003043e8001030010484901c410940c41841d200c4104e65800001402407813622604011200c44410850f039141e0310075410340700b008059015039410000010364860a501001c1b002c54000b002240580440030094501703000144121000a4400d9010500d580c004440365215503032241c042c002050781500900d40a040141e86080c2454440d4440300c030492056040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 995907059 1250 995905809 995905811
    0x1030609060b09071e0512070e030705060c0604060f1116060f0501170609030306030c010e060d020f0403120f0c020906040b06031f050d11010807030603201002010507080a 75
    0x241000882e41140c1e5100c08001d10118051410100140410300007001160343c01ea41488500320345402070050b00e245810000b00c101441d900c0c2a0300341c0d61344c480c410300b00c0da051080b4580010565035080c001c00c036404000019100a05107841c0c600244d8a40940500a16042c0aa0b041e0414200d2060b1904d00503040c005e03c40c0101541001c10013010300f001c3e048681400c0c07074004039400d20317050f200140483d400c0c01251203c1c4d0740d40080e1500c9000c00d540e1140d0507000ba0000d08515071040d0b04d121080440180050710b010000d19551049034040c9a21440300c070341c00704003001400303070b8200c64a0b0b101185003452490003c810100506240038440024031800d1204085112034860b6404002c1e000b801410a69a0b03040c004000d110301c0000b149040505220200c0118060405201101d42a5800340c10460b0400c16400199908400184401c0030103940b41d078000b01042c2890804482010358004449036203100c03000f0b110003d020030180c18256030400307050120390355201c01c10030361003c15420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 995908309 1250 995907059 995907071
    0x20309040e12220306050a0504030f020d1d01030e160f17100504081303080d0f06050d0222020d1505060a0e100c080f0a020106120b1b0403050102180405010b0909010306 74
    0x2440728040c3c2030b1a000034168514142c10003002c0c0300e00f507118a00860298541040d0441200c0040b6540c500c0b590009000071144d1038000002c80c108801c040301c1c0c401c14180450814607a030315461900e00080300c6161680e066000070407191189040107006000b4955071941c41840d03000c11940e9802120f00d000d03545030f64690000e001d2000400c00e443e01072602c200e030203149030350b6820b00b440310f0342110300f450030214a00250748480803114850141100d0010f41110744845a40c1c003000ba201a0544041c00c42101110003190940c0c5039200800c107403e50010000354031450203105441801c4581c024502a000400c01a11807603008000c46080e000115010f40c0700050141c0b0841c0d84d4600440c00901104d4082401b214a150800140c19170018982c001c0041c030350341c3e0030b1000740c20300310701800380586c001070300410384184142d01c401c442085011007103443c01e6640c1d652603003281d0101c0b030700400300b42002c2d0300705581e0320782030091600601200f04410304103031206000032010300c0184002010142c4e20303a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 995909559 1250 995908309 995908357
    0x3310b0c090a0305030711120a03080115110706230307082e0603020c060c0702061c060312050a170705120405190b011d040308071805030d020309040e12 67
    0x7002c0c41c060750f8488141d80e1581c01a1410410b000ca11401031442818804202c101400340005d45a941681681d580846a440c081c40807a501038105100d0040081c40d001c0550303c46000c0207010018489561140140c0300b100020301e001c802104d9036400c48070350070018841ca4691003241150060303280c0f0349408104070040d030f020510664842c000410348600b41800a0901e41580c05400c0032140101900d0346a6114600040c6900c100c42000350301802c01c1c40701410f460011020800d5004100c2400140592070750bc80c0031196142c0d440765400501e001032450015907101d40d04820640303400c0d100744001d040c902d00c058814052500903001c228a28070009048c004108981140c03500a4104541940c0c182e04003000d46103404d00840320055910100181c00c3c00c600c814451041c3e03007642e2400000c2c4c0750b0040444100c800d08141c0e03100100801004103955801b44800b10303851140e03400866680000c03105105c1a2500c041c424011a00040940e207145501c44045902090301000781ca103880b003d031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 995910809 1250 995909559 995909569
    0xf120b100818010f0e070503010509030a11030d090f03020d02010c090b28020d02070806130b040809041a011103040b2a071401080c070c05011b060203310b0c09 70
    0x2c44914012036080c1190305100d052135600061410042d04103641d02e007501d920906090383c0058554100742d5200700304141c0b6007486007200001e4034488800b942d07d004070011015040d0b4815a205440301e0022988400030150100900300c1c40c41050700023400a00c0615201424103c0b85100e40b508902000414200d0803103840300024020307411000d1000400e5659200035981e8002c00040720140c4240f000100b0304940001d0000d201701001d2050002805040d5189040d0b10000352045440307500a105080c1c20760b40d18040c1090050301c13404261022080340380010403030b980a500110f10764100300028003960020030115401004000c004100f203d4255500b010b44900f09039001c1101d000f10440804c000d05005241154040241c1c0c4940e9540c0702c41e180480c5510070501c0003010440480010007203075015054907200c65100a5180d4001183c64544405985c0100d0307020882d002e000401481c4103244412103851310700c400d81d001c90455a59910b041162030050042900b144010411306220f94807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 995912059 1250 995910809 995910841
    0xf10030f02160b16050309030708070314160c060509010e1c020d0c093c022203021305070203030406090c050a180608010209010207090f060504020a0f120b1008 70
    0xc89540d4042d4010541850071420740f06030f4203088008030102508440902c00c000f1381c4d0091265074081c605d4002182d89404596110700b200301c0a000012440c0d02c02d041c000d401800b0600480d120341050805246001071600403160003080a0200c14480030446903408841d400c0313020402d550382200080d80c01e202c000341113410305009501480d003102e5442040302a8901c08102d0300f81100c01c0c0044140100c4042c03180c104800300a8107900d01c20f8051003951000f400355100d400081a00510701010b1003414622102000405101c0140a44c010411410142141854000b100f14100703e1030802e183d00075141d05c400f4001411a07501c0d50144014816030040d20001040001c240399621680c2d54500c4898215801e00b100d0500d15010000604000c1802206c1c0400c1050340540412420401821b00914900000c1c0c05407582c1e45001040782d454078401002101000c0d11074407910b4480c00da00074001a0700c0300745900702c50b041ca55844c00c1d03034448401a1340042450b00780000e05a0341c03084480e02c8511 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 995913309 1250 995912059 995912077
    0x12604080702040c0525020105030f280b0f03012a02030d1d0d0c030f050d0609090605010302032503240c030618090c3b0f060f10030f02 60
    0x1180c007200076100d82d00003006103440f03180c040489503e454400420380040b4106e42019010403c20030010761050904107820303501000300c01740b9404440f00d240c02c81c1e081111900084180d669a60208034041c50606040b0345003180440c002e0000c886d52281c1620030324904006000c460110202090b4003e00a005030750840f10000310401030b108561190720491240300305c203408140284860000146e10580756428095019207400403000d600c04000c8800e5402499400c1000c3d0740c860001c119180d0500804000d01e00070303075020a555041d801010b041c01d2003540503201c080680c00515081101c002c0101080303a4021740001814445000200b540c0c55031190317034020013840c05540c0b40d41160940e001c08103a50400000d500810b80703500c0701c07204885100002078000040e05d903040002c051802c4100f0426459114106425504000c0d40210302c449010381a6170038130140c041100c640d41200400e5401a1b040782d070307000c000e200c84021456000c00040c1c95010180c960300040104407441d0112940c0c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 995914559 1250 995913309 995913311
    0x406091415072d06050906090c091008060405031b1b0105070312020c070f0512060a15030b090f0d0509060901030c0302040b0f071b03051b150d0b0f01260408070204 72
    0x69003a103540305203400c0f07600c02102e01c5490a40480c2d440040040d12510a840d035100070702440c0180c034200200050000c041e10382d03080180710040b40c3d500c02404064081d501c644000c60320350304104142c03100012006c400d040079030320805c0181d0103482c8650580070080000c0c24802d0f510250750508441007100c64140041842c00014003454240d000a000d00c1102c8a5811303081e81c6036201c0d401c10500c10100d0620b10030030740c410404600712907840e902c0700550505009880d080903550307a0b1458800c0808840260381c50700300c0d121072103d0002c140a0b680c500c0c84589013051400d00700310000340d054003501c20500d0405a88071912034000d402a4125030103002c0d04085503071540b0044c0d94400899120040c101da21502d1180c80c13103071101e0141403010a50794450040d080d280511040800c40c042991501ca50013902d4200400040c130840d801022001c0080c00f022488040c0700081c8100b079400d40310000d0401080d65040070319020344003810300b0041407a5660041a8503641800e1180b07003e41e6801950007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 995915809 1250 995914559 995914613
    0x3050412050a050d0905130b0a09141e100308220b09041401081c03110406030b1f0905120a050706080103021309020117180f03040609141507 62
    0x101c900001e10301041c40c4204101c9a11050050085400c01011b10480e44c010390001280c441d00303042134100290362807002e403c203405c0d5960345210343d054410806070082c07441418002c0c8543c07040000c440c03140644811414400310300740a06800d01c0c00e240713444040c045141c080f444d2044061910318582c02c3c43e544511a6034001d46910442d445940705c075040394800c0c1c0c503100c2203152001504a426040710056000b070b180040701b814000c0300c940001c0c5010010150f4980c6e140000074440f101403c060301142d500069541980b1045c072a8884420900242203e91011400e107100d500040c884240d44050302d4401c0d4101d00b0040e03061402418410042c86401180c10200e08190703c081090b040f039000310703807a031110150a605101110391070440a4005500e07487c0035014051002e401c2500400e256424041c803942142c0c05505012a03e4600c2e03040d42c00002d000c000b0b81c2d034051400c40180074000c00703195440341800009211030b40480c0130400d204030702241e01020b0045008141134a540c03c10700b0b802c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 995917059 1250 995915809 995915813
    0x10b03090d020a050a030305060d1b030204060e06100e0105040b0705010c1b050a023c090c131a1b0106061d030c0f06040b040b03090c15030f0403050412 67
    0x1064008451280c6148a5040c003524264800540d400803da040800f501144085480c12009411300902c10354005440709075880009006500d64030100d4039414103490f0440c05d600c1044280c030301c2035002c0c15080241c0e00034080c840d0342d55141c207505802a41840d4004441c020016250750207103900c410044440031030108103000041d0018081000d01d5543d201503000c2858008001d0440c2c62130140156002d1141c000041c1822441d01c188a8080c03010120442440d11194100a0409076200112400c0681c11401828007240068010090091050800c0c040c461514602109403048101c0ca0090700324583c102d410075012104411510204803003040c03050b02c0072a01a01d0b10340f242000180a518260214907403040784280c0210005000d064828548010050800c0d41d1a8405500c840c0401001801460400007003004102d0914007640300c0c030b0170002080c18050707503c1c0030a000d010010b8410b42c28002c1c4008403641714421841c01c940b030703841700d0034201c40501854200700440c071a00a90b03601 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 995918309 1250 995917059 995917079
    0x3180218151216060203031306020c0a0212161a090d0602090414071106160804060b0604090c140301121e020307061e020c010207050f0d0602030403081b090d150b0901 73
    0x80c03c4001880725031145a5648822039480c48107c6079000784042860036000060001d800900365000c03684106d0b60018441c4c0c0000e8a04440100c8501e00b90780a106020340c0180020040350042c60030205070455011101c00e036800328030410701da00d881a0340411404040000a505464072044090030411403001401d040d00e8a20200b03032185d0010424981c618070b12000d002030060320400300c81028565840500a05442001014000f04c40080e112159111642c984034040e00081000540114812003881c00c003030050fa641300380d001000e82c400c1005025900c0076440304000d256000c80901c030194003204010b200c840141c5c3c0002d525005242000500503444522055100c14030006c00c03691507000030040c0d039600c81d01511140981c000640030007091801c003150548200c00500030000b07038085640e40380203ea1085400724049aa04024031031100c00c845119146078060201e107038074015016001900c45d004c0c8000050240c40034043d02c4000c0c40301038000e14901c403805094140d0a51711010030003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 995919559 1250 995918309 995918323
    0x50a090b03180601120503070b07021005090c0a0515030411010908010e01061a03040b04150e060f180d0801140a091d0f1b12121801031802181512 64
    0x54540c0c425900045168011183c80105d680d5104006510345141aa600361001c4c0000700303904154064454400c15900c800d0044c54450062100901007200406040000d900c50036084903000340050051503542011003c1182d030020342050740144140d0281004031001c00d09908502c01329424070130b0524031400150032032070640c0d200503094104821121007018550004881c09840302d8054004500403d0380c2c003118091098171304001143c812181400507240c0b910540b010800c1070146410070228091100b8401c000c10010310140c2072507031041500618041060040c0101c9051848406045945d04203031030000b807118000030310090150b6030100007100303c40380c103d8029000340c0101c0c200700c0101140c941101560440019810900601444407424114010b20101d01c41e0340100c010b0080350102424629960310800e0030b000c0e46d00400102900c185d8040158018040b2180e4801aa1402000c2c02c022084814444040d600c031b469850120852002054102070f805015402d4004049105 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 995920809 1250 995919559 995919601
    0x40b061909140105040e03161707030c020a0605040f06081f0602010f0e16140d0f0b07030e0102120103060c020c27060604081203040c0f0e01260c01050a090b03 70
    0x800c00680ea40e1062000340c540800070707031b05c0a0f00104100d01d6509a0800c00d034075104d0160b5119184150884000090359100150507004aa012040402189080c50840c1c1c00703090b152901504252802d07040100b8082d05014140034020a078000400400c46010004c1c2a021907003aa142c0d0305a44060281c001d0544079103013034074141440085040c081d80091102106040c070741100c1d180e82d07e40783c0101e42c400c7c81c1d03c510942c01041c00300200c0104880c404510030140c0603401014850034042e1010b000c44407800a0110749074014003070b2840c40700302c8101c12411070360055000300325001203503822800c11602014003540540860104141340700422054241c10b18015101d0380a900c46000300002c6001c1c44c800c0a4250344004c01c122480980200510b800c58414000442030340d46900403070a8a051079045940600f4620700108011078000c14101600707401a08582c13003480c0748041c5962038403138007e0324a060100001d030303542c8114440c4800c00000c1c0f0000480b9038880c1080b0301c100300d0340005c1c0c1d0b140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 995922059 1250 995920809 995920841
    0xf090c030a150c0f0807051b07092405100f0c051203010f0501030213090b1203030a0219211e02040b071214070b10080607020c010306170303040b061909 67
    0x2121209900031003101c22010400d07214880244d48a41b0111507581c045211502d0015501c0c03042d0282810070011140500300b88400403500954076100c181c400480e080c1d00c900340b085031007010482d079203a10b200007031107030032900c0d04140c040420101a10a41d800e0ba0f0010b001d44a01c1900401e030000010140d8141c0c1c0100ca2010b0300030b41d8850044040c0e01a103085100c241850b180d040015451b039501c051403851025040c4c140c0400d00e00061401d40c3c10880d18504000e8000409000b501100015503a540d0714034204101c1c2600503950303507800740c580780d910f8150b5540d60b04024215a200030911080201c95850290354990700c5441621094119030811180051501d4000b180d0a019807210700c59404480c040e64108856610380c0104400c0c0603011000035920008042039460040c17104901c00c2100e60010500d154001e00018111006907010a030114500f1403c0b0600c030f4000b02c100e80e04076400c000c0107440794403050000741340d8070b04601c2c000b880701400900c00112006c494224002d10900380d51 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 995923309 1250 995922059 995922071
    0x206250b090304031703090f12030f060a2706052e0306080d050a050409020d150b0408030f09030c1807030506061819170a14030708030f090c030a15 65
    0x4015543c1c025400000e00308440d00140c2010800400007940c1d102c218041111030140401c0e20190a0040142c1003424420000040100b00d510090401e9000344041c1c507080301040c9440c40312038034820b000161092714402800701c0000207140d80c01c5400030309001400e030380c0055441c4104954080c40184950390400140700f0310401503000c0c6c481c24080701e80c420003800070000788400c229080d9004c420044c1c00c3c040203010200380c2c522548040d11010500385070006644c030590091001602456220aaa0750401c01091100213008400e85000b00c45600036141c46511600c00207013403040300c0e15510780100c0c0039240740942e5800811540c0c080c00c01500c0070041c0707842c1c06003072001078400c8401010440101c2054148581059040e007034049038131a80001d120340d1903420540548413081d004480c81e5020142c0e58090003441008003107400440d40046191030340e655984130312404000c000750b015121545c0056001c8a003031203040390230403004044d02c5102c29645804180c4000461000a06501d451 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 995924559 1250 995923309 995923321
    0x70c080a0224090604150f020d1a1e120c0d03020a02120607080408070303021c020d0b06030103111c05100f0b01180e1023011b120c0206250b 62
    0x404014003d0058a0180109684503110050150000002041c0440e0b03111801d44110825202070000060307540c50115160348928000803c06c442c259642c0d00c80c110303810b11851040482410540300030303400e5494183d8554104c80e540e0401c241040307025040103080c0c0e802c8041560114800d51000d00c00c031012020551007140207075842d0340403185040401d01e0040030a0110302c282c009841c001e031007880c000d403404c0516824640c1100c1c0e86d05020242ca40c0224801c4002846406640400c20068603441e003150b1441c1c80c1c5009281458454a0084000501c41480c0039400c444202e2400d4000084070b80c140c40ca0b107410001000510b2406804c01d18221001c2915881480951184650f180740ca1080c107040c4081250b00c0b040c0a8014000c4029202000a6040c20903910690035084d503d0030080000c86c03c2d00150101c00c003500c840540e801e24004440004072000e24184101c40c507407610202d001c0083c4042400c0c0d1051008000c005135441d4032490185101200c03d0341c01900c194082100d9403202 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 995925809 1250 995924559 995924623
    0x402120c0d0e0616050d0f0e0606130e060a090206040812090a06030c0503041211070605070b071412090a0f14070618030201032a12060602070b030708070c080a02 71
    0x1c1d0780c131404280090300e41100d03091080d0040c26203a8452100020544d0302c500001048580a8643c1905900000b08010f81c138582682180c0041c4140d40040c0a2050752041e2a41c54180c02855140c40f10b0341c1c1c081c4107040d500d444065501401c0c46408072441d50081e582c0350340e029000b0b020101d10070a01c4181c0400e8480c440c0c004c198421903036445080c15034a0725681c40d000146049160303003c004001c0544906807000300a468001c212036100c0555032545810500d242c00e40080c0b1003814882030012106030100c05030b040b14031400d060100f1603416101c48201c2070034203100045c050400c41c5121412801c0c4141044001c4020460720100c44c803040d030750303003003500e070034910001c2001041004501000994025003180081c922001740285610f0810b03140305020301e0140d05114002407400d841d011040f95944181000b6040500041c6101882c0c540300c0d070010300c80100002c00b042140004030b01e00c42d000302e09080704668401002500c403142070311700a5455a1041c0c80c40340641c4d0040341d403d12083d20f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 995927059 1250 995925809 995925811
    0xa020d41070501080606160b010612060911221e0e100e010504020d020c030d0603020a060c0804031e05070b09030d030218102c1003140a05060402120c0d0e06 69
    0x40c0c40d804030907941c17041000300d6900b00c04085004001e0000085001500400c4010301030321443c0c40d03500214500207406c034112011a089040641e241c819600071910010080c0c900e0981c0c09503400e00f0360b038048004409a06416403003910382e81c0541c11803040c1c502e58019104c00780c540314040c030162540e2340007a01007038441510031880c21826440050005041540080c604980041805441e1042c1c120041d4030b5a8030201c03c0807201941e80a06004503d0148104c00040c1654504900001c04580782e2010500c50380c400200301406064400081080d03c0c4802411b190308501603030322503960781010801d260b00c4000c0d89031107402206000e20b20b19000e4400d54841c00341841012103600c05110902031006604100b900610101400700341303440c04183da04501020803410102d02a000c0e4a080c444491305008c4100c06041c1065404c1c4422804210034071303807000e81c44402003100e0301c419000c20024412140742c075400344894400c2082c09070f1603034000c05080c96190b608001d4002608059511800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 995928309 1250 995927059 995927069
    0x70b0906071d0a0e01090f0b1f03180f0b0a050912090405060a12080c0138011209030201051015080415110712020c0603090a020d4107 59
    0x2a0759030306005042d00302540c641c1c88000250800500a4a60428001c240004d070701c204011604e440d03040081c2141c80c0106400b001c2c0940342c1c44003035280d000001b44003241d01a4054201360b0b0740c09080351104c3c6900c6081c0b64594100c00e01c089040c2c1203051440d0201021590b1507070244c1404c0c0890b0014600284c07096288009501d86070a102d222001c00000e0b0030003038006580240740300004603000d008031300320346000d134414206541e44001c4540d009007507441c0701e802c4001102030025000002c01c461808201c80c00c0b00642041c070750742e50000040e284013401c140700ca1a420710f007604c0c910070581c05511460140e100407006101680d5602118510a82e9020507200003540b070b00c02040005410032030f0003a415006a40215407400007500d9619260485002a1849a10035900040072601070104042c0d01009031031030752840c585001507a90724021440b0003401920b000c2c0c94070b01401034030003c101c8444400c41560808001403144a5440c50302c0214040701d40125186418200c1c03400200241166 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 995929559 1250 995928309 995928317
    0x30207081f110f0a090305010e010b0a170f30030402030a12030204050607060c0e0904020306130614091c020a1a0415050403034a0f070605070b090607 66
    0x20601d450400c01410b4901001120404280300c0b548450489074003400e4000225036034580c4591031805c00301e095071400f1034580e1459140642c47c03182da4640210f0f043c00d0303035100da9004030090722003801c00d4600003003001c0010040c040c00884504844601c50104a02202d130803041c0d078101e04182c00501c45120541d0020361541c40884194001001340400010a24060a00508250303541e4042110380e40496000c590701d546c0c0d504000c103400d03040f1001d0020854180c80220581c9000d80c00300ba620000235020400740c0c808400444100714054114000d4034464420311000d60030420032140d03444140b00101c900300e2000b540c080743d610f071000444040c00764020003c3c0301a4110070401c070501e21405070091f680498000e8004240003900e000c4e942c003c612170340d00000e40e945000300c451020b031045010a180da5860401034100f500e0000a2903424200e141007680d8803000d51840c180c9420b81005600c421800340420000d051034005014180da5409080720003401d548024040303480383c4003104d07180041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 995930809 1250 995929559 995929603
    0x31c0302040f08060c0a0e1f0c0b13052e020409050a0b060f03070f11010507090810140604150518060f010507031d1908011b02030702211606030903020708 68
    0x90707440b990308031f1f401c0c2601828103401000ca114540d8401d541c00c540c54401720352640d40300002c01174045038050340240300e014801c0c1484a1907136419140d0996502441d04000e005009400c50742c0030000078540b6100055045548550380e40c0d1181c050f20044410b964140d1501d5500303074190400100311140402c01501091655a5041d8103440004c0a80203000402003800701da00313602d413400d00c0b82c5805900c00e81c80310000c96150100851402207c0500301c180d0030b0400c83d04003062307641c20001c207400002c219000301d40d004080341060b090240640c003444e4480303c03402c202050040110496402508250b80c200b03001c1040301e00640f003500c2015401000140022880b2542c40f007868005141440004c0a0300c0030841c00341c42041c001580340d0041e80030b50350341d00a600c0c680b51480004098110b540d00240d4140f151079000910140040c061080c0b40700451000540485014000140c1040d045002d4603001526448020000c24083d0701c100c01620031901d01040c084d100080b0074000b00c036001c3c0840701d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 995932059 1250 995930809 995930827
    0x111e101404080d0207150f021201080c010903081e16120e0904140a02060310050109050d3201050408180f090c0a03020705072903011a0702031c0302040f08060c 70
    0x80d480b803107041ea42e06c0c80502502c00101401c0c000c101c0c0310b071003990001d0f0700c3c1c4459103c2030900c1c0c0d6042c8d00c089030950220074150b9450340c018400740201e0350050740c0140c0320900c1395940e514480000304440301440002588081c2c05040c0d1a0652426000325816124080d0300c03c0c013601d0304040041210b611008910003c0d00048248041c2c010121640d4161485600164040b0b5100e4109444000341c040803980c05020b01c1d40d201039150014a03044840c1d560300d10903070325199129418060036502d10315901300e0458034003603a2480703103418402c0140204030a10302810b08403145c1e0040640c6941000000c01c40e03503d82e140003200392581c01001000c1c51101c0d141e00324603103603a0744600c0e03151082c95000c1c40001c01181003405902d006110603d080d00e0700848241c0007281204102901007900d58040c0018015001681c1c044481d03020300c82c040541c1c2e46554000240b5140b03582d0b0144242e010300c40c800144055154010f0b000300e5410380540e0409540314402191540d0046440615071441400300d030322 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 995933309 1250 995932059 995932061
    0x1020f18040b040f02030a0b09100509041a1f120c061d09010b04080c0d03212a09320a0812070b070804030e01111e101404080d 56
    0x82040c00601c00100c0c00a401c001c00c0c01c1d11200480c0b181404d5000c402c102d086c0065000300001d455048038070004a01d84100007502d00c82541c018940100b61400c00a0b040000c201e812010403600c034610300c0034526050324400c80783c8184003030105c0e0001e0310482c00120b040d040b10440c50a42e030b2284a0500140c00c000c0111840d91604020700c20400400c41c10001a8940c42c80203806018034080c1c055030b45013480005440e2110131a40b42d80200000c0c441a40442c0c1e000c0340120110314035044042501c1c0c07210700003401900d0440409426000e140c54525141c810b141c0c48050f5007021070701c2d1101c400c0d0380c4480340142401c0c2280740d450314502d031480707a0640102e8101c490100f03000041c0b034603420721b031104a818a824401c05c4040003000e0001080d000f407202140c0b0a40d48440380d443c2000b254541560001c0810186007255410300031304000d45000030800b801660401d40c40e030142d108031101000c00703103540c5040482c079001c0c1081c0b0300454450203a011144440c829500300c503407149401407014050f4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 995934559 1250 995933309 995933347
    0x1030b1602070b0a0c021804120806130e010b010f0306140112091a0a0509010c050906090a08061e0109060b07080d1e0603050606010801080d0507050a0203030712020f01020f 76
    0x180c1140a4a5000308034442148040c1030211041c2d07960036003150701c5105004000942d00d071181c0442c1c0030701d020000010316250162501500c00e26068446031600d00208014425030030b548910340e804c0040c81580743c0015071228416100c00d9031a0551b07400c41d100c06074229039840c0101210f40560030300c02105540142140421048004800100c114054640f41c05034400d859150300c6003c04401400a11102800390701c0c0c11004084c02040120719015002e0864403420390154001c041c003281103402a540c41400c10000e10100040d50502e00e0a84440d01c0b000004c0c20b020b48904580c4000850b00b03070283d101c0e6400b511846424a0328041c2c2584459116070858112617001c00d4546102c068402403409076000703049428400030030740f00c0c1180390070350030480010b08982c1009018001040f000c1800100a2640b0030796050140e81c481aa060060a041503118040c1d094880018000c04200c02408844040250f65007070f641c1008482011500740c0c802c03428a26401c01041c001040c005026201007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 995935809 1250 995934559 995934601
    0x2030a0e03031e030108070906231c03050423090f1314071a03060f040203061c1203060e070906182c070f0804080708120a02040305011401030b 63
    0xb203040c05428075815111420750b80c10142c0c074000100040000c0707a0100f081c1e9001d001e80c8001400401d05007920710800d410f100e036020b00000ca03108541a100d844985200e83d10802900c1c251000381140d0401400d10f500904c143d02007202c03056140f080c420713031f030205038104c1c40d00051440e42561103080007100324510280555561080d40f41e42400003c0704400964000b018210141040d00d10386050300501410504c0b90b8980da8500b0000c0006070b50302e0320141030900904503001038803611340501140122206501042008000c80000303010300213000e0a20160040c0340c0d4050103d02e440308010030130380c08c058861901180990000b48a07042c040c1c40c180010f0700b502140b440000d91384440003405004080c640c5980c0300040c1c800e103504100b861151a030f00191905080c07000019100d4000d0401c0c1c0020005003201e0300226102c400c204041c070807104d042d02e04c407160740e2071802e140025000950191008444541c03809172500d000d90404440707141220b80003010198640d4807504400580c138201300710 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 995937059 1250 995935809 995935813
    0xf0f03020309060705010507021203090d0c260d05060301060509192316050a0203220b040609090c080112020f0102013b1606050c0102070222051602030a0e03 69
    0x20406143d2100005089124060b2002003014180034401906044107041c003511080c0040040040855001410001a0401d0726007503040a000341041c1015558180c4d4075440c0d000050254400307800d424016008225058000700042d443c3d241c01c0600b200d0722032040580007895040010f030041c42000c5400a40e240c032010109003910181607101208120a0300000070000d80da00b031044201300d4a00d102003004090405a03d070481224019549000d61a59840300b2500301c101e0b10b2000d07203007905140007440c141b40280e40301c686527100a044c800700c501507480c481d4a4030181c25207040c0310f070035403604940c030360442482c02d56802d800b030110803000740c0c4c6114150b41d2624000204100b403001000881e102d46845007210b148400e1522280500122139200c9540c02441c050200d075a48492600854015003422907440954054290190056103030181d48129100718280000c12440703010320f0450001c00381040075a8030888042c2e02d2800400071440180e00038070040e200c0c02c0c000c502c0c0040c0d410300101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 995938309 1250 995937059 995937067
    0xf0c19051e0301090c030302011a0108160302040f091e0207080d05090f0f0606010210090b060603101716080d080a05060a0b070f030801080a151d1b09070c0f0f030203 73
    0x800300c0d013900c01c100c0c02181e1003c880703102001071550a03c00c001c600318440c0310007800243d10400013040c554000d0040092074846055040300c040c02a03040300c009111080b4020a866a1501420700070304482c1c03c604031a40c0001d403000d951040601c03c80708155405101681840d01595441000300401403048150344030f508515078813110104900079141245000a200314a0000002410a105180142012810071a06100040b1100200c684c0610299110303600c030b40c1d800100c540390502c15401424441c0003148821240100855407016000003407c980800781e583d880d0240ea104818201203001a0082001c6a50074201d60003141d000342c002880035807103e840344150101c0c2c0c1c1c0411401c480004800c2400010140c20960603401044450051303c0c80401e00d032035403203010303d10040401c13150740e41786840c02518040c48210102c0d244580d0440d131000c030005144110802c02e12140e03034441c003042000202d060f8810751141044550028884202c281c0303a61741c155907189035800440650000340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 995939559 1250 995938309 995938369
    0x1815090810050121050a02330304121403060f01030209030709061703031303080406090c26010c020304060e152113030e10120e0f0c1905 60
    0x282101c0c00781070080024a54540092159401200b20007855000308a05000001c03440118145100c01d030141c4421421500c0e2070328003210310340315010341080e0202480c1c116240c07840c904045d41c400d0340f082c6181c1c5d001291101c402d80700c60301e40700d0301c1001194080000458a040c00c800064400350306060140c144818200040e0410415400c0b84040d03581d19441003080041080c00140e9007080c03080550b103075040c200b1810380c3ca401d0100f0040c0500c1140030108040004540c0b000e15010b03004401318102d1500d03052500004540030075450100b41c0211f03080c40d00b40c03106204440c00384040741c000714a01480e00100303440c892100c54003030342e008080440789030f615030428000305581c07440020b2900c003c440c0c001142c02c2c0765201405140b030850041d210748000030740220311500b95040c01c884e031544e00c180208088603d1100c0d041120082c40c2000100e001c3d840c00004c01408400401c0141c41005e031203a0140300c0da0342a004504031140c01141001c205505005900d18004d02c050583c2c503243c1c042030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 995940809 1250 995939559 995939563
    0x604050d02011514031606270803030403080408090409290907180e010914100612081c09060e1905250b0a08010e010e0411040b0607050609060601090618150908 70
    0x2540000046005042c502c404003824100c4904070f0231141c44101155070400c2c1d503e0f51b890100400040c00e101c0f038003001c641404411002d4580c1254028020700c210100361074240c561500156800981ca2010071310902c41c03040080c0b02c9803080744c000005103112850010030710203401c1c0d8000503000590343c4207100a81e00c4020301403000520701404a0450314007144034511b1130129410440d47c4c0f101e10346502484080c10165503441c2e0190050401c6803262084039144188940c000204c0904501d40004141003150036005504143d8003e01601d07030b004800040381c4456040ca80e401411070b0005002500c040ea4071201170090982e002c1280074960341c503003240c20202c1c1e000e225008040752021004116032204a204030b8007500c66100385071110300b019a24111f1081080500314030868486201a1160700d402040d43c04c480e80220403a01d482c240300303c501c0d8480c00c0c140e07902070011b4660307440410303100c1c0a01e420386807204010700107400c598a088950000904040e1030f40c2c00b00161044001854101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 995942059 1250 995940809 995940853
    0x60c010510030c1e051e0301090f1e030e100c020d0506041b030312113c0306010c0f020607020907020610060e15030c0c060403020604050d0201151403 66
    0x1103680c240300c44030b0560411945007082980700842014030a090140c4d40030207100a80100d50301651100203001d6010080c020342284111071542541c80d040c4840103001c6142094015103024564000060354441160b01043e442d01c00d014012441c0000d6a403014244507104a005035198079080710804015070003d04e00c04a00798064400c0d034880c0d01800241b0201d6040c0003101e44030407441c0340942d4510307600988124400701b50380800c1907440d034075001d04c5041304003110046074034400c031041066404500301103a0741d0890f91003942a00d0154802491050303280403603006260507100c410145d00c803a03482d04620380c181c11003260042010b0126000584031666018024182d580151010b480c043e0710300e60001071554003003010003001c50134180740d1381c843c0c5440109041c0d11002d035640d00d9941c405c1000051003000c0b1201c1081c81140108414580d0100300d240c0102e10500c1a181554180d1004078282d03444100e00301130460780c2040801001d01403406920f040d880c00b5003070f1603103690101c40c007104c0e54007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 995943309 1250 995942059 995942071
    0x70501020f03040525050108013524011212140a120c2c0a080708031e0408030a0c02180907050f1203030a050c040801051006090905130b06060c0105 65
    0x40011481100046682010013404c40782c9078890320040d280500080c034000040c0306e480d042031507220328101c448401c032542d103080340d10141080d0480f03c04062620f2f41c2d01d144105603c0304002e48040260b21a0140242e9030488840d10402c9801101e540c680c0c0641f41594100e010078480030340244010380c0c00e04400340c03000034416120503580c10000c4401d203054942d0401c03003030100728468040d221002c02c14020302e0064003510b1803450441b003040700880c400119940043ca030a10400500142c03000d03001005003040000c0e02024840380c0c5c101241c001d0325000301d00801040b070f08107100d4600c255100b50031054625000520480c0003c0c600b015150131404159044401c6801000c01030050b402d00c0c180c0d6151005064030451002c045c501012a16800301130060740c0703a943c035140071460704845441501e0242035060003c00a60034000003103003c1310410b20400b000300d1481c0c47d0000742e44290384241c070311400c1c83c07a00b014180d405070754511201000003019039034451000e010b00720241000f4420940315030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 995944559 1250 995943309 995943313
    0x41403160c0e09010c020a140f06090709060b04062c0d06290102331e07090806130201180e04170310180f11091801050d0305070501020f030405 63
    0x150510312402c00181c0c0080001400741e040103000c1c0e0304107a001030307600c4410307400818055440f040c802c80c0c181807a411440800c1e081c4941428040007400100e0000c0c1155082803040001f503503100f0840742d17240100d12843e00407c01c20030019002c100001180700ba02c202d1005421481d0840c100055254200c024081d01c2d0a0360700c000030050314034128600364052080a0007045024440c0b07000070340d5040315014036004000d851441c202c4106041d5600424a40f00107a01c0c882d0707103801c0f0007070b4500b0b0b51007071013040090303c212001c030380740c0d60180300d19006681720300001e841150f94000d260304120340418000c9040084044003a2002d010038010034019280d0002d4170201414181041039207c9410b40c80d1022483c1308105001c000440e5965581c12200100c8800101c541202c803080c000b00307840c50801c0141c0c0e050010f60018800c44030700070650104101c402c04500b08190148040c0802e0034011542c00030f104e60454070110b402480030b018401c0c8a00d001506d00500040a0040c41d08150f03400c032416 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 995945809 1250 995944559 995944583
    0x705010204091118010513031b150809060f1006081305160303030b1e010807030e15010617070e0616050a03031d011b050d020918061e0904140316 64
    0x3444604c41300b10403c80003440d02c80d08040c1e9002c2d492600080c01d200c010031461175103100000310040a09100010407a8800c8400c004041c40f0000c0c0c6880d0003216118a24020075000508043c4401d00480c000d4160031803000700707141072200a03101700764043e25007002d40e03598156810025404020044582810025100c2110300e18640507080c2c0c0da00c0180d01b486121151240740c110303443c014040071100030034644204c042d1100b0000f940240812098101ea501600c00304140361030445407558102da02035564440c051560600402172940e0039902400002c0c8080002142460004040d16940e50000961405550b070340d9101450864840c00413804252070303206445d60711181c2024002c2184030340d0000c0c4001000181d2039120803100e24402801c0c040003145c02c040e90074072603055074130401c2c001d0300411000b80502048081d025088403072500c2000440e00e0b407600003604071410a820f40d809001000c0300d85850b51010b0784070321005425240d070300c428006c0400401210b090a10751074050502003040e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 995947059 1250 995945809 995945827
    0x4170619180c06090f0e13030c08250c120506180c060c010c09050a060210091e060b1e1f050c030307030b130b010527030a15060501180b07050102040911 67
    0x1500b405c0e81c4419149607146042240402921000c0501c4992524118a202017030346800d10440c002e0b58a4049098183c94180200c800c402c2e0104508a00a0f502c1d40c141d0b031ba540700c0c1c110502e111010010f1060b0010004140e1881c000314070303142241c041405881c0000003110104120b5004244084c0c0103039103031405a04034a41084111015140c2602d03410b4803d130500001039a0340c42640007040c4100d6903002600140090401781d29906117480200200d40c0c1000c1c1820b0000e0104111070340e10641e00055039401c050a0180340180d0810081c150b51540d00d4542e0100c160f10601280410074440d04018500072030209000544c8244070b540c03030010f64004a001030001c046031682003c0010b030b00d0000c401c8603980c1c10070107956581428450401804101d4201601c20500202000760507101c1d000b9000d0402550307491200c014540c0ba141040411b9585004482000316600050810f4402840034000807494000415809018000141c40d160780c13841070400f142c1c550080d0440000c1c2c0030400d03c1d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 995948309 1250 995947059 995947079
    0x8040512061008030406090b0d110703030b010e0f0a05130b04050f010f0506030106170703141504110a090e091c050306040f1104050607061404030504170619180c0609 73
    0x82e00e800f10080d401c050524002034101c3c40d0078003803044c1c9804041094000400306802c4612094a045441c0d62111850310b03024016007803820450b40480c031042c2e1f10031014203102900340300701e1600504040d442450501407100317001002480703003130701c5864060070380301c0d52030b64015680035100c680b6410846601d850005461400710b030300483d02c00c50302000100301c40e40e400303000c0301003a903400c00c0c000c40e550301c5604099004005000c130340800c10309003100b0020304c1811120741e11700c40101a00c051000840c800259641c0741304001802000c030ba864401030000c400c1c0e00c4001680410117004444800643c2c40303202014820110201e8000b5000204010060030103001d100400016604140192400c0d130705148958025405014021040880c0a9092104e42d07042078003806503520b01c03114141481c6c140200150b00034002c00c1110240f4924290501c2c0c000698544620b51b031030102280580074240c17500261410500a0030b080221f449880b0210380c51029502c010541902c840c400f0910f801103040c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 995949559 1250 995948309 995948341
    0x60d230117120906072918010c180e0c0d02040e06040c0e10050c011d0a0201170c0307030b0f040c11060105030a050a0b07180b120f0c160804051206 65
    0x242d400601400070600c1c0b62214816100301c241d101120410134503c1250800303004185446404140c0202030500031250344480504210500301c9000303004410302a0320559542040100841001251080801500640303001d000d401c0841c41030041d141201585400c816608150010521002400c09201240c5842c1c80f0302100f540540c00c12600201c072080011f034490919034500404e0000014140d07404010030360000749195001e825041c907020303012205039560f0250390340490101e142c82d071042c19000441000076205914499510707245941c2d00d00103c003d0403032655119002701600c4000991507985000714401441a03654046d15411070440c054039013481a03000502035041500060081200880c0c0e40044d20341103003074884a03488014040300d0500e4980d417000d80b909030301c8102180c0e4842c510002e00c00405500101d01c6952a401d01c50b141400040d03070a201c8210041001d2058400f2403c040c034600c40c000e06071302c1c0c00d055843c000f26695015000e85070849400020410020030b445243c42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 995950809 1250 995949559 995949583
    0x50903030a121a09401506240e0405040f06060b0a0f0e0a050306010e0709060503240111011104081204030209180703050a150b01020c060d230117 64
    0x1c0305680394080c0440d140c1c0c03002900036038003051a40040141c88002030b0b402d016018225101d500703403410118800c0840682554111542c1404111407400b48060703001f10410744900b102e1165080307100000380c0600741c2045401f10188850580c01c1c0c4c8881d070341d52141a21550096400407480c116030714203002199016000116064024006d000c0b2030784c0e2008100d04401e402c0c1c241081c01400590001d040d02040c1d0b480150f06100d0700b070010552884501a49004914940b244e0785041d848000c00c0c2d0303050008980404400721031500c0504e14070400d50781140c2c4200107046c58810041d95405540c01c0d00c1c0b0048015060410000b820040d200d82000084150075290344001d06250440d80007030180c031405804c04412411915680c9903055040c043c100003994000c0c101c903040101c916210b035104604100d01820303246080c1040000e54000320398005000330081c0464640a00322040c1c43c0144141049804080d0488030713044031800c4000b5569028112500d440c0501e42d083d644c010745030005080072 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 995952059 1250 995950809 995950841
    0x7020a0c050d060603080a050c0f240a1409030414041104060302031909061e05090c04050c040b071524050906040906020d0f0513170307050903030a12 66
    0x610000c18010300460064400840e403450710600c0a061403000342086400280041c8000200007084a810000600048404401f51002c2c1c491003412113490366081e0b005003020280c0b03c910342c1085d64200442550106c0000070000c0c0b903890101d070300c00b0010402c0b02c0301343c4244d000080521510007900c01f904003c1004442c00d100103210b04142111078015841104103264011020a488254107c110a503211960004010005481c1003242c003a180380610540340074082c403102c4007a002c2c507000301407061118a0080000e203441c2c00c1403000501c0001c00b20142e14001340404242c40034114010700c14940a001e030006c20111070f2229108581d0990120049050018401f034038064603c0041d17000c03641b04450000d4070380da55501007406484100d20040c23001e8400a446c044000b0540d00010111340545801c010300c0d96941c481c104100b40004002c5c2c8810840c61085051486400c002e65004070b141c0350690a018182c8003103883e50b001144803401250031115804200f40c650701c2081e49008007001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 995953309 1250 995952059 995952073
    0x1104020c0316050c10090317070b18010b0a06050706141b0703140307080f09060601210b0d03020a0312020406090b07050a021302070501060b030c09011107030203061602060702 77
    0x1034466501c0c0b04209400c042c42c103180d40d41100348a410700c03200b100310001504601c816102c0b070800801c00c20003400300711403404848600c4600e81030344100340c4d48095800300d0080071988408103840c1c401d1080386041a07466484484075140e0351114000c1c04001c20181d21415103d44180c80c141e4252400044800c80360700402c01009401c841030b100c4081c042d020755050603598002030400302d8006091a200e400051f0000041c44240c03680156003c4c0300344400303010040c0d11340381d803100140c944206407a8a80001c6e2a03085014460203424080314107504c05150024a4110b880085080b100380d01e041580503070081041407041c950001746004242e1006101146054105000034049801d107020780d20380c511000c41c9402c2001030412015022640042000101c02854000b000183d8040c1504071036075401e082c1c0000c2c03420012030a0303901130725000c0700b5107040c04c8540004544c144050007110709284101207001016840500005004040310002900c1010b039094001e46041d1024201404641c030800d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 995954559 1250 995953309 995953327
    0xb091c0b0c070c0e1323060106050d0b1e03060709030b0c0f090405010305280b0606070206041502011a0d0f0b06010201020c1605191802030a09140a110402 68
    0x80c46503012100395000c0d51240c0041c10001914111038120384a54103410043c0090365203911405071140c0d100703807008a280704101700300c00c104010005403041c080c1d0281005221040c080c5015141c0d01c10480f00000d03961a031000018032084804000207404446061032411354201400550f601c0b208506204100514541d9449214603008040300c646410100b0340074200747d0180100c0b12010f80090061115517107a06009440e44034035003071244149507240c6044c03090125148281e448640007802c50b0f445684a9040c00801d5002c020201e902820412001c41c03044150b4041d4003240280b90300018078088800c030f0310f070354001c0000d03465446001865202e0740000c40d850101505554000c40000c0151a010700503406801521400c11080c01410b01031110f0003401d810880c101e880480b40c1340001d590714113841c004c0c042c03140500f000d112801d0315524441c0c05103400564114414600006644405403130340c64000c0030307000d405815a0866100a800e01800354240204040201d50451a281c0f0714 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 995955809 1250 995954559 995954573
    0x607020606101214011707050a1e0b0f0d0507032a021e06150108040507090203040309050a030b06030d0e03100506030c041d07080a02090f040f0501060b091c 69
    0xd207942d118014915000005034481d80c1290300d15a0f0b094414040c10040082c03841100c01c0c24060050a00320441c0308103141d0f04001116011140c01500315085039042c6184015523503003101640310070218080c0001080c02824008090903050b110180d51242c00b034112003070903540003601d0481018100f0b0252052204102c500f003010203c58090385515a02622060b4102620002d2680382e10080d080c100e0b08028011604c640b2a803200100811900340400064541d414181c6014203994804a000c0c8a60200b50f4004e42e046402410403007080d5544900040701e28040b6001112010254803e00840e810200084070030f01d125400c01400c85100c4002080d6100d103e06000b4070203544800c046001c50f01c2c184440102814060001c0c002403102c250f04107c2c4c5111107a2220440c8510030700020492004658004a03d9004042040a448480c0c0402070390720050000d031880c1140d0a4001c0000d10b003445107000601c500001c05445501c4902009015100415460381f00e221203000440000c0c14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 995957059 1250 995955809 995955811
    0x1c0e0a0b01170a020901090b01080109181502040f150305090105041509080f1209060705030403020a110301020d0f15140a030b07050f2706072f0a230306070206 70
    0x1841c1d415010b40510410b4510f01031036150040e41140d4108000b04140380a078006041420080c1c8400100381d0b40e0f407035800c3c212854041440740b42c880c100010000200b40940452081c1125480541096114403003410611265442404090f981e2240710f00d4080d05809440c0d0300c020a940200507074601612003a032921103003400340107400ea0365280e48041141c0d140c00d031200401d4900b4420f45400340f020605d81d40d014140d450f131405215110016038014420001c9031301c1954194050405164199a02c44400d6800f01550741c0c503540900400a0280b118440ca400486000e0b2021a009095200380b61603002c0c0c54011106c20722101c0400ca2450b1500d48000040781d50000241d5100d0742e03154000c80d0300d4000c0c0303030708244181c0000443c04800b03030714424502d520340b20780c02210458460b03500800c411480341101c0202002c04000c0c0040030395018508115003003040900b624595100da40020b003180c0b2660700b007400415803c641c02c04a603020307801c3c1104040000d40c020611800c040d031002c0e6942c88 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 995958309 1250 995957059 995957069
    0x901030305090a080601031a0f04080f03180610090c0302041a0d27060f09020112110d0f1a010c200409022d04020306100809030f1c0e0a0b01 62
    0x3000140c1d402c0e842e143d04542800820406055511030358503484c0c4408447c0b81103604800c2c0c113040401141d250341c02104414007e40e48412101e14226881282c032480d500004c00001840c6003901e56071020030b5040c4070044c0b250002004135540d2608003c00b0008440e050602c00e410944180b000380003480710107807088010710030a0015520b650308580280080d28a144203141d080d8041501c003601c203880f64a030003090346e100b0a81407206055403079451040703400100c4042e001400c5005c0c0c1c0000c2e43c4017540206444505c20000510700800910000141c2d03d180f04400000e550760b103200c1d81c0c0380c4030000825601c001c00346051144ad001035101c0100c040d64040b1324000f80b25000c40303899420f40d40c41d030014014550203800e041055080c20a261364442480c0b0383c00b05044007403026940b103840c0c140f08907481520700905107e050102080c0072034912000904091492000f0003251811030304c20805080b44484000100101101428014080c0c0d0140066800268841090fa9000982c103101c0141514 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 995959559 1250 995958309 995958317
    0x60102100c201905030c0705100e0d021f0c110303030405070b22030309080105060d0c060311070b0f06012d2708061506090306010b070525180b09010303 67
    0x182c1a8003e05080b261a80d41400c840e00800000800c040800603010305103a250903207062a56a1090241d010740d2440124006602524274a54030714160f80c20a80040c0050b10002900343e0b415024a400401080b0000200e02c04c02000c0080140120084c0000c01d13042d40034500718241a42d03940c1d40c0302c80c1d034010703014144400b00b03c2503e0328074403600303200d000a1075081012140f0f9803800c000e0145e03030b05d5001c1d21026500b48400118242440a209120b00303502c07514000c40c80e8030b0f20101314003c02c50002c1011041d03000304000d00c0410f08100b2594060900511009040c2c10440009070512004116080d28800d242e494405030503805c807240310084034a030620918003121941008089000c0d000f81895a45100801048129002031040d2180d04c01c0b004079442e000c00441001f80f10300030082e07840d42c0360307020900501c4109030060113402682d100d84200c5601c4c1d80c0c04083ca05191941a05022000c01c174030a00b002404164001c06035401e0960780100111541100425060141404054140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 995960809 1250 995959559 995959607
    0x6170613050f03030708160813020108150604090204050108090f0a0f08070b040501061703181e0d0f0605060a14091801240e103506060102100c 63
    0x40301c02032010007041000c240035207a0b03030300e01028040c2220030266940d4641c0503485a03007049090040d124180100c20b98400450035800c039034011650321070001c00e8040e00420301008012191034400c05071025014088015841c0c0341014001001c41c1e4000b001000b1079803140104070b0000f10042541c074034071500718200710f01014450404c1c036500d04ca500c0009240c1c2e0180801c00c828884194404020f4580c01280180b040c60751240c0036039a03003d11134240c031850404588040c1c082c83c1003941c04d20a80320855000545010850000d1601c1d4202c0401355410005d07200c8010400c2454880e46a00c2207044686e081740c03a08206404c0d40d42283ca00000f401403183c400410400700c1c04103070500803c1130210080c0401008001c40700468050100c1069250189190124410000b0313004d071842001c600741035032005460036051549103d403158001001c1002003180d910700da0b08561300c4070703078656002c4001c00a500b4808002131515810040300200c081c40c1000046106601403117004001d2002c100302c1c021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 995962059 1250 995960809 995960813
    0xd05150616110d05030d05162106030606060513050603010b090f0f0603010906030c1d1f080106031a0a0902030d1d1804210f030f0b1503010906170613 66
    0x1448a814055000d071a4180b0f440800c04000000c00c50001002000d000319101d0010036400e200202240c14041403007443d8944041c85514403c0340300303d2000300c3c0070800307507a2502d82d407040307070300d5500940c00041c000662084070319400400b04008000c107840192841d0302d031105c54002e5008104140744102003030f0300c0e4541a5510207001e040b102d900100155580e59403000a072001f48110b100444066028240018007200d00c078541804490703000d0014001592a0800c484500ca15a0040c030340001000b8008643c0000c04d1184c2c002035403080b401820b05107040702d00060349440c02056080070500b0003011800585000c900840144881c1c00c00701c83c1d110002c2c40b403209208840b0036143c1c0081140307402240100c420780b0268007460240040d40503400c000b00d024402401c0301403c5001042c0044d00704100c1c60305c694425024002401e100080d9404210006a00c115620701d00402d040320100052040740c1a03441040001c04c0000d52540d000b88404074140e0725160010050000007513000401c0701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 995963309 1250 995962059 995962073
    0x60e04090b011401090812030609100306090501020405010e040c09031704050310020d15210c1d01091a0906190806010b07030210090510050a0209040905030d05150616 73
    0x40ca6544100002020360310740d0801c4480100711601c860020300c00800004620001084c5801d807003041d81000c40c078654820b014400c0107030340a405000c901030118800070110394503102c1c141840d88910f00240e603503860700c400100505e1581a51510803840c2002e02849141c01505050490354840070341d0404020300213050b201409594007194050150141d80c4038104595402441c0c070441140c2c2c100a034407100c440078907104055011344402e6220000d4499803544010408284541c82101480303612520303914030400c09280d07000080c5101c461500180042c00c0c0c18003442c0081110640288507800c24140010704150001e45000c6c011945100c0c00c1d00710f205503042503000f608024003228280d595a0081c00c400d03500c100025401405506007000f0210001e000c2c0c1009150020003d148502a165900c002854080e200c491110382c200000080c0e515503000e0300e111707507000c2c1c809940c6030003032070121340180c0350b000b07141a50040903448805442d580d5041501d0400000c100702003c2c40e039261414071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 995964559 1250 995963309 995963321
    0x10030c02160602070317070507060c0809180402090108030315120f06131502041a0a020a1b03061d030708160501020304060912030b03100e07150323010f060e04 70
    0x401d03810800100403862980000f2044116481124040b14480c074900901031140100c402c010708a4000c41000c004061090f18010744040c000c1c140036180411080c00210060401c4800f030450f5010001080198604100702d140100110f1024614624041c07496042404010910b01e00c10808040003400703119080020007071401084c0211661800c0c1040c82d900c0e80e9103540030443d00b07505144074100f0010010700a580850344542c1c580403046107501c00f0241150018010101144110826000030511240d8518894824440e01032170050650810805a40d80c81040c201d03907283c490300490300980300004036a62036400015107a107501010f0080c01400442c040b0241c82d560010041c4020b02c030362644000c0001d4460348400107480401c00307064080e50f0660100542c1740d04546080364519095801c45081c1080820035905160348407603881c0c5210003021304100c00281d6582c80e180c1040071160304801c88407190703020031b1259850b122220719500030368011ba500b0021040885403060700c1700d40000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 995965809 1250 995964559 995964583
    0x1120c051603200f070b04180903030e10020c1510050d2f180403080114040b0a0b0a0e0a080601052b120f050f070b04020d08180405011410030c02 64
    0x60b03010f034004181d483d60b580310000104050f0050940000303005200c40c2c125012141000310580000318014030314402030a0401041d401c0c140c84408011440400340300454800d801000b0058940c0c03410a0300ca890981040d40ca40102d503540c10500503075800720060581100d600b161034504507606490100c21300c1102814014481c0500302300000302c0a15606244426603065810964401d1088000300e4440c1d0180c0b00540400e541d58014840c0d942e0450890170300c910060320102e0031031010b030040f034020300b99684100156003020840c022201e9008074104208901100d40f0302480c0d0038016401e88481c0e040c400d8a00c075101440c02e64041440540034500b0002e108100d2034000c50311410041b80384498042140005800c000c501c2400b140200240c0b051640711a60441c10b1100301d58403030b075480101401c1039902c9101640d0300700010340050001d0118003000281c800320b903003611090000790342c410f07040701e0741c42d0f40900c0706000346444101080106003958038020814214a084c20703030a1003078803809c0d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 995967059 1250 995965809 995965847
    0x9040917040608161d01080c0918011706010b1b0a140604020a0803040602030f07080903070612050f06010507060f2a1d0a0b030703140a060501120c051603 68
    0x40000c00541007402c00d88610035908400b64a10380c0343e4405c4640301407041810107550510b0000081303551040020030352041030390303009a20300190351001483d0800c2c011540403038140000010311084450b0040318200c190702000404195041001c0c207116401240e03a85001c009a0860481280c20200603154089402c01c40c0340503500410302c40940c0795081150260f0040810070700010341c2420010486040300e160b50b01443c2001603465000c500f82e400b0701300603241c05034203014451081d6001d201c0900104501d44440303480005294104041d59001810090038501180800c0000d0341c002d4200d4007640d90001c40085d000400c001c41600816001d160380c840d0580219540710001c040035941c49407090582c40b01c40d1142142c0d802c400302d00c1c1e5800343e12a0804070f030400412030300406d003001c0c64000e0a64107000c100783c8031042c42d0f41002c983c1102c40880c03883d124035080040e540c01c40a841c803400c00c2d000051150340c00c0c140e00505644038502030000f00e904035a403008140340c03103041c0c109003c1d510006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 995968309 1250 995967059 995967067
    0x2b050310031718030705031b03010e1903020d02030c060a0b060c0a0605090705030606060405090405120c1c031404120306051e0102010b0910030303050a020706181e0809040917 77
    0xe40010307500000a02d80c4000180752040c6918600045e5010448400030020f0011003801050607191482e2501c5540c0c0540d01c5058890a00d0740900a024244c003051048046108960600928011003102035201795002002181d25884003c1a13090b40f000b180d11010a140c510607021498501c91104518603e01440460b40c007008140d42026000310718840c200e440842c0c07100c1c01c158071140b05580c141d5200804000c10015402c2442080c1d0740140503005407030080c00c400c2042d540c1c4d54401c00ea201900e030001c43c01295440b108490400c007000c080e280802400000c541e02101c1003502030b0000e1710001c50380d140c44250743d02c2a003184020788005407004554941d481126400f8072201700705280035500f0400202290f06103900c0040c891204141034156091441c0c5040c2c00401d40a0040c1708510380801003940441e2282c0102d015a0b14003618650029846003407502c0340009056942410400030f10507500410754a50644641c810225000162103e56103405042042e8a40f903485620b00b0200b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 995969559 1250 995968309 995968343
    0x9060123090601110f0106031407050303090d0203010207020a0b0c10020408030306010c061104090b040501090209060f180d051c301d0f01320403090e090f2b05031003 73
    0x90041c0040301c1c4241c0c1c00d078100270000d00c0400c0e1a50b180c0e00405030198410f02041a07180b43c080240340d04540081d0006292510300c0d0081050361002c1d801400030364034006a1102038510810080e401d46000110440c20241080c0c80a9103a1002600c41070401c401591443c040c4103455000c0720390140001c4990f03a4442d620b50054000c0c160b6003c8103481540340100018450180d80202c0701d100038000e01c068075080e280001c40009030024110900030f080e440390f6003c03082d10b50b034030144074440c000c3c0c3c0140710000940c600301d09a4900744804c5c2003003000d10440c40d0b010401d100f05c2e584510368401c4030390350320809424441c0002d14210404070716502e00008000d200c0b000100d52032007036000c40d40c0244001450040b02a190314505945039007100071180601e9110340c65641d2454000e4424a4107044196881d480c3ea54000c900351070b1000c0039000594284d056240402c48490940200400716110403500d51484130714000303865543d0103005c40080081c15401c203460704140034591280102c24001c41c59 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 995970809 1250 995969559 995969561
    0xc020904080a112505100507170904020301030f050c0d0210030917030411011b0804030602030a0207060e10061703040905130f05010911010e0f01121d010509060123090601110f01 78
    0x10081c11312a0103000c0030701144c941030215026200103110340b2054078050050b6074034117004000e040c01900c001014032100d821a030700c5e1f00045000754000c1c0c890795111404ca003000c0b818480464400b6100d010051213010041e10b4001c2d407410103c070103040c00100004079040140c1c1120742094019002c0700d0000400c810440e02850100e01d681082c0d0303620807848800700400600290b10080904549c100744810400101e058000390760251600c08054141a055610300c025260340c841c0b01d1009410000d56030a0060540c407410b030042030341111910760140d9074030000b0340b64800c0e8082c030408c4175200c0000407010104100141420356000c500c4003c130004070305046008040c424000c58550981f041c1c146010343c4160f80b1250303841c2c4014114850b0b4030f0f043c2c005403200000b83e81c50b41c954903182c408844118001d10541c00f00801960000b0400d490250009410018140c1001e00801042c0b1f8402c50225400c240e1541c2404054460341000d898242c0165203410007003d10380b516100340b0807400000181 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 995972059 1250 995970809 995970853
    0xa14090d030e03030c030a0b1302130e060f0904080d1b0503071409060d0902040b0d0f0b070318030e01140309031c0b370303110d0c020904080a11 64
    0x401d640070000e080e558441d040e1a4031040ea14140700d0b420600c007091a0204640c01003444a03402450140d100100b41e4400003a6000807110480100380d4010070004c5d9408401001d81c40002258500382c03105407480000c0001c03a0281016102000c046a1840c0c0c1d01605d6012010420303000074090344800f40340000400039401180c04800141a25810b8030341c3c5161501541d101910041c0401d0402031802402002481c0035001a0390280d101c2c2d42d0305c41140c480c1c3c01030001315802144170705c43c20700080c103101440700c1c0058019803c040c98600700300e0120500b900c100160319490301d0700d2401010000012214644071030f050908801d4004180594064000001c1404c0038844808130200e0302c00c01030b88411140c0704043c06411940f840440142030280d4034074080400203001100300c1c1030340d2003d00b40120f0280c2c1c0c2c20071404142072400c2c0c03081d8400d0802070000c0528942c60180c03800310095000c184404809040104014004100c410b0481d018220b4662240c1740c0b40122858214190452118840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 995973309 1250 995972059 995972083
    0x1a04050a0b0705010f0902010503040b07200102071109060a0b030a0b0913020301050f010e010b0c071a041d04110105030a1d0d09080a1709120a0b0618070f080a1409 72
    0x8039003060001c045c49036004103400b00d50161901c5045a60b26154038601610042041c02040f074101d00d04c4001d800060b41421f09011004001a00d0707505034a010804201d00c0c2c516140f0030300ca1442003280b1980e9007040358003500d40c10084a5140d480d296210340261180085050380040440d0404ca007042c1000048110f0740c1c000c0b4001d116070b807646400413410400c203004001c245800500184568610803004141000118044440c1e807075882c51003003522008440102c0d426131000900b041000604030024550346929480c4c68143c0c1859a0388010386803907000341d203041c0304000c070005c3d1030440c4035445035920b1fa2500c01ea108030820b00000c0e941d294480480c1c41c401040d40468046100ea100040741e10760640e108003081440c101900342d50b001500300700e044d158090b0a8400299220f2000e11a60003840d2107940700c3d94182c2080010001c2c12440460301400e0810f6040802000c030780d1000d034600c181ca14604022101d601c0710000700000c1c01c010400c0d0106043d0700c42c1800a242c10008000040740 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 995974559 1250 995973309 995973311
    0x3120d0f0525052508030403030e0316030c0204020909180105090316170c070f050a0b0a0f1805042c150721050a1d0c03071a04050a0b070501 62
    0x607a03890000308288650078545030902ca41035080342d0129010380000c00840100d540105400150312101c02d040400c8050125041d40011040c4410550940104000c10084402860518642007900401c030040c240340139040012805940b000e5403540e5044890816020304085c00c18a030001c00910101d50107454102150b28200010b00112000b1065602d40b03c2007889404000900c0e4444070304221802c028100741039410425000030316010030803500141644007426041a10700001c20103101c066511002c2c00050400ca40c18005500070707090720035145542400700b806948a038116692688980085030071a181c18413a01d2020f25030034a058200f0403500c01c913541899400030664469464040802000d000034022584244c011020035070840350b002154007000105001c80004e40d8002e46100b44000c4d6542603610482100018044d13003070b621500140703022040c480203ea40c1d01c11510480c0480d00b81e4154104030701f01c40c282220002e0100900708400541c0703525000700782c2d40c81128221019 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 995975809 1250 995974559 995974561
    0x2010e16050a0902070606080f0607030c05040e070302031005060f04090b0604080d0507051203010e090606010f02060114010903141f0608070b03060402070b1612050f0a0b03120d0f05 80
    0xa541416400d8059510151222901600d01010b120294000c1c48040702c2040c0c84174000305411200b0008a8034881180b401070809040552019007110340c10030320002000300800c001d0088034901d203061a00210903140040e0f40365101500103407a42d41c0d940107103501c10030004d105d003060a501000382041d00d04114080101d1403807841041118810391207211840d030024000b6031103150092001c1d00302c0601803820389142a00f03100c099403160b031090f088190f68421280501007054020805507900400078284410810204c180180d5035003814030681d121041514802005030744101100c00040d54041040543c0c130380060806030b2a85012030900e04002d1054502c2e00280116000e15812038030000050906541072814010042d0300040a454006804300700700c10015401003051403103076442c01800025030107604002455984403034140c400142c140424028844803007070025030081e401d1840044c024100402090074030000c101208003000c004914229001083e41000c0c0404828072004c00203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 995977059 1250 995975809 995975833
    0x1061802040f0e27150a0207150b0a08060a05061c030e0f0607080a08041b06080606030402030f060106030b150c0c0906120a210c0302101509050702010e 67
    0x80740078901c80d00c107203070b00e03011001c00065100c3c0c0b006075001001c010206000070001d801d070b0030040c42c410a40040582c40400080c44201030692543e400240d1400300750315040c0785845602d0b40030b60781110042c0440c0c0e01c00030106161307110440b06004041300d4055400600e0041c08400c010002180e1150240010080d0300e04071481e42201404071652603110b6420040c500001d028520440c054480e800c100e0411000000c6a0505c02802b031580780d0341d40f0b400e86403800e0f01e816101103405a1401e060300d4a0035805000103600b03c00c5865100d0f4068461a0b242d50303a500029140004c0f455010105000302d20001c142181c2c1034200c81200401520400340c486c0e0f4248100a5501c620024440360f46c000d0171801d41c05151810825800c101c008042c500f102c96420101810803003180811a4050f030241c4d144010303411003010f082c3c03102409040c070010f40310b11390320b010392900b405c206c4030000c80d50740e1003140c0400084900c04030060100154100614a0000c6019000f00841c0841000301d10802c1c4201030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 995978309 1250 995977059 995977061
    0x50603060105030c03060402090a170106270209030a020415060206090a150203180d03023606030a020c0106060806121b06070206090409033c0f0c02030d02010618 71
    0xc0200c006030345507495a611002d0007156a0400b51415034041c2e02003210000325600c202129024003512514402484501600f09084400701d902155264041076510820b01d00100d11060403600b40060140c0c0c0c81542d43c0011b414000f00c40d60095100f480d1034111605039140e1085207050b900301d03408542050306d6840c1c040d951500201c20040c00085c0150008184403465005141c1051148249041003034925a58500b410b410801c80d9000070380c0440d01880144401d94400111400040b0154903e14001d903403550607103c075003610303005590000206207c0c2c04154112030076464000002c206d115101c520080005c841034036000d1040072300402d442080031002c562840e44905030010460398400400a0119030380100505980c01007040c0030b00400c030741f00ca001c0d0680302c42c42541c503144d10010041008113840480421004020300025000990300d010160584015215003441c0707103142c584000403682003499405c001d4050040090078061243c05401140c1550461110002c0340816048064 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 995979559 1250 995978309 995978311
    0x20306060403120c060c110c0d020303040501082508060f0603130212100213050a0602071a16150903020601080c0904060c0215180c0924120a08040f050603 68
    0x903038040c004020820010710b000550401c550380c0d60428113030b0000d858480700115201360420348046180c01c0f102000c042d80c01e01a440720081e04444040740c510309a00030a9a900440c0941350600c81c510b00410824041c0f215142c540045d07162841159031001d200092454005452650241c245503007031030704602c2c20300c050320312443c00b242981c089201d49400f040086001c00300380300154055004d0307005200f40d00b8002000d0080020803061641d519100034000d040009520800454001040600400030000c000140d0303d041420304076200c0002203900900401c03417140c000e00784500b03c0c00b88070344226181c100603c094000d03000d48045030303a102c001036120b00780030a4059008000d0b00c00500001d40745da1080c009a50380384111f8413403c00340c102003986144159612a50501c4518907036414031400c204c00c010402081e2803121807800c0051010551041da00d00c8021003454244804045480d05d4440c11081d0b80194101c403245481030418900359403003406070580240e404200429941400c0d1300722 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 995980809 1250 995979559 995979571
    0x6150207051003180204110d0609051909082709090a0314040617090a29091c0f111e061015050d0908030406050916140f0a18020c0d030203 61
    0x4e20711806982004000c2c103030000b003146520790510540d555240700b445a0f40190902e0300c00000c0c14140a40c01d508424841c036601e06c4402d0400040400041d4460143c4400d28017441020041a003008034800002d4880c206041d000301e01e95007000028400040e820440a0180d00c41c0640044018100f0344c46100c3e50150704042100002c07406c2c804d036010610940d019003036805907081c806080da11540522a101a40210340340001020390200f150100c842d074000c43c411008056250122a4040315801540740b00e00070300500390040f4480c01d005400c1080758001c0403040d41d008015a943c400242c44c11065411054030440d000a0009106aa0503d05a4464030707a83c1102030900501140c05600c1a0120140c8540311024100000c8248028501440c0300b80c401051901e0242d041c1890500003603258041186107980400511080701c0309080030007025512100003040300e00c0495500c40c0198010702c05002030036910b01c4105829809840e400300440d064500c992041a0120140d02040d40d02c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 995982059 1250 995980809 995980841
    0x190503030f070204110409060608070e03120a1830020f040203100806010902030717070f111e0106061403102903190509030703080c0307020106150207051003 69
    0x505281410840050b00199200400c08150320440e0101081d09800642c010910b8585905052142e1900605003660181031031030304800d18400880003a58488050202942000c000240112101e109040d031502600c0030944030856155a170f426101c01da000c180107800304c4070404e107030042000f05505040410f10780091a95080c1c0542804120007544040c0982e15910300000d800140c0c0f0310240011802040b441600688a19280c10041d281d20756412145130408184420071883d10740090200c40784501c20701e4070394051190b1a0410746802c0c034100003140001c0750103460320409241504404140c03206942c402940c01d5901c0001c1e011400180c880341c0c1c4c41c98030601d090228907084100809141d5000c45030004034a01c84a5480d029402030b1650207044040e141140a444403500136107401c865004025460035a650310300420025010b0f05040c00941d001000c21a03e9100f50040700c05042c01c995100000b40c400100659100214415507010304200c144c4440c2c02c60080c418000d90351401c0b04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 995983309 1250 995982059 995982067
    0x15120609011e0b0a0201090f03080f01120201120c0e031209151e0f0403060504030e09070905181b0f040603050604050403091205010f02190206160f0c1e06020919050303 74
    0xb50003022134100b00580c4003159600d0320f500001c160390140c201c000c180070f03803529551030070100200c021917001608950125071450481c80010f036413080c40039030840071072440050040d82e11001150b11003981c038402541403050f80c04201a0010760802408403103803c8401240400420b29205014007440d105604410300d034000300409401035000414091031b80610b100d01d4141c480e03a480f01140d005581c00d400051181110b00e140d814000600c50b0000a14204a0f0f80186000c00145803001d00030603200300512044041414600745000c11087d41c182264221b850300c084110350301d0250041d1180c0400241050045052270610b0320802c3c1c060f40d01696280e0166060045d40401106001000c4800d5940e44503038801c030410b10710203481440e8011200214000c4016002464804094407264010311254120070440350000802a00c4104500380b40e0880b96042c20f00c44080d417000703c1c0703980c0c40d0a201d603002c004100665009080e010411246200d00c4070107411988684442400382c150035a00c108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 995984559 1250 995983309 995983319
    0x180f0a0e1306020706060f181103060f061603030902031009020d0b09030d0914010c02010b0603041211030708071208090607350103060606140f070215120609011e 71
    0x1c5609044980603400152a2045654462040b109240d0200da4100903801c0c00388a20114040c2080f0f418801d01400d110380d00100045043d079100141030036103e00d01828200310346451f98016034480b0444110f100450741c0650a019015120040b004c0f4820f000d92400c0d804030b8881445031407101c58001c3c20013051242c090b6505464160040c0000d013841c0b0042c0078010207101140a0009441e100e000c400310280b4096104d80d0a6407005010316042d641012005405500da05007582d030701c039402c5410a00e04080700340342903d0000702080b10860f28000000c6903014450504000d200ca1840b0b91242004142c4090b81150303680b4003034402650f03540101c40410310482c452a08126a2001d11101c040e8011000e40c0d41024a214081038100d0752400d84010000c0c04114410340c8014102810110b0b25040801a883d880740f185610b6602c1c07038100481c01e2010340d00c2d400130030014816590f12855880c00d001d03164101c0340760101c0c2e1941c0300c0c1d504400003144101541000d000907004500203000210700340 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 995985809 1250 995984559 995984581
    0x1060804030e09090a02330a0c020a0906080d09051e0406120309030507170d0c05030f0d1d0115260d09090b0f0a0e04020f0303180f0a0e 60
    0x240c826410070202e01401c180640c0d9041c1e5080c0101d0008005000e031100602c180030b1142c240446003446031031103404d20f00c001e805651007102000440b6541541d18400900140c03688450400040c0d0081510113011481c0012a407043d4103440c411012200d0401d060002143d00a41a009064010000c0c040d040d03c80381074401c001c006010014400f180c8162150400040088203010580008070314607070410900005002d001c000e07081200c81d070901c9030850000c40c0e5841c201898090108040d04241900b400001d0042e00c28600c24400c5155076160351101c840040c000510062080d056103111070384024005108908444801a5800031a945002100e40741c2c800707e4042c480310440c0c000203d541548050192448a0b407694548520890070166034001f2030b1401a5a5802443c3e07151442503c0ea5428001c0c00441e0b1481c450704280790b8444c400700c0c4900098100c425014800800d4030021201d5459000c0e14082060703807104401031500d0204440d12005100b821610390821010a5500c1c0030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 995987059 1250 995985809 995985811
    0x20c06091b19051306080d260103020a0608191d01050717010b0f0c010f020408070806062d030708030406020d1e030c1701081501081b010f0909050c0301031712010608 73
    0x110413400291241da5050003418160526a40d40005001c6a140144c0d00103504c80d1004119070507001a178298116030200780c4070019030150000b4050034070006030780c14011a00c42051490340103818030840300c03199035080a070b807000014070071203500744000240c44a01c0b45242d40700662250000b020640d1a2015031107407580001d21080902070100445600130700240200b20042412020040e5150721b05043c03a4101213060f0081d0305503401403001d12440c0e59071b03048030500d1040302400080c80d03c145c10394104441911a01195014003a03003500040018021000d44120354080e000d03241d0255000c80c04580e00c1d00c400701d015a031450340c1d012140150740320754041e06040c40a428007400c0c80c1c000b41e0303076080c80c0c0c0000d901154060f40552800031401e078502c10410300421803d401441704c030381307080802954042c01901040c100082800c500040d503101e01c07a1100203001300c0c101041541843c500c3c007035495100340415550381034118401c010001c2017100320b039895041c1d0002c640b25030342420011282c400c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 995988309 1250 995987059 995987089
    0xa150f030c1715060706060b04090e032106010e030d0c03020105100b0f030907050925050903030d1109060a080a06050105040b0315010306170f0d110a030e04020c06091b1905 76
    0x11051105c880010010b1240b0005001d48074116611a0300d89401d640c2a2503050760304408980041c4000845001500c1d00c1941d43d00d140c1ea03d03440c3c1955140012901c5582480c1080d030f15115042d161700f9416004516000c07480d0082d402400140c0d5204120021030340c0034810800e03204420040b240800c01c2000103981c0050340c98050303c68403603076030001502005050b0343e07001c81d01c401d26003101c0c08144541c914015030307200c5080070790030040304030000fa0320380c01005036807454a030b100c0f00d95070040c1c20400111221540d00a000c140c94000f04030303008108400c06c6802c40340c024a0100049110742c081e0080e0307000c81d05020002d61540c2e4550001c46944804d00c03a40d01c2c185501c6041c08204032041c2c0d510303144003101c1c200c0240b40e51a1200b040301d18004600e00200d091001c10903c4691100700071981412440d01420720903a0b030700c00034004c9030084c41419000003890050310706020031060003142440b118540d050482c58215008010000600000d041c8606190340c031040030400c42c00d10228001c0615 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 995989559 1250 995988309 995988319
    0x70305010f0b5a09040911040f06051c0f030f0c02220b0103151a0c0601060206010e0f101a091e01030f090203030d02090a150f030c1715 60
    0xa050000c001c08401800308400041410801500401c040c801583c480c0c0900c1c00a03804040c03485800c4092244680d011060003203131a04007a40501205c1c000704040a403000d841004034681d41c200700c0004000324026184202408120300450210720140c80c840a50401c064118500c1c03903a8060750108904c600c42c034244100c811000c00543d4071924142416408644035178540d00620342200102d4607800321082c18140341ca414003018203540395030305050310310300b40f80c112541c203854549070903a020311090080b2074829100003040c120742c045191412078900c404101c02e81e840d403901c441c404410850740000d0501190784100207981800441010b110a84085980303403c00d2080030411000100054040084514003c0d002950f070500c501076072008219000c002c4215907500180c3c0328412103000c02030060f0041051292503580004030002060800000c5d80003441c0c214010b0212a03502c0b20200120340303801300303003401c07280603000030044101950a405402d03901c003083c0418001011b01403580207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 995990809 1250 995989559 995989597
    0x601050a0c08040f0f051909021303061505092202011d060c0f0c030109030c200607060605011404061e030e2b02010e12030c0904050a0b010305070305010f0b 69
    0x20070882c000070409000000300300c90030141000400000d010581d8810340c021a42c1c1441e010b5540150a540e0083e11138803076001daa03034040d25105a404142e41c0c0c0020780080c0c078003148801440f041d2815581252800d48503c4000d03601c402c241d01c1d290103c4400742c82c0d203440665504006620844440144d603041c0d803207451043d440d01022444a4201d090710720401c4d8444000440c1003402001500c3c3c0032181140248841040e07550f00400c0f01c10403200c01030501e0f85041d29600030340080e002d641c510441c00390074140c03075012070f0a104018010780d00c600d602040d4547c424803010320110080303c09855260310b030f8507803504950f001041403c4810320320104043c0d840b205040019802d004101100a03a608101d41005001c4005101c141d9114013039415685800b8584400304008030b90698015907100520b516130b035403110204414030a031140164018907000030032041503e90b03448420714880a84c5e041180b903031600c105404844007806115403800da0441c0c104100441c2c1402442d031200c20700385080e00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 995992059 1250 995990809 995990813
    0x31a09010f0906050a050907081b040b10050a180506040605030405120d09021203040f170c03010c0504032303090f0301061a040510020313090c031b092c0601050a0c 72
    0x129146280c0072500f80391900c040c424606410300415170002003c0026080745458041925610241c441c0c640482c20381ca160300039025170380ca500c1a002d584000d4000803141417022001481c030381c05603047d0000b05110a1090706440000b086810948001900f001e14042c1800d00940f85030304018001c84036031007180c00d80c24050526402814414562040c003145a0f20f6601c108007031916204503440c1a64030034070040216800301010002123600019095001d113a151070310a0400320f46404c5241c02d5070915012905155110004008a078001c172155203280d0240022000c000c00800b400611aa1081c082c034078061400c0705c48595450401000003d00a54400c401c5403e170b51281c000d1182050080381c100054185881c08900142e89407010f149000c4002c0c955142c04039290260350902a03580b040c484034540240d110100e280c003503a40c6e01031301007640b41c001002803074180101c0440714413207404245007910039442240e0a02009104071003e88e1203c0044400303412082000c020000501e8070000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 995993309 1250 995992059 995992061
    0x615070503070609080a091e0909020102030c15150d02100f051209060403200a0b0612030c0a05010f0c08041b0308030a051515030f091c03090c080304031a09010f 71
    0x18404c0d10560900b9200c4400d4200500200d49170f0b07010b994440d486981a1221440d0240e005040c1c1c1c0d008240018543c45600040303146020310b8480d0684d5106101182c6482200c0004040c49050800440d02c941c11030102400100e40807110000d40041048442c520b901d070182c41c1c3d0b0210131110b0700e415414000c130252440924201510746114a0300040c2c10300060650044600000540c000b007440304880e801d108071592489041d001416040b40c010101d141581c0300400d410001540504480d102c0f0b2802d09982c3d01d4080c0054120346070343c41e117981560204014040c0c0b40444009403600f0030541d4640e181ea003c1c80c0c02890882c4107148422002000154004002d5405041c04400c0001d00d403034661202c00e090140700d04040d10032441e509c03400040d920308508603070b48809880980e180f56165419428901510300c40040902504464801007655150b44003010340760054a10660a980c4c80360071603182d00c0740340805030401880c4560381d10054100c801213a0442100c0000080103458001d01034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 995994559 1250 995993309 995993321
    0x10210090b01030213060e15131d1e070905041104090b310809010e0307140103051602071a120708160311031f080d021501090506150705030706 63
    0x1141d98801e80c0c0144250309242c80000031243c51750b0010845103042152002e800c1e1001080c040e03010744104280850350b1660445001c2c52107072481c0c144200c40340356803001c8462880e61817018071b9124003003400c1e1102d50104040501250b02c00c2c060847c0c40d080456a00c00b8150040041c1c48803110300e41041601d803181d1281d000007030301505044803282880d51a42040e1120350440440152240030032410301e218040700000d4140d4085980b82c0e0300d17401c1a005917156440c2d0350b083d88e89400b964800040c0044185407090015200b40d03002c2109175183c1c0e0081482d0400c81e000200140d001180a014a9075a1003007404c80300421f01c07000d811b0164030340403d902e520045030700c03c000451140a1000c154030000340c038172600000e0306060100b00c12000c2041d00d43d000081c06559012154410100700442c4040040b014266030015650002d03004003020b980e518500a04c49140c000c80b50000880d0606841068040c140040a1002c1029084214400c1d900034010548140c041007007964001a1244508 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 995995809 1250 995994559 995994563
    0x30b0d050703030807021e120d0b0d050714030622052118040b0919020705030f0702120d021203181f05070201060f091a090c0c0d0f051801021009 64
    0x104d01c1460b0821001341000391100d8003180500109150340c006410200b000b14030a03d06d031400700e48400a0661032009802014240f42e0480b00007030014007400030105940301596044180000c618070401d040c941c0d9508102c480450b031900f50f00c1c1c4003900007055543c54607920f0041045a106850152600180e01402d1030400105c4400107110406104482d219245050b8101d408009210006010070000329004290840600e001c005000300260b26a042c4c3e81e0b0300d504034046035264a013101002055600940c41a03100d1110b080c402d041c08d100018a0304c11020b041e501421581c4044000c040c030541015184801c0698240341d2140780140400c8440c0d4501c3d04a441c02141a00d820300c90000c580e40a000c0b20216414070b071b000d0050004444014080700c0070028005000000d9004004904107915405c2e50b0280100d01482104141c12000c0c00c4081e080d0810348804801d00030040d9280004021000c02042090042c107401d40d04401c8401000b080c10b0043d07540540b070020700c01088403021401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 995997059 1250 995995809 995995817
    0xc030415050c0d020a15060b0a0c03200703150605031f020d05191401290f0f0417191b0b0c0708060108030313080f0909040b01050f03060610030b0d05070303 69
    0x1708010310405192401d0b0380f0007070b200c0802815044c088213400030310400346140c01303016105072500d0805102e8050140034007581e24100d062440c00c47c8a854075040340c1d100035100c10310890010300c100e2640340b18460445000034001c140e50701014001c44400968410f1190344180d09000c8910500a5401628842c0c0d030088251000c00050a44240c21a9012128264100d490f400140880b010043d1050518904910204240f49400c190310101d4030403400b01c980c10400c0071800005000e1080060401e585032110340106118600150030b55603414103601c084002000b00b4154081150103654058072244502d00d02c00c4c1680700c1d5030284132644030700c4c480091580200390400155006124090150028001651444c01c16101e500408201c148001d0076485000174100700c904080c1c81113908014001d0401d0000340b0305410b05107410402413292a0245c1400003401e50b0501e404190103100b0600240b036001101a00b0000301c00600180f0b5019420043c1e581c058030100790204980e2009512a0b91 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 995998309 1250 995997059 995997073
    0x7031409190819030e010e1314180f0d0818010608030309100e030a0f0504090f0f1424030c04051f1a0301090f11070302070f06050c030415050c0d02 65
    0x40450701e00030841500112070f0079003000203400258000410b00084209290001c5201e00c64000102c0d00c3d00c12004815800f4030f0600380c09501d003018840c41d44680d0346009003080040080002030b80358419149100300c990410003c41c0503003401030039160f401c2042e076100000d42c00100440c0c20700710781c0c1c260040c040c0c0e54400300c10001010400c00c03084a0700142002c05000b0078540b64034856807030042d42c45290500c00c52146036038896100300c0590303004040900c014050700035600c102200a0401c0c2074441c07405da041140307500c50120040c0c085802000200b4039125420042d0b22188002c2108050700381d810700800b0b0449245030741d14000c0d50300417810204114403640c0d14800c03081075070060341d0040c02540914882c24400b1311008064a04541c0758090106005078030301e100c0801400006001020302c400407680c00d0500d44d0004075034080d40c41c0c600000c000ca03500c40310142e400b8000d1720101003d41d48208028800d15003146e04040d1043c00038107000e0300300001582c1c0e050500404103203040060740042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 995999559 1250 995998309 995998319
    0x60711041d0a060f0905160807060302030105030c0d080c030a0504050301060f0e15010201110d23060a050112392d021005090d080606040501050703140919 68
    0x21040001c0300c10285032001141c440041003544480382d40402422882d580c454041480740030f504040c844079800740955144160320700040201861301c0c00b0300c1d0202d104400c00031601c00d02034400c8a041c5d40e401401414909001410021801421802110514420700c0005d00e5231400300060300ea42c071807940f03c00d9107444c146000e05084803110303480741110038214801000340e10300d819000d640144a00c07555010b0061103000503401742c61560311907a00f90400298400c600511907000c1c1c141010b01100f9100c6016241d244201c00e801c0a840c400e510020b2140200110b40c018054101141401c42c80460902000c062080c1e21002c00c0302ca500c3d00d0b95104c07002c40300300351a00504800d038000c6814060307d1441c40c0c1b071240c804510460203003844200d1492062800600030001d0013000c41038100180450f10740800016201c0505802d014045540800441d80c82e15250090380c1c25a101a034400b81019859103044503005119901d65940144c100310001c95502d070301040c0b050180d0005d0440c02d04078070342 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 996000809 1250 995999559 995999561
    0x14061e270301091106030c070b180105060102070608070507151125030e15070209070203130f030f1b0305030a030b010806060304050706031d01061d0601020607090b130506071104 78
    0x120102901ca03924200005001840d000c074400b40038582030b42c1d296180d6403543c40b0000148202c4001030304202c0014100580c65940440101508142074002d11158407440700699650234140200c5021400e40b40000d20628440c001401805024160b02296203480c50380440440da0b594440c0d207094080011403800d1050721111a0755150b107170f80519100019640ca004000c104050b43d0244a030380700c016290420b4440100340d84901d90000c1c003c40060420220107980c9502078606000d54204540d800076a00148203611022627405c55200320100311241c3d82c0420040f445208018241074900021020880c10030180c0341007d81510009091407440c0300241515a00130b2440380310f04401c0080000058021900f10b0071507206050105812070409070908100c025035420f0022586001800200745641d22420704e2000d21076800780305151941001241c4600049801c2d0010a1034810b04101b200071890003000707020002032500d0350b40340e2601d0016030725074451501500d4034500104031040c03038905 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 996002059 1250 996000809 996000877
    0x403140c012601140a050405180c030706080610090e010b0309190f020d06110d02040e010506190e061b010c030f02360301020307230414061e 62
    0xa400d802103a44545072460b801d44101402840b022501e0008141603586030000010f0140c5001402840305140ca01d40c1c241504610174140d038410b03c141003c200c5541000300c0d41d201614600d40e125001130707991206000c0c0303000a12904004111070bc0d000024201e4649080501030310291264554904020800380e1070102403951036165010107080880004018001c0f100c14140e06070f401e203a40010780e003000c4000341500c1e0201d010700040018003100c0000d59034010015070b0000b51041c00d41e80d0b00e0307100303100c058015810f1a140002c0b4507280442c10500840c0c4980304060020100c0f0300e0003900d6041403800382080c02c01319480703039120030003a02d281c0d8250250400806081e00110304010894503001440c20141603a82d500c98154802c4c1c06600285504003894148094001c0d9941c0c20403490090144c00096031000c60500c02100c09204010300000300d030100c9200f01d07500c860740034500e02003207020f9001ca03c060340c0c05009000580c1c5450320714030280010f09406981d125029858010248181031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 996003309 1250 996002059 996002087
    0x1214100507050703030504060e1603020108150d1509021e01032a030b0406081c09170a08031e240a0f060c021908011a03010519020901050403140c01 65
    0x41000108001540e000c0252483c882d00b5143c00700f8070351100c0c02c1c810001e2003007200c3d105250142c11003690307501c003082000008691007070340c0c1e140299481c0301800e105106112201031303000c0c0d07d15036028003296685604513441c54a94500140040055000680348902d001e1000343c01074851640210395078042c818041d500000c0c4d003030b1000594101d400743c3c5128891500750307414507594a81c1d020785615258055030140c8004400c55542c40981a000141a20b85000820001715041000f0400e60403842d51890411101c038000d2903844000da54000a54200506841e07007016a80c4810464060480f0302d1070241d960398519801d040e42003240c0710300d40b1020340d01ca5800760b0803001c1c0c1040240002e003024000c40e042e1780b07400701d030540b044e100003903944804041d5950b400b418244045001c00c0e040d402541108100284140008052420305003030369070440f141040201c44120755191540f05800803d131000381494010725064a9550346c881428840c8070807019035109010340c444558100b002410141d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 996004559 1250 996003309 996003311
    0x10606030b040e0a11091302090a020c0d14090603043305090a2003070b0409060e070e010e0f120111030103112e260a11090a0b070c121410 61
    0x310340c55006080c5e01c04504a0300469500c0c1c0000c0010034a141e00344601c40e4003c040181e01d0030003070b207a0406034010243c001c90600800c2c40f40400740b4003507041f0031802c0310444000c501300900c50b8100407490700007d000741d0303104250308104040d4288103000d54011900c2558004500602040e8000072903a00400b1000f0b19400103c118000c200740e80100c0014525a0700751f1001d13040076502007070038014180d00000c5803600204011a440110307401010946802c001c45441301c1d030303542c001101c1d500d11491102c1e0102d0308084118007181001d581d5101d1901c0301800c10603040003801c00c41d90850340f00c1c500001c0d41c4103001c001030041264000304594100e40c11182050004514414111035942c28030088a0035038500f0026542e85000f02c1500c9102e00d50800000c0c1015403108500046d800120340d0003003e140750000210801240350140d075981c041c05058140e8590a1030403000c1c00350b07c101c0d030680d00c01f5050075001901c0c0c01149001c0031864440c914400c00070b03a44071001c40c6060703151540300c4019 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 996005809 1250 996004559 996004573
    0x3060903020d0201230402060403140a03020c102c101d040e0705060c0a080301030c0501081e2206022d0301061e0c02030a03020309180f07051b010606030b040e 70
    0x7a2013040740400d4000340ca982c0145958603a41f00152051280f44e000402007409000340a03000705011a5000c1d05c0341c00794080e203a1000c0403108000309083c68403040400f08805800000c240300401c8541100d201801e0383c103d030103260b0080020b1040011381040c40000d0018103100580705200d891003154039a0071b5034140300203201e822507652038801600507540100c0000c41c107a40020760810031140455001300b4502d503296141c0c2000c060742c4c2014083c5502299001e07021502805002881c1011408425240b4440745c8600306115810511500d0400c1d1822900304102d010404910081003103000300e004480c44e030512002080c1e1400c02070001000c9044060004011080d084008145c526540c29100c081d07903254040141e81410b0b0160b006501032203540607901c1010340010042400d824112402d0041a00d195507151140307400320b0310200d404140d02d000c01c038030030302035006000158010019441c10700703052241c907405c441450780601d0000351500840e05242c24035220798000398078140054542 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 996007059 1250 996005809 996005831
    0xe06060303040b030601230406110316170408071e06050c0703030c1a1006030f02090d0f06060b0c0624011706120d050702090a0b01140c0c060403060903020d0201 71
    0x242c0c000c07841070b000d8403800040040c0c0c150388110070501076200c8000b1103000000300c400644a03641c01c54041c04000c600d58609121001c5000003c1d0b607200071170001d2196400007580d50301c240740d00d500c080c0200980428000811100c3c0d05000341e10181024a8000d120014083c8811501c3c0d00c1c15440081881401c10458000c0380001c903440003a80e8041c1007074a1800c541e803800c64510340340008400e034220b100a0a00189202480c080011100950b40038841280d414400600300d00c00c802c3c41d580d000306840d01e4040080d11101c15a1000c90003007600090180e62128680f415501400d505510b0383c001e14100a1030300340138681d58a58116410f2500301d49504071001030a601c81103d0303410003162030000007407515585d40d120921f011000a09650344030074980c4004d0425002014120b00c5042820f0006d80c1ca000c083c8640050781c0300513518200d45000d984061840c0707a10400c003c103400d0058540708a00b603206c2800800c025881001b0000e5103145902b0000e0030409414038901c1164105112000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 996008309 1250 996007059 996007063
    0x1e05031b03030f07090e01060503070c08070b06130b060d05060d0f050601060212040f0b03130206040815131106130504090804170d09060f11100213061434080d0e060603 74
    0x3041d501241009c680e203407107155098902d8042104010510b01001852804014a001883e4019241a0b0f45080c440d01e032410841c0503100c2484146400410910150440c0c0388182c200c0f640000c40038100203d0b08015495448401040041c207680b00e5110800400c203080d030402000c85050400d521050030642000aa0352025186100320217a08101201140031100c0c52070305041d803a03500034082070342c0355601c00815440d41c0903507000fa407001c25110000355001c10f040c9a0b0f10030f915800040244948100c100b007103050f0b0821042c81d21440d00b29400420a5120b620409030740c98059a1059102d5103064603044046400e00340520942c3c0241c0a842d0009411991220a039245400c059041400340f5400702e0f44801c050400e5282c2d0301c2290b201c080a20310741c3d4020400b40742c8541c41400c10300d4641000f66488100903002a424400030815a1030301485c1503862500301c00d141c403249216800062200c08204442c580646610000158040ca01802c038441c5d55a41c0c610940034010ba0300d42200080d03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 996009559 1250 996008309 996008311
    0x13030507060e0c0414160908060f0c0705100204090e0a0b150310060f0f06050f0703052503020610090908070f0309050303040f030218041e05031b03030f07090e 70
    0x14074142d1600200e60426400340154004907030090303c100070441d0401007408a1080070340b40e84040015030703d07150003000d00c907080385410341d03480500070040754441d51501c02050000a011301a0780c00b0900c28000010030902a40c40303146210080542c07a0360519119800315520301500419540c00449000c4c005100203139440d03400042204400e40c0c01c111600420304002410380c0c86a4494507060f030104850421513900800e81d9401407003c41c019031203001c2a50b283c401c990b0b034800280c0c4d00380681400244128010503c0c1c03441c2100c5e008a4001e800c0180e103150521080450160300041c0070010010300024074900188145a0140030022070364640640600c11040081d058001444440080c940120700da00300420000d000c0300d5a581c1d607110b041d0910f006c1800220b2188002c00c0700e04482518010000d8002c540055151000c000010001c0000c00c00c0040102c0d1140002c3c49942a0381d0ba40403041009085641c024640d289048000146c1105006003420148030101e03506215000990001c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 996010809 1250 996009559 996009563
    0xc0c210d1706010e01020f0312040c0b0708180a0b04060c0213052a04050d150e010b010e04020a030e0619060b160b04060e0a1a103002042313030507 65
    0x84480001e144d00101d0800301c401d44486503d00c0002081001508808296480303103000d0000c2c00f80f11070301c4540200d1140b00c2c00d4805410103400f442203600d0449004008090000014042a01c140d40e950b1304c124650400d6011102041c1585200c00641c2420b050310407420050440c208903501c0d01c2050f00899038503078206118110134140712060408880b50898015120003010034104024928010048804888400d150349040426402e002c410501400445801c161070700001500c000c8180402900720b802e03440e041540310300a81020120034400c107800b80c0b4444040080510340070040400351469548506541001000407156900c0d007040000380040e8025088074213a10366007010b030081c010340710b4800c1050040066010402c060000408400c08150810001540c3c03034000e04402501035204003880492189070071001940038030281610f182c0091503502c04291140c01080849500c480a812004510480440d1b4140b0503080140d00060906080c3c4902d441950b005100340104500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 996012059 1250 996010809 996010817
    0x6090f0c0504060311090603091e073b0702030c0f0f0303060d020a09020301061e02060610030c2a0606210204020307090803121f1a0c0c210d170601 65
    0x100f0805c00c461201100c00404008100c6c90b01c0e410100120703900d8911003001044140c160b80070307080c00440003080c00e03001c07510110111340380103070041c403a5415100b0440c0b13500c80024440b11001e003d110707885122402000f25a000319240c00c1745118040c03800c03007025141401540b00810604128100004807640281d09481c01d005504051010811980164010245440c000300c008030b0081d901c0020300d540c4d4640c030410200710360100e20041e603e61a003560100e400011070000b120125020380c000c03e04141540c1b0f040019500b411842645074089803540700c0840801c084d01e401440068001e40010f0012140c03101e030040400300e03040f07030340c0528698002e000d9078010001552241c0211720800042248a007604e40d00c840207820a41d00102c00c0f61030480c038801030242207402102412401d404d640882c11903d40381c1c0603a0440000c541c1208240e0041d501c40e103110268140c941d0410501000d02c0e02e0205840d050810810301d040404102081c020015400d80041c03480d02010041c94000d082820 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 996013309 1250 996012059 996012071
    0x8070e060d020d0f03020c09010b090d0210120c08010e011505071b0e0f090115050f011b1e110f010c0209100e13050c03011404140a02030d0306090f0c05040603 70
    0x2c08203100034031401d0082d08069811100906260b00860071406040c1c2c11a101c1d43c0c48d0307132500001c41c00d07230041c10581c5800404a4801c4401030030a0b0300d003511400329500300f80045081c20b8410780190ba500e5542c40000800e20401000341c403040c60b900502401d0104895002780c0840e5600500a000d440000380000750320088403440c0c0601014000b0290581a543c0400c03491f2500384081560b4007565840f0f230540ca40303600742003001001b4031040c5c29a5802000350b80c9003502d2400440300026005a05d800454142241c440040c0343d0b00c120f2500d43c99403014210701d650903030802507481c0410071041030140300005e880b2001a03034824216541558100d81e5840c2c01c1c0c8811480304860800c80e04900e04d94a007420904c01ca4904410744c2420580c850011100f045140f201854241c03241003009030324076584400032400148259042ca41d960282c80d007151098481c07500000d141c140f1680040002c290388100612860f500c074082c544040340c580005011005881c40c008065109621400302003507030b196 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 996014559 1250 996013309 996013313
    0xb09041e0c0e07120b0a0513060509090109021003110d0903031506030b030f01140f0c0f032a070b0f0907090f0b010f09030c0603020d18030804050708070e060d 70
    0x1500140005030000701c103160300ca8036400c50340c03045501a42c40c140480c0307020301d0483c40c030400c07401058290f40003d01908000351801c824400c824400b100280c80e43e540b03440c0086a152038002c1c04601c241c801380004200a06240140040c800800000300101410b140280764111400b1045521900c0c141100090000142c00e04800a01180c1d40c0c00e2040601c07140006003066240c1c10116101da03080313040d180c6c1c084400344107508a5001d00c0c9402403150362507000480102644860f1640002c07190900b40c502079205c00e8014056004840d002c102460742d0201c0c0c2d00c415080744c2c464030030007441c1030000d160900b240ca540301c074484002d21401060b184040003e0360030760184007400042521030014801c1c040500e6008025101c1c0c03204690000d80305003584030110303101d040001c0031a03800515808045082c440114040d60140c140c11705485d4a814952070710b42014500804070318000e50312140300e42041e207099030400c80b069001c2e00450340030490a01c05034812400d041c1e04090300300d410889460881c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 996015809 1250 996014559 996014603
    0xc0e0a06020c01051821071707030f210503010f0b0a0215060a080d11010506060a0918020f0c0a03020f0f031b07031a160f0e0103050709050619080a0b0904 68
    0x190401e504400c1c07594078594004840070ba0001001c100f44281d508883d2100c11402030f48e90070300f114584541c001c40040010500322402440740c20f00410000d051110f09035205007859103441c50b4074000500000042000002140b4400d010f0702801e544a4641821020000c4d6070717000c05244d2826900455020808030394900e200760009081c050b040d2821043c8030403001d44851070000c00740d9000d5003800002502e900c2c24904a4020002c1a12441e8400d41401c05564540130304d0020500c41a0b800c2103840020311203c0301509000815100502d0071110b20702d03000f82019580c40d80c0c03000d00d41c000c1c10031020380d100100031340700c500c4da030050205c055140f40210303e40b4051060f84080d10385403c19041e83c01000204855500c110010101c003100030700210301c1110b024203200c04440c00600c4541d01d06455620903002584c11a4207407502698290700c800020b64250320071141507441107030b4181040c0c44a03400800300c1e0383c03205403580d0801001d0b002401040c0c1407034000304000c110340000b9102c2c0c00c180303101c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 996017059 1250 996015809 996015847
    0x4030209090f0d03090b01141f050c07180b090103080412170f03100e0408030a0b190b0306040c0311030f0405030d091a010b0a0e01230d0c0e0a06020c0105 68
    0x1039031088540f40310282202800801c00982d0a442c00b000c9440046492061040c2c22204080c1c042c0c60a50700103065891028200070f01c0a03d2020450304104070200103a003008000040c08922400c8074240d06c8011154080794440c016040c06811900010404246140f040d2001c0f903200d070a002d031135408103107840da0300501c40700301d12100403002050080514035500c0c0514031491240032400c0318551030742d1940318614422100180181d00401c00921301840617001003e900b0000341c81c1041d80351814001e00520074a17038022040c18000401041464541401406010546d034142084042203025007040b01d840010f0016258007c10700108040003070800c1181c0d10950100010021740c205840c101a01040b5a4101401056143c0000c960b14081a0880c0c0304243c903500c131220765501c1c500040d00d545d0281c20245522460102881c440030004070010700840458003800286440941d1010b0111400c0b58001c41c080d129074007050110b01e0b00020006081d0909082840e00c510b4032041800903108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 996018309 1250 996017059 996017083
    0x402010509060f04031b0509090c04202d07020a0504180219090b0117070f1107030302030909070521060a030f0b060108060906011b050a1209080106050a03080403020909 74
    0x300c00980002800045031030050086c168064041689540300e00300206010251007108a50700180d842c1d2140d840e081d846680c41c0307040c8640903200c00e024111010895005544144d89904518520100703640e0034091170061050420000c0c0d0514a0b142c001c24018105030107594040c9907035545269000c1c1b00040304818440d4018446024260f03500181030a0581c144030341007150f424039007032820641c06501006c00c0350942c0003040e449580c1d20300c4211b40c482d003800042030a0180305c45101620400500400c0d026501a0b002950b8401310841889002c410090000c4c04010080c442200c1003005074924882914034518054040d4990400055406c40e01d64401890049003001c0407007044507040b03141e032052400742c880c403d143c9d40c0c2da82480500da4040320418009400c0340140215900014034041000f401002180c0ea0314245036114500e0403007044111000c40c00110b010054200d090140102074401910440481480c40c0d0750068140194040288141c0300e08001501081c07080021925403c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 996019559 1250 996018309 996018337
    0x403140f030f0a0e03010c05070602090a090e030405030c0906010804081c090b0a0c0903050c1002120a030527100207020609130506190f09090f0501050f01090e060f040201050906 78
    0xb80039180d00d48039481448420042412044200b00c18541841803484007505030321850b02d002d010ba42e031400290b2001d83c20b6035000c44050004190b10000c1d00c1044854100c03103000315922401d0a082505c1e002041105520031103480b400c10080d640d0142105400075403061901d5120040d005c0707500c0b0300c08040d001c01e40702246888070401c14410440e41c03940c011500f92070104010030210208596980c01400041c0c80c82e0b1003c1c0800d013081c1003e1804010000251060700c9002d902c0c41c00bc4401548504c004d038001a4494090010010b01c888180c0c4c60140c0d42c09210000014003280c66403203504640382400101c1e80403688400b9512000201c4400f890002c0c915400340304000c080c80c0c010704007626840e020301c1c000109003080e000da00c3c01050540b9910340d00e00e1441032801c240280542030180044600c4d01c151382d55080014000d00415001d2005000c00c0c0e42298100300004048030000c1d00c801000e540160240181d0100032010a0307000f03902032a04d41d81c0e500c83d01c0041045031140e850308980c59 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 996020809 1250 996019559 996019567
    0x120a090b0d0903081f0b0913020f0d0c0c0b220204090b01090b0d0b06090402010903020a0306050a0b2d1f020109020315010b0409090c090203040501020a0305010611030403140f03 78
    0x16142c0d440315103907901c661a10681ca885002007015000c145030020008000040d4060041100d4140940303603684004010006200e5018035540590b0003004c2c150300d42c0c0c54040352003405000103000c0d0342983c5502d89001850000991940484054060840c0e800050344221707512084880d10b0100005c19005001801016800c0c035102e80c141c00240300d45044681fa24540c13139420320708120346c9816160000c1100545840e504208400342c074018004905100e0f40c58000401610760a2401d002903008580008061800e0f110000554280c007400713521416081d42420100b4488010750b0a180860074094000524400b01040f03204444610b00034103003100c8840036000359415000317a84860b20070380a446030803c7c40040006200002e008080c0000018042441149407030ba0101c0080e501500b5003c42c1030360765076110003c070303402540d0581c0c081e500000c810140b00d4140c06194010209803070059042e454580c091904c80c001d03404024030004c040d203201c22034880304012030010307e42c45505403075032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 996022059 1250 996020809 996020827
    0x1203050702120a0201030507021c03021b01090515070c120c03020c042906030705030619030b10061d060d0f0209120a0302160605030118090f150f0905120a090b 70
    0x43c4a1803407408900103410500042c80c254404545c11106041c6411f05c0c4181c1d822030007040c0c01a411140b0b496803d82e88400c02e042062400740181403196001344050062504c030f03c120741e41c10701030042c180c109008501c004000022031010803030068a842e4500040324506c0d0f481c0481c184a00950403a50160504001c8140321480c40b000007000010030350013104c010407490034450180011030b10303038011800a0000a805080034007000c4c8503001c5803d08035400035200c0d9240d000c03c21003501d0890f1040459481445070702c0d003212007140316000396401004410701010009819100d44000302c041242c50f00305c0c0350514079003601501c0d110080101038040d1403841c1c0348415601c441111040d0010721070f803500c6c1a003078403080044030b041d612113a99a52442c5c0c05d20461202d007072b000d0003420701091340e00c80c980004507580c901d41d00052031240840c030f02c0005006e440e040c1a1030990078441100351401000c4030000c0c10019480007507448605030151602107140c425141c180b15903004010400c00004c603422 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 996023309 1250 996022059 996022063
    0x1e0c03070209041509201507030f09030602040e100602012d0608011406030c01110615120d0305070207080d0c1112060c0c011404020108190e1605100e060301120305070212 75
    0x4802c078000c00701b014005110800a0004103001c01d62404842004200c010078459030480e801d1800b5030a07c00c0482d0380d40d03a110412071344240e1205142d0f528010611020485000c1c017040204060710080c052202100300401034190702181e1903202f500c01050500c070201717064011000400e40d070002000b000da03521281c01208442101e1091282c00345030941100f942c003400d105503d4941d4203000742442d42d41c05585450f24640c030802540d10000040205904420806c01c054a038403c070b60300483c45003808540a490004142c21540d200c0e000380c003040300346652001000b401c194010201403480003184010030401220103007504150700a0308100280008604002c04295103070742c008002c080350380f82a9418240041d07c00a0000300c0310800715242d00160308028900c180050b50000b00c120850402c40d2401086c0000a0449031160108020919081c884111440424106089400c07145800070b074007440140280011100c80202e0308003810f2081068030350722170340a04a074208412010b0115 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 996024559 1250 996023309 996023333
    0x102011514030d0c0b041e0f2303030c09011202040e040503070b0105030601030c0b030a0b03010501060c0201080c030f070f030b041104031b14010c02030a02090c1e0c03070209041509 80
    0xc0c0c041d20a104030003d03040c1c46860b4058025810402c48041d5403516502d2481d003480f18540e264402505100c80800300e001d005a52105610440c038a0380095041c806000d441e0704e24070b040c1038607030300213104100e04c0f0342801e012100808070910300001d0045503050200001d0142c0e4001403103610300d00080104110001006144550244004070101d82c0d0311406c042d0380b00001d000080c4070b0344c00020200415040c40c0f01660700081c87c4000820460213240c082401c4072000d90000000410049a05042d960003090781c54000d21409501032030f40ca001d20000f1466071001d4089820404c0e4130601e5030000340300754043c50b640d060091040c0205500f180c02203200ba0001d00040e11150f03c12650321408211488840044940c0704803194866101a001507440c442030040c00d03a054000c0e440b004005941e20308034103101c1c4c0300d01d110442d203e29804c1c502c09010542441e001c40d00d100208440c1e044804000f0544950700e60480d910039450b5030314030742412040304819100105c0e90800807c00c00b080b003562046 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 996025809 1250 996024559 996024599
    0x6011a16060c140403260c0a0302061602011406090711010612021008060306060114092205010f080304050d33151d04030509130207110609060a030b01020115 69
    0xb0004002449219801e14441c45c4001808888200032401100c010044151103a074408000c40d805d00e501a450103003020101841200183c0021b810441701c90f61170303400c0302480b0700184000c100d10f400c18541d06c541e850001d09030621525130080016906841040344007442920b480003803100030b5413103465000048846104038810070418008a04007882590303800e00c00c0c3c00080040c200340c1c5801b0019103d1441020075014800310401250786940c407001d400c1c0c815142d007840d00c804581d60081001080710b8044e000114182c1c1200c03020010340b070001050b00c0c280c40084a900720305184030700d052880e10220854140141d001d100d85840381c000085019a00614129424403001c00f2401e024004e00b2601e0243e13103000030342c000850b560400784c1c007074196000d4840c0c00d00380e00c0d101c556000548100c0c001c40a1030032458002903010200b00c903a0202c0e81808405964060901441800156980c001c0120540405941d800030140c2c0b41c2c130075080340c0d2840c2106603040e10b1958031080192140e119030100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 996027059 1250 996025809 996025817
    0x80c060702030a051b090c0f03060f13020a080f06040e0a060507020a0b072606030a0602070212190501150302010e01121401080d0915020d08041502040e040b090c0306011a16060c 78
    0x70384044850000c844020423107001592850b42c03028100040100c181c00d2413a00460401c860308a0646144010218005a41c6900c40c0610b084900d510030040f004000714000c03420304813046c070032003000111900c10039445070000c40d840c0d0b54890103e14112010001404224a001c18400c0582d001140d0b10381103881c6001c80050054010200e426000081d10b495400d648000e4000000c00c2c8168080c3c0b02d0306100601c0a000c0612000900d0320344603174180780d01c1c068020003207810f0410509109124000401c920304075080ca00e140c002a15562102d00720b941803102240e08403030f90140a90000c0c0203401903180c10300003942c580503059503402e91030402102113201d10f01c0c0441c9801400304070252103005903004081031011540c0071541864050005c072406c0c404101c80d824566590700160010b00b80c080444c1005107450700b0025411607007e807903441076402030300f4079036a26240490310906450244581a040300c840400d82001c51160313003000603ca4450380101d104010040d003214080140703940d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 996028309 1250 996027059 996027061
    0xf0203180105060909071703041701270f0206160b0a2301050d230f01021905070309030809060c1203100e13150f15050415080c060702030a051b09 64
    0x500103600420340c1d03000c0260788081b40c20015501810b8200c00555036032016242001d58035030b0440e0788a4407d60081c400759440d8a889030142e918040400510000414040c1d0000460344a6080010890001074040c02c800504449600301c40001040710a500042d07d544070700d0314480f0300e401411025940e00c911209241e0b2a00041c01507031815041c2c2d02e00800c9038114411503031324a0303002c0c0d81d441c1c903680051003407500741e1044040030300030030301a103000100240c1da80b4401103488903081d003001c01c3e031810f106061150f5004203501020031029250300c60a134954626003030001030035500800e1002c079420310500500522110300c2d0070103180100c83d0900340c0100d184c2c840310342c00c0d0782440840e100b1014903190615030000c41d5005424400b00c0510f28400600a440d060b81e200036560150055039696008010821a80c02c080c401c00c1504001420507079185d034180070030961035140a03100c841c8030310400b040240035940d081c8004c03460103038098111451190780c0c1c20659a507032400c420390f1740b10f800004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 996029559 1250 996028309 996028321
    0x60403080f0c130e0406060e0103050706020d0305091e030f040b07050f0309011d010c082b020307050912030906040f060807020c0904200915120f03120403030f0203180105 75
    0x3030300f82c41020740c00304580308446081480400c0c0890780148241c030060b07102c90300062821400c00e5044d0187d4001c4003e00041e5040110103031916940300104c2007090b191070304000c1042c2c0e0110741c04069041c405294000240c518600c0c5255001d410b41e4078031903c02c001070000300a15218010301181e03101d131060703d40072806101c0303190700d9003e400c45180c04a540d083c40003001d50340740c031307000c0001600504052030781d9102a1150b41241c0c01c00c1c1c079465222130804000c00075103030030603da400d40b185602005629500e84000000c1c901d0092084103401081840900201c0303840c00c0c800d0f116095405072081c1c2d01c46a4482c405a8201c8940c840c030300c003054075440414002403021071040242c41d4040c041003919211951400d000c1031080000c94587c207030300c0c104d001e41030391074101d11802220012040c142080e090010807a101d4a04540b81005911088004440744000300a4800250032000d030090250366a080940182424040388a440c0303100004010389115118005402015040020009a9198 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 996030809 1250 996029559 996029581
    0x50f0304080c04090c0b030c0d09030c1505040503040603020c15040c06120c0503011403011808190c051b150705010f050106050c100c020a02130509060907030308010b03100305060403080f 82
    0x44c20041d100c2850f1032818448075084000558120000035030b034515000388500810125411000124002082031962130305001c0d03150b40751000030f00703000c908002c141400c0d035a0994170300c142d110781d006041d004603060262180a020f1065140115013050215146c10319001d20411894051000407507401c401016001016106d42d40d0b0061154582c180b440e4208007260701481101c1100311390640d241c0d2082003e10301c031041c40620f20752044042640300c200d1200c3c14009003405100c48010054101c1010000c22000651902d0200280d02d1a105049460000ca403821003280168008628002841410044151b100d00e500465880702008580d0301c5007001c03900e500c42d450300240d240d40700700003141101c2c5a507409180c0710061401101e4103001a6030100700b007000034600c032200b91a0ba4104000025805101155000400300040c2c130401d401c0d039070040c2400106004400c18800c010000600030700c0e54002d0880a1508607003200e9592a00c3d142c02040c0304000c0b640040b240c02c801c0c0200740b5541c80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 996032059 1250 996030809 996030821
    0xc0d080403050601172505040f0b1201020a05032d07110c0609030a02090a060918061409190201121b0e010e010e04050604090f050a050c032803020109050f0304080c04 73
    0xb4200207000074a8441c101b4480c154139200c11250603040300750000a5564891040f00001601c040340810060b000350104540c070a000269503220385d004201c00c030b0320203601c08200c030380c0200d5401a68036a040c02c5252080d410341d8120324030f10b440d0f0358002401446900100d840c401d20070f445040f10300c01e820140910116000c0d44c2c49490300340d40070101040062405168030b5034400c07a810740016485a4400000081d0b9121258078200320702e00c4101a0309021060182155880300c400f062846c034206051620f0355544102095210104056150b030216841080007405280011030140551885007038159510003400308110041826180524440d501071034007650309100503115040c003040344800b844040d100080c031103544166200002d8000070082240080804e016038000c2c550800c080c0341040c42d18280d2007166101b5400b4a5401c000702c500c00740c80b011f200454664240b1201a2460140d000d03080890008009000ea00301c840f240040c004090001c41d2641c1c0215442c12000c9400d000458072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 996033309 1250 996032059 996032099
    0x3050313060905090106110114070c05011112040b070c02090f060f150d0f0b060c0d090b0906030a0902010201090b150f040509030d2003090d091e050f01020c0d080403050601 76
    0x20131401081224000c265088510400f18000b144034a00a004c0b81803000d82110803034046990040749200b48003091041170020740c428409035207401c076100841da0408100802c02407054004c000010901f510078001410700681c05000d01800c0e0074942c509201442c1e04680550103101c80c02d490a486190402084103000702400e181c2d4030f42003003240080044e000300f1a000e17211540f03601c03810070307a512080c0052440c45215009411034851486c001410f1111076404601004410b000709085652801704a0307410004504001401211328070060b805004405d0303025000d5600403041217098038901d140d01e0303c0040102c039010925202c0504000032a074040d59500059071090207807030307400415580440c18644030001d400c4c1c0f002e443c00081c640540e00c1154112015080010780010094101603000060600c001003e41c3c04408421903c0d0200c40d644500c1e84a04110901400f46900911103918814409801c100c220f65807800c046619511a200445451140b10000a0801d5580d00070b000c1542c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 996034559 1250 996033309 996033319
    0x30f140d0c080307020c060408060a0605030a031b150e060f0a090804050d021801140103060b1602040b011827060e010e04081213051b060a2003030103050313060905 72
    0x1500d41d01d0380511500000c140344d003541721b01288804d2641e00c0001400050480703000074030f500d140068640080c1d5040b42d008030300030ba02a00c1d40c5d00009411011202500d0140b0142e82c001340700c0d50800e40300c4101c000d500107014501d48900c1d1074101101003102c92241c0b0784003516007403030b880c1d0f820503100300e601c1090080c0c1201001e010a2100d45010b100320020540000c0c4502c4102d018592012205202a8440f103920381001c0c0103829696018000c000003801603281d06818101e0303102c45810049420000240f0950366044142ea081e805101c507407002c0c881d203d800e41c07801900c401b144514028034134558426988460023402e0f82c11103901484041d11450038000b50242d20b8050805009800580226034000003480742d190782d01a0030805c540f16410504588d2402003907803e001c0d050480c1d5103c1d6459030516214003c44a0316101c00f26080400140340940c070030480e415440c01d02540308001d1031100e00000000009200001002e08203201d0000d0100340207170365401c029a40c060081c46455049 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 996035809 1250 996034559 996034577
    0xc141e0904020a0f17012909100507030207290a030924060f150503090c09040606150c051c021207080304031206030f02041a28061d06070201050c0304030f140d 70
    0x1822001c104e00c1c00103224034101f64200401c0c0300000d04d40400600ca1580040d41c0800c88105240c0d0400000c0d004000f2030b201d00110b40d6512100100e100c854408400b8a16400603c840d4107910942c450090160810b0401500c00f1910201501c481030003841e129940c1d003000e07804954280166001400c13610041c00310400300b102510140e916800090800b50320b4010074080c0030090710b0310000207228901c500c2000030f400741403084005404007122002001c01c92241d01e26000904000794031420103580760942c42411800c1d4204903d0526034246204900e800407890301c04102c4000701442c0664403986030761020851f1140700b2803c1751840d100103840b08801394801c90250030179a1040307540e0302814020007804824030000c2a40d041c40602010351240810b0140e40c1d250081c612207402030130031480c055a204003a8820000019003d9800750b1050900241a500b10fa02800403100c3c0c8011000980c2d03142ccd44d0700c0c2000340c08468411001d50f00403094a086070304001c00801c0c84c000c41c4040fa1aa0300c40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 996037059 1250 996035809 996035849
    0x8090a020d05100e010501150e1018030503070803090c031f050a06030210020a020f040e060c03090102070c17070609150806041104090f0c141e0904020a0f1701 70
    0x7201e41008001d481c02d0059401c01e0082c1e1034240038030002c0d030400782c001180d5545054120480c0680516600d0100200e001d2140042e942e0400604050016440c224041e19144640d0500940c0c40f9800140144800100c41c010022814040c6218107020420344400020b10405d1503102c9014040f20048415080e110307c290500d6603108607040008060006080d903100c0e030100d8406c10000d0340000150340700b15601c4085140842100d070840300107030b6042c0124071055292a03910840a0308068100398040002a018a025415100e20715080180790b22902c4c0d54001e01c2005c0343c1a041029028001c5440105050380a04480000c031140925880c0300d0402b4200221502000a0f02c0164031940b40c0d4815030b061103800026002606640c08000781c0c1c000c000d103151044070302c0c0c0038100061028000c8042c44100500d01551840d62000e403001103100c250328594011032040410641e4017174030100c0c88100243e409010703d2402007003500e17082d80e0f07194032940d4414103100034450302441146852134451 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 996038309 1250 996037059 996037069
    0x5121e0d08181e06060301050a020f0a12020f070c030521030105013b12070605031801140106050a0210110d0e070e0403030e1c02030d2a0504080d08090a02 68
    0x4800c1c40c1c00544032414030f40050000803200c0c0c5034a401a40d80042c0c2440042e240078407179640c210058a10451a107140700000301d81c1c0d8094492050240009012140c0c2711400d190100c0b100b050910b210305903298280c0c0b03880b94100e15240019a19807041b191420360380841d07005200c1c0c6c050340e014941410341c1c5c078110044a5040604001444026140080003018103a084c800210340e585d04801e00c0400b81c3d0b140a1021004007a0300030740c184d80c454101041113640150449402171050241030105203580707651540542035007010b4010b0200302078000212a0342c014003900d040c9045034240e549024032030100d0030955244075092018600c042141541c00b0300694840c01d40c070008101a511710b640c0d94084161603010444040e40401d490300003443e0301c441c00b4400380031200c4043d01c088d101103404000c001d5480c0240480001c2c2c481d41c03040e2074045d200442c0054042003200c500990801e550000000740640c01620030142548588008940f07000c7c09140d81900c51002d100082c0409122a001c102c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 996039559 1250 996038309 996038341
    0x604080306041d070609060315050d111f0f03050a0504050c0105030a0603170706110a090e04060219030f05060103271e030c110a051c020a05121e0d08 66
    0x3403c4540a80000c02c2c01d100e0500c2039a005142548403050b41030300c0c041000d01911401071084c01820306004040c011542d440341e9005010b40c0100c0b60824651140300881c28150005280d40043c0c03105002c06c03c1d8095208002443c0e0391100da0b020700258031111a1a01607c205981c01005038200c00d040600e2075220b00051035101d10880d501040403a5030740c8840504403006c21500000b003000082c640240801390161400e1491036004d541d00d0214100d800a2903100b0901a15442000240100d0140040e0340c0596036078000401c0701c0008001e0f010800340042c258a01c1e91917181e800c22000030420340c024840c242d41ca0f0610341c40755286003201008128010b40b0141c04480701503010901c0a10201e0807165140c003244a51250306450805e42091b8919000420000d4458000b0b02400e20803512401f4441a04102001007803000303140340e2000641c628201c0d00480d03044604641d06240314100002c1818114140020194000308400361081d204c01c4640c3e00180272a0807540407416000c84410b0352 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 996040809 1250 996039559 996039581
    0x402130b0d060608160b030a020306031c032a1710030c030f0311030a1d120d0903060605030606030c1c021903350c01060e0a060e09060408030604 64
    0x140c0400c0310000440007610240c00b619002c0e55094107101c0b044007003080303e03444402c180502c40c089140c04c0c00da0030240b0004082c9400e40b41c003c0301041040e00d08001030b061030340c4000001c245040c0e00540c018020100064083c0340d604205441440e8182054400b0080c80441c0e0380e40e441103060400c0700d9410107030140150120034960700000010660001804015511408002042c9005801c0c01820304440300300c0030944c0d030010014420303a00d0700704000510460743c4842d00242c6500e04000180440801d01c51180c1030b003d0260b03461086540b01c6208002e80e440348908124060700c500034150340d100c04440359505580b10180845c6580b521b01ea114030700c0315086140341e00038501580424019020203903141400020750382c05104002c031f260311082a554198041c14003021407004011101d0b08820002d0081d4840010100c8010a00790402400313090340e804102501e08004154000130300303091142c0030031080398001144491101165650241d50031040c9142135890f41410070000b48031000762 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 996042059 1250 996040809 996040811
    0x20a091e090503040e10050d110d060e0709151a1b0a03020a0c05030625121a09090d050d02090d060c02010906050c13170313030b150a0b03040213 64
    0x26030040c12518018109040e100384007540c1c95034504001c00c155120060401140e00b80008400d002607151422a04640c9800c40c10b080012040307403000c64544070340c040001c1c0260b810300c003c1c039a61050004002003110200001007011009a11054103400c0c01030151051041c0c07001c4032000381d002c1c104050400340c4046030078141d4240c1c1400400c2e03c0c09810840c202e015800520b585024800040301d12402804150044c029519009902da4402c216050b200d0138503990303100700d124501c0c2c40358980441d800c87c180d50030840082c03200801c41c0c00e000204081d502c0340081c240010b06000e004203d5a20000080e1116403e101a03450890043d40028440740d40140e0041302c5003010601901500031110880d400000311512641404001d9031002410303240d070580c2c200408420100a1001c16088905480c807402038500841401410f5219440060859814204001c800e200815902500413000c0076003603081c110140c0c09000c00c042c02e600c1404c1012009000040c09410301c0b6009881d860326040c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 996043165 1106 996042059 996042101
    0x20a020a120504150c060507030b01020318010c06091a01060806100305040f0813090506040510030b1302091006020105010801090809010f0e1525020a09 67
    0x18089541d000d00081864410000c0d50090b140741188030401c0100604010300c10b05010400355061440c15000c60b840601a110344014050180c000d1420200c0c0c2c500c40b000350144c02c0314494117129a40003000c00150251050b85c4545104007555003811041d055005014001600f03c042840061400d1203c0342ea902400d1354100e4041386800b00e2265558039103480d564040d444020001d40010030421028041600820251010f01c001040310390346e50350401007070b80c0d800e4400303c02c5041150000e201181080c0381c2da0340d100c2c100340b40240c210b80950303010940c9154202e40e6a0503459070036509100c0641e082c01800c1c010301c0304900901100540c0c1d11807035071621a1540e80e506002c0565070410a0b540586020888003030000e003120780d10100c9034800165640030800521912098400031040100804d035181d06d0160060300028200e402c100c0004000c0000503280c81354808005 = true := by decide +kernel

theorem cover : BRFrame.Cov 995863309 996043165 := by
  have h0 := BRFrame.cov_init 995863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 995863309 ≤ n) (h2 : n < 996043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
