-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1811
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:45:47.864906+00:00
-- url     : https://prove2.me/submissions/ef5e3756-0ba3-4ad6-a257-de4dea6ca25a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 325539568 ≤ n < 325719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 325540818 1250 325539568 325539589
    0x19020609181608091603020f010c12030605120c18070c0c0f03110103060509150406090e0703060b09010303020a0609050a080c010203070f02012c010e0a20041806050402 74
    0x41408441d07507414600b030303a4403940100701c00c0300c4002840d003000951811404074060013250340340070442d194682075074200403e040d011b41c0320a0420413106421000300e481c44080c1400004103850000308c55081205016900110a4108005a0002c00d10f520261204012404a6008541c03100410b8070781150848800c0303000035001d407070301410140105003006095801000c891103840c20443c1c200185c0010b40944003a03100701e41d030011103540001e605003043c98249460800080001480316115096903040742d40d10381d03814042d940b160354240108045886500e64104c070403500c0720300b55855990002d55800e0300f404010506512503d800040007010000c0417440d1394003d14080c1c0300c100082500d4000e4004590800001b0095941c440d0b440d40103100700840d141e403881000080380e00035101d038108040851150402d80d135075512440003641c828031038071001c42c1c45a0005da1701004410700d04147d0542c0c50f40b22a2055141c01810001c5070301c1507541600e000d5101c40085840da940b400050000e242 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 325542068 1250 325540818 325540849
    0x90603110705010903050a020d030911040b030c040507111501080d05182d2e0203070b070e090709050906010c081615061d0703150b0a0201050a0e19020609 68
    0x80131484400c1580010151205000581c00c603800c442c80c4000880071795407004c0026051400460030121981002d030000c400400d00942100c01c0c1901c1140801c00b200c7c0d00704ea0081c00655461024200c000d004d0160980b600702c41d0030310400c0c0754149000951944101410030080c0440010030485152000704941806000105658042411380709100080401140410790800072000091030624045842c0c0c3da0200c44413805200340583e0f150407681101141d911001548020702901d800580e01c104454403d82d07272035071404004d4240e03205003e0058000f905902c09c2c4034541c002409a03440d00e0300501d80c0041c0900e8901d602d19003030f04060304d007171181c20541c00464124161000902071000d9201d00400c42070441004007540e10300401451595032101840d8a44e95a0041000703030784242c004101d505d0740c400000310041c0e030f28503443d201548020300070700160351142d0402c07515421500c07407110310707030700407030281c1281002c0c0c90b1050095054403000034865000480c50f8503180c0c8400220344d080f1134 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 325543318 1250 325542068 325542071
    0x2010b091e090a050f0717030c06010b090d021908060f160e01091d07091d06060d0b03071403010f27110a030501020403140304030b0109111c0c080108030a09060311070501 75
    0x108488032511006c96005031440d0310380c1a003d221a078100081100d261042c80c03009029980d0900140080652011031019070140414040901581e41c0900307110000301803e0003025124513003c1e80c642001e00c01090303800c02c0510081045480d00d860b002192100d130241c50f10144149841c401a101440150407240080142080c017000588081c072440d40102c0d1031743c1f541035002e9600c2806c1d1402031040101001c0c1d4860040111f00c5600341040544618a81c100c4003040f10482c00d0086850b0841981c061404170b40c80821030100d0307042c01c0c815130007a506110740900c402c00340d80120b40c6100b09082042d11400b44ca20b1154000d20684c9000382c808101d0081602c4009540c03420900d01039005408203031160a00700a2203854100004200c500f1668007402030042c1d03a20302418100100169aa9140d5134101000345140c0340300c0000300e01c403a1884141d00013075030140c00e082c002c0803568140c001c01c145070f01c2001105070881d00411090212030091030041500f868980340f004041c0135103240203041d0b6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 325544568 1250 325543318 325543333
    0x60b0403030e0415031109090f0d1107030501020c1f0209010c0b0604060e070f1128030203160f1b0b0d0207060b060f0703080c130302010e190b040602010b091e090a05 73
    0x4040c54440051041b400c40c0c00541645400801940314020f000b42c2000960002038548034450007080b40982005c90071041d6044552340c3d450f0340742a40c0c002c1e24aa5020f40101c01042344050b0151344198001151010450610603907200281ca83c1d000610040c0104035007a0000e100c0d60340c0e0341c0204003e08030110820340300f8188100080e03c01d11140c0085404564861720000200f50000380c140300c4141207054010410280b48903c103c403440015056045000800c26035041c00003c1d00c808400d9449900c0c1e2034507100c900c0c02c102d444560600e0300b003c80c100000b40100640d41d81002900c0040d5a4400700596404140c50500c00402003039800d00d070401d8020a010030b080704c0c5003000e410054002c0e2511599955820b1109906114505080405e803044d41380c1880907506c01e1440c84034130440986008986444030640a80c0c003100c0d540702071b1f00c0b00c2d4001400d00c002903080c05521903507042500c4450076414880301a01181e050b00d26147c110302c0c0c171000000e0f41c01008114821b1030b43d8019042c2d40c1c02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 325545818 1250 325544568 325544573
    0x60f09060e281a180f06040803040b04050f040510060e0303071401050f160203040909081c0b030d1b02040b01030615110c010e0108070e0f18040b010603060b0403030e041503 76
    0x403410b1807040f4000d16030b840c1650700d06041d0100c115520301e03440e07a141041c0b5000800401c010032414035075207a0020010301010605500410041000c0c0801c000c5103a1640d00c0c1004102980400070100b50081d4209001d00104441480710b8505462803400e000d81c000300300c40046851801270000c003070034010841d0f6001c49501c0040d4025030040041d090740300c1c003983c1c411690520044581030b0200040c0d108020030041010b090b4030034202c0c5841041203600d0804000720680b80b1032442007466054550300c48240f8510b00c0c0400414941010300d0403c14014500c0861038170040b0021040a801244c03240c01011041e807181d448140a000f0600c480003140100101c000d020514603020851544120b1007004071070340c000d00719120150320503034075594550b41d0107008035600d04003d501c15801441e000c8842e49659245404600e0411120f20011441d180506001040b03100690220041c103141c580b042c0b012420010840d01a82d406041680b10a201900410010802e0300b030388003040070886402204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 325547068 1250 325545818 325545889
    0x160f170d1d0303041e0b0703021911090408090310051b1b060c07050706170a0c1707170a0b06071403120f0702010c0216090e070909050c0109060f09060e 67
    0x6522010305e040a1050386900007944144103050001d0007580c480074004550580810254507554031030b95000315030184c50703c04198041020346d02110710b20000309080700300c0d01703003003040c1c8088850148090110381000380020500802e480100c400c6d00f580060768049000c550300d94004440f08030b4007114403501c2e0024142c1c42c1c1342c2010038122000c0c00395210005015105600b1100c540c00601078001c0e1549500502000400c040c0d9141001d000400120030610820071240912650490b180c13440e611161600945103010001e241855403032818070007460503118030041c1c800f480e9009a8908540181e02e503e45e18601456600011001d0000100718100421040030f43c040e200c02e8000388210380310f00d5403c0e070711008400108898000c0c4d0080400403183d264202021102a80d001d07101040e48a00f01002958644c86c41501d5962021504c8102c95030301c415041d0043c50249880c0d050702441d240014014502c62007000d042250755000e4614541e60020b04001d0202c0032040130100f0b1079203808034035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 325548318 1250 325547068 325547099
    0x15090506130903140304111002010203071b0503040b0c1e0a0c140f0f0a08010e070609060903170f0d02070b0106020706031103130501020903160f170d1d030304 70
    0x60140100341203620411225002d924a102c1d85501c40050544080c14001c02c00d4000503c103031041d00b0155882e0a00b61121000000e10000540c00541d0b68580508098080c4008071000558501400303603481c0445c00100903501910034442030b280d940c1b40003180440c6041d122220010001440c040d580c03900140000e240003403540314100070b03181d1659a001e0058001e683e820b80c140c00000303041045880d4503051340b1020b4400001011200302c103807246003403402c443c0900c0410030158000042809070342d410481a10042009150488106045680c0c80c984221260326221103030501042c1c40415031410705c20348210280c8601b04540792861418000300c0d07160203216107000740c02042004a0340611a015440f40b850301c0060783e078036544500c914050040b145076025503032958240003001d2640d030305000c7c4821003400c0300d182200243c24070030701141c102c403940d100102d005009a00824800f1000c907144031814502d04145c0c1041a030075094800c2035207004412507150000150102c0c400c01d8000300e50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 325549568 1250 325548318 325548331
    0x10050a02010c0801051003091712010e0105060f0a080a0902060c060f010806090d0e0307030c080d17040209070c1106130e0105060c060c0a03061a19090312050904150905 74
    0xe019410006038195035a0f902801804e400c90f4902007500d180c18020740010910900c61500107010300c0340458114074641181100d003145540d0315004104010951034401d0142c00102d8079140b920b400701008204511880c006c60090003091000078012840c45d500803138003980c0151405503100108030506481d540112a851600042c50f40086482c0000040c2d55114000c100020a611140403d080e1402c3d5501685c1961504c5420400700c000b41c0015543c50003031a2903401071907500089180030705081c1c0c42908080750385010008220240e81c840e41c046405c41c0050420182c0c1c0d00340340c10000c2d1002072a01c0c00302d410500001e01d440587c050300101d001183d030001c42d003551598032941001028070407003100c000b05500c1840480d4103c9904002400381d00228103001a00940d2440d20307810000294020100c10840421007292022220700c206200d41c940f0304d403403c0d10030304603a1003440b2200740c2581c80301001000700d00c0028a48595100449030340d8010010358038540e94444070740c040e1000b180c14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 325550818 1250 325549568 325549571
    0x10230d09140c01020709020d0204050a0f0e0c090105031603091a0a2d05100306090503040612021201060806040212180712080306010c1a0a0510080703020a0506030408040510050a0201 80
    0x2079200140c010905003107042c4143d0181004d20f1401c0780440194200d64521250198200000121651258621401407000f10302d100006494812030540c0303118001c1c0034800c80c04040001d084076a0303105046990000d6084031001c000e4500803022401800108001840d442d44002048052140c09040300c0c03140c6a13000c4d06104640c01031104482b0200c1080004032514020b0041c15441051a084032f580300f00800b001c4400c0580e2511802c00b5511101ca042d2020341000a00384502c0350300c0001d65102030b5080c1415031030034290140d84c40200f1014492402000a900c012407166601d60701141c41d034007211907442d02a81050440000070341d0001c03000140d64070a148001903001c40c4281924885c1d60000b0340365003166501001924803074040c040c2114488007030302c440706003081941c2c1c0890180444150015261070001c0c20824181d43c1a001b294113540104420001aa2981890400c0d14010f40f481c80e107170b803101e1500341403034011600000d601040c20307a00740180aa004c0301070000719146900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 325552068 1250 325550818 325550843
    0x915080c03150609151804060605060f0703111906020d060e0705250803011d090f07090b04150305030a020c09151210020319110910230d09 61
    0x209507075440301182090804140c02d0018850780742640d1036944c090342410241d1038000000c4005465101c03c180c1030f00001031722400340024400d540c031404000d080309860251034131705020840c8005008031000203003040788444031040078000c2801565506001c0c0e00501e24030807442d103402c0b0040c3d00040d600220302840e000d4009070100c040910907001d04804d403100340c40e040f03183d00c5128500c3e05005802d003810024a00a40003e840c2c040214000c21006510788403118004000000b4000701500d21007880d44000c0c1200f04925000c1606800c40d41004800a01c0161200110703003c1c2c20b07889511101c0c000179200010a10070040000c1101d1000340d803e585e440009030041018104058a408614103145da808085d00c0c14411ba0030851a00c0c0039048545000c44100b01d6070507a4000ca6040f0000d012050580c0c41c40e2100340aa070102c0c0725090206418100c0c29400b1803c0f81548080800403c02e02d4502d02d448100f95100d40320807465503c1215036241e41d11642d0070701821410304115480ca44008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 325553318 1250 325552068 325552093
    0x1905120105060d0803102103020d1806030b030c040f0b09010911030411030c0a03030f020f030705122208010902130b01020705090603070504050f0103170a0203040519091508 76
    0xc50070b8400e01d0002d140004544030340d1603440e203c0d003004003c01e00104480c0004aa090b0449100999034444507825a02c0c1d41720358640203040c4a01c1c007545800f40400d088a8a000a602d2815001078500324070b0000703071040c80d420000f450000c40c04585901305282024100d2004000c0e00320040d1003205540c40f4109980e00c0e0700c08012a0055561f08070800001d101043c0042c40001e041c1d096100014110b803042c0389600009460390061740e01c12404a032011011300301903030f014084e00b03458410000180d41003109540341c0c651511907403540c007071501030001000d01c2240605240b1015030203002d4201003095407201000703802070425003000d82c4105801620408045070340c0c024400601410b0b030141c071030107180009100c54018060728041d494000d8480216840e02d85100307144c4510387da0201d031200b5500d90308040745e0b188024400c601004800f00600c60310303c4e80010403141100d00694103001907201da030424001d85915908a4009642080714843d001240700211006540a030750540f26104c0c1c0c1c05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 325554568 1250 325553318 325553321
    0x303030e03071a04060204171e01020901051608040812030907050a1401210e06041502030402090f09070e07110d0f0c03080a090c060c0303050f062d19051201 69
    0x140c00409011a511480c03083c11034044500703030464403900c00907007855103513070711710b010010007e900118942c008102c250800c03466880e07111440841a008501d407100c2c04000802078800c4109009106002014503000c03c205101290007e040c1103040e01c0c9881c01206114286900642c0c0c01c08c61440341d07010100b00d42c90a9402f82040b42c0c803a0207a0740903214440c006440500c29000d8801d8560410701c0c41c5101c4454500030b031501001e0180c003404003850300d45000030440c80741c0030f0700f040d40f01c0c814001c0000584544e840c858001c1d043c000c4001d00382e9034049000d490310b01d254001103440e240c42003d0282c0340f904580395074920740742c403815a10351480c400821580d1220449c40e10340010412145140464000c2071410382140050b030000c20a4901c40c0c4880d2014074040d8000c0001a00d607556003424550725211f03c0d60480c850051080305400c181c000600302d95450f401d10490601c0c040c00e18921195102481000c000001d4140f00c4401075194000800010307610915000304010003c140d440c4206 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 325555818 1250 325554568 325554577
    0xb0f160c03140c0603010603050601110102160203070f05090f04050127050d0c150c12020a080117030406080103020111010921091e031e0b01030f110303120c0a030b09010f0303030e03 80
    0x261407135045a10380382046001c0c1c28003801d06414844840e808002100c8203000078251003900c031440d000300c84490b00c10f15107810842da0007504120000e24003440b044c0c5c2c4403207801d50044c034850442d002c2501d6a00b030581c0144181d0b211940d501302d1300410740480340590501c0b0f8002600550a8606d900582c40341034030103210301c0b40010f1004482202c000f01c05500c552021980040a10340521101c04603418041207070b00411b481c5000c5461000104850400020440042c1c0b01080265040903e002d5000d0200030040c00000d05000790b0850a400c0030301c0952144488a4110b034801c072944034060403888642000300403020004540410100740401c1d0200202040d007258940c00c20705919540b5800b03240c001e07a5440c544205500c0f100785010851040b0b00d00e020714010f80400f00b1700609480c00a03c0e003100144207074026041400328034142c132031080805d80d208000d0032045554142919046008016201c0c450750f000e440d003000400d00303107a04401741054900c252020000d4510100079070b0303900d000303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 325557068 1250 325555818 325555843
    0xb070c0905070305040f060e0a151d0a05030a120f0216030e03030705190302030c030c03030105040f06060e0424090e0c010c08040306090543050a0b0f160c0314 70
    0x40144c4500000b8019442400c23984150400c0d0341602d000c2e0f0350f500132112145030400d032006448481003140321903094035009150301d0b0782c001808144c1070f0fa528161240221000340c401e0180b150705030802007200d07820001e1000c0318040c3c215508e601080c0b0124549042090640025a41c0c00034280203040010480d214171f80c101008201009540307112480c0d03540b03420000c07004c50005108900c1101c074100050071030082103074080c0d5281c1d8148803d100c00ca074426244019518204541080705541102ca01e082c030803410381e400700700030141200074003030000c691401001c5555032100024603041a58442003d181038081900c40d190f5038000119441c403101c07007018204a404210400004a49a210f08d80300303481442034540151610b69104100e40004140010710501888a00c0b031446090164000310003c3c1c1d44003044650800002c10140c225038010b40001d0000003503074003285600b21050310050100310700c6452a4011502d043d003240012071008552a1502c004003918240e004100428650b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 325558318 1250 325557068 325557083
    0xf030608150903070501050405060412030c1d01030e061509060315221b0e07021209010c14032802011404110f10180e19090c0b070c090507030504 64
    0x1ca40c0c01c0d00740c0001401440341c6210820503040040d0080c080c0501c118069409401b2620b05810001c000b00443e2881400305807a0000041180f50002c00f00300002c0361402a40301c407840c203075005030010700c00314041c400d0510890042144c0c041003120160a2824103850780030540c0c80305c1051640d01e2001c103064280d2030b02e101c0006446500120004110103000f1051486d00a42d940c58807803030300307110034880c2c50b04014800c0300340904140c0074000380d041202480181800000b98020310380a0080c0c507415410400c281d503100c81440084908080041151740c01d170b96491107108d00000101e000e00c0c0c0102d0001c2d2145507186c520500603c16400140d003c68100c0c1c42070780e2a41c1e104a54100e140040540c84030403200102040c0c3c03104da80100701904036403105094404803940d200d4128000c0c0e84200c4202600c8020000c0d0081c880b41810b2060341c410f05d01041100e91841c081a40010903085401d0203003020981030306000340c20580c04116500c0450802c11610f910208a00342d41003110040d0106 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 325559568 1250 325558318 325558333
    0x4050106150309080d090804030b07050a08070e010903260414030f0a050709050a020403060f29061905040e0406020a2307020f01090b1b012d0c05070c09020a0f030608 73
    0x5c1d01d1500f003844510b2048007171074038080e100e5441106a10080d200c8900161001c90343e2403800c2d0304044c0640d00301907542040750f8010150701c0020309100d21400020812081c84000c0c210060041c1400c01c601d0341c50b00d045545403900d82e01c007030111190359698140310f446010b2400c0b01c00200841c8180c0c0761a0014054a141420a4001d101426028015180955003004000b001ca030103072155020b042070141001c580b05082040040c00c075907000c3c0d50140c0000d00140000e036203a58100c12a030703108902d0202c100300f02c0c112200940d504c1c060b41c2d10850003007050204000401101360300a02092a058842e082070701d41c0010481c2e0007469840c0e1800741d21204100800151911407071200d4800c3d014035046019035222100030702c080d00001900000d2a5031080c0c00000c1900a01030f60303001a80850440c1000e02049404280804111040020071030f941d4408801c042c0c0700d00704071040b858200e021817100355599007440c80250f000298070030016030a01c00f25150306110340146011a081c000003010740 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 325560818 1250 325559568 325559587
    0x91b0318070e07020d0801090c051206060903070303050d0e010203131506050a090f0b09060d030c03020c060a05220b0f0a0c0c1214010212070e01020a0b0405010615030908 75
    0xc0c44040403040c24903100e8403900040344241c00d80e203144154600c2d809410b102c5003001018001680680064a030142800718000c20140d1000580c0c42c50100381c0c00c0d030602519504007050701c41c400c000c400c1c0d415020740e02e00841419003001c0140b0f242c0c3c0a203c020001003c10072500742c201c0c041907810952400c40c0d40f9881d00840e4000085103c52140c1140015800740d0718000a075071076081c0d610080d2810386583c2c070030f0b14040d010701c565010703c1030031fa541034071318504800080c04180c81c01e01c004080c040e1108000c4207142c42089543c9120202038030440c0e0f40e5650403c05003e9400c45c00c000010780603407132103003547c4000a100030b01c1100c00c004641420040909401038098000c61600b0b000c00c0611508a0702140703607041d0300c0d001011f144450440f42c042605015803090894103085e07100b60700410803c00340074050180340340e001600b072034101150310040d00101d0070406107550290070700301c078003042c401031000641c08a403c80d0000b0150f00240080c40d40d080d000d540c002c1d00090540303102409880203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 325562068 1250 325560818 325560841
    0xd020c03060c0a1106011517010b09010503091207030c021c0210030e150c040306060531020903061f0f030f0b0a021b06160801080d030c120f0902091b03 67
    0x100f51400c115a8a00d1030403c00e07440e03d24264081c81d00d031041d10f00c0064910350041004410315903502c043e0003056061101440d0a44249100a0b042040000c001400d440c01849408840c5080c0c100041d41d40040d4100240380084283d41684900e00c0600c4e89641c5840c8070314203040c060741c0603200d11054400c00d04c040d070052040c9082d1041a005250040c1020054014403501c202d81c54400681c80b1410740c1070910841c2c5041c1c1203103029400000207031010303050040000d03031540b41c24200c4550705100c410101c4060b0084006858142c8200f90074400440c55035107031056071801003200281c0140d86d4403481050500d8910020341408014885c44003c101640f83c959803103074903000007528000200046140d5917603036201d00c40890300700c0010321004d44403805003041041080e10700500194100348100f92500700409541051603035840310003017024020035440b8071411070307550308124410746909400003905034460102d04c82c0310b81c080064648000502c803c0e1904070540041411030340d80109018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 325563318 1250 325562068 325562077
    0x90103151a0d030206090114010501090308090f06030117010b04021c05100806090601061209080d0f110d0b0f0d030c030c3f0903171312080c0d020c03060c 68
    0x141022150030400792262158031104241c244031354014991440c003002c0302400c54414100c00e10310282104010072a903a48041e6483c141c1e03410003400c0c0e55645100c0b00046c0c84e51b00d15081560440d0011000027080c01c0842032481100601500a1015140c0b48003008128400c0009138030b25107248103908400e5040950007290b10810f0b8004290901d0b8650008610348081100d402e0480d41c4603400500032581d200e0b0313000103c0c564445090180c11136a80d81c100c0240101c800412889680e00c0c941c1003012200e4102440f240703ea40b0802e503940010000003405400752603046070082181044100c01410110350010050707030599110406a41140d404a8101704103940c15600b0341d0280c1071408641041210040300b2410810301d48011000c8100703e60b842c032495076a004103110096200b000444c80719421501c11400d444561580d403076140404075050182a0000f241501950000c0000c024001c3c000702100e104210440f100c480440c0c41c202d944800120060350550003920100e44c04104240180 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 325564568 1250 325563318 325563341
    0x3010f0510180e0a080903160b0a030e1c0207060f140f07050f03030c0d0c051e09030102040b0d090302160f0e04060902120d08061008010b09060f0703020c040b09010315 74
    0x414211070f143d110034907100b2405000d0361110070003d41d000c640d00d020080201c2001c424007540706858601039446a8030b006104603a0145502c50400b10507041052241c541015540e0300030800c148999500259507130000c2c0035030404034282c01000b100141c01644820508952031a140c2c1c40e26601880c154001e801c05042264148250492000d080d84140040d52040311115602c036143c40c0c4c00911601910700c0b0044e250180041003095000440200010802c003120041d280b6030f0b544100d10110303009204070b9101c182e403001c001c01d0790b10080200360440c4045134005d9084030002c0c03213240c02440044941d8803446000c841c10f441c0810154240c2003101d54400c1c064180025045080d4010446108075040d000d00644c0102c1581c0200c10b4105075040e8101c0304c290703000300d905200000060802a41070080b40b1103064082081003041d600c4400f21091084190082a00c400c603914000c1d5542080f003040700d00c030300c1c1801549012400e054110504a0340c101040d064410300b01e007030b10b1000f08500c5e1000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 325565818 1250 325564568 325564571
    0x27060d02010207050d0803060a1a0d0504230f010b01030203010b120403140c03090a091a0103050907050a0803042c060105071403270909060402090a0917030603010f051018 75
    0xf40596820445c04007880c0101002d07030792860480104500d0805c2d5800c108190300d2260010210300e09248152003503030300340c818001002e440b0341c18416800303503001d1200113032040302d1220540e21030008645c5c5034004810308001c0c04034030035400056040c1e000900a0981c2808180040c000c9034400d10314031900107009003080c0c02240e01100340c1c0a941e0b40407001d01003440c0d1000441ca28a030030080b0301c3d00010001c0340410080440d040e044040402d075451400303410903880c1c5000c41c100c0c0602b880f440d402006e00030200c0119543d1140071940300c0e001889441d109a81c51300f1019900380d91040c10172288682c603d42554642c1d43c0d4070047d5007640140c05c00780c540600024100360801c10401c001d10150800ea0010038030f09101001500c02d0aa4010f002c2e030058003180103000300701000050480e04194100c0ba2002e20f95603051011004142e001d501501000c40e5400100303610803600001c0d030240c1004c1d0002e101042c41c1e09440b80580700c05840c80300d024955402d08008a20640442119000d100d580 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 325567068 1250 325565818 325565833
    0x60f16080406021303030e1206040b0c07080909070917060c0a121b120b06070203060705031306020703080601090e07091403010902030f010203010f120305031306090506041127060d020102 82
    0x24136083c1021680003240801c124405214081c40d00d0f2a8010710340030100014515442d050340d03074000251001e800003090702c00c00301c3c2c410200542c0e40107035002c006001d06441214501404018118856032180e0410020108030f1400243d0001c246c1e13510501003014000e240c01c8140c2000c079850340700d500080301160f6039090104220742030320782e0b404400700c03081e510b00800a405101e22030849040f021321b203201e01d40c100901401614080790070791b8000c00d5814646d403039a59003251038011400400c030081c911880040c0150030560400f000e40d0060301c080c0c0e500c8003515102c0c0408080810281d40c00f8020078240032013003000e0000c0840003003040308040c0010520310a0369010030300d445a032099080380303a5004401801803250301e5000360000c19031071040c015081160b0300c02030316900c0050070007004080f0313001c48841404144e800034446c0551120031074599203000d00b0300c0e11103800038400d1a07210340071070004038070081100e0740e0f0007040840e16881c8103402e84500c0200304581c000040201c0c1540030700c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 325568318 1250 325567068 325567087
    0x2001090803070f0b071121090a080d02010c0e01080a0b030f030a1d03010b09130f080d020309060c0306100503091005011707060504030c1211150c060f1608040602 71
    0x40a01100c07440340b545403c0308103c61802900b210340c010400400c0000d030100342c0c0c0d440c81e4001000f05280d050001050108052501c0f40300039031180360301c85034020300b1800c0e0009281e80c00080706484054075a00801c80d9956101c8121104600440694000b0300028041103910780f490b4070500030740720020704607501003205058003030964106400e01c0380130444075440a070fa203036101c20300c9640800c0110004c1200c0c02f0724100044c40e000028040441c0c01c003c100a40b020800306003505e15499030406462501c801182c2c0a11020703500c00c8540c0c0c03600e03015600c040380c0c0142c120b4094901503000200b100003203001c4444100c50725040103282c0314103032282070302040c140f0325503200c0c09018200384490310940d040000074192030015241d0142e41044400c11041020840d1520b0b0032050b650140038902c1081444e00300410070803450b60415034000002446580368200c1803000b40a00000c40040d107a0680c3c0d445d070308200c1c520045a501e8211010036000340c40c000e21074400241d101c0d20980c0014100140740 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 325569568 1250 325568318 325568323
    0x4080c070503010c0f1e020a0b150414061c0206040510200604030212030103151806050c0901030b040605030a030302030601090f15090b1801110a1a15030a20010908 72
    0xa010070300104071245d000c000b52990140c0c0d94655046c0103804c0c0e018403001640000e41e220301860020f484500c905020441c2e40450001c110040c00b00108140700c04d1401c1034103c5c1e40882c00381c40b5203105090380801c0012040300c406000f0355442d0028040e9051519150500c414a01020990402c0080000c84c0310640242000da42041291410080070b46192510b4040c2c0360480c4581c900400c15401c0c0010000a44000c0c0ba01d04030030403075980030910820540780b041c040b010740c0328010899030a2070100b0407400c0070031000e030102d10000d90b0148100000c6005000444407540196030f05030300103455000c0400d000741c006680040061500e00103603640c8002405d041291504a0740403183c150400e8003000303522025060281082000f541d2404140320702941201000700400c1d41400030703c490ba2807501d08140054013400350407540c03401925820401d082c02c4140102e503594941c1144154100b5a404c0c006001080b15501101103401c50303010342210102100d101c0600da040200d803a40c04038101d10706 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 325570818 1250 325569568 325569581
    0x70b01030506040203120f09040b061c0506090601030c050f160507030f03081501020a0b1b0408030306040c05070302030409020f0d1803020601240c0c0812120a0b060304080c07050301 80
    0x503074007034150341c1810b104060800c003605101170040a8240072034034415080904540340b80300100c0380082c520701c1d05408661756003c1c003038481c2040712040c0195031002c80142c1040303228003002c840d161425500d00c2c0c0150201e0b02e011040c1ca001a2081c03103540210500340c401000104518010340d001c00320075556442c41c01d12150000c503a9620282d0b00c0c141019048100380350400c00741e00c0c440001404c101c0000359101c0b4842c402400c03220040c1c0c040340004000b1080c0c80444450302c2d42843d9215141c0543d203590354001e0301d00da070065203041c01c00b01d407451081c2c0950303002c0341e456400745242c64542400100603401c00c000200721202d0400103951011550301c11200900050f40f0300710865a00e6080c007908160059000200700c1d040450b62690b100d040e0460560241001c0c10420044107450408a07090110ba4000e55070a01c00c42c440e02000c0ca4442c000350901c2da040b00b05503485683c0d41d1038248140c0e40c0d000f2105e600542c050020500140c1e02d5000b0f0a501c1e50a4801c1303a03082e5550700f00203400e4660 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 325572068 1250 325570818 325570823
    0x71218060c090306050606030c0a0c0201030f020d0b0102101b08040303060905040303060501120e0d030e01020714062401021b03100603031d03071203033c050114011e05070b0103 78
    0x1d074040c0030404c00446000703c5031b0020003200e41034114a000850039240c0d1042200540800c03900c103400c5000c5a00075840380c0e041c1d10448000715260900194008003c14010005034094802c03492412000d2002d0300540450844003005a110184402425101100050000c406150305d0760300c0400c0454652080ba0300c101e001c0e940102e0700c0c40c275020002d41030560f82c05c20140c0060400b14205100d810000e4000000d120383e01c0c000903021081e005150081c0928100181140c85078070b020710b100b840c000707540d030b01804040c1072008130200d800c1403034042015068901805600000320502000500b1003038016882c80c05030590b4090b2404075010800c031802ca8200710003080c40140a07120720440c11094460170705c0190001c1000300d041031885521802c4248005040540b20995160075a554034100580c000c0d0b8001c1c2c1d004450078000d441d1404003072840260300514644000041d600003880e42b0a4080e0006071121002136a10b0304000110904503c0418240301c03040286000151000001900860 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 325573318 1250 325572068 325572077
    0x11030105090a140609070c0206130536061f0c0507090b06030c161e0615030320010b0d050321062107120f0218071218060c 54
    0x18145801c02078a07020141040c1c0302e4618002d02521102d280c00c403055044142214010000d0b0744019013160000a02140250820710101d0030006041c00c800d445000e549080740c410ba1102c0c00280c2c01187c41401c2041849082034410700403000ea51003c2c5a19005036001d0507801e0203100d040f00300340d184405160301da4002982000300341c4c10710209100c010090402e444c000e104a01d0200d0001340f0070700016169440f101400500540ba040040104805042d80b00b1100c141101403c24010300141d4508004d8517428102005040920040e20000702600d80c16119181c00954a8140e03210403c00100407403015075813810b8807039142d078402140e040480d2246000f55601c050401c1116101200442420f4000041000b80021940e8000f80c50900348000251042c2e0a01480f80780c41c40c0c8140303584025400f1150000090500440c4210181e04600a5030743c0c81c0c50340315203406400c0d114012034026001841130325102c41d954100c1d801c480c044500300c15101c2030a01035130b241d271800ca5150440380d0700400c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 325574568 1250 325573318 325573321
    0xe0613090203102f180402030c070203060c070c0f030305030a0207060e010e030406140c190f060f020304050f1203150307051c0b1302030307020405060d0b0c181507241103 75
    0x700c4e1a64503010081d044200d2603041000c02082d400a1301c101880d07551169030044001000e00410105440005400800304c50756418089030100056015a10076a50001c0154010840c0c101175142907003241e9040d03803400c0c0b030741d55a074450b0340094201480448146890348054a410602400b42e07042c1c140492002d940d5651400c070016000241245940c0d030046000d05c17202c80394007000316020060044800c50011145c01524040040394000480148494a081c141402103443c61380a9403040d4803c00c129144504c51090290b940e01a4100810981c0c0301000024550000140044030844000d03040b11842916000010b08603c0c0c0b0040006102c0e90600e5104144940c0b80b00d4503410001d50040000a40080d8001c030303031a4410008060700840d1070310041480740e103401643c412115003005030a0010b050030b40d29203c0507880144074032420518802d000510b450400311005c1000b65204e41d644c80c0c441c0c2c650300c1422882c01c803c022000b22840d41e105a80041c800c0c0110051507a2005c1941d55a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 325575818 1250 325574568 325574621
    0x50103060b0f0f0a051011030c0604120507110f030a050109050d0906170c07210201060e1f140301021213030f0809030a0e0621040203070e061309020310 67
    0x10240034a0055201c0d143c0554404110740b01d0b248801c1c2a50000d580c840b0120080f50410303207221114110a02c1d2a04c00080c003a03201402c0802c480f0b0003548621240d00b0039650350b81c01211503014850002c3d14050100000c0522807401170030300781c0200700141c2510381d40c180503110030742101c0c1c841e501a13400f0b80150440702c0559078000b0080025001504002d54201ba00400c40e050801d0001c0060300050f80009285043c4058100381d490001c0801c210b6a407d015640300c024043d00e00b41c410a03900540d540081107100c04007003181030b0800e155454520b0918034001d0551791a0100410b0950155030070480d001618002d0800c46210700c0403940c070480e004101d450014401181c0da28242c040008500900402d160040215a6002520321f444103c0c411444001000e512804840c0c41e0210b03240803441c140315a000024030701c254000c07000d694045a9944140941140c03c4030710707950040034184400c40d4550300c1d40c404007465001500b1201811032294594044881c01c1850340390104030312036400803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 325577068 1250 325575818 325575829
    0x200f0405270a050702100c02030c1606051606060302101e02030313030c050c030d020f010f061202190315050a0c11060105012d080f07051206090403050d050103060b 72
    0x540c8000e1100714441c1c070501c000c003958000c0e0040c04002d10315880f6000b03d0b540394800c00038044403480c00031080180004480c806541d030b500442e40030340c141c025401000c1c00801801c03c020111011501c0b1649040341c0e844081d4901c0409000480340140d850f0408800f6866485818061540035200c0c00710201e4035031245d42c903400b000c0c14050111740c000c0080240b10300504a02c19200ca034582040c03c60302c10325240203402d01a81003107850701440382c90620f4480b140d0000b1a000c0d540c003100000c00409641070310003801d554443c000d244083d04002c103500c0060904091009506001d0b5401c03988050300c0381d596500c8cc008a00c031110711161901e081c003801c00814810700c1c011403001d040403000d500d0b20460b5103884807030511469043c00312601004140503101c0603075070001442c2d49100e41410091007409003e40006542ea8502c1000100004031030714012011034000058544480c0c0c080d5441c28204481a180107004a08100f000d21101400003641d00a0b107010b14030800000c105d0142c41e60034400d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 325578318 1250 325577068 325577089
    0x607030909020d0c1b05030d09060e060405011d0a0b06010503091018062405060307050714010e070b0403080f03060a031e020f01030b0a0905060d0c12120507050d03200f0405 76
    0x20179140c0b5018030180040c4000044840c540c80c00080441c0c622181c0c20250700400c4904030041c0c03a070040c002004104030040d03100c031402000300002c00003201c051402180d07032107401240007002d12951038086101b1350700890203154000c84d420100c48424080069a60070340d090505c161305d441544941410412202d13006210002d40011102080328000d18440076501105100b041d0050038000040f883e010322132012142510b03084160401030792142e18046008100c00001c0010501400d0700214030640b02e04101c1e011290030114541c01c20880500000103580050003003a48244040000400546030310040c58a803621071080c035940032040d0040c40640e8203440002e904140c60403007160400c1d903030104040c0684152240001c0c1c295a58800f09042e40342c01c06000c2c06074a480000060381402140100304d04900c05c900062194142c4081603546015450000b4016008210a0a83e140c8258094048903825001d12800d280c040c0e0103c00960744102020001c1c500001014800c80c200001d000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 325579568 1250 325578318 325578347
    0xd050106062369220902040e0f09060106080a0c030b21060a0507021b0604034704060b0a1a04050906100f05071109010f180c0801050607030909020d0c 66
    0x101c035140c0086035404444c03107a0800e103811443d40148004034400c03c10324040152040910455885450300003d40b1028802c6804a600c4184440060592000410001e04951240d1a0b40580b5125402c640005d442001c5000040641c0c8000300d80031760341c0752060f060490702480c250000d007244022032281090001400312403014144024003003d07990028103075041614000c0d00c0601c031450034000a0a84c17003580d1000e496581d0401a0440304211104100415000501c410b20291540c0c949550b0059846488107403c0840c00002030103d5541d03001405c161a008180100c079580f00d090f440480e107515080f6424250001c902400340d0b08004104503008001142e1504101040400040214849004060801801003001d130100882d40c5915840c1c080020403004c0d0640e101d6101071880361240c4509109460200a201d5100c0c000d4441d41d00e8481c0c40342e98a1809030708002c1402055480000210704100c150750000039002e410b40b003c0c0441c03055804010440081c0d00360018142092000c00703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 325580818 1250 325579568 325579747
    0x601030f060323011508031b01150b0903030702030a050105061e060a031508030c010c1205040506042a090e0f06010b090409110d0501060623 62
    0xa00110f03540190240e202055a481e070560b001100d0199405003a2a04080103500840200401e00c0b00c00840a4010084148404030905040030411070a8480d13603940c0c030440b02500b110a00c440500381c4005d1401c18006000ca074504505076010038134002d42403405541036592070081c444549095a031400e05482c003603222114079040d450000d0750741c3c410003042406060f9a40804200100c035004110300802005c13040d692140c1d0807038a943e000e000e0030741e403a01c00207110000e01c504220a40c4500b42c0110b0300070009004690b200c0e5101d4024106c4c00350b0b40c0c186848415252a02d9100c66005040030b40b218081c0442e440529084c5c49180506042c0c0c0701da02e9030005001030040c1500034055030050002182c011801095a052a8001c041142000b0f60031035010341d40f8800b404015003207a0b044519694403c515000520002801094034100c1100c001c4020443c1d40410140f03140303454044040100741c04000848000e2050fa07032110400c46084000c0500388403031064014020b00070781848603800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 325582068 1250 325580818 325580831
    0x301020a08060609030a02090103030309031b110d020f0a090212010605070209070c08070803090318060405060702010c06180c09050606070309060503131203020d110c190512040e0601030f 82
    0x4040c1803490700500041c010500414113503002c0e40c04008440c0c004c0d4000d8104001ca503100e04008001d00714410096011529098130b451900448414000f0300f07980110f8100740303d011030020048082d400b01c1c82030364015050601f8403403035601d9080366801014180b43c01a03443c50020458030b02c14605038400300c01e101c000e000c0d41c0c0268803103c00c401d502c802c142c47d000301408814901040300380a50728014112000c084200308406600200a003004070000e40d5101c54907510300704200303103807295000c2c0503003100341071200c4001940940d40d010041407161002064941b001c0f540c2c4000d80c5217094041d62000280541006030440c01d01c24107070005002e4400ca40f40c060701ea10060b1070900c4510030001044400030024608140c1c01c241d80380724541c00501041a0381c58004014007075003154108203411864034801140503030418044030005600030010341144101c401503800300c5110440d09a400b4060b9440410715882010000c0000d40740e01c00c00540e40d810868001411036000c038404490a514140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 325583318 1250 325582068 325582087
    0xb0304080f0309030705030f040e10032406081009150b0307060c21030c0e03031315140f0310080609060a020d021b15070203120103150e06100311030102 67
    0x40465846140322140e00750b407900e83c0350302c4034654440c20002600314000804e5110450700e071400207108a4800303403c4915070ba107078560b883c0f140c1c055600c001000004070071010301d44d90340c903042e0548911204040001d01c080ea9500d0741030810828003564203010365207503068030070028840c2c46001b807040c4c0782034104448003000c80481d55826503801950184152891540d040120425038402c1c0414500d61030b1081c0340c5800300c05405400960071500200760f004100076090b09000080e21809039050b411800e406103032020052240003001c21040030002c0b9240c00f640700f00c084d0001405208205602d0707690303914045241000b40401c5400a8045800c0b140500545000004140e9005001c0100043c3d481d081410b44030001d01c0b0740540341c00480c1d20054128625034003c248030a4614512588102d0356984240c101c0c1c407071041503403100868810600600c08500741861000c3c16040302c0e032000481c000000034a51505034212191368020010303180a000300b00d0000301544540406500130f40c101203c10f0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 325584568 1250 325583318 325583333
    0x304030203040308071104140a0b06070201021b01020a0b070206060306070c020108070e042301080c09010302091801061703090a0f05060418090b1608070f080f0a06080111070203070b0304 82
    0x503c400351100101150800c2802002d02c07121444001c01001007201292a1411101c1e013001219401d500c00c0c60b000b0116001e0400100f00d43c04968141e0260240181c92802400c008110b68840307411071184182410000f00c1007140d15000e085650000d003041e1811104042c50a00d000300304008100440c0d014200507600300300c4450b00120381d814007190b1042c2c01408074006180c5e003003031024042108600d04404003900302c002d5042e6020141a00c070182d4a00d0123002c4184007e210080d004914a400540000c0b90021440300c1940c41c00c00100c0e0b07140c0d0f208989681c0b0034400c01d080001c0c0e0000182801c2a180041e00e020080c20308490151045c1d00d000300041c03541c0100d00c5114680054003104049814080e400044081d6200302c03089100e003031140c039071584189401d40c05000300d40d0050110303840500841811440100740e9503080e03100e5507030000e0464002000303031080c001a40c80c1d440c0454068001c1c000c010700495040c401b66113031081030040500d009619071101081410420920002c100034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 325585818 1250 325584568 325584577
    0x1c06031415012c07111905070918080708070b071713151e060305010207020108010e090a081b0601060807030f060506160c0312121407080a0b0d02150d0c050304030203 73
    0x541008401c4d9607100050382c4d5041c1c1965500998003401142c0031640398401080b400c040c3c0034004a55900b9140ca40403411200c140c0d1402c000d88400c4c6949400048912000704030003441601c540e81820310f1580c41402810042d10004041100c1d80e0020070b695030103115140c0d220101c00c1741d81191f5081e079262840a00118030708038241c0340e244d41b43e483780c02c1c20380300104901e685080e100b0000b003562420118000e4114a0b4200d0006004d8800000d00c0c22680020303d0080d04894007030500c5041d16590500d0701da2010044030b6211005810001803100180110b038002c1c692500d4000051902c0700d4020211101c4080746801c0324500f1030180034a40320641902c20711801e049101e814043d66081501c0d529191390300080600800c048800d85695101d40d00407181d810540050050740b0002c94039400d103480440d42200015503200004808040b0742c1c00038604880702921407031044001d60041450f03105400c602e4003c195000898622041051103002c80452442c42c105045040907035009440380308 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 325587068 1250 325585818 325585889
    0x9062223030114040b0705070218090f0313060c14030a0c0201020f0d0806060702010201110c0a3c020f03030a111005010602060a0e01020405061c05010801060b1c0603141501 76
    0x800e800206110f02070340441d01207a80003810301861090294a80540d41801c40e40c007205802405001433148400005a0700050141c1c0480c0342c0c3d003814400101c841c00300d645026107816481401d0002022004e0005060001143c7d40c5e904580d00503000291514189403e1702040da845940303844204ec1d4003c40310703508084211039040e510952400101d003d42190042c20886640000e8800400c840008200040510941b814412002c22410440c2c5e03880052100111040e900c1c000001028150340440c48a140b00409401c1c4000f21080072a255070003070202603000c1491500c023440b411404000c4000e01c101101ca040c0101d605220000f0344032500a0303d404000c9403520920022001c081d0140ca01909000e44400e0310b844080c910383c142011000402c03510145000004100305006020f110141e0704409a440d182c13100503111030030300076030750b4102102e0f0707aa5401d800300000705604040030031040c0f2100202020340345181004603002042e03103c80141e109004d002113079150241015840002c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 325588318 1250 325587068 325587083
    0x20315011e03110c06240102030a050a03051b030a14090a080712020a170405120f1e0a02030118020a150210090311060403020319020105010b0906222303011404 70
    0x30403450f4800c110700030100068200c0c001e4800b0080c00489254188100f00709110502c0c5074000304000680c0c13244241d0780c07120005001003012004580c00ba0b0000c90300540380901c1d00c03880380d0128081515640040d24540b003065155a500d003002d00e800140590442d808002030700e9014002e613902d0702d0030711030b000b802403409540e03c41c01c1030740d54000d000b15001103410030300034a0600c510380f030001c1095201d405110311503503034441c242a500d0800610056852000801080e280c5100807014560442c2c40e020003901d8401c40b940c2c0001600c3c2801843c00500004281c60200b542d43c6c070421807442e8690304000d540403039008480c1042a070010300301c010040521030015500e0f00c2420110b440106c42d2030480828805c84d014041016400002488494500410240d113044074030812070a807942803048031042d0b4400d014400080c54008000c0959503c0070381c074040c04050452402c40103030a079900000852403070b19045106401070151140e42d0090840c02040a0040341e0501400c0d00400f520191101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 325589568 1250 325588318 325588331
    0x306100e060301061407060e0c120f07032a0e160503090a08030c280206010602010608030702090c12090a1208130b06061e07050106080712110105091201020315011e03 73
    0x184210811106c066070014428000182d8404040b5a103103101400704d405000480c0044400602c0428040d44010740000507140351803854481f07801500c001c1d4000e0380c42400200a8051140c84c4c800c000d80144054041c0d41c189142400301e0b010b8004e1441c0c0280140300040041141601001c10044046036019100c65165215a03c0e415414091380e010300704402d0300f0103140442c1440c000b1024840d030702d241c2c0c220303072650380c90760003c80c242c1f0168415840350303a1041c0702c0c410041c030f4502d0820b0380c090416130a4900b848181c00160882000644000d0050b070400c0c01c0c500c09000c2500080100c411490800d40d0141c102618000880c500c0b000c2c014251010900200b02c541e42d41008035603121041d03204000402440000e00700690344050803c40f015881d100703001491344030100345c00c0e045840032800303107506654985800903e00380445c240ca0403c20200400c59180d9901d031140c01d6182c0702580010384074a0586d001c100f415138001c542c2418000000d090781c40c1a408500114071441d45072a002c03c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 325590818 1250 325589568 325589597
    0x40608011e03060606020318040606020a0602090f0d0803040512090a06120e0d090e0f090307021c0206040f03060b030109020a050103020a0215182503020f22020306100e06030106 78
    0x320070980c0005081d5801d009000902c2c40d400405410021070701c68009606540d01001c10084071b08038440c002c0035800051130365001c511b03941c1c0035140c40d1101920481c00000100c000030b0304051f02250446105038044240414448108070980340c05070480350380751404040b5000900d40425500c54501000a80e410703205200015801401600359440d04540f0070342c26031080600104128040c450506144d0400070302151403266190b030003444400051464031100790280140c03c5030380801c101c20010344c8408400140c5682004000408220072200d040b20705502e0808255002d15903041c0c443d81c1880d08a2015030749200c1c0c0c00045480034200140e40b10072140301a4182960308008480e40d24680c070802011142801441d4100c0e2100c00640b0208a04690740d2940c07102860011003410312920018001400e1490f90b07030400307030401403141e0300705805000c0003959a65806544122660080144515402d20041c00c140d180545c2c01c0a8507559884000304169010521a03a0108048030115095 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 325592068 1250 325590818 325590869
    0xc021c0c1e050f030406030e03040e0105010c0804180b180f07050c07050405090d23040312030207062309191e171c020315010f050f070605090f0304060801 68
    0x20a030380e208080e03c901d60203014129850b0b411a115443c0400d0070580076840284005c42150705907403d0801001003a4208001196010840c8100b160798460402000c20a0340c03d11071380d103440d15902400440d0380c00c00384082c424881960000e601d450f00c000703800e1250b042040e01c0c03003e902c440145801d1362201c0f48081c4e0030341350403034560216811038074000a008a207840403890f00032011030760301c8900d104102050850a584205134502040110070f0105100044c08400d24501e540c496140250074900c0a13210070003207402815094506510b4400c4035071b03d000000f003509a100507442c0141c0000400004641c0c5c8041c65000020305810003107012180d040030307170000c8040450b00000d54080c55407103103220a2480c1e12140384031500320f4981080c8950b1588034004c130f1b40710380d039170341c48200e003521101c801134515500b0381085d40709000c400d0103400c17100070a100180c0f00140c060200407440382005201c07541003a40e50a200f54060300100401c0c0100740c1c01810003030445005240000c14040302e10740245 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 325593318 1250 325592068 325592123
    0x30f02040b03030d0c0507060c090806070c060b060a12061a0a030510031a0403110c0112150e0c040f08010908041505090603012607030507090b0d05010207060c021c0c 73
    0xd44103117400e54401d0400e170f021000d48030302d074030a440402c42540416030035a6825030724401c01d80c03581e02820000708514071a10400354058807803440410725185620004400b90050600b51001407030300441017170307101158044c200090800d0011941d0300c4a80510380d000c3c43c070603a4150740c14980c5540100361244c0322040e400004541055400f65406442d164555000106170380c01d0300081c0e214100420312141c0441d0040d40d020ac140c4445041050a00810000d4014401c86481a111882c00014500f01e4045010b220701c540b940c50b50707511400e1640d03a10f10103410760004070550f850024008001034030f00e01287d0580b6038902c0c4540d071240030071008554600c80c00b8135480d00b0440110000800d1500304019904480311503050b400c0f04000c2803145a5248850701c0040d055900c000b204001481060380b020004803400b404c058888641c0b510346609991003488108d440940d9a020710b002030342e061080c044507a81444070000326a0341c1020003407400804c854007500c0c441d8202844041c2d01c49802d10034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 325594568 1250 325593318 325593337
    0x911040b07050105180c0906090415050a020c010c0e1e0a03050f010501051e031f0b0a03120206010b183006062715060f030a090c090501030f02040b0303 67
    0x381d076601461910b0303030180100740e602039012480000350b480360b000040340300c2070740703c40290400f43c0b2599490300708a00c004000e04103446000c0900d000e100b044042d40038440c800e0f00007030070150b07540b02c2a40070182100e0030513029108000307803d200c01400341d80f080f91603140d06a050010414201840c0005031a00c800d62f0320040092040030015000c1e4903041d007100f4121401180d5006135090003510000c0003401040d1456859007100c00c0701d164542500c00407580e0f0a5050340c00082d240c2803800405c602030070315081030350900181c0441458966040005501400700c0010850409100d00300d5002079150014003e48141b213003400c5521207181500000a41c2407001140d03854000c1d18090741a15014161400c1d40100301d40054803204140e5008103101c454501001781c003081e13660543d0568005c4c820040e213030744080704212140342812008045d600400e1941c4c80010900c02c02d2400c040075800543c0030383d6501e8140710040001c24403948a80c0407a90b0181c401140b00c0d1941400241903101e1085c00c1c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 325595818 1250 325594568 325594589
    0x111b0d020d11180405010b061204030c0c0506070803150103060305030a050f070f0f0203010c02010e1506030a0c0e0a0b0f01090b0306040e030a030c110a05071e03150b0414060604091104 81
    0x10320603c0c3c000c2842e4015030080d0000c01030004124180201ba20604405034124a000310200780080c0c802c071100441a400b541c20b50b0071160b2128006480c607400b400701554201008403d20000e00216000d1108260007402d042140a00e0740c2da0781c07601c0303024214404052060214850940390800c108550b80c00f035101501c180c04000c1480d24100d04540440c00b640070750718140f515426240144140016200000e008080e003452aa600341e02c612001094590180210103000700000c910580c3c401c0600740d8405884400d2500016a00444e010142c0080c03064a003008c1c2450a030740c020584909450300300740980e41c4c1c0d41d200c101044c0a85000d0b00d0103490703484005041c080c3e696040d4030058000065950b80700c1d109520031407140d91032400c002c018156401003002003000c005959082c0b440b0862201d0f003150308507541d844003021141141c03245001c01c0d44070041c00c0494078140c0f1403001e8114070210010b180d410101c002c24420700460003401d00043e03851941e410025401401d03100103140b0602c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 325597068 1250 325595818 325595839
    0x706020c0d0f17060a090b010e040f02040e100b18061e130f1a030618010801090c080a030e1504050409111804110925111b0d020d11 58
    0x1d000380341407004044400040e0300c548100c03000d02460b16089014980080c00403040504240c246402048460085418040107621451594440b80101c0240001510005071130350b1805039040e00980009060190901d4125418401c1c1c41c806401d95914011170500401c1c034020b01800700d0241e11503ca0300600c207501ca0340101480e203455900400d012000200540c040ca59204201000c4001c0c5000c0c2c000010080381c060940101c400002d1944806c0081044c0d02a603a600c50000b4604d034203801c01300c1c0594680d205c400500c0b9544200500800c035520081c650f05103035450040130050f4211505204010114022071030a0901c0181c50281400520400042c1003a02e040b07440000d40c00c400368003800348007281c08610200c84658a1044c2e810106070340c002304038401007200d0100000c1c404122200c03202e443e81e4440c0300c101c00e103003005c40641e1600c031000410b80c40c4c083c0c81c0c100d08072407a080352810b110404900b0b4982c0900981c9481d815079600594a1036403900c0000100c903041801d400c01c55445 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 325598318 1250 325597068 325597093
    0xa0c02041e0f1107030905040203100308180306010b07050d0e0a051012060f0e010306050a09120309140309010905060309010e06090319020303062b050f01090212160b0706020c 77
    0xc1c808501000b40e003108101d10038030b200c07440001d40a0403101a003c110111002c0003141002e400942e8805203000380c0c90000c40c3c49a413101120b8200c01c480b2040740706008180d00441c1030400050780074140200b140744c200700707140d80c9155940c1402d10b060390401c1030540d240c00003602c2d0b0220500c0a004000c242404070071007000028040d01202805141050900f04001804002c04c40c000703080c0c0e0035031200c00c6503a82c2140c448002406001d000001d0403661481441c0200302d598a41c3c05005069035030201e081183e9080c800c80e1405c10000a0300c007a002040b0640d00b076a0003407100000c81d0000d0310615220744d04d03400024010b00c5a102c42d4a01402824100041004084001c04a840e54440c00c0604070307184181c2207a07280401c86100e42c00203405120202c40d242c440c05002d04003111081c4100c10100181d1301c0170f09019030509079100a0791904580e204515010a42c0401260b40324010f05545a207220708101415071441420711303060000443c0c40600016404480e4031955007011119100c5052 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 325599568 1250 325598318 325598321
    0xe0709050a0c0224070822080306040b152506020406030c02161503111c1a041e02090a03061506030e030903100c0201270c06020609030a0c02041e 64
    0x42c18032000600030036000a801e445071032181c4503c551a40100107855603858816902c20402a01910900343d806c040c0c802d8841b0a0702040c20068401c2052039140c0c14840180015034a0880a0314810341801d40d03e40045d200c01c1081d036000e40f1a01c0224015210140c2c2c0b5501c1150260601411842c000a008186241c0540003044000381a40c01c8608100c52043c50b003100d08028011018501c00039055029054402d0300b02608409026103032078a8020f80c0d040454104103031058189085c0d486240001c800c680803011510411020f032024455281100e175a42d032102e80480f0b0030b180840c0d0100756218603440d0783c00008007441e0302810403c800c10901d860003240246511a1000103820039803c500c0c00c1c40040b0a0780c61510000d4010948900441d032444060000034a491007150f507180000c0c550866580c903503d0b400c3c0d000807028142c0d45424181300544614541084042d03501040611010300800422100c10b0490f0f85803030f0070342201910006010f00603680f22552030204040201c090500709 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 325600818 1250 325599568 325599581
    0x702130218010f0f3c091706010e1005120109151b12110d0902120f03070314210a0e060613090c0905011203020c090c07060e0709050a 59
    0x26a08001d080007003200c01100d086064038080e0000441004c00910b03c0da00445500d800c000320740c07030b640041410a0a504403a41e2000e0468000500c0c02c1c07085d01c8826401540f020041d18030310280e2841c110b4449001c554400061096010350345071440000ca085110f05485000342c40010004800e0304003108029020f001d0010f8262551012011041c031110300030f02c20600029548009820b5007941c499003521041d4485c0c0c0c51000807a151220150145c000c24010311031440d0580c07002440c040203005124190b00c0000c6462029440f84902d024481000001d80f082550b02d4a07110208080101070b00c800760160301c0080426012440da02000070003c80341d00381c41660314441c104080018180d4190b0f030f510058540e59002036005550703001288a07034200d090300c2802403281c080480c1d40c1d081c03c103040315802d0f8000300c82011070a29217420585e06200e8151075003400c42d801c42301e074100714550000b40c2c420300307200814183e42c6401c81c034418002405200020400e0343c004010b9890f112810b080500390 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 325602068 1250 325600818 325600837
    0xf0b030919140c0a030c0918230c040c09150306030c140913020a050d02030a050601030f02090108070608060d0f0c092f16050703080a05070b070509030a080307030207021302 76
    0x24400314804242040307441142141c6d001031212070082d00c0d00c104c01e001000c114a82a04030741d10103883c003011500900c144207040b030381d228100840020b40ca45690030400380700d01d150b01c55800d00041c2d0005991060301c50301642c1006002d04460500c01c82c00303400904e51544001c0c11a000c0c030300001600d000c1009607100c44802617401c0c5040c1d5aa8030280003400e04178010080d1701c006021000d02c41803c101030920f03030040c0b010b01110302c070550301c2d1111071a20400b68030440303a0012001e88034003103042a104407030040c03c0d908005d000f06414224081d009041c020601401191400d1520041c00075001c603d4003403d0f000b201c1010000e032548512400741c01c50b40e090104181c101e115064651140c002180c0c1c91072041102c04d0b00304002980840c0b0f001c000c00d1002d5134144240040071000ca449040202040d04054607569601e419500c0e0080310550014200c1003407003000c0c007072070595403004542414007540c0400c60b05e40e84d598102c403d4009004194007c0e410072000119000d03501c81c950f004100002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 325603318 1250 325602068 325602073
    0x5150105040b0316180b120309041416050a1214012c13080f1206011b050303070c0c0f1206050609060d081309020c0303060405100f0b03091914 63
    0x35082d05059580542c3c04a000320041040c1d000c00000005569102c50000828004601360040c50000b41034031521a203440703141d4100043c184503501d401d1040800e40310340901d10f11302510340b21106154001243c0c0f501c0082c0301000031045003c40c4181035007581440610010000c030100c0d1400281150003d00a10a010f82d00c9080c0240080c098111070030350329030004400c0500c2d540c5a03c2019405e5102c0d900b10340048051020b40744405000001e0116941031243d04030f100c1c81c1840005101705e64100007200001c079414109004188048120380c0d020709203080c6050300810a1070400742d0314945520000d0303440e5240c07201168a13004d44050210090080c0301c14089525007804212456005554240c2c0c06507410349079200154800c0080e14124007641d00785800b1590300c071820400da9029034440009608000308010407451700d807003095001110941030420983c02e1400390040300c04280682d640d4400c010001a03841002040600c0c82020041e081000310a0980303061624500c4100c50303000b050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 325604568 1250 325603318 325603331
    0x7080f0406020609162108090402070503071e2d020919110901080103020d030201060504140a0e0f03180a1802070c090203100e07031d0705010f050c06041106070515010504 75
    0x8105c6000da00c0951b00ca044903103003510203034058a0070034040d15504a60b031144c14000d00180e0fa8880c0f000d401414040c0f0051b607541c08051410052449a50b00c401c0340550f460050318010504d40c18990310078011120a000102c107000c04034480580e03821800a50000303d00f410001d0305080f070344030302807811003048040c4201202691078000c18011400908c4c0020f00d0703c00104090702c1d0070070703031061818028000003c2c0c0c1e5403030314045010384044030a1020005103070700074400ca40c56988200b43c0c0c200b4001000e44401240032403040d44038814004102c45062440ea040b00c0c1e642d40700100b040c02020a444880345a009511b124006074116001c1510b010b00c2000340040d00b04010b0003101d125517101070301003424901b4030f45210202c03040508060708160f40c600c064000d00ca154400c030300e0030b0b07100900203102c0c0300c1c40d100c00181b540c44000f0422041003418005c00074500400215190003a901000090b40f0000e40008190a0700600b08045c00e944200318003250b500008000542c1a580e09a8050080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 325605818 1250 325604568 325604593
    0x604151401020c010e15031b03090102070312091a060a0906080f0c09010321030b1012050a02040501051c14070f080105090408190302090a0801060f240507080f0406020609 75
    0x42d4403e052280d810960606c02c00d6442c0796050010350740030180c04c642d04400024201101d28030381003103d040e500c6171350000300300042c1a0030240c0401c0d1030480c00c01c04e100708182580c2d1701e40b240881080e810280099403010a2035659064158400341105405c104043c580d10061107544e60001100209a0300900042c100c003414402d1071541620b81007421044040b614400095801c00c802c240c00040655400d000701155844a0000e00300e04070640d03801100b603003906030b0803080b2040078005038a1207204000030006c598020302681c914503c4a40e4142c4514994108540030304040141c03685c0c49034809080140007504660b5125500610f03943e00d4010342e0701c1d01e0070b2205c51902a03401900c03601c401e02c40d9040c0000700505036010a00c3d0740c80d000d41010f10505c08600304644d0360704211000c0c0d4460034103104440c0c2440305e000007000103800d031601181e04c02014511001c004040d5004114000403c2c03418400c281089030001d29140d421640d80d07036903404000b912103800761181e200c1c0340501001c6405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 325607068 1250 325605818 325605827
    0xb270c03040302070e04030905090c070209010e130303020f041a0409061215090515090a060f0b060a0c0f020a030b011d330d050309010f020a03020c06030604151401020c01 75
    0x4200c2c0c1c9074005203d860305014070051060402031080b01044407405c8007141503215030940c1070254811001960b103480761071040040704241604140300c00c0c00c0440030450040046443d41c1d0b0401c0e01802d00681d01e10120b280d151a070310450b0003034100089403461010300201360740001c0040300d58400f803c00013981c48001070103051b061f00c0ca02030000454031801d00350b03480b6141d22890b11188504100d5010420b11001c4008c0030000311101d00140d08809144410b110050061540107011441c1c10054085450001907442c095440360508100394107444104105000c0ca000d4031140d002407880c030102d542d13450720142c0342d81c09025003110089001400201f44845403080d40c0110720300d4401d4110303818a0041c070050380d2840d03440c081140e55444000030f02500c410b001410442c1c06540510780d00c501c841c2c0090442c00d030389000041150702501510000c298080340115648008030f404079504e8892400040c003501d4403c03d01c2c2d042e20f8410a001400010002101c15403280a030241c480c031424002c019a17 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 325608318 1250 325607068 325607071
    0x605090f1204050a050105030c070506010e0702010b090415020a02100624020a020a09020d06240905010807080a0c0e03010f0e0106051903021005194802040b270c03 72
    0xb13400100004040c0034544c011006180e11100040525003000d1590301c0300313813401400380d0048001d51489001d11144640c217004403a4a11800d407510522428956915446c11072440201c0304803541c0403440e207441030301c207000c029012003046000344a031740e032034840c8500300f00285055400700102000c44041c98600216000303074203e40040174480c0d11894000c2410184d0300c81c400d07090b50b0300e40e42c0c04040303240c0b07000d22820f80c040c201001b224848405020009080185170390049410b01c041e80c810412a25030100005034031096010001c1000f080001041c2c840f03600c040030346a815424203a1241e040d150f241d01207581c0b40381c02d50081c040607507074100344554001364000b6013048058000e030500160030300200c81d450000031454200d152140c103040028008100e003005200042c00c0504550005440070380e085807c1040e2030389901d40c8000001c2840001e2900180a8907489100d0500000c0d0350362580104904000030708480d1002c82545900c035541e9550304c9545402410440224503455003050649 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 325609568 1250 325608318 325608329
    0x100501050f01030b030102090a030804050a0602010e0a260a030c090e061302030408160b011406030f04020907022b1d0d031b150b030c03062a070605090f1204 69
    0x8071035214400045003e445080e00d80c9426640800401d01d864a40050312002907000341101501c650a0004000382c0c009180d004600716030402c201c607009110040f0340c000016501040740c019014107103288001c00c0100000403450020041091078640e41c15410106c09402640e80780c101c0547c4421090440380c50940c2c06a4000307242000941007120168000c41c0c101f8001d6041074140344081800c046100c08010085900003490801008150070700b4285028800742102c05c2c6086107807020241500f260001c0001e4400e103415804100f100c0c0c000d000740b0f49016460300e84242d42d100c0c0c2d1445040802802207072140003c80e00c00c0940e1b982201d030b0340c04005210004041500080503520100c1d400044824040340c0f120585100c000010700740d1440104c1c5018a6070040b41500003d0101030410300170b079000358000d0300840100042c0782d03500c0a06003529006082c1090a2008100c0000d019001c0d0780e8004000303e03e08028841038400014000a07181241e0045880d251101c03101c0800d14007070752040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 325610818 1250 325609568 325609579
    0xb0c0607080702031b15010915080a030c02041d0d09060e0105030907060f0912150c0503040b0402010305271b1008010e0402040209040f090606080304062f0a0c060210050105 76
    0x100001c076140c035804950290701c0000700d0304001b1403090305040d029005c3c0e200d410359940e981c110300d15500d1010b154800916a82c80075088500c10390700d0280065040c0c18000380708a540d161075100740e65181c60b00c0c480e500c201d01c0844c0d090000c07410700078040c54054003408000c5801914100c909601c90000c59100f000064007a1406078038281c0166480080354074204180254a00702203403001d2501c210302d00302c5006203040181c01541c8c044e10300c11600403461b12810004e08008000c08901c4015000f03801650a1800003680c0d9542301c429a85070b030068201d2051903040c01d524040b5207000150850500f414200c402c2400c01d118410013400c2000000d80c04042030b8000010851900131081c500e40c06400038002614103018040014102e4600000c0d5552a0396507080c00800d0010f54484d001c0684502002940380604040c40900007008000000c80100e5440d040305545108440248107407182020072625030300c5a92422103900d41440c040c420061140d00309500e80036610780141070482c0c030041c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 325612068 1250 325610818 325610827
    0x40204060c021c0803072304081c02120c0a050d020606131a120d030507050f0906070204020f120103050c090112260c01020c0c0a0e1305010e070b0c060708070203 71
    0x248403030950101c00d404100411034441c0c802013181100114420892961401d86030300c0c000b8240c440540400b600000d448800f030209000850000461030810320707044082c1011340e031106c84200e01d8024489405150b4030b0000c106030311003000000c0c500c480184a0415280d41103642030f4200c1c0d481004030b0b06660700c243c8441490700100f229601030401d041c008214000f9031014200403445420b01070100d100c8a60021316100c20199042c80b0791a0403a1840ca0940e10300589403500c850940240c1d0107061140c4000518182155617039411124511702c2200780c01e449a019020000c1c003120248810740391400749141040881c502045114141c0320071520000401c42c4a464101c8040d840344040400c2241c1540315101d00000e80e805840005031071400980e03524451300c01c041c206002d0384070040c060300302e407042404140f0181091941c0241c0308100605504203504004d4050940680100720f9405110000702c1c41090540041088403840f000b02c1e42c0545076404101c519000440c5c407c030050b00f0500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 325613318 1250 325612068 325612073
    0xf01030b070e03161e0503100e010221220c060503090a051c1101050903031b1303060605150a02060708060301060e010b0903010e0d1d040e0d030504050c040204060c 72
    0x8400e5001070540c600382d9104403030760010034540a50130141c3e040d8041c98450401c40701c9850030000342110b01404400c0e22103403411021a03a584481c2403404010790f120070402003c0e032000d5050b500140d040b0b85030b110700945000c08505968006403203266501d00c601ca595050b0174407211720403d030154045a403007001c40c5048000c80d0030741c00c081c2001074607005850300c01d000f04000b00702025412990300e51343c04d1540d0130208090011a02800a80110303414001000300401300441504d0b80320f41c2000031421100503854401c0501d100703250031003050100c0c0304004070600001d940844c1c19100156200301880300010051003441c054040d4010060340300400050f0024802c00c0140d80181e405000490501d031509008002090243c211050320b803004541306c3d0081c6424012070b90f080c0b02d500301801c003141011200424800303801009181b84c8600b100702c52540d4440c0d610000d481c500b0081a1019030042e20b4004014107000d607400c3d10644240400080705241c544221402c8030140c2d01c420349590500d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 325614568 1250 325613318 325613333
    0x18041401180f030509041811040f0b03061f03050a0b01050306073002160f061a0307060e0a09140709050f0d11030a050a0308090f0a020d0b1b0414090c030f0103 70
    0x1000710350015220380108014800c4102d07c50003523441441c0480da04400c1506000440720948101c4603014202021130403103031400304404e030304100807a0000320070190610300f2219248066200502501c1140c030b41206200c080c000107810707640b0840684942c0d03201d0400450f10340000140500010003030480a0703c00a17624611010051801d007800341c200242c01e0180407240c0c400500a03294134101e01400b504101540c0b045600da4410120a01c451903500c00109503981c00310300070782d82800001504680c1558072841c02c0c3c802440d00709020700888076034120300b0b42107420603290710012821100b4081150f00d1f1220807440b03140380c09000100021280c0d15036440c401221440c1c40c0d01401414941c02c0410b074240a04486c1034000c1c1c54208090600d00f581925104040f007010300d19030025018040180e43e840b4008090907040900440d007600c07059660081740d49506d02d031101c10400010b0000381d0400203400424003070b404030388480301e0355a10a0111a1803008440c914000c030111801480002e01c807 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 325615818 1250 325614568 325614577
    0xc02090f09010906020406020a150e0705060703030e0d091d09061b040f060206040b0f071e02030d061806060203031006030c0c0501051f060302070210080618041401180f0305 76
    0xc07000104500e00d0949030301040342c0c0103400100058211000d81003d108260250703080c2588522002c000c4010003002c1c094407101c0a021f03945c455040006d82d6428036201340c10642d0444410300c140c42d10524010000b400700303860f80c40344070315948200680c20050481c11540c41c1c0302d800c0b48400b50115503595140c007503801c24a2003c0c101d0340c030070900000c20100c21035074442d80a00840d0300140118102801d010340c000000800380c1110181303207801c104c4102d512006200040200544107240740c2c0e1401c500740d0850050304200c541841c608540051406580c0d500c084070030160079001c1241c01d40700c41040f41c49100c1219801b01e030b4a41e980f8104aa140720740d0025122050b14500f0101840c2142e07036040c00d484003542d041c1c03907440d404501c025038183c0045001d0028605414218500400d0b40d01150074000320000e054180800840015020746038a00c500345090302441101c6810710741031408603000507184228400c59803802d41601c00080007096122101a04844629005202968201d409912 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 325617068 1250 325615818 325615831
    0xf10020304080a050c0a080a0510090305040806070806040e2a0a03140c01020d110a150e0312040b0f04030504090507021c030b090615091c2108070c02090f 68
    0x2080000041507403040c807651640c0f42c40b6602a01110181c20204005805250001d4441e600039000000005d01300140e03842000301c14040100d500382040c00e0555580c0140c1c0d2000c80640150b80030841c01c103902c0000e55210788000c0b10104214404845002c1d920030002c211901c106010201ca1844500c2145010201d804010130030f010700ca0b01d0f5501c0c0f0140b103400118800e804c1d80540503e5038150b1301804401a120101e15080f8a0b40c0b040308400e03a611010a24050103a035070000501200b4031580d08070300c02034000c00e07080301d035a59140b01480840100440d02980c0b0040304201040140b080940304c180101e130140e0300c0300e0502e8106500e41c4001c010250501d006c1d03106004150030011100915198014900e480008860750400d041c042c594200402c03940c800e040da40d0124842080b0a8282c48040e041500c82c2c2c4c00340a050820700c103200c0b180d503101800e500c90704c280c40d00308002061704000e450500c603a00c0c210940c6072608281c0300c81e40700d20802980080c103940094002c4401040c03855020b81c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 325618318 1250 325617068 325617073
    0x50c0703030b040b061201031218090f110c070303031a01080705030901020c0a0b0901050f16110a151b03050103020d080306031905070807060801152304090c0801050d020f1002 77
    0x900304d00141c01a8000b4070b4503480030403594010000c0c8415054841e600403030070b0404c480068801c0585126406090181480380d176651075051240c49500ea2010000048404156540d0f01480414a40d1115144001c0300007900309807100c0b02ca107042041d004521007041c7c64414182e01c0c2c00e001580d480c0c0008010f4181990709101070107443c9020801e280080e0b0082c0005081c07410055002425500300402c01c0c0983e0380c02105004031000c5402601e617401d005483d03c180600d8800c41c0c100e060040c02000503240395144291064844203a034000000020b001081c4c00f0f103403806000c247c040c2c5201740702c065404241c9030f000c0008500260000c5038483c0f00201507400440c0c14070010b403985110f800303058500750720038041400000020011900509068102042c443d80740400044031855000e00500030003501c140305210160440c0d000d0440b031000b800003291515180e10b00303c2c00a14074100c813240026040000000c0c6030800721200140640c01400040045007a441805075049070002d0000461 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 325619568 1250 325618318 325618331
    0x60405031002071406070e01031406010915020a05060f060414011d0402060d0c02010f0b0109030b0a090c0b0f070c0608010b032a0d02070b06030309030d030c0306090e1f050c0703030b04 81
    0xf900500c9600e218080c6501d51071f41c0349103200d00040c2101e0040c0c5419016100903414021541e03000720440041390301000c4c0c200c0c480980003008a0400c1c40e49200240039224200901c0316034501c10300b4141c401c00c025038040206031400c803002c10340700b50203215140300ca5402002000002d00c401070304a91190000e07010a244c4400000048200c1e02c0701800c0200503503482c3c103402600400c070701890042a809190051071942035456481c07620002800c0c00000c1030703031041143c0402c000c8018150041840340003841c1c81c0d02400b06046459401128119050518030f0f00105056000700400b9044e140070030303400d03401d40e5200081400c0645c022160300c2c0031803001c4c01580740070105550041c0011030800402586909071807510400405000e403100b07110350018440d02e1126100058121103c02442c80c0104580071007150540043c019030300310349503480c02c1c54a095000480000e188110541000c505407012a0a84070402241d0b807c0d140003154032410410345000c00d10a8101500c0200002c1c00066403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 325620818 1250 325619568 325619603
    0x90209031c03050f0105030106060e0127080d030c05040f0b0703090e10050301050c03010311060d09020a06080906090115051314040b0f0f07090909051606030605040b06040503100207 80
    0x5180d111400c4000b03510341c0104840381d812010901d00520050313009205685c103100014041b21111402d160400010b01c0e5107102c10f003542d14021442a42c00ca9012400075103950388680c86412106486c400f207800e0031080092a84582d04503000c1301c8008401544035424442064000d501c985416020032030071240108122541300390b518010090222180d08540c0340c40c0600d42516401464400e0b80101030004001181c007585546d800c00c501190141c0c1c0d2642510100310013040744d51806500b100040e04045022504000c0e05030040e0268001c5601a683e014040307403d0f035401303010b40394100081c91001c0119061000383c40a03624001040428011074000086250b00401c64003039908601003001d000035410103140c0c03180c02c101071001940d50791828140180c4090301511420301d54994036001c003000c0c0201844141350010106032058401c0c1c0d60795100602418890146a2055203841e989002d0ba14050701150200c0b80040c002e480031043c01507850b0002c1d081894240d41d02c50690040e11813 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 325622068 1250 325620818 325620853
    0x6090d0b010f060e010c11040e21070209090a0f0201050a091a0912160b03040c0509040614130203060f0703020903070b1c02091c050c0d140d02031309020903 69
    0x29000c1425110a103d241a078014145852201c0442c140101a418500483e2095145286000d0161000302c0d04aa00c00d01c8103203494040704d089440d80ca0b4202c5080e1035a4032010041c14041d000726005545c5480e212003440d22a00e0080c07009114a1006044400550103a406400c00380030b0703400d00c0e6081035615030010190f840407124400700342100003040341346440c0110381411600c0c191001403940350100c1880051805941c0a02e0741d1861001c00048c08006c00a08a10040c5c9070241204260f41401d01e40b644c0509001800d80740a86400e0000410a00c0c14140c46200c5980081c010005034442501c90a0000c1025101c0002c26408200c82071003514100121402024071291070b950700d00c2c030340c000c0e082031b60442c10281c400f031801044042071a0340c900112204004681d00c8a0481940720f01c0d1591900380410041e607041080301c5104001e00100c9041117096400807401d4400c00000d13104200e03100c0c402c0b01303010514013191060130321000000d0741c040d28142030098120392018003102c20080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 325623318 1250 325622068 325622071
    0xe010f0903090f06031404080f0f1c050c09030a0b040620180904150b0d02120714030105040308012306070b070f32070b090102120f0906010506090d0b 66
    0x700441c62004080000700c4500c0c1e80400140340780e207030400101d24001403a814004010b00060304484021a81249103c101c5040702c1460f1044407950751f59103d4502920080342001c80f512151600c2c0c2000102055100000c07220508802400b5004031401d6645000c0c0c0c1c642c000c0e0054481a0362040c02003140c07903413017650b50213010000000c01c0d2940b00f070040444042a2150549004082c900c060100140d80c00f01e4040350000c440f20003091012800001c02d00d4540c280801a40c003144a40c40d41442c0f82c7c000c0342150648550440c0c4040018404d414142a108240c4000300040c4a040041050841d081d100031040d00000d00c14400a10300c020024100341c00805c001d82d25281d40c82d060224468100681314100a01e50401a070b032004074090503100c80c0035500d802903403001c22010000403010040219800755600c010240d809040110b8024002c0d08140043d1000002c14004585500b0540d034207184503105104c0104260784c20a424000d141e04400e8510350450b48032216600060340d003d201c030713 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 325624568 1250 325623318 325623323
    0x40921020a02100c0b0105150903010504060618060f17030c010c080f060d030c0b070909180b060a03050303010303050f090603041113112d160b060a08030901030e010f09 74
    0x40ca40e103216401003201042c1581e00c00380c14440904c841c44005010700d108181110001c841c607030022a590610050144500c220311139055180c1410001000501e80c003840545102444d002d080c1100d06c84160221100350041410701a503c11041000c07802d15060f4445280164003903c1c2002464003049080d94460311018020841c41c5080280100300b10a02c540c0c024003c83e018500c500c642d850103043c0d200c000c2d074003038046c03810000003c1c1d41a002c0d802c1c00c001003000344002c011141441045841084681d102201c0c08102d16002c0360051031b0007080c0c4801c1e0f071340140107140b45074a1540e058405600c02c500b01740c0d52a030288000801c40d501c0c1c001561081d809110711240c1c07020800c04100028403078406c01c882c1903182802e000203101c401020345d140e200036400494810041955811900c0c03019180800384030900040800850244c042d40b055203600c102581c549585801d4104a9a0005030095050700d174402d0258036a658403d40251a16101c41000050070f00036802c26482507501c8803905 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 325625818 1250 325624568 325624573
    0x20a03172706071203060f0801060305150106050a0c05010902040905030702102a15020304150e0c10031505090a06050111011a01050c010e101a010c03020c04092102 72
    0x4111a6156000d05001c0c4807105480040031520400011094050000050803c40044680f0700c4c107203000c0c0d800030020300850218400304554541d1858060325507400101c855014000e601e803604c103028400e42d07050358030ba03483d030303070304040342810105c1c0c00c200201c605131042e40d00c40c1d91140141c3c0b96842180b000da4041d80145a41c0c550500502103c0159015500f0400501002c00c0007180700c1c0990150f0310700b000076080111120390b03080c04100c00c4911500402c0041c40001840200f003000c00440b428200d91500c10700840c822000482d8440346a00c800642142d548402c040c1d80a01c00d50129040d01070200c1c40503c181e440303a002c1180c00f207040f15071807201551504103010560700301402e80312034982100240f2205046900f855205840d0200d214103001c40410814002402034228428000d064021222661842e144c1c503c06040365a040100040d0907a488032201e512a40e000110b941e010340003010400340000900c801010100010b0710700c0c1c401c01d01071440d4070140301070308180300502d03600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 325627068 1250 325625818 325625827
    0x815013c080d021b15220305070b0301050d0809010c140c0a121e0302190b060f010809060f07090504110a030e0a0302060c1305030a0506010303080a060b0d09020a0317 73
    0x3002440c20b010342d42c10405540c0403100ba8000c55070f5010711181c0c40e5600703884205020320f1764462540c0500900c00240d555603507a0480ca81c03180d071484a41000caa01410894084903901c83e07025000344820300a50780c1100403aa052404921664020300b40c03c00c0625250304480c0c1107413280807106010f140703c0001508103403440c42d4a460724003e0301c405000d010064200da698913035200e030380760003040d0002c10b4821040308490301070500a01000d9507107225810b00c10b107000601c3c504651340c800c0403501c86108400c00000140c1e294400c00c0d0b01c5116141c624000c0107151100560076600020040003001003001101010900d9104e1340207601c050015000c29a440b003691010280a0707030990700e8007083d5507120b2800356010a50009105401c402c43c3d076032072555050204001c6a01440c0380d08a40d07010f104002c81030080000016445048034041d90b40d407451910380c41142c1e002c1d00c440d40b190028100302400310000c0b811565100c03140c0c5510013802d02d01c00d503941740e8400e000c6070070076601400c2c0080c0219 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 325628318 1250 325627068 325627079
    0xc080a0809060601050c0c0f03070e010f050102010c050a020a0f080903100f230103080711150a11030a1d131419021204030c020406091a03070815013c 66
    0x2c080c540001d000d080c0a07043c0141c0c40001d43da00d0742d115075183e1240c024184040f0481c0c405100701800390800c00d0701c40f0040e607110322800401c4c0025204160040d0b19010f0001a0f03903200d40240c9902d06015400f624003c070ba03c1e162501089090304041e644c1c20000c00848145a900300540010b21110160105140c1400000d40c422201c0e2808440b140c490915900c0b0306108032517500e60b0540303500118013a1100307a41e0a04a61f1074400310081600320307200c50869203060440303101810600340181d45035400c000d20a98402d49038003135034030030380701140f00c001035114a401c00f20202510024080c0c102c0d1103d440c484651015501d0b04244200c0d81410b0302d003880038220310000a40030ba00500641949409240c4401e00c00e445401480502000140c0c0645800c560f140e80090004080191041c007512800c03604d40c0101200840d000ca1203485003400c0058441e03400b1814900100d0040e038032800c070307a20308081e80300e062036030100540100050f501000c14120800680450042c08510241130190510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 325629568 1250 325628318 325628323
    0xf0f1802090609010e1807080703061406011404060e03010902090f070906020102031005090702030c0d0e0a0f0503060105060f0408011530060f090b0117060c0a0503160c080a0809 78
    0x2525640c003d40005005000f201150190380750000900c0c066a1440144484920b04125098000b152a030281603000405d0082c107800070032140d0003030f001c01c0042d41c0341c440040d10100351207529007010503000e2100f086072038000c0b440c085e03d07801c0c05000400c03000420790001d0f07844c071811940010492890814044035690115a89000d84902d000842c50340c200f0380e9200183c5c8140b4800c4c1c5108603503079400500050b100f402070395088001502120510b41d000803028107143c0ba048000c5014400c039500004941c0e00f01002d5404903000500a07140030f034204403c0c45001d510401800d00203000030003001814210900c00d40b00c103c494100702000303640c108850f402040903006207080d641182c81c2203c05486492000510324107501034000070b24800541035000103003081c42d0000c0c04601c0314000002d004159815080107804100d0b0541e4100d58510301c00c6965401100c41c111300040c4c3c02d0000407005030a0090459100895003002020710025551f044029413100c007031200001c0001c418000b914404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 325630818 1250 325629568 325629571
    0x13030b010905070c08030a0b13050a1a0411070213140106050403060b27040201030e07060e0a0e1e040507030606080f01050702010b03032b0e03070c060e130f0f180209 73
    0x41e1130a940789074620344801c40c00380405851003002c660340c4d85100503203641c0d042407485681a09103040c000342ca0101510350041201c244030344040c400709080ca121a20f00b910520300f1404403074183ca8180000c9400740711516414020b1580425528900300710f01000702c000c00c0780204426524980d407241180b40500650300300070310860003140c0d1484d071148204c805090303114095880d0420f0041d5542c03070307000490180c9800208000e19000342103000c00d10641c89140c07100990404e54084940325507801d13407241c5500b0112000046840180c11000420301008460307504a1b0140c1c0031140e9451300c0780c4507c01100c0070381d4080003050703010318003d500491003805002c3c0e0140b03040c002040f0150510000c00c0d01c07403241032042210000d10580d1b03000f4000c0d4800c4210400281c0c01410403d215a42d51070b5030b40c9602c00602660b01914910002a443e4402c007004a00064041c10030415078141030700c110090080725101e903d10640b00c207149001c4044512031000c90117828400b07400c0c1c00c1424014030004000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 325632068 1250 325630818 325630831
    0x80c150f160c0920030609061f1107080708150a020c0303130212070819051011070201120506060a030905012d0e0703080711220507031a0d03030b040213030b010905 72
    0x3c41c6100d0340010001d8041da030340146c040e11105200c6d0390300800529020004000d4800c0050802000d0200c80e520000b4280d4a51080080780c209944402c0d20039903e1240348280041c5a2003100d0700f201c03503250344003d142c201303003544409070424003403266981c11900100c8108208002410102040d13280142e03136852a4004000a082c00e5414568910f4a641b64504901044d41400140030100307c800c201c508501505e02400700140800000c04984d254440e0000368000395605000900103000b500c28a806608020102c81c0b0301181400c0035009004010010740e15556188051150780380004285141c40c001c06c1601c07202d081c2d9240d000d07001c44004080340003907079024107401d00001740c06100311003803a50400e07407549141d0320403400600a100c00000103070741d00c0c1c1c2603010503080410380e4214501901e1070303490510850b00c3e02443d0510130b074000c0d1b035640c2c0e10061140260010070f001c0c1c1d00c10a2000c03000f510151400b000340510f90f1740305c144c952003214800001c500410888600e441066000007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 325633318 1250 325632068 325632101
    0x9040614030d08070507061503030f0f08130c03051506100203040e0112022103070b061f030c051b0304030606050307030f080a091518080c150f160c09 66
    0x2410011aa66520440b621401e00031444042034809000f5001d03103481561040052041030081c2c0c2d031003081c40c0464032044010480014143c12524004c994802031030a495690041036910041540409400010300345d4a0400201021020580c18854100c2e0681070806400881c01d01506200000258420031421908203002c03d00203d0020003c0c1411203074010076200601025000203207160710b5400d00c03100021805906903500c0d01c40800984115401102d01007101e0b51154180442e41104840742e111000c405020318001034000c0c0c0c0600d2800b02140751050420310719072480003c16641c0443d00c0c2c0258030220307080040090600801c2c001d083c00381e01a206070343c55030f42c0744003131101c6004004194134008950030039014443c3c540003000701b0721b00b0014842d0150400024120142d100507011900b080b40c4008210028000340007503840c50040c00384107061000c0307810422a90480e0310028003c0a080022034185811080c652027228002c291420005181c1102c150072520300d03049800c20030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 325634568 1250 325633318 325633349
    0x6050717010f0b0705010204050a08100b0d0807080d09120903051e0a02010f030b09180d0c03020c1215010b0a021902060412110904080315120601141212090406 70
    0x5540d003400c441140c43c1a00c2240e122612407510178003a009070f81000c2d801003000700700010301d10030024980780300a40700309040080300c65150a101e05c0b050040c2001d0800f000070800403001640c4c2c0401801062119100090243c03115aa00034403040d185c0b01020015046c500b0906c03d12000340300a03814031900005211002c50112a060340f03038006050003a05000a000d4070b841f00c1c03070003a000310030032080081491001c0c1c507228041103040c1100e246000024811b0b144960052405244406001c9800da0028403222000b881000200000455110401e000300d946080d400b0b50140f4865010b0b048044010b6280d08014400a1a25807107400d66800700c2c2d4401800400740e2280c208a40640300c05001140e0305030a903090030118a031400304026005a00e0740200710501c40d8000c0650300950304080f0b001100e5800c2d00401416061001420840d07402c40c800400c600403039241401a14480070f44030032a4403807165142ca0500c03020320700303138851850005060503441c6058444c441c0603107901c00361340c3c845 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 325635818 1250 325634568 325634579
    0x50d030e12270105070c12060b040e060402041512060c02060f1504020310080f07090c0c1106091c05060a05010b04230301060b040306060513020408030d0b0f0d0605071701 75
    0x1041d2100d00a405490308003649109544d10800481d045d841e049070312049034940e580030458a1070181902075856034681160a01180750a01920110f40d60b268020b00303580d20390741c007040002c0c00a000800341c54009651b0002d10403180c0b400e84a262030184100046030600b800c00603040c00c00003000710085e1010300c420031010080340c105105d400281900c0c01030712540d0340f1903107518240b103c2d000100580310344d40c6004040140082c1c000141e541068090140310404001902c1d03002e031350900144100703540320326568031381062400350007805402085083c2034029a40c80e80c41d582502d10007a130b00c0d038100004000301e0107520f0042c00e0040c01d44151107450686000c81d1507401c0d080004001114044a140b42a0b82e950300f500f004d0007815401d50100e036681c0e80c070729102c001440c1038440d0501072280c0418181154900f0b1090710102c40c000e1014601e020071642c004030007485091b0410b41e01481d41c0c1070040c402e8480c0380c00c0000c0c291007800700003124289010003809440c490a4407141c21400107006124 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 325637068 1250 325635818 325635847
    0x605071a010b0342040c0203030610050c0a02060a050417150c160c090204030b0a021303030c08040f0e0108100509210c01090b07140708190507050d030e12 68
    0x9221080c05080514200c214806045200c0082d65030142414100c4d82d44c18028021501c078a14030368111000c00c002620301c1740c142d03103d02003142c1065120511030004600a030140c0b000380702d405100b4040e0f6242d00b82e1903000424903084104410005000407909201200d803403006102041104030003041c41412044e07480003645401081c2d032006100c0030404068055114500c0301890350b10031034011300c85840380764020080d0424401a00c1d001c500c080418050721051085030811010b40000845850443d24103031490708d0614012101003104000000b0030000c40019a03014103030884040c1c0c0654500200540350089a1200302c54551410381404154280000e10b03627002c1446035007601c40a080c017220081507011351500d0f6000c95080001040800c02c1d8607400901c80c034943e0300e030a00281103140195065001c0d241006003d03520400c910f2403052140c80491f080c5ca144c6243c0300c0d190510310f6070b444e8103202c60006d031240400d071901c0018410400910210f500841080101401d1540185501c803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 325638318 1250 325637068 325637071
    0x1b02011802011d04090506091b060306014505010e01090905060a03050604050a0c0f060f230c0c0907050903031b01140103110907030c05090108150a0605071a010b03 72
    0xd0500c545107000040034440314048820f000c40003082041031101c141012a1101c504548d00001d50080580154440724064480945031034003030500c900350f583c0c0c04015281080000e00e01c0d04600c9040c042c0011802002d2903054401080840c90228183c01e070242004101064016078140100c5142c031030600d0b40c1c006200003c44c3c0807010041120346418020441d12010780d040a41107000b2002001709200001864100441c480c0c14151961030340d4440c841d00d049241d001d14000a20071420414803544120181420203802c41c40141e20044610780e02100c99000c07020080864006142c180c1041c680159095401411800c01a00d40a081e0340040e03124400d1404004091801d80344100700d212096000d41168031001c9408065940c681c28645201c1642c00026803150300440005001580301e1301a00c51484103a4813424149807106d030043d900142c0043c040c492103a4040f61442095480c0c10400c07006080310b4940c01d40c0c40c012818030380412511501403042c40c3d482c0400400205400314202da = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 325639568 1250 325638318 325638323
    0x50a0605150d200315130c05130b0a0804080901090b0a0f030c02010b210a0c0e0f0105011b03083304062907170403240501210501020408101b020118 65
    0x665820b048200103408501e05c0d00030801c0080c80e0114041f00d00350000020128a00b43c840601c10345540c8004028036403003410080c600088c480c03400b20703000402c107001800401c501410192035082c1c440c9222000c64200c00c0a190000c1e50032400401c1c8107030107102d501c082102c640300074031950b580c18001c1080440c130310311050b40c1c100300010a040c3c01d000c2032042e42e0500c1e81c01072907c46802d68455031281c074500190b45500e01d04018500005056015012101650180c564200f0705811a40c900303988200c00101000d01c4042c00c4196402903181e4560003101ca01a405c4007600000c40c0502400116416a00400c8c0038005066075514000e4082d0032070440007240340d0b442e82d41e8100c40d103001926141242001100b021000c1004070800c0f00b0380946801d607150440c1c032106d0424250019806540c028800c0860113481c81422079400072003412035824241c025400546061f80d41d500c82441c01107a00c0354005540ea803610311200b410603e11107160307100d8445c8024403405920792064601c0c0e02412100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 325640818 1250 325639568 325639591
    0x20721030c020105150d1a01060c05150601080604090201120c05031005010203074103030417030610080901090b090a1b180c0c0b100306051b030a050a0605150d2003 72
    0x252410811f1020015920b4001d01040c1442c42d42d40d90409040b2181d11001140e1500800140d048034101d000c160522400050b503945a254441c0402d2100a140142c000d0341008245181c2040d0702c2141d025092090700c95a03619503403490901d0700141441c00a80040b4110342081020311301040d00c940417405e1150807038090741c11141c004a10545413003800c0c800a076030104420304034034004030080007551180780105903111030825441c01c0c0400b43d100880300294415002c3e00c0780b1811611500001d54040d215500000d6034030015128080445021640120590b1181d100c03641007209408503d0100d40c1d0714407103541b1440c2003103849131428031816648070000d90b8803a0108030712071040d00c40d2015135802c12401c400c075003420301d0540f007007560038002500e81d1b504010100c0c1280c41c10300700040c1c400d40c40d111802d003103484103607103c0050302c4094030141501c0c3c1c43e20004115076075035800680c00e40d80304a810680e0344a4480d04901078900d00d010765080c8981c4500c01c14010f1a00c0d4044913402207282c0c0c2d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 325642068 1250 325640818 325640839
    0x2a0402030a0b19030c090606021e0c15030a0e1603060509030d0606030b1002030a0e060d060f0b190c0c050111011506052104080901050706020721030c02010515 70
    0x258000c1c010503030103d50001c01c15070480b80e840380c0004400c050b44d0154500707001c61a195450301c01a07451314800c0e1001a449817454500c28018144000c040c2540202030340c000007400000140008040c05401140a00c00814854018800d2082c2da1014507400701400545103070a40b400c0d004500c500c4040c2c002521100052503a80042c400ca4010004000080220707a8031904010b00038030000540038082c024103104659040d0000003552040312142d66400e4901d070b03c41080c4505500842c1140b204252a002c010a00c4590311156038081c0140303020b002d4988901d84c0a000c2c3e101c84221181060041d1403504d000411000003c0d002622002e00704944418107100c9200e0042042e00002c2c0355001142c00040b416036484030040070240b1004207250b2500098400c008038140c425980208842c808014000f1154050406003207800c0c000e040c0182499815242c81c640c5000c1e00000d0148414641c0540186076058030a00c002c13a003142c030003008030b0b1601c48081c1414164202c50203114002008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 325643318 1250 325642068 325642081
    0x9040503040e04150b1918020408010914161d0702151f1a0d0b06040b030408030103200a06030b0a09091401110a0c0303020901030e0105040c082a040203 67
    0x1141d005040186040c0c40c1850982880061a180c14921030392550819103a0400c03480c2c00144e00300000b5540280303007006490102c40303d2012074aa908816460380a100c0000c004800707200d80b1070094003034004560910209085142402146031614030b840c1c00900301488411014503004040104c0c0014101142e1601c010a03071500c400010450000030340c400030050030700c000c86800e1040f045510155260281c0350082c503600d01c00d83c1c0c800700d4100b602c2032002c0080c842003a00000c816a0340581918541030311040c3e4a90f940e030040320203403204c0d40000010400c001c2481039a0b05c10304c80d09207090205003030402c0060381700c98040c4203090805442e802e491400c2ea0303c0c41410030003000807800400c580d038070500d03101400441081d420301403075103444208074001c1050000c9841e602c00559440741e0420169500340c0094000c43c3c10300d410590703100e00040c1c903082e00348206409240a030303c00aa2030703846d10307222501d002403a00c45401e40b044803494dc4e586c0e22840201070008030f141140c000d41c807580c130207 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 325644568 1250 325643318 325643323
    0x60501230d0f061a120f1b0a03080a110d0f020c150c152205070b0f1b03030907150c0f020301090204060b07111903020d030e03030307050406030b040605010806090405 73
    0x608042d24981c0380184c0082d0b1403c03070020300c045a607810b441c40864924009005620f07840c403140c1c0c03035006411510351609000041485000a0b940040926903140c1e100c0d11480000e4001b544c0c16000f10302180b50b1031058540c1040000425601c610f0400300e440714042d0001e44460b0500050345c0614a1101c0180c90240710301c0a54a00c1d030320000840f0031034144030103454850b40041c1c80d800d0103040c030328440d2500b4180e442e480c5113803075070404020700702c02780b0340340030b12000b0fa00a03c502a10481e081c0642c02141e0700b52000e03940f8040c040e000030f580f2400c1800c4c103030742450130580c03210000038000c501441b4400c0c1c001c00d112415640000c4111203003440350012902500d0310076002548a440c1000c0480c0b40010000034100c00c60003506001c0c40e4111200a1202100715003504801e01c2120140801c010701c6e20000700c1e03408038800d207456416210341c40d022130324580064500c8030204802080900209030f041c4078015210390119024170025113000006810741402030020303801064030780d0014003401800c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 325645818 1250 325644568 325644593
    0x609190c090f09021203090f060304121b0602040303091d0106120e0a0b0a06031b050919091b060f050405091803040308030c03010f050909060604020c010b0604090207060501230d 78
    0x14002c0010149203401c0300d03403a5403107107014a00ca40c0f1008e8100c540d40c2000c009580c41b0b5640140000400d40c0c06d00c006035188690211540301191040900000043c03040c005480214825203c0641b928144038451040c0b0982000a404030700007071004021035540300c10304070042c1d05070010024183e032804a645041c4910a41c014049001407420300800c120150311035070481e03010b41032a50100d003a100c61250300450070b10a042d8002300c030001060103401d115044606c9040103440006022429544010100c1c84d007040d044042d107144001040203640250290003003d455103001ca103402d0502c800600c0e0b003480600902e0440421080c3d01c5502c0e0410001c5a01440d00054559168640b040e05c8850360f50003400303000e071840525a000115410403080c0385000da000d1001405295441c001480000c2d00112942c02c00d540d01d4446059442d01c40500410180c401503401607954034460030318100b5244180d1000d8111060001d641c00c0c8001b401441007480c0c80b08685c0d1041e4103000d4180040031608 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 325647068 1250 325645818 325645823
    0xa02030708060a11210703140406060819020a0e0711100905070911030a0906060b1204021c0302030d0911100309020102010e0105010b0702040b04060905090609190c090f09 75
    0x1644201090355140010700714030800341c0800510a000134198060700d180160080b56680c3c200d10b8041c10480b5202c49030095208441d46000a1811040106140d07840300681c4c0039201c50f5902c890521441e4024000441407884606402403010b8003680890366500380c038880c10050445042c0800d0140e4032600880d0390b08280881111420301468410b4001000010000c23284d41c81038404c0090340c05124040c0b540c4808410042e13030306603510241120f014240209084420603a1848085004e40100000e400107511a402e41400341c41c1900c10b114069181034000c10030b142a822003100000c2e800012120441529140804c0c00605840d00c0c8901d11030200840e58001c07a040441d0b0800c82d815400454118000d9000f4454000c134004221308a43e0704b03000c1c200c140d200811642c405410643c00c00c0c1c900300405000020400e507582c035208100c90081c2c840c1d8800d90001000d01c25400000c101440b940c1408a08180c0c40400544d1291107031482c038403940b401d01e034548071407020050043d44400c180700e8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 325648318 1250 325647068 325647073
    0x106030e1f02070c03031d010815100c150b01140403020603040201050a03060306090f03030c08060108060d1502070c05120303270a02180106020d0c0f030e031e0705010f020613060e0a0203 82
    0x83c2c172032078060541842602c07200c84000418451250561048501600410001e01030301040c94030f1806203c00088002c00703103018482c0386400040000d0070000d564031444613208000030741c08080c0780014104c1030100b00180040409000500140c1d0f54a021640c005909090580e42c07003008003815405404643d002900c040d14181e4480c0603c00d0031402d03a4074061103070f41d04100d0b061080c042036903412400d4030b44a001602420001700142041460907540c907000d512801114011052158180c1c0e00640c0125201640040100040e0034483d140f05501c50544014504520f06850510f0300383d0142d0080080311910450303400c1c41035500384605e01c403090b00039240710162180c440c078104000034284075450062107041c0b001040b2a01ca00c000260755030f03100c0c10001361071150791000c030380b000710841441d54540074080c0740481d03d11200030080c61201d042c074040d1070103601c0c1c00e0024107802200844107003507410101c100b101c00c090b81d00c0203600c0030742d00a1001070388010380d40c801c6161040c40d00d030003505403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 325649568 1250 325648318 325648343
    0xd080a03022203060605091807032a12111008070309061b0c03110f07090903020c1909050604050c0d0f1e02040519050102100b0312070f03080106030e1f0207 69
    0x1130b02c2d800c40303415110240c81590035078807031400009002c17414818002907508001420701c0045e091102d00c80d085c5800b4040d2084060401320700c0c03440d0100c00e5001c1c2c2c1d0003e8100d01a2000c100b801c3c485e11741203803412600c500000400080c0a8085a00100461f0416070342e00c8401080021aa00202444c1d18040e02c890005514240203000e170441102d00780e011030011a40798040ca5400108403110788449070290140916041c2c00f0b0300a4090018114154020700c00c0c0c2c4c052585904109245d400000d01c5840095403602c6c0081c0101c1d200901424012410304041100c481e4144c01103618449040400040720f01904070090010b009040080b165100c0c0c5c805184204181e507000341050b150100e0b40d209840c4080c42d21010f40804078130803030f409a049640309005105065001da0580390b00542074802da5030703040040550700e42c4107590442e2118291400141070650103a0941d002d4495400c0801c82e140b0070402d8503544802c900b9883c040d0505c00760341d5400725042501620b0785260b0180c0b145256 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 325650818 1250 325649568 325649573
    0xf0a06031502030403030605041b0509060d14311103070506030c07020307081c1d211c0207170106030b0915070203360306010b0901030b0d080a03022203 67
    0xba41c001d03030302640003a04200010030140341600c0340c500c40e9901d051500501c4011450309443e43c1c0c02400207603501010034411090118050700805140f41e4040d660f040c01362420588205015101d00c0f0321282028990820242003001c9005c00079500e60001220350354003441c0d2001074508041604400d03000b40020043c44407000503100640021031084007616011911200019a0b070032219021340b510007584900000040c0c024240203ca034440c3d408500c01000580d004920b503074081d192041d0403d200e0002e07021040d2802d0209400c110710819a00341c0c0003000c144029611381081c046c2600316220700b500040c1c01d04095104400035540b140387d8083c5440d005400036120328805480312180e03081c0c072002401140c808812220b035070004c2d4024000c4480300c41d130382440e0b003018800b00c4500d50041141c10a015601085018020f01d0030351052551002e404000409545c40c0c2040117014854040207200081c0c250026501008002d140042e2a401c4000d0910f001e51401d400b004400d440701c03038001c0306 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 325652068 1250 325650818 325650821
    0xc0d0f051602010506060a030203100902210112170a18090e01060608070c08030415090f021908070b09010315030b01050a0b0c0c090406020d0204080f0d090e0f0a060315 74
    0x20071285580e6002200100e100142e090383c00c11210654094810481d045501c0c0c001e5000d141c2040c0500340c08408182c035480e26074101d0f804120000e007000d1740d14994180440b802030219002d400546944400000e0760b985420110043c00c880440910300410a4500d02d403107903605000e031102a034074290410760b4880034400246241040da80d425400c3c81c401140c1c040c000c41c0d00c540100400d40ea200130303001c0340307850780ba2958102070011610b5081084480c441b05000e80214031149000300b015101a5245104000405101c080c842161004082007009101e002041c01c7c0d08480241850300d6883c101c150040380100006101200150780c080c0b004410701c13042c84025410798400b69484076115032100c0c010111ba0083c5104400c0f01e6221502a0183d810300b5500a6081886108058140030518a5607803c0c3d0b0420f4002c140d865100e203401d280e65000800106543c0d66241c100650403600785105100702c0480100120340c804500000310381040c1c83c41e4003400c0119040301a4201400318000c8550 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 325653318 1250 325652068 325652071
    0xc01031d0111040801050c04060f030b04110d050f06120a0b040501090f0f05060f0c040302060a09170109020f0915010c0c030204050c0a0e03010c0e010e06070803070306030209090f0d080c0d0f05 85
    0x10203030345c071b0840040c1003030954204a50680b01d040e1207207900100000300031000342800b01c04a64000340c85802d5170100c41e20107400f038000381c10031910108081c80c002e49000d84079100100424400c041240712400c0780761000c20706500c815004640407246a44070f0030142d02520624030000c1180445211010900034601d25402200e40b10300180e07401c43d00d42a80412205c0b10968882e89180c0080004100504d443d1008245002c0a420300442482e80c038280e5804046070100d42d6403081e51511003120461a281c441d102d102c40c0110b92400c540d08081042c507144646400c0001d050102e001201c3c0c00740644141c42c50011035008000703010514101e016801641c21240d00341d0042400c2d10541c00c12480d041c02000d0800b5016174500418682400045800c0c1002010b40b9030003840c20051800400d13240d00041d840b40060b0f0b1030100d10203246206011070300d400180140c1c05c0d0380140184804c2c404c40441d01c1d03000c40c84075180007034403511030030041e500600c11712142c04032261920b080d50749840d03090b82016 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 325654568 1250 325653318 325653329
    0xb07050a0503040e060315070509040207111f0e030105190c0c050f010c09060f120f020c150906060105040305060a0b011b03020a02030c03150c13050a092007050c01031d011104 77
    0x4425084e409140c00e80c01e1f803815141d410109000740440f00c1c0d941040c0d406480014015400c1e0240403150b140410000306011500590b1312407031102d400c0e2025044034880540c400b003030f40208002c2c030f08254010501c00d0200d031081c01503a282c62241207958441d0048841c959000700070b9030302014446003180e000305042c01240000c2085050b0000e2160701551100448fc102600d87c5242c084800c04c41200402c09803a403140050760138080f25122410400c4810900d5403d031950800e40d0900140b1145450b000030403032410400108000e00015102003046034200d50101707004914440c40700010b840c250501c1c0c580301058102e00e204c46040c50390004102942c6402a000c0d0383d0240501024907846100401240e410b1010344c401149210344260000c0105084001203200099141d01c00949803002c594060040d880d154074100000b5100c0b10036001030b40c0f50142c400351602c3d1495540d50b88450003d002e8905050785d540355000034810700c1011110241491008002804038080c100d406e035007190052 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 325655818 1250 325654568 325654573
    0x60302030103120e01050a2a0302031b010c0504030b100b030a0203060a060e030c09040215070803010f08240a06180e060a020a020604120903080406030603120305010509010b07050a0503040e0603 85
    0x2d600b103e402903215001866041e590709103841482c25007987d254141e01a031502145c0040c1e141294100720050340c2814920a0b0302a681d075500900105280d1640341d5107420b01ca0745810300c0021001e40100c00c4808581e48542d00a10580e0380700840c1d00314403041e602c0300c0024000002009158a2a580158071904084800c031b11082d072213880481d04266880a6079415074080340c2c540d03c4504d01500540e9100b072000345080c00038000e90902100c20380141030101c41c0402d001c00103100c0d094001e0011005400020300a2104000d90810b424100305402090281210220046241814240c01000103003650f1003d4800304013592422600801107209040d48900461002c9a42c903280ca0007200c41c0c80c071155001304015119500c5200304c0949031584042401614100040003031048005000101030b10303140010400d2039410010500c3d1948625030040515210050004d4ad0341d406515041d520002c0c030198030781e01c95141035445d1510341480a0b21a100104001030641c0380b02000b244225426800d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 325657068 1250 325655818 325655843
    0x6130510020109110409060204182304050a060e100c02060709140906150d090507030227010e070c15091a090a061104230114040b0405190f060302030103 67
    0x1800ca08980c2d11000044c001c80000d4984142460f1641007130042a000b11801031402e03a0300c2c8005220803211246072075805803104031101c0c41c0d000310010f10704081914200e40d200c1e807802c0c0e618281c4a040c90000100255a250a15603158038104050700400032051010001306004100280d6102002c0715031400094510b040400d07400c01000c010100311801405007005511389800f00200d20085503c6148040e03002c0c0b101c8100260a0700400c18854020300190a5117030550061000303104900300c010700030948c04214046242d841d00304443c1103d0a0a950f4200c940f1080710032102c2c400061400385c80050b0301d5080e070101c0801030f0301001c0d40c94441e000483c050303040c50701e0451150300100c60202960b008404800041001ca400c400d076006000e211003071070a0784603100003030b207040030075000f0901c446100ca4400065802c2403500803101740380306031346040c40d2030080d106000740304038058140206045020140054007060400004d00b03600500007201a80751007000700250024071060b02c40c00284107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 325658318 1250 325657068 325657099
    0xa0c061a091f080d0504050d06140c03070f0c05060406050c22050406170d030213050a15020c030303061c06020d051303120b0d030503060a051e12010b01021903020c061305 75
    0x104c01240c10341c240c40f400e003014641b20030040011000101555582e03266028111811640002c4520910090703400540360708160384014545888160074006011840b0700040c00315100040065200b81d000ca00410581d40c2d100303101002e03000d1410703c0d81501c0c400c002c1c642c07150349008c041c40003a5032045e0307420072403903a58182003968100c030040244000e40240900c0f00140b4801c2e0010099078a5010041003426982d00210f1101e04007540002240001180030304003865061042c40300e220401c800a6003981080000034181900c4100c05031018110204107104014160301501c0d181c0640302c6c4100042d240041c841040034034550000c80005880745130810b40c1c029640308424403240050100e00e00d51031a0303075003a01d199001505e0158040140080007850b03603203003105004524141950907100030185014004442c58200001115034140503070b04400da41d00141140b40040c4643c807104810f941030a050b03040034842055207030000000256041c0034090040321108465082d550030000c500c110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 325659568 1250 325658318 325658323
    0x150a09050c04170313290f0a021608120903190308011d010f050f04151818110409020604030b0705040f0e09121e040e040501060b0a0c061a091f08 64
    0xc00e40448069410702c0305229214410391980201c1c00c803143c6582c0826000144032140390003060a040d19458006900c920680d27040c80066005010a902c00d01c2c243c0c107048002d611610508c10f542c182c1180858041003030764080142705807041d0783d01c500300c20424036410001d008030002d0180c01c940c80c0008814040c60300103003c0b95812141c0503152030044a003490704000411344c00009403580207032200034101c92909600e10540080000d006049114039034402e10070162000c00d0548080d0302c80c0c440c060700118100e041600741c03181c0200c500040c424003610000e192401290000340c401d02040c0100025160040000d20565281c040d2081c0a01d1307890000504802085403009050380008035820072503003444029012001c0110364100320380741c81050f020b000d5080b0740d2003d80e903079007130030188801c2c05020300c503690103415154030091400c881c054014045414107403000381030710740c0c40d40413000b03082c20010024078001c0001c040c1c0c80ea50500791846d10814520710741c0702c0c0002c03000b03000025048900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 325660818 1250 325659568 325659577
    0x1020313030605040c0302030f0d0f030902090609040c0b03040c0801050f0103050c09070918050a110702030a0b060f0d03030e0f0c0d02010c0c21030e06070b150a09050c041703 77
    0x5160100388040d095582e820050080900105c4c4d00700c50160002c80143e500740801c030010305821300102a03c0d2410f10f0003c2900d0000e94140d03081c103207099500400350b2140121150302000681c1d1040c0d06454518100201880b69405a80c0c0c280780031041c4010405000000c50846043c0c50081c00a500c601d80c450340c2c10320b428031004001ea03008940484460030300d20140703688903013a41050300a1a80c3c4030310000c0c551580b0310715240e545649408016000b9158425149610b03583c0031103a041032000d9003c650381e21003070440a41840100400104140da4000c400254180094182c41030718440c0d1501a020385094031a11565002d000e40b5461500c000142e00c060b0200d00400c042500140e640042d903040315604011741e0f54213248030300803820440c80b2420088400030058464080c8600c0e00703000f4465000d01410910625007041500c000c181c0381d44244e600f0504504840321045644400a444452a640100034a50800d000c010352000e15070003800403601c100d844400d581c85d08400d130b01d80b07078403d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 325662068 1250 325660818 325660837
    0x70b0708010f0e010e0703090b01082b021f091e031706010806060a111204051009060804060b0f131b020303040503031323010501180902030c010f140c0706030b010203 73
    0x1103c001040003094a000c4943c109081303060001c0c0e9100b403611480e0b40400c090b00007221310740c050205000e0103815010000ad420003000c000f28000c0c020000000d455041c02082078007015080d40c811002c540007584150030081e41f11301d80040030341c40d5141000c0401c1c1c0700f400030350100700789030240d44d07982100c000d010384944c2e4142d450002c00c0e9105003c02403150000d0700c04030308000381c0040301c003c0c0000400031403d41b03842e05501c545d10340d032402081041c400c110210490800c00303601010843d07150002c42c07a54000c4c0c0d0221001c15490700301008a00c250410342040ba50240c1c600302e110092060781c0d400054801c0d000600c245054800001c103030380d64070041d54018656802040000c40840b17107401c2d03050f84030f0b00c00e442c0f041c11010204040b80d140b000000c1e510f6051b9642d0401003000d40000c14000ca0408401c0c0c1091081d0b03041a000603840c1d02001c800c5a050180d40408010410b01c80c01d001010040034103011529060600642981c580160146030040b910b4211040c02e40d40c00081550361224 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 325663318 1250 325662068 325662089
    0x1201180f0314220b070b012120030105070c24111207021006033906030b0109061103031303050c011a0a0e010b0f070312050403080a060e1029070b0708010f 68
    0x34a820054030300410722000d080c0780960300ca00d81c3d900050382c0007080c6034039418601c27508410413100070401d0300f150005051103042c040402d026000103085130072656507468000c02c030507108c0c5481402e0034000d007480072502d0904890001d480c0b6641c080340010140a445140e0840e00c003500c0c0c81d291030342119003501002e803102d22240402c0c85e01c41203c1d0300c90300e03080002c400c0d2400c0c1501c1c0040c039000b06070f000341c01520100ba2034107c041025640060b4050040105103025203d04800506d25526848050f000c0c070105203884a1540c1858051001c546112095034020000903000c0752041d86810080c030403061054100c15030004494a8440001e81a54100c000745882c0c603034000c0002c1c4580e401400201d00707000384a0000f00f00d1030b40034030030144690b00985500080c1d1408603200741c1100d846400840d000d0040d44180416009421848810b81e01880c0024103409040150410b100d5505a0b11400122001840e5010841c0103000e40c0e0003044a500c03455a166210110082001a2070003068101c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 325664568 1250 325663318 325663321
    0xd08280306081209151303150615050306041401080a021201020906040b1602060d051509070f03090201020c0307060f0206090303070c081606050405010b1201180f0314220b070b 77
    0x40c6000700c01080352144c014034003c1240981c850b404000d4020700f001c2c00c0008080c020400c140712610000c04030b03240c0c1400e401c00c480c81c140b038055018403102c603026404100c070200001d64503031107607480f0b0901d81452404d000690341e59910480d550380c2d01c6a000324000d06140400041c112814002d5402c0403030002d2103c2c1c1080d0610702080c100340c0040d00041c13440340840c0b0034000507031218401000f008108090108040c6481c8194004c600c1a03041c1d9107020b88403000c1040103165100700615810f142c1854040341055a50004034504507690303450304d03890f000300e55001840580280941507582d240d6001e40300280c0d106c82c0c039180c40c0d000c01c4903141e0114400c014000001000c043c000c140901d10051600b01000454030f641e003c6810451341202c181c1c1d07441415103d28981080810010401c1c04024800c0321202088100e802214500050041075a01d03820400c150048100c40c076810360040070a034450000b003a0300101030400211004a81d01e40c003c0c00315401c0e080c5001c449003650051710ba84840d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 325665818 1250 325664568 325664593
    0x1020f031e0307090e09030a030c0e0904060b040e0105011401090608010602060f0406020c010e0d09050303040303051801020f060405101b0c14030c0d03050f060406080604060b0d0828030608 83
    0x5030b1000703091408004284502055803c42402124010752103140115210400074001800300d40d0344c00543d005000180301880881d41d0762500b4544d015a03c2000031804094600109000d030913000e024484650800300013003800344488105002c800000d81c0e4030503080381e8403401503403060300a0103680c0c01078001d00e00003131411640213180764000e44202d40040c074040e02e1210303607400c44002c04650001a00105c6104d200e40743d20071a0310000e000100c1c059458686503076400781c090700c078006203241203c0943d10520544d1f070007400100508100e90050b1801460980b6110b80c85040c8071748582c1d0302500c1c0c0000b0f40401050a0f0101c0c035000e009480c0c000320800360b919543c2d0b031402e0004c59181030b44001c012402c0002c09c140051f2030000300c0c2c0d4030f010032107003440000c0755800f1600500880c003c03441c10748100040200040ca4a42040d00083c00003202a0190b000c05c3c000403a00381c000e890000000b40207105080204803909030f0b102c5a01c000003215642040442c2994460301c038605160340401d804211 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 325667068 1250 325665818 325665877
    0x15010510050f0a0e04090b06180108070603180c0b0d1104030b070e030a0c090903020106090c020c01180b040e0114030a050606010f050c01060e01080d0c02031b040b150901020f03 78
    0x1095580c3e03040101c0462415000581a144a1002100c2d022101002d03c10682000d101d0080075042c0100e500e4510b42c104814039680d4039140c1304690402d521040c406401e10484e0145104113500f041c001ca00b4552104800d64450344104420010903281028210801d900c2c0c0d4117840c180ca80c4411310250701d031524002103a8400040001e01c1d0705000c0d40707401e600020650790070747c0c0007000e030000c01007220112400e0190031210640d00c00d00d03403a401c0c140c489400544c0403c00c2c078015082401d180f0f480d04040d0000807140c03449600310b0705440c0720028000c1001892045018129448200c2d1b2001d4400070600381502c0310405c5800030155400071b03002c03400039030094081040e00e03c0741c0d1814a0424002d4141142034890603404464900035440060102803403d000461428480d4100000c2c140c445038086652408030b40c101c040802451000190f5941c0c0b2600030b900d050780003c05041050342c006909201e184c1c4501c01d018090300c951148040700260110130f55000384580d0f2400c40003110451403041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 325668318 1250 325667068 325667077
    0x905010b18180405010b0301061a040312020f0102071104110a1416050303040f03030506010206040c06050f071a07030b0109050a0e090f0f010506150408061501030f090515010510050f 80
    0xd42c00800b81c0510750480066542d030301e00c42c600500021550b44c0c0c00b0300c2410700b111a540c20501130300140010a45d008140581100d0840740c0c049100c50403002031000c201e084c8141d00c41d0603185940001a20418403140c48808540080215800c101d102c940981481841c421280d861000c9183c20648100490800000d420007890070300341c4c05030b8080f041c0d84650860744100d90803144d03010380450320070a142c2d0520680d9400002030006108038201611100302c0206144502030800c00300180140c40c07080d54109443e2602e9210480803901d44d400220308036801005c03200c0308000b03440d1080e01c00c003e6110380000c908488014050900311410032464004840000701707044441c3c4290098820490800c0180d00364610b4400300000b41420041c00300708051803900c00303441c48560140018490090701244140c1c100411414600400744203000581c0507000b590303803612009250601803001d2140104081d180c905890105c00f03a0b0360380358010131091401404900e000540300b070003c2c0405501030070091 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 325669568 1250 325668318 325668367
    0x100b0108061e040c03051602010504171e0408030711010201052223030304120216050d0c0305030307120608010207050a12050f040f0303081509071b1b030c0905010b 72
    0x5400d100121001c1400e41c4e02e40c140210009903100200200100703075600703004000c140f0340b00034001c03401d00e0344910340308100449000b003000c0b10005841e102c0103034200061040e0554034101f5515036955100e0a612a04404415606040f080c1004043e543c41032280c03910654440034604d00000c8424520040990b06103421a943c0c0102c400d0b0490085050b00d1091002c03000c1d03402180c1d00e24140c03426486101c40540d45205550000388000b100c40304044649081c3d80003641e610302e20403100d041001c6071103590740c4003516500001044c88003981e80211143c00106842c10144251a95014818200d105a11024141e40c01c80d00c2c0890001d8540307541d0103070010303036494114100005000400883e80c42940308114045d40e84400308100340c1c110284a0b801180104500c4c0d01c640e0751008915050f000400c202d007040118071041c1c1c040c500c00d035402e12103aa00100d03000c9084003459040608103900d0700080d1140c52500100041c030341402d02465050322100f61080e820014244102e8804aa83d125117 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 325670818 1250 325669568 325669609
    0x21b0f070614090603100314060105130b030a0204110a14120408220608160518060d020f030f010303091203050409020904140f010f0f0821090918100b010806 69
    0x300b940d613102c0300994042c1d0400c5044030780c00340ca103242296141150903c00d107010b400040c01081503a8640ca483c14003144440404103401c0d540500103801c0550400c00250300c9490000c104840c580b40b400900310090b017607114103001c41901c80e0891074a000b0720034544040369091001500048508001c0d041d04204032885140c040c805c0b054000d050815500000c000a100c0030400c032106800d4841030ba6640324038108603251075420925018a002d400c00001e00a22000455103244481c66044498420f00d409245860b801d11201100440000b0700c405d03000500c0307401c1d000c03a941c07183c5810701c58201c0d4580c80c1c03030349410701c0c013602103010350000d2410903440390f034507140c44010982200604d407041810340e804490390360608a00004541054201d40200303c0c06404c1440007031000201c14003a0801d20302c0b4070802e0b14001d00000300c10701c074269034103402034a030000f400480782d482045040816403003001c0e15130750400d0800500440d07a000c040702c8e00003503000b0007141e9542000030303100450400f2403c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 325672068 1250 325670818 325670827
    0x51503010b0622030b0703050403020622060c0e0621010b1c05150d05030a030e07050a031e08160308161b03030609020307110c0607050309060d0f0906021b0f070614 72
    0x15110340c5c10038219500000710343c07078000304410145d061001950000038107403400e040d1002100030131000e00481e500101030a07541c203140301c1d03614090380c1e0702d5400d0340008000796640c54a1407452000600d2140f07402031b54820300c00000c103201e0620400d9510031604412450011a07880f01c0c020f02601c000340c021802d85981d04248000354454003030f60070405010f10015a5284940000101142c6402c0b8181900f0741240310280030310340d00c03c07040b4411290400e4810380c54801c07101242c020b004418074010030f02400090340700c60070f00080341c070487c02c1070207501da44401d55501c1d04003200c50010b642040c00060680000c8110010280c80207016440c001d1a001171010784507500c40003268001c0ea84600420390440b102e0380c0c8400204200444003100b595000d0030814141c1d1030640d28050703080b8240c4114404103512102d51a254018013203a40c1480061000c0702072410903034029070000381041c81c00c4a414031281c0c81c2400014650140e07046c2d1900030805c0714034000003210211029801002120010031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 325673318 1250 325672068 325672073
    0xb0c07060216140c1f030c1e030501051504050904080307030e06090f0706050f091c0512070c05040e06070f023a020f0307030e0604030510051503010b062203 69
    0x407290036100d4403520400014035002c01020349400411008144159206a001a1081090482d03510399150340d090126074405038103000d84030795043c8e00074514940c10040c2c210f401c03160705030082c6040b42d200342d82156946028140341045441107014481c0c1204405001c10000b9070300f50002d42d0b10500601c0e000070301800d07489049040c21025220f008040d880306d082e6110000b000c0c041c40000704a5814003601e040144070b4401414010307810300c14403a98614101c500d0b8064504d80c9041181d50050554990f0060314011601c590081102030740d0038101c041c000f00d1142802e11401c8100e144000c000d00f5580e031020411a81c1580c4a240c41c0c5c00c500481c0d20b055003d0100d0895075141070001c90300782c3c640d00c001c2650080c0300280d0480380f000b19400034509262402001c0100c070105034040c41d1038171015240d5000702c2c5143c89144c0c0300074945d1045420f0742810790180c0d80300c0350241c1c1071201044140c00080c0109403d0303409001015600001c204003000c01074400100d9000a5844030316200070306692074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 325674568 1250 325673318 325673347
    0x10b04150509091006020613020102070306110f070605192d0b04060e0609090616050a02032811070b1c0603020904080d0f09030f050d0f0e010c080f01030b0c070602 72
    0x1e03504c1081c4071030689410702a0f10303010b01505601004080260b018a081c540001b903031006244000b5200700c5e9940600c03280c0c4c0d00304400300d80415100380e030180d81e6003181b85042e000a1200312005401c0d45003000c002c0031030a949000782100d540c80c0300d903419102105101d5403201009054424100c0f0361380d50f4243c40107030b240c40c02820000c24035490382880b1494444144051584001d0030034206400400800ca0700b00003450358109054068a00300d03031a1410842c2c141c0c0307140329414000f00c40360404900750030040383c18010003580020b669070710340b10440010344903951080d507800364807140201441800c0c0400b10141d140e8808403161427001c66075540c1d980100f0080601594103480c10031001501001c407421500a0042010b07036450704005000321900e0043c0442e1260408808002e00002c0790688040260480c421421a03840c0c00c001041541d8243c1c0d000b444031042e03a01c0825000c50000b031a0049000301e0504030f0f90845103030210b82d80c40c01c03c0780c641a0302c01d0208907410f03542440f40001c82c41e0308 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 325675818 1250 325674568 325674571
    0x81003170d060b0304050304060c050f01050a0c0f4b0203030f010f0530010c02070510020c060d09050304080d23091503060301110d02070308070503010b0415050909 72
    0x14140c2565941884001e680a407041504540c418560400034070001070000011a4100c94040c40c10000d14406071070400d00f006400801d4071980e60a10051040d04030b5264000041041c90f9240c41d10840c00b101c07410b59824403284141c0070015842e207d00000b03011110900c82c401030300840c0443d0040c41c2141d46c0100c000d500d0390103100690005c02004074048132002290b0240070b01d61021a01a4507120001d11441020000d0401c010032007500409410001e05000441c183d49400a0010600c5480025525820740c419a8800c1e400c4080c50742c407450010070b4035108100090038151400f0aa50304d014080d1010079022120ba2100b04000100c100d000e002903119030b103469851129201401001c4169003911007801f1f103026200300404a5960f545c1c1c1d0407a222046019620b94495a5650000b801024a0078a12420034000208d5004410a5900400e0201d00c641c99101858496560446d840c0c0000d0066115818003008203000c4420200d40303449040d01545070041c07510401c54041001e0100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 325677068 1250 325675818 325675853
    0x3020103180c080601050f0a030506041e050613060b04090f0f02030a0b0c090a06030b092e0602030310080703050a08130504060602010b0a1e0b130905042102030403080307081003 78
    0x4c00300041c0560702d0103001005d11107000703c8034003540750f05640301d464079000c01030002080214583d550911140030002148155900036040e10080c1c60011a0040070b0184850b048a0030341c900032a0741901d150a106040c10b0b160450100e5110b14082c2c0c0d0703001c0d40d04111100980c3c3c0f51062200c1c010004440041d0310388100303585891541c40703c88d4081440482202130708504141400e00283c4081e03030b180c1c0105185e00103d16490400c002612a50700c003500e0406554801150030101004602c0341d0f0000b008500a624410100750255031380d800342030700d50400d03000040c902c3d00031100a10104540401030031012a03001d84034054903940700000340031200700781e11a40240c0d44400150f801442d0005104004104006078032a6122000c2c89003580e2851a00880241d80030201d100c1225010020704400a026203007000c01c080d08240c14001c110320203070141031000e4844e001084a0003840030060341c00720381d8050000c034115111408240da48000007480808160400c82c030010206030451031085c0080c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 325678318 1250 325677068 325677073
    0xc060709061205370507030b0901080d080601081503150703051f17010e010c0503090f120703050a0e0a0f060f0e0a0e100306020301090b01030e0a02030703020103180c08 74
    0x3031078a00c014107015008016190002d10304030420507002044c1e104014588203510b00303282010000620400c0d40501e4160248106181204100750160103071311800b40001c0c100c80183c410f03a130b00c00701a030782c80010048210000d4407c0303000c990306501171070240344c20125600700c551a44c4042d10201c0d15050004403a07030f000349003510038003611542612406400402c1c0207190b58140c1380b02c0c901c15510441c40c0c0314000d04003501404c1605081803c0d0321001c0f181054000038002c00340d1510f0000c0c1340703410a80d40c0c84014059800792403010305002511003805a0880c0c90181014515201914640c001c1c0c081502401610f400807a0796036540c12091010b00490035000703160130309021004262030341001041082c1700c1e92281410040e030f01c072500c403002c551418182c000710756210044241210625800103003194000300001c6540d0140c2e03000480c05d0f030000e0360200b01c4d021414850680d01c803409580a0b405400080050003d07500c06e4005071010360351303030816800d842450783d10080c09030015400140c858 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 325679568 1250 325678318 325678337
    0xb1b0316060f02090906010818060f011d04110f0604080303070c061805150c04080307080a14070f060b1f0c0c0e060604090c09050a122d030e03030c0607 67
    0x711051040030445050000210f0412a045010441c4c403e4064103031030500040b5800100205511124071450318510030586109041948114844413021b0041c11609401d81c04070360003081003007401e40c1c4a1600480002c060484007010b2021940d038881e203582e0051810003001c208503100308025030041c6040d5550082e00703801405d0000032030340324002e00381c0700e03a00c1c600e1008045140040c0054500c0c10022428407581c840e80340b03041d0144191391000081703000c0850f0b20802e00400801a0200380055103c003924000004103120340c0e4851000014902446030301904082082c41c2d00801141001900b00c0440e0351009a1074084440c00c500702800065a0111600c00c101c1481d11f10030080031401100140c90a150300020b0050140340101480c0940c2c806540c00d03c5480740784000000c14001c3c003100c2c4d2040d183d042c5980290481d00c4181d85040c0c81c1d01054030b07840080d2150050003440c201450004403440e50b401c5a404c250326413815450b00c814401880c0050050183c940140c0d019140d40408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 325680818 1250 325679568 325679573
    0x50a06020610050303040b040303030b19150207142b060204091a0907080708040c030206030109050108010507020c3f01090201111207060b1903080d06050d05070b1b0316 74
    0x2140c02c1e5048980690421302c0b040001c072494806032800c0d2030b41801d01040d0440c03494040b5407458003150b4258184220307074600150558a0055a450615043d42502c1c4816242d078401c0c108007043c02c8209400031300301042c1080c14078000203902c00602200d00d2000f030001e0780703454804c00d03038020350400096903950b0007401208071214807003d050a00d05a84807440780c500710310050030b20400100700000b81306807000024200711507038142501860b40200950303201d503100d051141c028407003409000c070a03610381008100442c0c00000c071146a904000c01031010109001c40d051242142100c401403011a80074200d54012a0100d02c0c0d8241c1d060400001400300a03800014460315200800300c22941141c03007a5114518500215100c2c0c80e080301000c40c0d460045800300e070b801911b401c1c490b8002c1d1540000032040000180083c9003a0040110a004d0581c4a004001003401501401402c69000410800110100703501915024003100d14081458100000c81c6080d81e01c403454202200d40c490024008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 325682068 1250 325680818 325680841
    0x90b0708060a080f06070e03070b030f06310f020c0a0f0b010b03010e040b04030516050f1209061b1e0d03150312030e1009050606090711190c050a060206 67
    0x10300c8008024040b0b118646102a101d550190040c004c001c0e0f01f1a0065007902c04100c80c0340201940b00e030390b6075245003c40e0341c4100310708142c5500e4481e0011400560724156074400e42c0384400341040c503000789125001c45150040600c0030418842c95024890040b131220180401040c0c94003456450b0a81d41c010301d48480c840380c0580015094a40c140014802041410070166215900000e0308002d51210f08040c1c0b00d5014150481ea000d1100303040f440304001c804551640d9041a43c4116185002c1007402d14085010b4152002d80000050102510910442040130784c5e0104c01c0050b10b02070361042c0d4500d90012403000344500c942c0d12003680070098507414850010711114900040306030303a0465640039056030040001300700305034441d210340c10038120500c8403179001040f902e0b04100714003180c5041da40340c4004a40e00d030300c00c01b0440006a001409084001032241210010b002c00d004810612040100c03110429a030180c1280310116960302c800000c00084e00541d002400c071841e0800c03120340c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 325683318 1250 325682068 325682089
    0x109080903070e0c0418270b090105010b160c1d071e09121506092a05070f030905270a0603020603010b1e030403030608060c1201060e04090b070806 65
    0x41040c180c040400c600134046406880030b48141300980c90107010024500c07406051031000e0384005a001070140d22181484500b0040c01078030032a10744003250364400700c50b400c95500740f181e20410340017000280e4100c010f010070002070034402c48034032034640d803a0544c2088120a03011121003d8030010280201d03560404180350819911500300c104507840310100400c1100325118038900901c3d147e9a8900b0040300d00c1c0e540c0749401510004020076a90b03401102c01500300b11164001014488114406600d54459111100491501c0f00e901d8600c80d0b5940140e5400381840030f0381013040f441004102d41d41e580d10716041003410704c81c060b12500c40300304250380084000703801c0c00079003883d1510800050300c50000f580d0448189580d815225440300b0401e000c91410342c0140c1d040940c0000c00c11040680552210301511260011600a5a00e0030f090756154414610350041ca1184c180040284511035448122590b20140c030104541000d60741d070340e5158805840b0303180840d01c81c1c020042181003002440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 325684568 1250 325683318 325683329
    0x7050c10050105010e010309080910031a0d0b011e0b030a021306020a20040b04090f050610140409080c0307030314100620071211010e04020c03190e03010908090307 72
    0x81007654500700010380038080404d8007038107042d1504000c2c401c0c00107020541c2c14031f9001a104440041418000900420720f24440e80412181075001e01810b0900d010306002c1103074841280798980c1d080c46181c4142d95055007030303688907900d45000454458440e0002d14007880f5006800340c0c880d040c107105880c0103029608038204647c441e8109502180300d9500e40007030b848100024581d04a03200c80410007420109858a4210b410004103a080001500e441c1030036038000c0e000d40b6590b0300c951514584116061081d004100310000c2c0009841c5000d9002402c8a4445d155107441c240070382c2807032070461b04001019004030380d4030941c0c0c0749800e150603240c661141850f220712800f10306080000d8468010000c82c04040201001c6540310002e0410420014141c80d00700d0720051449031401007901200c03000d1040c005204050200e5079410b10307000340c4480340782810195091400c600c0b800f10a03d2601d07000381c0104000c02c040300d4459202807160813072481c019030741c40381d41751040c5043c1498500d07690f104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 325685818 1250 325684568 325684571
    0x409060f090c17061c0b040501050603030702060a030e1005011508070e010c170d151505041202090402181608060a1208070c030c0f0602010c1707031104080607050c10 73
    0x40d2200b60368030049041c10780c18030350040002c9841d9100401c80444110302c20383d05007000c10241d50103024000001510580c404c00007803016998080c141a22401004402500800c0901560110368007903000481c3e0390540d42c0848800b124410908022384100313921001d00c09081000c06900142e002101e254004110b05040e01001c0703041000900800c0401c80c06414811517100c052a103201030001c030b500d0607d01d03860601180c08019102c80089401e44100300c8800104140000700c1400b880c2501c0486900d10403c908283d4035400b408034602e00100200e13442501400d140500018608000340160008588030003949001640a0070004000e0801c46c82881440c0e000c105403402401c8400c00d280d44118440d8a41055107410400d03040181c000410000c1d5240010401f140c144c50b92408a607440e40c003c1c003c2d1806003030242c540c081c0604910410240407030018010380d029411031814071103982c0c4001e181940c2e5035005401c00d581540e400001881c0018038034100c24080001c1424207030000c50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 325687068 1250 325685818 325685831
    0x40213140103031e0e0a0b0702060403020d03030516020d0f08090c100e130b090a09050f060103050c0901090c021b0121060e0906100501080c070204050f01080106060318020d080f0409060f09 83
    0x40c0000047d119464481000040078411511000d00759801943e024002c2030f40700f8501c1c503014024140c1110216003044001d02da001506200168445c081107150f215180400c58a0504944840004042ea0071070301c82c803424149180c9070b41101d4802400c29070f440a05001d1000104a102e050b01e20122200c1030802490354070540d0380a0419402400b01c0100141c1010329280040c00d0151072000c0c5410350151030000005c3c00300c040341020480d44111240c1d07e2581c0c980316501d00302e420040368640140c6c44144038108659000343c00c1c0102c404c05062480b03202e5212030200e10035076100090040300d130b9201c0b4020085080290001c54020100380041c140d1803800740300004410086e03214890401008102162910014004450440390040d1003840380713140142c0f284030034003420320881201d50710340f410001d555486807042409001c4000705011060f04d40e50200014080710b40d209441d540d10400c0b1a030280042c1c038006200030460020081082403500410220280c070760340c02100c1c56800c00f80b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 325688318 1250 325687068 325687097
    0x6080609030f0f091c0c0e0a110a180b0a110c0109120b0c1306022a010e131401060c060c080f0c030405010b040c03140a0c08040213140103031e 63
    0x5040c2ea0740400350210094940b000354000896208045101c010a0855040601c09206c0c88803c14000d403080c008807103140f91111090b443c00c6035604280088069414401c0600e420322400c0f039106200c0c0e400358084c0c6030a4071540c8000850b80300b000700f08045865085122014101070011116015090803c000306518001861080c1ca01d00c800c0241031154450020305500c4a40c41614500104091000340c07480e1034803070203036a03a0012040b0110200500c410ba58484007a95034818400f00c060b50b0305a000039007842808001030101d104021132075241c10300b2108000502503024020308a03a40e42d0b03c05a0541c1c10000101d40c0d410a0300001c00c04040c04100000792081d040d1070b0030402c48440c10360b40b642d40c0c0c1001c81c010004410300580c003900380b13919900075030391640208801c4c1d044031020320740039280c0382604800c55030100c0c00e0a0112b0484400100507180003030f0b4680c1c40b4841c2001c0400c0f0324115810020312072400341c00403804140381c1800104980d14641d84500d002032a0b0901d5003c404a24 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 325689568 1250 325688318 325688347
    0x5060a051008090106091803025a16090c02030306010e0102030903010f020a030e0303060d03032f071205031512010209090f041b0b07021c14010608060903 68
    0x1c2000c8401c0c8160540802c91280c42580b00600508400c60700f0400701d076482c04440319180c0072100a9005114418100c1824035086d40601c1481c0110010900b40b61520b020300300c05070a0707031400708400840701c94201803c034200180d01e604080880015004803008140d0104d0308141c941c00032504c02e4500071480700c07242e4000080780d4004500b401c01e4501c030154072004034070350b01c03c004106d0380550074030074131410710101c40e009000d13001c0c0740d900d0078410f0781c0c01c0c030000c03564038042203490540c0208030408890109000b07500080c850400c1442100e03100490050111180a510301440304501002444038180070079443c11808a00080c42d0862550a202d41e41c88120151300c140c09104907101090314100b840258115040742c44083c1c001d0165281010104590f80d004840580b0740c5400710401d0416445075441c810190b8007070190090800e1425000c2c4001c08210603000040400344c0c50600c070109812001140314641200e00106146081440e80c504100c00030700080050342c41809101e800f80c095 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 325690818 1250 325689568 325689589
    0x60d060608070c0c06212901050a05030f060609060703121514010f030608011401050a091e05100504020301080d0908010c360b0a0f170105040b011e05070605060a05 72
    0x310301d05800c05a202c0306d004480c001c1180b6900090500e010f062030309909200d18000341205007030151046d800d6038140191441d116031000440000e108000043c0e00d01031942c50341da000340c2c0241445041c084031001040e982c0d4048a001d034007041080024900010781c0340510250060282c520309503051500c441100003c518502c4981070020000640c54110b02c240d110100a02d0750000a0003c2120059005048039080c01100e004164082c0701042404050080320411010106004030441403180c0703000061001418441c0031400c040800903859131580051806040d040c1c015248003d5911000f03403140300c040d884550b6590510a91203291a04468100a40003520301070340701c1081584880140b0039111694607401d1880001c0c0410b04400c000083c0c641c1c60502d03111041d0b1511142800e5410080c081e88007130b460f20030038006004900380741e00005100709060501d0380401c03841400002e42042041e1203030300010300120b4018148802c50003200e403c040c007a40d651802505010208aa0907030307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 325692068 1250 325690818 325690829
    0x9090c05040c02010e031602090f09030406050c070503060103120e0a0b03010b130302040e0309031b03030304150906111305180406020901110d0203070b06300c060d060608070c0c 78
    0x280d03020492850b0b4001e42003150409030110a8070354460010048900c010052801603004010704000030701002c81420141c0d0090322594000d504003860150100d0b19075011500c000c0082c020444c0008446c4c5040220a0103113200320810040ea005081e0014011942e0ba000f0500c40c0603450300030050140e040040343d0546507034007800c0c0c0da500c000c55100c0540840c1c56200075041131501007030b280081e00200107000310680131815200c0b07003066038182d1100241c1b030031010756160f042000440d00240503a00d030040402070010002c560b24003140c856034102c5101882e000201800011207141b8003103840b0071003001d000d044a501c0a520340c0484880e0000d48002c0c401404981d0026195507036070301510b02580036403690030844e1038164070035000940701d411205044035601d090102041c1c091810070703890b480c01890780041d03083d030030000207000c514810b4808200500c0d01821030303e00003c0d01e0301001800303441d8654038082031640c44c1c00801441d101d40100044108069a848040001d4640304600c2c00c640 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 325693318 1250 325692068 325692071
    0x10120f0804090621030c150207080c0309041d430306060f061b08041815120b041b0f0b0408070503010605060706020a1b060b03060603030a02070611030c010905060405010609090c0504 80
    0x91445141d800a109d100400381103c00b010030054602100000101420750045e98184408100c0c15a00554001000c2c42d0011a42003d00800050b02146908081c5603c5018042d1440b4055884402030105120801511810080c609100f03208c0c1c0d0340210030081641c441d004500307508e0072000030141040f074460340c4000000128040140030305103064502038400324071081c0d101190b001644004080f40f1040040d075040e1014000340341810024807140345030300440e101c500e943d00d594505070f50f102e0b80308d0064819012804042401c3d40382d0241003001c0d1020b034007450740e100e051010542c5001035039480030748070b0707030401c2407c0c45a502c5071420f55030819400340f805600d940102d030080d03500001040680a46020b1540040700b4081140c201c14000c900650648490392128003e15480344a00224070015030f000f04e204210b5688107054804981c06c031442079078106102d502c405800d5802c903900035a22030341301c4010312052103000c0c45071500034544d02e20108101c5000b550307401c102200c5442641d100d103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 325694568 1250 325693318 325693343
    0x71d010504150813050f0303240d12020f1b03060108010203070e1c170405040c0e091602070b070b10080c100e06070b010e0709090510120f0804090621030c 68
    0x2041c800403010f421319404005d80c0d00c1c3c4e2640d844070503900c1e00704860400310700754100036081030310410403000310003020060041044200d060326141c96600e442c41d5400700310310440e80401c0310010240465518410319090803000741380f0400400d880c004041c3c2141955910420500c404180c01c0b01411540e5103098130002210350030f001c1c01e100b0090101c140136003420360384070704a4100006c00d00140151807044804225400b6500402c440000329012003a07003007641680407403c042c4a9140d0703405500820300c120307156551152040580c6400404044030211280c1040c410500b020102103000350032a040180034000380440050600412004400c050003015501d003050741e203920302100e100c41d811050b48403d43d40d582c0d0701d00111100c1100d090000903602e9030702060303a00300342c000d00b4016140001010110750501d80c181c01c0704a890002100c10010710041800040c0300500640004d18901c1030004209181200040c0c0b02c0c00e84054008240403600c031408006904030020420003904561181d400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 325695818 1250 325694568 325694581
    0xc01180501140d060902031b18060c010e100e0c1002060609191a03012d151e0509060a0b0706050601020f030f1306030612030c1a071d0105041508 64
    0x2036100710003d03055a0340c00c0003030108244d4002e0300114080c0b41c0601049012211008050b100c80c0a1030219210980d022484030b500c514013440031340b91800d04000000781c2c810b8500045868000510811a41d007030300d0b1071103061846000d1000024055042c0c800d81c041d00226a002526100002c0c0a1441012034501058507091580900c00c89000516070801c40300011000205040d981c880131103210790709200f8600003608409030703a0040080c980383d240596203680d03144000903048075481d804412a0140c0000b406000f03440221014591130a50604014107020500c58225001030015005144401c0100700e10a611412190106c1d0080b00000b840d40390080100e081c020354108c140344521010030020b040c011000300403c90241503e9008000a03950881a42640c5c1c40e0303ca080032217000c0700b59010100f805103103144842403150004103182c2c40a10030000c56204191280c40003d03441d940141070280c20381301c1c80e58a242007400d101d0708240ca0480b002c001ca10690b0080e008100c50040070521 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 325697068 1250 325695818 325695857
    0x301081e01150b0714070501090302150f0703050d05010506040506032a030c040f08061e040c030b010906060e1503070c031101020f090a0605041208030711010e0c030c01180501 77
    0x510030042c500c81e100c0380795202036407000341c1c00003241500e20f00c01440d1103040e10400042c0c03182c00c980703060b101c010700f540c0356400b00460600092200655900c04100c0c8422120f900401012218401d456094981c07a074131003000c3c00c0313500503007141d409070134200828443c66641c9829654044440a00c086076000359012041d000040202d100080305008820300c00c5080c2800050425581040c5048141031759a10510f0758a40341956030442a030f0f010b18248121603903000390710b50302502039100001c46660b282d5548107400780903400014030544d542801e1040c158083c0c1400340c2c10074221040e10403141ca10040c0045444064060000e001050809000300b41c0034404040e00d02860100864031074043e102c1c418004c0c0d01240d1810712034506100d01080711406202070740c05603403078200700c2100c0c0d80156452502d1680003802c00f1040c004c0f100001100c3c280240180c0507009882c0001d030405488500602d80b0740200104040d061042004c1c941d079040064010b508110360003460030030b1076070813000003219 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 325698318 1250 325697068 325697081
    0x60c010b03010609052e0302010804140d0201150b070c0b03091509151b030f060a0305010c0c030f171303050c2a040504120c0203010b06040f03170301081e01 69
    0x3501942407400000785aa0140d008520420a4030000307000e020b00c2850405404441240841c1c006c5500a000c0c000755110710700c01580a0312911010212440d0b20718113031300e401c103658100c00040c1e44410000c00f07200400101c01004007005540b250034654269074094900d1058000c01d850241c01100140c0e070b0120411000210007844d22201e415410003c0f94507869a00d049018030108100102240700d00609003800760076a0102c0d43c80c0390454070342c100501d1a4540c0501595480408400c0c0407020620a218604401c00c680e100c40000142c2841d0282035010a01445801d12181c002011180c40082a029070300207044000c5036025050751505030b0b1316026648282e01d8600c03401110148907140c014180b23400c080345060000801080700c042200b5034100700c400414041604003144425802110003038151440140089211910340340411401d40080c0c0c03050f55000f4012400f003050000c1220380009000805912030301c1c540c1080c160f80d07a6212b5000301c088000c0e151031601c0707051103029848031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 325699568 1250 325698318 325698341
    0x201030c0207320108070f030b010e1017010b180603061903080310090c05041502070302270a02090901051315060903060c021501140d080d0203180d0509060c01 70
    0x40f5000c0c040601c0008440f14005005907281c0012024250720f50700030400c0ea840746a1a0340c030805070b2281c044080f40034010061010781031024402c02038034180e44440ba45000903105580e0382e01102044003116880c0803060740031400140f0b0401244120010300d547c41e801d980343c01e407221542d0391160b10100d88060a4001c03401820f4440c12008020003c1480c003c50007004407100b0814001e0320b64000c541103e04c400c05450216004000402c0304020070308804104000500580d4281a0f4a8001c5290814000100341c14002155100310740c010310904043d40110200c1811800c000d2000040b408900c0180a964401c9080c03160440a8035019084040b242110b100c400020690362180500130105501045804030700f4428403207640741c80014a0b503c030b5080103e6110050b46000448070040144010720f17500011030700018000b1400420040244000e02c0400607500e14203031100c985c00c20360f01034030001c217900030701411780080354404240c4420840403250a81d8940c0124a030034010040a86603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 325700818 1250 325699568 325699589
    0x2180307030602040312021207021309020312030108011404050a06050c042c0708090a080f0c190c0b0a0504060509010c0515040b0a020a0215040302070f030b0a11090d0201030c0207 79
    0x200410401c1e03005881160304c00c2c1c1701300f44c4185040a0690720740041a00c0c23403840f07010a018101c05803038000c140c10b292982110780003d51030f1481c0c01190400d881d028800180c04400801004020f40074403405080c0609003070345d4030090805903540380d12a086981d01a1805441e14089494082c00d031f001c8400404a4580c600b06807420b480f5101e10304440385002d080785005080020302281d0240f0391261007903030303140041d01c010300d120f17560008640c0008000c10502201805041d140e104100203100d80200004521004a001860103041d11100b03900220423101081c005a9501034100e81542c041e91450f081c403075111545480102c0d0400a10034001c0c0280c8292039078a0110086409181d000d1030003000205183d40d9441c14100a1313109400c16040107902600e00300300c0d200e440e5440e02d50010301c688161140c1a0f80c80142850b01065504266a6000c2c20300610900e210284654031f060010a581e041c28a40b001d0005005100f200f80040d050540b01c100440755103100303110f118054950717000c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 325702068 1250 325700818 325700833
    0x7170d110a030e0615031c2c1c02060301150e041e06150e0d1506030b091005010e011413020310080106050301020405061605033a0915021803 62
    0x100902400306602e0f103c0e89409020040348013203461800a101c40000500101154400001014003040c0c01d0744d0043e04114480c00f4414202a007048921101110748004608000b0b0140030804807201110100511200d1402c400c40140c9a00f41580c4c110340c4182c041f00107210024100340c904042c3c2d052016803040c6445615404140050030210511000080c00c00030300b038403411a0280d08480718600e00c007080503021042c10038503007400e984440314401d20741c01003032003405544242524426001198218400303010000310540410410001b64110b09051040c5c0d4904226502018418041c0905a1000300044a20364442180c6c00024503440d1604542e2490110303020103440e1407500401d141e5500b050b00004603880c0c14025941555401080c4e1403810425418240703155401000880c0c181c04140454540742d642d404e224000074807012034600e00c004407045090301106207100d40e5140285004946000b140c03405040444038020107000594460040000c4200d40c1c018030b12a40d41840f6608 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 325703318 1250 325702068 325702087
    0x20109060213081b03070b0c01060902040b120c160605090a050a03091703030f1305070305030a031d032d09031603021206010b031b0d02120610030207170d11 69
    0x2241003088a543c0019076421440c040f41c1c5031061400c40254961690021605100f00b03008a0014a50b42d10814000903051f42e803040c8000680c2c0250344280076480340810005504003248481a92144080b13070078510380903540c5081e40416000180140c0941c0e61800044c007045001c202005d00b042d081700440e2032580040c90020201e181c02c0c068185e104150f58400e0403025400001c2e280155050fa03502c40c1640c2e00c100300758000e1400d4817001c2e1001c2c403502c40004045503040c07004240d1082d07a550301041e41d241d8032078850b0440000c03858241095000300140e00361303412051840004d0f1081d446240210800b00d5a145141d40520b0110541c13500580110092000c00d805c06081100e1081c0e4059441c103404001e0140c86003424400d610408204100061592188a0988004d03400040b010350a10f006c0051110823a00b0005900300c0310f01427072091110360301d001c1902c4503100000d860254546113066403815041c0c0082c280b00c10b203c03880071410f9a42800e06401140c1c6180402160341d440d4203c4a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 325704568 1250 325703318 325703347
    0x504030b091b01021906091704080105071b080a0c03030209060a03020711010201050103120e150a020d020f0f030a080603030d05070f1e05030c130b0d0b0111150f04030201090602 78
    0x350902c00c420510340c002945103500101340b0111644448200302d40c0c001742070710780e0000340401c2d00c0100c40a08c4422001044081c80b030740500003400b82d0301e00014480c6000c20014110408030702038440c111424000440004244008507806551286807044214030039160a5000c0d004912140b40d0007039005c56034084507641540645401802140d04854081c0e10f24016802c0391400c0c00003610407134201000040796400344400c0c144280029050030900810036141841d1782d04400100c0006800007815900e000354104018490a41034002400350041c0d11800c0342c0d030320320030071010360306000d20440050890340e010b00548807000c2482106000518210100419150b60050708202040d0912820140b003c6100466280c5910503200c03149561581c021003801d581280c00d102c45061094900418a250403201a2000c51000c1c040815400000c1d00090a4211841c4144026070711081581011500c1041419001040c01080d00441d4440b0300b41240900b48201c0003815842c0001140701a082d0907 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 325705818 1250 325704568 325704583
    0x2304090212060406050a151214090c010215060d050109120203030426030a09080c0109080c15060a1221050909010522051e011203020706111009030504030b09 69
    0x128000c407489a5200c4003084100c400c41d006803074100c241c5134414007003c007041205000350a200d08010503011400240142901e400f2516032807444603090522200103001c00201104000034006031800709140c0210307030300101c001030840e841140c1035001d04007800029800705a647d5003003c0c00300301d52568084080d40d69031081c0ea0441e1198801c5540301d072442458003081d0344101c0c031201d03414695102e0900040181110f040700ba01d036071000300035002c2044001d00c141400c0510074500aa2030700012481503040100da00c42014031402c1500410201d5a250390505c000d49002004641114406051030440091036421100c012002000401103280c0c0040261007603860443d02c19149a80701c0d0140454480c800003601000410f40311359104285058000c00d5005040303000900c42c03410303a5812540124002e030710076000416142003c1042c9581801540d0142c0500c0c1080240d901d00f0212017923460b1a036801c080300f450340d19a402001c062049040ba8011074201d0305020980c200605140c0e110280b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 325707068 1250 325705818 325705837
    0x305061c230d020c0f1c0b060f030d0e15040816080c060702030a0b0405190308090f1203070f031d0c040e0615090c09030f10050c04051023040902 64
    0x40011800520384001005180480103a02400c004000070003032060050044410b15400744890a030300c0d21000c00e801b0804041c82c05544480740500303201c82880b022130301028060b802a003000380112042504040c45118401040e00d8060301c24110b612214100e0180c3d0b0825a41c1d0f0080d40500b00c0300000310150401034601407070070380340c2402ca0380042250f1441078030002505a002245403501107240c00c0c408a90050051050300c2e100c500031390a945c1e1024806170304402041ca080184440c0943c02c02c000c804030700f40440141080e520743c000309a02030000800c120108880c18138200c1100e442600b1000c1030034061070f68503c0000064902c280c84000b2205403501861501041c00010b440008140c0e01075281010f001031180524024444440001070140480b400c04000b1480c0d10b0310200301aa03410b101d01c50107050314030081c0b45041c05840015100d802000c0050001344029501d01c50f81404006007030401d0b169401804049107030b1700d0f0748440d007041660340201d400900100c03030ba0003e0210341d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 325708318 1250 325707068 325707113
    0x7020909070f0e07090620060c040905010f1202100306080a1a070f1b111503040b010e0c18041418010e010203090c04020703120f0b0901050f0904030305061c 69
    0x640f1035500c9442281e04070b075400300061411200700407841c0103401c00c00c5180400318403012041d5044080ca442d106090701c400565040c0080c3c20040d0207c28819180585842004281080d01d010000d4100c5035801a0180c4101c058100c0c3c0418240a41c0c081c00084c80c484041e64035904d0700781004514120442c2983c82c0c420070f402d0001d65598031500b220029107040b40c941d100301000b101414810078030121011510a150507204081c25030fa035480741b140c13040f83c2c1941c260b903925081c035058019102c10780c00ba44032244010103002141400307806482407156124020b02850b425000001d015042111965880e020201c0030701c00c60941c3c11140780440c1d07511314000c0c02a508080b240030308070701c002c883c0303000325401140004820b45001d400415140b802480c040483c401d401c01c04204848041e0810520030b552090f5480c0c2e2410b054401e20f0041038111501c2d0956500380e8081803104000030402410580d032a400620960754400444d01103200c80a40410701058074034080c0d401a807141511202917 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 325709568 1250 325708318 325708349
    0x9010c0c0e041e030807050904060e10030c060c110103020f072901060c02090610030e06131a0c07060e010e03070501050109050c03100e0a09021002240105180a020702090907 76
    0xf00907804102d048640c15542c140c40766035050401c6038541c1000c90417581c401c0d16108001120307030b203441c1c065004604405e40c02006918510301505603d00507400f41007404818800c0c900483e107150b2001d0460344080c200036075079190118408440c1c0c42182001024044102044451120464441d070303040400701e04011031a03600c44800362031f4002c0c1d00340d00a5010b544100000c0c0d140c240740d04011018011400d010500740c46411041e418100c0440b420300400c00281e28290038005203800000012209d4107501c0400d00708079003020300300e210760080509100c2d1202040c8098013004d41c41076010900d0b100a8035203c2c6400e2138280e01030b080a11484ca003050034200820329175500107080704d00404004141c1d40a0610b00320a00303100c400f0080c0f50044c081d550b4582540540c441708070803000004c0310750107003059841c40722010200c80788808820405c2c9160500600403a201c171191002e0648184450707070202c0d40d4030078901000c0e03c50148025088a000400c0c0300404200062403070a941c0d004601c203150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 325710818 1250 325709568 325709603
    0x216050415210218040b0c130b070314040f0801150501050a0f140a08160f0e040f0906020403080a17061305070219080903071707050609010c0c0e04 65
    0x260740c103190031081d190703100e68002c10440c40040141d040d04a07103000c030b51031200c0554000505800c00001c1c400c0103044890200000c01851446099000d01040304250034001c1071110055600640e0082003884100014a4070526026450b002c0910047d008810354035920303592450b0082c2d4084c031440c00c0031740c00c00d10154051040e5440070341c00e440040c2e40700e0b03041c00c66507003048410740300e1001000c05004035041d4414045100500400040005031a0011641050aa01d4071818640403201c0c040003490801681050b41c00803c5c03000f403100440340480c0035192100428002d00c54020020503249c40041d000080050745009440e6040640d1070359075180c01984000c0c41d0107503003291203a602040514444183c941682d100d160048181d1045445510052a564004000320300c0c0a030303641c06020906d000d4a00c3d042280c10007420fa4401015014a80c0d2030415a680740c01c0d00a051041da404106040aa4401c490401000307402c10b00790b40000e40d0300d000b1a80800c200303031070545101805070b108415 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 325712068 1250 325710818 325710821
    0x8010e07050a0c062904111e0706060303020606120f10020d0b030102071b08060415050406180b0402120c0102033a0507020105070503010305060f181b13050405030d0c030207060c02160504 82
    0x10240c17000c013085243c4580c2e00c803003c1d9101000514442c3c00401803041c80040350b60f600c0bd10780514800c3e0002d1010342060800c00a90020380007038000c441c0d1240b020496204004034280f501c4508007003000d07031150702001c40d04000d0495241e103550550b2022443d50241f219640c1542d0010440c40003110540b0b450b03030a03641d02c58008035009080b2206919803020014525804654000d0050700c0008011f0001c0881c0c519400b403011069070308255800610080d03203401100900e00c41c140030f0050942c0e044c500c001079100e00039800c481d49034443c410200010080102038602c072a62040c0c1581d00c100d040303110044000c000c25100350b0019860603002a001602600c00c807810f0b65009001000726640351030304800714a20007064411041691244010b400d001000546540c80040d65055180c0c6100d005024420f00307441d0040c1a2030342800c040c000410000300854038142d080320004680c0080c0030708180c0103403144103030041105180c48070380500142d011038403648110081340c0d005901030b0388408200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 325713318 1250 325712068 325712081
    0x2a0203030f16140f091c050607050a0c03031a100207090c020a0c050402031f1403060f04120c0503070b010b0d0525050a0306120501020a0f08010e07050a0c062904 71
    0x1090f401860092000b10481c040c040390102c0701102890424084003049805425845050400c0795200f9107400f007010038409964894400d240c4107041c40002c0700010000d10100e54050705060781e40c0c091308101c40d58515a81518940503040c4403201400340b070000d6840030030b0f00c5040d40482c9410508030ad45480400c200074150b4114503601e400d107060008120095001030b1461501e822101017159051030000c10300001411b01407107004200001c2801c1c182051001800e07240700302e0101f01040000f500400d0800008030f5581f4100f4540d80c01032801a00d5841b821402421010510000042d0b010780040141380b1581050b9050005440d8041c0d841c3c1910115010301080700c1c012441e40c04007178400d9010b0700c20354003145008120035589108140072030306050410740b01c5035000101a282c017608031010290822152900401c130750700d840e11500840b0000351024042000000785d40d00054441c610308851503410141c00c121130030034803d5140c100549466550515400e0b4441c0c804070f45880d22425 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 325714568 1250 325713318 325713361
    0x15040f0c0e1008060607030f02030c0609010e1b24040803070f0606050108040309210c1401180803041203110f0604050f070f1406070b07030207151a042a0203030f 71
    0x240d0500240c4e91f0151010340d45454400c046100030b10a81c0031003001040003a00451140000094114030b6441140c20140202c0f021028000f26204103030f5140c8542d5a0f9071400741c2c49032140c2a040b00c0d111003c0c1404e10699000c2c10280c400401d100c8140403820900d42d082c1031080104008507582c41d401520700c1402120045c02040c180300080110050002151078142e8005a101c074410a031555645500d44e00b5070070044401c44e860012400351358000400d1240c0036407489820017640d241000ea15540d11550094041d014814501e180405016169650b04107960100791400c9001401c041561917008236410360300c6100c0c21030000d8100303001040c440192440300400e04009401c000d40325034903140404006401134020407032500030502c0101c219000340d059943c0942d8a11070b0382000030b1211030001c2c451140510300740b0312007034402d801c92803104a10001e4402041850f508015480e10400d420a108400402540d100304020341c040700070b40c803070280e1200c155040d89a000e2989910345544524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 325715818 1250 325714568 325714579
    0x1032405042027271903050d06030f060f050907170712050706031109105307020a02060c1c032306010815040f0c0e100806 54
    0x241405000c0114101c440e81c201400c480d041102624400040200c51010540a040300405004030680c0320790009550a4000515040c0703000c800c4c0c0311a4482200341c10b200c0e1562500c403100c104060003201074a030161130030201009120303a28100b0703a544051441c2d0407152180341540103417030381c6040c2c41558000c1461000404d252410080390080d910314502c0c2e10822403045540001e00043c0c05040e20510901c142c02070100b03249000c601030144c5080f02d80c48100600240070b0250f5646031403207075403514069440d0003100706411070030309071603002071440080c03841d169455451030386980d0400c03800f0760b00203181d081d942074040b071200c0181d1b07504203540709401a00101000005442e00f01c02400d100c020030b00c2510403c21028204808580a480039400480d448a080341c1400d010008540c41c000303d030300404525443c2800000f00402c01c010040b810807101003800300382a07103ca03403281c060444e20007070400600150020107040e140031110564454180c00440e11016807080c4105801520003804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 325717068 1250 325715818 325715843
    0x40e070311040b010c1203090308090601151b050714100c020f0904080f0d060609290307180f0e22030e040b040c0e030607030c050405060903010b090103240504 70
    0xb0800500111082c45041000c040b03502e00104807006050740300707044c0c44c0d200000c40244915025184130001072818400741c0140004100110401001c4501000c80380317071212000b2540714018200185452014001380314200003c120b03000c3d0108801881d5404444214541403524412a9500c40045000703400900300c841120140c148800b040c0d0b0483d1040081c0703410318a01c10034402c1683c1158942201158907140100902030b0821141e002904035940e603485035407146c00e07041e400c9182c8070481e04d4100c60004009080b03284681c030f0f40d0803040c00c42d4808100d1182e071060004401382d400d00130b0701e044014003008030303850000b0540c0304608440c0b2900a00c4030103020362000c0d1050b10000402c25042038581d411000c40b40da961003042050181a01d13180011403050041c9850044001d01d8a428586000c0ea03460780c940d0010141d41c11a40c2c111030701980d0381c400070007107070140403190310450f0010441c400100400080010b43c1341780752880810901d441400d003500100b51001a41c1c0a0091003141e030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 325718318 1250 325717068 325717103
    0x100611030c03041403070b1303030305150d11015a0c0c030b0412030c05090a14031c1112090d03050310080303090102130806010f0b1b010204060509040e0703 69
    0x131407024000600030140d404c0a070baa84c00644060703000c0042c604141d040b01c0d0090040582611900f9000450609900304006580001c504050024440503140705040c41c8081441d0303101d03070658080003207a5401c0e910103003142c940c280000010ac111030001201c4845100d0002d4030101905d00200010303090f0300964100d01401681e2801c201c48050341d59100051020000c50050f40b036940c0580d100f00090b0401141d0000c006080703d558001440030408204280d01703403030b92101c09141c00d0303810070301280d070f560841350780001d140480100165001e200c56070001008160821100c2c070400c0f038103d090700e4110b00020313004d0744503114140c4603035800a85404542d003c24815800b45901904d40741841e0f1038191140d003c00d185400480c1d000c10142c0d000a003071090103001809420041c0300c08ca000703180c654104444800c0381540c0b4001c40624988c003040140c200908201e64180d08642c80008550f2681c540707900a0842d0302020f4900d0081f42440c8000c200b0010004004044075088103031000c2441c400e8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 325719424 1106 325718318 325718339
    0x31211040f0503010f1a130f0e0f0709020705070902070303140f1509040203120304030927050903160303020a020307020316050f010504120f1a100611030c0304 70
    0x1b01845c0401044c401031090000044a411400c1c008801519009108941400b801c282c1821040d40c0201804541402c441d01e001d41510302c0c49848000c920180d114800c00101103600c20002008201056405000c0c01c82c400c3ca004108690604600303151102d00380c6480ba1084140d01c14050000d9401030840304407142070b1442122441c0a4000070348400200c0d10301c03c0c4144001002900300352044901c3c601a0186c107a001070044c444401899890b003007030003181a1185420040341d4201400015210484205088401160800d503000c50103504035220190940c802441011b0050343d040c000307808861401404194454909410410454414070746941808001c2100340003000c4074245180c1455080780505e10864560724208a03141e1110009884004410040c8444000494014421200c09954920591605008081d120710500080e4409030784104030400450144 = true := by decide +kernel

theorem cover : BRFrame.Cov 325539568 325719424 := by
  have h0 := BRFrame.cov_init 325539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 325539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 325539568 ≤ n) (h2 : n < 325719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
