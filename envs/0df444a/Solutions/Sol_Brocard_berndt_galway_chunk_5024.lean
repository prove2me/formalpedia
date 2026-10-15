-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5024
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:29:34.044142+00:00
-- url     : https://prove2.me/submissions/b6149f63-1f19-4ed8-b718-44a8be8e22d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 903417266 ≤ n < 903597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 903418516 1250 903417266 903417269
    0x51b07080a02062203120f0204080a0501110901020d12090204060b1b0705101d0a1202090a022811010504120e030a0206030a020903030f0403060507140930030304110109 74
    0x103e50100d2255028406440c50188013544d81c18107142042c2c40c044403e2002511030001020030161000c18002030071a400200b61400600800c002c000101c141e50f18180d007403080d4014240540d01400614860600c50200520b174652444000a4088466400981903518560000c0001507010075a04505480755801d07061000701d260060801d00e1805011880707800200c0426000c4c0031f070498070075503129030140b034900c1034110040c002c040041e1205000151000300c50811303800b4100380c03c0010340c020b64a2003180e05900c140c8294015400c00c0b00b528014080c4040740b1001006040042c0012031030382400b800d4025031041d00d00d07022804498400516039800082068401d6202108900158903820300310794100c140b1150269a0b0800b480c00704e07280d413040001d894a0705800107400420701205601480c000d0b0010380d1002a102c403800316041c858011500d0032984001c001c3c90301d10389040c402644082040e1002008440c0c8118524541d0460f041214140ea25a001c0c0c143c0f0050f035a8059010030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 903419766 1250 903418516 903418531
    0xc030806030a24020702030111030a0606050a02031602040b03010f050a110f0702120a050a08030106020c0108061e0102100207080415110a0f02030a0b07030c02060c09030a0303051b07080a0206 84
    0x301c108182d00c032190768003420f1448640c04034802407000c090034980d0b011165019000b8000b07000030300c3c0141e201c0d0004d9108a0300e00d003003580b4100d80441c410748190201c1d0707a40050350f80290b040158800c18150792a417102e1040360b02580e94603444d03410b500c0c01e0003490407110f45024001410324100344840d080e54440204110318442c00c02210b810361844a00703607620030760146c0b5250500e9829405140c9041e603040005040c51140380035140c2005140e174000c0d4141d401c1c65090f642552591001520001c0341519078a90260000b045521030010071700c60f01c0381c812414411289400d01c10700510040387e100300c1d41502d00721400907083c04285e0300c442c2e414504080a160401035104100380590701c03046800401031070111006d514405640d0b0800240d05060380040711038bd5541404070025000305101d040d00005405080000f8161682d010241c40440c403018002d04007030a80e5070380441c01090020f22000402204481401400760403001801c400b40c40b9955040c1e56414400b0040c0c9019001012907 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 903421016 1250 903419766 903419773
    0xf0a021e031812121f0806040c0f050907050c0c0406060c05160303081801060308030f060108070206070807120e0d05030f0a0501031a0a0209090f18070e2e03030c03080603 75
    0x150307600020204403018a611304000d10255100c00d44840040c14603000c154100212001011800b40c20205c0d43c14040d03841000f170500d0781550f078621410303c46500d103e1142d001c0c5244000030741c194001c5000b480800a41c400758ac0c906050710000900300c0b0206d410a0001581108503901009010064444070000c8100240031040c6580d0b4005c020010007064030303000c052096409201007509400070703c040d50b0300120064403440d100c400340c6909042114481c0c00543d240700400c0c0140d0000c50040c0c010300d120b039207480700366032450420384641c0d1104001c0d0603010364442e4007903402c1d007051007288800f0000f0740e82c080d81ca0030300540a911045c00603040e00ea1003840c2c10010000661408078505600040e42d02e0501c580c1d40e011075000080c02034085c041d40100b023520410441404c082c00340c2e0720409055440d20015010041d1955903035400d80945203400070800e0201d202ea0501e00781e03d82081101e82070f10071100407102c2001c0e10300890381c1d004802044241503038404040d006945641c0c01001039004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 903422266 1250 903421016 903421033
    0x140301140603030a0c080705070603290d03080717040f11060a120b060d05150301051b03010e0402060412080c1218091504060b070203060a0c02060f0a021e0318 70
    0x3c0d00c0b441621403003424020040704e04410002945d007521800d54105054078403407655028041c0140540d50514071100f2964505151044805100c049072408060300b549e4a041060f41d00341c4a840e00a00382d8014840c151415102d20103103042c655200d00e00c0340c0e14800b241229868465080d20310114864440c4806006800311030350310511448101280101c0420001d0900340416038501c00c1c10341103506141494100a03400d9800c4a412610300410380c001c005613960b0248650304ea0150039150410050704000420556001c500800d8005000802c0c6900e4030740d45211a41c40000e0140d0b08603032039000801e043d00100014400c0d041e1180c10160740b00d1600701c2c2031600703503010010407940c40d10418005c0041a0340700f295003610b030800d00001d0302c10420341e9283c003141140c54001110803486846001c0000e45030071f00e280603070a90048546c005240a440d58004605031203002003007111026801d000440300380c01036481c10704042d006607805035074a05140c43e40001b25100742c00354011070f500c06140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 903423516 1250 903422266 903422269
    0xa0e2e03060f0f0c270506180f060a0507020f0a0902270108010f180b041112010b0702030a0201080703090503130312030501030b07110a050d0203040608011d1b131403011406 76
    0x1c5546089503070660b111011003448585c40811076046c0c100036041b4902140300ca251201503074482907030003400c6802e800c02d58425070400a052107100b0042c4009002032003d02c00504251030100d000d503070000d2101c0d44183c0c540390a507040b6048268200451141071410094064030f407000540c1e050400e291428041d81018036491007040e0b94030a1150501c068400898061a582e1101c1001d20009002b81705e060400d5000014030b07006403001c1003484841000016a03121903a08a540507507000d0050150721109400544402400400400605480f007442030002a020b000401034000400d00042c1c0003821030500000808a442c4030303c00740352134100140041400c40064a0b0700440d140781c440710b80c03040d5041e8a410300b50b0007c4000c1c46841039004501d84290044051b0064800ba56965042c1e030b03988200c4180c00c02200d01803601049000001304142c004589900030080706181c200a180030741c1c204214601d070420754009009500940c0f9621020300e003c1c06141200e04051024510302d080010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 903424766 1250 903423516 903423527
    0xc1202030903060c280906020106060207080c150d0f06060807031514060f07050102032203090603020901270e15011709010e07090203150a0e2e03060f0f0c 68
    0x203004604d0749101086a821200c04c90812900194070540001240b59800c00c0241c9112030500501001d5402c00e0008181c1a20000d1988125000c1d080100f8407902e2040901802203400d181110703000d00700f0440e00790006001c5c0200c0940d1004203500040c41890320000910124014000301e041500388649032034a103c550fa80c81080e41c0139200c1c006126003a030b80018031280b04034200880001c102260007414800c0660146208844998550010001c3e22a002030356900c0c1c20001000720b40d501c1418400a40700c2c0d03000d00202d4106060082c0b40e090f1224040600c14184a15680034032030003107080c46402c981c10380030754002c144403a030030910200200c00681706214144201611202d881e0020b00c02081c01d401000c2a111540c0a640b00715031100c0c9000c0c06940101c4050002c64040402041e45040500780c103000c541c403201e010401c98480b40412091440f46a00780307009000550456035032100a250b00e400118416a400200d02c0c10221824059071405c0b200c1e01c1d8501d180c0b22800c0c043c1034219 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 903426016 1250 903424766 903424771
    0x911030a0c032d1b02060106080a0b040615180f1a0f0412113f03040f0f08010506010f0c0f0f0b01031b0b04150903120c120203090306 59
    0x1400400c14030301c01d5a0440080c190034149464900c0d00640d4a10031221103100042140038904041c0a403030790750010f0340c4134940e4007070403e030051b8446801004400e102d445210b8104650072004640590030200080c2a58080d4112000c0d00a458071410000d542024820348400c0310050204d080ea440e000c09506921104d2050703082d48078003240d29042445843c0300320307a418000b024405032183e403200c9082407403005060b000c44914101c420341d51458078000800780d540f113000a070082d0f8022a00e02c00c00070b020f1a480b002018981e001500f05009070400e00107080070300300c0c0c00e0f20f403680c031840d141420300034011b07a602c4202142d1400c0c0a106450b640925480c2c003441d80d82c00d04404410443c035140328140076000000d40071aa200102008001e10070710101d0480f4007a181c2007a07090441d03480030b205013016109508002d0001c208c1080552256205090f051440d4145031042968940b500c246c203a06007480200050703241818201000748030442040300d013010b8801503091001c2c0e100801d0303485602 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 903427266 1250 903426016 903426031
    0x3070219150902010c1a241c140a05030d0b060c06131b15080a05060a1403070902030109090c0e01080304031b051c030e030a050a020d030e030a080406030501091103 72
    0x81e40c0882c0e040d0790080c000411000c0d440301074040c070185c620b8180c0e2076480c4259580c01242d60200046041006003081c112260280201b190103609003060700e801c144240c028007211003070301a940d4010704010920100724151700400241d541c07910034000d050f00303d4240c191524030071401884018a041e03000964103511411202081455003010301b06244680c071080402d80b000204a20042182244640450080e441d19100c0e44a15210341540c4d2044d64001c4882e00d8109940a00801410f141c00741881c641200c06010b80d00a2616008804203076803007600615209034451102c01c08200c140300144e0020460b6801400b81541000e54084d282d100701c0c40050001900d200b4440030703c84c4c18200c00030050000802a01a800038a030084079030b0008407000343d000c9a10244150744c40d0400ac260030312a030303a0000203000f04030460f07404c01a044456550a9080203103190042d10b45881c10800e10782e000b80a9030b4851348580c6440002426039605030400c114041c246030407404004044410369400140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 903428516 1250 903427266 903427271
    0x1e061f0c03020c0a0e0f151908061e07210e0c1003060612051902030f1509010f030b0a02090405010e0406110406090b0901211d01021e03100315020307021915 69
    0x1c9100840b070008a4013484292311503185001c008800074102c440000311620f480c10341e10169948507410880c401510700300c5038034040620009a8031807046162060b0b403c5050001c084050b043c40a48086605403407100318154030140404880f8031b01131407a544421b183d8902440411300f4103000a000082102041c0040b070b49078404200900e20056200444000c00c840c21034481c5031082200c0c031503040c103940c0783c1a2120f40b0041c0451909105c04c00368140c4e001a40c0a609591031075580c8100c6200050010701244e500380640009a0356601036076000703003e41c0c803905100d1b041500b44202180c2400c8400d01c1c40c07540c2084100b22403a0040c9000e8200c480c4007091507142d075030200050702d000101044040c0042c001d08005600d608442c1d00c4003c480c13140c04110000c803036614070725900300d210302c0b4101d6401209004144851801030002140c1c4160000109900e5a41e41d40d00c8202085100043e070441075000b004002445504010b00c5003010b400602c00c150845088d10350440020764241c2a0310401d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 903429766 1250 903428516 903428521
    0x11040812190f110d050d051605040b070303090206030109060e0702160b090d12051e03090709110c060106020604030e0d1101260103060e070e1e061f0c03020c0a0e0f 72
    0x14003500d40d4140f03400e540000c1c1c92a400c1002401841e03940311003481540b0b42d140c50013092034010741d4000c850024446803a0240380030300b42404884030303401030300781281015240c40c0003400580342c0300050b41c001c1c60300c0d440101d1001c0c01c1400c400350914000f4030481c1154012811042c0941c3c000e1000000c54074080d0f8559910524400402c01c407612070000030704650a03950750503103001c1d88000108245540070110038003002401e603d00761035206c1611303000c0741d6070301c5150140030800b80b07917001e06458181000b10382e2030400d071038120908010090b40058050b0b00810100000d0541140d0324441c02c40044450004000040c1d42e80c10810034a11080f80c100318485145211000b9010100d1050848011f50b5800540e1f60f46031201c00303041040008105070094a03070010f0440c1012003042d02812000c8003640116060701c540390310205000303182542c045107061112007110003604241c00e1183c1ca503078417824800c0990030013925241c05090242e0107144441802c200c0310b102c401100e9000212400350300c0c0ca64 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 903431016 1250 903429766 903429797
    0x40b040f020607050f0d110c0424030f0201091202090a0c09091503020a1a03130303141f05030d0c020613052806020607120c121104081219 61
    0x203a0390000300940240000546406010001a0300342c48a101d0100722541e030381c5140421a08884258072260599010480c000c8940c41c15410002c1c81d001080d0205d00070b001022030b1b121040380f1503030007515010003c916000039175a10408007005003409072280507243e070a42d0f003c282d411000611400c10345540e1641060442e1081c01c1880c01803400c290b090080c000325581003004040b02c1e102c101d10607101d51000180014040c007413183c02003032048003142190b031040c511108523426000c08504140d43c80141c404c07100450f25806028407010404800f100740900c209658500c12900803d02ca030f03000c0f80b00f01500e80e5000081c006200d0b410b4071426150095000140050140b5400840d80703ca43e2080c003951080365005c02c010b000400240c0100911740d240000e0f0f840303a1060300c281c4009803000d00c1c20082101c40b07401c071f40400320b202d1030000c110003503250b6075108444400149680c00d8000007410821004104201c008a951030b01c0700034505101d40c00c24100c1061008400801e00c5040b50751342646 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 903432266 1250 903431016 903431033
    0x90812101a120604060f03120903050d090603180206030a0b040b04020703030e1c090501030c050c071e09151202010215130b070513090b2806021203040b040b04 70
    0x1015001c1805096401040480525070482200482c6180144000a82501d003030b005070003c0341c5605201e540c4143c150b840d201030031413050310720209012076541d0000002d00c0400c2050100440d660f59140344504040d1b0045c1602c0201c1e42600c8003a50481e60400503903941d10032650460445840000d4104024010070058585d0681d03481d4802d02c04900301c000c0c0354058102d6020b0241075400e8580d051038846542000d05081c500c0c0200141030340704280410750095000c0c002c25001c5080290402d0f910001d030f14580702c02508500c2101640780030002c50904030381105030240c40b40c62414000142421a6140405030a00c9002e070b1000034801306000f0340e4004d00403000c8100700700c035800780ca52400d8603844401e4000c1d43c0e0203e44212400001070109445482a260340e500d213040010482841e10a80402030091a081c10354080c421a06032180d1080c1c10790b2070070707000c03c24501c41200d01c0c1c41d01d13901038240080c10358a507120200400810000a049414841d407082d0b01c41071010b403940352403c010b0607 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 903433516 1250 903432266 903432269
    0x2030f221505041a010b0901030207060905010e0c09160c0f0201030908030f270c0103090507081005040c0603020304170a03021b010f0515100311160305180409081210 73
    0x144206828a440815000c2c0c101c1ea1040c2e0066814816010b04448000703078001c024072440b4070390036003032200c0c0c02a50300c6a00182401409898007051104250315217500315802e01e81d51008a501c0301a0342c01d280e0408100c0980d00411210140a42d141e0f4400c014142e2180020000c10b06c507c04040d203821a8041d502c400d070303002d030407030704503a16403500800390060644142d41200c01c1c1394042c84602c14885140ca4244801c4a0b1900074184076034410340150301800341420112168003480001080c041000c00c00904e140c42112800f0446003028281101c2110098118604150040003080003181344818400c074031582c5030b1522592030038135003411002805000c1108101051140d040e1411400c1500251914159050204841d4a401c002c1c128040c0c440d40b085071f0444448818030748064000d50021550804d03050801d45000c030240555001da9610076012404200f01040340881003d8400640c0d00c1e200b000c2e5002c001000864846c1101401000c0d0021905080200000c02c0c1204d2244103e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 903434766 1250 903433516 903433523
    0xd020d0812010f0612050705161406071206080a05060c0f040b0316021504020a0b0a2307140706050f090609120706030f09020a0b072904140102030f22 66
    0x9940d5850f5601d81c45149000d00c50480020b0300b11681c02c101055910409000d4039140c0c468901e03110034507000b81c02c50400e40b60141c90321083c0d04450f154401c801d0195911030402e13503440d1003266482c13001090894110340c0200115500c4031050000080c00000c003150450700d18100b544e150f1051100790314039446203421a1004040120a110240c443c059885003a030382c0036000c2c0c0700c8400b00c9031001f04114404850203540a42c6047c1c8c100040701d040d000030404010280b504a00f4603002450b12041900c9846100da00d481c40091300d0070504c801100c8880c480038041005d81400f41c0780042c000e0042c020780c251816015800106811107640e903100b2140c1d03054000d0108120080038040703a41d11000d841c40740201003410800e0740740d00342c10f0510034900748035401002014100d0038000d028819800a65040708c1038501b02071040803071a40da40a010540d01025008002841c26140464a40040068040c0c040c0c0c018814010782c4184249001d0340818004034000441d050020040b00400340320703c019 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 903436016 1250 903434766 903434797
    0x2031c200c210c1f0f021e0a02030f120a0501120b04121e0903121107120507050603040f0204110c03030609100b2802070308030103080715061706150d020d08 69
    0x3c1030740c18120400c0c1c440c4c00444010801030070000e84401c500b41d100380c1800601c42c290b0303000e1246007001c625019201e00c1401c0d1048a0034072040c8201800749510001458078800d00480c00c201021910b4003c00d4054003004600e406502c905694020101c4005440201030047c0803000b2030030355110364244004500355505401c5203d00081010703200b410707103010507140d40c04214401e0300614010b41001c2c10346101d80c0f00410045203404161041203062680c100c415001e0154001400d983e0b0001640c0680d001c1d08040c80c8210705032040001700c440e807582580c803481080c0203241540101106803940b1a01c140e038207283c0c1d5a1805068080000c03641c006122650b80440c80c2c02d00d041e00c83c10100c041402c2c103d1006100088540c0a80e502e200d248002022201c04100510004011001505140d84200084403158031111038980c00d5801540101090780762803400c01c3c2c4845400c014041e0804c0f1640041064002058003060740070a200402138001e9030710601020130030134650300f120110a00c4c054030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 903437266 1250 903436016 903436033
    0x12160602030c0d05060405100314011824090804090e07050907020106060e0f030d120b0a2709020306060f19090b10090b1902031c200c210c 61
    0x2c42c0d4407500220481c9444a24020010301281800c1c8035550084a240d542180000e03d944c0c0d03040f200100070024081d003552a001c000c180070001a100740c2c2d480c0c1c81031440c406650034400c0703282c8880d0019043d0b007895a080132861000f041c602001c840540c0c1c0c0d01c9601003002d405501440d480d0200c5503200f61340108224080020072607066000d401034078015a02c9500d07801d00c030b200300807080c000324a60560680200b015400054018100e12003120b008070320200302100c4000000d0054403190340800c2e11140c801c8040f803203088480c480b019050018a1041148402540101c1c0e81c5220081c0700a0107003403e184001c0700c0e42e45007503507000304040c03150261103402c1d2500741c1703d00601002d002e400d000382440f080c469029401407170482c003501c01c03d10740c0c3c2d82440d401980089030309a031101c010701940810044034015034001c010440007010311b41c0010410910415004620012a5510205020060114403420786000c91400b4211000b10388042240c0d4007428604a00c0c03080d004612000e2050050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 903438516 1250 903437266 903437281
    0x3060e01060c1b09050a0b04060b09010e03070e010801021308060702070303080721020910020a03020309091003050a061d03120606070c12030c2d020d2603180a03021216060203 77
    0x1052060100769024407c3c580288203001c240d519034020320343c0d03409051126203c1940f04450401c030b0b41c0401021514656503904c40050101001e0b0010403803071350005807111020500c181c8a4005040000c02046245071660009443da016400014200852140400c401600c21400c002c2160104415a0a6000f9994680000f5030142c4c12190281e020440c190740b055001182d481c603840e0301a0041e500d020038440c200045c401d00104030301802c003210000400440c1040000654903803048000207051030510a1642506640811020460340104607001c1a09900d1048a03000981505e0381900c6903520b14201c44580381c180c011000c41c501c00d08603007052540c818070286400340284201660056000e01d1075191000703080c08000180c4ca007070104001402c01184403600c141c040c5509511020380c40040c0c451003540352a14148001010052007501c10100c8014560142c0300d0004150020050390041c2d294003c84a070202413400200d520310140300e202000754162036000c1c070115660315202c00e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 903439766 1250 903438516 903438521
    0x60f04031407050d060c030f0c020c0114030601120f1b020d08010501030204030b01061b050613030e0901060206011e09142211040e07030515041203060e01060c1b09 72
    0x8400d4440800031007104000000100d82c07481030b604090f0142055420710b49921002d071520241c4d04042590383c909000c1e00c8141803207000111141a40907120018049000414981600c40549100c0c901007042c40f5080e03811000710504090350000100d5a440d410742a00000c0c0300a0394091981c00103100c4074108aa0302103030309880c08105131a5180e0360b9803200011070403800307030b170000405803403800300184a0745020f0702d40d4106046901e0b0302107403420502d0741da2900304013060741c0c03200308140302d40c02e00c82c2090340041e40c001c1414800d4031001980d600d001d000030f6540d071040c443d0490020201d200c1c003660854081d400d030003500c4080d50900041d500d041142c0d205010448400c1812402074100502c03550280314038104407078011560b40480030341c10040100500c0c626014241500c501d401c00000180c050203400756160010240003c00c0c5400d0030b1001704401c0b004a03030001c040c509602404400120244103055a0480c03800b0312f48000d40f4548890840302d0300d242d80046910904001440340290f4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 903441016 1250 903439766 903439769
    0x20604030602120702070b041206091403030a0c03020f39100612025b0801121e140c0a050f0d140703150c1706031e0c060f04 55
    0x43c905419642d400e03000c9032504103c0c01114810002080704000da034240c200c8101d1028040c030000124003c01d0f40c1c0718175031102d07044c9038807449410100422000c221140f01d14440d459442c2010b502d00180c0e00310031a024810341c1c260040e85440e4000c82c42d8001105404000c90400030f00346036414441c80c0c980b4650750443c008019000e5170400c040032911406280e2445d0010390701a0a14400d841e403040d17500c182d00d02040f02e082c0d04000340c442c000360758401c0d0f000284c101c10100d00b07410038880554080802ca5181e600404003070000c01001000400360300d030382c9201300ba5004803480301000d082003141d640070234407017101601c000203401e84090100c10100c2c450040c04400c80d1340d0441541d4401c24480070846014040b588205444204004106140101c20035640c104050711307041522507913002e24071a0480c0d2404240c0380d44002000d10143c0100d40100c030141381d110481c0143c40c09400090b0303503103100380122240c910b00d16a0b03156502420401d8240781840100300d0364075076905081d01c02003604a07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 903442266 1250 903441016 903441037
    0x3020d291f060f08040b0a0b0a06090806010b070c030303090321141807120507081c031503020d08070309051509150c0705010507050309041a1207050328020604030602 73
    0x9840000d02e14011401501e22407101d894001c800ea54540351602803d4004211080b401c0c1c442405400e60764a14601d400075015a8441151035400c00000926100c8140c00900703070040200540070102e819201c4102c226070381813078003041c0426180350031a81010f54441100490540f00c0007030f440804180c10421000a80415001081d1703554a17904482e5000c00d820740d00a0b03040380a0501c81c03080c0b4104120030150040049039507d5907120419460060601c03500211205126030303100c10583c2c140a84014000003904079403020382140c00081c0c5c4626034810042038420005440410140a408140001c0100408040c50800c030344001a03502c0e44040c0307a042c0b18034407081081d8072070406d9100340e5840703521283c01042c60341c1c103100054809034000d00041e40c851109020000c09a03450313019040004008141c4d01002c0130103442448a1203002004c40d0348142c0101d1030900c41034600085006992994002e000c4a402200c18a1500400c0310303140a50054000036012042c8180fa400802030b5442 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 903443516 1250 903442266 903442321
    0x4030b0103060c1d040e07080a080a1b030e0405041a0907140a030b010b03280b010f020d12110702090103060e060f0c030420090412020705060403020d29 67
    0x71080e81111107138210903045508501d8000d40c0d01d000d0810350b02488100034a001110700d1a5111428a490044800001ca50780301001400d880c0d566070100a50a206100b02242c180380b0000d81d4020745500302d001c81c500d000301d69480006040c008040503000c41501408090b032040c0c180010416100d09140c00780e01800350352989801c6060404090003422aa00702020340e185908000c020411503002412000e800c0108000384002c1c100f045102401158203250f0004094070711100141505047c480d48000f0b40d0400d41841100c1038100800c2c4d0f1440c0180714000800c4002005804074900172014003940084001002108104403a0301031180d020000c0b00311081a0f0314080f079614452000c0f10020300001d000c0c80882c0c00920b1003200d400f044100007080d0791006014401040e900d080442c0c00380c03100108460650446601072003206d014120581e119441c1c40d04503000304618103030a087c0280325135030f41140c0c0100713810315007030040190107510100b4400b42003a070149180000c007070764030394043d06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 903444766 1250 903443516 903443531
    0x50601050111100506030c0324060d1e0204020d020a030504060501090608150c090d110a171e01020f13080606030c1005031e0a1409030c03040302150f04030b010306 72
    0x10b01858403010080200c00007058038040100d0f140c0c001e0701029003240d815115032072103010725a40c02d000545044042038009a812000d007401441e5030394001e403034070b402091228030383e0010a03200e150440c5c5201c03c507010801c40134481d1000c9070091280440a800c904d102040c400c007581e40c9504058001d60240c1e400340400e136200d94404048440501c03850340c01da4050408001144041d24269512802e00c4984608242e05040821104000090304440c01480403035400e94610300030950718054811303800c0d001061843c0c07502884c0d0300c2000d1100c01113401131403a019042030300250100c5480549010703013161506060301d85200c1402443c015900c6600a03017001a0300340c10002108480b1101c0207012150703040302000280c5460740064005c6901200d550b00700120b00302e200990b1800f440002c2c90010302d00108060300110340d800545075a48603001003100704c800c00d4000064400782c0e82c04492022050540400c1c450240c480c40402400054010500000344240084014100c038081c2e1700c180950b8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 903446016 1250 903444766 903444769
    0x905060a0e2806080a02360718030c05060f040911190302130303120b0d0503090118420f08070309031e0c0209040c1403070e0c0f070f05070305060105 66
    0x180e9060040e40c100c0e610030001000989400b07c510328400460707600d080c3c050407002e1003156562040e011030304200080e41c0f061042240d8811901042c2d02d034541060349542e0b00319620122024494425a44a080c0104a40001c203007864129401001c40003c104420340e00f2300051020b03070700845030390440d000320300e40100400ca00074002c50391512071000500b0050303400c41d43d0540f00e8001c2d450129190950b1050304c1080340e2280f007610700c4441d004400a503152010100010a0314171a0104201c01403080c1c2000c02a2621301702d08005150021101ca0107102d41ca40d1400070014003601c2c02d0480041ca00c10180d0340a070f00b104040201202c207548005060f520344070183e066800441009000a0307145641c45402258a190300884070098900200f54a034a900001c141e5030317060714140c0701c4200a40c400c000000d2980000e4038100425800b0301503035854040c0c0074461080080010320040e01c0019404000b503039080448480741e6110b1004030091100e0708219940e902c490000325001e100e04400410745 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 903447266 1250 903446016 903446021
    0x31103180d140d02030c0d0c090911130306090201020309030a080c0d0f0206062809022503080703020a02240a05010803130302040b0a05090f19150905060a0e28 70
    0x6182640d1894180c044041d80f009500c020b1400644504c240030040000314240910010f98099503903000d442c6051190b4801210025402c40e2041941000501c01039600b0074440b0003140e801c041c00141034409400180d00710f1140440e1658140030f5000c403403082003284000f03404008083d808503034101e0a2148151440100f000200016a0192000454a00d00340c141400140c00070320741080041c10101e011200b00d1090307000741030004d4020615041816600b44c00b080c0100102c44102ca0714072144d10060800400500400c0c1055000241c0084441c001c000001000041030004d044815084c143d207070301d40d0780c10f0300c50300001d5042c880000345425000003924814a5110845103140c0c0c515800c01c80207120f07075140182c1040400c8000900f503607504c0720442c4140004107015003e442c01000c000f56031401d0610420718146421070107088000c6080410301039803070501c000100c603241c2c03c0015100c54515401800040e2240c8204070404041019000502e00d0103401034601d00c510300d00c01402d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 903448516 1250 903447266 903447287
    0xc040b0d12020a0312061a030910050c04030302100504030e06031b04030b0f0a0614060a0306090f270f02040b040b04150611030906370c11041b0f031103180d 69
    0x807200c07d10b9101c0030842886000468000256108031900c940404c40e102e010703188200c0314005410303804603080042c150140140000c40d900a8402c100a00c0e003076801a01c000400d03e000e078002d550201c0060418138107408544801d100482403951602e0343c0b03152500004c4c07170480b041c854260496001c607181e05013070301074407090b540d010355400c0301c4001500a0001c60f40000d41203504041c1c0381c3c00300103182201403044962400d240000404c524640e0702015182c03a60390703031201030041040901040405c00049401c042e281d41103030041100c40f40c140c00100038011135040a50305c1450b0a1110110540001842040303510a8a03106060306900340340c65101c1c081d074031509400540400800c65903903004407594000001c4c006250686c003080c1c22820501903240c4079210040748040d0b40304401d1000c424800c10211800310f805119008800180130490554291541c6c240540c4001c18aa068060342166420a46429445450745094401d8039441074440c4160700d4907016403416401c80310301c030303095100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 903449766 1250 903448516 903448529
    0x403030e0d0c1e030b04110907020d0905041122050906040905060f0402120703030210050c042711070c1a0a0c0b0907050909010f0507020c030c040b0d12020a031206 72
    0x11000c0c1d207000c84110400014050301030705040d0703003e070100000317548101c1240684c0c0940500c05181d02c0c000203200c501800074010b0741c1590301141a0081c2c2d951301c82503203025142c090f100810405100541100700b030066002481c400c4240d50b0084000105c1c40b00d40104980c8100c034031550548130703001403004491100001404c81d812840000d07800e000b90f440d140307802901c0909411050140e030020f844c10446503800450060304030406600c03a07040d1a0013881d80080701d02c2c2c922440c00d840d2580405c0d15601c150600001c901d01404412545503081c1e200c000e05000420300c0700e5a6140501c1d100201c0612030042e034140c2c440c0358010b48000750b041c400340e03601e8031060303103980e1903809081d00c6112515100800341010b620500c180842c15032142405240250404c0001150078240042107030166100107003c0070841d841400c1c071181551f070025900b164450140d600060040c0c240340481d44041c224080584252681d184802906900041b00b144441c041e6845000c8842c12100b0340c4182c40503449800d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 903451016 1250 903449766 903449783
    0x70e070207030f02030f0307030206090105010504050f0604050a060504050c0406080a0605010504031410020f0909091f1d030414280504240801051603020324010203070f05030403030e0d 81
    0x1c1c400215421090030081380020304440da99070309488200c0c603642c4020030480060b0001410b01541355424051740303014003011102404286010410011300b1070000b080da510541c1c541000c545225460781c0054098040580280f04038981040e2031800340d4410b1294100180308040041d01c100f5441c4104419683c05a481d68075061445c0c4600c220095900d168003081e0091161460070b201440c4024800c100c1200e2205854600d61003c2104061004003403078441e41000c0c0c030390b0000d00c0340e0420540100c0083d020000e07840c0c80d80c500702d03030114918500d108003e200000380420f2501d201c40141007190000c450982c0310302e610300c2d00c030050442410100404011904414820781c5040d8108200a064051741202444881c2d1190303201600240e00010650b5990790a0017000c003225072541a0388162800c05500c0c5003070140103510900003180082211003590402e4003903e81c428022035556980104040c0710200039401c00c80d889078040d210440104602800078807040c00c043c050400c2031500032104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 903452266 1250 903451016 903451019
    0x30e010f2d050c1b0f09160807020114190b1203070f08090402030a050411010c020604050d1a0711101803031e0c030906050f040506010605131a070302070e070207 71
    0x90724401100310401400020701c100c0a5152007044012040c0c0441d801103a00074039410705020342100c2400c0fa4074000e051040422060b041103040070142d40712949866940e9960701f1404070b0051400010000444000340d040c080404d0360000c01d1900940952000c00900c0315040030014104160600c100490b0024400140820558115105141e0007540e2203803810034440300213400c80e80119101d00341c0c23540d03c10a20040c0461030380303119181003007030818142040032500060f654ac0200d00c9201d20544400c60b44070100604409c010300302c10303080c048210003030904200c0a45000940c520f41c2060b07200e98815681d201c1810b0003403079a080194041302d030700380c4810b45049000e08803843c10746d4048074072514400da10048a108003038600d521a0f40000d010111450040140c07000a8009c1c1482001c40b020300000c1341010909a044902d982800366031050154821017041072554012440240c801c028141105560801000f5044c4a13500342c0e03c086444100c030401c80d000c01d990800040e40000350 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 903453516 1250 903452266 903452327
    0x106120b150a06050a0f0207180207051009080a030b0d0209070f18090b091815040f0206030403090305210a1202070c15080a050408190c020904030e010f 67
    0x50704107000003851454448001c01241081e00030b540a1030024000144406010750b106c80c02d400311010501c041e018951500349a000c0c55214a0801d00109a0001700303101042004c011030003069151420610080310a070a1410340c2e40c200403c0000464103100101240b4038141d02203040a40d0b000b010120603840b2100b00702c0d1070505002c0d01c10b041c012861a05c05051519426840042c211460701040c070303c800300103101c05c8041c003920000850049a42015101e480400c119064400045940c4420b60311820000e603600c8121001070341000001052100385a0f20112001c1941e00480854004a042030605441d2554000201c0700c804003e00c81c440c0810711807203904e10780001000000d420100d4507111845461250b5006490381161042b14040c2035402400c0140e01c444c0c010003c2001d86815100c07140702d8032070305294100e28a198515841c49502480c101030b8035640207407500072035142610b03002e0000c8054000d82408608000d092420741441400c2c504485d1903906001d4417003d01541 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 903454766 1250 903453516 903453533
    0x1050315070e03060406020c07060306050612100e31020a1502071e05010305180c0103050402012a2001140304061d0703061a1e03010204080a0302010b03010509010612 73
    0x2040301c0204600b0090080203941e007000424020703030042c800165a082055641460020203506c023800749401c01c1030422503590303403500b524000302892218141595880041c400030300e4082e0070182500000710184002101400d109080c49103205001c000c2110100c900c2d042c0f6000c8540d0007d40c03002140d0020301404100101d6218291914011503400685818084c00e0100c800303280c0298220715250308008a40c0d160113025080008810b0307404003038a1940103d51100c0c03481c101c5a05143e02c41d0040340459100340c4400410b44400719506807403001d0b5104040d0122105403090f05c0110618040c400201c0071030b1540d501d605030503100c040341c00440c206000c065130801842a0f4045581e41c41400341c1a0b0300c2c0d00180c2d8520080c2020300000c13802c2d85080401c8446200c10443d0020a6108041c0c950311000340c40412203030949071303034a802044000000c3c0a071299400104040c0a800c1514042540542000401301d4003100244055030760682c44a0880700301d4403031810f180c0d4041b01c14401045030300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 903456016 1250 903454766 903454771
    0x60901060807060837021c0c050a0203031b0418020a02012904110d0e0a05070b0a0e1c02151309050402540a0b060d0e0a020d0b010e0f01050315 63
    0x161114840b0034175200030004a030061140d000c40c08200f60003515070f01c002c91003440c07050801070401074241200303030740002e544c1d000051160a15120340c8074031001509075102035400502c4006107801c40031a000300710398060741140c0b8040e0055803d00a030100100400001c078050601401c80303000c840300c001020000074200d50b00c410059001d01b0800c00e2480b25450003000a4401303520000c02d0504003518000c7e1178019641e002c2040700500b840262441c540c4101c031040d0310902110002d1172045c0b1303001c204180d80c4400034000e44c4400203144081020071014050015900a48032440d01140d55196500039900210741c006e60105002100c100019242012081c0c080d1143d0301d001d24541c2901c4418010b030010300034244045010b002e00440c89400d51380c2959102170710f000e0501104140070041a41d600400c840b07545425240c035644410507004108441c4002c2c0c00814241c0050b920f03040081642000380901000e2003001d40c005a80400b2542e00e10741243c030003500504200c10007500041e03840501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 903457266 1250 903456016 903456091
    0x1b1a070c030206040308042c01030b0915040b0114030102040b040e0c27040c0302160b0721050612071d0a020f0703021f140c1b0609010608070608 64
    0x1950001c00903031520406440030b1441814296607079410001e00366142002d44400a1203083c5102a46a1054600b00742d541103035807100003808691600803c2c0b0381480100a45150040c040004100074802240e0400303040f0741e848140549001115000d143c240e00c2035004059010307004100800018182d0356400e544050b0701540f0f40e003800d0940d04c00461440a481e0003070030b642c10740040d07954076192a01c58045444a141001c6203081441140349c00e00040200c0080c0940301c4110001d0001401809011144900440c04103615100500e10740f00518044da082030240891700302e01001c59400160850a49140d084503007041c081c510240d07031040038010a940e0b01079409001c0d189101d00103402900e03c3c940709030041c001d016481d031007800c10401c4e03101c110a070550520742e80f0301c01d40307010080c1142c00078901207680341c1d90601c000401110003014001b020080c810103042202c84034045d40908156640700003070b5200d565540504640d042d0703090700c075444981c460901a030409440350305145040c1c002c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 903458516 1250 903457266 903457283
    0x15180a032003160506040201020106173c010905060106030c09210c180f020913051503071d0c0a0e0409050c04050c091504210501150306091b1a07 64
    0x2000f084101d10701503441c81201d0550000080c00115a02802000c0103000c8000d51100d92003503541c00903546a030031401c200d04002100500100c5840840d8404843c0605910600341808010140342e00a0010a400b030320117000c2c80c00089a004d1180c06000b4100c40d460381d83c0f03602030341004040100c83c040314000015180107441200001465480c0c00070081164805070175029001e031080c1011f6900703444045600c00e01c1008002c0c0141c0e5801c0f08521460b1007014006050354444405a618001c0340381580d41c14810b8400008541d040e4110321508407582d203541000d60740700e04001a480d4018001000f0108246124007078181c102640703c80020381c020382c1120b8100a03501c001c203044900c150b80910701d550001880c040741c0e00300712144030b020701034481c10b0341d2a040c81c3c00e074810b804003285415040d0f004d021500d8402409404d40040c0607600c55490149586540d0386001d07001810a80c0c402c403030a4030103e10b960905003122041c201203400300d0580741700f882c40038203100034035a014802c212901038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 903459766 1250 903458516 903458527
    0x80f0c0405030105181c020d0f14040b07030f09050102060103020d02040906110d06052403041b080309100e0d060203270115050307032f0315180a032003 67
    0x16024044d8502a4030034055004006070601d000307900745000d4080c0e030010fa206103981050380310703800103454010702581e2403c071800c295042c9007180c034503a00b10700e038140b031502c08140446c0c40000740c001448087d200380c40d10200030361141000e80f100c4019100b4240580c0000d0010400340c20711002c00e03211148010000202d0340b034641d8488049440c0b9424030f0041a00100c1d074818070910070702c00c5001802049500000c1102c2d405003d41301c0a004951070380110001002290401c2a4152840305466204404801c850b4503a5081540d94006071102e40c03007480c644603149105402a941004820320140011807042000d4540401a51024050700c40c0000949606180100d80c0d68040c40544105000400c85000504a042e0a06815044284250481d08003040040c00944203444980e55a0740404c01c1407480a00510502216005064160241c041145159500403200600c0303000c45207000d4080d109078400f480e07900c64182d60020081003050a602998600142c6442000c0f10781c141100e10b80f4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 903461016 1250 903459766 903459769
    0x130b1302040216020108060303131509030218061305130f030e1507120801050918032116033e0720040902010e0f0102072102091501080f0c0405 63
    0x1d0b480540300508a44003c88824119030b07000b9146a00a074085004500b400002c0e46007916000c0244603034918080080c5c02886518051f407802c81c02103400809143c51002004641150a1130890b502813003aa50190011225000c0c1e00c141400f4903407011071400161040c0d600c003105c0181d94071094060242ca480241625900c800308002000041c244523501c40c1c04610304003142a220002d92020b020307100e0018032464640708086907002545003060f20100301c5040d01e05085104540c1500002081c4000a41e0210800300d0480e000301c2003025248801194070f2030413000c40780c21000b1070050680042d1610620140158070490301c9040140c8100014030003c480c0150b6030044078221441c1c40c072440001c280074040344070622035542c11381c0d0510160117583d00081c245910103070328501c41c3e003015030714040a0744200403500142200181d030b18205044210f50076184103080504038032034846800003400056881c022620020703810385400840740c647e031110307881034240101015000042400b001866 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 903462266 1250 903461016 903461021
    0x9140a15031d0105071b0f0516030302190510020d14040609051c02190317010314010605220e030d15150206040309090209210d030c08130b130204 64
    0x1166280c80018003520412003000d003124901d8102c4000fa454030040008081d0032a2001c2c2da610b0a99a039545411001e181081c090744018001403d5486011054142e80e00351100740e90a0341d001e0313000c032989070012200c0d0003220307084c028004205070030900c500b1091080c01c3d0041c000341820840c02244042d0245654100014100c405541603611498a1024014148008100081000311017080d50036001c801039501e410302441a29214002c024050926128a4803c00003158020f07014085507520f0800035598488403400608552038141c0000d0a807074902001d22500071440f4070f5410242003000c0707120040c0003841c045400e9000400240d9542d5400744115000500c4001240c10b55506100b540c07003009940d05071140c250f60002040c8404660040c1c3c48004850400340e0150742c44818101003220140740b5000c0130901d4410141c002600c8201240d4660020580e54080003490002403049950800a4880d504040c4101c013901e0085201038801c10350060040300000607080c03841d4041000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 903463516 1250 903462266 903462299
    0xa031713260d022709090304140f0d0b010503010c030e06060f0d080406050c0111040e06040527100e010b0a09090f021e040e0606060a08040f05160e0a02070309140a 72
    0x4c240550400401c205103005004680c1ca00c0c003940d07071480510700404515607078400c40c0510010150f031806d120645541d010b400132411030380038051144421075880d100b02c40e00009e0150364070075403c090061500b00d02c00d100d001185100031000300402d8035403c0a11030301c805e0040300e45030892411005500450315a400400050070150f80f155aa400d5008034142180c4107202101e281071000c02003040402800305050340c108408440001d52901c85408004450150b2209103103030030821001d15a013184041404181c2c040e140e0028080050b09d149a5401c8a00c5200c4180d40950580003c2c022000741d80d210346601803082d0341140800e407043e00000c0c02e04880f1501140180b1806101d210340d170070302c3d018a0300c00d00c14400c002c0c0740c0742c200b050024400e400791811210070031003440001018421a8603400341096048026103031124192280c05100c280c103401145d25510f19100400c24440441c821580c401d0f805070350340319000e0b0500140c52650f481040c8204d501c100d40800c00301d400070102c0551034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 903464766 1250 903463516 903463537
    0x6090d0201060b12040320010c120b101403040c0b070c050301180c05151204030e0909030304051e0a12030501052425050a031713260d02 60
    0x90641044024291492034001006400040c4941600f0480f40a1296041a4542000c01c3c98501c1880c0b03251a00140d09080c4416600700540b010066070800100b6420182243c404d00640d0a120144007042d9188003909002600f40459410409039000285420030b104100b0b1a0f003541d41d40084102c0c1d0340049009488111101804200700c2c54244240450801c000d21000c903000c0042d00e60207004a00b500c249806020707140385440b0501c8011080300d4140001c158840c085007482d0030010030002340f286910f40a00425004114415030000559125035800001000303140c031400c111080c84504e0405071049803140c00401ca000800d840744580c0300000a5500003003941c500810410030744d0146000a69584001503506103842024045038a08a801401e144048200c003100d14011840318030042c280340108008c040815902081081260443d209c02c0c24043d1184c4480609240c50f00c540200402c3c0c00348622085141180044540c1c0a021110b2609128510f004582680d201002c8907 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 903466016 1250 903464766 903464773
    0x40f03121103180f0a03030c0302070204021201030b0c040b0d0b04230907050406140603150a030f03120c020a060b0a120501060e07020d02030d110f04090f05181203180609 75
    0x400b0788484115841003243c0d001c0c00403d40c900c5080485074803803064010103030816441d00071501c0014040d07012100c40359400b500440da1403407203081180840c0001c2c002200c40c418a00003050152500c0b5082d18142e41e00c2c0070249290420064184005188140398103401c40c0d00d4140d826869000c0102040d003e02d000f121010381407030032104117400c04441340c1102d48610b19080c0e081c40a44180c0c11051010001a90100d40d252a045180107218003601106684200c4050b008002c004481c00d4040f0709902c80d84444a8220304100040c041d1081d1002e0a40180c0c0500c0d50400412410740040070341160107800303880c070951261110480d218403558244c1e80d5a44038801000200c0b28501841d07800001c51024050020700e1000080d00c0c1e211b0329030300070b10581e00c401c80c41204c2d04000d82100c4d108032152103d280c2c5c441e40d4445001c0640f684460a4582518200c0011000c8240601314001181c03650081d01c0201400c8414880c29000a42901039409480c2081c1030300107002c01c0b016000c1c140c01c6004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 903467266 1250 903466016 903466021
    0x6050c1e01090c050a0b070807080c03040308070c06050a0c0f111002070501020f1606050307090b0d05071d0901090903170a0b120a05070501050a0527040e060c03040f03121103 77
    0x8450f40e452580c0c031041c05611203090820882d600d038030941e1011603105510300c0d520007460520000300d014075207400c600341c00002000410080b8410013000b00034410703480340b031341580d980b6000d803000c1c0101101c01012400030102e00740000c00041811a00501c203409030400c1003074100c041000701c0c41007e83e450240c0d1102000380705960701040359542c1032800100a050f401d141a00c540307541c1c28540304103c00c0c0580403020500d40ca01421015004c0c209020b80ca035200d07042c040c10752020307040640e460030115a03035202071a000c5000200042007290080e001c0740c41e50b403901c0a2070300140050201902000f10311120120311003003e6450901035407400c007000c03031052000070400102c40d50041c881080342c0d000140f86800204003003000801c9a1013400c02c180c03540703803c58058401d48a40b080b1a0380c50b00c0304ca03003507050000e04603170104803449094600300503d805500c0c50b00e030b0301c101c1a101159220403d200043c00629007000344c0036024464641081d440f080d0401c5036060f03400d41a008034503005c001c002c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 903468516 1250 903467266 903467273
    0x5030c101e0902060a05130e040c030b0105011d060c030715020d0506030307030c031b02040212150103090506010e130c06081e01030209180322090b0609060406050c1e0109 75
    0x40040440307050000c100019070040d400034800340f00702242ca4051010101b0862150100341c0e0980e0007d168490904e030036881d007841c0c0010000100e000443d24900000b00101d03055228030030000002080e02000035082c140d00042002e690445032400d0340a00c410001c103c00a103000c442d500b0041c00140d400760300c0d030500206107010b44030003c00140c003c0c3e01c24408600442d50041d248010540c2506180c449212031a8200c080c81c00e00d80030180d0000e000181030609203c815141c2440b40d030001520409242580d00110240c43e403124003d405944110014403103201c10441807500101c0303008000c0c489450b180c0d50b02c4900c01f1664441004039090030100404104030300d44252a070320b10020b40c803659604690000d800300703c02411210340c940c880e00006083c8030382001162a0b48980b5a01400300302c40e0540040100c014a001d2020803a00300030103086a402d003142030329a40d10340208010305240c10041304030396640000b0b12800c900e211b0380c10100f480409071003519070605040b40010421744040e04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 903469766 1250 903468516 903468551
    0x100e030c19060501050d02090c0d0204050d0b0403081005240c0111030f0a0203010e0109050415020d1e2c0c130207020906150a050f040f0f1508090a0201030905030c10 73
    0x80c0b02e140240c2d43e003115000140d0712313061065800009480466228103002000b50000c0c0035603001160849100d003081030604c4441c04000d84258801c1d6203c0c2910342d50800c404152440030712030103070001c010038005100380003c4815031090390b00903a08282443d0f6510714403800d540390700c00e482e143c2080000c18041d1010700041e1155000c0424041913207103514100304004011414820f01d50416583d10201d410896514100905103030303144070540d103c0000c8582c00c3c00518545240403580401c84d0003076013811869020390301a9411028000b945039400040304002a18402528810341c0120740c0c140c2c0441c3c0d1200301421480c0008180140c442c040e41c070500210740b001a25240c402c42c03030340203020b01c00c144450488aa04482c1c0c50040e469080303442c070072280c0c3d00442c0c20200e00c1c004600800310340402542504400c441e11401504034042ea403840c01e480c4d80d241901c42d0116500700340c80e2200594020740183d4001c600c100201c0345800c0d4101d403c241004030082c12424856214560340500c0410b02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 903471016 1250 903469766 903469769
    0x1506090315020403030504031403070c0b09010207080c330d200c0a030e060708071406180d05070c0b030f041101021612060902090703020307090f030302100e030c19060501 75
    0x10800b10302c2c2504584020b0000d010b43c1c071005120541d043e4900140c07030801d00568103181c0e403042251800359241c0031405010703002050481c2c01031160110014103000c000414221820010380a09d141e241e015500704500c0c2e0091202c100c0883c0e003104a140032140038001440c0c41c0e681d00a0000301407441d51940b40c415945411404860101070050062522020600610780c1d6414100b1849484400000c5041c3d40550f030710150903440086034100901c80c140c0c1c1d1014404034143c0541e042d903682c5414101102100c0351100080394052403c03041001c0c010070003440564000c2244152403995903c03881c1040d8400c1714204d804c2c1c0e2130141400b00f0007420340318118000000b4006440d503002c0464404805591038031940b21107109800c244418040190701c5039041701d8014008130210315001002802940c010b0303070030100088842100103030a0214500a10030341e5071560181c0717a800543c0042d0b202801c0e45007003244d00c5001c1040016282c002c200407080d011034407038014000f0b0000b0360410300100c8605 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 903472266 1250 903471016 903471053
    0x5010b060309151b160209060108090a2d0f12021b0409140105070503010f08161815060e01120e030403200405041a060a06020d1215060903 61
    0x14024844280404215003c400f501c5048014080d52150708100c6580101841c000e40440001011305040c2d554603460160320b40240c1d011174503a03c071103004480c01d0070700b00c071940e115030012019040040c4248028040384140b82c641007524052012001290740b610203411584545512201000c1114202d0502c480c41001d00180411000c1c00082001103826450810301c00c0b0790300c13084002002403862020050600800080101c0e1502d800060140d070300078041c02d031170042c41400002d0100c1000401c80510310400c0c3d04a1102d43c68908142c071f40b03100c0c5400d079080c1d6546071040c03040c1440440341c0300750080c01d25648203511600548000b404170066003181c45002d506040216000060000444085982c01610384010b400c09800e42c6e079841d002c0c400745680c803e042c041404103000340156040d020798141081501e4507202c1d4402c004142d0031030700c248000350708412000032040780103c940a154401415000c1100740c6000d0344100305180380e4100d0b50101d0312403031060041c418008241c541c00e419 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 903473516 1250 903472266 903472279
    0x1e1005071502191d1018080303190e100906090204090c051504140f01050d0507030603030f0e2101110c01090606080a0f02040203101e03060516140d020415080405010b 73
    0x209242d0500e00d41610500703c40c051740001c0040c03015184a80188200646031012001e1040d440310001030b125481519215130740300a486010009215522580c1d95100d24400100040352005a44001501d8001c000380c480660b200c080340c016894034040c0c4c01a16100d8104080424201000c0000c105043c1c00b42c03d1401409010901c640090440b040d8082a4110350030440603980c01e0040300c9920412080807640f60902c003e00040640540050041d2031090316220031141400000b241da07541c201000a900c21614800041002c03048200040001e010310008030f07088041d041c01c000681e2040d821506940e541e02c1c0340314284000c030310030a4080c1c10742c0f4000c1c3c0201000303a21034481800c21000c3c080d1189900002040c4014548145c0c60020108c07540100c1c039584900d5454411210244410b4442900b40b80c0001c0c501044070500380d1a81240b61241d9410005884200300b035900003a043d20b803030310340c200000300d00d44e42540c40440b4216120340e1044a0b03454a813419038292002611407034003070032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 903474766 1250 903473516 903473537
    0xe180d0e0418110f0d0c0306050105010e040e060a1e0e0a0c0911180118060c06060e090a08070602070b040b09012f09030c0a080d0e1e100507150219 65
    0x11900043e4901d00e41c1c04554284220500d03400242c101700c0e0004000309481e4442d040081000b049401440c12a0026240c281ea0103906a0500c8141d400d218000c444c1c40d0000c500041901e01c2550100c4001582d842c100c90400c9640075034002150007003071011403103034407034a00d0320100400c00c00304002400150b00305001c2500c0703285c0300307190300d00030900420313031a50720071a041c00164440c0c101980c2c18203282c410003e10039a03401011340a104551015690139041400c0031609510300202d1600610b4a1401882800041e403100841d681007120220f52980d02002040003180f10600402e0107a4003c032050315803410070041c02421522a0211800010f64040380c1000306c40c41c882191800a08203125282d4900744500042c0c1041d09140815034003104950300401c3d410300000348010445155110308200c02d20f01000c022084c0021100c604880305025080c40c030380d040c100641032651200c0c0c100142081c03529518040b000d00903181c0c01030915404119010740d22000011329480d0546070070b1a0207001d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 903476016 1250 903474766 903474773
    0x31e03070b0a091505040b06010f080c0702182706010b0409090516090209011d09011203120207050c040f0c0e060a0203070f050705010f0908070e180d0e0418 69
    0x80c0211440a8003003018000001d40c0240250003c1003a81c3c1c3c82030002034005401d0802d43c0007458180d8080e244404c1502c001202c0d54014480c500814010361207165031547c45401d0282c0d60f621442049800000e00e03804090035110000d100750041000040000b404031000310300c5181800380c9806a1a9540308000400031414903000f1a4150f070640500850004410b05110345014000303554030080c5520404000b405090640c09061565000d98035007154007888446080096910321105920840c141d0040118144d91080c0030340c0c081c80703818120700300d00250480d48101d03000154280d415070040c02d146903082c0351520034090340501d068810003090310028001004000305126083c0100400159000c00b14003c0080d9452190f01c0801043d01c4031261510a0b2550700700d01ca050f010071307a0003041d0702da80d40c01030813034100b91074000e4018803040789032155094071000701401112428800c3e5a1040d003058041c0b0000640c0c8090b51911ba80c40d601410510044400f0785a0142e201050404800d000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 903477266 1250 903476016 903476023
    0x1080c0913080d090c03020618043606090c0f090c0503010e0a09030522050a080106231f0f0908061e0402030309190609060311121503010204090605031e 67
    0x8040b000a00007642804c1494280d45008094001943c0b112011940c10010070704120494007401041d1800c3c400c08070511151480402e9802e60100d00301002e03130b082601c030b0182d051991451405054081503603a1651030385a4000820f4101c001180002c3c8400d200108950090422448051402501d035600d410890b403c401c401402d003241e010348506030b00060501c114241c0f141c0012544001142e4540e030f201c00c8010412a108141c016070980600184011040c8281d01c22104901001d40d404203d02135280356000d50241c01e80d40c0702c00d0320000c50100400c42c00e07081d001440e82d43c07a106140d41017040081d10700400e640c04208036a01002c10050003503c058407602c100d4114a180b21310b2511640700007421030041c17064041d00460054110318a00d907903c0c0344001101d40b02c5d1180345031292500d0045050385c078103500b003a0049404101051031010303c0110396130301c41c0001800c0041ca044250019007079a00540c000e45d0810b48407032040c0524901031003081070503e2407000c5403a0310740407035006646 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 903478516 1250 903477266 903477277
    0x60f0903230a051f0e121c1b0807030506030f0d2607050702100801211a190606180b03092b0306090b0d0206030601031401080c091308 59
    0x5210407640000c45844081040c07401c0e40e40e0140c1501d810700404655502c3d00b43c40314104510f400d040c06005e8580e000e002c103030710303500d148041000c0740b9000903070b54030700001d110030b005214095654070918020050010b04825520089503030380070080c104100010180c0d030000d09040e01c290007058000d0358150300011090841e00e001d00f001d07140c91a1140101c40804112006040780382010b404202500d81e000c0024240c1a00c211105894180d10032004c43d8002424091024204071580c2d001c0144501c05450001640c4201c1400101d0555000c803544000b006079040c403048404950f00032030440d56030107030401a020701c2c0b0b020203106d003445462515084083c41102014080040071841882c0140074603020b00e84a0a01e01c40b21a030341c07140e00c0190600110020001920300440031032045100d001e00d40003440c0c000c15041502c030481d020012103a00240907103050640d143c442003101c01042440d68000c01e45100941201d031080c0c018810305407030041040403501110184507000604d8001640c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 903479766 1250 903478516 903478553
    0x120613180b090309030a081b0303190b0f1009150201110d09050c090709061e021b0118141810090c051b030c01060906050f011404120804060f0903 64
    0x1405500c40c09045070441c410640042d03014003076544800306001105005200f48c069000000340982e82d1000070036200e0000340c03800780311454040307000301216980d9002614500001040c08040b14170000000c1c03c0020300856080c0441c0c5001420010300c881c0b8040c003c0440044e0000380920f0f1000507422b0070a00c10425502e0505036100440340500c03c0800049581b00406421031625060514001d001071500f842290002145021000c0844016045100600090381c0042195a4042c4009444a50080c1c04503042000148104d0b8609039244843e41c02403480504454429100c40207200742201400400213040742e0580500c6030b800700d04180300048800080b00052058000f113000c4505118242e408500080d0080c017880304000040024145a28014001c02c0340b15a41c090400603580036214040d0310072210301c44c00c2181d50140300d10010040360003081c07629240e11050340b13034040e07c41010140c1d52000c020500348145900102c0400303115000d410034a00041c9190f5a200300115481c2c1d00300c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 903481016 1250 903479766 903479783
    0x50108040501150605130504201813020d14010b0906070c15092c0c0904060f031a0a2702040b04141b032502070b12061318 54
    0xd02488000c0d07100c00b4104490111400d0103e40d60080240160858840c4014400c01c84200240c03529240c803a1661703075021420145420901250290702e00d400c100c14881004009000321f80e0710b43d960351056803030450482c40041e111f40381c4184442c1140c08840d180e00740120340000601c0306602e0401500d0f0710031000c41c2c0c030307694600700392600102041c9103501580c01d01c0301064401c2e03d0b0507081031514042d6030340004828209110f840711301d8000640e0003904c0115000d00404588a9000f001c003c000c1c15102820200b141c030b40c2c0364440c50100c0002d902c00d45080611480c00c0c044030810400d0340d50400711024040c40703541090015030011142090030580d2100f03504002a0031901d660300883c80741040103008001e440b42240c0e545180c01c00031640d142c2d07014000c20803a0b40c00d80303404081c0c0b805444084040241000381c02100c1d210392110840300c1c015440b4030340c4005048003c11000f401088181c035031121050805400380102c514904219082950070200206802c1c0c122070b0040c80c0954005002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 903482266 1250 903481016 903481021
    0xf0b0c10060609030b0c070308040308104b0902090d02040912021009080301170a0c150210091a0406020f0c0604050622151b020c1f0207050108 63
    0x428a04081a12412030941c140400000d03541d41040300001140d0160354030b464030703035074125005590b48501030006001c203040c0c2c1c0110f80400d124040151f806030180304190301154071181c40d40ba910313204c600d40c400003a000c440c2a641c06101c00060741e1107000c5e10460042104042e540d046880d0002d409013189a42d8045001841da90b01d41e80035082658018008001490040c1054065802000e01c0c2d03001520071b40000c00401c1c00d540c4240790242d070b00094000c2c110790038041804511034540e9220a060703c10417000501203044000f400c801020140e08041f61101d030b110b0040d040092190042007490703d01803540c008103489580c400c40641010702d24030301517074443c42c06034028000e01e407540423080c2002c54200e16403400003480034021741c003420071a0f840313039200248082400070362006010b0402c0e0800c0c0080c009040c100c2000358a640d400408200b5452402260101c4100c200c09003005911101c00c4ea021400c007480c1c40c01e1207020005a00600400ba0f21019546400c079100d52410440070900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 903483516 1250 903482266 903482287
    0x901060c0b0c16030e0315011a070606090e03041a040608151f02070e0112021503090f0109061b11120d06051305040212030406021203060112090b0703150f0b 69
    0x100e4459400700c0c00f80c91010340003070400504602c00c02842e50701900c12501c0c07a8a1007513501d08068100c40454110210380b068100303004226070000c45080703c40d10346842020500d010b10b40a44825944c03c04000e40e262440c00b403030110149085074505590b204108400d010256010003110b5101071000c94404064201e50f000c0f45444070f8130141d001540f00d240c40720342035080d4045110b4040329032031a03035180300780d0b01c07100b2804121101c0c50b402580402c90300190010181c0040c081d40c0d00480580036107100e1401140810b0070360b40007140c00c0301e1031962400c803580c8041c040c613400c440c654203d2900d00d1049491095156881c0e0b80c440446500010119003064280800e0b00640c0203440064500c512181411911401070b20082c1c0d4100c5c0f1402d16002d910b410f20f4000410398040755170560040140340d4050161103802e0b0300141c4803a041041c0342e010b404a40c1d000e800f8050355107204580064591500120050481c4c80c41c4968588503580340c882002280304d031010310002d8035507600e140c6950351861344 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 903484766 1250 903483516 903483541
    0x150603080327060f0115090b07020d0c1701020310080609060619030804080f070510050301060f0e060307081501020118021302270411071e1b1e050901060c0b 69
    0x2d4001c0b09511902081064000450001d581200d00c80c1c90311880412079038500342c0c0d515a031401142101d61040c401403000d0314200c038807450300d20b004002c020036040e00d4400e01504042201c240b000940e40000034840ca000510344002d0052a10304094402420582152070700c40300041c0110b84a07103c00769000407540045a0b00078015544501815512603a07800400d8491a038110200b9a034000d09074002440c3c200112000741c60b80c0d0503520685543c0c203002040d1004035401307a02c0e60030016400c0048101e5101c1074019809a81161a1000c251900141444042101c100f66604690410701d540c6d50305500701c07415512135a4122441440c0b02840c552981c028043c9070307001801d60b16080320f0f2890040c07288911202458003941c040c448007917580700140552044110003002e104020440401889817003403920714661184040f00002a0500260080d100340d542120300e074803100500ca0101482030000350b0707009001c00d5400007142d41c508800500540b034160400307005591214005a184806030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 903486016 1250 903484766 903484831
    0xf01050d09051515010c170f0705060907241b1a04050c03061e0a090611040e01090605030706120f0c260f0a0b0d06050a091506030803 59
    0x880800c0051070509100d42d807194183d02c0c01c9005444103001c10300c1070f080200c40c18081401a19844280440c0380c0d501425210010980c0c0c61021081c01a660040440e02c0280760807401000184000c1c10b041e01d015003014040e5010324001c601c02ea510510507070084102881800c03860030048000f1030200d81c0c400c203003410510010002d0001c940d5100c20112030040007402140540201c0d0000f5a04506259035040142c1d080709641c01001061070607607610000c6240c0c420b00c42c40001c03481101d1a9104001d407011215544580c2c9000714050103a4041ca0b4955401001495024080149010b01081d103400c041c0c0600030800441c034002540b07180710b44e00b0181d0245030b11501003007120100c5500404103c2619a05a982140c090424000c501e510140758041ca071903041d0384039580c861765129001401203416594005d0321140b56000403405d00d105041c41840e090a011440061a14240c458964480301b400c410924104090011540500680b44e000d84140481865100211400c01c2a20300c40d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 903487266 1250 903486016 903486037
    0xe130b010212030901050412030207050703121e0e010f02070b04031209080d02030a120c02121b0318150a020d08060a03120315050409020619051e0a020606011d0f0105 73
    0x31310084441c15400207110f240070320740c0c00e040010300076011800e0f4030070070401a00540c420101400400d80700811401014018100403445000981c03c1140d040b42c210400c0d0007203200c000c030a9800d540c000e4801c050080091015120190401466101e20f0186000207405401001c001e064228020140d680c00b0302820000c0716100051854000d640364000903191000501c0340b05d10f00d8001140d030103040001c03140e940192801c2180310194550039080303605c0f400884483c0c0c0702d00440d000c105100900340c1201c1075808410341072a000500140c11080e00c4908060102004400d400070f9001c1103015400350030f807030980d005440d2000040c62500319900082d2180242c180c117001010307059031290040d02401e0980c1c6020503640c10420045860025010b0b4100d030342000510b0307103019121540d1140c112507007480b40c00c01001080c103002c001d00c440019003600c81d000400103622501000034650100c001d01e000e060300122400b03034400d24030102c1402030007044a580d840640b68010300541e02c14000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 903488516 1250 903487266 903487303
    0x110307110a0b0412060f05010e0402010324030b010e100605190c0204050901050a050a0b060906090a0f060f02151b070f020405191802090402060a02120d0903030c0e130b0102 76
    0xc0300e04c0d169901410a00302265042c0c50001d4402c010002c40c000d05040b11001d00d07502c00599540c5e00154040c0008003071162000011113175000109506000c17443c00745000c0c100d800f4640d81450703009a5400700c05494124109541101004081e070b00404030fa0b2081c821070410004800600f009407145010303030790025489410501003082c100c00542c03103688101003108040c04551110007850040b105440e0407507407c1801085125064200000186004034000c0c01001a10b43e07184031103560900ca607008107001480e02451802c0701c80d810011500d114100b400100b1860500c600c21840000140c142d440090501242c41402c0c0540d02c5a602e42d01d6030060402c1c003c520301410103400b400f058010803038120b880c0243c089092141040c1c040c80d4a540a40301403081d480e503808100c40354122080d664114450170f0502032450f0042c00c0130f480313490607a1030045501c0b040340c0350180645140032451810018075076001d150603901e60504500c1000541c10010b400030b0380c40c00403801e000380c1034408981c412 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 903489766 1250 903488516 903488519
    0x5010f110321161d010c1403070b0c1303170c070f0618031203180c03051c0f080117010b121b0315010333060312110307110a0b04 57
    0x411500c00200740310a0080c0c69a041d600c541c0007416424200b101d14000400361040050040390f407021040404c041414901050f0318507517258580600c000d03000b00440c0d000441c2104c01c0044c442c01441c1c200408448031424005d17034800c201d0300440a444003502da5a2a140308003071014000b82202c04581c24101a250500c0d150002d00c5010f01d294032030040080c51110f01c06200901602851081d25440503d4202031000c07110114043c1600b1201a00840c600059040000301070b01c1000e4001c40c891005440c240089041c01e1f40d0524080751824107000750491001c3c00107030301c1042d190654a000d5544038030400505501401403040d03030905500400f605040c2d0070405400108925491070b0300c0c00c20303040000b8020605031070f000100800400041c2c080014000074040e22840c0c0480890520300c0003903030840c0e411074003814440300704003900303140e85040900038400c02c40501510b0342220b0802c4e5440d8008041441d507030b44901c00d0050050319000614005640d20448814000d040341c09040303032030342d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 903491016 1250 903489766 903489787
    0x1a1e09070e011502031c02040807090c090f060206061302090d0b0406150f0918020d080d0b03030c0a03030f0e06010f0f050d030903030305040213060b070b0c03060a05010f1103 77
    0x3041580554204246a40000034124009204010710200c1590145042c62140100030345050304141c2800032040e000d20000ca507080040010b10000c1100c1740700414400750303200000e441084150050000014000c405000268000520541042c01038444044080b01812050020300402c3c5015500c0220480e1010a200c01ca00d1854022400345108114100c02d81e440e054200165103d04003580852040c1007040da010380d405400114107000b400030203649280d002400707458040104550307400e00407800303091580c1248162035061174180e008624001d58656150740d1001d0110000302096141c40e00401c4043d116005119040f020404881155840e0703807042010f030320640950b260070051842c0001303e40c50324440c9002e01a4150b140d440300b65080d034504801070300303004005903001221144014004056442500d000306222010b043d00c49c8a03a1808064030f0202405881da021030903c207100b0b04d555001c0b068021200c0900300702042d082400f105403800b8103a003404070311500000c100220507 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 903492266 1250 903491016 903491023
    0xc06020a030e030712020d0303020c12041509050f0f040209030102191d0604030825080a1805131e0f0614060c0601060f09030215070512071a1e09 64
    0xa0701c2a210035400103518014142d55070014070480031583c5841e4140d81c0907003400c0e2840c2d40f1940c040d00c0c008d40b80203003200c605841c0c0040000c07400c842146c0000e0802c60b4035070307107106401303000100e02e803e00381c43e454100001c1c5041d910348000c0d440303452145020801c503a034541c11108884d8000d4000e6440302805c164103c60074500d0440c400205290860344801c40c01c1d281a810000b5100034a460705060450b103400d1140d0300880210b04281e0003140d81c25411b020f01300102c8104034803540400e5681c1c0050000142030492002841843c594441d4051086070744424804086011204c00081c080140001d041a0188412103080c8000e142ca00106510009500a441030b81c410325042500d00c5200024080244695540680c880c1c102d4030050014078850354224880b8400c40c81c003611a0b0380c41c2d03000a00c100b50030700100444100b00007285000c01c02c051041705603981c03d604800d402d00c01681c0786c0e00720400c15290440001c0b9080030000e604110030480302c1518460300780c405a5240b4050740300310f40c7c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 903493516 1250 903492266 903492283
    0x1118160c06050a150b0a09060804031115010302010f0216050d050c09010b09030c0a0b0a030506041506050d060605030403050d050c1c02030f4b09030a0e0f010815010c0c0602 76
    0x20300c844c3c400f1010455011500444900c0e11213a626000342c1d41c0342003801c03140303950050400c80c2003190a0450282800d410417082c4409014943c40d840e2552651001510141c0a01e0141066401200415110048140e07040b000c8460a0741d001d10400071a180c030f00e00705102c090a01c0e038407848420021a80d18203d90150984043c154115a511568030b01002407240d282d1203602c40f00c9200f005503602d04c07442500403981028014001044c010040c048603456000c0b20781103000062404100c0609440d002d0003030000070a554105a89503051070b8400030064070941c40d035010450346940200d52048103040499481d48418603c0f54aa0101c0800391000f82d44107480034900c100400d400700d44190000e007108181d0b007501c01030845a000b03400c03c0d0958490241e032107206e1b1168055490203110110141c00501c910f401001a60307817450151009881c02c0049150a4002c42140c2c085150b01e9800481c481d0700004506240e46008030310310012140607a060380f009001c1c0359840000a05140c000540b0715 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 903494766 1250 903493516 903493541
    0x120a05032803090b042603012c1303050f0906040b04061e0815060c01050a050615120109050c0705010617070605091e0303160f1118160c06050a 63
    0x2108450112000c8003660200000548080313100e0740440c0000380c0d0598040c0e00d8010845900044140c50710840200b50400d0380501202058201141c0e00d100c52160400306601c040314400007141004a2201240400c14000609000000400c00f90301d0031600196001800020a401c0c2e8541d00c80802c107000390007274815800460740c2a4000b03500662020a9540e54901595896000e5615001c0740518080d401c1c01032600a901000383d6041110300b030007600d101c0c1100180c041250f0801400744180d06c078000724604001c0c10140f009403003034040c1c80600c1d8116182e034803021905807198007508205100d440e000800643c60020000340c4407500f40c00c4d0348500400035041d0f0f50502c1d03480c03009681601ca802d04a580c0f2010510088090b5a40d8210300448960040c0480c0d04142d0307202079520940f03801400a0b42e0080c821030a0004010000c04c012902d5101940c84000c0c4480250301c1039160744016140d0324101214602110303503103200c0e000240c80c194001c0d070148210b04100a00300000d05c800701c0c1c080d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 903496016 1250 903494766 903494827
    0x204050903090102100c03181a060a0e06060a030e0f0124080c0402030c1201080106091109031b1302070312050117030d091e030e1f0905120a0503 64
    0x400c1020040107035005031906801410b010740014120f0300050000404040a0503030381d501182034a05130001070070700a40304102464030502c0042c0880c4002c9402040b113440341802c0c01c070a02800d4000a0400d402010a80b002ca03201c403444441030f00a0961101e40d21803c0c03082031080d8110900542048540354078034040e12402c086980700380d400019450107407501552000101e00c2c41401c1640c000c540c0159031040c1c1c9802e004a03150014004d04081c0e2000308180c0d11000b00b0f20911407284a100d140c500660201458400e404000c41c1c0c581006c000390005200d07082d07414195584642044001c99100c1e00800c42d6a041c0d00d00c0d001c1d0449550500385800140707440000700f0b01910480a050f40154140f008504203494690040302034486071a04449035100c4964081070340c40d0b91a65010003510a444010400e000902030202440030401001c04020301c00c0c452907600382d00100b902d016142e0a59260041c2007984032000d19041807518014694840021680008104d07440c01b0040d820001504 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 903497266 1250 903496016 903496021
    0x4080f0c0606090f0709060c140313030b01140d020d150c02011514010933090612060302060406051e04080622080a0c020f040603081c0501080601061413060507020405 73
    0x130a450300c4012101c81c00481c0140748180702d40c83c0200040340341103200790014841d42d24a0100281583c1200703090003203002c810301c0140104000340740030714007401449071000219400320300081d200d03680f00300e0081d01584105213420f060010a0b0702007044001040d4050180343d5141000900a01c0c0c6044c180d8200e0809041c08203d61036050f4130a00c2000050350344030321060900c0c001c031200e4105a40040c43c00b4000384900c0d50301c0f008402c901d084d0b9148a40320154401c0c5003001c098003003000e00c0144003001c0d10301001070006071364990603601034544510340141c0b52041040c509019880ca102810541100800c1c0003484990014515115a00a80c0c10800241071907081c01c075100200d401c0101040020302001010320300c501440d5580d035000512011100701070f030380800d04550309130f0001e440c2c80000145807445072200b4040904a00d5000c1020813182d850107208a440d81c0041c00b49070104410ba56206001d0143c20381543c0d41d0000349003880c0e05c21990380d45c014125611160301203020b5802c1000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 903498516 1250 903497266 903497281
    0x4092010140a030e0f0d0206040b0604020702010f03020d0b0409050a0201090e040804031e021f02010e07050919110c0106030201080705040311010e010519020a021915030504080f0c060609 82
    0x41009601c00030a00d01d03414a41200000e60160582c0385070840e180c0f1403005600350803681000190310f440619000ba0000e4100b505010a455070000d145030f000d0b0b030041102c44010f03680900c8012a81149180042c0c4a00c110518140075008092100764041e040a10100070702c100400c4105003503100b41c07201c0008070380e1038005402081c0200d4000e41041c20901041004c100201c2c540380b0030354001c044611035941c1e00c0c3e0028800c1d40d04020182d803038040400380c448815409228880d010921030004003001454440054000c0380c00030004181d00248400c100014000c0740c10070408142c40b000303c0f680b6000c41c5003669000b0000361000341c2c001007491011448050142c8212810340e40c009a0b108410005900196200d03943c001c0650b04020003081041c0f0f04101000c00c42c500550294084e00703c1c04010300400032000780700800201e15185c03034901013003000d07600e80760681c0482142c103020499075201e0808080f14082c54030907131090840000e01c006450300108015204500071240d018a40d1550403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 903499766 1250 903498516 903498527
    0xd0915030c0908330f1b120f07020c0316061101020d020c0a03020c0108160f1e020a0c050901060f08070c050a030905090a0507020c0d0c0f03030203030603120306010e06070204092010 80
    0xd0300100d180045c54046034030400c05002007644955a420818500308a071400e02100c0c0d2011505c5202078200f0601740403416905014003020f001c0214002c0540b41480104404428103a1080c2800c1c0003141103410b005003021b405803011034084aa0440d1503180d80400c00b5140c000b0b105044006000c1d016402500b907002c0c0c1715143c082c1502c510220350840210909036081e606800910f000d00c141c4c01e1034041048501c440604821a00381c4c00743c0400782c03461501c200d081031150402c912514020005010855002820070312070304403480d00b41559106c07a0010340d440d002c079860152080c040d510002e01415003001c109812140e055410107695a0341080e084100c07001960b2040c0184c0002100440a151032048001c010340a507010b40081540c1d8082c103800c84583c0e43c012000751b0008000c00605140030300004115510030440c8034554030700580000c06030741c8440c088900c100404540315042d515194004200960b000450480c4c81241e50880010031055443c8207104140507005c0c0808144201e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 903501016 1250 903499766 903499771
    0x80d1b080c0a03271505091e010905030307050a0b0c120f07090918080f0c010f0e0105090d020c27070305040519081204050309210d0915030c090833 65
    0x3d401005500f0304104060505d820765002c0329042180038856501036503034141d544051065884414665480981c0c0054541c00c420740c0b026200350014001500441c03000324410f05a15440800036a45680b290100b9143e0f010706650806202904010002d4201e4400f44003409114aa128048010303500c429404c181c0b03541110f1040c030200b81c0c0c40d0200000303043c07101405801000c0b0560700e00304108002c1c040d003112201e040200d8200d85500c50480315050a2195075080609800940750741440000040c2da05c1d40c00a1070b0f24007502081e4600030801152102c1600504035006c03071451241821403000300507140030b66082e5518090b2020605812400c5a007050400340d0000b80603060041d0b4602c080c3d49910b009009440300e01080043c45041e6a0304244c1c040030130000320844558a0031448401e10f46084914500300340000004284181c01482180c41018500c07407901042d0070120201c1100e005036154403600c1c1622032a407400b54401540e003246807003003020155a020101c100c14291207205401d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 903502266 1250 903501016 903501077
    0x1103071502101a13020306240f030c07140d0f0201021e07050a06090507030c080c01140703120e030a1116061b05160519080d1b080c0a03 60
    0x1424012a1a07607160f046a404003c0400030340303020350852804205190194103e20800170341c00010820315180070074076648601800c1030380140d5400c49540412440c415007440e1040410084006031100c502d0504490744c00da44460704c103070002c00e020003107941d40f10701404170400f01e5141058141c18610501c01d0714543c0740c10401c8070b001180d1540700c8485075031040105079081d0181c401d240d804580c09014031402c081c4207400400d49189141013002c03401d900780d001244c058000c03810301c00c056a4000c05032010401c407000d0360b50340d55616240559200a005001c210100c0c00d0405a4031144d5020015058045142d16500c2c00804c3e4140d1090b10b640804046400d44000200180314051048220241d5286108480301025445480d85880c3c4082c1d403c0042c0d1b070b0031652790240418140580d05056a4042025542d88107003000300c519104c413100002e9404021354034030080c0281a40e100a2001c09800060a65032040340105064031113010803803c0d0b0120300c2150340280092040031a41212900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 903503516 1250 903502266 903502273
    0xc030105010e0d0507120b070e0d151e1b120c120203151207180b030a03140d0203101d060d020402030a022703010c0903050c041e02031f06020c0d0f020d0f1103071502 73
    0x5041540d000a040780c0c403c40551841c0070407803303070b01c01d03091090a0001c50110403040018404440050100081041b80d403209070800b21036021003508860003e8110510403005a180e45e200c588140785280d038010240c0c0e00c810b49064400c15074a005c40c07100103450300c20300c84010140c5092a000103131103030910303540d406900c044c01c05400300c1e2080804e4490f0361080d04466140c0040c010000c400d9800a1307a0300d88030354003100c0d410020500060036082c2d00410300315003549140707492000110400b4205001a008a400100041c02c0c0001ca0b0304541e00a10500d07200e00c00d0403030f01c01882c0c44846010341107600942c6801041d28450f0702808119003120f40c8400104000358040c0c0c1804050500303000e0b580358500b04110420a40812400510700c19502d10001441c3c82c1d00c8034031005580d0800342d00800554000f1802035410351030b50b15148102030b800c041107807025801440864114014804080c103080707140e000f0107041002407010011543d1048085924064403001d0710720f5a10811400744002d40e1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 903504766 1250 903503516 903503543
    0x60b03010b0a0c02060c010c020601051813020301060b040923130809060d050705070302120c1e03191d0603013002060408150c030105010e0d0507120b070e0d 69
    0x48072500809441400345407500d184082a0b02240c41c80e04007104000040c1d440b149001c030784981c1002028010901195a00c980d6000705000054000c0043c00f40c0c00b500e126411040b00f9074900f500490300501740d4084042c4d80301c0e600d0610100510a04030006d52031000259a0540c51040040c041d00840507180080d207000041c1c0c0e1014200d078041e01c481a003000342071082800c0e417413903445040d20034016038030b4443c0c2e04c034800e15000741492590440704500000c24002c001e1650300020b84200308214181400245100d8280307480c0c0f07980501c4402001d4035100029080c3e400b5070003a1590001c0305040301941903c01000c040107920300090080c082d450340c0540e40b201141e018450300360020313140168000140070158021900a9006402c0712240342d100c09923005908251074030803640a070208000c0750855040500003000240d12006051180701c1d407200080c1800700070b00c00c82c0c009098000c44250200601d00d02401d00103011115100404c1503814480a01d0602180c0c1e40400360307200c0a0000c044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 903506016 1250 903504766 903504779
    0x90309091609120f06050a020a080702060424020f03010b071205092d0d05240105150f040e040f110d15110403051204143f1c12060b0301 60
    0x98041c04113480d00700c3e000070500f010551500c100360254101c4039015030703a108181000380c803803140544568115440360303007000045440503020810b1964128600d54a074ac0d02c0503203c0d03010780258107138004201c1c0b0000c00010b41014100092034100c3c410b40245055413800401900c1324001c0031061508858190521307803400e54070701549a4a2820050b948441c2c2c49000701280d101c00500c202115650b2095500c0c9813000000450068004038000200e0200d6060001043e2032000b0700380382c000f28900110701403c0080e4040c040d24050a80c00c0f03401d031001d2410b41002e807a4900750740c0d01a00c1d40000b041010144c1d042010120101c50340064007010307100c040f1440c400050206881c5c4094150042c0b102000107107060026482ca480f014480c0d0b0380700e60802e2000043e0541081c00d41d44540710310009451142c105e528204180181d000300f1203428268800d40c05003034050080211aa0300588801b2a03207106d204511400c4030125684c2c19140c103022400a904a5215010b1000d4401c014030040000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 903507266 1250 903506016 903506039
    0x322051816030c111b041d0c040b011710060810051c08090402040f0e06030718050a09080a03021b060c1e070b2a0708070609050c09090309091609 64
    0x540c210340c540345007031340425004141042c0002c03801000d0b031000859420b00c54501800794051030b21402c080e10042c40c3d01580250782d12050540032600981c1c8070f1a2146071a8000c1e04005001071910310a48018034190460204c41344280c043c44011420324004510346d40701c40c503099000d6407400b1740034030445c550780e08001c1245003804008882c1c8807010402c6844503291070001d84014042e480d03c035122241440b00400074081e0041481c1c1c040e038492002000b01c0c0107820072001c001006242c00261507101d103044240902039180d8040d0540600080a4040b51361643c01042c040d40ea031620000d00b030217052959134442c902594012038009007030020b003070b203d000003803480c03400f08038030307082d01d00c4d01144e5034618603203d4080b02c0740303554000410010300081d41c16005a460814113082c2c0503141207031075607400e4014000c07460058116035540c081e02e005c0140801c5020001c0c20014145405844c0280d502a80c0398440c8080c10b0085d50604081038080300048032105100451ba00c0d800c0000b402c11595195 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 903508516 1250 903507266 903507281
    0x2a01060f1e0807060c0506150a33050d06050409050c0d08071e1202120417011e0605100201050721020c150105041103010f29040f09060b12040b09032205181603 70
    0x4140e400c0d0382b4045061010316a100c250b800b00d468032a290303845208020212551580240d000d40d007001040b200007500481c00e29031812003203510004014490270b00d00c140e40503d2200070411140c034480340d45000d852760385000e800c501c6000d14441c02c5601c6c48040f40c580c0c042c2017429606d01c2043c0410710240ca015400c003110100541d00000f5040300b6048600100703008840e00500b400d03076841042c032845c00c0007000e45041c3e100e20700003400740f03060800e002401900502c000c42d1400d0083c101b03003e000e04540e01162562000503089400450000c410350054650030300c0340c148950b10b0500f920f4841021241980d04a5a41103403041d0064a000c1c580c0583c0820310740c5c00c007490100c0d800300b4488100500c014102034240c003040790b10020700f440207682c1110f6254000407031801c000e104080b401061421161742c8164011030041c0b103616650501c0e4514007420246603290b0104007500c4c2007201c000c11010b021140c007103515907500081c1c0211080e039040203031411244100048440341e0103070f0003904041d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 903509766 1250 903508516 903508559
    0x90123060a05070215092404120201030e0a1406090c060d0b01110601121211030d15120f06060501080712051504022a01060f1e0807060c0506150a 64
    0x81c07410b0001d1340011500c141c0b4110101c1c914401180007846030401550300541c0710034009144c841c20040c1c1f6120368460146100c4d01c07403902020760b07d20003164469007280c11500304d100704440c4c1d442c0040c07400982c09411100c00e12224070407480060700008001070310300d120100c00b50103145000b090b40c101001a044001511741404440201110741c00d0080015074000d24024101c5000c0715000e2034494800031640c07407102d08118500414040384070001c0102d07043e122a01c032002601110021110070112603a5000061045100040b0024000c0346009040c45d2440b0310400c1003681c4e00c400055072500300507503013840090000040102054266401560050300d4a85840c00540c1140c0000c0c050b6400550b09001164200071003a6000341040c0c0c01440c5500c000002b840f00f40c0c1013408021401d0403611440384a214203d40c00e40341c8101c1b91007200094200d08064880300d82d141d0701d01501080794102c0c00c843c2407203800000784482c5410030405072030003030003414121090b01d001020202c604c100369010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 903511016 1250 903509766 903509777
    0x1a01061706040e0d05030703050a0501060927020c070911030714070c2102030d022a0a1208070c170a0305210124080f0f07090305010204060905090123060a 68
    0x100f103014020030a40d0240c0840340e580c66a0fa01d00343c0002420340700080c00540010b810040140100768002040400b40d030040f0301c01040c44801d90074030b1800c405910207800e154501c0041d00100f804004100c90081e507155140c10b000701151500d601c8114071044070704100240140703411907600303482c0c0001841154081e6140c01c511540324103a04000f05400340308501c0c0c4d820340d40c1c1caa20842c01d00b807200d00d140d50110700140c481482102c03008908034801850030407030b00e6001d43c24a61a6510b415084025041441411a10b61828900116140d01c80c0c039003541e1140010400145040c000e4862044407042e00014044551007a40c0555441e000405200143c1e0303552402000100005441c1500030050000c88403044105400a00b500da42c4480e071804c00c2003010b4041003800b51040c0e040f01c4d0410ba020142007800c0c0d40b00c0e00c044500d4410380d04001c0c807030b5000290001c0d6481d48040c00a054400442d0001c400e1b90b60340c06e402c18208015081040414040e106a01c50742c9850400351580c5e243c1811300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 903512266 1250 903511016 903511031
    0x150507020a0b0d05191407110a081605061807090f02040306020304120e0427020d02030f0624010c0201080402040b06070b04111002070b0307020114070c1a0106170604 73
    0x7050b940d900a83c88940e5500c1c1c0d200c080125984030040344d515020a0b80e101001051000c3c1c880744034280b8014906000c1c0901c600d180c1200060400445164070f400c01c440503118880314030311503800500c0c00c40c00d44503031041c58042a16807102c04806400408440002e00c03085142c00c0f00d80000d05102c030750340c495942c2d0a0000202140c0103000a600c214072412a100340468100c6020305610078284419000754a840709850800619029030410b0110360410320714155154800603258861011000750540203416841c440d800c80024201c0c002e060140408803410705103400718240c2c14001c1d00090019100342000c2c4090350091581c10b4015001402c0844c640b01810302184c8076a100032800c40d465802482040709000400142400400084914072501c90016070002d6071452580203c0031100070010106460034001d40c007c1752042102c030f1000c40c8619101038050010a640d8006039218121100c0b0442d0040101d201d0b581a0740740794079050301c403c0c0243c0c010304901d200241480d800540e41c000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 903513516 1250 903512266 903512279
    0x30504090606050d050c13170c0607030513140d110d120c021c241803090612060803040b0a02160b1b0601030f02060705030739150507020a 61
    0x81c100600450307111142d0380c2400c0c0440f00c4c00c03101c0007403401d000c0c080288400d06440014289940464210603010250a4003942010381040d1481040940c03106002543c40c08040d0842c000e4428403511540401d806603480d08103014101440341c40320760001c21075042500082c010102c070048003101a06140059181d50340301131008860419801c00714020540d4842140f801d609a468602520703130348a600030b2040d0b69801d14222101d0030000c00d0000302981c0c104000b81c3c1e94000882c0280303046000c070b5110030500700507080c41454002d03200010301c04020310380054224090300c3c08031100d0500031854a407400c00c6040003030300004010801c5003e580c009a203550740c0d1083d6480a4503142e14000d44d2000c4111640c1d06244102582c0f071282e410403801000403441c00b6079070380065a015956141e52701040d01c0c020382503109184009020900e000c89040d010001440450900181e00e045883e903401d050030220304008a52240100b54600810744198091107107025104c0603201810094034a5159007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 903514766 1250 903513516 903513521
    0x3020915220303031b1b03050307021002040b090906060703080f1f0f080c030d020c01051b0a051b1206011e1701050a15050904060b120709090b0105030d05031303050409 74
    0xb8400c0e00007a4a030813540d80c0c202c034101c00d001ea000306503080c4040e10300c0b611480c80c1c0702c0d000e2000005e403d011001c00020510350007401054000e9455120071903035030752150040c101540081d62000d014140354400100e02d81001030446c0c10103901600c500e4481d90711018410100d03000105007202d030700c81000501c3c0c1c01c0c0e401c043c0710708080c0440703c48075507080313080800d11440e00c0f022071125071095112400b03500e261070700031400701c4101d002031a2007541e440d48521603d04011007444150841d00c28007240300240a80490f1501c1019000000c551400380407100b00104462444a007040541207000104843d50b450b050b00c100011440400300351650765041660750811404115200a035180c0c02003101030030040c85030902000c2001b4a202d11141054080390483d032005000900c1c0558646039204d1a0341c0b25010074980909810440e01440d898041040c058134422104441044c4482e001107907915003c1006401030326196140750550381d4440202014050607582901400340c00c000101e64540c150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 903516016 1250 903514766 903514769
    0x20d020c010203011a030106050d0c09031a0906070302190309020d06050f01030b010602070f0b03040f2a0e060121060e07090e0f06060306060a14130f060302091522 72
    0x80d00010303100d61500d182c810560302c0d0140c4090740030300104014415140c001050740e41030180b09400181500841000b9142c5071029040a4030300030b00c9171009204507100c83c0364a442072501d0802e4405036110318905409038050350300030410386204400300301c4007240b2030f41c84460824001400c50450703650310385a04003110802c1d0744000780c50f442c020040c824810b5801e8800e00400261000700303691460701038a90304c40c1c030071805803000340f01000003c5824005c041d0488030070700b900b0841161480c030400e20030203144c2403009000c00c0c507103464480008203a000702029520a10068441100d55010016612035081506040c1c907000c660f20400410700c1c264903103050b4410101d03a210340300698149070a2800d150002400c00564181c0001085115100d010035640c20600550f141a2541280324080c0ea1a468088408592140c04592028250200310b0903404807200c1418031418151501307400c8040e4803c520040303822a401106404240310045c0042800150b0000e41c01407c10441c01131a03a404c0c503d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 903517266 1250 903516016 903516037
    0xa0623161a04030e01081806011404060b0f161a090102030a0f020c070302131d0a030e060309070b180303180f0f01080a091a180601050103140f0703020d02 68
    0x1a8000c020400045010050090325080c0d9007804034038066500a15440a107006541009401804104018010450a20303100034010950301250303154440c040c000e24040b18498843c0c0e003006000106e11104e00112200894140706d86450002141800d03481030080c040d00316400c0d10032806403010100c443d00302034000c111000005d603680c2451401c40741a02e40d82c448944a00b4410050342d000c100001460a049a03815284905480f1545e00c40d0300052000ea100321251110145004401040c0460f015030701ca8440d0f02c450042141310f8061000318002200c0c4043c06a0121000303000441c980302c00350032080520300c06056000940c078082800c68000d804c0c402c90260b6025282c10042c60056078400207a0401d49401c0407003503c1070002895040060803004c4080e944185060900034406441100990303100188415410213211030203079a0380c480e4410015010355000454150320a0044642c0e038a0520703004041602c410400c400caaa2000e445c2600740340c0c2c20070800201001c20300150404440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 903518516 1250 903517266 903517297
    0x302031203060405060f0d030c111003050103051203040b1317040e070305090606060d150807060206040c091802101206091409010219320a1d0a0623 65
    0x1402c409010994201802da240300d03040c1038039a19003a4803402641d440440e0035203010004c250751b03401d04904600580008076082003550280701002e580540140741264420403c84442410403104000c403800705880007480c504141c000700303407010300d01d0039104c4440c0d004aa0305080c0c19094101075070036600544c04003100c81131000070400030a8040c4941c40d8050801e01c060600c624113000026154446d82e2113015005a0710707150081600c1030f64003a0009403015408441545455141c0a559807100701e0342201c0380241040045402c135400c2c02002210060191401c840c1105a4200321900c9180440c0c8070811610394001003122403140980001450403010000f50184480c5020b15142002080034140d0ba0040110271003400750f50f505002d54501c2c0740b9000c203080c000c1000c1e18400d02c01d00d9801140981350013664511131640f110040550008645486440c1c800c0750401400003110481340a40c8002d180d501082524081d0145440d40190f08003080300000030840764100076040b00415518151 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 903519766 1250 903518516 903518521
    0xe01081b210901091509030903080708250308130503070510060611060606180a0e07030c0305150306010501180b13080c011701031e050a03122409150302031203 70
    0x41d40d224201d401800540082c00b15985980300c104100b01d01080c4040070580c1d400c80981418844c1a440014540c0b0003541d5568140c64188883c0c00d801031210400c0042c010144140305005020301c880e2915070540301c000e0b181c0d035620b09401c96000145801d88090208200360030000d40240188210100ca50a000881c50b0030840010608494007a070030150f5070040e82440755aa0b9031006459075481c0786a580580c4512840108036000c0481d4003c0744190007070402d100b903c0390950040c140c500c40c155000c021a54070b010424205075104a4a290036410031070041c000c65100b0769108041840e21000420390303070f680e068042d41a0344000000312000c03402c01000d00010109110744113004a09180007a407520038615480010241844014440001c07141102403020b00c45038441141d82e046401e40e075030110a4280540401c116030501c1501c40e02d880c84160074001940c01e1000b0761600d501c5d0904a070781c107040c000300041400e0440181c05200f00c0e40c0010041e50104005074901c40340203080d41c7c490 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 903521016 1250 903519766 903519817
    0x150a110c060708091003090b040506011d0f0a1a03251a1b01060e0a050a0f0e0d110c060406020a05070803040b070206030a1409010b0a090c0e01081b 65
    0x49140c00e002803040004110550100c0e001c8000d45280d0b02d800c8800040640307560070150014241c01c007004101c0c6110b5010401402404100c41e8100c038000390300c0c60701e05284600c942e55001c1c005c07103034044450781d0030020543d480c1d001d6100403941407101c502090a0304140d0300191038100303804030811200460301d42139480c400314001e10400600360b12240700740c01c0203010784401c3d50b4017503071442c189a81000f80480300401e000b50000300080131151461303007080c2003600e009005003a080f10405042c41c01e01a0124200710075219100c1c11071819006444903442802045a00300f00f0381b0240c8900e4429107103106aa0b5a1f540002c00040440340c000308a900381e1454401e08001030b075803281481c0e810901040002c070448201f00c0d00d01a07030407290b0960366030701d1040d1440108a0300d00c900c0300c012900f03000c10210150552040e007046034210340300c0e01f4132030391403122a040d18460004100040d0700305c21850700b654000d03c001d90f00101003a00d198886a18000e100b40c29402c051150990440c52803602c0c18417 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 903522266 1250 903521016 903521023
    0x4060b040e070c050718180209071101021207050333130f021209060f06010804060507021e03221a1303140c15032401020f100507020d081005090402150a11 68
    0x151880c401f542c0d1090900c1c2d40001d660b024008001c81c1c144503100c11070380540203082d030458100a402030844078846c180704500a065820456048030610554072450000c641390050b140901e000022071000402c00a006028504800320180e000c0991604a0710720384000c00c0c00500054502480034071513500e0410003881c50180090511580001c40c4003d012244c0d81c049682d540c0642c2000011480e522030a004034509402d01201400310021424421524507020009055440107024800c1c1001d100300500c28140400d03201c1c00c0d080c04060405083c0c10100c6402404040503485440c115043c0e980d15540c0840d86020394916158004400c070209501d040720021054041620301c16003145407031001036484400541c40c05c031000c6041030304007100c1c1c0e00c00c03c07607600e80102680a40b41011a12240b1134040e200503180070003d4000ca0280403070191182e0500361151800e900c2c01ca0300c85242c0340c240480350b00d001c1c009a0300030000138800181030001500824035106142e0f90100101d1241c81200d04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 903523516 1250 903522266 903522281
    0x50703060f080c0409081612030623130603020d06050105180609060d0507150908100c1d0a03080711030d020f0c0405090a050105010b04090b04060b040e070c050718 72
    0x216000320340c0c2400700b20000500010780d200c0c10f440c00101318006050000c11405014903420000040d40906000c005040034403860300400c03518103004960319103507065211415030b02209840d8050003050081d61400c00403c2c80c4041c445040001c110f502d0750041040f406030f040d01552510f071a1001041b00341055403484800c262000c1441c950340c101030000076012040a4101403003006501c2c0740c1400d00ca8103200000041400025140703031b00e500038001900d80d80310380c400c83c0b90320700032006015094030031030051104104160703490140c180030309503284078541010901580c01c0040288044000348030b80008080f0307280035074030f8101e0304070b02d44080601d03000d02c0c0c102c0c41007103410100d2904c54202c000a01d0810700314040341c01169650300e4004442c03510780c61481c0581a0340c01c00000240a81064004109a0b6a113a6003030003e503118170203004c00d03201584190000c07044100000c020a03d46501d04941180162401000c42e24907070321a01e00d003000541009940f102507950728285040213200f0400b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 903524766 1250 903523516 903523529
    0x60630030f0309051e010e07090b03060402010809030d060f14150d0e212206051206040f0f020310060e061b0a0f0b0f0703022d04081005070306 63
    0x20401440d40c0c000e01d18420451001c061603203498818081000c00d0014001d14682244500048151102c4850180c4102d11220107e0300800c040450031602902801040c250301070003c081c9915290300444417440000c00600f0341e80801d0220181f40655800340d00d004103c42151000300c00d05040ca0040a03001d1f04031720912500250554040310301c07800d010703034001a03909ea07000942c0c84004680c680c20301c0c2c000c00000c1504500301000c0c54502c01c440000c0c005829885401c0070305075010034814500d28010740212004203106100c000c2d600e14100e692035a008001070008104444034018100996078091a440043c0e41c0110030400d00300f010002c48030040a4602d00149200810030110b0614440c1031031400d648021a44000b9903d44200607441c0303519407042910075815030500b80b9042c0c1d00e0040e5008004c0c01c17001004650014030034003da031044009040707000f000d140c1c0711811480c0701440c43c0080c155104144000907250301c0501c0f10303225001d803d100108a502d86407000804542158000301c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 903526016 1250 903524766 903524849
    0x11011109011d010c12090810050a1b020604080d0915050901181106090f130b1f0f110c0406090608060c0f030f19020406050702010e1c0215070606 64
    0xa449982e030002c50613260035000300c010400203440010071210103003103400c01c42c214030904650411004007688120710851180c4003c01059041c04d00c00c5043d020403003580030040e80648045004201d0450040c4889174101c2c000140c1d41259039a0502000358495491480e90b542c0c03800c10500700400e00482629540380c0b401c090081c2d00d2031740e4143e50041d0341c10405010322070115070061203882d071402d001500600106030062400c003042000d005000c0301c0310b40758005ca05901404402194803030a01d500d8404548802c0c015510304441190404030100c07030055a44102d154010780d5846070f10a95010303100d0072201080707003420201500e02e00040030b040c21310b0a01d82005120101c4004006070783e040824000401e0480d1030fa080001c10320084802c5401009200040c0010300b240c110000340aa076200b82c0b58100c4020083c010000e02c6800794201403012900090754500510b80701c0d000109800007641e50a06001d40343e1940b40807120103800014200b0520703100a0542c1c950068013050011007404032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 903527266 1250 903526016 903526067
    0x100f0207030b040c05040e0703060609020f040e100b031509090601060804080c03070501060e0610210903051312051002040612050402010c06050a200c03090d031101110901 75
    0x9650320641d1001030a00c1e11644045010028001d40080080500620130700680d401240300f40d40b40c4203030b8441151024500500012072400c1d0b40255212401c541c060b041c02c240c601030001500c0d00e070040c44550440c4101070003080b001b80e600041c50054110701540340d0806045c00c01d100e2254400352034207080d5032013500100708680c0c1c01100d00358000c0d8404021900e501c1000ea41d44d00d14054600010029400c010010a00c4075030540b649100e5001100c2107400b102c1c0f160707000c3e42c850401c0c0c88003100315524640e90130030b5018107400207110540b0074030b0170764580280e1000c0c1d20030b25072164000311003010b1201c902c9014403400304a0b0010b005801407007180b0341071030000042c00009030103501d41c0a007611100041c0c1568050030810448541240003030215140c40c080d0303403000b0041d651209440d0302482d14518180d0b60b4140c2980c0080e03660320015031074580c4801c200401d03581144c8c011420450807034008069040280122850083c1c42400692a0903d41c0005010608521012000d298030940c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 903528516 1250 903527266 903527297
    0x4060e0411040207021f1205060f03120f04030b01031202010e3d090629030c1e030d0305010e070507020d1b0f171506010c0b091504080910 61
    0x100894541c404440040c2eaa800d14800706291421780f042c0721240190320080f0340003e03500320541c00d80c0b40000b04c004210503602d2804015004040c0d910281e095400082c030780842d42888801005001c4100328813030308040d501c0d03640c019141d909820460341108032904e50b1800d19024003400b943e440c005805066242c44040c1c180d0f0414030b01c100854030341c500e0030480c2c05241c030314840d15402c10110782c801401010b0b254242000a41501d800c1000354184110b40782c2c1862014824000780088010080d203800800e9904000c048032407459000340111000c0505c070144e07541040030038001d0f1890f0314042455803410703604d00740b2a440180740b802402005c008580c010f0703a0b07030040c40c140c0ca40d20071030f050b0031945901c20016480025800c039020400c06440042140340d10810b6009604401c3c000f190f103654a60882114200b8040c0c91060104400c15481d01c0094484461160b103e00ea1800b11070003040f400100b0403072a001581d0135101180c00107200c081a0500e2000c075030001d800740c101140c030f2115000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 903529766 1250 903528516 903528533
    0x30d0f0507030504080f07020a031707050c0a050a0639060f14070305090a021914150f1c02070305040e1501092309010f170601050f21070b0904060e04 66
    0x5031940b06d00704009010700456849000daa0051a0040f410002e4450a8810302c2c1c0242d00908080d40c2d6407140300200b445510740100d42c61305440019120b4000300b89045019a00f0054012202d6220440c42c00340b401d4042c44608071408004401c10b100c0130360405401c10300121001000614074960520380c0d401190003072041043e800c0341e22450000b80701c0e42d4001c0410b0800954402c02075103c0403d0410104000702019190182d6900903103090007200701400b0040b000c02003031844480c140041c402d0001c400354803000340492405149840340d460724401040c004a9005040403004503001050074424a080d00c803140307900282554601c540c226800001030700002151144645400744206921803000d8420f42d900048200a4488080e030758513131000d2500301c1041c0c0110719020310703410600d03000d084002407418100c40003d031203580505040d90a011215441c0c04101340150b050305181e0340d0b400c20401c10b80000b8241e806a1a0f101e250010401081d60403da001c444d000340001c003400003080600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 903531016 1250 903529766 903529777
    0xc1c0506101115040803090f0a0f020d08190503070905040e0705100306080a0f020103230c0a0918150b251403030901020a090512060613060503030d0f050703050408 72
    0x42c00e0045400342444807152810b18083e21010b079115080c0d0074401001040d0340650300032a410800d541180d00345c04000c0da030398041c2e500040c00c0010100c9006003d41044880413003a2801003100c04e00d040900c036402d021a1504408000028a000003007124150344008104041c040c111402e0100002e00c1c00c2c0c0a03514080d9020f62446144078604440042d0300a500a100a281490603542c5200140c10b080d401c0001400b010790109050508500250f070f115884046044401d00030250141c80d250000c0040c1d4004110920600c070b43c80c40c020480b00701c00c9400720201440d82d000410b043c00b1141c1e8034900c0c0200d44e80208140403080c030034801030041c2040b02c1850000001d004402c11049401c000e5154000c1910a44403404004144140c031032041d002401e828000d502c07482051542c1d0002e00c0490088454102000c0c0c012001046043c1f81080010030654030000c2c0129940d078407000020304552000c4050340002d5074a141e6071000d56542d000d11a44496182001c0286180a03120605140b141 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 903532266 1250 903531016 903531049
    0xf150902100e01080115211b12050106080c03010b0703050d05090c030c03010204062705040207050d0e06040e01090c0c051603140601081f0f0f0905010f060501021b01030b090c1c0506 80
    0x2100050240b071000754040904548020040c62594003141000349c102c5040d60114245a400d00d4000f0030800d020300745a40c0240c1c1d020707646600e5a0b203000180141c0c0d801c03082d002c07020401c0c01c00480940c480c3d24007420380501c0600015058240443c0201490100124103040c080d0340103010401203d0380103040e1407410104071180b40500840540d0380e200340d0045400050380b00e4400700c0d082c130901c4000560b0a43d4840b454a40c03160500824007002107501a80c4035403081007050344010702514449402440c00f007240c1f81440040c0c4110f0345d8556007000c250309502c1310002100c900c00c005001c2d000000c100d03040315a20180c8029414820a42d450309562015056900030403014a07070b5200305540480c0306049404020001501d81141d0207000d091104004c1d1080e40c00e22004440300010791180c4002c4a1058008005403000030070f001c1c0c0c0403d59882c040c4e060564401217040306d9110148444d02c11800c019005590b9465090780c810161078a810320320300645450304000c026140c80c5546008501c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 903533516 1250 903532266 903532307
    0x60510080d170604090c05030d051b01150323011a030c12060106050c0a050601120201090803030f06042004032108040c0b1305060d0b01030e0a0f150902100e01080115 73
    0x5641059480f0003084d60007d9050f00c242c2d0424042c5541c0140640038144080400b20400003201d6100c500341c40c03140713203249095019048108009103044402c8040003074134080982291507044c00080c210780801c001c20100610714003050381c040c03030244140c1d10405002c40703810840500403200e4a50300c1105000340810f00c1000181150011030400c00c0d03010150303004045901c10b6031a4440c45070300e03551400d4101d010820b02000418150804030a892096180000c0e09590b0794800c82003001500707800c803620b8401c07180840031400c3e01c49048000c2004e14054814140101c84c11044c00800150401c500000c2040110601c000142c83e040b081e0102e6910b581d64603107440704003c00428402603a44540d521150011390407041442c2500013107440760702621b00304008121a900302d501c4643c5040000c1c10f01c141c60059800280c0446524004030f0401c841c001800e01c803a502140c80b41442c9007a0f600032030743d001404403441d81c2c40800d141c094861508a040718040305034000d040a006100c21000050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 903534766 1250 903533516 903533531
    0x60e06150702030703030f080705031e06120102070f0b100b0d0209060d0c0804020307080102040501050a031527050a0b06091e0303040b0a170127020403060510080d170604 75
    0x300882034034140c5400a00780c42c0c200356689400742c50300300c0c0c0c0541c05010a06000000d1002070040c0c00b624030030304e850400b01c140c00741490702c0c0c1402110010306050f40241000c2c2e40c0d044c00701c000d1000d4041d403449010540856201c80c184200c10b00c1f4010150314414102110621202484105507900d031109004003584030003207140026840d000b030394a52207915281c890412902644803510600450003507064600b42c5886001560903480360b40075142c01702d0310070012202e02c0c034800c2e40100d00b907403c680080300043e070300d448104107900341914003854004440c80750141c043c0074900c2016040b00150340d04001c05045400858000d01a000c003451095001e141030910307241d003a0440010a800040603640c1e240c6c0c80740482013841d00407940810010f48a0807015004211028100c1d0680381c010351600807110b03000e0744100b0b01c20003620400303107425020320000000440c0c1c1d010711801b80403008900c1d4411404e0011040c41d0180500080c02002020303403800c405803001c80311185d084036058502003802c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 903536016 1250 903534766 903534799
    0x201051602040515122e0e07060c0311060912090d170d0c0c0803010302091e01060207240e190e090703050c01080702070603020a1b0b0405010f060e06 66
    0x5840c0300c40060b4100b07080c5010800100980307810503034541002c584105078a60340d0100e0b00e139141844000240d07114040409040c02440c007196a030540c904103e404100542442000ca042112551000010600c1401c9103000c00d07030842505074850000c0d400800ca507282240d9400c0d601c000c2d1441d2403070034090004007050703162580c3c6a00c452040d0001d0410080148400040000d50700402d01410824a065100002d0620800c000c0021f690071001e041c0c01c603401d503000c1020110000e80700256100c0d1001d800980010499201030007001140c01900c5401c0c0307000394000b41404241510048140c0b100540200710380c22002080f40d0000580341c180e401034141401d100740c80d03007a41001040004040401c1150300000840e8820380f0310400c10340350200044401035a80c5402039036000090703003013441e040c08800d120f44d018101e050b40c50b141075003d0075030003102c5245c0301c201d0030011354680d0031a1b03042000f0301c20240241d0044101182040002a1800039844092000500181d00c100401000c52518 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 903537266 1250 903536016 903536047
    0x10060c030c06050915010902090604050415030f03050d060b0f030a0b060904021c060609060807030509120301030b07020c010206130201080c0f0301150210091a0415020c07080c060c0a020105 83
    0x8550b001d0340c20007140c204403a8042d030303820b280090341104900c2c2d0b000100d003903103550003903900ca000d0241819090074103190400c4041c011811950762150413403017000000c40c4c03c41c08004103880c0a81c880c560350b01c014400b0107094034400e803c24668240e00b0002500c1c909030540840c1d6100c60740f440000751400034140058064881d194405600c1400403541d1000841e0020041d005001c0e1040704100b11581d40300e080c0d03809000d030320407200400c02000c0000c1210340207400c21795024201b10162000e8074912101946035400030303007007a02c055605d038040003900c039010804103007111000d000400b920b2401294178112958040c10080c10403141c2801702d0700c220b2900050310b4000c03038140c1c5499142d68440c013080c18102d050549410041c0704d81c590045254a03144104007a1640107ea130320050384011a51780c00901d009001201c0c814400b0740c202d03803070007403d01c044c0c00715840704030103400ca803494949201e24140029484070710821042000b03090089000604881e450b0342800d10948858107442c03003168 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 903538516 1250 903537266 903537287
    0x20a03030804050a05071e0e1605070c0f06031e090b0601210f090c0911040909080903010c05040512121b0703200a170c0906030309030f160b0310060c03 67
    0x60303124010000c100c81d44202490500850b1f9503c00e524011381c0c0315980d40740504107450302101030075100358140000d44038000a0043d40e014041e2603e0095883c40031070f1061001d41c0c464000652b40754942d180184840060901c4c10b902e410090001c0099912003440712034000c0c200c40e0501403034080c240c000f107001d440b5141d03a10035950010002011070841580c007078944d44004aa11050402c000320b0044d070503120355403070300c20403803c07142c00c19060418400041c603c0b610140c8030b00740c1c203000003107543c4d80902468a0787c017a1a5103194039035181009100540040181014072604245002c000010b030f0030f410351b090941c010000c44088501d0310280d40c108000b075040030385030317910071354a070000e8058103040300d03034415030a071000e4110a650f200810204182c01c2800200740d00600c114000700e00e0700c0d40c0080d42158008054030300d080342d4640064542100303200640340b00d401818443c2181201454102c00400c1c00880d603d14602c3d21a17a00d411303040441c0500c0c814400b04c500c0b01801e05119012440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 903539766 1250 903538516 903538523
    0x14061c1d071401021c080408090f03030a1805060702010e1903020a17150c0703030504290405010c0e0102061f03120809010b1504330f020c030a020a03030804050a 71
    0x4804035100d403a03a49040c101c1d0780c015800343c82104542108588010310a030b15810040c1d46d401c00e240c6840c0d071002000d0348240728099210203121508100c0346c0c4e09000401860304031b41c5a40942c0da60789105108110b66560005114110504c00600580d802403801ca11400040f140703040794000c4403507141d4000c6030030340010b0340103241c1000104406513454410380121401004076044080d8401c07122403211030403500c1c880886014021940024000c0e0000f6401901c510344030612804054000000791080207510301031442002c06100c1440428071078100510a076181074082c0d00c00f0400080d50329503001c0d02d0840d407508030309910501c01880b01d03029030185a05c1020714889400c2418003d01c0c415090303e001109510f0040029001e19042580c40d900020503100709081514202254076010b98881e500208903c0c14040340c1c443c145040300720b078841c0040b51a600708410328081e00034031701603160b02154065801241e009000da03444181c014101d0780d0600d01130069a56918005051000c000e1000703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 903541016 1250 903539766 903539773
    0x21c141e030c0a1101090c17280b01090501030f02330d0506010206240103090507081f0e0303042a0801050106140f090111160e0114061c1d 61
    0x4040300c40b140d8010030303e032406035440c0d120350a08209180d08a8001440042c20812816070410205c085200c0c40344815205a094415131f416121060b08807207a21051203403960141008802040481d96840c0d0150181d14020801ca40c15640ca00e440c4080b80407020340300e00080803901e100c003664840c00e118950840c8810301c0048101b0104c0c1c1020f90401301025520340e04000000b4015440002d940303200d0560381d000310b22400d98001070502c080509078140340c100354452070070f140415000c01005005005d050014a10351341c0c21090504100004141e0f940c2c9035040414900c0606800415650000d40080b81c1070340102c180301d0301020303110407070412213208107a1080020b0303442c10642c0b106040310a183c5811510862039000350380584640b07401c01004c007030f0a0081881a51042d03d01c861108880c40440300c000f03807800072415a80c0c1c52540003a05610000e8014449610a16401e0003e4507064070b0312401c10320705c41a000282c500038402c5000003036680f0500040e00d0013020101c5140d51805054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 903542266 1250 903541016 903541021
    0x1713060314060f01080c0912070320060c070501050a05070b162339101107020609220908031803094c021c141e03 50
    0x180180ca14840c070312180081510000b005070500c00c0d1014401d84050b928540035594000750340000b90041c004140d04a814503d540c0030a01d010040c0d94060350082c0c00950081da41901034507641d4140b00700e4140201401d022041104400241c0001038403c242005500c503403c5c088100d50500900390007401190403c014006015040250a0000c2109076290400b440c50b000d40c507032010302050700303111f000c20042110b0f10700c02514080c0c0300c1c0c81c0254501e290190180d1041c00312600f80030300c0a20340d007680044001c500c1b030540c14864840802c481488207800c0c124660002401d03401405012030050000151280020301030109070500840286002c0226001d01d05010b001600115000480c811942d20715020359000041507410300071000700055100c002c1c040c40b01c00c0c4143c056510011200018440c06510103da4a403401b0310318030307860b139040303007000b01e5400a15150306070300103001104101e1940c0100c00d038000100002101c403480e82596559402d11071040c0e40c0d81500390a030314060003006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 903543516 1250 903542266 903542279
    0x20a020c0405040f03090519140f0910080d170703020a031b0309030e0a0f121b230406060806061324080f060d1403090907120f1103041713 61
    0x4280066000307a40308080d46449105001c4002307030014010b10350f07800200701002005040d21241c0c44004001d0503029034000c0c49000706000742d01c15a11005003820258080c80068020007085107080160b203007074041141255407101000c00040d0a40781010340002e20310380f15500980064074168845550020300b0800d81900600400904504170006019941150aa450310741d414105654031000d2242405181094600200031643c07011120130702010022820640920700c038500030130340310505501700e82c241034041207144014092940302e145041303428880f0702d6121100301d601c03540c02d907185c554441d00c888420f4000100c03940030001c0304000d412a0041220420f5001443c1d07081341c0c44185d05070f143c08030301d210203410440e41160042e508840e520301145e169002d480c0000366070400d980c43e0000040110301c1a41041b94104007142c00f94414004001d89031051048e50702c000c400822440c1e40c2054808014800500090150707820010110a0860740504440b1081a0003450f59641d640e01c51 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 903544766 1250 903543516 903543533
    0x1a10032d0b0a0b040f2304020c0a1b030317150423090f010606090b0d150e04030201091712010311060c030310050f12031b1e0604110d0f0303020a020c040504 69
    0xf0191185409100018820300c42503010028001038805012a05046d03000d01c4025080300d130006885203e501d0303c910204041c20300e091040b441409103903100c0ba0560030050516600740d11f44109003808401040320f442008003450603480c004881c003144d02300e071001d51506000710040300400b00130034520500028100008448801c0c80003c0000c0c0180d55480005681421040c802d804a404c1d0070088902025000c0c2e104240300c1064204603d81213841d620780311040038080380c0480c00340c1c8d51840c0740800c2c0400701a403850044000c0320701e070340707030400c45030340d041540d04c044c8001042d100c030316110142d56580356425601c0b04c41214044030b84070328098503080b44001080c82005d0244022110030302079403c01e030030032140407a1840000c61a01029a12032425a8080e00000c0414003900c42001500c80903540074040d1480b841d8010400c07401d0508041d9521650081441c2c454044002c643d0001a1240100580325415090060711a00c0d0390b0320503800d01c00f05640f03140c0c0c400e1425040000304107042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 903546016 1250 903544766 903544769
    0x3c07150302090a0b0909010b030a02040b0f030f1b0403030c0203010e0a0c150c08030c0703090801330302010e120a02030d170f0708011a04091a10032d0b0a0b04 70
    0x222280040540e503420740e80813912400103401d820040800060001e00e018000071900240395050040c41c00395240d07290102604810030100724481c3c00014401c07100c02000d006030700040da0444402034102e044400c0d1702c40744100e20004051041c004009029035a080d8000c0c3c0e40d100e02881500d2100740c3c14a001c01a804040c010000b00800d11004206164030400d0766801070303a80180418a191154a10b000d216004150100d0400c1250003002c11202c9084c0201c100c880d04070032200200029000365040001c1402c251800030300403802d801c2001d80e90201480400d10010745001c2c010008039100c2074249030200030302a400d0320600c0d560080e0313a03500c419011195510711540c200107854804501c89400740c1a2000300c00034000f18018820202d0444c441c0510180303142006150682e02c80c00a0309641c4000c52a448c8160405e2042d050b5003050300c60488581180e181c00c200061800d00800c525205c040c490712248911000511800b48c00d591246402800042c1400c0049130b442e0070b0b1400b103a01c10b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 903547266 1250 903546016 903546019
    0x9070228140c13020306210f1203012310050703110703030801060311090d12031d031b070303080103030e060403051506010e1804080a050412143c0715030209 69
    0x300e107203c3d80410b290300c245da0042034003d0985844014205643c001035500860521150249020641080c1c408020540c401c8403210405070f22985085400204043c010121842c0914000c640e4a1550303614070605000b4112814540d40b6902c0a0804598a0110a201c1a11441083c401000303040c1c0203610035049032001d40d4107200d070b44070450b0144030700d0264089194016140102040005000742d03800c0109086030b1400249580e5070700c000c148244030070031170040b80380c000050301c3c0d40c000e5104402c810280c08450061031050301d1540c0041249105120103003c011520a400e651a99014110b4009581020880d04400998107a107c1c480310182c6140d030214201d142006071070b040000d440311070200b000f41c3c0c8200590f0350b6142e481c5d90360722103900101004010807011078501e544038681d02c1624003d540c82024030840c400348618081201c0d01511010300d000000f104000e02e81c910203110106142480d001054808411070302d4800180c02528451441480c08050950f241d409403400220 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 903548516 1250 903547266 903547279
    0xf0d170c0703030507110a1809210e0a050108012d0b030103060c03240612020c06090f060a05010f03060f0e03211521070b0708120609070228140c 64
    0x40c06c008100003c006842140b030a160b00c025803c0c80e034841c45d0304c14221a4001c0c4e1011052283c41030a400f00d013940c041400b8041f1b400040c09003590304180004030054039080c2405811541010b206000590302c2d03200741001c190450140d115541880c03803000005008001c0c02d80d840c5e50f164070f03040010700100b510410001e45004054805070074003408120000908020710003045d8103001080754055034101080a46075020400105110410000c00384210306075800340ca00880c21004140c10710b50b0103009208030750309003001441401ca007800c484e8112940070600040d040280d84800e0081e005000d0880414000030522035140351400444072000b0301b851624034030342d68510140400d4000007242c1c0039041603868800106080094204a404247e07080032188016034070391942085034491201101c02c820080343c104403010300c1c5100103810500443e444503041ca40032800a60300c1709101c260540e00244080003c0300002480304594a17550071000b2113140407580301c2c40c2560741d4000080d240c000e08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 903549766 1250 903548516 903548543
    0x1020d140a030207020f0909010b1512220c060809071d06120f07080c09070f0806011809060b1207170610110f060402040b0f0d170c0703030507 63
    0x38420500444241000c102140c1000d41d51903045000b500801400c9030000b15540342c17004244e907a01206449003510030b00101c0c1541d2100240000c4040d2030940d0003500c4003e211a0341d0700b41742d901e10582d000920030807110119030786040c0d00c510000c5601c0702034040f0250f40c0c00403407220360015406100c3c0801600f110401c6550b00e00d59000d1860658400f69030311544c80204106180040100300654403050440c2c8040074845149030620445a00800c515030043d0304001c07442c00c00081e07150340301c0c24504103546240b820b0b0034040c2c14518002d0885041100003e0f0420b1017651681d050400b030400220100221502c2d080748000c1c551001e4491a2243c6800300000d84040c8a070702c0c40072501d09010510036164031000148400003000c00181c41c2807258003035113610114000c004c130f0015007034034000401d11806c0c40e0043c0000c541d00604414010f2202e8204003031b8545403403011104007a4003101103103450800420300042d50140105001c0640540740002060646c05800b9110680c02800c0f0002500e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 903551016 1250 903549766 903549793
    0x70201150519090c0504150804110d023d050405150301180f020d1107020405060a080d0804170705242e050406090e060603010e0304051507060903030203060102 70
    0x361020500303070b045614460600151216400013403102c186410958202921100030360903600a0075041c0c0c0000c0c1080742044140130840d04407255a013408c2e00c0d0684c1404040d00407070b8034008884a26a000025041c28402c0d4a03020201c1c2c1c1e0074010501d00d080011540c0e800c4c01011640244600780c8502c102c801f030741035600e42c244200d0741220245030b14180301860030382c90103000e08000c0c28018a041e500b800311455402c594007802011108105c6003d560302c002e071040208655014280700e0280c11554400d2000301c500044807a982c3d07107181000c900030355071440d00d200c8181071721030020105040420b80300200500002d0b211501c0601c040c14103501c0000201c0c45005440c11911800201e8041c00215051111a805515468000c6000007042511140803070192034840e0301c0440d1896954100c1995104144080c41e008401140240942000707060410f41c1d9020302d0140500c80c0c806040d0400c181d0400700c04643c03009901000c24001e036416403c0c00740080d00b0446009001d40260036000703400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 903552266 1250 903551016 903551029
    0x70906093803070c11030105090a0f0c0b1911060c030117010e1209090708090307030f020102120405100b03010603080304240f0c08060102030c0a030807030e120702030d080f2802030702011505 84
    0x1000c02800070142c0c4140c07a11081189140d18003366110048040b0100700801d40c14000c0032012026822840881072110009008400c000c24038261504000305010000740d400007124110b4803003001410007c07100400d01c50060075030f0b009015040c840c00107503a05014807030b4042c15145600301e13068081c541d201c08094032010401ca507441142d80080020704002800b07500c0f071072500c0d011403000508008102e05010700b260350540b01640e03a46d10034400030341e0a010a008250308401c003600280282e40c955a20310142d03000190000703015907000b11100c503400c4400541d00d20f0344154002e0a010b01c52004442c2c0d001040c074078a0280c00543d18030001051540000101e840718550ba40c004c000500d442d880464114074098103181c105a12166000720140c0204010240b071007410018236500c1e03c8a20400d8a4100c841c0700d04814403c41c9810008120300c0c4142582c0d01101c0001d000900b5100020405854a21049086503440c8040103110381d0b80d6056002801d6955010072600c4501d480d401000306 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 903553516 1250 903552266 903552271
    0x16080a061b080604050403091203110d050a210b090a0e0705060c0d110118140606010c021807050f0c0102030a0f0e070611030c07030b070906093803070c11030105 71
    0x480d109034040f500e103082941c46941c0c454068542100c0c40e503140d0580f0906542c0c400c1c016000501485400000d01f4020b00c0080c00f509003d06102c1c0c41c10b01c0c00f08000e013100000205071a60400107000b04045d15000d504004070384040140b1424062604092040042c2903d02d9402c405118504000c5003a00344030301180d2015000c0401440e04120310401240c41513052100305199540314460074030002d41c8034601c00c100074072801c0305058280400d007410f0702e00350000340030504100d03403011850050303220b04a6000c6004014687c04a41c2d544d0070030b090310244a20b401500c103402e80050f0b592403550040d03001d54050200b4103018440c00b507000480c0004e42c0d960f40703481780c40d94000084c10441c09009060b00b80317182680406880c10710314403036036060a100607a40250342604549040010141c1e1282c0f106014207480d041043c02242885010140a440d8240c40e6400c0155200541e002e61180101103142054698045035039142c0100010545d082544007244c0113000c40301d0031106450180134880c13 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 903554766 1250 903553516 903553571
    0x40929090c09040b131d012f0c0f0d11060a0506060f0a170f01081207031409010e1e100e090604050601050c060103060606090e240316080a06 62
    0x80c2000d40b0042040010040d85074013079408591024011039a001c01d0145014070f4001805050000ba04100c6060942e440807880c10004402401007210400c086c03005800600c0d90352607803545a90366400c0061900011082d800070740d1255640104a15500986100341071150704141d94050301c40341058016200291006940540c092224501c55507110001c0c1400000c5450304040040601214a15010301686c44080c0d0513101c4005018120003000303034141c8082e140d480286000c0098070010480780058803841d621a200160b1000036a01c50740c0110007498008111601c0c89400790000b541e2505103001c003a00941d10100d441007007038021201b80c0410000a009020a03a4640007088020039000305818144002400b4003804203608000080c06140304400001d441401c0050140c400b10b101c2c1d110003401000e40701002030307240b03d081c01460a405040c0c0d041c07407400310200c0040e050200c0d071070300c04240d0f42d29840000307100240010a00c060300c0c01910100801640000d146c2c2d04040c4481d01d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 903556016 1250 903554766 903554791
    0x604060e1302010513051804050c0a03171303050d021b0301091e0602120108210304021003270503040f0803090307120201200604110406060f0c0804092909 68
    0x5401550140d401888481740b00c03c54903410301d48500004121841600c850749412008408102c2041410410002d40f030004442d14004a0f02d503a0715010b54058509580044040205070306414402310500c03200a9035101c4103a4005040401c40295201160708450038150310218207046141010b20884100720341162054610011504100f5010710300c07840103e802c00c1d420007179608038001403004240640021005002440c002e441c8000c007036401c29000c0002d017002003060100503580c074402003155a0700c500300400d0010300c01e440c41f1030198040444800210004524004003d400b100070020351342603400d12585aa03c8180980d41c0f40214026950180e02401040c410065032110941000c2d1051400c8103c0000c8144400101c0c0c014101c65141c6501c08800c2c041003146400e0049048502581c0030041149030100c01042c100d0062406010300c065540c000091001140032070f00a040d180e502488011140c080c40d42c40c51403440c18404008400a241128030301d40700788414000c20601056 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 903557266 1250 903556016 903556051
    0x170a1208061e06120c0d0903050c1c050d05180d0507020102060c0c0a030815040606350a020a02011d0a020306071403060f010c060509011509090f0602090310090b0604060e 75
    0x28860a100140c55070306031205c1800f0030f203988803c9000c1c100105129546150300d0700030352034000745080f80e0b1015212141c0c10f11a03101c0982039001e000c1d280c016a0180022405440e100031a02681300303e07101602ea41e000c2d424100f080c80e500302c2d00030300c1824800c0e82100e801e9030340e90400c0d1407640160f400c81201c6070410400d20f00800c2c45054642c1d04600c40c1095002e0451543d000079084811550000c030200b43c49440d0c00d1a0b85400d4180071120552061a04085000c1e4000000403903900501c0c03c00c03069030124158128510035405010180c0402c0131040309580c040030113655034002480100e20900c6214001502c6034411250605d10314045502d1f142075031110010840ea4890400b07040d030410840314401c00205009000e41070050008800004103043c1e0892032400c00f0300143c0000305182d0500d9128000158510a445441d40d00300b0781c016150034121b03000038100394410340c80203031060600781c0050610050741c1c100c0d0b0040e181203034200651070352074600104907082169410a00c0404941 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 903558516 1250 903557266 903557287
    0x130e0105090a0525030501060e0402161707020d0503070528060c2609010c0e0603010b1e031608070801060e010c0203120408010204090b0a030507170a1208061e06 71
    0x2140c0003192625203501340d01e407903103051400b40303905a000c400080d180c000422005401c0358520502200664065107003c00018850324030740211030b40140303404007003c0002165081d03d816103041b698018181c0385501402c1c00c1080e6a0f4200100076513850041102c044030005200b50000c0d0a80c90350030800040c0e4090b034480100034100c40b500e04060120343d46106400f0b03a02249030803030354103041080c812a1305000716454210b80c040310aa109002401c075024006c0d6807420b01f9641140c4488440c2541e13007120b480400e00d01021110010800c140100030312084404120b503205100c030307036a600c5e0310081d0389805048840d0b070400e02c00c1201103100200c000491354840d44c00c0c594041e00150458444020400003a15036922a030312204541e507020400b44080c004a009615030400700312542c0364058199100c146e00c441161085108007003021035001e01111062004030500342e0450700c0c1c19405500d00c034014140c200708448462080042180902140d043d0038031103580281c014100d242040600030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 903559766 1250 903558516 903558521
    0x140109091a0c04030206310621110f07030f0810141810060905060c070b0703110a080307030f0501031106071b0b130801050606033405130e0105090a 65
    0x2d00c8508640800c00010016031a03a0004003140b41003600f0301018920303a8400c000811f15000c1c11113a0108a040041086a510408030b082c90715001c080507100e0449480d5000080c9142c50006480c20350114460841c404098080e0081c0c5001c2d4070358441494074140c04603400201214540799020990b00144140f0860850408840c2d82c00ba010184000d02000c02e0225070030200da2079034015150210900400d5400042100104402d4507000c2c11f00b0000300000da2105803d00031901980c1010031a08141440b071800315040c242e40000f035500e40503442c20400c0c4942d1017200d00d6804a801d106260f00100802d1047c5412690802c103e02c645d040358004212840d03101c80710649026101e05411060a17901c58060f00080682c0a0380070350760112540101900e00d440c1d840310381d030f5915000030000700d900c4000c01c907541f01c4507503140900301c1c0311280340300100008491161302c07590032003000c1c100350107401000038076a03100700b81c144480703856071074020502e007040900505411006040201d0300e1007003982c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 903561016 1250 903559766 903559771
    0x2100f1e08040b3912010f051318030e030307170406031b02062d010801020304171e0d0f0f090201031b020318040216030309031e081306021c140109091a 67
    0x444c641d031810203c8440101403840030782240340b19400d5407100304424a800b0308084a1000c1480040c0502c0e241d40c8820100c3c07022601020b820b0004841252031320795001e00850700b10580c498810544400d00c2c604115440e0051b000b41c0011a2520b2171004408100c060395850102055004184966a01010080d01c510f805410b25000320b03c24890b425816801400074060528a000103807240352a0800010080b801c115402e817481d000c000039800c204000d0508032555081400c62540c031901d500b07160700100f0031507000101c170900e0442691808245a0400007425001741d03020300015100d03108000000b290101441e02607403003048510f2400d00040e41d040d01d150b03401400141000842540001c407480d0703074007003140000d030f4960380c6604058118100420081225a8102040f0041071000d0111400900503000201d9841a0300c1c1c2040919011187c01c480802e000183d1020601c0001001c1c00914042c1032070340c44281c001060044083c4584003100740c206100a0221206e04946a09001c01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 903562266 1250 903561016 903561121
    0xf0f12100e04030e01020f0d02010218061303030e0328020f121b040e0303070c0b09060c1b0124050a08011103191517150402100f1e08040b 61
    0x1110401c01112005000740148c212a42c1c002603510000c0300340c001c48160130340340d906120701c2c0240207140303002c4200840b980c140c0e80d241c100404254940d60020b8503004001050400c151250f03c1418000140880880c64852080d92120045000341081020000703134002d10101c00d500c0402840d0304207401d02480105400c001d0000910208102035690031a481105c61002040d48007004004000e070441845a0280751440900b400e0704020540f40b81d60b100340e0000072401c507016000f04292100a510512162004d100154071070303244510122841100c80c4030b0b451240b00c00c5200090140018020b00d0034401516002c0351841d955011007001c441220381c030b00f445c11542d9103444050046095080400346c8400d0351100d21048011004501d03140c6080408514500c10308140b01c01611000307100984c00c01f40b4202224520043c1904407104140e0720100a07545910141c00100c0700c8d0480c3e1118043c03801051801e0156848402c1c481c0ca040508115030b2a800e14558010002d10003240c440a101a8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 903563516 1250 903562266 903562273
    0x2a0c0e070807120914030a093204050c3f1b03090708121309021303150e0604081b0a0c050d0819090e090a0314030604020f0f12100e04030e0102 63
    0x7190191551f0800c1440f800401e840c803009000040b02090600001e000042c1c0c00007503400b0341c50517052006075401c0c03440d000301c0d240c50200302c0403c820000d4600401e8101682141c00c1e411002410640070b80f003014032000ca0941d1f04803a020108000c0d1944603421445403050020709000c80020140d000400400726405068004100c0c00b1003401524410200e007020f0300c0c1c94200510705c1114548495003c108068810402298840080c9451000300c0f42c10129a01c100d2848101800c064542003001d00c3c0c90780607a008000c20080f81c0000303031150403241030f03c81340c040d124a45482d0303803900326180150078040d004404000c58a0996100c14045108801036801d01d601040c0000c0d60030060b26401010540c1980107201420380454440d03400441e01c4002e000a604540780580b80045074400d4000d010400030015044d9155501110f407094403994019555194190401140da00140c0f01c41801e0706581000c1001c03000000716010070b0700c030f4100e070508503926159400d44d504d12300744000b10305500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 903564766 1250 903563516 903563543
    0x80a0b0606160525030b06280b071a01030804031103010207020414090f0d051b030909010e04050118080909060334150507032a0c0e0708071209 63
    0x30001408400141e100f64001c1802c000b030303100c0000740700c0300c0084c01003803070305400c9000c10225108082c0030b81c00c003100340c60204404003146011000030411500740e840c40c404540c00041c0c0843d000340100b00e018001c0b0140e0000a00c0c0c040382800d650002e11014105010900c824400305030800d403501d034503000050005140c0300c150743c042800d850070034059450310818881040882e45007444095241c2c61210090414543d0144001d40319006550010301101c43d12900c044000004004440d181130f0003c000a2042d0f80d9101010b041034402c46e01141c40307508040080300c058140494460310264020600303428100d1034402d00100410040c0030fa81e141c41240319481c0d50088440d0b0340e101c880d10010f00b103441c0d184d038900c9505200b91540e00c0702203d6450b010009404582c084190740c02c05602d49003548141c440304200039908440f035020b41c00426580c1c00380f40104030020025604440035441c07906941d90b00c0e141d0a489440c1d003200c1d29004904544080500d51003291f010500603403041d4002190306 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 903566016 1250 903564766 903564787
    0x60910052502210607180801060e01080d0203040303120905032701030c2102070c090f09110315010e0703091b050114031311120a060903031104080a0b0606 68
    0x104201204500400407a80c16401c0d41800c400c001c075039a03014080c41a408800000c81540c680004202d0401c0011010701500d6628050780400020f00800c4028041d03261a4505580211020f01c01c0340c42c00d2046444241c922030021041ea01265050744034030840c066030480000c064184840102c1e41ca000401c07008181c141112a010b00c2944954040440c0012200000d001c40740c002840f00c007400b000d40c038030b6444c040301888140304059588401680310000da00d00800061150f8010552550800e4411a482c0c002d44d80000c4050340a4a14001c484015506141e00c2e100702140d02c0107400c0101c0010f00036000203504050700300206240001c0c0f0151a903c03003030070311071100d00d00ca098032061b48410802507900841811259601d29440c034a1030810701c4800e02e000d100c50340d0040000604a003000b42035640c404102d17048005a2064840030103c501d007643c02801f90100440c04a894441c070040c2c415007442c180c5043d242c20f50300900200b459074a40340c00c9050018001c56000d4001c120b40701c1807 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 903567266 1250 903566016 903566047
    0x30507110a03032414100c021e0901060504142202040608010e011520070f06030c02010f05012907020d0819260405070b0c030c0c030c06091005 63
    0x2160080d600003440140b02c4408004481c891003a64013016040e42061004c0005150700c003050300da00311032011a01c00d0301c5400303030307501c0b01c0c81400a503000410622070b04e0180740c01a60340e001c4500c100e42041d05680c0f2200d0990f0540500e000710300c0005120b8000c241e1a0031b00080340300d18091030320042d080345803404410805a034030903002a000185607100402c4000b0a8810960141c0301102d50b01c0300507540700d034005007101ca0300c2c10321040c0721003c203882002381e1600b804400b018020481d030038500303a600c03104041c002d8070040004a00540c40c20610b803006401c14030525044c1c5090005901a1040700ca210080950b00036841c081c0580c010400500107075500500f100155120b074400d01e4861164050a15241141b1a418024800f2050a0128075880f10420702c0400560b900c0704940d54890382012450312003030740c0000c2070208000414002e07114000004d8090150000200c880400c800000d050300d0711290380382d0780d402940912181007180352a01c0c000313584aa0a01d00107060081c0101d801c0030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 903568516 1250 903567266 903567283
    0xb010603090c05040b031f0219031407020705010210091a28050709120305070515090106080a1230050618060f040e1212010f1208090103050711 63
    0x82a07554880400b00300611061800504089900b00000c400035008240c40b284441d01d0480900c1190900411140c0168107459044240c4ca480302207400c065540907000300202c005130183c040003a00090080c034400500403003544d106901900f22010185098009481041c2040b595240c1e20500503100405a0070150b1144182c80d00f4000f00e0040f045942010100841e040100107080500b04144690041c0d0014104c031095004450f8007105410111414011071740000c20500584103103640100b10301e6151409410460000c101090b550004180d40703000a40c07004040030081c065881e1014000c040804034141c600940c283d902200034440500d00050450a030b01845e980c00904c00c3d5400c02c049540040b000e4195011054101603001440604902c40c54a20854a800c4011054801404803206500441c010300d520307064030f94160401607100f4040c1300480d01c002d181c00a02c1d0504c840494000b90b4200c010546001e10140044001c0c00d0700420410030b00c1400c00c2210303541c020400c010341 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 903569766 1250 903568516 903568529
    0x312030c04090e0616020f06061012050f0103023c0102150a09060c09210204060b0c01090b06010507200f060304060e0d14040608131a1e070c020108130b01 68
    0x1192402404485205e08030000c210b045501111110003507107000500650000c8040b500b6010901e0300310740c1211550740711a65010000c4c2800144903c94a56009090680b4821a0454001000c0700403031040590003101c4010301503410004107aa000d510f40d4020312061040c4152038805d02c228101c14241c10040c2c600117200f41d17451840c86c0c24840b803480303407100c28996481e01d0707200c1d1441c00c0f10700703180b2000c5e0703000d45c40ea46c081c0d5041802c1103640baa4080f030000d15200c0c0006032100740b4409014001d110321030080e120846481e0020b1582d600c10b100b103c0e0801d40c450610404070183d401d88034014140e04c940d540d0008041c5c0b15821f030541d200703006588601c1c0b04075000701d150310100e00d181d81054144404082441504c030f008400800380e5038103540c01e40d03103d860f086100740d99001044114502010020f810600b0000c107480030340603d00e641a11400c035a4020455031900e0821210b0440ba0032039105d000250420402001076220300080c64205404104100b4010707039a440d0201843c3d021790216 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 903571016 1250 903569766 903569773
    0x1e04050f0f15090106080a0e0105070e030f120f0307050913051510080712060302040f0209150702060f031306060e1017060a02070206040e0a020d06050405060312030c04090e 76
    0x100810540101482c1d000c415001d02810011204012a041100600841c018070414500294aa01450b8004800451890000e00460410290190130403155102d982d01a0003902c0e000707034201c10300240d01505003071b00d0b4844c00c0c81c01c0314400346561a0340010b014401000402c10400900b81c0c0c0d80d00340034125800d14900000c139400c0a400644400381029900fa028600a1040c01c00041d007040b00d2030380c8280c103410000d00c042c0200c1c850b8402002d0750382000350700501d88420201c0e058a41d5015103550041a12420820b6100e41f400c0f0342d00d400b50f0704000307521200400a81003c07091101c05550400000d85041322403c81581d035403416034145801048100c0001000c00c01ca25001c40c1040d001001280700c2d01c042203000d542c81d5915698020904810b090f0005251411520390000700c400811135410a02418101601510b0103513021089200001d03003412800b04881c581445818000c800060050400f031a444420b020076800003814020f9148091100095a02180c01803c0184030118040d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 903572266 1250 903571016 903571021
    0x14030a0b040b0d0f020405130c180509030408030a0e060f0706151211240406110c060a120b040f06080703120c0c060e0a0f0e090d08060604051e04050f 66
    0x90008071000009401c1c4150508080c110100d0100b03072500f403e041d016100032403603032341c1c00c10780c3c0c0c2c042c0d507034408020031710f4840c4074001441c035901510340e08100340280024051529a40c4d000d40d40ca00450042d948a600204158002d4900a40d102482250f01800160402600714030000c2c490700a1003040d142580c03102c9002c1c04817001104210080c080c0308164903002505a107520484100c48103002d4010003400007511408460201440510400e20300c801e03544684403035000306004540d201c0d101f03240c4550820040c0d2403410310306440d0400256503418400c0c420b40a4804054a9410302c1c1d550056656004680072901c030b8040d880180140e14001c080b120302d5440d104200d0701c440510002040007102e0060300280c4000b03c802c2c01c40d075852514082a22288000596107100c42d400043c0da08903004c0b000540d1011041968410200791042d3350f5144d6100c00306890002c02250300c01c0d4071000800c01800b07680303070001400390b0800c0310500b204442c15032040490201e9005840a00340e214400c0304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 903573516 1250 903572266 903572269
    0xf060f08031306021b060706060509040516080304060f030c0c0602040902070b1803161704060f110105041e0620040519050307090504061b050901120e0a030e0114030a0b 74
    0xd00b400034400d0348000c151007104c0618500e80c100d01040020300c60100041c0090502059402020103064014041102424a07203801d5544001a503100040311040702c2d400918440b000c01034804940440d1968000c070910200c085000f40380f0041d51209008190100c000400c1103032010704041c2425410040c1c1d40e42da070341015007520500428a090000241562075826003000c025070390010740c150041d400c0750110346400303d00368100c218400900b0303401040010f46641c3c04901c0904080c0641c981001003000d080000d4242c92084601815018580003923000c12806800c04141e4030f806100000341030310940c010031408103240315183c000104046000c1c0003906c0c003011105c5003064103042c1e0300240340c90b100119459000034400c5d1650b090342d400c000f50030b000301c5400072040840380c141e03d8030240401c100080e00fa508900b404a00007100a1410300c0c0b0104241b1458110b008440010241030460742c0d01240c861415140b41e0b07040100030640080b0510312040954000d8081520110b1100c030a8030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 903574766 1250 903573516 903573547
    0xd051204061205010308070f080d110405040b0303090306161202040f060e0d0c03170405030f061b0901090b1e03090f1903080f1b16020a0e040804090f060f0803 70
    0x80b801040620b0840100001500282215001d0303500416503030300b2041d1400c05a259000311042c4401c0642030107541c11182c071003000104107480d011502004a50b0403001131660320b02031100a95010b5100c0d4002c15003205501d503142c00041514602122810f10520800e001d80c0c00960103070b44030011945051140c0368100c030040b10490000e640105018a81c2c1d158098000300901c80607040005080304100c0b0f020410040750041c22001d0210b45601c090207002c50396880c0101ca800d60020410700241289060003412034074507840513034036400e080c2c4c103160200300030754070072030004140d0366000920f07030012100a006144540c0342000648528055154075230b0821200340d06480803c42c9101010000a42110035590000c2110010052550b034150b9209a0213803004d241d01740300a008135050035200051915030813824400e90344170041540e40c0304442c00e0318400782c0d0000d0801100b8041840407003120f6001c0041080c05a20118410341e8032480881e40701821303040b00c88141c0000030394092010a21 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 903576016 1250 903574766 903574787
    0x3060d0c150c2d1401091212050f09100b0f03330709060509030f010509100b0d0c0b0d0209100f02010e15010510020a170403020306010909030c110d05120406 69
    0x44100c0c1034a40119400c82c0c0030f0343c041c4001403050710864510003c461095026080c0d055002c407111011103052000a0800c914003e0b803071088504200000b6007000411680c00d001d001d96000070700b1b1581e0591780040142042505154100b8503960b145961a94200000021404011107151102190181129401c030b01d1080d46c02d401d14100c4144a60707a81e02007040c100311545460b0060b1100700c0c0600190a0696031900e4042c15800d12040c030850310b4002c5202c0e80200d06283c410400c811803007051004074411514082c00c81800b4203800c006540e8110b0082135080c0382640d00610303100500c0000b50b0316014082d9010002400c0350000410141c09104250154014400512090301c08181403004035005005550180d402100c130740480c0c1e4020005c02c00c200303600c00d407113450004806200f800b023500f10f44016480380c841c040000494180b5403041c1100d280d00740d51904498615a15001c0204424401154002038080040b40104009000ca60603c2c6092010550760381d1401c076004120f503014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 903577266 1250 903576016 903576053
    0x1a22120b0112030e0d080d05010f140109080c060f0c0307080a1103031312050f0c0303100f0602030d1a0303161104060f0e04061103090f1005040803060d0c150c 70
    0xb02608031002c43c0d0070101c60441582c0c00c81c2c002440c0390003850052070b903029034600c03001e021f8100000440c0c0d00c0800440324054a04119807100700e40301b8003004555019a520480d0015003250844100ba4146003004215003041f4401c0703145030401c0c80a81300e26643c0084c4d03080e11880c201107900402c0350307403090f080394080c20500000c50950810750400004195036200c0240f03600011401c0d901005c0c0500b095030f41d0203c04030300070f80d25081c0207548543c0f0303540200e61024042064500c0800d030425006a41001e031010b0350300441c204086600500300500050300c400503140008100c0140954080009154030f0526404604000e500e5150a41c00c0c10000c4500c80e200d5420300505002c04001001076004982020350369580c6901cbd203007806401450350b04007030000190000b0401caa01c1c0000240540c402d0b041e1000c40b218800802c1c0101d08690003920004c12540041000c80d46510385104100103403801081605029541c50241c0340703002c0699000780010500490700744040c0a40040c2c0395100010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 903578516 1250 903577266 903577289
    0x41d07141908040213060603050f090708031206031203190b1005090402130825091a010302071a1f0b07230a0b0c0408161a22120b01 58
    0x700140441c0d49070544080040015940004003595603005841e00714410841c1e04000185c1c9800f00207000d0f00d400c64198041c1034002c03012032140300d400111001103038003081c051420041d82e82c803403c445001c043c080544c0b41c81511900815016040c1c021405511090002c2049000002500c001d54072070a09851140c0020f211300b2070155080411501111021a0016a900303e4071070302d0845d50405812000c65442500c070100d50301d07241c01d1442e1504440210380c0381841c0796900b8240065408540c400803d28001c8100d5000039406034000d48030103071107503664404114408100d02040c0c40211102c002e0400150b90b240320640020320300101502c94202050325090040d1581c00750000400c0c4820070030500306050036910b1409000b0a03000c0c6500c81c0c25401e42c0d0604001482094100340a180c00360300440c0c0344401d0781c01c0c0880108040b58820012481e08101ca04075803542c0c1c0d04039200900d0304002c02d0040c1003440c140e240d20007021f8000030704801d9002e540742c1020583d1080c143c200021410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 903579766 1250 903578516 903578527
    0xa2009062e110102041203140313080903010e0609060a0c0e0307121e06020306040608010507020a1b080a0804030302160e04020907050d1b0815060d0e03041d0714 71
    0x1500c00d480740510990300c0748080c1c003460040480742441a10303000d19840d4408a80407803100c0e8200012034002e4061343d520310001b189405004420b00c000d03141640055003c10001c800110300e04098292490001c0c0009082700a0040300340c10000c086544214541004042009014052051406d1a94030f484c04825030914200804d036102c59a020740d2103000800782e55042009080b45012001030034485400348078449038580305003c0d40080c2e8540d440f450503c9804207004005105403489155650300900341400c1700d41320b0419160b140486020307186d81c0010301203154041008003d0100f0b100f4500c03107a5036451420000c0c02c0074182d21110701010001c40f030401280484200150b00503404071344a50003500c81d841d044d9180d00c42c9401d800c00a50401551268070311005000015004080d00d80b9400c941d41c10320704450398044103d0300c540c050381c20321610350f80302d441d0352000e40782181c0303102242c3c50305888040c2c80f205008442500803003d1041b108208000c1c0d4030012a400451001c0802030400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 903581016 1250 903579766 903579799
    0x106050a06021203014104060905040201020c0d0615180e0102041a0a030b09040b0603010b030f1203100302150d18020609060703031512230a02120a200906 68
    0x1880107110320400710b06d03211480ca499454942d600d0342c1000e00100c603002e26049061115030702d0192034500f10710940c54030030001030003a0315008640c4030701e60507400b42c1101c000c10700030840c94544201040d51a90b554019203441d20103030344011400340a02580490f50f0b250001c45107070a40300d044c4003580603640140000c016002d4050401503e94011140382619103900b42ca007240108500250f050b0300803000400d220174803900e2441507000c1c0b2020f4000b4014882d8840038581d07643c01c0080940c100e580040007403485441a00041e6800c4403040d4503441120b40d13a0b4000843e62129240005280d0030300148680000100d84110340c0d012101c00d600c02004842500050058064500640e019680010f180c2c0201403181d8024030225544114504140d500c1d4800f103030341e11282030070446c0c83c0c8100c0c00000710203900352907540418600c03aa00404100c0300f25828002940050340002c0d400344107510f6071100040e2206401030051059001c071001c41881601000036100002c4c00080c0074200c0401314047c3e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 903582266 1250 903581016 903581053
    0xe01110409050a090b0f0405210a02010e07030309050f0f0d030512070305090303010308071a04120f09050603010902090d0503070828021c0509030106090e01050601170106030b01050c0a03020106050a0602 89
    0x1181e1b0704484005a642c0e542809030510320203d20411040d65010802400310303071039202510300c0c00516070007009003a5400101031b644041c0303030002501003030258004021518002e903e0a0340000f014080581404000700880c0d044200789104902048010400ca160072020074641c0f54400064a028002070130030090040d264030042c00301522070300001410700c0612080481c1d050704080305503159840c83c54070342460000d000e150410100010400018800e43c030307200e00d0352102a07800007030100b0f15691030512881c00940c40b0780c405581001400c41c91002240d014005040d140f4001c4140c0c50780d0b41d10a9081e070700c00041c0e1a00c85162101c0002d40f03141030360780c00a800000c8140000b128400d003000c07214140c0300360050055440d459070828400ac200c1c1c050b1074103c521094190b81c024802515040015100f4a6860f0b166400712008007004100c024404c2d0894414200c044c10040d01e803081005001e414141c01c040c0641c0544c0d1200020851401e08041c42401401c2d10302c0036000c00404c0b14042c200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 903583516 1250 903582266 903582271
    0x1603030804030c0506040309060f0504050306062b0305070c1a070308090c0d0501060810020906070f030c1a040201080603160909110d050f1603030906050703030e01110409050a090b 79
    0x30880c4240c00142018010450324102c503070000c040f0b608030320785860000e26414041c000c0c400022080c10040480a01840541d030940344014058091707940ea20040c0300040d071801305421803442c040d07000c518041c2c7c986580c25102501944c0e80680c3c0300780c0c40c03c00500c40700311a030001c01c0074144035101d586014449815030322050350501c0d080c80543c0b220301c03100d072a290b02c1c1c0007859030015022802000b08030381580180100d840d840c00350b0f8003645510190318124060800d80b5900101304000d4a0700144c0c2c00246003c10902c40d00b440640d401c02c40d22284508803020480d0a240601101032006543c1c01180040d88406c0c128001c2030071081080d04411000d00511a01c4104d6459000040800c0b0103845c044882000180c030100112002c0d0034480d68440e0311141c1e16869020f052807200c00ca081d0603207000d0649030035481b403561030303841c0283c1101c00d580545001d0301050b81d118103450f00c0a000703000d030b21030440306520187c1c0c4407824101c541080310301c090106240e05240803240070009031003100859 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 903584766 1250 903583516 903583523
    0x40e040f02040f1b080f06030c060703021504061a0904020a05190b0d05070f0215070809030d0c020c03011d0d0c03020f06011d0702030703140c03040905090601171603 73
    0x814582840c400304010b4800400703424100c0d4101456003602079010b0810400c42e812a540c0d1480588802d03801b0b4103161815582039400d0b400003e42500207041c4100101200c80c802d1040320350401d03056100c01983c110076035045880d5a11030204031030a41041c13218820b208401ca40800c07003030070568002150301049204840c001ca411014684080062515080c028001041c0217030780e075000503001800801040307a803d800b080c01e40b114030907141c0c070001d18180d020b0040d038000241030300e80c1c2d00c2c00d65010708001c2801100d84810412890120001d018030a00390920340c001b004180c0b03150042600b07480944c10040342028103e40303082c0f0304c88400512844601c0241c102148486001d003400ca0030100510842c0507140b040b2400042c010540000400181c01040b0560b20a81c40700c10f412603c911500c0800380024105000401d09203040b8402030403800c144908a82c27030256144400344c140c1e0303800c69080340e0b90b8028000400a00f5407014000300d60103c1b04000e000c061420b2842d4542c641e00602016 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 903586016 1250 903584766 903584783
    0x10c0824010f120f090614010b030f040b220b04061107080d02030705070f14190201230915120c090607260f031608100e04020a09060609030611040e04 66
    0x940c60000d16604c0f07062003d481e8542800301c4d10490030918040c0c4004d1200b00c0320300b1050000024071a6900781984c1c0100d998904220641d180d94480c5541e100e4050708845c1c1c00d40304628085000f11003041080e002c1807190380081002e14207818428112030000300c074480000d50800c04040018a800c040b1003940120501c0161aa00c1d00b420450303c90003466001414400d02c07294200c24884005d0a01d4100001501158079000b0000f02840c40080c103160028007080071081a003420036a1a80202c0c014400703007a41c00c5c200702c6d1450019405003264584281c0308000051a500304841c901c07180e50b80710f54071441413840c0100785804a42c0522030f441c0050100901c9080d17070b1400001154405016000341c5080075111007840e510364906030300544408045006486107820494098620517102c3e2400f019810300d040c1c07401c0440c402d441c00c0104101d80c003030f125920200e07511115200750030180038981d40d0300c9030881c01c514001c0300b1074542d00442401c070340782030004000e000b0094141c107910030b501c50b616 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 903587266 1250 903586016 903586037
    0x10b09040e0c151801020d210b030d0c0b0105090603070e18030a052703030d0f0e0f0d08010b0c070b0705030c06160e04020403052508010c0824010f 65
    0x45a0402c0c180241c402d600210b11900501d41c44244805002492080f000c00b10080b4816801681c1c1c842407801803202107110000100f96002c6401e04881144220100c0811149c03e07143c0003d0512911440000100e0600740c80e02d01802040e1201c0c5000d400b05072655020f50a080b0006552400716104507500c1c90030700400503030180140c00b0701c80c02c0c07001c60f002102e445040c9100058401d4000d07103460075008c200102c4803204c0e50b04207100c0c004900700140c065071030109029080c030041c2490a00c10030b030070b0740c444006d61110102040780c150140d660700b0140c00301d1021018010048001a032111128040a0015042d03060000c980c401c02c441700100c81555480310b81c5070203811170180d184403514038061a41000034000003038103a080394841d195203000300c0740818800c1000b00d000c0c0d4040948168000c5115020300511900e03044a501e040100c80c1549a6964000300d0039501001c40c0c20300028003000130711a29001228034030340307000e40240725040c0c1c04240c100007c1080c08400003d41c204085030a9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 903588516 1250 903587266 903587291
    0x513020409050a081201030b0a0911100216140109080d051912020d15092009150703020a050c0108390a08041101050c060744010806010b0904 62
    0xa08420250300002c02a1504c1200c41c01798030320381d0244400e40704000780d80b0001d81c0c9c1001c0d40c1301e0304003103079440080b4410740318281c0c0230f028400a12a60300002c0d4816046103070001101542c1c0d50000b41001022001d401101c0e400041030750314641c0c4a00c0344c0340e011201c0300c8516a0400c00707440180c508940204000c0c00070780301c100d528012220002045a00c00108101c88040300c8e040f0300e070040c01c5d80b0740c1082d2442e03031819240c00700d9601c0b102c080206880298102d141c0d03416800280b2a50000034030049001100880030f00c141c0d484940c04601590000801804208090280c03c1200001342841d026510304101030000301d1892034043e00480c81c0030f620760040d0f01d00100e0984064280c8002050701c8030346012000c0e151f050181c0e801d482000399006400450362141c011140c1034414000607162544552101366240d0340300050790000e945c0c146450642081c1c224042c0104003458030348111888903003608040c141d400680150300075401110051000418005c102c84d03042e00c1c241c400080020a080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 903589766 1250 903588516 903588523
    0x50402130c05040504020a180e070c0b06040f0e0a05190c060c020118090e06010b0304031403090a02041802090a0b09070e04090209100608070207060905010e04180b100504051302040905 81
    0x700b2856100703101044a071030340c0358014902d04004039141b190a0183d5111b8242490127801122072400003036172400b408000400c83c00c034984d00508080d00214410000c1425030003900c05100c245401c5034015080442888010806070084240210784103211800640341c2e02047c0e11180141800c0c0b101400003503086900c200c81a010040090354118009516061060007401c0d041003109100e1040c0000801d041010004490003664140c03a841622082da01e411a03a90308000e11402c854011144540d025860b540182c2024042a00036a21255414410001c00b51400b1f04549203440c0343c44614501500c4503440a030b00540c00b41008048a000c01c8002805000c1c40500250051080b0081c803550031084039094080e16060f0304e40280c44e680f1000100e956020358400c0700001068100d003040194010045040351320303005003010440700389250703081300340c0040e00004440014900040050b40086051a4000740a0403101840942402402e00c813608440d904041c0c49166100c1d0390804000041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 903591016 1250 903589766 903589769
    0x16060c0204271b14030a03110a0c081c0e24071401050106030c020604050703080904060806160306060203041208130e090a02041a2d030a150b010201050402130c0504 72
    0x4a070380c0401002645000c01d2031070303c210039090049140540100b001035030111008184003002d40102140c04003500c04460921400005180358001c90388100c000c9012105618040d20307038a40100900494201000213502c10700d80d001041121284481d10079946280a450124040768050300381e0300350301040724946100326440240300f442076034144549110190401c46c129103454604200b003801c010403d90701e03404111002801c0d07820191050000030007030350150000c00005040010640d448440040c68100d068071003403003e02800c180c020b100c03a03041c046e003806440d0500c0070758106480c2c024001c001d0801c0000080031100041041040c0150010070017000303100c000000c1c08281000c01c06952071360544101640901c1c101480301c0c03014070040071101b90400c806880304006624054680b00e0f0080c550600588000b0a4180d0540c02e9408201c40d5034a180a130a0b180b031101141400b820443e8aa1402141564182001c010140c1e45d901c000319140c840c02080422410b01881044945100e00d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 903592266 1250 903591016 903591071
    0xa030c090803040905041208280b060301032001030608070e0408070807151a0f01080a06080607020c01030516090b0d0b06030703050115140306040c18120516060c0204 73
    0x203d0006a108125002140a41d00880f482e03556119001800c50300c55900329003200c5002e8100708003c030144840b0b0610a00702000600026940c291000041c406600a9000b5204003841c00100b01910f25030740b0740048840001d00b0704018141c41c0c009100c3d100c07061031103524092584000017509010b006400c0751202076109088954418452400401c104100b8850320140d501d002050340c4c034401078800111045a000707041c60a0303010b04c440111400500105005559a15440e00280302e07081000810300901d43c60b0080c200380f00100c00014103d650081c003080454000700c0c02c000e1500d8101c001c200c166103910341c0d426074881606081c00040d18000c02c0040e0002400410042015410740c4960305a03a180807543d440d20001c14021905a4009090070800c003034104045840351400d58000c0d00c480d082d030b003421041c0701003000c5804482e20003a0f20800191010541c801d04210050100f6291b444414460340c96050520350000d00001400d03000070700940e581d410f1024074403000e038141104040b0b03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 903593516 1250 903592266 903592273
    0x9030207120312050f07020706031e0f02120408210f150d15050103031d0a050603180106030615051005030a1e09060b09060319021e060a020319050403080a030c0908 72
    0x8042460016405d01103600000500038440c021502c20322901502001d0103501e002d040b02c40b00c0c50040b440c004c2541302000c51070594204043c03569041c01c0c20450703111710300500039a1345440440455111000c0c51104072224014424104a90f080901041a800481d8800009280070040020805075160b4030300182200e4a0300841e21000c0045e50081410b1360301c241c1c0c90006580203d1140301c24128900c065651214818005000b2414108055680005144011404008a030075201c1c2100c403030ba001603032080d848141e40400d1002d84400e8000500040e1210b02c44d00343c0310040100903000190444003200e807600240940055142c601184452162004000c0c00e5800c2ca082d070002e140302503040b4000d045010000e101d515020030142c02804d0400f400d134540014550801c0364045000b5280d0130b001c071615100c68116258a8060400c04590340c005642d14039401c1a0f100003059080215801c0050030001400020f81c18001c0e90100c1c4100c0c01d010602d5200c01e0010f42c0c2400e442c0d00324207120301c07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 903594766 1250 903593516 903593521
    0x2040324150e060a0605030403051e0f040b0405041802100e040f140a0e030c030417030c0a0309031e0f0204020d110f1201050609030723060304150f0903020712031205 73
    0x1c2c044000d0b41e000e1001100c80c404d486640e2203090306c01d0300003213502a021840030b110710b4415041d0b0305901c100c0c00000079012442c1000210341c44409811541202c107160b08041018400360800e0711030150760b40c003103040c00580b03000c145d800070f041111072108203000c02c86174011410240c1c50f250030865600c8000001800140d039001114205a082120860b540c030742490403c40740c1c640c1c0801202c103801c107450003451070503080504021820710780344440f0203644010080f82441d08070610940c01e41e24440c0e03441c014210b1450821760b200720a05c8142500d802d01d52400180002d070700c401500a200e90540b07004d42c40e490006010070040c81a81d00380c1c85004d4000440c0c440c4855071200412070880b640d403404401c0d0b40c9540c103109003801603440c3c0581540c440001071040398020781410101000e6448016441c032003000c04500380d07810503142111202e034640c000c034803180c40500458040d0755508078104a58071107a2030003075460405105002508126030354050a051007040040004400e9810502c40c60 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 903596016 1250 903594766 903594779
    0x6090c031e0911060c0a060c020102030907210303050a0b10020c1801080c060c03041502010c030c02030a0806061c051906050604060804200d0302070609090204032415 73
    0x81428000d40c01031400c00c45601c0303651015030b11074440304903001282c2c07118080085042c000194032103101141a44600c0c5928000102c60f8058180a05901c3c0d00140e22401c094111030b18210302608220950004080303110700ca1005d0600040321981c16260205091f11981c800740003c2c129001c0441d006020080b52440f85034000584c24001d601c19981c0c0d601103c00b05c041302d95400c01c2030040400c160403850030a411882c0c80d0010f80402d0000100b52450255104030b400c1c0c03140304814036600542d4483c55642d10700b5803d449540c401c820303180040d6207001103580009080210082c85580b2504010035154011200e07492440b44e1001e642504101a00304451203003031030020420780c600702c9403c110b000305040c2814401d40e011110540c642d81f20b551110b0f626140d000c10140303017004019882c0c480c00202c0344e4800071000c4003580a03801800e0000d060110007443c080c042d40003101035078010001000007824030180b03190502e0a240340e0301e0001d0300031102d00c405000c101002c0685141d0340c4030701141c81d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 903597122 1106 903596016 903596021
    0xa08070209040c150f1d031009051606030b09062b020d080328060b0708030a2301180908030402040b030a1704061814060d06090c03 58
    0x40c3c903004a51070001c802e030440360005030b40f00765258160b500860900b410950340b4841c81c010560050200e07544450230310103a0b0250f03a5400d092018405e041c40b21a0106200440c00d245041d43c440c0010040c203c81c0c208240b04200e0b1401148541c030b4034005000f114042c00c40b4000d071a0161850034810429941c0081c2d801c08058181c500000300200300031403240f05284100c0c40b2007885010704000d401c0c1d2102214194900d041c0c0d091110103117000503a400d069004499aa482d5941601c00d006400e0003488002596948a201a47c501c1404500340c1078aa0080351040ca04401c0c0610405540540034082c00001e030400214000d4101508294a4100301508541c107504e0b10395601c0b504100c034031071102c13484103011400348150380e489058a5410344450841c240c1d45800c0c42c9888000f47d017850441071007054001000040e5000d036030855801071001c1902084000800c5030003502 = true := by decide +kernel

theorem cover : BRFrame.Cov 903417266 903597122 := by
  have h0 := BRFrame.cov_init 903417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 903417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 903417266 ≤ n) (h2 : n < 903597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
