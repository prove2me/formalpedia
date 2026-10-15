-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5087
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:41:56.073358+00:00
-- url     : https://prove2.me/submissions/9f4e733d-d092-4036-9e71-e50cae1121af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 914748201 ≤ n < 914928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 914749451 1250 914748201 914748271
    0xc080601120b0a0218040c080a110414040b04020702030d08040b07021b0105070f020a0612180b0f09150f01030b09070b040611010221160e0a090914011103 68
    0x300448a840c2d2006281c001d61100b03504ea20b10050210f16005d05507a1801515076020862361084601e0800000860866a0300e000e04d81c1e400500f00020402c0c02403161407542110001c4500140c60304a550103d0041d10030904025894068649905041c0d0b03005a10140103a0180610404c9686c9022050744d031a500740030050500c11134481d050a03150300c25002401401d102e004001390340405a070100c1d11000441e0003910108809888008210400e403244868440400c5071816140344075840f1902d00c110041e040c1c1d0010032040c40040d18144c001c00ca06801c003000b5680c1c881c4d092a1401d000114000f01b8001103801c10015000314410f850006448420ba0b460110304620305444c0040580e20350b03044001480c0955002e1010071510124140c101032030342e840c8203030071469291800000b45614180f841c03000c01c1c410351560481503a210001594192004620006441c03019410b02d03112020003420700549540c20076010305004078540001e0350061184428040001c40000e24002f002c085a8403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 914750701 1250 914749451 914749463
    0x30c1502150c0a1116090c0c0f030809030408030d020702040501091509200316031b140703030b031b0a08030c1005060a050d0606030b010f15120e0a0c08060112 70
    0x3189082003848014a50b5140f98104403241042d1480e640341040d02c114140010443c44880c100001c11035030061100301445403406200082e025a03441e0b00c81101da0b00003038200f003200000616040d50400807507000d8141242100d8651001000a2010b5442003008034000c2d4208000011100d600740114080011580000c1d05a2405c00100303900038107020750611010941580c0c1a02c914000303034000c50144020300051040c0d4080d60038007605940310307807903491060079064a03034410090b440a644241122940070441d0354114500b006c41c00741180500b01c5916001c0c0320310110382d01418080c10804000191514013075959182075581c1c0320f0285440c001025000701084130110001d951002d580260300810701014271f41c036000800d030180f0041c041201c0307040d0341d84414424444001d406600510680c2022140103041000300709244280c04011414449080111000800c40d90801c0480d010a182140d040038601c4c20700085000041c0300701c4640b80104000414007402199600c0f03d55a0001c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 914751951 1250 914750701 914750743
    0x12020f1e010c0c120803061e0105250c090b0907021b01080603073b040f082a1f020c0309120a0218090d09150c021504030c1502 56
    0x350041d12241640c54045a00e0198100c010400601c0000055000340c00342c05029128903100062010180404c00c2e0345200d140954004222a80d1200444080300c1d035a40700818070050421003401c2410f0304400060441c3d50039040480d28082d980c0c4019041c3d0b6040300d812034103032a144401da0700c500250242d1109105110840401c0703502034640d054000e50003070300300c6000565824484c6d84190803410300780c40c0300000010303a01d003140b0301019407801447c0208800e81c1c0e50925603219220444000e600034800c45002c42d0040c03d0800004214800081e0040307a645115415449aa103c5075641807160b1000c3d2060384406040ca110f01c03e13241c10f000e103e002145811018010012000907458244080e0310801c81940016200c2c0c241d41e512000002d0015600350a103c00340d10704100d229035918080240b5910b04201300c404160f1414486005410b00d902200c0090011490b01d0001c803160f070000d2880020008100403140301030700125140d16054001ca8200410104c3c0c5802d880c007981d0610100d45 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 914753201 1250 914751951 914752009
    0x20306130c0522080a0b04020306160f2106090b03010e03030609010311030a05010f0914061b13051f080c0304050607080606070b07080f01060903081c140112020f 71
    0x10010010007819006a07490b0310f1659042c29070f140c502c118400301ca000c00c0c003805020450808112980d009400b441d0301000700c0804180040c01581c1e842040010022003101c80e01c03034600880e001c4402032001c48400c4c0001a281d149400140c2440341d0038600961900c0d407443c0c111318001c82600d000303100080200c0d117649d01c3c40e102c00e0111070030550059858094901b0030000643c091084c095807103514a40420b05080c7e504004106030b83c1503029030b4080d0488020003201800d900500301038910b025840395111900f901b0141900110b5811290700004c1c000807400406c150102118824019031359014407940d558000740c44213000c241c0d00240294803010102c1c82c1d080c01403001d243d10400103411035082c24825110380340071800c1600c0c2c05000c508002c050045910221084501412460904200c070302d14603a40d0300326510912920313036207007a0700b03912100039240c844e00031003199800a0b00406255071190401d8048010062089214101a800044150902c414491607150010f80030401e0820741c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 914754451 1250 914753201 914753227
    0x903100b0402092d04020906070f05240405060108010612060b180a09021003020c0a020415030501111b01060b04030807030e061b0f1c0507051f020306130c05 69
    0xa1000540c426001d03c40d020480e00c49049201d030602e01e1400c0d61122009010000c0d511105814030640104d004028004141e01c458040310b0215500c26411000f100046c100315060800c601ca4002c90460410701c541480030f0b4010380140540d0094094400599032031080b03600f21040382c441c00003403208410507180851016030100708c848801410307000c1041c0700761030010480b130400c646550840e6580c01b842c07001e42c00e001a40076001e100c14141140707001221001c0039a43c050005009215940758009100e950502c1e080160003198424000e1001c603051429044003504121010700c000f6208480c94005401c0c14001c400450340b001c01e02c14a40703411a2a022081d500c6a1401e80501c40f100402207a1034403454020f040f0642007152027003111803081c02ea1030506038441c0e0000300c964804904440300856480820a20345210700300550340d200709113049801d00b640c0d04042841d401050080d0180c050198006502c0744908949044103009103420140031108401c0c1d070800000c0c010b100c09110350b64 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 914755701 1250 914754451 914754461
    0x3020307180e011d0c0405061f021c020f19020603070e030f160807141c170c150703150510050c0a050307061415040507051603080603070b090310 64
    0x3080901003002c0035458009400c0d516500301c0341d600c121005440d0b20360390f44103024034041d100045074140964201040041d401017182c411400ca070740e80000c440d100d010b000f08400c0004119003104580310154000001c2d4840314861203400c6140166281e40b55044e188400c459140c640c02440c2c21304584411004a07044219031040d240c040c810404100c0e02c040c020068684244001c5243d0340c011420030082c1c905103038095002d241464803080e00161a565400408261559a00c0074940c0800450508400050003c900411040c00020b17850401040124000c83d0000303e146034006a40c640d92800c60494583c04210b201082d504402400300e80303482c1d040c0300c202c00fa0a240c86030404900910041c03c2000880e0200c9490784005150000c101c101d01401b18801c2ca515844109032500106080c81e620746125035a21807603441000405845c000d400703403495960740b0903010448100350b14010340710710b2040c9c0781c6c4c80c0300b031041e01e40014180220340300b100c0100340081d015225105881c44002d0140c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 914756951 1250 914755701 914755739
    0x60403031505030307121b08070209040305090603040503070204060e0405060402010c0302031905030f0603030f0d0504081306020c0f0a060e06070f12080103110a0e0103030c02040f02030109090204060f03020307 92
    0x1e078054a000500340d800300007600340381d80540c11450342d0362040540903202c030340180604482c2c41d00d003c042001040c149019550000c0c0c054981c1d00300e9640b18601111640b140f40c4005c0d602c02c0000c01417006002e000805482004e200341c03410004180c40301840c1c0000c43c8110340007800c0d80d101d400050015489460700354205071081c0100ca0038040580240c841d1442c014110b50700180b00402081004060488001d401c0341c01940910b25000304865112241c1c403400d50181d0321191907201080411002500f260012901245011501511040c00940f94204220160301c200201207113403101d490920440d01c212201612140034410700701d4244040da41105000340d0b82c045548289401003140b040e403841c40c0c2c03552a80d4003081d0b0360551405003507031040d41d26080d001c0d21940f2810700040401102c254103503501400c4c00380c000c03c0c0c2c5200140c040d25500b068800203038008400000c4101e072a030820b07044903100300c509100c02502c6811390b142900d50b170b100280d41603100150400401c07016040c0712840d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 914758201 1250 914756951 914756981
    0x1009020c0f030f0c010b0a08030307270902071a060a0510170a061518060309020f03010f0c090b120f0403050c0a05030702093304090218160c0506040303 67
    0x180c200151010b0540e00110030300103000c0310015640c45582c01c284a030810800088a00701c841d00d042010031542c03800024104c00521103226124401c100081511016410b00c00000d40c40c0705441d181400060740100310100d40100000301000e084202d11a15a44551006401c003414103251508200450800e40b0f000303014000045c903100c0c2c2056162803510301c59400c1890200b41c851410880c00281030200d010341c3c04001c80d1028014842c0b40c0743c0d01d0034007210200e1802049042c0d050000500451001e03000544c90b620700b03540040003a00c150002c200d01421600c070381c2e5117140e417100010001d10803480550360003506a00042c641e88980f01c0c0180d0018000e2030100e0500422000302807801000703031801d0341c1c2a40003107412030851a0001a150380040c2c144c840035440c4d00e41078041043c80a220441e080c0d403004d102148242130329254400c99010b50000c105180f003110b44542c07203040345800d03070340036600c54411130300030a0f907a004160802c08581d005c0e00501c4503a4840d10f04500400f00d007008001d00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 914759451 1250 914758201 914758213
    0x1a0a181106040e130c0b0708030103060506060f0d06080d0e0a0e0a1103040501020309010c05180f041517010e0a0c031b030606080f010b0a050112150b03041203060506031009020c 78
    0x843c000e19450302d1003101c004a46442c0f905160516100d80c04055010050801041099100140c0c038070068134112588450b0209040d03d92000141080c020001010f4180d140800c403100c0294858104204450904082d50807419422000711499031390490aa0381001610702c04108105000c50f40551041ca82c0d01e0024152030026540075065009070307020758003a0f4021050022010080c800c1016079042c5060a52500c10420140e02201002c00310040c442c540c60b18549040b80c8458000f54214125642c03d0300c00c00751030f18041c11081200c4009608d01d9881c1403002c00b0b0070000012a18212a003201d03041c1c4649145583d46601110403002603900f09588030380000006443d030003014003074400a4040d1148a105000c0c00d82140c2c0010011440344c3c0081c0402c00c030a9801043d0080c103040580400300c2c0100c035040c0b402020900980c04440388090000800c4180700c442069000002a213980500801d41e0f13400400940c0d000540d1511035607100c4070010007200159034014040c07109420b0940700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 914760701 1250 914759451 914759459
    0x12080919031d0a0305060a050a02090a05060c0a0206030117074505010620210c010914030a0908010501210203010b100905030f03270d0b01031a0a18110604 68
    0x3944140e13030b004031003e034044000d00001480720702400d070f4418605c0c2000c6061501b1900000c0c0788908521501d8021800000d0b1000300e0f42060004884403a0081c05055036541d46104d0352a849110702d8404200d4050b452002c83d51350080c1440c031845040134100041000805030102d010700c2c6491030015400310262a40741070740d680e0ba000b40c6000313003480e03203402c00d4000e42d0b12030600ca080384900c00d5151541211032081d100e41c40014105004201840d040d503120b0140c4c400d01c0e80103000c5808003400c05101d10014038000000040100620341c230555440901540d00c6954a00380e68081c002c5001c108034a07640e05905500100c00400001c0c001070000c03c4440d44072003c2992442d012080f000001d0b801d000600881c03d04100200c0c2c1c04007034100541c9002e0350808072030496140c0070f45001d410b03901580341140d40d41d68117035884030454005e404008503595034504040402806164211414030410000f5000ca8440c414076420020140001101c0001c580d1042c000a49407a850365000206020110f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 914761951 1250 914760701 914760709
    0x170319170403020c0a09021201090519060f0501031407020d0c02010309060e06070e0a0308090411040f1205010501060914010f020319020307020f0301051e100308030412080919031d 79
    0x2070003a03000390060418683c040061004804650700460a40d60040000c01c0744c126001079514110340c1111400105070b16202c046402c3c0f03806a00d0802e0741d55060000100d05400e0713442d10802141c4007601d0402003040c2c2c81194240180003220280c01507004103034203a800302d010794010000c2500c14500001d0084040e580d01049901c40708200105034442e40400c107800b81c0080c1040c40107a02102d00807683e914540d5402030314030078010101d014a07107445040d01459840d0081c0c2d009010403440401e0f480c2e4480c0b44a40c81184840070644256080c10000181c6a0181c0ca02100703847c007902c0440c1d500340225005466031054840c8030011440104060540c48820715503c1524882e80e5002c0c5540302481d0041149a0300f00d00003841c4a64034000c107000c407440e040c807081c03500131500300001d00c4039a899000130402464941c0c0050901d003000003c10042100c801c410842d5401241c5038000680c40d01804035030b44000007503020f08118400010307500800c0c040c129480c400c5030030040500016860401003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 914763201 1250 914761951 914761997
    0x180506040f1112010c0e0406080c0607020a05061914040302010522030b07020c131a0d060b060d06230306130203010e030f0a08070503040804030321060e10170319 71
    0x400d0380d03503503400c02a030340c0c99004880ca546c21200311400d1010030b00b011100c544800c030000841e44030714400200d00003103403070302c0f4099002070038000e0045880315071444103038203400d81401078040010403820314028060910f81c140e4096a406035222400c01c07214000d0030b0b4440c00e13610640032403240c20360000400561881c131071a2203175080c2e0303020700310703481410040c0180300c1c2042100402080c10000d0301c1402a40c10803840c4002c10302218036040c4029542420402417024407560f5410140000c1c0c040e81446541e0041c60440b4800c07864070340d407594607148031070b100000400002e504d44c00100c00b2803564480e130030080c505180020000255804e94140d10351940d444091a5082c1000210701c420741940c004c40400c1d070101c840d04003a0301e1480d05540e0b21b180740c4600c1c0001828000c62085040100308100d0f0181d1059045400c104a41030712a0040f004560701200c0c2c1e5800084442001324041040d04880381c40c4402c1c40004500f0044200560011900d45802c01010043c0034105890351001034103907 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 914764451 1250 914763201 914763229
    0xc08070f110709020327011b020105061f09080d1d180703021e031521030a12020d23060d02010c081e1309050f271e01050109180506040f11 61
    0x6201c81101c810851007003074508c80c0300f056924180402060381c8400c20580c0c82d24120030301e0045a900100410745c0c6160b2039410000b000d2241c0305200d95242d0300140e2020040c11003021162612a60320100604000340400d51098000c40f08003140442d402034010300383d440e04146001d14200050150000180c0040b40c04501c02003ca40c090441c0741407440d4151201b4012030401c0070000c0c5614101030341d91180a080e4420845503105c0c10741441c0183c0d0580782502c4070351105008021824036007102d0203603000400d80482030754402084883c0740110000542c981e043c1c4601100450540325074070305405c60108a03420b045400310710b8459080344401400c1242c0031501c0390700300358208440d030401c580d4000c008610f2200f041050201801c40850541d650003005508050184d4800520500b0041070003029001100e01c1000a4003045064004a040e1703900044200003030300e501130306101803503d180030181031500001c0c08500415038810b000e103c1e0900521103080900e00310b801041d51823800c4c901c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 914765701 1250 914764451 914764453
    0x7110f0418081c0b010903080703090f030813060207052809050c0d0605010311030c0703031d151b071704030b0c07060f3605010c08070f110709020327 66
    0xb04000e101000c000c0443e403245500b50308100343d12001001800c0c009042c0009010045c021500300201440b42e0745200203070100e030300c007601c11a1341e030f140600c1560007202d0780300044000341002046107880062098100c42c00104109000e0301d4072013051076000c01622007108001c40c4103030042000444d502406000f411280181a540c0400303610341821280c250304590704140c20818041d0703a0700141c1080d03c4e0040c12441c1e940360349031300300c1c50207400501255145250340000f0300381c2c40680e2603000c1004c03001e444103888149025a541005030215020407541d03160f80302c105101d80d002090b4548044103009039000c880318945510781c1c644065440c001c440311180300c2c000240050400902d40500417054803140c105100010700202d00d06001030944403507031002e4138500300e56600d18040c0c075200721006070440002c00c10700c0d4181c9001040301200b01c40380d01c04102c072088500c007624443d0b003019010141d41c00180c92100d00740340044002c3d60010b040d4140c074514162600031400060215001c540300808 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 914766951 1250 914765701 914765707
    0xa0207030c06080c0d0b1906020319030902090c1333031406100203120f0106020c010c050601091e0c030509010b040b0f120f03070c051507110f041808 66
    0x4036200e6078030780c11038000030100400e010600c00800e218500352190b1840b00f680201c0c80d004013070041005c00b26032400d0710740500480400080c1c2e041d004002454100c00b200000c51403401062010760994001e0200250480c2c2c10310700107000b29040c80d003c0c2c110500070b880c0b00006680d403040b6180072820a5500021100058040052440141c0b108a000099107090902c4031b6183c0e0480410644001000e441c040d100a0526601c460b04c00d04c211a0301e03000d040040c80042c201a400d403400c0c0042400785802520604c01142440d6000d107810602280d070210042c406a0308102c03564011b40391031f018440103000c51035030310b20107038125005416104005603000201e41c901605040d081d100000c2c0403c0c0105e00d0f000100d80c007a15041f11404852400f034484861010002d80840d1800040310000030b4a03000c040f9182c2d007002078a40c070700c0301100d00840303840b580060101c1c0c05a031548501a03005014680305003140c515801e140e60f0801c40000d000f040003541c003050710320004001c0311484040b00c91034400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 914768201 1250 914766951 914766953
    0xb030607020f010c030e0a0f02010306050a090f050109060e04080a090b0309010e0c0f03070519031b06030c0516020d15020a021005150d0206030c1c0b040b030c0916020709020a020703 80
    0x1d01c112840c0403283e140502815440c40d86c030549681012001524211030341150000396402900103a0051101070107244140d80d540c4c03c43d03401088800d010b1610701d400d100c0009001c00f420f000f90401c1c2c40010b40f0036030550300c1d642d803030004030380c0484e1151044c40290900000d0401d2080c001d9407042000d00004248980c0a201d000c6c00d14440c4042e10b4802d5030400307890a015280090080b0640d0b000380d42c407194004a040444180700d1b04c65100a080c4000180803500b030561700c11171a41201d106841c00d01c036103020301006540c94001c0c2080c45610b41c040c08001009803a103088421210b502909903042c1c0030000040141c2640c1c42050000056840139403150390784034151041d91b9221025840c207020460341480010b080c400ca00d0304c041e20030350300480031030740ca40081002c40342c0d030748180003503100d48014010069019095107904a40300d18a40003041c040e46c240402c02c0e0314850340050042e10b00c0d81e07503000c01091064005080c0c504611a00b140440c00003603078030003800b04421a030001c000c880d1031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 914769451 1250 914768201 914768203
    0x30c060c010e010239030a0c05010615030207050d08010b0d051504050403030e0d0509030d050318011a040b122a0a08010926040902070f0b16030609110d050a0b030607020f 75
    0x10860070405070b1040190705d217103290070120a03980c010215152205141c1e03c20f080c011f0141c115a04805426030342200205030094140c4d0003000a1845081a100b1110b806d90054844140910944440250400c4040070062041d4400d5500c210003030702e0b105040b406000401c0c04c07654112011408aa582c29814815500c01c0240c004041503a01d041e9141c00c0810300400d407074800c0d2007200c0d001d10401002050004884200031055110144001c000c2d02e0001102e0030a00c40700103495501031480d000d20402030341840c4041d0340080c0140c800500c0303500d816610403581d1404440701514516111039460380d165840100b400000c00070140041984400da00301454001c1400440100c5001d1103240020319100540170381301110710945006031148117508200240000d0344a000b0440c4030003004000100c01c8088200d100341e50265010004181c80344030410032601089501c05603039105205103520041c07143c01099201c541d01d6004942580204042490840c0603a0000d0168001c064801c2c50b0b203030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 914770701 1250 914769451 914769517
    0x70801031b0506070f020d0f03090614040305251206020304050f030a0c1e0f0602030702070b0a0e04110f030405071d0609040f0204111b120702030c060c010e0102 71
    0x15081d442080e0140b4110000e1028070038080c00500d43d80342e092519082d035444103034075040c0d030360085071840c00c402d0185001000d400242c003031007022a4107101e4080c109201c00c020340c8c0a0304d50240090054002124896117800c2d500300000d00e0036070402601162004907180c0c0400c00360f2040ca005070b107a007054a0082c3c201442c1d607010750303039543c010700820740159440764a8054030340c1c0042200b50b016800011144010112900150101e1204940c080420810b5030003184141d010f64203440307260340c4034000740384c2a10070000484000f0340080038903655803400ea40b02000e04050785040f81c5c030302102d0030420324140d00200e40c01c0d102504184010401c028401518080300d00f0522207648040c940031000078a5200042c10141400080f0b10f540d02c11500c9a612070050241900e403038584521f40070540c4a08001c032a41c00b00d0303a50246840541d41d000141c02614059a8020f000d0003007515800705022103a00803002d142e129640b604200d5049000a20080c2035051008001c599604481440d800d024a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 914771951 1250 914770701 914770733
    0x1e020f04060e03160302120a080a0509031b0a1404061e060f0504050307090b040902031614150a032a26060d060c0e030114090105010b0c070306180b07080103 69
    0x303044001302c480844219044502542d9040302d09050442072a00014074050700c40e44000d003200070014103010a250000e000c1c020499007201110140742550010054a100203090310350045a41007007805410040b554004000d40060000101c44d90f0b201a02c1c980c0020251106800e15104071042c405290700c0542507a1961150401503d42460500882d03581d420340e225101e1600d0703075603607240c000b9601d031703006001903e070001c2c220345101c1c551581c0003070f20b0700d840d2058003451400001ba40d0120704041c00848080c00d0009440c07418004014002d0b0081c04442c0800304030020084c5680701603500c1200248403158640e980c055040405961401c41e205014840d803400744800c40c100716455681181e40043d00c3e07440f0030301003a580d40e0340300300b42c034004c4103280c04e07503415424003d884911040c1500320506c603000c03d034024410342e40ea5000e601e0241c840c0d48420310081e04074640520103c0c00c503400c02040903040c2100412103200c1c584403c00002400c0d1111000070707101c9c0d00100203104203801d810b2142 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 914773201 1250 914771951 914771953
    0xb0415110418150b19110c01080f150d080a03051e1b0f04180c05040e010e09030708220501050408031209121c05281e020f04060e03 58
    0x905100301103002002c00106a1040c584031001c1e941250740038030410b0001c081115006440381c21152804201107070400e000381c0001e00209490021107000141d210071004c0684038250706444031090b000e801d42008041203038110818003d0b007040d40302d40c041c4601c1d0038000c02c00760307480e00e02d1010020700b60340b0060b211400d60344590714011070490a4406154002103075103c10395035180500d01f2500a4003d910700c40100020100f0b00107141c03550105901c0041c4d02c0c0c05420050201640003e640302d0295010b00d400e180d101000502900c038401c1c202a800a41140440c0e00300b0000b992800ca16600141d2900003028280d500c040b210011705050602400d02420214201810400d58a41d03030b0280f0818056506030b1040441c0403100244402c80c410320004084961300d48914000207190f0404d80003172200e60789402c000a00040d105581e0280b600710542c0780c8032885841503109001303410312000d04140c14203050314000880460384000c2186441c22140a41c845140580140061500c900c0c03690003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 914774451 1250 914773201 914773207
    0x7090c0c0201080f1302150a02070905040b0103120516060605010e1f0f090503011418010e03030a091e030f03060807051003110d092d021e010201090b041511 69
    0x503070f0045000c82d400a48140d940d40696542c0109601c9907400c0d00d800f0b90000418100240003070034010081c1074013190b036003c81d00c245940c2c0203041d00316102110054a117410007001030001130040d2070144da180d41e0614180f420101c8409154403a1032620100f02c0c1d501307540c0e00d010042560804800c4028120480d22182d40c4414070748100c0540899050781401c00148110401c5035602800c0038202a0001070020400e025002d0058400f8000a48441c02e004041e0000c251107507074140105840401007402075400c40e195202c0d03070b40c094000c084080312100460002011600d455001041c4824000e83e05c1c0c4042d920f1401d0017030215401504189000d0b0413148040c40140c454285c80800c2c0e40c45480c00180f00c50707084200d82400d00030241841044c50030102c0440a010043c9203400446c0e001a074040780c041040000103101071440e0b04020f40042800b040362301c00d1001d10b40401711950040c000414901c2030340d55000503070882140c08072184c000351408440048194403411408a00310381185103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 914775701 1250 914774451 914774453
    0x8040b070204060b0304120e010216080601210503040303140405030d08010e060105180d02040e0601170c1f0c1103030703020127150c02010213120b070201150b09060f0c07090c0c 78
    0x1901f0902e29041c0c00502140c45455169640300700070030304290380e5240004030102c0d00d856503035440300070a10a4400020203280204c10503002c60300120301d400c1d8050001e6240c640303542d0301524885c030300e1000c8400344482404009502d44042c0701c1010540c0e61135480c035410790b0500308202c0d407112028028904008042c00080248005d0220b2000c3e841c030100ca150b0180c0ca01440014040c0c07007640d007041081e0040100000740e480c640ca03c05101c0040e544182c407030500b101c02c01e00c22200324564059065141c82280003013118000c1c4550715030f80d4000e0341d00b001c02d003001c08017092542c2d0050b041180141e5583e0000480e20100719003c28199940c1341d0110081502ca0301c40503e0320800019004403240e83e41030081e1068001d604840c0d031185080080f607421691611a000303c860700000503a000c058441c005280c552040c42040d1401d6181400300c800e203424510b1995064104c041d4440e0800740400c6010790051a0b40c0203421001d902e07000403c102810610b0030340a903801c500020050080800c1000c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 914776951 1250 914775701 914775713
    0x1d190f0c020109020a091a0607050111070507031e030806121204150306090506010c0305180d0f03030f0524190b04242c1f09050a0b071e08040b070204060b0304 70
    0x1401b47d501162484c0d201c15050402d540181002140e01010300d8000841604001000c6140402c490003000d120780301d9003540d0184942c3c803c07020300043c0040d80c080002a05460a00b00b8022100700500849038000b2140c0440c18081d4000d4001840c81142ca40600e2006030703041c0034420181204d024180440e040050001e882c1e40b0000c1001424008041400300d209000101d6009030200000c261141c4d035121070800b0782c001015060280c001a04102095a218416004042c024950191503161130400c0b4081c140284552402071680000da440031001a500c0590a42d0040c00240c41019691454684001846103128000502c5075641c100d03003065164201075101541c0c0000040700400c40304138116038101c86c0c901482c4560180d09801011800c00d2481c01d203442210a40d1100d0032041e888004003c00002c4a100b107141003102040900c0c0013502c900c88418440d18800c141000301e4a05940b0500250003981250b11000780108444080d80740c1402010001c00070b010343d440c43c604244d2a20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 914778201 1250 914776951 914776991
    0x3010e070b0a0f120207080301060e060a0914010302120c030a2d020d0b0d03020604020a1a3a0b09130b0f22030206060a1d190f0c020109020a09 63
    0xb09041c0040d441440504038000d4400b03d8050840c40c008554500c080e20384904150005e0003000d0000e405c0040c4180c55081906c00c0368803100300380d164040020b1510000c082e070310303202444a0381015001d014a065150150034814065034903040c2c22600c903c4e044401100b200c0c50100f02400710035040c0400104102c0d142d00c08091a49075005c0982d0724001d520311100a881004107160300030205035100c106040e800302d1000d01440c030031134004000320381d515002c0c000e04a10130014180070a040190200100030200a5030411105110b007e06c1d000540c0104121404200348200359107407100815581c9181010007590300c50444889503880c4d8540e40c50780090044001d01e50040196000c011400306003080d40d40c4a201c1c400783d0800c0c01228960319000b500c40320280d03a2103005900c0c20300f01160002214080141a004000c216403590307944000c01c4880001d02030709503d51695404603400808041c1c02103000c68035a0b500041003c426510500401c96801d610541d0082d01d08100e2401d840706540324 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 914779451 1250 914778201 914778217
    0x50703050f0a12050a0e0d06090311120f07051005010b1c140123040f090606050d0f02010c030306081e0c010e21120d0b0306010905090c0d260903010e070b 68
    0x200946410004009484840307504451035404400d180f540800c21034203400811642b0711a50b41d00390b902100300a49607440c11002d80d24803000c002840103440e601550009411031500401c1129402444035218a0071500284c001200c140d40c001b583e60402c5016034030101505402c3c2c1c06c01c1102031031080c8200c0c880da4046c05030301c3c002c070840644050047d504010011094200400c02c11081e01a041c0d4140188088201242c0c942d0404d00002400c0c54801500b480740e0f60400310001210400c1d90046881452569080b02410358070a00400c440c1030030407100d60410b031681c40460000d80244606032a10320b4222005040040b2425400b0b11500c4042100b811429402d031151410070038424914200030340c141c090400120301041c5102a228540c2102d806d81c40e050b8255281c1c4d0741c880802d03030182c4000b16924a11944103000780c44003800e284e0109007040707001e03458000e050b20b01d1840d00c040525050180092402010a00a403103103002e102d5910045621401001c020380f901d04140f040d0302a10b18 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 914780701 1250 914779451 914779457
    0x705100f0c0b091005090304151403070503040507120f2f1e12070501030e0a1707060902060d0506030c0307030b0c092101090615030203030d0e030f07050703050f0a12 73
    0x1207202c050f4104002005281085410300039480c01c3c1420f5560380d0010b01ca200d0720024401c04003003c0f14011102d641c41200100101d52079603075401400d842c503a0001d841180d881c440d07441d00080020942d0f480c910782d18130a40d1030007401629401c000c21000800c010310005c25810146000c4109030341d80c09a00c0880c000c0e500b40c22044104c17126040c203540f07013201d8290402d40300050910b250300046280e81c00d5407400d80b010400c01c03060303904d059034a0202c603000902a01c42e0301d0785041501e07011409850440d00c142000715a42440380d011036100d40205841400fa56102d5040c002549800d1258450000c7c05900400c025455501e9201509001600c2c0300380c001c100140321640c540f1025544204d801203a11007010008580d80d80e61b008190807041a607071285481618002107035107010800c00ca0b60028015801c18a40545480040040ca1914400b070f210808c10410303442ca010002d000101d0041c0c01400d400d51a604207641000101042400d11f0f41145080ca40029102c01ca8205042041c0c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 914781951 1250 914780701 914780723
    0x60b0d09030c1a0f01092c0f1b0301060b031303051c0606080406060e060312090d050304170c06040f05060a020c040f020706061505030f150924030d0e010c0804170705100f0c 76
    0x207d25641030a2162089460030b0080301030003c0001540b1140640c0c0b00740990081005941e00c4101007000d00043c0d688480003540e400c1d003803011078403030400303005403540d03200d04441545001c01b4507100311211603000002160241e0104003c1c8031541c4900d100030105101c500c482442d0840c00251942851028507050040c0451465903948444684501c1154003508603030303450742ca0b50019255484480d10003140e81c07044554404250601a0649007180d1441d19015030701401c1500301700c4550403d103100003c42c41062001d0b4515540c0c1c1c003800c0e418a05190b001607440100d0b041c010180d5000303401805840c0a46c51203001e00c90b80c403000f1298441c00c0551605100c1e200c010b841c2140c6002c040145038408004010700501c00c89140980c6c201c3c80840340034401c03c1d20f800050548960b1641e10710000f180041e180c001e010750181c8040c00103548241810b515061f19100c5c00d484c405440c0300b034000c80d9400380105110908180d05200d186a0712030412000030190548000d1408642801c001e051a9102c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 914783201 1250 914781951 914782031
    0x50a140c09010c06020c0312061e030a080703112505060f0306040209120d05030f01080c1f2001060905102301120203041212060b0d09030c1a0f0109 65
    0x380e054841c1d11101006881c2d0751901078040304441d08d02510401e02c50511a141d4651003203444032030410041001e000b0309485102c5d40c032140240d130000305c3c00360103029200d155007030f000e4418000300c0f40c80a06c614003100500507107464022480856081640121010400d08203848003500550b80d1042d001c40e0007581e00d0500c440401c21626016001070040c3c802d40d103140c0541c542241c0078611815690021501587e40d030340805030b036807070601c00c919000002800d04100d000101d44202000c05500c1c02c060320b004012030100303ca00310b0030104070101c40c0d640b0101031000030301600910390001e0104100b00c8507141065602d142c1c0005910020070000300c0c100c060301d550f9001d400445400c005044003103460349880d050a41b44003031584444400229040740b01c500211592007440700b0b44d2164082c1c1824140f003404102c0041060302010b5041c03000a82200700000c0f42e000021001c1950b000010300203080018040c417004070103070416110b10341040c0100400890302182c2d8525152000c80411040300d01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 914784451 1250 914783201 914783213
    0x150e060d050a08030708092a0f0102121b0607091d151503040b010e1012080c0706021c030902150d06150c02090609010305060c0f0d0609050a140c09010c 67
    0x1c80300d0700034460743d800300c1045810b0750012042e5103d81101401c2d01e81800d040304840c2d0703015a5a500d00000500c5004181c0743c0340c10a200c900c5568201070045400300b42d0400365400c5950051080c201d8105410740c0741d0000034100f4007440c2d8004415080421a1605101150f9041448050a00d03034400040c4000323081e8110083c404c20b62003a005d4050a02860390100070b2a4550086506175074403224840000307030124034580107503c20000d050100e02a517040c005102c0d60f4825407d400e86141e0014014a4001102484520006c01080d00245840d8904400f400500028012400c09140c5440400300168558101c80c0e00060307541000725980d506800403c00c02408a600481c1e018000c00001d4604107401c0340700f0710920350084644a00380e555000c01c001103170409000003007107074203d4000300d86c002c0350071006441007040c4500f9450800d056655800215580da81c05640740c16118401d10004c90703098410b0000051810728038001e04d150210f1031902c00c1c0b04d060305960401242403204014098 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 914785701 1250 914784451 914784463
    0x80d06120317070f05041401050418090203070f080d050a0216080d020723040216060903022b0807110307150b040605033705150109150e060d05 63
    0x40806511000d4481410014940c50201d002042400c18160209a5003801120b8020141d0016540c06181a090483c00c2034500038000e91141070110500020442c015268204d000c040d0449500261464841c01011301c0c000c040c1d0b009400039950311009000b44400494401c00303980090030304550f60000207904078500300700b140056001c00d101003804150b420012484999107801c5900b215511903c031606a08c08000070620400418400e503a07100d25801c054001c1e00401800c18200400c100351500c0d072005944040d042140144c118070a00c07050030819404103c0c5240c2c07614401c0100001700b031340c042c00480b0060040c60500180d11001e00c00300c0000c104646905074404010664a0b00c2041d030007000d0144050b08074480c0d030410398003045506000604c410458201c4100d51b031368207080c024914260304518801800f0044d070007900000f00f001040a541d6030b80401560440ba503241140c050304545032031400480b1141011010040040040c80e000c0c0c1142044522648212036450002e182003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 914786951 1250 914785701 914785709
    0x1200d0b0d02031509011104081c03090f0503040e0a23041509051b010507020d03031a1c0515091b18180c040501030b1305010605130f0b030d0c080d06 66
    0x1204138104041c0c0500c044007080e024060540013402a992403140c80c0310203006502501d29140e02407031000042c0380022403000040b140d0360500081e030704555107d1452072075101000b07130f0b9207a000040806c182c21070088041d0b44071103041c000f00041c0c90410692034000207840c40340128410f00201290170310014510b2080c45200c400e1042082518030f06d409a180d400080302c640400e40400507880455001d101110002c503401062181c0c511070342d544c19002040310121070944030190001d414500d8a5440b0084400c8106180c0c0c0c0d603a144052070103034079050101d10340200404240080c8800490300048203c104e001114228002ea00c818000c20101e82c00002450b607000e81c01000d00c90041c49001000712106c1108050300c5180166505010580b031007032000400d00908000060008442880c0040c00ba501c103400209207150b403240003a08004030b501203400c8140e03840306010806040b40c030804c1c5a0000035000b410100c0d20550000e003096503800009402e48100240980e2001d0300f82d88000050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 914788201 1250 914786951 914786953
    0x2070512010606021902090417160809131119050f120609090a05120a03020c01060305100b041a04091a04120f110a03110a02061b01200d0b0d0203 64
    0x144559803035001c0e008601c5070a000d80a40c0150940c58034102d00901c0805401503c141021344032907445200512034201d00c0c010112042c402d89281c81c0c11882d0700800c490081c180326468040a504003c003c0d6015030040010919001e81203001070a0507040e038032031002415003080c054080840c192410301c10b410045038a820b0005480d106030201c1c10045000c0d00080d1901d02003036885000181e51082d001d0400341095004214501c18266a000103250700c14080c54090300303180d100401182074601070f13042116941c120580700d041c0714080d44940d0b000315500b140c040c01642088140740c0c05000f510a041801030b616625440c0c00c1c0401d0074408241800507841d068041d240030708180750f442403200140000584885000713681d0f0703481148180007610703003a406032541404540c0d0941e001c1c030f00382d034800401e4016048004090394460014000c454025010400e40305a140405400c6455000f401060041c0350b080581a9085a034180c480e01200564001030035402d0000140001808200003585 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 914789451 1250 914788201 914788219
    0xa020405010f0305010605100909090309030b04051506031605090c043c0302010f081f09020c0f0f07090b030a0602031306051029040b070305250803130201020705 71
    0x507440310082c541d01107a00030710007000750540f104100600610046401c0c000200c46003014448018254480101e2501c20b040c82011140d49503103005c2c40700340c2124140c9080e000015804010308048600d80d51007003045000e8025860302c48a644030014860081c0c41c060031081d000115907983c8201160050b00011b1400107902c81092029821110080c1e0029048000020600b240307082c455074000a50307034142c54003d41608401821075036071800514030010782510301c1054034400e104d0204a00035066509025030740d00c048020b090302d449000180d060b500d41c02048070404280e40401c204054400c0e03240041303900102640000e1400e0902903010300707021710010034060308013210743d0812101441543c1c00d2100b030b60b513116002c580c6e492a210b0b00a0030601c048001031035002c8002c1805011904555050605440e00c0b58000f5940007003800324003141c0000b0754150f014203212906202150390118400500785155074041241c0005001080c0e0003001d00014000c681c024003100300078100113030035004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 914790701 1250 914789451 914789459
    0x3060d081912020702090408030a1b031508150606030403051909030b0f160c02010210050114011706030d0c02032118040b06070b040f080d050106030c1805010503090a02040501 77
    0x340e00c8030106040410a0200c580b000042c0b207009940c1c3c0301c1c0d00104180003598494803100c4080d0b000030036203008950b940d15298441c4100c1a0a40300035202c83c0d800040800284d00b071914074061640122440340d10200020020080f824203403540709100761066501e82d100ca00d02518580181498901003652107140f124809130b202507000100e900901201700c29440d52218008116815111181500c0000450700c5001e801011070b410200e1040c8100c41404540c02d00680484a080e08091000c1d13000e6515030b8081c0d071340200c0c00d0a100e100182c0046040c103041000959482d480d104060501c031000840c1001d564080c007030844000a400c0342c541c00802001c1d00400c1e43e80c010241106044020442004d050401d4814540c250340094001440e0182a4607400e251050042040310050701c8901403800046440000d00040801d80c100880c0d20350400300302500307a40400c400e0008000c048240d0b10504e04901703034400c048030001e007449580da03110704c03041604010103540701039005410711000007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 914791951 1250 914790701 914790727
    0x10915020102030a0b271302030109051509030a17191515020a0c030618082701210c050f1b16180b010e09070f090e010f030803060d08 59
    0x144030f8400d10004200c4540398200f003104c0703424001d00035029240060038555050441b04500c64016540b102c51480c24806540040e00391031003000c0c101c400d41c001c4c40c0011107100700e0102c0d450304501c81801450a1062408000340503201030310303016403469040d2011407840c0a14403602031205c2c0d008141801043c0e61400c14a001d0b80c2c0344d100782140ba0104007170300390420380b0104880c00c042c0d0744100c020010321320b107071145e901621051800003a0f4041a0000c000090394100c0103101e41040b030081e06422191001c41d130001f042060080714144a0040140b5002000c0c2d41c960740d075200a80e60b40002ca1000e034101c200c40502480d550030b1007403030002032411145070325203400c10080041c4408072410229443d803c410703440210310542d90940140b00c520121820250881a03000e8410324100d0005141c0000150005c0d8090303403a00301080c9400d01c0700e85219401410000034028880c1c4281083d4504030030403c4500b410b20024008100100102d1705aa032061943c2c1017594002c0703101622024491103075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 914793201 1250 914791951 914791957
    0x180303090c05060310050f0a090203091b03030405060f0c0f0d090e150904120c0b040321090201052a0a05030a110609071701150b090406140f0f010915020102 69
    0x16a440c0d034400740005010b162040480e44242c0b011050448403a00d00001d02c010b050110712031a5000007002c1d40410651040e1020b98880c1080d4802060b8400d512a2000b00c0d820103884d00c180240c0040105111b6070311642c0407174590403c006507955480c200c1d03148450034803403010114950b6001d150380000707009600584010130740d00d50b1803061010b501e58050701c1504200e549044c6800070908000500850240c070b01c800e5411003142072010958856a448070b000b00000c0300c040300031403048032002c48000210702d4032002d0005c00f50000c0181602d5034002800301d0040101340c280300c029075103490200e0550601d0f4121844001002c542c042e5070f8911f009501c0703030091221000003c81e500c01c94481c0381c80c002822030044040001a001c4207090030030740d200c407008404122804e503407104039480c405a12126018001e2051111132038a07004650b0801c0140c9003142d02c54078180d81c004401c1100350360781c81d150307180060003100c24000d41d10501006030703298526a4811100840f940c00002e0680742c042d001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 914794451 1250 914793201 914793203
    0x60a0309170d0e0a050a030c020a08030d201e0906130905041a0403091509121406070309032a050319180608071d0310020d0510051f0318030309 63
    0x42400008000400b083d44c40c070351118064960b600440d480d40119008040c07041c0003500107048443c000303460b24020b0f032841e40201060b45011380e684484c0307220490904503046061040517841d5180c00c0700c04064040400e0014002c080110000480800c1030765000300b22544404903040b40c111f51030b958034007400207150031501640e0300900d182800c85d800031000052407040383d07d9101c5200190902202c0c402c020300e565010018000e264101141d041e010800c0e40b0a5103100340d01011092000180550821034060102c10506040510040000f030300700c00324000d40c03040d0304165904403a158400c3c451080d244000501503020001c2d540d0b204841a60040c0803418064907050540316054a102a0b001801e11030040050301240100719890b1142562403204002c42090031010314020f0000b900f4180000318041c145a400200c400a032643c502030260312032070711004400b007a0720b000003144254001c1502080980551444541401e01035440040400103440b04e003a0680f0703036490088c3c014801c405e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 914795701 1250 914794451 914794477
    0x50d39141519030507020106050406080c011e0e010302180d0c03050105101d060406050901120302010f060803040b0a170f011d0603030d0b010c0b150a060f0806060a030917 75
    0x71094000300300380c104880078409844202c584461403040120002c1402608090443d500d440000815540f64021340c000780160308040d01d28000210000342004000f540895008604030207603480380c6800c280d41030700c404001e080c0036070340e1490f51908007039001400300130903800752001000c03005102096000c0020ba9100300020040c50b200c00c0b0005014001901c03030303410508865119094480320000415403c500c1c090b102040d159241e01c005100a5800d07000050002840b06c4040e0503d03509020340304543d080001e080041078100211540c0304c0c032a5008034000c2d080001100305955118501107a20b590300040c6c401941c0c20449042c2400e00800c2c41801c0c0c85900800b0b40f05d0441ca80c040711940964401001503182419051022003d4001040c1403414406494207201c0801c0e0b051109500c04c100803019601d00b40901d204005c01060990000400c100055102400c000c0d00b1242031a00304404541c1d65031103030000f2500302e01624051100401849204504405010820006d402c0b0317400684 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 914796951 1250 914795701 914795719
    0xc01060f0906050d1e300801030503030612030d0f0614010203090901150309052b0216061404081f06120f0b07030212040c050109050d3914 61
    0x10755000c2034881600a580d40611052141c80010b1040d51505021032507856444d90110700540320003002c003000015100700c1c1072614014a07090002e41c0190b40c0b50300003d040c40078043d4155107910390b42c2d02008000900441c50b0301405007002e0750410583e484218600410b208541c814140b8030050020340c407a0440c5900300c2429500da543c000310580e00d0940d0701400c07842c0d031030f8070b030040d01800b036401c910b41d007814150313900744c298082076080c0300314a0300c0c5180780455807041031132a4000c49204401d01c801003c6402011081c06004a490645011100b481c5044da03081040040aa80140305650200d481031041d031981c58820902d1944d1003510700b8940000300110340d030701d0342626030000d08250000d04140007203010f00d0004060b01801078000d143c0c2e00d4018146461465145500001900d041c0d910443c4e512040181d981c3c458010f10280406a074040000d042d5a40d80c05400c00d1074422040443c040d80c40c081c640408075401c502070111000300300841440d600c20b00e245c104203d008040340244040707 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 914798201 1250 914796951 914796959
    0xe03010c0314070e0f060d021b01020c03030414070f06031505011d15091207090608011b0c05160b0c010b0607120c080c150601030506040903230d020c01060f 69
    0x2c1c4545140340301241440c0d071203039a500307000b04c41c80701100310604d40c043c0c40040f204580d034584002500c0540524800181d0b5100d48600503510340384541c07080503e40c0e0040001c20310711007010040c0c80c0c002da401003501001000b030801030360403c48103030000540004503410000704030b50302da082000d98545c08a400c0760907a49450044450095401182c0341d007410030b04040403142005040c005860b48644e00c40c80c01d21362040c0c00101041071414503540c01e58031895040c4800d40403449528010002c1c02e000300010081c401034408248010345c0003a06018035000d0312802d1103c28410981d1002c00002c4c0507483d65100c000040040d008002204001d41c40c022003480300d130911f14200d80003950001c0f02080200c45441084030508003140d41210f400a0920995909020800030454a4681c04c440d802452130080001012200700404480c825428000c4c1000803e4010501000c1070a50310f070120794540f69030351450003074803c036000c4000b540d100042c0c50800385010740c085010344a1450007080e5071561 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 914799451 1250 914798201 914798207
    0x9070f110a030f050703110a03090807120c03080a020c1003020301060f1803082b061401180614130f05010f050406080c0d1d0c090924041b060e03010c 66
    0x106080080100e020798000c0f0000f030340220068061075100b0300e00030030017101421904e800c2981d001c4044000c02d50150007804400824440500a080388503018903420055844095050341d091002400d400400100407148510904c280120741901034200c0d4014081c415004000794000d00c5860000340e0701d05483c04099214041d02c103400b0a45c034500070f0616085450f680d046034880c00c11100c0c0060380e03030021800600d401c05a980300e101c0304540050082e140207100c0550252184142d0304214203202201c024080003190801a1156071400c8030210ba403441c50320640b03100c4c00b5148501440780607400503044c080c0007980003e07200203030f85644400000c0ca40070740d501d028a000c0c45001c01c48120024160030200f00240c502d0700b9810a001c15124100c40781400103803443c821501007504021001c1c013103070130002c0c5115008400b8a004001401520740102d00f207071000d1814411a40101c00850b050018580b0a59040464286441d0b0346903507a002c081d2440c84800707c000d0195080604803062580 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 914800701 1250 914799451 914799463
    0xf160c0b040b0d0e16090f200a03051b0c03180405060d0b04020102071703221208091f02070e07030c08010302130905030d0e0c0d08070b1509070f11 65
    0x2c24007041c1d5040c43c14508981d4003400d810105807030745110f40da2103c4041001d07403180c00300070524480002096410501d00000b030300e64084603002a60301d0303440340c0704074490090100c03410402945400215500c400304e40c200840e101c0d80f04030441c2d20340884d03555003104000c4010002d030040b80304602d00340f4030307460140b20541d202218065400260f2000c15804100c240303442c80d40c4144140305035001141c4805000c900c1105000f0314107201d0303101007038500d403a11112041d120f0700c00035107100400045c40c00e49101d0080307902e000014646200411651000e46031100000086d4005205c1c1050410201c0341c000d6840c0014850592480c8440300400c4800340203100c1e450808038241e440c4501d580c2181c0070311010340300103400d400500f43c3d20400c0d031012a8007031001d400010740aa0000c0f910045026185203032050740140607110703090300b10325480000c0c900c104692140d540301c2c0800d01260356880c9000c4600883c0c0310310641220382c1104022103140d10100d52100401d0360386a168151220b0f2201039542c00c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 914801951 1250 914800701 914800709
    0xe010602010c080603120f1803030d020301210c0b13030f050d1b020901031416031202070803120604050402120d020607030f090c0e0a02040503010e060403141e0f0f160c0b04 76
    0x410802031402c7d843e15010042100d400c844007005412510364003c245164000c111500c040c40e0301000500104117a107000b002030303095052420300340342c040344c072130000000591188020314440050510811600c0c03034543c1000310f401005542c02c1d4131403400d106840b00d80802403040081d802d464601d0b00c01440803105000c264000d0900c140aa0950343e0b0450700d2960701c19225001e01c140020a00d00007803240310381001d50f1045105150b03c00100b03038081d01d4113400390805400350300240300c148041c04817010540e500c1402118040f60940b40c600108910000180f070240890080300303820404207400040c0740740648100e40e070800c20b843d05110104110749412100510783c00101600b044445800d03e413542d04030a2881c00103143c04d544100007800c40d00c058241485c2c903004141040280b60f00240356251600414020a1401e112141940c01041c115211854113440101d12044203895a0068900100c14208400e542b50405880b41580400c0e84400715030310441d00380c0110300340c2800c90070f80b002c036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 914803201 1250 914801951 914801983
    0x70c060203041a0315060c010b040c11191e0303061a0405010c060f0e030c070503010c020609060103080f0d1d100209132003041202010b010201090210180e010602010c080603 76
    0x803c01c0b008950703902ea002800c20a00b200141000f481c10380d0350180101140c001d00e45c000100102e5142c14070040c1c800c204443c0d010b00806041c405e440d4400440c00412010b061000000c08401c185400507017690900080f01b01d0061038080707881010b8056001e58282c039010f0041111480000744c0c4404188600c1c003403e0300007182980040001900c6401c00750284e42c0c21203001c40d140b0700c9071030101c1c40e542050100240076400b181042040c0d04082c03090b0280c2c50103503c058071851400c00d03451360b83d0301418440240b54400c0014401071021015069811803d501001840080541e606400f01c40200b20f0048455004400c2004400c03e49072084032a0a103019100c20011007400f240b01d0000c2c0000400f01e082801e9184540240d00c080c0402544124071513170240954028420b00242180ca903003290906580c503041c03008015940b4034200c0c1d4000a1140380c4808021030480072079103080c00eaa4041c089219542001042094064110140300300d00c40d5a4807005072f40c1d4808040d42c98415504042032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 914804451 1250 914803201 914803229
    0x6070201050a080711030d021c05040c150309050d0f020d020601060e0d0606050d0b0714030405031902030d05070504230d0311070e07031d0f1005091908070c06020304 73
    0x2080f0f0050042c1a0b10503618100910200b250840440c21588004104015a0390001e80f25102000034204400d04a00c160001c1215140640e1400450310450044c480441044842052000c0c842c0d002800e08540c400140d0f03500b0301c00380c4d02c00783c01030b4041a0030002600800c501505002d1000820703174121207050f510105c102e82d0a0040c00b1140d5a00d09050304c0c2251507407404240c80d2136115084400034131640702c801e060300d00801c000b0b0807030480640304c200301081042440302049000050b18800ca486040681c82800c5140342a461441485403000c0d8050608080059454000300500304070340103601c8001c0160030021100b45004a0341608a900104180c5e1241c0400d1003401605414a0780030308541c085515a0020403c4a030100c0740903002a032503c0c011041005040d900300030030021200144901030015100e81d46502c4059400002a0340d03400000781014020807081c58250030840e0551034111083c2040d1440d544400016100580320480024200c2d01c0017044800300e550351a60a81 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 914805701 1250 914804451 914804467
    0xa150905072c040506060307120f03050a030b12010509060703060317090a0e010801020c070605160b0402031204090b090115050301031b18020c0d0311121e0405070e01050607020105 79
    0x711408141901480340c1c41c00c40008a00060480b01d0600840c0141c2c010001440d219040524111180e0003194122058113140c0740011008104c0c62840d40d41803c00d96240c6c0c1036444203c0091080000891340a005116480d449010650145005803100c0702603c0b03250780c0d10241034064030319074440108081052070010070020b4a40018292000e0001c0050750003070755038803a00c00080d600fa004117210365400190f040240004000c407030010115800c103036040c0000c0240f0310711810811040a0000e001e84000107086641c180141c0d00b124140480554442c1c0c1c84142601c001c1408180c2540038040c42070002c5640b038146e200e030b1311f0724628690b90513155038250350b500d180306d161601741d211504017100004985450115000e80143c0702c080720041c0c55002c20745038503107800321114920090514100d200c0d40540103a0b0202c9001c0c00602c40c410105854501001011503010b00c91420262000b5041c071042010101d820411100c07030b0b10071580f2990706d4908001c8180303e0301c04020f002c9542008861 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 914806951 1250 914805701 914805719
    0xb0108060a030201050c0c0405160801060906052d040b0d1a03061902070501061508150901210206070c0e09030f070b060f0d0803240a030f0c0f080a15090507 69
    0x82c0e1b905034941070722611031b030050108003905c80075105118045206031100141550102d64507006029030315101c01010310f0018040c18611031800300000341c0c0200b00d5101082c0c81a40e0100c1185482d1030305c695030719071b07a500490100c0d401071401d4244041c106040401c0e80000088014800b00c4000c01509054855424180c00d1801000b0b48900705074003031100d400030500030310810f030003402c050900380808207007401c0c000c003280001040b1013200ca1003032640c14104e88419100c00c1c156880341052071f685000440c2e00c5000703080790000c0203601520005a040410005004110481d0322101018586489510f09151207019850a03400141c005004a40204141045454000002518620040254070302194141207556020b40e40d00c980002407200c040031415442e954840c404a00c43c003840c41000000308a80f1840c0300190522014500c2d4009100082c0300c04e01c003c10b01181d034190500c0e41da21075262110070000040c0c4011401200c2c540046156014070107140b0791140181c02c229060040301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 914808201 1250 914806951 914806957
    0xa0c0e0303030f04031806020d0f020a1a090a060515120303010b03060f12010c0c050f010c0e120106080a060b01021005060d1b0503030f0d270b07020319080a0b0108060a03020105 78
    0xc1c0c0811103107104003001706d698261010040c1c00c2c154007501402d012002c1c090003088c0940880002c55000d40401c0300440c2040d19220700040c01c103941402d140d1143c20390f00f031400000f150040c020307a00c1c0c042444403205456020300780c49001602c0c0129036801b4002926102d010900c41c28110100810000b052854030011040034118001c2c854040519074941840c21281890ba08034082a00c08040c0c80c24800104600314182481740024040d0b00400b40005010f000c075800c0d030300c4c0a040b480c000240072032000e400a0340a0b041140c1150307481c0f01340f07043c0800035208400b0010301501801161511301ca0b11800b60910452025154100e01d24407a514010a000001c1d05608040d52404000c14584e80600080101c1e881e1f0400c5a0784850010f95420111100e030302801c2c1010718140155071002e9522900180c5458012403060b50507590010107074254842c2030f500426041045800c0b4810a41000100307004141280003000100700160064401401c01c1d07a00d01d521041d0740d202040198031580003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 914809451 1250 914808201 914808203
    0x907140409060908030a0506030d050d020f160302060708011406090607151104030b010906050f060c07080616080f062b06060b03060111010902060d050c070b0901050a0c0e0303030f04 80
    0x6071240c071a19144101c4004507411207507014008140820144607020303c0f40c02060481c0901101d90400e40003800350300c101884408a00d1300401d00c040d85c03a20072400c0d280010300070814409008040d26000f511043d0032641800890648000421800ea101000503a004070182400d458001c192040082c1d43d0041c20084a0258046464141c00c25680c0150008000a071040d15211401e500d0f2000c50303064160070000000e854200104a1581c0d01c0358080b640f5001030740c48503500d18a00e101a0304000c0907401018561150a040c00310a0f10454145650b05850382ea0b1244c0980f00c50110062425041e0380060f4403044080e20031203070800c00b28011203104d18404c20b1170801a419600c01c0250b0324160301a5500c10004400c0100c1540c0100c07415002401c4000208038004250f4005441401400d0002e0300c016543c2c1c000a101200103c101c2d15001d40040e00708000d45060b4403001c1c0640b44c11182030680c00d052032040d10005004646040150b140200a181180d0300d464001c40700c1400200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 914810701 1250 914809451 914809459
    0x204020712020705030f121e0424030b1942090f030b0123091003170721030b150d0c1b02010f0e100305040b07020105090714 55
    0x20000040e118140041580e185070083c207011860007081506000602c8030060b5035400260040402c800010200c0e5600d80300e440158502a9811411032040d0103030b0303040b030101104212010071341c0c070304101e044e8090301096a0342806122041c506004414031a4400b07980d445000b104140180d24090043d0071b5466070010588080203c002e481060621524482022401061079101116035001c4e01c02c0019052001a48501d90720b0341e0368141500d001441607040d1240d4568011411102c195101c20741c4004c010b010b0801805e0200b0108409034041c270007200d010b401c80e520594514100c000b80c0740d02070b0b0000b6071050070150b800800c860000f40310102c841015540c3c00303140000e44c2c640d002d080f490720309800500c0d203c90b08951190102c40718150300d0424401074580303518618030308443c48a40c0315030a01c3c06142141c1c2461b130507646a00c0c0c060f07186921059004400c00000e5065020070310560040d100c000c000d4541d21001c0c2d08a0f2000d4500a4050f0060300c0c090005628680407d030f001754000d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 914811951 1250 914810701 914810707
    0x60c062a091e0406140a0603020f04180b040c0e040b011b15090f2a030809010e04060b0d0f061706010e090a0203030d0e010e01140105010c1a042f1c020402 68
    0xb000541181c8064001a24040404101480d203090640c0d00b04054411030030110320b080c0c0740c40702e278112074081ca100305541144060400100c2d4050f641040b0140c00001e032082c0b02c515a005005800280e400756801c1c041d5285c00100394141d0701c40c00717a940e98070451612105203284036860300c0071407540200312001042d1301c400400c0006400702c1a0303072010038003501e030b00351b100b4102d0f8200441a030b040481da0100f40500d941c3c207001007800c00d000c0b104142d03000d00f0301a1140180c800800c000d001694059000c4110105001c1074404494200e1084d0500003c0104800c03a103c0303203c0700d88a41549240d031240c0e44440014410005980f40c0503030030403030080c00c07168407180c564000382c6568011002e00d8404e5440b4400111001424010180c40600c200c0c02804640c50200359440c2c01c00c2d05114140c10443c81d40300c200d05018003888900508055080c41410710f2600703040c400404040c40940001c9110446801030f00d1001030000b80c8220080181581101d011f071591b40c60303200d864241c0580c0e02550030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 914813201 1250 914811951 914812009
    0x612070509010303081f06171e070302091005040e0606090a080d0903030e0d051b0409060e03250b06010c2301050f090304081c0e060c062a09 62
    0x40d4100500070340c86a50395446034500701c82040c00b0444d106e243c1060080c3c015000b03108103034201c074000d03080d203203121000c0009035030705001c0c20044c420f0000070402030105c042c244254203900d50020b000e0180706070b030b05075900c2d991103c0440e00e0b80b081e842050101c6101d0000b2070411b00d420701c010240004020320000b140c90300c03012414140520749c00100c011500254040013015009008102001e83c12034898601d000701d9140c480d1950b404041c81c0c9001070520151640c04d95490b80001c808940282c8200022070083e0b0000d44c2e03952014005040440d1119040c444400c041074694076010742c4181198003540794600159134510312000e040380c21401560821218243c0c5d082ca00ea03080342c3e141c00100711824190261038148e0f82c0031303003002c1881d0070812080c05040702c00140c981a01daa000c0c0f04810740c21075104121840b490103012240c0c00800042e00c9680114000348140c0111075408a00780194031815001c0d0680ca440002a00408000d0203100418a0922000001d9a0b0b0380000100300c1864 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 914814451 1250 914813201 914813209
    0x4090c02030f0d06241d03010e101e150e0907091109130b0a060e060c01020c1e030a0912060e01020a0306090e15012601020417010c0c0b06120705 64
    0x4600903c0d94803c0c0e5550040100241c0190880041001d0135a042032544450400420b0124540700002100b00302c0c030381071001034600354044240b00c0750780000d035011075201d840d00784058a07600d81d000c80c440c8203031078618003020000d1151380b42e135001002c0d401182c41d140c104a982d0b40b0800901c440100c1c0240030001070040d40c0c40c011441680241c880c0182c0c0c442421041040a405d8804090503451900c0d080101a45403958808143c03992070921401e440d08400004255105480f400c1e0b0300e03540045200c4000403400500f10b14101c202c103500b1030000f2080c2e124a6500c3c02080e54000002e070f103070901000060a40c1c0c0807025568090705010a40340c5400c4a640d082e644200800400207070340310010040516607115004000318888007400341d4a141c0c000031896a030040c05107004030114400702e8055106180034036110702210100954850f541d6407a10542e50480d4200c04105500b40b8a942814a1185890b41c502640c4401c030141581c80355001d1020007500402c40e052a482620030104080d03507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 914815701 1250 914814451 914814457
    0x10f020304060e060a051009151d04120c0201021f020c07080303011401050702030c01050c0a050615010915300216031815030b040204030f0b1f050604090c02030f 71
    0x1020b00004a4401e81c0e40c2c0700249007403c000c2600c0000e80c60182402591034a2a2802003190140d0601242608881c2c02143c0802c0080d4004841054028a0036031005055000c41380700f1401000040090315036101d01f9940601c0c0907078000d005030031800c0ea005c4d41c05000126402c22152a40c401801c00115001803450700c3c889070401c902c140d1011004000640d5484440042e2890a2070050306000c003c0d0301017aa580207016045d03042c0072010071040591041003010042d00340d080700c12511171b0b00703041109801c0d4072101000c16000502c0c00c0700c04500804059402c03600c5040300d989100c1504800c60007402e901c5000c090780c141040701d18024a0054804e40040c1810780d1002d58a18030150b020314000e4491f0001c00035181040180400030002000142d80200d01e00071079003004075102d10310000040081c4120f4100414102c400d50fa0324080c00400740100c0d1040681321038103c151a105000141c01c5211403041540c801002c0100f4031440c4026000107844201c5801181e081401c801240c1c1383c550 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 914816951 1250 914815701 914815703
    0xc1603090810092105070803060d0c15031116200607030306090f0c1e091802180f0a0b16050d0216050901120f0c090606050a02010e06010b030f0702010f020304 70
    0x3901c0b02d94030018444000303568101001d40348007640889800b104c020744180115500a04040404000240d8585681001d00c441c940e00c4402101ea00ea01d85801c0c500e00c4080740c05010009260640e40ba607022160001c884d00c4d201803d400d10110141079444815604003020112034660b460310011429031540c0c3d0190410034440d840100e00c50341003542980440b88441281548182001e8440d0407039a0842ea680c2c0000d1441e902482c9560740300308042d5100500390703001411b4070718184140700c0c05d0a030950160080801100483d00c00351401d40c104020251031485060303100d0803038a0b082000105a00041c80e8002c400701300e2813602940b0740c8840d42000307641600c141c0542c006c42c01d2416104045600c2201a141c103c681d50039550500c203c100b203020b0b03101401020310034144a03d40c10f000518078580006d00c0d6074071081c44165100c020080082d0050121240550700304040b5485d440004512a81078603022080c20782141d644010b00c00341003030084c102000359580c40d03840d0070292606000942c422 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 914818201 1250 914816951 914816983
    0x70e040b0a0902032e0524040506040308040503150c1603020115090b09010e0f0f1302091f08030412030f11011113060e2214130b0903030c16030908 65
    0x1490381440080751400c048610224000fa0445c280401c0d03444010300764010000e4803140d180e00c807072031840461a201d13640244d5030004010400000300603500300100281c1c2e105400743c030005000030450911000c000d543c0003214420030701043c50f4514000c840107031543e0180c400440d410315840d00200c108032442c1c02100e800c60302c4820107001402c2000100e401030201280580c81c900d001c2c909200c0c69400944981003c2c100e80740455034802d241c414a19245c0e40042050843e42401640e825200130b003c1d118420425255a00181105011041d141243c900d42200c0c3c842c03030f00a035401c458110704e00340b8240c02d2207444015400515424407451310203843c41042596246d800030f501400c5003107540e101408004074622a09801d40b0384000c3c204040b20030152598a0844501914015180c0c04011440b09030710801006220004150520219801448081950b444a0f020700f901c0b131008490961030800c042216407155602c490082c10440d02900d0615119611210a2401d0404420b002414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 914819451 1250 914818201 914818231
    0x110301030b01091b0507032010140c0901020606190312030603021504080c100201110a020303010906060305061c1a040506071710030f14120a02060f070e040b0a090203 73
    0xb4900113441451502452200d40700004e400c110b200818a01c0703440002402c1200c034103042c1c0380241d20301058a902e614141d0036120104509510140100141070b242030700c4c219000c001c605001038003001c0b91080301040e4003400080d0784071014018040310703950000d01c0340b440381240000800d0340b68240010791040b035030300800c44c41d1450042290400b41071208260280e0208401c014a600000d61140103142c20781b48000404a200802e03401040c80d081e40001560000070007804060f800b10045040e40c89582081217425118076084048800860311705800a001c0c55030a1070040e80c404000000c98440ca254903215440e10340c01c42c00181e0700340d804861070340c442018020400c0d0006220701105a49403070492251419081d071450000c038500c40a400c994600712082c060000c04641544075061300400c840851441c144042d9007507111980b000014021140441c8901400c8000180600701d15524103018660090802004220010304551301c6400e014002807000214006148034030191134690384 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 914820701 1250 914819451 914819459
    0xd020a0b1809100509040609060c0314090109050304061107050a0b070b28020c03090a0b0304050d0f080c0903150708061201141303091a0d1103060d020108070201110301030b01 77
    0x4640d42014410b481152400200509080d104466404552044401848030345517070030807400400711b41e2000380100f802c02c181000400d07019000b9040003418402d1001c3c40fa80d0f54084a400c17100611001403aa40042004028252062032250003401c0d0700b0041e10000d940d0740000034556400c1e80c1c0080c10220020420030203000b09131848652121801d101079200740c4818202d145c17005808a2214052940400d01c003000715400c006442d041c0c14041c24018400f42c503084040f103540c0040710115034600c90301c2d01100820f03100c0c070060000c41c103954803a05840c1d292141c00a02d6604022003141c1c0600c60342c002d19001e900c40c070f640a03008180589445203181008000c2c0644010081c1d44c20025a040403826141c124a541043e6032020814082181c090090b140444180f4000d902140808220400e040c011001c444010072801c1d00b01e000402440d00300c00c0100105000460350241d0102c074510300580954000c2582c00c1c2d004040384000102e140000788004180d400a0b04151886104d4100501c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 914821951 1250 914820701 914820727
    0x7172e17100513020936030c121306050306010c0b1501020106090c08130203010b09011d01050f100c0516240206010308071205120a0e0714010c030305060d020a0b 71
    0x40e00080f0101c203c0200a8468000c142204005001b00b540f420700c0700648403400d5039213004000c66190040322000e20040b014446a0380f42c2000d04d0070002e038055800320399004a420b80850303221b94040b0791241c00d6680f0707081c0242c441d5040280b4440c1030198000c04100001c809a2400d8468050302504168640e0028002421075249404c98015149400c26418010750081030b802c1e44461590a82c107810701c40380c07000c24058804203030047d0300200ca000000c81c3e0441e0307000340ea14034900c1c11203c4030308036a41d07034003004602040d081c1075070740105d1210200c80d600707881000340600c0680624121203074080850841d010280b0f15034820100c90400b83d680d803e81d201048d00c40103400007140f0041a40c1d50540d00c1d840c8051194100c0109000c072040d0004000c2402602036400c1184112541d201078030b44903803070002400ca0845000824099040e011030f1004081104102c1000181d480b45891138481d9016001864068140742c2d1203a040482040117a0ba01034000d0302401e9031180160300c54200140907 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 914823201 1250 914821951 914821961
    0x30f071b0f060e04050603100509071e2417130215090105030c0d0f1406030d0201090503160c1509170705100c0201050d06030b07172e1710 61
    0x858410707524241004902e0380540c0b000924039040310700085c15216400060b113071040341003680380c41c0b80c1840100f00c1d0f50030300442d164040f14804009030300010150054900c10800c24081d4400029100c1350702c11407000081c000c0102840b07107050104080180d501801408181114850126405107500004605000300b1200d1000c1841b0b403694180550240060030301c3c00000d054400c0d86002103000d404d0741016410003c254200580304024115041d001003c0b08842250118040d201e07032900c40d61610310500c03400180603000b501850a140c00d44962080c00a403000042d41d03041035404000c01c90303a48a50048035a00c3c507507212640790704d10b000380c46001d50b030070b44502ca000780c0c0004804114545807a154095440b8031442c00c3d02d0320313102900c0141ca039802001c03108203059107410408000c01807a0101c2c14025102a2100707a840c01a00034400d2002108031071441c02040c5449100350154004410b01d0100b85840640c02c0300e01d6100c00d0100310b284490744a104065021004250704501c0e00e00c29 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 914824451 1250 914823201 914823209
    0x5090405040819170106050f0f0327031305060c0115080a050c030f030703081009050709050909030711130204120312060b04080a0b0901060b0d050105090a06080d050309030f071b 78
    0x1100075044c540440292003180144100000d00200041d00d03002c00e03990000315500089402c80080c0c50742010b0050f251364201c241380520b030002610b5020258503400200740c441e40e4003030518107034600303040c00b0501c045504860b401045030364880010500d003260040f03c520150002c40002c4c10306500c10f0a1051406200b81c00f8140281c12100720f058100303038040f040350396050301803c00b11072035101d0340618003080041c2d900200c0c1091401c000e004500e03500c04019000ca581c102d48a81302901c1d0b03810001d80b03034072468200a0210b8880c42c0105003034100324000032580c5803002c8005060599401008042d10200c0008800013000151142e082c01518411a00540300303000b800c41c24607041602c41a591038804201802c080550310000d45207400940010000d05103807041c1c1503da0301d10746e8984000c1e00c000e004540c03285400703000040442c070962281e4011545040b00812104609100985040c0c1c400b6200545601003042030b90b00320700a038001005443e1154050b2880e0401001d440d0402c2c00c030341d0700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 914825701 1250 914824451 914824457
    0x90603060906061707091802041b02070e0705072003010504081c060b0901030e0c1002031309020a0c08030c16200d08180a03050a0606081b0a060c0305090405040819 72
    0x351350740b1034a10010f15102070f03e4548500003001e4081403c018400f629800000754818101001490b0b0070104251140c0c4841d050340858082d2900c41d0f20f07120004400315540e4000440c28070550000c03880f8010127421600100c1e0007801d003814410301085c00e440c021038090712100400a6000e01c41642b00071050381c0d043c0322010404c4414104605001c00340f05d001c1e059410141c031102c00c80d10401052120900001c0001c01e0214542280c0c40c0c040e4481e0010740301d02c160790000e1400020044068000c96040c40120340e1030a031f12800b15078840009030000740c24520b004400b8041c42c2c0007040c4481c5808012030150002196010f0750382c00c2c41c10a54400f01d8032a001f1204a0505000542c1c0d84080ea000703260454a012012040d110200300c40481c2c60f40054030a00c102c2e1071031028082c40b58042010f9403111400d4503a04d154000d250091004405041d5400013402d00d0104201845010080d040d00d01c01d00d04940b400c46210000707025a81d0603102510086800600c522000805010151141d0000d017 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 914826951 1250 914825701 914825729
    0x150301121b0f06050c010b030f06090c040e07090e030d050702030423010806061813050f0609041502090d05030a2a05031603050705030a080402010206180616050409060306090606 78
    0x70003294000100c80c41843e0a125020a815822000030340111101e107102608441002c1c04003240e499075142c0c260f818880030300801c03691035120f0074603025002d90761703030703c40001e00c915441d01d10300c00002e0251105040450100348042c030250a041e02a4170301913070042d4015619036050900c0303d808040004800c001144038081c82c1c21490760401036103540010205c44060302e901411105252a00604607515880300840c0300d24903200509903c0240100081c501d84601d0707a56a009002c01c421040d01c01400b0b454100480e5901154260010a80ea400c043d1121007104210358a01c1d00e19000181210b011440305401205591200b001e400000140322240d902a5682c0e0340350b142e200e11460b0320384c0219005802c494020306000303030100c0e04229800340c11a40ea03548003100050510701b082e60228014052040820705106802145568030195070024016a486404824843c80e002c40c010105000e014080055074048903c00c49c00114015400880c0e4030f0482d14000c0e08662040e004054400d0f200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 914828201 1250 914826951 914826959
    0xf030c0318022e121d331e09010204140d050a0f0f0605090a230703020306070906110f0a171c0c031a011d150301121b 52
    0x1d2014411481e80503204030141040c031660464800540b100c4800c3c0b60340c05260744841c581d82c0600c815040328043c2e4010446071450803040700403000403680c1c980c0781c0c1e0300044504180c0522030f180c2e80c001406140300300218444100b25060140c104440c41c000166400210341d283c8443d000140780c0c890784403c000c500d031a0402121034100f42c010035030140202854180141001010003188080c0c6402c03c840409410780c601d4400c1e1a1000d8002c02c5441d9400c080102d50030b071000082d01d10b010740c0d04c05c4100c0c2d22606000307180c81000c0c500c11005a01e41c070400c0b90010150700c0600c400ba000346031380d40d1030800e21030038a1400f620781489514160701b10352094a61100782600401d581003a1a4000704070880820925081c01440c012400070011006240e5448000181c0b907620003100804a41c805124070b00d001059001482400841c0d40d020036107000170a98100205000e005403140002c008000055901103000c20701e800982210318400c40c403000c00c2c1c05101c1100449070394840440d042d41070090034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 914829451 1250 914828201 914828231
    0x3060915090c071401050103080901120b060306060c0c090712060506030103020a0e0613020c06010509181518060a060602070b280c150b0109120c030f0c050a060f030c03 74
    0x8000c044034001c55010800e101000a450131103081d40c2881c400038052540c483c18004290f610403805240030940184180302012803600602c40000001440f403070a581e514414030030507910441018040340204c080060127540c03407002d42400380b0005d079280b10000300381022032030887e646c1da00010700c540700c14401000144c1c0d071503042074280c0d81c002d0503101c17203038644d0004225503102c030020340d101c82030010841501109000075003034100da00842e15180b031a2218000c2e02526482c0125000c0c42d80c0101c00507443d80301c0c00316003141d042114a85020914060088820700b81070042d10f00ca080180c880400308991941048010042d10320342d000a490010301c40030101071000c4503800810b050101da2600030b022405070110b03e00050300448002211088031400300c0c01005007841c05070220f04202c101060b80394502c110f83e20060b510000f1030740001d045460b000c4403102407000444032000e1044010030ba51722443c407920700034010703070300e03207428041001c00301074280d034205022042014a0200481c0c28208 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 914830701 1250 914829451 914829469
    0x1d2e031a040c090b040b03040b0f1e1f08010203090c0603060d260a050c0105010801060609031b08010c0804110303070f0f15050c07020a0905070f05161703060915 71
    0x12500000c0c0e004555800f9548044258030804413264003140c0040e5521042c070045100300c2c03144000007402c0e41d43d40c2100c0081c500c25294407001811509a401e0b070066159900713134000303030144000e403485c1e030410b007210b080e100b0036401801d01c90750080180203035a10100030381c030703500c502c01c0b0b490904500d814070100700b03221031440d00640500f00840c0c3d110388211400300540d01404142010b80c1d6509211500504913501507507a0300070540c40c0070000584c10310306100d41815201203542d2001e40c0761841c0c998410300252440c540144400440700040c0c80c0e82c01f44103c0c9420320b1f2a03121100d040c985800d024802841602c0c00c079009410402c03161b000140259106010b80764410b0160005241504041c00d24200071601d88900f03501d00b0061001154a80025044051007280c884a0950f111107259044e10300603508400460820101240818068009006151039415180503050210784030041d090411130002c1000ca40000240100c904010400c254054110704450305954100008a1070b400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 914831951 1250 914830701 914830751
    0x60108040f06060e13050d09030309060e01030209040e0c10050304111002010b0405010609170714150d0615032307080711060c09010f090e071d2e03 65
    0x81c03540a203104002040d444403000e4107034150002214641441e01c103d2190503100103488511409910101d250b2284c2031034800e40b94181c0c0d0f08901185010707000e0301c4100b240590303d03051580a0040703031075030b07107640c800c111a00c04070300c000300f00741c2d480071050200d149c80448521003001020403c21002c0742042c4140c2d42100d10541d0950201c000e2100c00300d00404080451550090810000040700303580328880780142c60030360f40d032601040044a6000e58030300c500d1003440381103503801c40c00100510703148228220940701d100c0300e103107024290100b41c400ca80740d80e000b0200d0003c80700082d00c030790f6605100315108414062080641050200c02c03120321200d0040000081001080000e0a43c0f485403100d00c02d030500c100304032896070400c1951030140303412084002d0300051027100302d0405944110b180c0781c100c1d40484602c607481e444d840c0c01151004100b00056040c180b0f1001c0d0244503440303c4031504800c0b08040602c6020003502070300011081c800c90820020581419801c0303280792421b502d00f0141e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 914833201 1250 914831951 914831963
    0x6060b0a02121c092301180209070e0a450f1d100c030b010807110109080a022401050604090f0902060c241e09070b03090109021806010804 61
    0x32200c4100d03d603259070306040d074440240e06201c500340c1000030140d017031050000441c0280c80d80210004545088940016441d04241789021158000d0704001005941003211380c6404150045408082815426641e000000350301441405002c1051104a070307120500e40c02c5e8102c0111464948240645040c2c480d0b004c4035a6980c60030551903c500e03031301c1910724002103040d940c070b030070605125140c642002402c00035005090120960015100b0722401880490584400c0025180c0e103404440004d600c5074181075a40da00e941c0c1501280341d0002074403070b00c0c4155008205c1480c5640840406411180321500c1003236009006000564446060350192071608500090004038400c502002c0e0581e0000070390840300010b0308400400000c00c00c4000000201403070f10f00320f10020755400d500390003100c20308e800d03d4450011003000300c1d40003500f42c1c201e000c0100b03c40016450305800c00986d40103681da0801a035642d4220030450400c06011070b251071564225604030f160003070001e02000c000070801410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 914834451 1250 914833201 914833207
    0xb030a0b15030703150b090105062803020f270a03051221151801060207060f0201021218010e0c032d030301140a080a050a0b2d010306060b0a0212 64
    0x940d102040124000c40c0c0081160824801c5c41e4007540041c59040181d6024049400c00030410313041902c01c035900506d00c1c40104e6a480007288011815454071a842010584c007004454002e1104501802c00c10f003200a041040d6001c0110100307507404418581800354110203402c1020910205000b45e07500b0000b90084d90300c85001c000c2c3c010b10850003a0703406a00060710b00b40008600d05000c041d107600c0050383c0841d002110080e503118103e20034403410300168080c140034040c283c070500c0c4888002c0174030f0002506041d02d42c52144d030002d004540e080c83d600c0000d1174200208009000300ca00d2035605802801c105440d00340401d4071110b6200358030301c01c040c000003503901030100402ca41410b404108240c0e07031a96101d1104d1204100000c030f00c14030500100b48045603222020a40d661517650000043c81d00d1021a13498400074031004009011006240305c01e40600c1c1d00c200d8031140501811031580a00d076045240410485072113820185c00e0038010b1001c126010380000e03101504030481d52005031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 914835701 1250 914834451 914834491
    0xa03150f0506121b060c060108010501081218040b0f1309021e0f09061809031e1603200307050f01060e0c0301060513120302390f06040305061008010b030a0b 69
    0xa0280703d1401b903818240f141c00c000096a10066000e64140c880701c07001c0c1c0b00155600290358400c0c0c00348035640d4aa007049440518414a4550b011610f200340c041c0840e00c10511030303400660b40501c1101c21000380e6494500c040214a007215440c00e40b91140c525550701c1c14245408500164007004403030740030b03041c02004140181d07510000d1120a4800c000d281d841c2d40381007030301c00c1d4407600081e6803c00302e4007004071445040386002059942101d041c1181c8000300e603558800f11100c0380c03000c45001203a100611800010b43c0240f0040060300d0191000340207042041c0400c80c21500700364011241540c0d05070034032038031200c4481200e046480368030301141c0310a20848064000d080a6100805c02d1040941450030140c0110712403602000708001094202081405461681c5160120403602c0d014400c109000749013180040c030401d81c025080c0c60502e81c895030341514248007038034a003803d10000d0108002c0c14400340524131004800f9805810a003507180e036104d21021014000c2c6070542d01e030f5143c0350 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 914836951 1250 914835701 914835709
    0xf05030c0d05060d0606032307180f0917042903070804030e180403081006020304120512040608040b01080f030d0b04090219090c1409040b0a03150f0506121b 69
    0xa4013203034100b030b03040046070703074918024480c2124451016103a40f5107520080d1803d42c00b0032400c0468001c140320040210031001c000b8000c060b054403074400641d40c1c0248002003255070380701140460401000300d6a45d81454040040d400205040003901c44d504082d61108408003020799421a2b680d0401d41c90540b614901950180b20f2059002d80000c03922170700c1d6024100d1404c0c0c0c1030290740243c466030110740b10382c404844001d80038080c0700d000d41c2c001c1104000e2588880c1040c0303083c90259090b5495200c8104204150341d119502010004505809200a20541c82c03c001d006001d501d0042254111022002d0744030b004d40030550702c42a40c0d80d82d2001c2140c807150482110f081c0d0041611140c10358004074100d04146074091145030030329152010b00514003c0c40c040101020034881e460030300403000708104c094001030031110b4004214420020015180b224142e00780c0608000118459070071744054001c84070020091441408802c10300b420911003c506408103041c14030348124400681400302d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 914838201 1250 914836951 914836969
    0x150909080c100902040506040b151317060714160602250f2009160905191d0601080414010b0d050c120c01050f160c06050306010f05030c0d0506 63
    0x2580740d5018403900c010490041d580825a090b01c21181000281c94074070920040315140210140c029001c01005090500b403480074092244030340280101032a114907503e00d07031101304940007005511950500004507044000d1088252804840c41d0821402d842c0c90408040d42000c0a082280d000031030100000c115500b45050412030b050712a03103d181450001c01d031031a921015078244030301c200c1c82a02c1c841c00300c0044982c0c64001b4014000c0740c64186a04d101c040c0071443d444248440201c000960b5110001070101b140c401140c142c8070f444c90070f540116614101070f04084042484410400070381e82007042550000d0304100305080d02000080e00e0390040000441c075960000212090f64200200024810004102039554515a0100044550f919a207603080603010078420300c0240364030b03c0c10710040c0c1980840840090015880d940b6801e4450407141c0000c0d000810000801c001540c2000055056600601d000d40c518a4050f140101500507405000590350315000850150395941d900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 914839451 1250 914838201 914838217
    0x1090506040311090f071409040213031202071a07060b0a082d0102041d25030207030318030e12030f04080a0b0f07050909060d06090b07020c0415090908 67
    0x5010755a81d1070341002c1c00111006400c0c0d620030060203000512a80142050034000d890584420b19065070020b902d00c0c46400080c045078009a0074051300e0404c401c0701901000650140c10f8550200650b42c800a092030700d55000f4840703100406107402ca51b5501a41211202d0b5041040010000d05d210005031340452a60700030007480c451428072040c1030042ea01c040103101d00c00e4031900840104a52614241d0207103120300c0d900712001e0b417505e003601340603a807805a20200039660b01c0d20802000c10041c41c6900030801e5100002d50104e5410105034042c403c40500c514104144286188641e500131b10b8080050139240c0a180b000c241807944000070000e032110060000000381d15203480c0d202d401d507103a5944030b003038400494a0001c160300901483e541401612580c0d5441d18095010007880140c0c03030090011a04803aa6243c074a02140b114800c2c504140c3c07143c8500c03400c1e4100988005c4c500020441c0e1548a00d2428030700404261601885400300c90400ca8045543c03d40ea090000032030042240d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 914840701 1250 914839451 914839459
    0x120705100c020319031406041820010e0906150d02091e0a0f1805072a020a050a06050d1104180c181211030c1e090a02071a06010905 58
    0x10344a40e01500840507104d841c0c07004000c601c0c0e100b0900412410359031000450b00d42e142012011a98504094200c5284800d50764410f032104000e5a0300e10f00e0f40d0058086554401c0b04920841c112581d0002c04000000c20072105115241004000196803082890030118400c40000c0d61000420300d03030f019100c0002000301010076030103100c14080748101c91034107842d208548119001c1281010302c80840151408a010b0004401075205a10b004140c00390203c000d1082e865540c1d10070b6a0030b240f0307010800140d000d14041441e07031032050000e6509240c100600c205548481031024030b070311600b40c03944607115850100743d44c00c85883c1c81c1d2aa100e03541100c111000d00b070101c0b419a00c015007000503041c440355140c4c1040700045408051196040c02078641c440c40c00c40905012402c20496440301c0800207054401d0074000703a000a03003c2d405035000d41c0b006100c01d44946102d15110031080c2d48502000b10540c68008266100000704660030b0381010038911800200300c040e4411b00e03071280035000142c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 914841951 1250 914840701 914840711
    0x61c08070615180207210e040506040b130f2406080903040303120209030106180b1f02071505070f080325050f0901140414120f12070510 60
    0x10810504903031004006480a60520016034000600041000100c403540480302c0c5820051080040203541700c131000307965805015580424101c14402c1c14091850300d900c03444041c01d025018032080e5503000340124803981c0381a25032143d82d00c400352500000c581c240d00005041908401c800010f00035500d0404c0428134580784544ca03c00100f0982c0259211504c841d100d03560340404a540c0c2c0d1107540001000240d054003400300340c542940180034400002030000c2203403031304d031026001c3c1c01d289125001c01e0540c0318087e030921410415450207050107100340b190006200c005000e0341c0c0e0700480c8a50007100d81c000020b0208103100d102540c1d16903501c880000a1012941420701840d0016181b811030304a000c07400504e9a140c102c40305051580f140c6541c3d0521100300c0c0b0a511a0704482103032818410628140c3d856000414002c0001d00900744c00c030400e907038000c01800803407001c4048645150380000b40c42c1c0040f075000501c4145000750096019502d05551418900303150510940d140c0081c208 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 914843201 1250 914841951 914841953
    0x81f0305120c06010f0b04060807020c040507021b010203160b07110f010c0318051005102606011703040b0904020906070c051f12050403210606180303080f061c 70
    0x151009004001c0d84000b1101166220040e80001d04190720a01b0040c0e0070030081002001e004101d030650100c19801a40c81c6084004041010f0340c80890390350b40160844807200c846011031240003a003018080c4020b40c01c00c150060420a0003010480103400805148006070941d4032683c0c041252000d40c000b920010751203040b519003e00325400c1e00700301190415a0102d070f01064072794807110860300300008120700490030702440b006103c05440d07509071b450001c4012450400c141c503c0000c881125184071030f04030301c003000076041c128182c1000403440c514450302c405010000040e034080d10810040c2942d200314540000d170082c8915440c10750400c038040380300800d0240705480c450803200161810104c16000c1c10495507082100b0b80d01c400820425501c100d0b00f01090362160764428401c2c00e088210344860300300c84143d82044480c04d00c00d80d859040c140500d80d0b000c24841669800500c7c2c3c55003440c11a81e003e030110000070038071501f4854500001740c00395074208184004034005403803400d03a070b085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 914844451 1250 914843201 914843233
    0x70504051b0711120d080f0106050a0813050f0703032313150302120a021305011e14040e0103080c10090b0402010c0606030b13140a1214040b120108010b0405040201081f0305 76
    0x8220383e0081587e07001b6000040c032078003030011608074a8103036854880581c0c80042500602403504000d550038070070180f003110030b58020030000c8042c60294981803841741c0c0c4100848000c00609107842c0d0018000e102043e00c0102c040324807400d880380104d10b0030310140c605c0012002802020b540039a10441d01090044a54580e801809504080004240340c51748072001550f140c5003050b280340e2000409007a0038100c0b842028003800e1810100815881c2640e40c000c020406002030700f00791100c04001441c1d0034141d5003000072001590360b004003884042b0180c1c5034031200040081019040c403038a45856010030045070700120146a002940c490607041000d0780480b28100c1c0441140d40340038204540e005501d0001d01010103540c41880344e031000010200c00c60381a000b03001c951066000911000c40c403c9040c1d400b404074000300250f01c1c900b5600d4841001c1c20b58a80303400c0c89024900d40010302000d44d0f4042c40d030303d90100548442c107401c00412440c4001c44445a4006403082c080c066400c801d860b9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 914845701 1250 914844451 914844467
    0x1819050f030711030f06072708012301061701170f100203011806050f0d0206120103201f05030712050103050c010e09090304121109040302070504051b0711120d 70
    0xc0c0c254110b0384801803011710a56101c40c01e80310780010541c15021107031395201c14520300f0344005002107040e414503a1014120300707540d2426003941c09946a5104420680c401408c0c0d1030042620f0324240648050380341e41448000010300441040080425841013003410405c803043c1100c05c038901b05c8200b5401c10a40d000290003e0040301c800113000100f1140c1c1300c0d80c41c01100140c8100601d07940d450038109003081034001c1003010407030f00321406101e100403102c1036001e11030013580a0000d01003a864140c01642a04115407500d030300c200480641c40f01000b100700c2d0b0743c0404800608100e41d403500c4180003a1003d00c41241c1d21380c151410400040100680410003004643d8280c8030441d00840f040d01b0401e50250864644110307034002c0c00b00b08001d034041046000c006005580c2d108041c014072004c0380c4074081c101e50950250340071042c20881c0342003c0c1304a42c0e015441c08048044044003d50401c1c9610400801400207080851410700d90780e074001034607411070040011189a2800150b014000e1381f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 914846951 1250 914845701 914845733
    0x11150912041d060a03020d0c0501032d0504080d0606020f0f0d020604080a0c0804080c01020c04050610050319060f0311010201020306132307020f061819050f0307 71
    0x10051815034518480d80405403020b44020082040040c0924035103034562080040c181680459410b100001580710190b6400301e60f40107003035048003282068009000da6001300c4055840700b0191402d0902c0f89220407440142208168021841d40c03141e003800b003000e0003501c6c1d050301c40c18901030700000d04580024465100e2400c2c0d105442e98011400e12040e240c1080c100544056003000002034001a815401849030888905103075400a00b40d840720a815000750f0441c225940c0007082c4070340b1540e0100f110080c01a01164244203920b8002c0101d80d00040c040b46540911a010010615955101c1c0000c041c5941d103d0040290584d1908141c0441c125407005440d40c0040f6034190616502c18000c40780320f40006040314580c0c209035101c444c000c100486a4600c503100a171540040210507040b401d018418590003401c00c0950020785504000c00545600320320b40d400e204150121501141d00408a035140c003440e180d08100342000781c00e0113840310300284c4d14080010b29001f00310402d58140420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 914848201 1250 914846951 914846953
    0x1060b030c22080601060f0203070615081504120509040b180f0c07031409010c0b0702010b12010b0a0506030910060f0306050705090306060418060207060204031a01030b040303020703111509 83
    0x2e46162030010341c0407018015500b6503007100d00103001e500d00030f2089004c00313a003501c100e038030b003000d00d88541d003c0350112085481e98200e10b0100308110b500070409440d6046010512984500f4190741c0c2078060200041e0740703810700801280c045103580d01d643c0a6060450b0203007116049001020b09030080344012100710450120300030100c0c42242081041c0c3c1d00c0168542c640c0c90400d10740b8203108441c0c0e00031000e0581040144207514000411090303085002c0c918540005c03440c03c3c0820104011245040020221a0b140c00c4900351039070f86402c00c500849100703907a000e42c0e940300ca80c00282400c010700520751b0a80d060070030008084142140d01d40880307010b50010030050710303100000c40e810f120300c2282d03551503032054000c1030a502e499031094459203181444454084000e17130b2104142e03005000d00340c83c0c066010508100348514010b002d0701001482407264015070440d554100704050151016003015808100348080601945401c100689018100d9841d2100101810703843e2104541d00145 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 914849451 1250 914848201 914848237
    0x5090f090706052113060f0501090b040c0e0f0420030f1012381e01121b050604141915080a0f0204030804030b0f1e040501060b030c 58
    0x1091050040c0d0302c0c44e40030303d03c0780301c0d5060711404608000040900a8800d24000f84441c80001d2014868811203412a100104080d850060b030f0008032940340b90300c0da000d1800c1c140c2c101c03181648000a00001681204c0c96081d0365403020203d0000d01804100c2105409450081c4070300d600c1e444095031140310000201d540036560705604d49075100951050740e4070203d88000100020b5006202d4002c64141d10010402c0040e03c0049540844035020503803406280407400d1281240041241942010b44100a200c142d40340021040b0961a903a10142501828094210402c03103081c9002e4010080101038545440d2600e00480c803045410000900c522900084059804444200c0b4000c4880c0300c824030ba00501d04c0d08040d130341e4185c0100344d500502e950704c2c0e002000703407020310180c406580198070307554940b0b00b14035107041d00c1740000c2c140e00d06503580001000442066010000e044a950420741e41c02503e9900c3c20718054941d507004a00b004802104000341d04501101820b100b00c04e001e00c1072a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 914850701 1250 914849451 914849459
    0x2803050904140405211b0c062701090509151203030709030c0f0e01271104090b04090c05040902060702040c0c0b070503010e01030809190e0604110711012d08180303060109060807030605090f0907 85
    0x2cbc000b0440e1156070b4008000d03d0000300380c80d6119410025483e03014019200c1c00d48032044090655000321000740201d04020800d2050103011a4003201804c2e403070300c0d22450b040c04c00c1c54041a2910501c1095a40b441c00b00c0348201410070a0051a4aa9800c0100388400340d0049030b8840e845d000f42c05000e181619005440400d842d242c0035403001a42c00c10244807505007081c00b0300010740580c4d282a600218100b00c064016103031441542c42c80308903543c17107400b0300205203801221864080c0800041003401c0c0014004a01c0d41d4071b0050442e940301903c41e607110b8540020600c20350f055615403050040f1454002030b07818645030750724030900049804208030300034801146458000d07268003400c4041d826005000c00d50168103444002d45102140c980d4500f07594408404100ca049000c0c00014003850501000d0b86200c5d0301c034000741c41910046d505615043c80000e0a0640c24441c01c2c080010500100e44410300aa00c260003070304002d03040040515018080c0c286c000e0081c1c8144543d80b2030040006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 914851951 1250 914850701 914850707
    0xa11030a15021b0c010c0201050f040f0306090501110304031b03120c0305011a1e0d060b0307020a0209070908030d15091d0c032803050904140405211b0c062701 70
    0x101d1340141c141c4800151012640044695410044115803030386410407000c2940d50300f501c401d40041d841000007081c5030009240140c2514a01352804200c04030074404d01c40001c1d04110340c21891422181410100d01c0c44e414111091500d0b0000340703892619000c07605580701c0d03143d045a4142c0b03840340680d00e4450343c860400e000c4c034442c7e0000489a0318030329540543c180015001041000301403603000c9040f94648600e005250320946541d03000d46e01225005c0c04500b4011240c03a0f010040e4103001d0002441e044170242c40788500c000003184180c2d42d40109000782c4c198200714000e48880d880070808241c044403000c1c3c8400029034240118800d141d840161407500040050000c0e581000706000c01491541e081410140401d0880078031905000c1c000003078440d4407880c100c8030315500402c403440c10107041c96403c12461001e4440d895904a4040000c000d02c0000c483c208281800598407862241c0c4550f03051030703204400316901440c0011048084501c500d0200d9418010382d20403650005440015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 914853201 1250 914851951 914851963
    0x11d04051002071e232d07050a060503070e030706080105010503040303200a1206060903030c0f0203010c030f0506010207031e0f0f210315120501021b06071d030a11030a15021b 77
    0x1400c1c114000c00d0b08507460b416160741b124441102d000310781d801c503190000154000d2164000c0400900c021040242c8a903102032603154282d0190081c1040c1401e0030b20040c50a1014003501c1e041c0301e00000440c003014465806080c020102d1b02e424061400312a20343c0b4403562103503041c0340c0000c010301081e400504440c030920040f0740c0c03941c5a034101145140e40644020000c10710540b041e4038036810b0800980c80030b0203241c901270004d07038000070801c0042841204407070010f8860790455000000510016181b401082c04440d9240300020084010385800d0403103800c8044020010808505000100044400084400d01039503545001e4203911000450480b14251380e0015840da001008004105c0407605c48802d05014100142c604000842001a46e2030500d044c00201c1e88000308114405500500b000582840c540c03845040c0c40409001a0f03444554610181c00b001e440c46c0d040c40b00340c3d0304100a8098a81c80101c08501080795141d00b0300a40041450ac7d031521103e0320b41240000001c100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 914854451 1250 914853201 914853223
    0x1315021b030c09060a0305030c0607031a030c0418020a091a010c03080a1a10020a05060c0414040f0212070203040311010809031903020c0a0605011d04051002071e23 72
    0x18040d406030702e4200200d009000e000540c1002c010326020000c2102030004040d900300300030041c165800c1046c40107040b00c00080d41d040501100e004003154640d4040340c44601c44008a90105007490001c824505888a4100081d4450080b42c8002480301d581c0d045a0a0811290320101c040c01703c0d6401540c801491100c014009503000c4005810f011035035104d041600400209266030f01020300110321001212103c80d80581c2c4a106060100001000142e0307010040c3d40c1c2c401e00b05480c0c040005000933000f0303c03661246444141c1c01a1154196050b56a06070b81d0903c640700500b080781e4041d4690b8803600080d58400b00c07401030b003d9135500600665020b401c00c0700c010361800d041d0b130411801000725110080105030b0204410250781d6020410455501e01441d03000800354501501004000140c20b4161a60400c103010400880d00c042001c84501d1052040582d070340525160a6203400e45009031140500358452010082c448080e480050040d00744000f40004410881740b60303943c00d0302c5c9403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 914855701 1250 914854451 914854453
    0x6060203031605071a0906070212091210020a0804060f060b0d050714030106171f0302130f020712030e0f060a0b010e13020901021b03211315021b03 65
    0x4041440803042e00107030004018645880c40c20840d0566a00c0c440f005081903c00c0c0713000c080420b11000010034020150461500e00081a2072400781e00458000e01664555600c510103484000324005400c1c410703c0c000140445046540e501c071000c011340303004404c0c0c81c02c0e540c1070315040071507111400f5032081a040c0d500d042a19814236043da0441d4010700001058101003000c103484144242c201a400340d40604401e03220354051802c0402c0c0749403c958010134503090410000c800c10340c036600409980c01602c4d01a50304145118000c030030b8401074000500d40c100218030006000c0c0900c002d60103403100d5134889980500600800d51007841c0e03150400d41d0f10040355080781001c160341242d60340c0807078180281070500141e0f0442200020f00412040321801d03600c00d800150406103981c0c14444540303001a0482840201e00030280803941e592a4002d03c4240c4a100300c080000818001301604c14815000089d840115203c0c2046c0e5603076600c81c090300c000361040041041ea820116085465881c1d0094 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 914856951 1250 914855701 914855707
    0x40b0c070204020c100c23072d06060501080106020a0308061011060411040b15030403050d02270f1e0f060909010626071205040204110d060f05030106060203 69
    0x46445205039009240032a03006030300704080300102c103003030008102c03059070404005442e034540407010704200c400b003000c41f01401c200c10504105a0701181503500080d00140290011080d42e80c245c2003100b190040c880341112a590000100000380d000181a52001e98500d44140d0744c0704000c5c2d0391404840d0006000ca2140e0001030000c6c03d00d08064822145207103400d8001d0740464404900b4200c0035541641d210f007040c100d504440c2450b00032683d44190940700b807109510714949006d140c0c00090001800c00c1303000100c04c4070081168040d9010518200308109a11446200b110907428000d1300c1d1a001c0c0c1e10300d0206000310714020100744400010359155805c503a8000701001781c023100b00404285d04c843c1c2800450030700d886510745a0b0280a03140c9485626400301011030764805405000e03081c0111500c410042000e6014004104a08040302d01280586a92000502034001c2295a0000050102e001603003a00540c002a0880d03481166061800fa1684e0515098031018020440568020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 914858201 1250 914856951 914856961
    0x1061508070c030306091d0c0a0602060406021e03090109030e03030a02030403030c0c210302010f0b0f09040c0801050709090e01021615110d0207150c0212070f3206040b 74
    0x30b80780c8009207038800e02d00050754903196131510003159450410034a4000b002031080c0e52000c410812052205005c03103d40b0030840ca4241b0003903481b41c005000400305600420008894031070001d28001c1d080c2c03141031040d01c9103001911640207201032a41940000d076490012209810080221884503016a018502c0e0608540b001d541030741107242c0880c0c0041071030200180500304601103125130009050100840b12817814001d0079141561104d43c1c917103180c5800c458040d610302020b5040700d0019181c254556440342088401d4041c59889414954200020007005503401910001070310504c0108010744000445414209d00810303c1c80c1384204046922000456162813100c1c4081c0012900422203a00c0c0441d04075040c4c020000a080301a00402d4220420101c201941c021240c880003c2240126140740299a1024986032100300040020b802c800c0c4424400b4020300c15420401611040300354010000103503201c00540050241029a10340031007001085450080307800c00c0d5102942e842e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 914859451 1250 914858201 914858207
    0x40c05011d0618010210022803020712020717190b0c040819151a01050306041103090c0a0b03070e01050310033e03071a07050a0c05030106150807 64
    0x20700c4040c60788000c8251401680c560750a0000c2c051450045007004541c4888400649418070788514101081c2c0144500315101c42c00598000c0c495600343c008240880310302c0350680c02846404801383c10703e0303580c0b20050407080d0001131000c00c692043d030b44102182a091444c0e5152094407581501c03000380070b14100701080e42d401e503041c3c0050b40343c1e008171f15090303594580526010700900105c8010300304941d544140501e0035124480c40700c7c130042c00d012a00469107440751051424503c42c5c140400480400c2040e140c3e80e11004e5601000000a40c1c2ca04184003419a00c8526001e40361051800daa00455051a0f90302568015100c1e500c880c042240712100540d519040206007080c1d290301c80c540000441c100c050340714490b0b807018001229400c4188030940c0000c5844500707090301407001c08200074640f0000745000483e4017103801400d0514464011480910502c1402b800394810078050109005480c9050f00c1110000c07030081040d55904d01c143c00b02c600c11641d940c4007040034000098407846c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 914860701 1250 914859451 914859467
    0x3140105010e150c0c03240105010507080901210908071202030705070905041a0c1e040f1202060d050c030a0e06070c0201052a0c0307090e03070201110c0a03080d050f040c0501 77
    0xa40151070b01107060345c001c0ba26040c40200c6031030704032003002c1c0000540d2200503c03c1d40907110a2a1007031a1882c251651401c0b0700c504042207041054010401c002120003200d0084030700c030002c106114860850600c1c0c5160341042e403042e90613120b00f00105481d6030000044a1280e41c0c0507016100462400c1c081c2c00040400400603100002844c80b11041c41d40c4030f2007001e1054a5209980f0b03165040c60200e039803041809000c1c0e8000500030001404010360211a500441c5d0340c001010705082c509102240b154050701c02d074009203900f04820310501c2407198018500c580e100000800c401007110740790340d0f82d4200581d06507001c00c8880d001744c0050b51040009044c00315031040c0040c01844018500523940c4d501000000b100c1e0445169aa01450240680340c014510000107200109000710a1a100e119003000203050045144000803401c0062000d0013011100611040300c040e41d9040c1040141e0002d00032070000ea1134840010102c0c0d40311038655020f10b8001074820361041c180001918184 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 914861951 1250 914860701 914860717
    0x9050f0408030c09040504121107030201020304090c12021201081009080d05070e13200301030c06032004091a3708060903070b01060512070c0309080d03140105010e15 73
    0x4010007a00d141c45c0c5035401150302440c410400c009044025000080c4402d03001c0e80c400d4040e0700410010130250381c0c004180d40554030030400000d1041c003401400e4070f0420802c0c0d0801c2209001040809803400700d5890f8604035686007055031140420000240e0803143d0564004141c16010300121800000c10f41c810b80d80f09104c3e00b001c501d01c2030351b080001d26440100e10705400c1d80f520703032594008200740e0000d195a80c02a521160307086505540d41d2940c506203d008002c1010307a9019801008800b80f4070362094625800143c40e41caa40b1410240003405190b0035012000c08040800c8000d42840000800c03003076a20303d003801110000911482d02051002c4000c108030b511180003280c642c000348100c074083c04820300115919203c600d0090b5030b40790144d000005002d4103201c1d001d09840440c9580e0f600c0120b40c5450700c0841c035103140699981c081034114008070308c200da01036514035415a104d216a21104d5002c40890703a80c0b0300044601c090304000468000b03940c00348020200d0340001c0501070321 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 914863201 1250 914861951 914861971
    0xc030a170f040302040e0a2303041403070b0d06150504050907032f18010f1704020d06110c01200403060911121e010507090501050a0e04051f09050f040803 68
    0x43d40e6500010181c2c0c00550a400154004000342d2040000d090500050100b4603036510010407035034520349850b806a403281c4c3d501e00c1c1100c005401039903000d005001c0a000700030b42203900d9442c29a20100242014025544c02d40000c4a0a020950080e02a1411144003c1c80c240c82035031050000c03400761881c4c05404280010910040c2d05164680340000750754031a28164903200d0103001500400c0311a04840c96042c03240c5178404001960340302c07541180040b020b10740b40c1000e884510100d00d40d45000400a00711610701189010203690140040c1040810403000b4010702d4020110094809000380141c20741c05030800040001903590740120b44020b000d6012240d68407a00c10205904455a186012072034001a0800c2c0c9904000f00345001090001c00080226240295000d400311500380140c170305000002c601e602c0000e100d40741c4004030703540251040c003581c203001500d002e10041480c2c0d142510000907a0128890304588203241c03162050382c420f20403a8840340c54000306580050b080c081e04d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 914864451 1250 914863201 914863207
    0x5090d140a02100302070c09050f160e06030f06011112180301021201060801030209010e070f050306062205281502190b0a05060306061005160c03050106080c030a170f 73
    0x1598a8140941c90120f02c3c0d01c025030313108010b01d444400c0b640590002c00350f640c5400300740300b190350201207081e0303010041c002001030343c405440040e910031403800810359104c0d03400020005420910801c007409840b0a8803410011244607180903251650050700c6051920140030408000c80c011400049102c00030b0300041c07401c4c81903c068100c5103801d03041007004c104000010411410449051070040296802514503800c0c03000d4010a040b0341d02002c0d1081007808008160740381e4840d0120745070101519085610940b1006100901900d40d214951084010310384c2c08602115580e81f04406c1c4200400c043c41d50b074203280e00b1201001c0c610402d2411441840117145072a181d81c0c0300c1542c3c507406004010007900c2e002c1410420390300002c2c891802038000500f8007440d07445121140030401094240b0740e44071143d030985a0306580e148800944110030b000000810700a042d800745090b128281c1c20b481510080a040c140c0d216203092000f05103610424401c103103c1c1d0355070090205200c4041281b45 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 914865701 1250 914864451 914864453
    0x4081c021b030a270e1608011e0902030601050c15090f070f0e040c0e0c0903070603020405030c0904081e090a050108070813080909160206011a07021c080c03120705090d140a 76
    0x101d20b07008480c8440c40446041c11045032035007000e0112300400a250396944d03d0944810541a14259440f94550380d030740110100f031943e8042c006a45000d9403000032100e01900041c850700d510003054544203400c2c000c60071944440034003c211082500c01080160505600e001c40042c04100c004000341c40c00c20060b00f0119036464042502c0e8010201d414085403900c219004060820945030700440031f041c410031040007103850210784801a00000c480706001c036540ea0428820351320a180912440701810400d9201348803c4c0c1c405042c00c0c0d441914182c0d6040d1f100c00040d40c010300c0545441c00400c1c80303000018a5481d1030b01c00940d07030303d100da1b1001d403c22503018007080c2a041c007680e441152081604821011660400881d401801e04100380c880c2d00c83c120302042654440c6e124042d00488008802d505002040202c100c031a0ba03214065a40d1100024102512034005c40038418861000402066800344a40195903414170300820000300c1d030219940d0529201c0c0c4000344110a4021034175054 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 914866951 1250 914865701 914865719
    0x21203090409051e060f061905040c03020a030b06030105030304030803040f1208010519050f04020d02070c03060b030609240402120607180608040804090504081c021b030a27 76
    0x2c2c0e01c0a200e68010049481c0040085907902c1503035024070580c3e4010020000d00703401e907804440d08810151015038811810207100d65a85100342c11107a00241000001e0202c144d069000b08050061581c00308041003440c41000610b100c00e20440e5417690003440b003800894404002580c000d03205607400c0c1401c62103a13440141c510b0704103074944040b820140041009042c111a402c0101541c07501d0141031394202400240030340f0102d8041030080b98049a0171034403140c590704a45400e90040640043c80c3e81c0c038030785400901140e10361580280500f001041e0000000509032062001d90b0404800c03041c03424030101c1084d82e0040c810b036489800302c1c1c094014640c00b440300b64041d40711560b800e680f03101e005000b00d6108585a000e1001c1050b80010040450310750410b032810742d0103800e000b003030549507810b2035032150103805104581c40902404034a00180d850340102115145049904a0341c180b81075040c0e120700641c0a2407011840782c0a00360001c204004101405c61007000c180c07a44103458260368 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 914868201 1250 914866951 914866961
    0x30a060510080a0f02040f0b030706050f041a0706230705030606120405011a0d08071203020c060c090405010b030c1b030f0c06150307120b07030b1305240d0212030904 73
    0x1e403803d604a064130300650030140908100354001e04d0741840382540000100395505403e05c1444200301000c43c0e441c0c8850502d0044038010b124141000074194210010b92920390710010049a0040c6007403a0800281f203840e05508038190412841134142d581c01d001900e590740300030071460740a0810460500e0f48104044c076240a240208000600d8211412003156007082050040744a000b540011358000395051044a04803580425030708a201010507003078010f03028288500d0080e0080104000300f40445102401d4010000c48003400315076603e40700700742940320582d1080c028860402c0b51b8101c000b2018000440e0007440c030200c914001062141d1141c42d00041e411110680060303060211480503410940e150300380403000b13000c00d2440c00c03011504480000d200100259070010000d01e19038080d500122030907002800c00d0103001e0445109500900048a080301d06281c825004440c10001c8031200d02c82d2140680742c1000b031640d940070007000c0c0c0c01da1406c5000b1031104022007503041d100d50282c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 914869451 1250 914868201 914868203
    0x91e05010602100e010b0a0302010e0f0a0e040506100f050d03090e0106030914010203220f0804060c1a0105010e012f03070201080a050606042304050c0d0b0d02030a060510080a 77
    0x3d0028441c1060000b41a034a6014501e60660304103544030b9041e642c1d00482d08208c0ba8242400c2076000f20100c04074581d100344c039121b15404149004009070940840807818031951140c0c096076040d03a10700702031420490b014041c070201311036010018440c0d0300b030101000042d107020741003240c00710b0b503540c40068011000760441000691105901c400b00b0240b0854801c81e1441c5000030343c2140b030607280c070403441c81214004c00d41c2c500d10340e0100001d01502a00c841d0000e40c10a8543d580c2d5500c0e200b0241001172580400c9942d54001e600031810701d400c11808074161801692000320034031801c2c0044485016110391500c0c15080c1000754500704c8036401d07404000c11105005507490744980d0001504201c80108009189810103080144a61710b000440d02560090138801003019400140c19141040d481903068200b40341c0001d016075902c0c0903000d03080140c1c000405000025400051040c4011030b450000c1d0142d014806203000541b09070000c80d4001c0b421000710494580e18070401d0b240c000c1885c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 914870701 1250 914869451 914869453
    0xc02010e01031415012a0813090903020a020f0301050f0f0903090a0312140a090e0a06030b48030c07050307030c0302060105041416110a0308270601091e05010602 71
    0x42d03422107940c0003241c0c1c01c41c00d01c241020301b17107904d1054050360180e4080315000b000c160000400320f00e10314a41c00c0f520090030004004128403c07040c9406507880300d02010992041060304040d8031585014003070369104101410008125803140200c55a006102400181d0540001d10004141d6101c495016004501800540d0600c484584024103001c07080c4013601c00012040001d00103454101801004603021001e20302c11aa507103c20310b0f002000030b038100800c01c0d500c10342484000005045008144415170a107400c1c00203e0044200600000c0100591126551640c2c55400d0a90001860b0301c00001c2c089540f6014440d40c85505551160900300d0102c0c0710a07000c4814141d0400000d4003402007910200714003840e110380040c0d803c2006001c44981c411a81c01200c44520840450b0782443c1454100c45404d01d640c5000346c100c2c003048442c510a02204400f8291082c89852010000245100900004e9081010400141c5001c1c002107408042001034100e040c1c6032441054000d0003558 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 914871951 1250 914870701 914870731
    0x70905010f260c03010c210c0f0c02030102040504050705090a0e240a05060310091b050711010c02190e1b040e04080f030705190e06090d0212030d05011509060c02010e010314 76
    0x39008000a00740300300800c10f149440040021990002700c03c09180c00306003854801040c841c400640a80b180d50403e641050400c424800f0464001010704203501c0103c80d803d101c43c3e2035550904400c10100c9002c0319000a940c05440090450704004000b0360002d440034100c1c944400200b20a42e1050760320707140745031685204000c880c8151150842411035440303000c440b6800d541d0010b03e54000c1c040c5c0648102d07007155812000f68083c3d280403003e568054070441e07410071502e40343e407030401c0240710b140007510061000891581480484001c008403001c803907402d1074200418803111020040045031204000c10450640070728640c0507510581d10343d41d4559a41d4104000100c480c6421801001400201d140d402060399406042c1c4000101c161103002c1c42020500010f00d00008040060800c1e000c0080c031424104138030782206040e82c0e09224480c90010181d10125000310721403117004000f0f203000142c4801984601116032860b0414500425100c5460382c15060440c4291600340c2180958 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 914873201 1250 914871951 914871977
    0x109020d09050f1f0915051e18011104030b0408032a0910020a0302151506270a0e0703180b0f18150a0c02070f08070905010f260c03010c 60
    0x71a041319800035000740900504041d5030b60102d4038143e208a2800e4280c694001074010001d105018240381c0005d903a14109040c09011340c19002d40f034039148400d80d400c02c0352441141680004030740440c0d502c0380149011f548d603602d90041d103030070140190700780c600098281109250004006082810034403034555842250800b00b0403071100390f00341c842c1550070160007480070a13000320f0803221107401c40c0860b901a0361040503011580a0110340c455200340080360500340b4510b03204846100d01030011880004860f05410802c0d401014031600400b03000404c006a8198481d4010441f0280880300e1101a05040c0ea148441c640d0212280000301c5988010408082c0c80300703140041c00100301d030141282c01420800383d518902c0003840803019540b90740b00454158420000080100b082d454012001c58450751880c0c0c44012a01c5100d41c102d0400b400030503d0424007248104883c0084010f480420f01d0410141050a4001a8100c1e0b40680341c16401c02e0344081c041d03240002140c3c0e5031181e8107402 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 914874451 1250 914873201 914873233
    0x307060906110a091e0806040204050a0e070308130b0418090303020708071b35160303080a050c0a0807180e15040509030a08270d050316170109020d09050f 68
    0x121120412003175001904000f03090010440d1a0480e4050380c0110311580c4401c80100a0049250f10400500c9003060000621551074082c0440c40b80300d03968008419a1450b40060500660242125004070915000c54940031a440629014030a040240c1000342d180ca400703d007078012b10001d4513421000281a003080e59001080005850043d032144603441c95800c090200c001c1e079500c1c4114052112800300f6942c00e082102000c841544010b044c0e620f41ca9140041001c0420355991384c2050418010038503100b60342c2e00b0307143c0050140da6141519582c11034101c4041c404403ea01c050070f80d0110000c24a45405000544146e01a085c2428201c5d001000c2c402201d1004000c0c006a80091060510559002e001a078215800000c46d61a030128500901034002600303800756414401ea411603422141c010008e1072280361300300040410f60107149400e69214421031804181498400d0051041856681c040c007900d19400000044880c3d141d60307060324080c203101d0f40c02ca2031750203803528507d0805 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 914875701 1250 914874451 914874479
    0x2405040b030106060813170c0f0d020d0c060c050c0d02060105030c010804050a0327060201090308010605030f0a24121106191d041b020d110307060906110a09 69
    0x200c1030300200410383ca0030780001c00170034015160301310800f00440c1480c1808081c02d074a07100c101034a0061503680080b400c1251344c031072440232010180d008100240b00303041c0c004102054440980d4840b840300c20815520320000b00a060b241c881400002e110014070840e04110140c42c04900350010080c5506201c100341c82d051402607124100b101540811000030404148004031641c9420304000e2002c89055407491810700849184442401c400300040035a41500700380a08c901a48941040c1c0c0d803949400c036191f11045907001e074110070141c085400031700301e5030005905011055440003d8031020600984c1407150f6400704040d80c2d0844000ea06204000c8030a1040c3c0c44101ca08502c0c1040603915036440c000110611010701c08400d03100300180407020ba4910020400500c200070001003240e80d03840305c0110644100040c0b0410b11120005170040c21400c08541400c0000d40c10403000ea654103014100700035044034070507101d0b00034884110010703003d4900b1042c2a00c500d206113040041100c880c070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 914876951 1250 914875701 914875721
    0x3073510120305040315091407050f0409120c1403070c0509090106050109060c0f06051905060415051512010f03050c0402120a180c1d012306030406240504 68
    0x10000d84501c000a40010032642126440744010403280e03c0c610701e00000300000e10020b80b4003500c0b84c004403001800420760300280d940c110381d0303d8510030b0028180700880e40070950017040002c1c0e1b409508111030181000c8070700d46104441080904444665140c11500051012114400c09100a010a29040c24104c4d130000074271008000403482d02c00000e2004902d8801c12045c080c060b4030030307010300851004100d41250000f8051145082802c4107542d4406540444454649490049840c61816004044190300f0203000700b68110708001c200100d090141c905940c1c032100401013240704083c1c40d01400c1c000d024800007440064030314144141803240c003241d042c0c40b451041103400c015494200c0c2240d0040d041040020700001c6012828480301000131024150b0b0035501e20014030326800d13003400301c407101541407241e00366680c03884d66440c400d424030581c40c40c0c68418803410180c4c1c18a000a154411701400c00840c4402203d81280e80d11650982c5504210707514503001e00690825000e068584 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 914878201 1250 914876951 914876969
    0x100519050619030e300d06030c03061505030601171e070f0b0703050f2b05010609170d030c091a2703100e031e090f031203073510 57
    0x741c0713000030059111850507500651171400604441036008120015031310140910881084420386a040c484036000840c88111044cd040c8241c689528056464050803500c02400400d016420080c010340d600345001c400c48113910818a904449203022030304500513002d070070068008281890300d07102e00e1003150740045488003c10400200042c2c0e012044504150038808002e40320464001520030074040e0503942e0029000090040d044001c00b58001c038102c54050301c0710f14203241d94000c040051601000b104055821441789603041b14001d811402c1c201d0039074a0f01070941d40c2c8890100d00600c640c00340800f1548000f03d80142c105400107550444141c904400b8034540c41c88400080c0d4900d0380500b01c44016480e044a1804401d0820540358940040c502000ca500c0b50080d1425103038101c1c42d201d82c4140e10241d030f007a00721304004c120308014000100d01c8038070b9030740c5103102500c1c2e01071101e5500d400425080f09002200030703e600044080d48001c55610400e0030000c00d080d840b0101d0390840441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 914879451 1250 914878201 914878213
    0x603042003030313030f0c02131b020109030c17190804030e0906030a02102609120c0d050313200f0a05010c0605180f100e06100519050619030e 63
    0x110303804e0161160fa0750b1600c0c000101e0b03080395900715490700d1006002900016000504519180c071074020ba0112070050701e03642190101110100d00340e40c5992405004505038240e0340c070204140030103e80380b030400208054130305142586907100c0c0d1031494420100144802d0f00303002c1055408030142e1021030303044a48074840d05100d00000d0316030064aa009105001c20007961001500a80108400310040c02c864050741c0f00015a4201c41403048803440201d025520781d04050050b0003080d07a0044001c00300a1007150005082500d0135800904243c00400030406000001a00075804c070203889000d00582c00d42003d04c00c184400020741150701441240c140350284a2030b40e02408056005030020000315003070b01d40445c40b544610703100707c3e80840ca0081c4101e080340f40380300054908101d20b0340d100c2009445081c0c0c0c0d0f1152144007e0300c06803505421008100601e103443d00c401409226849014005641d0f9180055000d91001518800d902c0d100b00401440359010310400944400080207015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 914880701 1250 914879451 914879461
    0x1b05031909171b0f010903181d18060c07020f0909061f0e0f0108060c0405090103081c0501140301060503060f0c071b060210111801120b06030420030303 67
    0x41030300000000e000404000300311001c8150084002c94040f144840c291405114140c1c0c400c0d0103811507000c15804035008842c001c0143d403a586082c0121414030140380001d1b003004003010040e102c003401040700320450203800e200400090040701e0141e4100c2102c1c0c0c2d80c0e100584180070503d002c000511f4802c0b05135030100111190081003155000015203000c0c104010300b410301c1000913041da040516082d17000c4081148071009003082d41d0503604e00008403006503681d010008418841c60088681041500d001000005c0421000d807031803140b00c01d48620208801c01c0e241b01110002d80c07124024500c200000d641600302072084070007421050b406000a8031b8141000361518001504081d1070010001d22501070104016a4848aa13601542000c943d9500d5170020359800000e0800381702d103450405182030107205802201d1900885503160410811b2450040d80c1d2034210b954211081a1036182030300107a40d0b01001984128454041c2c94200901001c55000e0950500103490203540f081060207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 914881951 1250 914880701 914880713
    0xe150f06040516170c0705030d06170d0903170408031612110a020918030403050a03090f0e0a11090604081501090c050d020903100905010209101e080a1b05031909 71
    0x44e40d0814540030380b0300c054541c030340903800b03901c103400c0050902d00001c11a008247c0c1e06400201c102c50b0560b0400d025030030f0749504583c0318031881541801040c0c2280042000a2400211100ca003a0a00391036043c0795071a202141154407482c3c04000303480d6148401010070030810016100300201340b070500010410180e04560390588140301a1040d1604800200700c0c070b42440320501551400000d598460b40c0e03924010380e40721b00546040700403640c1590045101c4400822410880320390b101e200420362190b05800008001102020700754500130003181405450380c500400041c680000100f0080300540c1540c0705651041c0c011500742030038070449201c5c0c107a20509603041000c1d01500140d40715295000289840501901c244400381804860800d016041d400b40803c40007e407107420100320640401c40c2d00c88500110300c05100c081c0d5042d0942c8034892a10950300c00040c00002648140c00100350382e401d49204101320000f1000000c103d105600eaa40d18030342c2d994060400d004801681e60341c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 914883201 1250 914881951 914881967
    0xa0903021507020c090405190b07110a02011706010e1e120303151c05010c03020c0c01080601020d0e01092607060905030a0f08070204152c0a0e150f06040516 69
    0x12031043c0143c40c007117800e1003010701c240000025548d2100d01481c22610f0000f005d10022181e0001040c20b11b40826652500031800f0903000703505079130304402407192803050140368101030070b1941008103000c202007140d16a140400b0100000310b0041e20218100c00030803010300081102554640c00a10510a00c030621454020508004440c00c204c200c115420700001324a11100161141d03090840006100381c142d401808410b2000090324150310518005480ca0762060346c100d40180d000c0455018035501c608903480d0004c0d0305142040712256645c80e1800d20f25124030000460b415003400704c4041980c2040394000502c482c0c2084080f5914017000603854200904010382074200c1040300c2010001e01108030f03222158000c000300300341944038000c8100d2218030b000300d8007600700a50014041c03441c0805107075891145e41540d455190340f01c14840340904030202c410500d921440884180d030700003402140d482000100920000c138a0018200070036140e0140c030060f400100c121180c1d060f66800104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 914884451 1250 914883201 914883223
    0x515030109231c0c1b060e0a1413051e0108030c0601050904050303010b0d1b090e01050114090d0305040e09010f060b03090303150a181a01090b04031104020f030a090302150702 77
    0x10861300c40d682070074075407841111041c4502030702d11141070214400390840440e0034400c0d01943c500700501e80302c404040c4251000f1506540c400c0b82d0196500281240c1d4108a50043d000c0304051226a070581c00010b400c0360a0b000050590004501c461005200300b1003e401071508aa01c4031a904043d22901d4030f910060081e50b90480340020070030741d07070300c00c0c2d41161030110f42107410030001c40d2401d40700800e4604079018802d4608445800091103602c261002d0001c00046038500f0319202000040100150b02d95404a081c05803d010028100c5884c451503849503507040000b042100045001364102e448036080444050317410310a10011034400401e580e4861a851400301e14070a202000889200496000340102c2c02e1801000c54049469000740700602e4400c042054a55844001034030180003a00500985003010f0100304041084a10a450a01d2000c3c10040c60130500400d0200390364011078105c0c40083d114407890b0105541045000d05503611a903e41c16641003984000f0b4403403050b418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 914885701 1250 914884451 914884457
    0xf361c030218180112111809060f100b0706060b040b07140613030806040608031b010605030a21050d11070218060105090f0f060a2a150515030109231c 66
    0xc07550b0806c513561281d40e2007a01c0c0102611241c070b400b2a44040c000358129142d090fa8022503001c103504040c040201c0b80100c0d0031b540d0303d020140c140800b0428a4000f800f0940700b440d114400041c5100440c00144064401000c020341c6d100f5881c00c0c20612720b003116902411a60000040210302035075a408000700301d0340762601c120280c4035100014080d08903900041e41601001030f048800030300409060031100d0f4868028440c16075260f081685a200307000d4007030110305041d514041c0381d41c0b04400703004a0150b14100241043d907078401040031103201075490003d280c00050910300b5441d00c06055140100f450880082070701d8013100090040c060140c06030702441d00304074400c48955400f00100880c0c0c4004d4103590300d610031224024901e5150395017201c00e811684440341c064000b04414015103c1d00b01c0c3d03800840c0d1031020650783c01000001c0c103420404451004480f881c1c0d5080c041d1a00c0207009400305c0525031900c4070340320440d03d1100311000711944250001450740c0b481d07148072045058581 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 914886951 1250 914885701 914885729
    0x6010e060613080c030c04140703021308030a0e042d0b041419060b0f040b090406030212060106020607110a062a080f361c0302181801 59
    0x100031070810300400d220940d1010311208041805000090030041c500d00403800c0b00d000030000d0301407200311804000ba0030340005245000804240c040c3d00101a1021151308040d105640c1d80c03501d40c01c3d60002c94034240010b4900002c541607241601a10302c0c24200c203000314001c2d0850640c8500340c0c03003031030086103886903d810b80b0f0340e05d03a980d0f54804141c1d070340b064200c00403030702c0c0208a049412415442c1c0a004518140703012442400c01d000707070b13802a00c80a0b1240e01d041c2c10880860080d03080803442d281d020303441e50030100040c1c0303402000c0c1e203020710404000c00680d41004800390400e0340c02000c200800c9154282002220000249075030201c0c3c00540008038a0b110b64665800c0d0007541d2840c5414000008504040316032081c00148900b10180c01c008a649803003400c4422080204d4001910400c500d00c00e1600010324100c05020022040450350b006018028038092541c90105c8000403d50214000b8100940e0315035881c07056008031592021b0346980e0a0000002d40b0601900b16040081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 914888201 1250 914886951 914886961
    0x50304060e1c0507060507020708030f0d1e020a030b031b19120b16030c092d1710090c15170a0506100c0b070c050109170304030215040506010e 63
    0x340300741c91030344129442e81c0c0128001044003078055408800101e070070034902000201e08a1000c0f0b104401d80b2198800f85207045020740841d000c64000c815503090305a91540701d8281c0c5115169515401c41420f01c001da00c400c05c203040a002c1300c180d041d01600980200c0840c022100c0d001ca103c82c1d124104440d0010002c00f00000803504d480d494000c0703080018003007120014850040e011f18880c02d1008200f01281040140440544130002d59980104200f000244050f4a1622204a00d0b8040c0004d02c00b10321011145030f03032101200c0d8071404600c124002501003a04060141c180c06413149030741440906440ea9401404485034810801a440840c0f038800440380300f910320311542012529a64258200481003400a00303040d580507220746000e4200c07414032401000a59001d54001c00d0520740341d80c407040c0c02d44003550f82030802c5916540c0c4010314000079a0304220700e0007854140005640700c3c5060305e4081d29001003070400d1102e19101e1010407000800c005071480c1960325800543c1490b440c5c0d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 914889451 1250 914888201 914888203
    0x60c0a0306090e0c100f050d0b0102010b0d15060501180e060321180103150605030c0c06011707060503100612020d02031306050a090206070f0f0f050328050304060e 72
    0x40741e0403800d0403070b041c812894081e840000c1d4101070810b040340d1140340c0904d100700c2990320482c01989000403c10503c04815840d516900200d280380040c00007003840010035001803e403011300c440840c2c85407510742c40c040c041466441144080c01d020f09141d500307090f03190040390181c201c07449090075080c10a4002101502c0c20301003605245950510a042201220140110b4ae003040784886001118041254019846401003191174019035890140c0d40c6e00340b16040318035600003014a264001c04003c64058040100040f070b00030500c3e0340e41c0c040e8501c2c1c083c0c00903040a55642c007950800c2814014402c0d559000050361084031110300700f855521103c3c5100b50003a005504406215030310200401103141c241000c0d00d0003540c80b504080000340d50342e210303110440d06450806500b00d0310034402c0b54002000d00c8480b000007030140c021607400c2031407541e070840b44000402e402c4419420100c0c03800002c0541c072107045122500c0c1c010a80180d070400400500780e000040004e800f0b65143c100c10307600310304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 914890701 1250 914889451 914889461
    0x110a05030f0a060e07020a110a2d0b0f04030507140105033105030d06050303040810020f0c0105040804090507030912051b03030c0703020c09070918020c01020316020606010809060c0a03 81
    0x1681504000340b49025170001c0e448031a001001c0d9030000b004440300d489450003078400c200361030424aa00190b9044601c104291f84905103043c1c8008202c0c0c070002c030310214600c1c00b0340b104620081005075260b00307600d0214181001c42c1e0006041d0a101e407450040c50783c0003025240c6c40500d54079040000310450484042c81c0400070b461550210801c24400107121001c001040d00c000003503024850b156881090660b00d100314030607040c8542007010015910411034004212424507408054100740c80181d1040c02c40d070040c6d83c101c3e14034100280400c00000203000711607100e8081d040c01c0198032000c4e100e11075000c0346200041c04100002441d010400d00c44101441c80900240c1103a8981c0360038000c0907915803100100b80c026105140b0540842d103005002c01d48603200c2d80d50b440700d46900d0080c41c9509140504408251180c0a101070004010241f002e1403242102082074020b400c4001006400c01001501160401c0f45803002c202e100000040c1c0550000c0c1000300540d519914800d00300c2c0100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 914891951 1250 914890701 914890709
    0xf070e0609042103050402030d0804051e0c040c020c010f0302031501210e0606130608100c09081009020f090402030a110a080a08070b1f030609020d020306040c09110a05030f0a06 78
    0x8541543c043c0000e500d940000d105500c01c1d8200c4004154141d801d0f41c92090403a0b0007401a401046182455561501074811405010003166420144200010181e40c4c400809400503400408464031542c0d110f94800c0000da143d0808600d107041c2100300080341468464030a05114074080785c0c1800c840040d941d0101c40754149400c020b2881c0000d601c64658005680440c822242402ca0034580710652207480d0445141a0003031094000140303644001e0241d01541c0da0278040345a80c0060441da00b0b01071440d4200703001800165890071441001040c1e01150302050180d1030034005c2000507280046c5c1a0343c070f142c012120301d42d482d5200f0300044c1d8243c07140c0c01ca12201e000c0c107500c0500700b1075100003a01c1d40c54031901e6401d0741503540303544440c60f407031540c0e005010003400510100080344040d8460304125001420b000b4250f109500807070320381803050320103e420030000d070f1040110314a180f207280c2140f001005a10710b08280c94100600c80d002c0a03110250000c0c459001c00d806640c1d90384160010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 914893201 1250 914891951 914891993
    0x9080a060917030a090309143006070f23181507031d06030402150c03073e03150c130305030d0b0f010f0302031b0d0b030f070e060904 59
    0xa00d0044e20010181035201012408100c4480f808101100d071680b0780701c18490302404e041d048501041c940100c42c150000301d000c54100d00000b012010b0404d1210500c01e08160701c40700d100d1401188014050074100d0182c0080d4501040c810314000d00e071070304a48005401805083c07051119a0010f02c0c400150318144100340e200280380030030190070101e4041040c0a0303141c40ca0070580924103009140c802210025803099070740c5910b18003030303203200058503c80c00710404681c18611955101408400d28403401c06c8060080d080c1070301a400c90710480d060305500c210020002010150100c2c0d0b840c111164841c00c540b82c06800102c0860724541a1105144401e080700d1140b962820120740f41d91000048e403401c982040e406031a5424078064800c0c2c02101070f9601d04200004070401c07002500302034843c00c640e80e003401d0010301480088015100c041d01203203000481301c0c460382c00c052401801440f6480c494201003400c01c014031b80b80241550181c0d003540c40010907503852410701c100300c0c81c454840c014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 914894451 1250 914893201 914893207
    0x10121103010609231308091e06040e2509090902011b12120501180908070b0906071106090d050c100204090516031e02090a0b031e0709080a060917 64
    0x56032221381c060403c0081d000400035912204465020300c201500e018160300b10810200b80d850612002d4001026440f0001c000c281c030824002030341c282d200341c3c0207003800e1008a0511a0451401c40c0299002ca04084905541115900040c154801034854200150f40c0e030000d22080da402610800706200b54451072a0045407a883c02d120304003800e004c000002880306a24076000c00e468405d9605940040c0d40061800d181100f04102400b000320044030003100a200100014645040f40c034010441c01010b032003640303040d100041c1866003508003800c20741e02ca40140185120f021030108000d240a19080d5910403030400030600d401010740c107807510350b40700050008507144681e10541c050603140040c40d00c190704410044040d00c6a80310000002e100200440211544950003054540c00192110071956031b103100380812504100c2d00b603600d507510b0f06003110200486103109070340000740f820300d500349500b0201501d641d01813460005014950b1120038009120221081200c900c641c1036440356 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 914895701 1250 914894451 914894471
    0x110a0204111213030806150f0c01050105040b0103090327031a090d030501051804110d05060f070212040b0d0f05040302012f2710051210121103010609 66
    0xc496202c040c14203191105140400d01d40c000f143c861000c5190160380314141a11144100b100300a0011401d21505404000614441c142003002d0641046040c1c00081c0c00e600d050f0612003a110401c401d503041501d4048c02d9800a0f400140e40d508011101340d480003040e00700d07051800311000580000c2c000c081002010903440c002440c903140306160315015101300e42082d80c015001d0302c10a010b100e5000462143c040c250200296030359501a004950344100650120f010a0380c00890f483c05441e05d41151040020044480103101d80001d81407004010070300011070880d43c0d9018a000d142c55100c0c002480c0000020a5001a26140c4444104002034107141c90080c0c000d000c1080560b000840318034041d02101e165030030a8041c050001d040c5440c2010441440034210018408813208807100f4201d4211500c0d0003400903d13008a5859482d61054547c4504a03031100003041d11003105d00b900c1d8107200380d80301010845002c5a115041500b0303010304038000303405441980c00c840041407402c1d20082c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 914896951 1250 914895701 914895731
    0x21e0a14040b0406120326070e040902270c130314031210030203160819143c0a031b02030a0606090b06030402060403030c0201050d1a011b0201020d110a0204 69
    0x70391780c46921010041c0384003000d000020581c01c2249205111240300003082d860041c1c4041c40c00110040001452035403d500158025844480c2d22201800c500407080040004141e100c4d00000a100c03030781d050800708098401030b2003481c0001032942000021032058144100705403a5992408000421289030600c03505065142510060b40710340702d0709803403241100120313001c0b8082e5802d42c0c001e0302c003812050702a0310b04290b48280c101c074594000c00a5054440e018481c0d030384428001146004103400000403141019000e840e201d41803200500b01c040407080c00644490303080d60509107031520285c220410016000c0026003c0d405006a19036403007003051681c4034905540600c2010080300b0f9203d01804540d010884000350003000800c01400801d0007180080e481c0c1e881490030601d846108041482510960304144000440000301c0c0c107810b6030082e4040004e031a0004403814041c2075500000d40c0d41505a91120174088071401c1e4480c00c083c248485034443d5000350090000007503017803080e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 914898201 1250 914896951 914896979
    0xb04260a171e040b06010c0c0b0c070602070b040e0402151b0709140c220b0705100203070e0409030509060c0a06061a070b06030109020a0b0304021e0a14040b0406 71
    0x40d10081d80000d000b0b000a1607a891251288024044440e035495580090000000c0c0880d03050050021120000072100c55120000d4414240780c2a201c0c54010102e03450b010880c2c0040c4d0542d00280c0003400700d0701c0c3d00c00035901202ca10030702127040703922240049152500c081800c0545624006640c60303017442074010820602d404541180c8041e0b50300c0e0210022103240a075110008030a0703001054018806074041c00f040c40d00203400700800406c091022000e074609a0200103042c0010520388248101445440c40724881c141042d0f01d50718041c1d030002c0103002820019881a41d4402e10842410b00c40c50540b5400c14001d021503643c0e017007196003540e503656680e2040b0395050400d41d01041c045001d05101da001c2d040c0c0203030541009203540d0380511001000b004680c141d075803070420340c005d40d481c3c4c2c1c4442c004201c1e100110f5900c0c1440c4c01440441e500220003c180000354120444154039195100002c41d40542c1031070402c016224001409004411010303540030741800c50103d040c0d0100e000c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 914899451 1250 914898201 914898227
    0x190b0304140318040209041d10050c040b040603020a030b060d0603111c30080403030c0905010909021303060509030a020d110c100c050105010806150109030b04260a 72
    0x218000d0001d0441c903540d40b840380e042280140a1007411012243c1041c0c4c02400611200500c0450000c504014021042c2204000024a64414082c1003400081ea21549401205410720286001c1c140080d08100b03100342c2c8140b4081682c0000c2c1c6041852081e0300541825400030b0815a0300c1c00385084600280c4030602098681c1805012070340307000d140801e568914080c8203981d50f0070000c0c8945903007803981c25844040c41c08401d6100d0f00d000d840380b03001c803805424005489103d0581020b0030000d003190712540050342880403080050100341c1e082140c1314100d81c0c583c80b000da40c400ca402482804210603130710060206040205126856202102034481300e59641c1c01c0f1200d823031000104607000c0b805d0414440b1650032030521080d02d800c0182e10300c05910001d05043e151466a65241400c40328240e20403002c5800020600c1102011039030301d1030070031001b403034641000c0d821074440f640c102101800041c06c0f020164a11034400100105c462861860714a03001d8039003e500c0f501511070241c03d08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 914900701 1250 914899451 914899463
    0x160815090c030c13151b1101030905070801060603090b0f040f02090c0d090c060e03060408071b0b03150102120405061b0a0507060903020102060622050403121a0f030109080a0e190b0304 81
    0xc094006d1002108030079040c150081e250b41c0c0042610401900280201c60080e00c003401052000b06208400f401800002c10899a0000d03107a0b196080c07050b81c0306406454000d1054181061001180c081050481a03a404841c50b124a032152843c0c0c2c9540c0c07280c108400410740c2071044040501200740c001c0303003c460050301d45601458102003055201c24040340c00030b003883d10501c01000810100070450a010000404003004a5102d03980c0c1c0c82076400884220317140c0300300c80c1d4480c2c00b1568188580900341c04080022401e1608000c00100346000340e0703040410400449001445240042014003038258119050fa00320a40b40e48005000706075030700041c2d0151141d1408207a46080c9180100c0c00c3e080d0910691060305003600758900034040241054040044140c8041d0700c0940f244101c0081e070511000350040821148144014130021200140c426454115510003162008c0c08a4a5258052400040250000340090b00415807103041c8000b09034051070100384020304d040110300a9011704 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 914901951 1250 914900701 914900717
    0x90f1409160927110310050604051c020a1e090612021507020f040203090f0114070221040e01031203182f09160815090c030c1315 57
    0x88a449036885040c428000246004a040040040640b1111007100214802d80142c0f1580a80f0340c05803404014100b101c40c40000900141c0303c80540c40d200100b07420760745141071034034100020b0403140184603880711074010078010354215a145501c0201078448405041c10b8038040c0c3e415413010591a000d1081c801c0c2c03501d0404150b140e480f10a0028440e4000d103d10321200d0501c45101036500450422030308912880800c0da0140d0350390020314441c84000000340314800807035907803900b56140b070024014090200c1d0180149282e000c01c1861110012010692405040c84c00f9031115106a501ca0381090003113000100c01c21214101c3c3d064060525501070000c1c0021110f040100c4481001c02400c40030030f07640700d18204221441c0452808042507403881003a20000c0801c18104044404a411012000e03248261541050a00c0e4000c8040e00d41c017001040e8201c04114a94801740600c1c036442d6020001a65401c200b1b011036100044425941f62002d07603d200304050b0041c02c61610011079591 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 914903201 1250 914901951 914901961
    0x191508100c0f0809030d0c1e030f060509040b060402030c070f030518091e070917030a1416020405130f0c0503060901090302031605160803030708060a03020d030e01090f1409 76
    0x2c1011500803d8100040d5152842d0814050010320300d0440d038405011000c1d10f0a0700000c0d04942d00c040c41606070310049217100e245004200bca9010742c000034816442b4900b44400314501414032a8404416200160782c1d4540101c0d0f88254002d4400062110783d064098104040d80301c00a0b14858030380ba607000070229913a400b04884800c0443e456241d41d03940c0400c03400d41404c14816181c108141e400c05194850300d0b1900c1c0c00d1b0300340c2020781a1810b03500008000d41c16035070020120030940d60380c5600b1424041c1c00304040904a80303d5001901c0b940c0c9410220309a500211080c502d565031102c981ca000d1020782c40c00500c1c0d9815403255038400e000700c2c400105452418040c00110325450b81c059460960110500d480c500780c4420280c8191142060b4130141c41c0303514031101c0150160100954482c07906960007040d540c80102114010480031000f0801601c0349081032400981c1402c2000b40b81c5100c1d00101e80c810020380c49a1080f0035841c0000601c00c10414200c00080700035240c00b1250740d10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 914904451 1250 914903201 914903207
    0xc0b0a06060203091003110c1f05221703190605030c060a110703051509060604140606181509090a0203010e010b0c071e0503010b0405191508100c0f 65
    0x3611400c00542c10400548290740b400444042c00c1c001c0c2403c00181c00c5210100b102842d400c0548182d2036039000054810104c01c0d050300c00d45070130842c950188500d180c000da1481056554580c40b10806100c4144c240400404071b4210440300c544048803500c2c3c5c60322540003c3c5003840440c0b45c00c4100e14001002c540d900300455050341d85080a03003914503144500108a640b200e030440d4150396801101da0100001360188000d401c9244100a46480c0e82410346501341072500c05000340d44034510301110540d92450703c2c800b8945c018012182c40780c840c403110a00d0103a090207404d1845d407100110343d4903030488001d140684004141034a100303c1ca40d0703a0f41448803ca1200303001d6298220306070801009850740d054014113030400c10000340e40015a85204800140408484802c0328040b517050900544c1024800c0d4074032980216010f01c414104891360025900d00013400b0f00010340c81c0c0c81451195040f10600340c00400880d411600106c0004941c00010400402d07039100003041b80e034403e003100c1d01c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 914905701 1250 914904451 914904461
    0x1213083a021b0111090609041b0f0809160323010618110c0c060c1005040b0708091b0f040603240b0a211505070825050417030405100c0b0a 61
    0x44c80ea41c1c0b64606882d41d07017000788070707040041210360082c0c481100a055900e40c84001e410318105440781e10380c072a0014000750840100400e8810b856020002e41c071000308000f0841b0040700d800c0b00e0206000d040b4003400820800d0b5110300d10203c0d48c2004c0d0300080b107103041015000c46d0050a0300801039060f407480703200d060340b01d038412641d40c5038000018042d2500e0890b0041500089280841754201109403208040e100220781c191440016907040081068000e00c049510581040c040e012010054124507444480742001354000d2100d0751284035692542c3d40400091500f01d180c181c100050808000c216250380c0d05288105814805070164a05059200742c06a034603034108880d2410406d201d0380204038501006903126045103018515282040c41650b0040d540307552441801d140441100c00c6091100000303034038a400717140c07040f640c0170342c441d0a0701c0c2a6861030200404500540c9070b058598062500041d80c0f080300d000d00b00e84119041100c120585e403040a0350f00856950b440980c2c1212 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 914906951 1250 914905701 914905721
    0xf0c0b280f120b04140103061506030209130905071701050615040602070e040816200f0d0f020a08070602060a06050a0614160c09021213083a021b01 65
    0x5030310750b140007100c210660044000b02001400c00142c20094101c800b0250fa801ea1003178a0301540c442c00c440c540084a40c1201c05070001d420254540412100441c0c1320b40c50300c00d201080c85035101f40d014204001804207038003e04100f0070581c008070101e02100d0080a080c0c0303469114144109507910300c0c0c003042d4161021140303240c01030310225140c94000800c9100c0208200c803442402c010448081c05070b00e0701c9040d03050041001001d00c02c102019002050320035945c0d03921910904519001d550780700010300450f59442030020000c02941c0c40813441a0940740c0000ca80c5001e100f01c0410500d500180d81482074001d0601030080300d60340d90070700940800b54000c0e03000081115441850004021004100031407840254854030075003921143e030f40500c190041d6282ca0340000300729001002c04196243c0244418100382c40c403140c03a58400c4000d2084010045001060300e078040507000700c2ca2a01105140c07010a203c0d000c85041d82004002d5019021022920380203081100e0700200c14800d4440079 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 914908201 1250 914906951 914906957
    0xd350406090e043f0e010e2b060209030f010b010f080106050a050903100f020406140301120f0201171e01080105090d1407020a031406180303040f0c0b280f 68
    0x40b01c0681c10511200d201c03521403c031120180300720741e180c4c0868400e4030041346030180c1c0c40c056400320402c0010040c2d0348030001c01c2e11480c0c10720100960403608a02d0040200700c6509000d0340e220062401d20701038007500c1501603250281038020388440b201034010009a000998440c103101c82211410f456880d03081c0904400500f0a0201143d8140110700030000403200038201d5880582c0d007000103069410800b003400c003207500410100700060f045541d2403d074008141b1007504541c10320203c07141e00321a1010141c84091010340320b40642e402504d00200100d80c040f014001d074035140c141c0b151040035800500b11202a00e03000090b00031010704c107840c00350341c0c510050036a030210010304454100c042c0d140d400000c0020050540182e41e1a2500c4005500c102210710380780c000b684280c0c0c101000200700440c00000b040e1240300c040f8011080742c1e442503020100000007007047c10045101140c680008443c00c8001a40000840c14000740803001000c1d00100700d96514408012941451002810b80c04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 914909451 1250 914908201 914908223
    0x3060609041a040206040308070303060e181203060a0f0e04020f0a030b16020f010c030e01110304080406080915011e15020705240f070c0503010207020d350406090e04 73
    0xd00651030310b540160004043d2800c0540b65210750565910040044011a0390307100108400b00410349040e52000e401c4034803408101c1103101080c0c07502ca448004641e0402300000182c15507545140040107000c4100302c644903d42c40c0c409180c2e250034152010b82c8500d43d1150250050716001001c1c1c070961340d2060b002c6500707486004081c1c4d500390b0580c80c0c0d1415402503405910b0b580100344035500c0100b049960204901e046402d041d803c4958009000c0e0800c2d030100708010200d05587c0444007100c0d5503161401190392007420003800d0004001d080710100c09081c000080c21400a1400d0b10b11b6040010384180250f030310012504c8203c4005e400d900980c011030420402da192000c8040980603050075000d500303052100280720b1075400f4120707070b080501c1d011840000340041c05401101629080e0001c5103481215000200e506060050041240d8214520340034a1160303001900881062028252491340803a40d8a480e1a00180119000660b01200c0051103100c449211030041d1340090504031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 914910701 1250 914909451 914909483
    0x240d0804180b040b060f03040303110310061725050717040501110106061413050a0e0f090708060103110d020d1416050913030219050717031e0a09120606050306060904 73
    0x3a41e40008100b601415070320061000341cbc1804c400198860601c0c101800442414000007900d150f0310a418038444c60000030400080581d03a040c2c0e0200044c03094000402940070072400c1f1280e21070110020943d03068401c40144082e104000f9105a034000d0700e48418080a41104074200c076003e2080130009240001590080b00036040284400c22201c403c2015060316040401d1058036250700003050301a081c0d04014103950391078101c9421407a543e019048203441c0c107107030755681e082c1030001a0188036030105032010b558070700794481070959002c1d282845030314890401c0054080c0b22280d814407802480c0500d000000440040d8080d80e500412055147c0c0f00c2084100c040341d4201011004c1d4855140700d401c1e120740e900d1018401c640300341c00420045080181041c0e18601c07856640445510a10003404043d4851600c0b90b54a030300c5c4c511064a0304c14901c0102c42e694041d5220500140c80c5643d06020700001d40c1000d42690825003c07101c40d0344508090118a210846003d0400e88120040074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 914911951 1250 914910701 914910727
    0xc020a0302060306180f06040b090103052112070f0f020d170c1b100b01030905210d021605011802060409090c150201020310050306240d0804180b040b06 67
    0xf42d040207014003c051141d40004040000920584000000001b004100203030341c68540140840304405480f1210554510780e1100d980310500541240000003841656510302800d1007614100f03195942e040c0307014101100c0141801c8504044603001a1024803198822400084c00c080c100e54240e40e00d00740d803542110300c28003d60000d800b0543c822010083d0480302c1c129120260990039100c005060440c20426075030044507100b45005d818141040ca01030046000850241c0000703200b010b42104a20850742c0781c2c03c6910a002e0200c0e1030a00c042201c600c030200300010000400c0c0315200070000002d2160100c01c1000342440c00a6004c0302c01c02080c405001c4580150a501b44a0300f940440030f92100f1101c60314100c1052a900141e50110402c50302c500c040b081c1c00003e000940142115040001001c07021401c0c010f2004180100c0da0894511038440c00a08a0400e40000340c1648a94540008482c200342050200c0c0141e07081100140c1d0500d480d11915a10020062034545003c00384a00d003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 914913201 1250 914911951 914911957
    0xc01030504080c0703080315040b090609040620070b1f1710140405160b0306120a080a03380f03100504060519021303020d0f12031a010c020a030206 65
    0x11940140b00340140040c003c41004a000075520078a011034a074684851103148020030000807a1084d800c0c4080c142690325500003464002c1415107050301c003995642060745c00307806500e507404000044014294100728514020303100807441040320244136161441804400680c1250b0481c940c034a200d0700300410750540003209822403032081a1803403000000d80c144202c40d21501d0030009503031013001b08010030205010844000140310142607900d0309140400f002400000c014901a40c030412011245802c2040000f00c001e90154586940d0440e4840080141c1400380f82008842c034580548503083d401070102c2084500507a81011120021804021b400d0460ba10f045804d4017403070511b0922441d990090500c554020780001c15241001c2d480d81220950a8400801e8184117001c0c0350f41001074003c80b0000c51360103d50b14249885581440064210085401400304c0d1040000d85a4250550000300540441041444140120500548800b62120740003075000950143c01d2006107040302c01307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 914914451 1250 914913201 914913203
    0x712110a0c0b210f0406110c07090b0306091906110409020a032406120b06040503100c1407020108190b060a090503010b1f2a0308070f02030c0c01030504 67
    0x85682449160300e46200c4820507800104a90b0701c0003801d41260701d480c90340c144070405011512070b40340c40d110f4120079030000060401400c25031192039505d01c3c0c41c0c004007554000f2a219081e103c1c030b960b4461464004000d411192402030244a0020384e103000c000c00c03042305421101400c3c00c0d04c0441d60ba11400288081e13050440501814000401c111041e80701911090009850029481181d407580840050821031071000e110b84040f02070200e0359200003407240300410f900c0c01040007103103180010f00500850f00450b41500c1514103130409603502da0002803080c040e80d12201c103040ca4481e0079101d00d2089110107408900d03404085107040c4010005049a034208090004082990304001041c03580104902d0000910714103040c4110f1400388034110b08684201c825103141d040c007100030000313200350500c1d05041c002c056031100400710101c08250050b400c0000724a00c042114640503000c2d00b010f860010014600306c0840c5a02800013085070005200c0c1001400f203032001c01c2c0110f01030000104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 914915701 1250 914914451 914914453
    0x90609111902100c08060901080303091209040902040c0c0c1202100807030b0a12170a02190303020409023405280501020c0d1107050d060c1e0e15071211 67
    0x90f020311044041c8100c2c0d10b04040c5940c0d10080b4103041080082c0a141070300310803850741042080c0900d80d080000e0804001d01a0103d0603160841c500001e8018052520042e41140c24151030320301e03250717001e0042441a031085041ca985c841d120b41d4140399204200c00001d401c400c841c00c0c00880300e4090341000f50b20880500e00400c0d94040c000105860801541c0082c040f080740411403c10411600141d20f01d1032101c2508074103080703a20303500075660206440c00a0700380c0b8590455406040c440e4040307501030070300d0380415940d0b1403054076260841510306c207880300d076018900c1c06405013051405076800740640181c0104840e2050407201040300d1400400c203441c10076000240400200d0038000b03040c495032007401038840080c44180c06081c1241d10307169414aa0005281401155258440012000e800c40c07030010b00390907080d03025101000301019490602c0140140c044a4603842007120341d41074015203a0203c2d0030b82101c4004018081d00400801c0a110f0780540380d10140b00c3c1c241c416071000f03458 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 914916951 1250 914915701 914915713
    0x1209060b030109050313050d0f02040507050421030f0305041106031e13020a0518041e06150f14060405040e15090601080d05190c02030c0316090609111902 68
    0x1000280c01c55000140413030301500f01240130203a96940c05181d4004200540312904a07207a075603100c06281441c104000d00c110399541c08103000511074400c1c0c401824400072002120074241c984200004602001100014441011258918468001c003406030b035201c803c05a1040d004420000035400080c019001c80c01d80344400210204071049442c0141800c48a15905090500511a2a1034a074102038011514020010700c1d200c04000340943c0705402080216043e80640c5020203504607040000d091603041459508c0d1294542849d60204d0750789000311031a07280e0301c4000c80180e4000b0001c50fa03001e0428441000b260403c0c3d00407104c5441c05030152800b2400300c070f000144d092800c0d54000b025902c100c0042c042403d08010b200801311a50400c1810801c02c0c1c0203219180c0d4003199068208101040c15070110346003040301d5554020002c09540c5240210840c145813841188100da40107402c0010000e001c0c8210300c220030b84042588002c61501440907200c4400714030b000c2d281002c6114031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 914918201 1250 914916951 914916971
    0xf050c1005031906051045080c03151003080309060709080604020d0303231503100b03070b0304080c03030a0204090c1d0d03020307170a120b01120906 66
    0x1290345003164400319201c242c0c41c0d0510b40c403d10000d0310b03414450396000d0b151407000d115035034801d4640143c0810520342980d40202c40c1c489940381c140320f100000503070038a407446000011040d43d400b5001e1440c02d20460070301c41d66004815030728150710400c2138140e0403030b0b528940310b503045141590340820b2424100029680d644c0e6030304540c6c0d004a8003120550030034424005556440505080205030ba900100040d04054000980c5494070700d0f0000c1c141a0365140448070041541c80c248100410942c0460b910b28105401d21462041c010300540710707000c2c0038800d035400300385841000400c90004d0018003c2500b00180b8914580c0040c005452005042c45010b0880800f00b00851240c0060913016845614000c600300c156206000506c041c00b00c2c4001c948081c0540d000c1c200064141202ca80591500d113040c160b085d40315800001c1e10000300403a20440c98601800180f082e140d840d512038215011003006481119030040074603002440c40100010403503040d030001c0c50b169004400008982e4a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 914919451 1250 914918201 914918209
    0x4061103041a090a0b03010f0509070e03100e010b0a0f0306020921210705060601080a020c01140106020706050c03090402130b180a0512060415020c0d08040c1d040f050c 74
    0x5800140c1d00a800003949040c18106021403100070715003004503030700710750508092403c02c0300b076409154001c282b0000001c0038244075140100880d440075042c2c1d024952110041c20140002103003000d459801c0c903000c00803500300558028126403080381d01c130a04906554a102c0a540503140040c0c0c0b0504204100507403281281a03803aa11041000038102d00035114854000c55206800da0b413140036052210401080001c1400b5900034401d18150301940d80e0408903000a018030321b04150706620300000403c51703101c0c03050380c20f042e00c00726006c0302c1440e130f03a640d0101c840c1c4c454001c0e0050b203500184500c1105040503000390400081d6030100d101c54030b171100d002d40700786c1d002103004842c812020000310440e41407110f00c0402800c81580c2400400e5540e41005980d0b00020b04010100e0b0425404d441a5021682c140d030003041058050b03c7d0341080e02c2400a190340c40030b950aa130302e241c6100000689100451544058018142c00104541d5982d100d4500c52483d4802c10fa8050042c88800aa5039036 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 914920701 1250 914919451 914919479
    0x50a1a0a1404090c080a06120b1009060b07150504210c1a07030b030d0f0c060207140d030b0303130e070908010e030a0908010b150d140421080103080406110304 70
    0x820b0500159544103404002c00d01c105c05445100d01c00d1802a083c041c0481140c0b034803031480c2d0460440c0207242c827840040c2d2001d400e180e00151b0807070710340704000c140b02580070010825070740120740d60031890113203c20030170440d10207543c01032941034102d925408007a000d01e4040f080e40d1031406c003900380c1c1c0f803183c4a4000300d0000802d104400440749040081d050740511410701c0201042d402040c00c3c1551140141c4030480101000090000b445294801c200c2c00e901200c05181c0d00c0080c5080d143c0d240710b011030f550201d65221502290078101045500c3c01c0c0003098440301c50a58144000386c51500c40c8000d680308015000d40c040026920f40442d140c4070034055484a88145c2e0015965000180c0c401404d40b501b42e00101200c2c0d0401020032420703030701d60f01000400ca0684842940e1403801e5035041c0b0003002c1685200c9000c049680422081c085c000408d8a074a106c3d000729040c58580f1075004407003004090200810740c41c0184424401c06200b90411303980e081400b82168505030710340c0740040d6090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 914921951 1250 914920701 914920709
    0x7080616021c0206150f060d0b1804020306070507050102270a0501020102030f01060818070f06110a05071502071d0115050f04050d021f08060901050a1a0a1404 70
    0x14000c00d2000d000da8104840c1541c01e82480740c0c5003082c00c072840025110a0041c10000840601800000140e9139140d07411079082e0004008030741d11445000210003410080d501a0b202d50300c800d00c22801c2c480c4500781c00340b007245c0c020050281c9640b20301043e01c0d580c0000c04180c03495982482500980c00c2c01001e1154110f20440041030304c040081c041013a5201c581d0080ca045900600911001c4007040146d1810350300c060900c0c003d169580c030944120010b04011402c21441407090005281000f82c58001c01e40d2425560041c51003206250265070307060290006006910019041120200d1048042400040752041e100d109e6034402c0c2c04101d03240c49068105004034080c0c01004490070900840c7c02150440c1040ca00380005c038145d40c1007602a43c42841e01550b503410201046680b028280d8021943c4032011404456800300e000700030b800103c6031540512114000410359140911148040318280d1702640c0c0700c80600e00011115400c000031104c02e000c501c940001405010201a001030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 914923201 1250 914921951 914921971
    0x7200d051c031e0c020f06160807090308070210140f03090d0f02060114041119031409030d0207051e0f01050f060913031101020f041404062105070806 66
    0x10740c000700003010041c00c01c09041c90526150590740540e02080e9000102c14800502000604124051040e030620030811260181401200b0400c940b031036510044014012a0b599691496031311940280c0c0c6407441c0740000b0304040c009010080062900340c1c4044c0f0740c0e90712440c01001009071204681c540b45c0204820500081c40482000501f00e000c1140b0000100d051030480852a5131030006900e4503010b0140710b4082c00c40250b20241501c0d05d070481e50324a0803281205655641542211036035504001d40000000c1c10401124543c0f0101e42905001d800f00c032000d14603003805008504005d40c407941044581c3c0c0100710900d420404c001e0042d441003440d400182400800c130035070342406c4500041244c3c00e08001c1178140200c54a441c0450b0b98032950301d00700d0032030010560074161130f46086a080455a5800001c04032039181d0100d02600c02c0f07a60302141482c10500800c108000c0e12a24000c11010400c590141130105015580d4424041d00074011398620300d40ba800c00f60f0811320101e440c038940f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 914924451 1250 914923201 914923213
    0xf0d020f0114010e1602010207050607090509280c140f03010e0a11030a0b010c0209010602072309130215070303060311040e15061203040f140907020307200d05 70
    0x6400e80a0050000003200a0818011036040c8070541d111514064880201c00710301a00d042c6100d8001d41c1202c049070303001804c590192070000c000500e0000305000381401a14504003003950380000040c9041c00003c04e12040306006910000708005100c0f01030b5150411201d844040d210382c20781c0000785002c8600c5080b1300d640303605102203e5680c80b030140c40880402c0c40d042440748207200400a40307070032480204000c241201d40c0b01c012600c0c06543c40e00a90311801c03c0b0000240c46400041c54402c50301c038080340c03851007107038401c80385a0480d020f801c4507008404407001a40000380d40e2801301c12903100524801c0c1521611421200d1504003d10403404240e9a010500500450800350b2002010882d400d20442141e134404540714400c1074036038200c042885e4089001c0c0e03510b006550384449240c8003166182e5585500c0f440c000e00081c0708200c012072105e00c800e04182448101da52240304a5001141340140a980d94240a1001040b1030f1050600d5422019160358041c28109114003070401001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 914925701 1250 914924451 914924473
    0x403081306110706020714011709060f0c07050c2e0206010303020106170a030c4806170c0412030c030305060907140702060702151e03010513020c0f0d02 67
    0xc18150b00034409030140d4400202044416400a081406e440c2819891800c1c182c44e038005a43da40040b51600700d0030b00418080141120002030243e10481a40f8500e140540b10301084120912a41c48043d0154010701c00c15481800c096181e01c0000402e0660a83e03003e2081c0c5a80403940f41403544080184c100c035004006140d030900440000c0c10564041104504043c00b41c07a5441200070f00003020302100b08800c0301400300c0c0b4010161108080010860131450380d00100240e9890003032421451140106500d1504100c9164003099076510f450b01e49105074032080c00598004000e00e103c00c0d02c001081302007007000c1d0385518404814032944079400c9243d450310300942501d1004040c107014003604c10400103030552002c480c41c03e0300c07000132082c2d64607400b03400407440610030060040d400c03606541d21302401c0030119006150710380e03c40c18403045650001420300d43c42e1101f80b003002c0d0b2060160204c1d481d005865030081102d0342141003180e4040300e90800880c104013942030000007681084903120 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 914926951 1250 914925701 914925707
    0x4050c190c0b24040e010b0603011404110c0303040807052104050103050708090319030603060203012619150b120d021b1c05070b120105010e01170403080601050403081306 75
    0x9403c0781100c00040c401e1000e49014480d08070032080000d00c01c07521004044000c0c1000c0d0f20120101e00040d002603942e6031149150086600840a1603000b01e20307203a654441e11856902b0b0307078001031049010b180b5640700e035150745e0030941100c04140d815002d0b444802c0801e18400c802c01041d40002801c0e00d880328030740000501102d5000303040406020000c400c0001c1204080201c8910030788444195032117503e1010110001c01140e00002c00e482e10010010801031041200440d00300401c28500c4014500803d01680b0348209065061b01c180d1400b2140340001c0c00c1d00014503541e0030f8a440003ca41c03c001c8002031600000840d6000950004806120a59030600c8800701c00d50030b50840e0114103105402292110100440611103c01c0700b03001c00c02003200c04d014240c0245820f000440d02c0c1c405488120108640c28442c841c04544040c80300191540103517122030008c03054048895075560baa40701640c840c00000c054038100801080048000b0b00e07500081c1c044050790108100700182844005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 914928057 1106 914926951 914926973
    0x2120309010f0c1704231c030f06030b16030b060d0b130603031725020606042d0f060323060a02040807030204050c190c 53
    0x11015a510541040101c003410032010072880380024001e445070311400c90303191542c4d118940081c01080b04000410038020312813001660041d40e210710b0318280300c00c070f0762042800d8124801c03c22445905208800c004c8200700c008200003411070f00c4203501d6500003030000e0048103081e40304103092446904485440030b07010b0302c115140c0f245030110724094035070440ba1030701410140002c0d1118110300d01a03c000c0342c1e0151188d0441700103110000021100003802d1205803503aa05010100e803049540c0c3e10040155a405400da03401d02000f00004d6800e5603498000c5105500300744046480910841c0d82c01100c070900010340c580800014002900242d8406040600108509440b2820214828840620142c152000c030382e02d125418007203010314003580455a0003080284014200307540302d1034001c80d01c0d141d2681040240c91240203d0b00300400140e000812150b0034808000c050060 = true := by decide +kernel

theorem cover : BRFrame.Cov 914748201 914928057 := by
  have h0 := BRFrame.cov_init 914748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 914748201 ≤ n) (h2 : n < 914928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
