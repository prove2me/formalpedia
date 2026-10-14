-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3455
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:42:53.525645+00:00
-- url     : https://prove2.me/submissions/446ac936-e01d-4d44-9885-9e9459cc2b5c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 621223021 ≤ n < 621402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 621224271 1250 621223021 621223033
    0x1209060203092808061906080a240e1006030302063303010f060608060a0902030c07020f0f0414090c22053103030b040212010b0a030617030a0809 64
    0xb808910031051004000012610b6144114602d8480801410182c403072242960b815262981d200916a00440d0014480900e803600020f0301e03135004601c01d248035034085000b4105074803031324100078240032201c00070f09880d644c0d142803c42c61100304145085a000c2d94030120700e051450801900b003002c0140385e240c00e0007030401900c100390103401f100305134a40c2c0d880100d400c1001d03001c0824010001c482089240314a0070801084803900038a4061080e9021900f20240ca81c8500d00300081e40419211440146018484240189000308a0f0046904e028081c20040c03218440001d042c0e62041c00002141810072045c800400e80511003410401c0056401c1e0401100952a00415845c004040040169510085000d0700350f40c1c4212000a0348000000d01401c083d5961890b0992000004501091804131000c2c1c00d070a080c0241d4070000540b511400480e845c000c58006168440c5130b486040640d038000c08200c10b46805403010150b074a1200440c1c441c1c1c0070340006482c4290240081c14694028 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 621225521 1250 621224271 621224287
    0x8071704030f17010e04020a1205030a0507020d02130903110a0305120a06081b04060608011202040b01232a1002070c0b0a020a0515070f08041502071209060203 70
    0x4154400d41055241c40c200c2c1184492500894001c0e001c4082441c02100d25000010411000131807540664004c486222405503107a4080c080022000b10040443e00240050118640208050b040390f80c000317003041f072200d0101d5000848160f0703050706c202003503542d9048480034503a02001032090440f240303009100310401510b000e0402e01401001d241d26000c0000080d105103801e0b044440180110340456405556a0107400780b81402003070310b64000c5140403000142c80344100d8115040b0b0b03500d03411001c0c07144103503000c0c0310107010040d000034140180c0070542288000b1003c20702e500a1181000140c84034912240340a800040c3d040525845a4289203400590b03400700701d5603020328403800010307529045803805c448941410751200082c68404500d2003141c9801048207090b251190007510b140020407511030a91a006560420000d0000e00181d10002d00454030b5070740180c061038101c0d10703d0800b20486401ea80c0020001c5a1594224201500403604100901c0c041d00150000d10f040c6140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 621226771 1250 621225521 621225557
    0x3090c240306052d120a031e0c0b04080717030c072108010b0315131b0807020d110705090103120210060302061e070b09010b0312090a290c0703030807 66
    0x6560f441109040d0051582c0d400c0e80d01d041d0b00520100280060311b000500700c3c14060202008004603078140d540c0f424442c00218890101000c0d0750354814420025912182c90790001908038140858092114101c0c3c4591042030001440c400c0e0141590b99a440c040da00e0210710070413980071a203203002c02c01c1c071644980a400100c268190f4250101c2541c5941d182c0d80e0500b115480c80410a41003040010a070394050b000d03800c000340341c100310001e12001e8651543d04a41250341226000c00503001040c0c9292614468582180090117440807109815100c0c000501058401e80c0b040390f183d081182c0e10b81e0f01680502100e40d001c43c010070100005031070354000c25524415410131201301c509640049410003021815030b101290004810310241c81c010b4426802040c4010501d8400d12603449940120320100d8200c3d0801c40014100030307110362800c5091011041c402d4101140e051087c103080c4142020100900360214000c4010300100c0e1842c1030142c1611400742440040141c0908190a140c1e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 621228021 1250 621226771 621226819
    0x2100212070f09030804120201080f0613050606040e0108070617100b0703030e2d0304140405060d14011a06030106170702070f08010f0c050a0206040303090c24030605 73
    0xc207414103035510303880c2070b070112082e03071003a04003c0110201140200b14180f0203040c1842407032003a00e645456072915802002000003c0b650036070300c0f00b1501d078004406101d5030090340c5c216a02518003030505803503000401109509130402d1a4640c0842010040c2c9940f04c0501c0f940c3c4050480d01800c50309240f60340c011405400c2c080c44038044000595001098441e5000c030040300c1b000800c0e02d50040300ac20b00c1c1101c1402d003204125440c40c65440541a211001c003c40b800c880a00d400c20164a80801c10b12020740801020181c0c440b503034016101c041070216045101007000140001a920004036203503007010b92020627240103410600050201c140c10034043d40100032003101440c4a5904c0329000c03032400005801000325400c40c2c0f44005408030054204c0c20301c02c80703450004d1008080a80d0304a555000701603d60380180d0040000c940443e0103075002140310b82c0241c4220650f1605d58a0881c8190031802c80e89446400c4040000081c0343e15102d94000f4040c100e40e9903040309034a10074265500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 621229271 1250 621228021 621228031
    0x2010b13020309060f0c04090608100b04060b0a0c140a0b0f071d130f02190207050409080304021e0301050c040e07020601031511070c122003060c0c0a050f060702100212 74
    0x40803031701003100c001c202403e45008000c80541488080c2d00c41c02c030251500f4485014101c0e0300e003000d0707000ba117070b00d424001d003003d944080300c0040c10306665030300464220714985000d40ba004612900c880200c03078148442041d007801602e1290740c0381010480e20603a940020011010814802800da9040756005050a0304d00d00456402880143d90a0400010600088410f40b49480003d00746111030001e844101900b00303075020750b02019526420721080e01c10100c0020084002040014010301d0580d8062220105903040035481074040c0d40880d003102d800780c0702403400322000b1500308000c08c0d5140901e640100e00f44040c22a95146507142030900c2c2c54200f440507126115851480e02c5660340c0d080d00e00c00d5400c0780c0d05901040d0740d1b0150621085000800342d6020140500120740f2031a0a4039a01c0e03482d01c0900101000d80d940000e580407600f0a1650f100c06000d18481c4001145080112400c0d216043d8040c0c031ba1400e203068040d1070007c03102c0b0030450072401409001007207016040b145600c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 621230521 1250 621229271 621229291
    0x1902161b0e0c1c2703091505040803030615070c1e050d02030d08060111031209060c0a140a09030204090c05120a03050301050f1203220501050c06130309090c02010b1302030906 77
    0x142100f0800f01401034403040819650004e505042030501d13500080e1a4200c0c0c151046448400c035400408580e070744603501400c01180d100304003049040c1031184500300e04498071401281013266982e649605c1d2926544121201d01d0304484481106c100c8010080c01090112044201a5003503804682c9850224040710300b4422081c00040c2d80d40d0081c0c150a203006211001d89a450794500780d85a8940f4081c2c9030f1000fa072041d00b002403062030b003040031105441516103606280900d90189440d0a50011160500300105002c6c00801622140510502a807207418060b80341418842031140d4406001040101d035481041e420010a4010044905540e025562003000c8a5440086002184000d9044055120010b113021940704030b17034031190f4104100c0c01c00e044116902c200454580c00b505d41c2103103581d080032001c18281d048850425004500c0707800c0000802d580d8200c00e0040721220725090300940d45543e600e5901d440d00c0018918025040301e821403c40c14001c4515540e024014204481 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 621231771 1250 621230521 621230531
    0x30504020402040f1212020a030206040f0606181d12090f0301020415080403020f0303010303120509010b1302040e130c030b070309020d0309080d081902161b0e0c1c 72
    0x299111a011940548805004203404c1541c914070050101600320060b01c666104600012446202080107500382d50150300800c4103803181d0301c4d903500c0e4003902107003180c801d90303105000606101880354240c00c1c0040c0d070200003018107141e005000c4a9040c440f120340304d034018401040e034001007442030b240f03007200949400c1c03484d001d2003011a0084c0310399000905a500c101403100f910035130090086129920076420b981186815840c1c040e0380e40000c0c000217010580301c5051140441c40c43d48403c0d80100e0344030000c1090481c2d20007142e5584103041c42942429000207051004007041d41d00281c000c14851801841c85000303440341c2e8449842400001c1c000c151000200e00301034441c0c0c1003c03a8894006000607122225852302400406c2d50303100314409801072002c0b500b405400f0300e80c5c00744150111f0842050866200b045940294400c858005e401101e8100503c00310b00c00d9617149031024400c4400e02415803c01d64601030640c4020300cc200d1820f42004110840d01050814401c180085100410b03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 621233021 1250 621231771 621231773
    0x3070305092a01031509051006020303041a091c180b0315010810090e150106020610060e0d0b160305090319180305150406050a151406071202030903150f07030504 71
    0x1019003440d40c2030707200161748200003150b07115035a40910701807880139101c41490341d0344803000da840c2d00041700c000d00b40c2000d00c3c12540103400700501c03055003c90740030300b40d4100c072402000140c051304010400100250307070031400100c1c0600190b245005040c02c144040e0661a00360900c601034042c0946140c10080f5a070045280e803071123440c40c0f40c082c0c10603842c1444144010006036940e00444e03c42c0c900c1030260701c0e00004049001041c407900079118a00e801640d2801d0082c284d611041780e005250b0080042c04030fa002003200709444c01e010320260051040040c500c0340300203050b00c4010b00340070300e1900100a40d4510300d0040000f0015118a414402c2d6160600c59070484140303943c0c2d1001c2c00b81d003d00090700618410001c401c9108238418042006141c95040182040f600140b0000f40d00340c00001d0709200000d000390581da45030300002c0c955440d00d0070564946844c406104d04000c050307171000c06c902c4c00038602071000c0c1400441c00040000c1d68500000042100c02d0068101030500d40c0e901c002c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 621234271 1250 621233021 621233027
    0xa0e011b0b040f05031b0309010e06090d170f0d0f0e070f061b0f0b06010207170a17090a0816051504210203030c101407080f191103070305092a01 64
    0x1e080106c0c0007000f49000283c0c141e5162aa8044940140003c5414508240c00d24000341500c42e40440540f0700402c1080d95554902c50b842602c40301c0700140403d00048400346e000c00c001705034001d030b40c01010940c00303400d10080d001d680c8100c1c101030790b03500801003d00c82e00074002000e80c101d48041c0341c82500d611501d03c1540b109000860083d18804403002d408042c400088089070099501ba17080310401e940e41c610034043c004000e56103001e5600118164008128402c19040c0d094404d00350b40c91a055480c80040c001e020781e64003200c220307003043c600c15070f845034481c0d01d000060030305845007600d080001100c14140c2c0b09034010501000500194480240315840c0318400e07442d4050211780d6a0280c510701c680c1e44641401880b5141c505200c03040304440c0c806510305001e0300454941c0c00c8280c640c2103029036000c4005101e0b04080b401810210351540003030159404101410b22607640d0307400e05100003803d640d8000c0c403064003a03010786110307002559020b0b00e0343d040e1040e080e02c0c50310003100f0307500403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 621235521 1250 621234271 621234277
    0xf15091c15090b06030105010b1801050f211e060411071703180a020607080703110616030b030f06070807020a060f2f0904090807080a0e011b0b040f0503 67
    0xa00303060031040c414011034645a00502e0030a029a421808a0755407004240c281e5109000749942c82005000416000480c288840400141410294103104118001003100d81002c40d640c401d01c0790408903010a10700a410780ca800c90741c007006181400031540400501110050711803401142c0e103a60706007000e01c2c40070a42d50110740c000d40f0018048030311101c46619800a44c0c0715031201050b450035a2041e0b034005424105180e0180c40c450502030151140c0e502034015030700503021302c0800c1351415845c150500c06a072095180801e1300d2585440e006004003122016a4160700951001b0403198030002c00040b1240e1105c046c1c68020459950303518103e01340f0707580e2800103101d40d0414140c0310340c41d400c07500726071121842d4002068010500012942241c15107441d1156005420050074886041c075401c2405103500a000c0c00c1c0c03a1108560f00c1607415400064010000317070182d00e0704a15903070b00c8540c4c80c2108440c0811401c4a004070303119560102d2011740014114898030040c0f1042080900039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 621236771 1250 621235521 621235523
    0x307110d020f0915010f091a2a030a02070e060306060409060b030a05071a0715091a040605060a08010605031002070f1a16030501180b0d0816020f15091c 67
    0x460003d820882d0081c030500000089031404200d103d10945100d078854400c0000b103c00703162540c0c100c0d40207035000000d16480101d07103444441120400c00700304100d0b044400d040f001c0b4180115900e180401000b820a0080d802035208603040c081400303031595001882d079800c40c03400c640c0004e0b81880741c0341460040c655410710716014094420303101c00380b08000c40e40b201158100300c420762500400105207d2540709405009040703420114203d1a03401c03480c3d000c1d11031288113005913584003185038040366540c44115000c403a40d40d00e034410001d8900784880144000c0401c6402413240e1401d0000098940c0ca44000c1003c07480d5001c1102000c0c00410381411494075000310707000d0240703400d84091410842045a0340d500714002901a0280d2900c6032142c0c40c100d42401142e00000070308410000e02804080141c20b621804540a10020a1000000784180721010086812035001441440842010401c5651080110145072001d2002110440c0c841040484844940c94181070183d1102003088070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 621238021 1250 621236771 621236779
    0xb09010e1306050a0b0c0f15041b03060603080a1b0203030a030b21030301060f05070317060d06060b03070f030522020a031e060b0d030f050307020f121306020307110d020f 75
    0x150024000d550170004129862014017510403800b0030b0700615507a2640903084070480000c01c40040c01042c82c140703c00c100406120f401d05c43c43c503660b44942042d2520b41c0c001b070310101400940300c2d0900e500400850226440100c1800400006800080d01c074041c060b0710310241a00c1e40c908240340e0b512a195449040703044000e0040081c6680c4902d5a03a40090040d0004503056007003a140090150060710340680c1d2584c0c43c0c00080d0a259184a41000301424054010081d02c0203c00010054021000501b420709030b940c0e00c900c0c0180c0002e0039481180c00c4142498580700c2803003115580001c401241c114600740c075082c18002d07031021a00d01a141e50000c1c043c100a8a22030800c24011000440200c3c020b400502000580c4800c02405000540e03000740410703004080c0400c058092800313140c0c004002e0042e150340c8142100c4150421300ca8180c543c03003140c400510300c1200d01140c4c0090000e894a03100442c14102680d942140750039501001c00d100d0030903450408215170b103403081d0300d030030340000340c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 621239271 1250 621238021 621238039
    0x50c0109050601060807051329160309051215040c1e050a0b030c0a0f0306050d0317331302040e1005030d020a0209061c080a090b09010e130605 63
    0x1c00d203651101030a024580000d0305042c0402c3e5450710550949070410070650b0782c03c90705840c21020044150140415458641e007440700e0400f1144040e026207804203e91580e4951302c100b51070020521240c58101d90700c9440b40342480390122030f000840351100041040c12001548035810a41c01201d06980b040c02451a0f0602c5841003902404c0f0610450740705941024020b91034080b1000180000c44654040c1c0740140100610144100c1d58410101c0d024240062003584901c00b040c1c91515646041e4081965130b00104203810f420b41c07116500008051140b0402c1c0e850340340c0001e0b10940c00c00c0700070740003400005041141c0e0741d107012107420300074540003155219030b2070f1200080386a04880341021292001c40006590501181500c46424641d015260007149503007007002420020b001c00e0307007200c02001c501c20032040c601080220350340a943c00700e8039502401d60081c15090282c01003401c0f14024400400d450740c00401c140303550b00e01210300766600145a003144006025680c01140d03c0210320b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 621240521 1250 621239271 621239273
    0xa050105010b04060f03020f03041e05062403011a19260d03063005030301060503061c1101030c02011e0f0c0201140402150d1401090b030f0d0e01050c0109 68
    0x580b0041c8110f51346a15041100250084280e0880c05560301c140340c0400200f000600041d0341c8040700e268203848110081d00800f054603910302e044021100c12184100301c1040d07040030010340403001c0082d88114024443c80b035401c5000c0c1420045d42220900a40103030150b10409110b410100c0d001c0d080e041c42c4a04403044c40800c401ea506007024071070407280071b0984000c04061180c01801c0c1582c40440c003c400346400c0e0780c12502d50880307001d0200554500c02610000090f4148001d500900c102d583c2c29840c4d0800078200182074142c03861811a0340c130700d20045c0d00040d494520340d840c1d9110908001982c103d20340402d0707000d0710003241002001e42c1d04031003c001400540d0b10800c5050050981000456600b14069013280e00300e160003505800345200250051902c89008011089002c0d145410800040c2d00c1800351640d07201d043c002d00d0848001800302034064403030180d0140081300108a8100c0d6220314a0701d60344804400300412030b11640300000da074001c2d0201c5611101c030500030081c030082 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 621241771 1250 621240521 621240539
    0x1203070b040201120507080c130915050103050121020f010c060509060106080a1e020708040506030a091106180906031e010911010f050409090302070504022d0a020304170a05010501 79
    0xc100e800703d002c140a940f07601c543c20703442d01c105842400c0d10385910039a5101c002e9400c7c2d0035044a60041381d003002040010429040c9802a141150350606419104901303080c009415100141c10941c4907507102c0010443c1c4445020410001c0e9030162400d0b2141080040100c030741c0d003280741e000f810150404051001c01d0364002005c6048940310f540d2102161a415150340644490b05011140844903251450016176243d00410041c2d102d2404203192580e134402144554000303c440103245590b50740d07150140702d600f442c1001d86840c01c84407030340303003220184030340800361038038120346018841320b400083c0305e9202000300748061001040c04030f400c811244103550103000c0e50f00d8111040f007008018450154084c0d107034680c40f10202d0300c80740d003424240b0084074010316001e00180c04512550341d00050a80b610b100800c14403090102202140100c02421404660048040c0b81810800c0000300803c82c1c0c003000b52002e83e240d80d00346500c403401d405002d038079040d11030901074055440c0000004800c14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 621243021 1250 621241771 621241793
    0x50405120f06090f070302010806030f0d23030c03010303120b031015090501080d0521040c031a0f060d0201050d020f04050a0807031a1f030c0609050a051c02120307 72
    0x400000c0b40d500d551109582511400f4254030742005a0200304280019070203070140d40c0d44502d010301110103481002c01c4803480d00140e000f509010a41d00d4004444c002c004e098100b03040200c1c800c1c1c56285003041d0b4621101f07403105102c058208214000e1000d407500540d08112400340000301119a4242c1c07241d2200024001c5940010720342d50005d0001540754a54000c2a040b250f401025042076040040151125070150040c4851810226020142c1030800011103004a00444101c1e9186085143c0804030b07003049241602013080240c2040525403102e103d683c1d010809403070f0f0040f540180d1005071a18014600c2c240036103400480c0c000301c00c070386110181c012030380304480440144c1d554070016510744860b4080502540c0c52254560f140020b0b501d60250081002e900c2c1800210090b50034080344040c9800c100c42519041c40c003044803a51141da810090316003180d6400240e0310b0800042e502c8420076103465541340e0a00d03800c0b410b65892045464000300d040094035aa030043c0d15041001039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 621244271 1250 621243021 621243043
    0x303140702060126030306010f091205030a270303051e030c0309010c08040b060d030e0d140c0102010c0207050904110a0b0301030507170c01081b1315050c071505040512 74
    0x4d4a01040c2d140c40004003040d00c075165074a902540c0703543c503098011103a0044170350140050061a0000051007620740307110360305960245c17001d1622060413100c002d1203101c45408080c403151501c1108042003481c80c2500c82101e40c1418910303500c410b50200015601ca90380fa0615079110088200410402c4a100031481078486130000c000c101c0c5001400d440a03441034070003504440a10000841c903003403e0b100d901d5007138000d0800c000218041d60006440014cc40401c03a851030381044041c40c611000c01c081600740703100b40000e001850a20000035540d82030741c4200c1741f24280c3c0e10042418049055255000984040c00d001e0240307494001c0305003580c0c0280700031030b4030744240b81d40003444001c0804440e615501000141c000021900011070382140050080070548070420f5002a020016100501080b80700600880c025480d00c52294080710002d11800d0a2007000c018800030a10040360032070554101d11071003030f4110810502196075000d5504840d41144a17082822031440c000102c0600d64 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 621245521 1250 621244271 621244289
    0x40603022a060a050402190602100509011b05180a030c060f031a0f2b061b0c1709100519090302130e0a080403030c03020d0305010b090d03031407020601 67
    0xd41c110151008108a006050000364105801007800c10403030b5044039801c00d0001303144448800c0036240031500001d90b030b440307038003d0307840803000c10380d002c000c2d01480c2d500c620a03100070008c003120a051402100c401000ca013081103000203814002d55911003107058004000792403000042d480e80740ca90900b48640c001c1c03002280102d043d12001d544280074000d400c142080c5441d003500170090901441d12166040e180c0d1241c0c40040c0e829040180011843c5d001c1100241401354142c981821001c440c2240c000b070100d12010140c2104264114001403551980f1054040601941038050f020b2800b0716910154800015a0030f542200d512030043c0110f07a40c000100e042480b038285058401c10900e100094200a2800750b041603480640d12041c80c00d1802e07004c0d50b000401507078480c940d550054100314045000c1070002814181d04002e000300c081e41c0c41c20104242d505200301c06125000e030030100340c8a5501e012003501014440e400c40c401c0300309003107081c0d01c035402e180d0300c043d44a01003400345002c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 621246771 1250 621245521 621245557
    0xc0a050a141f090f02150d0b04090b18070e07090303030c0e030c0603060d021201021207051c0902060708070b070e01180b250602030403080a0207030e010e12010204060302 75
    0x507168007150b0480c40b85003011441c00302c0c1d004002e20b00042c22030040252500c5036403081d000c3c0075072070b4000c40140c0c01c02c45014003581c855140640c5401c44821141d0940240d107030400b0600003502030b060050b082140d0101c0303241044032007000d89280103040c0d0010801a54050305020201340c20801c001c0540e4403a4500f844001d0302103408580e4880031031012036059102040501b85070078040002d40d0810406000814407103a03d4004c03034400000522800c9003a98001381d103200417400c06101c01d40040030303458030a00e49800110f8941d00844c05603c1100f155a403920480c0440d0788400c00c072400f050380440859100c80007030030110341820080740d4104c0454004084e0052542c031074120101d0154841410020f00344c03c155a1000d190040d4a00000c403485100580c040f13540b92401070100d6910808003d0707a40c0c9001c0c50020100c0300041c00c9004050300600107003000941210404001c40802e190060003000307503400142910340007020121055200141c0400e5150b4160010080c50210100940c0c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 621248021 1250 621246771 621246803
    0x30f0c0f0f250206090d140f0a0c090c08041209170d1413140d02040905062a070b070c0b070906020c0d0b0106080702010e063909040b060c0a050a 64
    0x2005100902d0020350101c1d00b00304003807207480d0042c4039048050080a01c00791500b42404076a14042814104a446a02c02d400a00c100002c0b40694005000c03401000d02000f040ea04000d030050001400c001c050810360b0401c1a0b1031445421410020500256a00b2440c61035202464940000500010005609070540c001021100c400c82d1002034100c50360001d103030718003000c032450709040b0031240303034481050160703c00942d0f03d500035440c0c01405400685860704112000c521801500b200d1085580465480131a001c00f45a00781d541e540d4004081c04141d41d180c02d4102d410700e140040051000b40b4490034010711a90010070441564042d408440072040c4c010200048101c12200041600ca070420044c00620321440000750440030a00001c14251808104070b42062070854182c5400c069800d040c1100003110712500d00c4a50b00710700481c19242034009042440d1003403101c001d0003152500d50b01007082d1182001c9852025408060350200100c1d8545542c6038040941c00340d0307100500342d10041c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 621249271 1250 621248021 621248077
    0x3010b0714030403110418122006090625120506220b030f011a2404060518060703022e0608070305010b06041d130819030e030a05030f0c0f0f 62
    0x7c0300c80e8216144c540383c5000b00104881254409035540c100f403124200e01910000c00300076480c096890007004d054140341900300180340003110039200e0f000003c6050f28050140e0001100803450a0040c40403455903500b10200d41107018803611030184041443d4044100e000e55480003040d0b0604905030b07128040140411800d0ba000c2c1c1c21501c9000a5403c1c0100c450301c1d00d00c840600341748505568091500540306000364580103544508041200003c1c8020000ba10508071071400004607a5603080090a80b802585c030007000c2e0043d02da880c000581e0441200340b100266032801c640076002d00c10907403605c50060326003041c1e1000301ea066003028030010040c40c02800b030b54182c1d102c001c88091401d24583d14581312050180500504403c115540c2c00030554a0b0000c120f81462528050414260000024103d07046c4844d811001e410a00516002d1540207003201c1d00128615043e00203900e800d503603610540304403201c1e840d042d000002e240d80a2a0240302404103c581205071110540094040b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 621250521 1250 621249271 621249311
    0x111009060806060901031d102019020309045a0209130519020408030a0c0c0f1503201b012c120c0303010b07140304031104 54
    0x1000104002074000303000c5042c090042d01c50840145000b25851035189034110f400d00d480d000c80c3d6056001503541490488090055000185c0040c02001e8013208580361030b1028014940303001d404c0c0c2008860160b0103482007068034019a80240304000c0404016904030001d0b10a00b007140d044c1502d01612280080c03400130415441c40c000e0144e50500040d40100c20942c01201d400411f807650074494080141c54211149000080a0340c0016590600e004005071410100c00c0403480d181c0100800d210803800403007506c0950f861420a601030702c445141841e18001c580d080800d84000700c18001503462542ca1206240381c080340c40c208a18090722581c0d018481d02c0c02d88128010004004641040700a440003c0480782250700016080d500040440c242510102845458840701d50f00d0a81c0070809001080f01c0da460000c4841c54104000e00385c81d180d0105114a018a0101040c51414010ba4181c0c202606405100360795035141c9902d009040492018140c0b40101d1505d000290141c41071408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 621251771 1250 621250521 621250529
    0x80d0e0d081c06030f0b0603060a1a1207050d03032901020c0609041407020606030f03030103020f010c02030a06020a0f030c050a09031506080307052401140402031e04111009 76
    0x300078501030b02c040721081580c02c03900c21a0301280c1c3e01c100c00004130b2012002606a288510104075003030408004051074004007a0011414914150509500f03402d000d0150719201c600303039490381084840045d0b440c2041d0035517000c40d0300103d810b00e04004060340f5071300c903031804080c040901000411401c4240341c02000602c0ca14056400014001e40910742240540b455000040c004204080c0310211404450030035211000540c0c000d006000b03131840c0c107011070315500010000030740c111761554002031380c101c2400c05011f0601280000325029500e00740107075080c480c0c004200307659542d50b10b10014400c01410010f0030000c1e15103070002110030f01c5a0101d0b802820150f5030070340300c20b080d6220301c0c00214120402e58178150350340d00000303100f0f0014409042c1d10ba01403c040d01098024194100019850307041529410801c000140940e640416403034032101d409840040c1c980d580c000030300b0f46011a100354070000502e000b00f0002040704000300c0d806400700c00e07590591204021001a550b00a56001f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 621253021 1250 621251771 621251783
    0x30703050a08062d03060a0207080409051f060f02060601090e06042414041406010503130f0f08071202010608030412051507050c0607140702011b0b01080d0e0d 70
    0x1a04800380b149100310b070420801001100e42844090b0010a0ba40f001d00b006103103089a11075440242c41c040c4004da510140c030303000551406080d650390440510481c091094416500c0d40803504480340b1030303044040300d240e98400b044c0c1a6124603020b010440e9041104005109080000394254403641c0210221400906041c620b074071703040d08000141c4800c025180003040030312038401481a00c0440030b80200280c116540e461240340d02400103450540030101400d00d01d5009002040e40d102048030350000701c1850108000d03a2a140000d0a0000184068101c0052019000070f00131460014101c0e80d10071840400042406501682a20568031591865030020300081200500c0501c00c400300a10560030f840c11008001da20144c7d95506503540000a0030200c3e040c6858402080026001a901d09001600c812031103408842031040400081c10004c0c40868122a4903002d1100800345038400400c80306503848030500c1d580c84245c03113002c02c005015008075140341d0504190402645800007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 621254271 1250 621253021 621253027
    0x301030c140a0909410a021810090906020d0c020610060507020102120c0105220c050d06021e0306030709050906070c080f041404050c0306090103110109050315040b0903070305 77
    0x1c0300c2003008040844080d00e140020103661820642012800300d0b0b00900c0e503094145ca400074015500d01304050041807a0181c0c005103da0000da61903807a10344030f030a822444105283d0f41c007101e020003a002c076400740ca401418000e035002000342e00c0d009401108048103080000c000d5403142240d55801c2942c0421036a20703140c00038030840340305400918910340180102da0b104998211001d0180d40400c1421b203050b591a81808080403000784101400020701018091016454a031400004032074031560784074407102c00c00202000516010348000d00803003102c00305a903220800e0032060350b00403900144680102c0c100030401141611800d030003028030300001c201550321141e05649418514500b503070201001c1c01125404011b1000a1014015505a01480640303500500c01501d0014003c07030040742c0700f4000c1101649500c5d40b03860441e60464441c400c96200b20f0010ba4038140c203508165014018069002d00f80d03020307082c0c4540500d1103041c0d440a1035a46460140e1240a0320100038000b070020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 621255521 1250 621254271 621254279
    0x305070813032609010506030606030304141306091505190b07120908190606060e130c0e0406140a0911181804030f090b031009050408070c0b0301030c140a 68
    0x40c080f100c4560000307981e0004000c0710042c5003030300b0402100c5010280c0e44403020081079080c240320705074000348180d004605180c180050580310210282c11036000d00d0906c0362002ca0350708280c20480091100071030400c902404103e841000f084c6c0b900440c5d0083c8184482122040c1d500046007045420b5402c10b1f60809159550740401d122015100b40108003c10001203201d003424031414955003800d82401110038210b14004007550842e0380103800380300d6112402881600e901c0c0b8021a560781e45840010450300c08442038034541d40d400d8003d5002460200045564540341c0e580754101039044840890150ba00d403180000c0d034802024040380d6100500ca8807071011103c003180984600024928603002904001450024030100c509900050350003500010241c0c002c0a084c02801da280440342c554501300507121510001031203000c0c041aa1a0009070070302c808c44c03040c0d6107030030b41c0101305803007080da5502441c120b0b40080c0026a03008144c000c0000308903112030b181c42c000c400080c02d40f41c0f1591078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 621256771 1250 621255521 621255527
    0x30f05011a0d200a080f0a051311040f05070c03090f03050d08092b170402100c03030b120304030308090705131a190f050d080d0506060712080601030507081303 70
    0x849001d9007000001e00740e0002031010843e0140400540c00c1da01e000403850205041da00480000d44003400312842c0005002d030310700e0140800c2c40d006401080300b60a000d6480301041c0289207400400c40c0e0549424240401c440e40201801041802565407150007911800145540b4189110042459214a0310242210b000c0c0f80030b10b41c0202c4030720641e10710110996030790a1100e201e44030003840d84410703590090040d0704001c0d080020400d400301c154880c6055400b040e0880f0318514500f06100002c85c41394201072003074101d02d1690f40d000e00000c2c86c0b94102d44686c2c0c0e580e00180401c41c01710742d124000543c4080001030042c01c941e4000c041220408105200000412861100041180580c095284c0e030392101720103a90101d14040c000500035103081030400c1041440c3d000701d8440c1c0700880400c800f02d60a1030582c0d1105001c508002107a0300c0b040d00050305403140d040020141d0301040510041e10750040703a0300303118540c01e88081c800c59a94400858024400701c5800750402c60002e005000310344 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 621258021 1250 621256771 621256781
    0x11506032906160309030309080f0706110f1b0111030a0219080f1303020f01030c080a150f0e0f01140d030c0305040b0f0306101701060813020a0303030f05011a0d 71
    0x3018040e40c3c0b43c8030309605a0215900d01680990100d08191800c1042542c840340c0368008000440207001060b82c0255090b480304000c1c4981001c025070700d08004144141400008002c40c1c02c0800c0303a1400e4900c890025a000d2003800260200b40030010f80c5140360341c08030494140109960140c01014061503180610a0340840300796825041481500c4400d01420010b00c121200c201e0039180041c5940304203c206440480010704150800005c020721039081202e140e005092413801048525000040403a511800d074024003110010701000601882c4501119000c0c0d071700c8420010807aa00c50717004086040c1e003010056004195120782c1008030748038103148240c0c141300e454800e14069540813685c0e202d401c01400c0302000600081440030600e000d08000c0001c28290801e40b400c180344ca100b0212400c814440d203000d00402c140000e80101003005070741440740e0f004116440b83c030f8a81c24002d0090030929400100f540c0b5100011a580d2020703860700417480607580310303207280c000303000d01c41c00c0542 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 621259271 1250 621258021 621258101
    0x1020a021203071707031b02120703030902040902061908010f05010905100215010902041d01140d062c0c0901050603010b0a021614130506060f0c0f0d0201150603 71
    0x5802e410002c07400c103003003001a005285c2c51b039021550b0b844d12960180e800150b00181e500750b40c000c1c40c40d11980d80382e8a094500b8170340c05040000d507140c520f0021034058400420029070261000440c03c000d241d0072002201030700c190365030f014980d80e00d9414110011889004003030108041349801c105a10b807284c412412000752344151860061740c4210a0018142a00002c1d01e054012800b840300880a000105a241c400d24240c002035242240d00c00075400030a017518003500390003411205006664000c0000e403134809039065100c043e406400840e003000b10903400528007031400c0d281020719000d091107050b110020680352842e480c141c1120865404810350000b035008074142c1306101110000a04020a5044090b185101c1d0080c100036824444c0404404800d10300000d0240c2500c2d20400e5460441014004583d20100c3e652094540380030309480ea242e500c1001c0403128015410340190051500d00c51001d11000e80b0f503203080e802d482c10042d010b40300c44803500d841c0201c0549008041102 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 621260521 1250 621259271 621259277
    0x120b0a091205090102280609051204090b132d09021906030605090405070902090411031302030105060f0d0f020607020904060501050102070b04030b0f07050405061303050105060301020a02120307 85
    0x802041e651510042070700055240411404103020009503014005290403581e044050020f1400035490300080f0324510714090b101c03503603508540c420804c1c1040311600d140410ba1035a6140c56031440003401400b80d1b080054081c681f07005840040c800180103000801c2403041015000c2d8013061380d0a140080c6421013081032030b48070b40301d407400350f12144842c110000c844005500c2039420414041d0a0783c1459201e640101131240410001c6680495030130140e544441c0c025949010354000034015012415407000d15440000c00d115a00b44140d8aa5039000e109a0003440b06a03244010000b0800548140b5604001c0d0081440c0028042c00c0c100900188018511414a0450380120382200c3d422a000c0300c00507a104018416580c0400200004001820a01749801d040d640c0300c204415018009042c25108040407500140c001e0082d0350103064054095a12107522083e0880741300d50510041c1c4c0c01e54642030118500c1d04060007200c2c116060350300140f040000c3d8414041243d803000b0240300070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 621261771 1250 621260521 621260531
    0x503030f25021509060105090129031302040b0f0604050d0623011703030112080c100f0209011409060318010e012901031407030e0f06040501140a06120b0a 68
    0x111102211641c010790440d401402d0841c8685540c1040d8500a460180707254880c0004011941e149420b013415511040411807440a4030110910381c4400070076181ca403250080304100d4540003640c0501003150085805104480d44d01041c0104c2e40041c04949070400320811050141d411703c6601001c0b03c1c0d20900300000c40b44401d02c403070144a0b50704400c520189090341d0040001e00d01604854590038040c4e8040c40c81c65140c0744907800e40c114280ca000307100a80201c0c15101c80c1d0018072010010783c02d03100061103442c0c04119040b0095104c2d1890901042200c80041c2c138000340c2c2d4003070f07441609024180e6031458031a1404660507402103034014071290340b24208040018030078040c0307102c0342c04c0241301e500c003162400d0000e4480c164442200c6040614242c0c0e1401c0350140124480c0d01b0462a0a0024403812494849410081c41c85042441072003101d0038001040300c158810714541c0341d56144500d150b107820302e61710207440710392140c0d80c0910388045c1d112012941d9900c00d550480703030010f40014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 621263021 1250 621261771 621261811
    0x90409030e04020403060e070806130303180c24030e03070807051f0606030b0409030909050601020f0703081b0d050306091005030a0c1a070308040b0403031e0609060609030503030f 79
    0x380d900c15042218071ba900c45054820491040120b50040d0960202601d820700c7c0c40307820004104242c140180c03c03d5154003880c0d4180305100c0b01148a41c0d0001c02e08208d1617122955880ea0b2609920100100c21904002c10607103071003441234501d804091000340d450420035881e0410b41342c10540042c0da0a00550f41094050310300c0400c00300125465040101325180f030460064200e030002422103001d1414100680f00196000308820300b59030103003000090503126100109c0c908602d00d5103200e007a1042107400b00030b112401c0013914884881808001030039850100003038892107c02d1520b00400c2e014004a20146001ca803c0c030380c45880c8500030404d550703861000a282c2000000140d94500c43e00d1000d1007040720720400c8012030001d580a1528041c0195030081000794000c1016006543e51408502058820b0300002c03a59800004105000030030003c0c030000800d0544240110305d482c0c0400050b0040c0588848003c4030382090107981141d817104101c003018440100040c0c20901c01401c0c180c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 621264271 1250 621263021 621263029
    0xf0312031b0909060e010b0d050403030e03070f11030c03060f0606070c06030b1e1e06090405010f080d08040c0b0a030b03060c041409090a150b041d150705090409030e 73
    0x29a0701005030b44041d0440d1030328107010115440798120303648003410074006010780c40e162003c5820f04000b40c900080ca5036100d007401c6004001e440c3c480307040d6010016a907001c1c03101089412406a0081410812001111081556030401401c0e1150582c00100c0024050980300b032940703038001030140c1043c2c0344c003040d0ba503825050303001e0780c0255001c41e0791822100c0d1360b41000c14200c14150190202e00344405080b4002030210340c1c0b410034449050055220006160300c94406540d219a000362051003196100c69400360300300182e0140b00c405110321506240c4440c481c1005c58040c40c0c002804812850401c0c026070105d038405424001450349039882440d994800f080110b06c240f507041d02c519113481c100f07487c0085c041100c5100b41c0c4210400e0b003e00202500114841040da64001001c500c0605200d01a01c0607203158003500b603009242030380304113680ca05141d4640780c204c0320b8000e81d402e5001c072001418814400fa641100020342c28401900c081c141a8000d14001e8024240748440394600b40002d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 621265521 1250 621264271 621264311
    0xc060a032309190512042c07020c06070c030c080a020123030109090305070b0901050907080304031a07180e06041b170907030b01080a030e0105040e041709030d20070f031203 76
    0x3d228000200021400b00300d0b55581000c0005403047c10310301907424610310081d50b0340501d40b1228400d10000990400300003070710420300300650340304100080d4240c1d01c0c2c1d0546d0f151044050107a000c605840402051510010a09246080c0c61441075082d0390030f00d00b0f804000d040c241c07021014840100801c0c00424080341d0b10740d101e07075000d00002c034040c6400d40b03400741003503281e9000c0141c0703074418801480002c5000e03801c5852803801c1e0141d80d0059071078082c102c812100000e82c11490614204c004113010140d030140900c41c000503201402038095007403412202034405c40040d80001c05043c082c030b42c620105012a0b40044582084034026134480c4c8400e05200ba0a0b404180c441d4010345582007016009000e0044001d000d0030900d0078107151004200d140c0d0002400240b02d000c000d603510030484191001e071342c82d480c805001c440301c8010340340c009800b01c3c00840004407105a4504500713043e01340018440280d0b10b00c4600d035418249140c0e10800206111410441819181c01c0f10780c59903c0c00310300c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 621266771 1250 621265521 621265529
    0x1005060118180f05041101020f031303080d2003090c0619030b0619110609030a022107080d050a0608030a1709030d050403091503060e0114030c060a03230919051204 72
    0x80c61b008001c0400191500740ca42c42030306011b401c1031201d2124076101c000c840b011030b60400f0342d0a5a40c1103003002c60008202c80c1c48040015900080a90010100040a140f00d201104100c41340c1c08803a5040090f180222240340590384e4000c0000740c0190b100c1c0e048103030149800ba0200341000054402030880c00c4030800407800003001c01c1c200c00d900132410040c0c0d58004060402651909500c0c01e4025150301210300c0c80f01c20314101d50780e00805455001d04031a81240c00403507107921030701c080111030050481503e07038032141d0b4109040401e501e90701104075420104292910400d070b143c80d2080c111048001002945140000d0242594280c114040c59103d140f04e5510040280e091402041c6440601c2c6c00c850300f091328040050100c1d152001075241901c66a8900491014281000900c0c0182003498a60011300c00f00303540d20a0354150f00007900b01e01901029a43c2e400314000b01c0a84050211100c1885a01c0b964804501c0b411410700344207000e000320107442c07807080c00c900d1050541c2d02c103504c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 621268021 1250 621266771 621266783
    0x512120f0a0e0d0503070311030708120601110f0d1b1b0303020609060112081b15180102071511130e0403080901051003060f0b0a081005060118180f0504 67
    0x2603808880c90740442c81e500e6581d41112407030080d610316101c16036a802002d000600740010203420030a200c07410000d0340c061550043c184c954070a8517021410110350150f81650105908001d00041c045000c10000c03a507651850041c584000c0481c802c40300184c07140541b400303c00d000c3d080c01010411806c500c0080c4187d00ca040b4541c10302c3d500c0d0007403410200411000c802d40001c40140050001904141881038201c1072880d01c9070048030798404410301c0d11010701c42610074400c5c4030201ca101040003901c50b940140d020702d000e10784046101c1c04c0c0d10a0990081c0341d09641c40c3d5407076a0321070f03ea01c001e04446441c10110304018014111011450081d04180d8524965108010030140c0c0b0051f00740d0b22031040c400920860034103416422400300580401001181c43d03010510000e2141d60140400030320091440c03000c2e51743d0314082c98683c020b20360170011503814000010f1040d4014201a6041d114213070101c5079061030003401544480101e00368042c0c01d921801d5102e00c8080318001c850007107003d03036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 621269271 1250 621268021 621268027
    0x516141507230306060904090606081204031a0a061a0d0506100e04090201030b040c091e050102030a0318080a051306020615090604090b01030c0906060504050a0512120f 74
    0x1901804004100405110402600c5184003980801c82c0c0d90164070429401809501c9403107000014000e03000740c1e05880d0b007103890603040a0612107250041800c440b00c80d402d480c4000c400c2c0d80d5600c940d2189000c081c0000000400c048000e1b4401e41d5815405244100002880c54031020f04946150032810080a409c50208400c800341c240c0f403180740c1c0c04c910b04072041070271984030590248c0000310580a40d40320b140e40c0e000c01002d6902a421019414900910800c0b810800300e20281c454509800740241102800d02000c0994168440107015100c0580040d0b090043c0504128094444000815040c2413219000c50001785210050701440c0c1150301e80c50303100d22003103408100070350283d03000c0c0046600030350078031884052540040c0080b840c00c0e50f20118560301c0b1404a4013030245103400a10b404111400001032203841141503060383c061000c2809916136034081100c00d1b028501840e40e000e58001e03410815440c2c4016449504401c18090315410718104010b40d070a50000c040002c0482400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 621270521 1250 621269271 621269293
    0x2030f0d0908161202010509040f05090709052d0702010603120e0f09040b1f231806090a0207150912022a04110409020304061512050607051614 63
    0x40c0100300380e022140c07952051181c50890713210000d50540380060305000c0d0009100c01c0320f4940d030b0003190031049140424815410940ca00a07070381e48603413090980f0f0fa0700c2e08010807001441040c0210100c540304242c04045c411b15848110700d90b6001e0300d80b00641d903a440d400400100b4200c002050100c0b151039601117120094107009903204030a941501c035401842c03c00000034035541001d50440c5c00124030541c2e500712082d14403841c149940003441d42c810400d08502f2060150030b01d948100794180d954050600e4403c0d042e1566900540c1c115074082d0311301c000103907642c00584c00f9143c0380d40a650f10484992020220724119190120700380e4610b40490b02402d5081c0c1c0400010a4000880b1072a0700c080382151010606a803000a19a1140e41c66a182c040a20200810349000e030808a00455a80c1410700c0c1c050300914080e150301c1000c02c0502c000050785007404220411a0350818044e04541d6506101140c00760b02c050084800305c0b078101c03010380200d5140601c1c82d018100d6403004081c120a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 621271771 1250 621270521 621270523
    0x90319121a010f02010e1002130314010f06050a03080304020904080d0e0604120e0d15090203030a09090c1e0e190314011b050d0b0a090f0207020f0102030309150402030f0d0908 77
    0x94041c0f003019a81481c415013020f4400181e001ba01040d10940180c58490b09000b4050042d419400a4010096022020400300c0190f02200d140f440c1e0440070000e0581e100c00348840c02c00244400380c618081440010094240010a80d500501c50a012440d162589089000b1640d10844245003680400104420040f500d21020a25809400c1c0740c0c03540211640012448448a0f07070080004c9038811101c0083d482d6070300034440c1c0300da006055270340305c802c0340c14010709200c1648909010b0302d0808101070722490080d00e1140300303075890b80071030640008100b01c00e80f0044401e501c0e81e40c206840a2800f88000004840c000103184940016001140d0b51300a00b800d4800c40d005101070041081c075042201ca0b00700c0300320b4010000c5c0050210341d000303510001804c00c0900740e01070500c03181081d43c0a00c4c86000c560040010300e01c21034a110882d01c0013001217a82e40130464448840e40d004112041c0d400c110302c11156482031009040351520200d2489140c10440780c5c491103004071728034007018030200740 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 621273021 1250 621271771 621271787
    0xa020d1e0c0225180e061807060c021320030702010b130b0108040b0a0b1f03050f0103030806041a2e05070206030a0c02030702191508090319121a01 65
    0x400e0402445040d044450444101000da11542c0d600c44020300c29402c0716400364201200d903100010646d40d051510468221110704c1d61116044940101c110104116004d503c032030f800070b5005020b800c40c451002c1e408800404c5211840c0301d40b45418410441c06050340401540316818a40c000f03c0c1105d180c0781841401e20081101d400518240500780343d140c2d900a01055106401c410100100c1c0c461014840041038424a5181c0001074404000d0f500c0c009821a5501091079550400c2280d40381d40450494501c2800001c4c00652000302280c0586010340125101400d440c10903851040f05074005000340140303450058001d803019070b401d2000202c0841c6451034401c1414110314241c40c541c0000e0309072200800716a8080c1d618032103100d03164801c1081d07800b0258050072101d4181034104903007920048512850841010020901c50028071608810340100d440c1d4000750701300501c5080d03049103c20222000390030000301966051515403e03008012307001d01c1902904001640d22000100002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 621274271 1250 621273021 621273043
    0x10212010f170a05031e04090903020610080303070206060f0415142403160c1401050a15081902063a0504050d030504110a08101a01080a020d1e0c02 65
    0x2421000010010904c084106c2c1c9104c0c000800c0d4405a00010003204d41c0382c0a1038005140f01032816001d9002c040d000100b0030701401500d15001840c50755500f44913640d210444103100140c00c03000110f941424191036802940b80b0003400410000000108c0c0201405a503000e03044425420a01000c42e007040814202e60f200351110440a0032051000c0d40700902c17020b070112444003108404441903c3c828610754004990000080410440d500c1410340a0700c416611400c059180803140c140d4440300d001d159080303c410718090203801280e00280030051007200c00a9800001c00c00c00d04042c0c00b103464080c0110340c4038140703007100c0301d0703060325007070943c82808042c0f8040618203014070011501c0001d19000d81a0b044c90045041e0b40c2c2c1303181c0014041003000001741c011071100e4010410a5021500300b800200304401004400c81d60030404000c2c0c4408860240031582c1c0e8008140d903005a40c00134443c5401011011910070740091101c4010b40c24200c10a01040d0f40b428196039059051200001c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 621275521 1250 621274271 621274273
    0x4060501080106140c071703180103051317090901150e01020c01050301150215090a050c0901151d0a2417150d05030706050f010e041109040203010212010f17 69
    0x82d40c104039000c0e01100c41d64061102507080401c0300c4081a904001c054090201d001482c0100d0700385190b0355589030032030850210100c000c0c80014050303510030300c074581c8a80c5150803103815400c0c417038440c1040010035585d80e40e20980100000e60040e02c505080394002c045030420044802e040c1000244114a88100e050464000c0c07000f030b05050380d00000703990559035903903910000c045803402c0691905030000d03003910100c5403980400003018800b00d4050a518021410b50325400002d5080092032002406000243c045d14400b05926a02c12800c08145000e08030000d4000203211000550340c19a560042d014800c0c5e1003070410f145001000c034400078900c64140b0724003103c0400d02c0a80c4010340108030300517282002034036820b6039a030740c04c0020b501600242501d075151400d09010026100c202e401c9443c030003080f40001020f20300b0304a050310603a080160f415010ba8078038100054840040d005990564080c03040c0500441d03500d0900d8020010f00c51401c0c000e91400001c25010781d031808414000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 621276771 1250 621275521 621275537
    0x30c0e041709060f09030114010b03090c04091a06030a0b0112060b01030905100e0a0807120305090d0e0915130e07091a090a02040b04090207020f0f030c01230a0c0204060501 76
    0x50703242d00c0282c61050f20f40458094680b17204a01003401450000c0422402810000c00000c0102c40c41303000f10b0148003003409807002050740d03105000039074805160003460000742283c01e0100f1481401c2c02d94200703d00400b503440402c2e4546444402103c02e8024a0070003604841c81410031100d8803418801c0c08080c20240b0013803903140c4907107840d030000e240c000c1c080c1c944482000706642800e00503010510340c80012661102c40381d080c860031400c0780041480200b4504804505003680c0043d426803800308543c0d07070801901d030903c148101c107030303026105011441100520000b40d030fa07950141c0f03051444140000581d01c036480e945500d040c460350b0200c0c03400351030554075100180340741c1e41d0340e42d800d501030303c000d20141c0314600800001d10039580291404c910103c0d001c07a84402035002021007a000720744618609002c0383c10030007600045680703c1e0b4168000100510710394092154031903c1400c08040b081080104598030095038800e40c071007400038030000040821843c0510030b40300500401e19103c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 621278021 1250 621276771 621276787
    0x31a070e01080f09070b0a03150b030103080d0c05041206050f010b03240f0307060c060f14060d11032e060b030c0705031303080703030e0c09130c030c0e0417 69
    0xb4031400307040c01e000d00345040000340070a4020000796008000c49501290380e5088244010003c240e0f041c0300c82e6005002a1000800b84956070589041e2a04400c1a03440c100e14484d10400601103150300304140041070000064844c02d10f40c400d29864090390000c02c0c9464040da032003e84100580010540900038414440c0303280030340d6036080c6005030f9021341031440d01e140e0700040c1c10001948210380c0d140c45980d00105529600c402c4400c002da110380000d000c00c43c24011008162072002826034858801e01c0b00051417032420704883c100340c50050600142c408020004241040710f124030302d4603002104482e1100d900300c0b43e006850401c03ea4134040041718104900c004080c07002801d03580d9265000710317044060180520440706043c0700307810109106591307460700f4442c41c0c10204054001c649070103048180c413180400c0e1607003084d03802084142d8507942c117981d54140c00070780d803400d803824041845c0101c0051400700f54100580059950190180b030545010103030348100d0914424103c006200ba01303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 621279271 1250 621278021 621278027
    0x40b0403120903051e010b030d020703050609010c0c08030720071406090a1e0e0901051503030c101a030604060b1513050f06191101060b121503070807031a070e01 71
    0x4000302481c3c4aa07019605d08280105c4d01600d1807e4909a0500480180c1c3c0700350b03a00081c038241107911560980b219540c562140b139003240c02202c604800b24082108003400240104021548890b0318108003200072210685c00340d003d140112401c2e0705a00004061045014520808154100464a4a260140e000301090010080344914084480400002c01207036140e040711030040e1200b074548900174541005c0440c040c040680d2500d010b000083c08800150402200311140e00c0890780041022140090003d801041011110780748000b5280361407082d50750074402640540d00854010070103c04102c20420700b14860400311116250401c840c0c1c001203203541c40002125400c44501c14048038500210f4041c3c41030704109101001d0846103001c006130001d14000c80001680002c001180c0c542c54a502588604104080039a040340c000505c41c514044640e60802000390544401650b01c10030340d441c1c1550754104507411415600203225410b42c850403a80e1003042c610384503021f14054000a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 621280521 1250 621279271 621279283
    0x6110c06040506071e08090a170307030f0519080f070801030507060503040f150e060604150e0421121a011403040606050a2d08031c11040b040312090305 67
    0x1450107034001068150501c000456517131541c4e01c881102402951451900d41019031121140512905841001144020398203250186a03039480d0019460b22115850549510040d05500030401c0b004001038800320f1a4008642c00b0408592207100c40c4d4244010310914400008080c6800c0000300001000440c1000500c08120b8000d81070081d5661079a00382920030016031007000c0e200740c05140102210700482e5215a01f006620401c0d9412600c4800c100400d4900151500640b41903408041c000d8030b0111041c50b410620070760700d541d440b0113140b12024403a01202541404250f055611403400e110b503000d450038080691181ca5411200280003910700f11a07044d40079446e4401000140810940354040005004018000c9180f6903540700e042c0c10351803001040b5444d18600907040009103904400f0b04047d1038070700c0d01035030401c00c00000c14010940c0f8071080001280c0ca503914124079480b4400100b000d4400e070807100381d4403811070808503180035890a007a8100030200e5800c0000c14804110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 621281771 1250 621280521 621280529
    0x90506190c0c030206031303020606040b011d0105040e1008061b0a210504080a030c0801050d020909031b07051e0f0609040e0f101407050306101b050706110c0604 71
    0xd401ca100039800c02c210b10741141d0308000e40040f000014003403502c1e0050030041c41603100e5421154182d0310003091105545070815a01e002c04c40b258002c088000c140c40d04001c80b114180b400303d040c00e84d22218118102d8068a4400c1c00280070002070081e0384080c480250b00006070b4541e484c10f600e1491020a031886800c98080030406100d0154400240d40280d100e104040204240154205400e26050a5020001080c04640b030406044000f500451026040318001440c0140040b015002e000e5030135001400c001280c00100720080440b0f20080c00d00d50200d80b004001c00c8510309100a004410941008644141d12030a41800c001d80c0d0b92201851841c800355041515010f240010034051312112480c0c2d0020b0080c0070300d03095000b200040783e203400c0392018018130215500f0200f9142944050b12a440054010070000c2c81d641051505600034501c0c52074400010060040c005110b40102c6804545a0300050010410113600480f01c0d521810307281e003d0b110031507201b0000381e154420b03482 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 621283021 1250 621281771 621281777
    0x2104140c060f1c09050f010e0c12030405040e0f0f1b0402030c0d0e0c06120f0a090309030303090807210906090605271008160503011404090c08100c09050619 69
    0x2000d80600340264000b0800c44d03501c0b5045660b40044858a40c1c041c0c0403102511180c0c1c80342c054104186c0c5040e0803003a040841c45d00c040d51402e0300342400d1001516440d5000071140c40f5513940308444160030024041e5030040300001d042c00c1100041c0034003007800c000b906240b0450040c0140550115404201c9022038040540090410440c10145007408021065164044070108007118014081d00126205400c4840b40622039682e0b072018030112900c91034040c3c00208008410300c00a80640c3c4600d84103401095518101056075580380c450110b1035500c08040740207004800c2c003064028400c4c40c041e140a00344104071038205800109207010703280c02e84200d50032840101304100310300c250203030020b00094040a040d9003040c40250482400340c88480304510340c80500c1005900c03540507030b4180d03880da1000032001e020501c00c200140030480d0058a03240d841042c00904004100082e400402e40c00101103141c03440c0c0f1501800e100c0300c1d03a1125016610800500300c004211484502184d41282 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 621284271 1250 621283021 621283057
    0xa09050907050406080415050a0f05090109080a1812381f0b0a110d17070e0f04050108251a0705030f130e0a1505062104140c060f 57
    0x1007131000141f5400d1280c1c0200e10301c0d1000303001c5c10381c816400031003903820000c5090000780c0f10150390500320341300140060480c040510003101554481d00c101105501e407844500e0f90940c45040e450308081003c07001b116032000810340c01080140c0010002c81c0403156942100740001450007030400304400400b044a03250b005120161000f8a801c40321010f0f00207100704e65100c50010300c001d00301d10701d58182810303d40f05812410446c14407c40c2c509255040074800c2480315100c00c00b05948510085d58115488410701c2045c00032521107110711802400381200602f002c00710880340006c81043c40160442d001c0c24403c040c44107900c240441c52085000105080d580d4419040881c118091403210440c04280081c02c03002070307451301481206580d171501150310b45403948500030046410103a4008003035032440f101000030385440000b811040540815082400d44031180c03845903510100d804a6150348120000d4150351030821294070591000d407400761400040f01920b0520380542a92035080040039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 621285521 1250 621284271 621284273
    0x51f03110315011509050321070305070506130b010909080415030902030a0b01060834051603030f05011514090d0b0c030f0604050606070f0c0302150a090509070504060804 75
    0x802c48404101c000660200803961107114254250603140c041c03000040f604100031070240340225881c240c440301800d00203103407038845561040d5031304103d8058090000a00c00140480c5003032000e14031402c45c0d4012541d0f03146440c500a03085a4041c3c100740f080034500702406000036903400440c0e09030b4a42c01c01054038030000c0708c800c83c0a02181180290076000761451402000b80c81c1640d181659030586a0340203940d9026400c001c803003e001034406503a08030103c1c00540b07020780003443c0d3f00400985007062428100d0f0030200038040c4203500c2100007a40d14040205118060303c034150151242182091045c020f5040080442074885080c01e03c040c4001145141072740d80102282c00e660b80400c03e1411803602d03555184442d00115000c0c000c00c3d07005800100c0900e00742c8941c6200e00d200802032814031103191280c0c0c44500145400712908034040703501201599651808070103518560881964409240c01d00404041c2c0e9a48103e00520b015410310a601d074004c01610b0540d000c41c1b03450000eaa4071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 621286771 1250 621285521 621285523
    0xb3112021c0203010c0c1a0708040209070903061128050307080c0c060103030519030605010210110d02220e0103230c090a020c07050108060a060e0a17030706051f031103 74
    0xc998000354591720704200485660b80103030111890601684101c0c1e905913159003800180081211907400095006000a005160126018bd0406400d01c0d19112154aa80d00c2808072208caa0300d83ca8050404038040e800405032540160504010800c24103514840070720240450201418030414031903a50001001c4003004d80594526110403812159156900d081c040c0071a80904080c5807814100080c0c0e00700c1c6806030149404070b4074180e006003080c20140091100400410703101a103094010041800314852900203020340e0402e0715001c2c460007610001c6a11404107076400240c8d501d0308880108041204c4006030070950070403900c10945150304240d65400d1400d604900740d0b11a8074a421b004046030143d0282c41c00600c1241103402042d1101c0055a0246080b41c4050740101101d4090040c50312419080c4228031010b8001e007102510b5241c480074070310140007005130700e0303101203000001c0c4006030280c1a0402045490081e00b6407030f15004529607009400081c05000580d01c0152960320 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 621288021 1250 621286771 621286819
    0xc0f1905121c050403140102120604111308060f1e060d080702040218150f1812100e0c01030612110102030d09060501030203010c030b0d0605040206040b311202 70
    0x500c040b4042000b80d222540503200390814002030342c943c5080620000c80380e005108a5030090384e0100b00f1200c0350740d00e40800028000e81203018407030510520200c0203461400c1c00c5c81d8040c10a100c050807a526045c00301d106824001400c900c0160111aa00440c0b01e0801c8022a0011410380d005406140d860070060341300c0c0300e0868000e4002c0d00c000795451a10084a2051040003400c580b04000f1441002181c5441c1c00342c4403503c28982020010115220190404400c2248000c3d16600342c0504c124880f07410040d0b000e90087c1e080b40c660503045402e21042c0007201141d0b5090030104401c0b410032504428008908078000c2c4003ca5080b03000c503080c0c1c000c00030340f11001d0f0412001e200e0640c2d103190043c060442032000324069824900640b00481c044d00501b842c5420250400036940c40365290f0201400000d0000e03070b007100301003002080941c1d0440c02440a98415202e400300f0601d14510711038145032284030001d50011115040c080603207480c01310b40080341c04548001c1403201001542072620 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 621289271 1250 621288021 621288043
    0x13020612070f030e010213180e010612050709110406050c0106050a060e041a0d1203060801090f110f01020304090e1e0106050a1e05210a03020c0f190512 67
    0x40454420401ea55a0101c50040035248a990074001c03021218901402d07030042400c110201c050008081c040d541030f80701c0c8241240d20f201d90106402039058030143c03c4955540207548224a5103030010140f01003080003c009240d5003604109500807404047c00c14085d601402c0c003000000a40f030b2040da030003500482e0190000400058030180d50342005071042892104c054029410f04c07102030079211a600b100300425502130080641c06510b0b0342d40c20402000d2036848000d05070b0319100400d54100c2407083c0e4200600c0352031002c1101c599030a00342402c401410320f07a88680361003c18002e140e640401500c04030707441c80320b01141981446a40608198803072815403554000403400042c080d0301500702d401290b60a555103070119460710310382e2086804031080b00039207030f112900402c524280640c0c400c22120600460384e03118054a210f5909006d40410182c006900601e0307c2841c078030b00780103403030301c0103204075015507414809480114400c0900c0c03250501c031b0710400d2141d00d021001400700c20410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 621290521 1250 621289271 621289297
    0x10804030c050f0319080603060402060a0c0503040608060f3a0f050615010203031e070e1c060e010212150a051f0e0604030201020604020f15040b04080c040c08130206 73
    0x400003d5007029a02e4109000c040c0b04220b4401d00c00070001d0291b02190700800024000c1d0500f40c0c7c80307809108580e0300800c4030008000003615800046941400a00094002641c4031400d50900500700001640400800b82c810310801c1e0342000d0103a011101040d25580e03171505085109130111040740181000300d409040340084990940c1000004171b10540304171180300004114880800049a50740070031100810948039003039080e5500c802c0440134070380c04030b01d520381015070100c4980811440d43d032245036401c030045202060070070003c150007030850107079070f4200071420401c01421454010f14050040c01725032070b83c2902c580907600c0c1d290f1503201810001c0c03c0c048402e4445032400c0c4815058154540000d41c034030600c401140f40050844048030740513402410181c440f40c081103182c6911041c41c1d51f0101011010304404101213001e80020503264554a0f00c80d850f22200c02c5c01c003258058111320440c43e01c500419010341204031240c0010806c1c149045808c0a032020408a2060760701d00001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 621291771 1250 621290521 621290533
    0x8090a0602151003080a1229041413020915030a050a120c030f030f0b0a06030c18050a030b0a0f0212180703050601090207060204170601050a0b0405010e010804030c05 73
    0x5503500020040c2d881102075400042036a0b80703000801801c2114000100291010040e0045461040300b640c8030030021103038001040e51908120200c003442d6200039504030040f0600816036441c02c1d11814208017600a0181c1c11444c01c11050348002c224000024850034241d4042555228107213540d0490b000003604550001000f81002a550312220a01b02d440700100b0714460525481244401400e80e4103807250761001c028114281e002c1c01c0e00b0010783e06c0341503441c0c003880d0b035964030454404000d05039510005440e403100c40c0c00514503044e0903180d41c50a801e15104004640f0f4101a40b0120b03a00580c00500b181ca54100860180038031584040e0650b0000c01c02c40510910114864010503945484000341075060300c14a890307078698070002d0480d803c04001081004880d030003c1042600c42d0b4801031402d1344030318849819220741d40c000100d9501c680014002802c01c802140040c144116205060615100000301040b9910304140d0400828202040800d402940b02d807081a0740311040d0b41d2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 621293021 1250 621291771 621291779
    0xf1109060711190e0a02040e070c021210150e010b040504020a09030b010f1d10090e070e01090c02060105031c0c060207080a0e0907030204120221100c0917100908090a 73
    0x8003c0b0382c01d00075280c001c0c1c030042c049001c036a0144211021a11302c1e00e08000075030344292040d141441003280c143d810000c140b44040d05000c007400a0072000044860001d4485200c003080400c21445802c08441c09076190014040120800269400c840c81281c026aaa00700c182e0210350741c0510390f100401c41c80036400042800c0030010800c00680e0000040b20400380c4184901508182d003c2e159054800c049040c24880c040550700088945062001182c01c007907511200c1d0100d00c0402d0380b08103c11651020541d031126414840e2600611084000b80140030028000504003540d0120321414002d00c12a44400c0003801c2d01a96142034100400703d84480d20640c0c041c29420420500b1841600142c0024018600a1080e1010b450300c83c1750b05400c0038000c0d0309000c032104801c404d49545800c00408609546001c009503c0742e020001008034002908281c060316205007504800b802d0715003083d410281d40000280f410440c0380c580f80c0882c03052400d040071400d0384514400c00e9041658142c000c9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 621294271 1250 621293021 621293059
    0x815010903030509280314060a0209060d0506150a03021e2b0f02070602070209010b041206050c070b010816090203040803060d0c0e070f200303040b0c0405040501180f1109060711 78
    0x414487c40d0fa400d982181e600d418141049100b8a640c45078003070028802c021200a055000307560000c0054000b0f0701020740c4c9044901c1c2c60308a0954600042d070000f0700070105d4844100114102402d4030402c504040503940804c0002d030041940c990f10052400c0b1220504070396030000d0084040a400440d170f11180c1e42800c801a41c40502c00f680210b1035000002900480300c0104c8003280c0720807030301c030101c0711a690350036000c0c20f03015040c0318000000b03000b030b2404030703d130401154000c10700d0100400307460b170303910036604c0345000742e58442e84101e48140100700109070001c1c102ca501140441c0c001500040c545043c440030500b03a00101c1890090b81c0402208076081000c4840f0110291100d4059100d0400742c60182d4070a882c42403402d030018004200014580801e140d001003400a1460503c1d031541e001c0b804440c400da0003010558020040d1090442c160b01c100c041e1041d04420170f01c40e40c1070607030030240c9501c0b030f05c080c15004080019204040c00802c440d409182c60000f0040111034000203510 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 621295521 1250 621294271 621294293
    0x8100b0f0406020607082a071502040f090b010c14030c0a0302010614030102160807080d0e03041d060a0e06030718020304030f020712030305180d08150109030305092803 74
    0x4015204d00800b154805010341c4c2081d100e09821401105980c0540c000b50b404000541c4102080500a011200004001200c03201905a542500584540c40e080c5a00b03040d03c1c07240d0080314510310b00000303a0a2642d001040303503840e0703070058420440c100c086035032103143d4230600c0c803601810f0050b406010205981904032400322001040c1e02d11420313000c0c2c01010b00700d1064450300c0b410400c1502d05000010300345006802c40c10b0090715014180091144000d040e1103080f1200d41c2107820006062110b11000c0c0703035400f41002d8644e02610b41e450040081551076a260048400801100d030004016580800c0503a02901040b0008034074814040c0700c2070301940003514100e0219042111902c1220f02c00221142110080415804640d620f51003d174010b04028203902c48a94040c40e4a10021404014010b01c00255603222000c0d0301e00001140750100e241c0741c0e46410401c1545040001c02e0380321007a115aa8011210b40c00c41201841302c50740e6155804c15840d0802c640303080c002080c84a0f9481c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 621296771 1250 621295521 621295529
    0xf10120b070906021203150a1a04180614010305061f0e030f010203240105310806010b0a11010902091e09150106030b030705130e0106050f0303090108100b0f04 70
    0x20142c0e8a51540300a984416905202c0a0340c414180001400184c0c00d40d00f24903000c4015144444198403002480f210a4144481c43c1c810740c40040c0402c400c0e02d42c0c4884d01c40800f5410300801403242032164064a074814413290504041e05c81002c51102c0e640e01001540040c04600d038400c00b400c0b010005440c0242c040181440380c0642d206112003c44103000b03d030300c604001c4107188a00800700c0300e000c458104041c0700504000c0148541d82e14000801180c030040c0a12443c8924500e80e028000e078880003c90300b02e8440c982000e40100418075540d070035641d4048803803c0196220f000700c5441801000d030400c0103503100101c0303424081201c2c4840400320070303071106038856003039035548004041c1d0b01e07040c0c03c0710805c40d0058800100a4580f09510005500400400313440f2190742d0345000484140c28200118010356540703059400e00da9003413141c400104002e8800820319424280000e80342c2c02121174407414008200c0000c1c07242c0d030012404201500ea03555105071201e012648070b181540141c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 621298021 1250 621296771 621296777
    0x2b15050102151e13020a03030327120309020d020a0b030615030106141c060602011d0606091302130c020a0c060825090906080a26030f10120b07 63
    0x103000c50700240c441140a00c1804081d646240401ca03c502686920030024980c9900c0c0481d0808040166030311b6046100644c021b80e008103c0d550309074142d81400d94a46071042c070741d802800b103090000781c070101642031102541c100003c66503003a002040c803140031032000035800496004082414070800707000d140110f0382070703d180c0681d111080d002c101621003801081c01003036080c81e080c05603240c914010100d9002140d10645100203120403501a5021600a00090703510390f0f01d0300c804d4410180980d4260004039000f02590f04007200070864900010b0442011902003202c48015910b50422049c002a05000308008449608074003d445040150089032001180280014081d02c111002030240c40340420000c2c0c1810181100303500d0007211480341090004805000070705e4150b5200b402d0081c010000a840c2d41d43c191b2070030512031500008490f10003060b51040241120580c8c5c10749a102c1c086012555040c3c13100801d45144901c1c1e5441705582a01070500e40b02040254001280165000d132 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 621299271 1250 621298021 621298033
    0x90609060b0715020d020d02072a030b0f07020102121014062106040b04090b010305070602070605030705090f041e0b0603061c2a030c050402040b2b15050102 69
    0x1c18100414460050041c0c2102060300005038000e038594002c00c2d9100d040c141c0140782c0700042608102340d801803c0d00382c0b91085551103902c403c4540409098119400c0018000500d00312f68a100c41c44070090101a08040074600243d0014001d5049403802041202000380c5454100c1588499511a00440d070024903502004042810081c0039942184444041c54045814407203042c1f00321407001b880580c3c040c0d161a8440055107c0703210b02c44050380504039000041d810750905516282c070b039500220442d8400d500c10003095502409494012180b031500c81c0d0b0b14480c400c0081c211520088070150303c42e2602c040c001e54200208006860417070403000501c15514200100501ca00046440a4003c100d094a15124100e217008000c00103103d4551000380640c4400100b8056500418205100100d81014018400c00040c01b100514080710f0951503d41481010300c0d950046010000c200703140e40740c4120f20812148100c40100c1e08001080101d603010002c141600c52881c0b03d01400360141c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 621300521 1250 621299271 621299279
    0xc041e0f0f06141801080604140a060e0c0310060f0c12080406181e0c1203030902012a0b07020c10020c010e0a05090f130f15050f07080117030405040609060906 70
    0x102c0075030f294002c0091406030b107400134900544290400a0060354407a035a4400c4205548030202814041c40826500048072800c200c0a600e41c8280600381150703910342401000703104010040ca40c8281c1700c1c01d1600d1854420801702c00e40e60320480a000601400c00344040c1500310342c1c0170450034030503800f40f00d090144560440380405a640030b030a000c2c040c410744454407690b8126120300b803911140b0810920308540d5585980184100401e241200040d845080c418155a800341e55205503000c6074102c4440402401d212041c0488401002018084070400040005009020b90381c4c90350342c013801404001401040c000e40751800e08003e540441d17220b8840d81d150782090002d00d0140ca00c0079045810780c1d1244044411703051401440e070300382c40e0042120940004c610f440b2038030000d03100b00c82e014a088006001d0b1800d403000101000e40a8008a04000b101039000e24102c0c110f54003888001144a0811820b82c2140320741e400080d041402c010002621900e1a8080000ca60414200300314060b15 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 621301771 1250 621300521 621300557
    0x60705240615070302120c0a0c08010506090603070807030f021c150f0b010509131107110a060806031507140708030a0f090512091903080913050c041e0f0f06 69
    0x3c0100280050f8003203841750b0408901c9000401e0701c0c00d1000125011050141d0315030b802c034040c61300a004aa51180c040c0703c420b00703007048550b4001d40110090214036041c0040303540e840c05207100207805440c0d5a900c40055403201c841d42504003a80789520030b1106007070300f881e10180440c440c80141c07161410345c4440c2c1140051080d9601541705030b41d4140b420349043c00b000300d0018a0b104100403143d6071450110031080000c0144105072081003081b0030b0241c0202000301e0b1140300c0c0e026170140200c0d1410042103a8012400e10301171400c1809003e829116a00110352a06a40d80e10507000400068408144000231024501c2980d50140130b1240c107605142d030409440003418000d00703661041402030b41518680b000340a420034094a4843d80d14088c40622640314041da1003500c6d030050000d2260124141214040b051902d4983c0c20310107420000c03118034161184d8440c66000010364101c040020300c86807241d8000780769500500d02c181741c6035810060071013010b105042c003045a010058401e0a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 621303021 1250 621301771 621301777
    0x507140d110c030d1421011a03010b0f180603070203070c140d0b043201050f060a05060706020415050a11240c09031b040f06030f02060705240615 64
    0x1c050090408008050400e0700ca50003c030801a11045e800c5c0141c14140c0d0400780c0107101602801d8800395294585140f1110381040403150045011041006111803000c900c101c8540102040504d1b644201004803518005920070149612550010901100c954008090a01c0034010144404225640c0a1700c0445441c18008560804682040003001c00c0c3c01d0790030203034803034060010035440c40d400f003a95110b032031407600d40682d12510301e1908101c0c0301c00900c100755001c030f0420340e441202d0500d1400201c4144041c030078540f2616000480030208640b03901601d0042c443e00800914183c4a4070014183c1c0e0040c03034501c80003c80440e0305521703d00c0005214840403c64201c038410010851000300400b01b402480041264802c00c542c50598408208010300d00100c50440050081c130300082009460207201001c001030305220080c000700340800a0b000a069044039103999400061510a04002095211405039030345040102e40c08052042c0992081004540c0c0c880788144a10305600540 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 621304271 1250 621303021 621303043
    0x10f0f0e1507110109030f030c080702120f040305070b040306141902130b030a09030806030a150506180907030201030b010309080304030c080405100509030f03090d030305070507140d11 81
    0x25001c40e25a500c0020140800c94101c0003514080d8424107108a03107a0030b4a80301c205c00c400244c3d021030000303d6a070f070501c40c15050f00c14a142240c00c5082c0040e009644811030088241c0300d260010720440d80b450b807501101c00441e402015a0107080d9211009016a08a0711040d01e015091481e00341c0c900360302803001440389192840143c0709035401c107490030081d0450a1030019070400c0c41c138013003036031084280518171411500a02058040503894018601c0c800a40181c4c041d0348810034150000c0c8030703104070f100d540702d224600103a25614100003454040c401c0d40301017a200030940600034400004101901901e000381c80622040411000450840340401070241c0010800d02c0454004ce00c111041080306010f0a04941015100e1001030300452000d046000881c80005440e421424140242901480307000055803d0100f500c000c2014580416001010540c1d18400a090700d4042c07825a00c0080c0c00c45940310904c1c2c0040080741d80e81d503040a2801c00b040d0495041041d8500c0001c59070400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 621305521 1250 621304271 621304273
    0x6040b07030e1219020f0c010c06020d02040f0303090608010816051e090a2f120c0705011407171b1e0304032607082206060602010f0f0e 60
    0x5689252045008140d4441c01c01898001e001c00a0003003440300002d0404100031400002c039131507a000e4080d1501001007034810382c0350482c03528010940e0f0000100c0c40e00541000000d603440c10b00d208441c00a12494219085849103900080240f55002019109444048d01c400c40543d8841c01103e58510200d02c401d40c070400112001c0c01641031201c1121544034640e49000b025101010010700702c00001c07980030007010350310510561004500c00c5011000c64200034400d0088400c0d41410328944074880004003210f917510081036a03d5080e030111034080760002c0c0200070100c5060014880f0f664107450325800100550301590032801c0c280c5e4244d0068081c96440600d68014400d050b010703420034086288918111030040c400107028100861140c0d2095884403424900681c0602600d17001c501c03032a00309078206041115083d088a4a20707007241e03070102a0747c486244104052004a030508000b400e180c1007a50014243d030301500b100d000c000b20218180440d4a140e9054001c03500c009050010b5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 621306771 1250 621305521 621305543
    0x601050a03110607050703290f181c080f0f060f0f01020114040c0302210601093201060e030321070c0219050f04021612111207140604 59
    0x900945034002d01d00e0030203020075080440c65240c150400322207900985071091034030881c8200b801c5140230080d25440c5c40c0700c00101030920211103200b1780c200414081c09103182440f0044401c01c03c122603140000c040908031000380101d4401030000c00c1c280c6000080300703986408a00100c00c1c580d000d6102d104c000c0c214205004000b41004501d01c0762010050541d5a90440c0003070000c00c42c4400d61140d401a00211499880c41c03043c41a48441401403140d200c6103200d001302c640c8400b245090442d9a00f85010a46c46035542c4903211501c0040c0405403180300702007000b01424212907031071b8107c52040c4c540700c40e81044442416144d00ca00441c04144100f608041024052010100e030f80082070740c540b4500300356451303010645c0c81464001001120344180d40130070007480e007a0518001882c0a039010f41c205500b03c1407851003c01c9030400144070386100c41e410888203224071420740c4202403031340450f920b01c84000191001a07000007020364a0301d91b0325600d007802c41000100c1d203002c2c035070101034103034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 621308021 1250 621306771 621306773
    0x5060a06021f021c0b1203120117030405041a01080601110a1e1e15022b0e0102040f0807050907090e0a060801020703090501030b031b0111010f0c0f08090601050a03 72
    0x1030358216010071020381e00f0b01540c031180140703208550351010b107203a000030700c845501708204601c0300360b0200c400c840c2e00811120005101000d100d5044440310941e95000e1071184044031b00318011500425049841d01803011007103851540e60381d152403000c0c0c80b008400d40311080115003519090000003600e50024409100069022031840c0c040348072170841c00d00c10004c50fa00c00120303080003200611451003410641c001d000054101d40070200f04480704604d09407410302021001103500c607130307940c030000105280820580c0720381140d1031103c20780c0001c540e943d031200d00002215425005168a91140302000f1405003010b007035450041c042601d940641c2031804020045011008004a8083e6207a0b680060610807d0001e440d01e03503c2619038800040c01e210005040310703500c1400c54881c0e0710640390340b00d0120b07126102c0058000d0a01c0c0c03000e68414440c0e00740e8050000b0032008000c0c94900a41010941c0e03202c1d148881000d0340350380341603880d214400d81594072442801507551040044074100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 621309271 1250 621308021 621308053
    0x405070203160f020901060302030f100302130209031f0204090606020c06091c050105071d1c0b10050a09060302030c0a0305060f0a062612070c23100c030305060a0602 73
    0x82c00c01449801c01210244031a40030511001080e0b01035004a9004000d00540301075000200790f020741060b202210582c55030300026009510042c80c0010302e81c0c0000e81d016a0340303050028042600e0300342d030102000456041c280009600a00c205980c50346000170101c0c3c000d1000c1495031001a0080240d401c0024a40801c030b19980403444400d8201624030002000500c203001c1c5900c1901d880d1144d042502590403d650302d242000c038214450340b14005840e03441800000360700c820343c0c3c222050301220366651801000e60326542c3c01c16980030b58042c1000030818680c0e081075041da0320940a8802000400080c00b03403100050100a03c2600101c0008101c100c060368040d610082c441c41c00f04107a992004e500707a60041121110b1140170050360a2408014200520311001204240d96031400e04030352114803900744140644400f01c3d01507104c10400742c2010908080f8100010208075242d10035490240250070080c0d400c0303000c079080c0400144a444c2842c0a003040341d0707403034014007031072100c0100310 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 621310521 1250 621309271 621309307
    0x9050f0d320304060e10120f1104080c0319080304060902010e06041403060127052a0a030b0307230315101a16020d150906020403020405060405070203 66
    0x440007018225040c0c5400c1400040c0c1c005030490041c01941e902ea040040040014115003c40c90058180321051400c0710350000420030010500c2c9400a003001d049002d10003c3d01c48404001180400440c000c1170090021070140c881c8402101120618410341100802511240c1000b4100b03c005000040101e042d54100c0181184140741440300354991200094981d001074020800700020340c0d122080904080004501404008a8000481e0ba00030542c0040c0000b542c1e56003083c0f62100081840a80c40b41040b04441d5507c2041c1c505043e541d0042000c2604003820100001e410414188090300700403401d0015503445411288110314000c0c91038641e03000d05c0c1c100700c1c0c051042020301c1041c0391449448501510f0034000175446945803001c015018210325000d001c03104070800105503040081d1560286190b81600e810307182440354201015820b84015000400c1d50920481404008ac03660040094a108503070400090319000203001c215881103e0f8100035900400480c42d6444d02a084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 621311771 1250 621310521 621310553
    0x90503220f0333061d09010e0325060c020309030d0c0809091905090609010c09080c0f01050408060a0506100203070b041112010e0312011703070204090c0b0a0f09050f0d 74
    0x1400340010300f090b210004403010381d4080c3d118501103044400e090441002c01d00d412600781d9009000a100000801b0344070711840c0004805040969444110b84801903800840c46800150810482180c198040d4807a4804800c2c6031181c0103502e2012940c80c0254540d090381a041442c06050030464401e101e500e9901502d861450390021110b0030004025000d42e40c42008070750050b00c2241400030843d42510300b16058141441450701c01408480400500c1c105001c0b011a031944018880c0001a01c40303120340d400194545c040d15003001000d080503000a40102000c1e101803e043c0754a0700304903200c2c00f030140010280300c0300307401046c041984090380c3d010300c5800404206840000030103080c2102c0e0320301504100c0317810115a0b142d02000d040c07201030060200100080c0c1075042d451400d5124400e02100902c41c40d40c440801040c45881e1400ca0003a00460248036a40c1e550484040c00101c0c5000c60303000015060781c00807501e41401e0b600e003000480040c1141e003640c007640e034841c0c00c10b41f11000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 621313021 1250 621311771 621311843
    0x50d050a020c0307050c0906042f13030501050403080f040308150301020d06080606120d0f0311070605093a1b060908030a050109050402010f05030703090503220f03 72
    0x10030000c100500f40000c1110601c500300070100203d84c001030000c8410010000f42c401c41c0b4020700c0d151440070018004442c1d42c0c2d01681c84044400820b843c2a090190600103130750f0304144400402005015448640268040d4841303140d0355640085040ca00e40c41141c00400040f80035000c602d00c0140103045a902200040003d814020a116000102c41c4d81d940258020382c8a001480000e0508441c002411140940500201d070041e40000e0300181050400b0000c05a07a420000c0c0d04081c0300c0d090f40c40f907551000e400d00090500006541d614040c20300f09091a203845104800c4403400400300ca00c404e4400c440d0507100850866090b6510001001081010322800e038002000805920411180318429600786459040200706441100e0050b0020390302d580c80c0509110140c4c0e04010640010019442c002366242c0c0c0d040d8007240a80b00e44c00c0001d1081c030021038011240e4084014840c5030a840c4102107644030368030040b9105031110b9110182c008140000b0710311054100f900300c50509601b0130307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 621314271 1250 621313021 621313027
    0x804050907110d020d030f0b03030f0d060909060e010b03010c08131a2a070b01030f020d0c06050a030e070b040b1b0706020106140f0a0506092806080f07050d050a02 72
    0xc01c02400c00c2c0c0d01d0140440140c00c4400301a005c1038052080a826545601042020b0701020002c01d64911580d500d0360901040840c100028240d41d40018002d0510890103102e060710310700d007080141080f00000d400c15400d00402e5040c50034144500a60301e42d2035603800e03449880d0250324413900d0351000340544100c2050548003e8000108200f01e003e030b18038400c00c02c00000900b44981440c41070402d040303403100301000300310007040b509a400380c15250000703e003448414052001074940420580c00601151405c0c2000412075000340252182410301e0b10140038107084026040c0c0c4496240c051610581810300041c041d001c40031024040720402c0340f0310314102289010442e40340400517400003005039101c0340c0034440d00f01070306141c41807102c0a403500b082ca00c42000008e2800861800f520740214008214610382d0ba0700c441d440c46000c11846025040e0b030300c0c0058907109040d024003502000c903442d80c020403103041c5066161131241459545240c20084c1c05010a0701426020744030005180c3c0034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 621315521 1250 621314271 621314297
    0x14040e0618100e071505030c0f090111010507030911040207020a03061d07140114041412030409020f03090715021e07051c060c020303130807170c280804050907 70
    0x35100344015001c50400900d105480c2605e900007200030960302104100e001d00a0005403d150019102e40e40c3e2000b189989550400e00100e403c1e04016026225540c2811306000d84182c2691041d103905000b810350440204110041c802070340301e49a0000c0d00980c85040800214540e0790049602080d0300340121401c24100710010b1504016402c82c030107204101c20280460342e001800400d000f9901c2b040039040c28a0140340e401e200d0104503c80340950402458200c00d40d4081c0b01301c2d0b000d40b0310001c0864940c501d00506d1000c6400440301c080c0705110b41c44001c5101c3c5a054242d00042d2001d43c0101180f000010100e41c00c414000940c4d240c52051440c0410166509001614001034140702c03150000b80390308020040da200d0081ca0010341d0010410307c01c2080351000d00302c1540740c200030300030350b541e445103010550f03260740740c45241d4003c0c004100b4500001010a851910501c0f0521150f101c9611612903c1c0200c10794000808515003000100081e0411a441c550b114005080c010f0301d11002c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 621316771 1250 621315521 621315553
    0x102100209061603080f0609011a03090f0709090c09050c04061b0b010b0703030b0d08030a090512040f0e090d092c0a0213170601090b0d120914040e0618 67
    0xd5210131408940c000f0304201c0e00e0400103042e554800003c0328a984a5498140c400c01103003031a42080310350441c0040000c0070040c0402c809250070106400300e42940b075861800000a142d5018200c9600d281900001040c500030301845001d150041070380c91510b0b1424805640740c83c503030044c01070364005010051000c20070b40703039000b8001c021030152700d0f9840f80c0d80c0c07400070700710380014404c4c1d0b2080d00861080e10108459800383c82e80800311100005045005040083c681802c0b8210304205280001d00407800c112202c1d100350840d4000324110099495110000342ca9401101224000400710041000020700c0d50030315200c0c01128803051050081c40c00c8481c144030108554100e500e51300050500291050210408000c18200b10720700c2d11141e403010340383e480342018840c0102450b241c5080011a6a4503e0401201d940c03081d55110a0000140d0180003440c852085907806025184d18900c04e0a2600035000310041c0301014102c40d03660210807503c07154003003040c1e58007441114066086102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 621318021 1250 621316771 621316807
    0x110f030f011e05011211040b040b210f150c0f0c06070c0b1506030412030b0a1707060804032118060905060115050415121103100b09010210020906 64
    0x1d51050b8258008800c40390b1030341911010b07480f0115a650000480000c01c002c03407202109010b044401040c084003002c00a40a0b100741ea54481d44080b43c10030b0440110130072104282103261500543d640d8480c040703082c40d1070b448030004e00c107854040c0100055070059035100802195107618192402c1440c1c40c80501e19000c4203c0780c160114041000340c9084c40020341e00e0a0f48426010319a8014030a902d000c50ba1500000e0001800f9061b255a403030525030090304141601080a000841c0403a51039107908440e4074100b4075041d803030151500c04642140700b45000b83c422500b54841e03c482c144a25600c1030900d0300d820825003404c1d5501d070603002c00c1e0042440c03511610700503040440ca1708c4180c04d095007011302c10780c0110805041c1c90301c030229054114059030101c0321440b14454480641038000ea41a0f0008611100007900d05100100065101405903014580c40d2420300165602c0707550b03549440c480d40ca81c05025030b00c20780d840c20740c2184035001011031080c05410103007840c013101d0ba0004500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 621319271 1250 621318021 621318041
    0xf07090e0702010204090c261603050c04031202061602160509040c0b030a0212100e0c2b020a020c030c030304171e1c0804022202120f01051903110f030f01 68
    0x660246905005c200c0d50500718140682c0d0701d607140070542070609d942104100524440010300d43c40380000303041000d6403400e4500458018090640006408030000c1d11040200c4044d200c00c4481c481080f403141c400a148002c0d1450400300022250601040000c0000c0052044030511134501e40460151051005107001703120420000d80c50326650000441b500e0001822407420910040d410003201c94800c1c407481c0c01540b4140c04594130b01031400f541d03034601000e01220b085485418007100300085568001c2c0441452035090b1080c086086c0c04250311945004403266051b4001d00050010a60942d41d071300d10705100b001190810582c40348260b840110910310721850b41c00c589001070130700c0d03104a02284003414501e011038191034550f000412116134094248010816400b007240e030101d107981160300e4800c070400030650900d044803110102d41002d01130075001d03074800e1400180403d200180001601d03440400a00010800741c00d01991120301100389505124413990425032920a210f01c40c07501d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 621320521 1250 621319271 621319277
    0x10060c061d031918030807080d15140303091011010b0d0803070f02030c0d0815120604150b2b120e0319030221040f0806010302090f07090e0702010204090c 68
    0x50005011001c0c0111a42c40f0500600088800064803407103a003940b201540d030300c81a03503900c80c8100d0900011600900c0765600d40685042c5041269160498800c0100e6198000d9081586186000e150304d9008400c401904507244210003000c0500a20419842c81900800051000340490001d022204060425503079000b0000511200d1940150503460380f50540c0001c40c500004440320a9803050b408594000300500c510100300010810214180e0301c0600802074030300000401d0281c0e4560000303540444041c10391003808605080640038204903042c004100200265900c03002c62060040109210f84074802c2c40070410014410005201c803800142e076800700030641c080141417800341914103c001c0c41ca880121640003a40c00100503d100155461328044145060030004050050381c0146401c1080c2031001b20700c2c4003001504904030703802101c8580302601c1d50b80c0c02c400b00c1030003a9100030005080301810700043e00140b00c0f107a04465180b0005140503a512032080440d2220f04e541c03400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 621321771 1250 621320521 621320527
    0x13060e0111070b060907050703140d05090f0609060c04180e06090f190c0324020c010209150415110c0603160f110c0d060603020301060608040c0e10060c061d03 70
    0xd004049043c81d5009500360b032541c1190034101c01c090300d40d004100c0010104400309100080110a5200f50703406409502c1081c09241070401100c0d440d1120701d810b00c01503120b01710010b0007980001400328003400c0c044104c1d0b0302d0941885012500c10101740040140b89403101c520300c410030002c000c00741c852100f40002e0302040000c800c25608040c0d00030350300100c03012514a800046004a0022402c83c3d501c00c00343c0364038103c01001d034100c06509400d40e00030244041503e9094602c190001c1000d004100d820180b414000350204010380a20300820300c02020283c400c0c40400c2c0225000c400c00203540c07088440c5070454000290042d4000c50700d1151090030002c000100c16040352003a601d12030541015902c2e100d08420301b41d034581d68007001600c508060301000c418000c41da03101102842d0041d00912055032203001c0074240c00401d80d0215400200c07035400041c4000c201c001940101d407900c154251072441c00c0c1089031945500841503410307641c4c03068003001400d41b6000d50f505004024001d0740d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 621323021 1250 621321771 621321773
    0xe0609030f0703240e0d030b041b090f06080c090405070c0c09150b0306012c0303070b220305090f1c030206062d06071415160e0913060e011107 63
    0x440401880f11300001303282401d5a00e501d541001c00c45589014041c600003522144c400001000740c410b0590340740c0001e821280c4030345429880f284c2d00080c2c80b0000442d011031640d5140403a49001c1c03c5440d000030324018002581d151505801c000c2d080200c1e80b5100d810701140e81c03108201d008007507000d2199255903039040c8171000300846900b03006010f0388a416045d03203032110000c0d00d600007045032024141942070b50010600008010102c0c81e40c0301908503031715001246003485c40184213a9060b61070600c09014101005c1d101c103001d03082c0c1d0380d1555441c2c0c00e08040c441802404400c0305400c60740000c20081e03619035652000ca940c1c0c0401e0096001300081d0419009200c003116010003030168900d5040c0501c003c0000754503c103520080142c0350030f95200303860300b07025940310041c14850503a8041c0401c0382490300f0b01d01903102d000b043e50a94503c0c048503811400d444100a04c45415008014540040c081542603107010f2401343c0242e8011540200c0302441c1d41c00c690700802d0421483c400420400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 621324271 1250 621323021 621323063
    0x909141903080f041e02011e0c0b1f03060c0c0f08070c09060b040302060f0702030d020604151b0e0a170a031103030423030904090308090d0f0e0609030f0703 69
    0xb07500308144500c3c0c0320850505403540400c44c0c3e031011010481880700c100e48011644510f064009001503207920358004014a080241841e40707100c8261015521000450040300c1c0406450451040d94241d050803a480c43d564034014005070b14601c801c0c00705a5142c0c402043d1409035510b00d00e8070480c1c045541e07102e603160551901800360080341c143785c5040c109101d251018230486040d03e40440300c0c551100c40c1308040d50094490044000e405015141d4807000040e000107859000700d20841d002c080640b111700040003142d078541c0040a2407a08a041c4004850082d5204400c4030001790148a56603150500c401450640fa012000180d00c000003050626900040c084e00003101303500075614500741340c2c6441500f80148850210706082e2a5003002d19140c0070411194907200203001404483c0d958203000d0003001044480c09102d024040402e90110f10810a0390180350141d00e454145680080c103100c100d801011072240c15220f00340c0c01c017040c40009c0140d2030007180719030829414201034040c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 621325521 1250 621324271 621324287
    0x321603080a0516030906060f030b061203030903070611210a15030b0a11070f080904050604090c140604030c0902090f22050a0209060703030b0906190909141903 70
    0xd4030494640400e0180e0801e1066110140f004689000300312441e150030000c0042906620010071811514000000c200d2141071182c400c0f001142e0000d04580300406442e182c1c401210100341a41003000300400207002c0e0761050344002c50545401d03003040d6603001c10300748400025034414628031544040000b41c400f00e008400881c101500074030000e81c55a07841402c1540090100c0350507545130328144800b44507100c2a21030054015240e02c07080480d81c100601c40307610501510303000f0344c10300b000030b10b4501741809185c1026905c40c1605d4212031405440d03180040759502c1c090b41c032040800000011454060f4200064013014000590b00d1039200300b0404c0203248569110302404406081718030002080c028200b19a0300c030100070400e90341d0866448020300c10f0903003150780b00c1c002245040030b1603030680c0804070b1001e050364081495103555080004015164504c6014680c01b884140701055603500864001441268194042111102203c0c20041a200c03002040480180c411382070540c40708030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 621326771 1250 621325521 621325531
    0x2270102030c061803130b03150418030807030b041d0601090908120903040f06021e030c030f1303020a08060a0c0e0f19030204180c05030d32160308 65
    0x107614105005070070544408008000800c1404040d0040081140910481d01000200f0300e51030000354a41c458400990005c1c0c48141303072440c1001003c600c2d810310741316400c0081c440e40f01c050800407107030380c0458a24000400702820540c8540d803481c83c80e111400385040c0714134400001030f03105440c40c02140ca08141640b2080005040c0904500400c005c5412104800c603003080907005a03640d0507002d0320f0f500c01e81e40300310001c0032000ca0015004d0b0340440c40c5120076134001c0d816007504424200300d650f280201c1e0103000b0103410811640d42c1c070061351002011040c41c8101c60380c24441d500d4000501c00081d0390700c4690541c1116080101c00901c0c3e05c950b0a00d010907044c03030041a00b144d004100100311002005018005905207043d91100c0c03000004001d6500810501c880c00100c00500040c2c00c54a0707003102d4013440c0c80400308003031a0210b02074903c440c0b10742d1390308180e126500300101e540111003202c45200800c0f9074903440305d0640c1001018803002d90346481c81c1c0344403035250081c0030b1400202 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 621328021 1250 621326771 621326773
    0x9090106180c09030b0c070203030d0c120b060a050a030b0a090212070903031d0409060501080f12072a090c170702011b0807050c010e0f160e0105060d0b0402270102 72
    0x26100802c0742e040396502d000d4907000060300da441d0382c030b0052908540c85041e4001c0d62610000c180b2010310301994003c481d9402080c2c1d03c90f40d81044040084058642c1c00c035155a00400502481e8106441480038002c0102e07140340c085005c0481c5d10206070042031a42103d002d09800240046003a2000c0480540002043ca8005021855034030000c0a0100c00d08460031154800e2a0012080d552030300a40000b45d0401001c100a580d60001c03d990740b030250305181254058a000c0c00009100007056030780d0b2a800130500982c0d074002941018140d090443d1f4140b002180d1840410045117030300c0303203900007011034440380080e00b1280900340700c2200050011086a04050308100220124070708400009044c3c108800241c0300c0c00002c0e1958040d40c03902c440d00750301e4410702d48003600c2c2c00500304e0001030f80c443c15a121a00300103d010b00010f42401f0340d0408640b84001003225007400350080409103602c40d0300107040c0d031880c0c0008041c1e0b403051483e1004007400121841d0190000c02c044240712400b40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 621329271 1250 621328021 621328031
    0x314070509150919051f0b0408060604150e010801020a0801050609030d0309061b050304150204050a180f09080315091320030f0f0f03040605270909010618 68
    0x50820818a5400c40110301400f10803022460100c500500d0000c0941c64000600141c9008090f10325a41041800610141c3c1407040000308000c0d02012581541e0340b21015250651320901400040c00f030461025298030b18284000884080d41068140a000324000150340caa158508c0140ba40b001a04550b21070392003002030500c15607000406040550307482c200840c2140180c00c2c100c0042c8035400440c081c140406a1a0750100c1d80500103610540c4288005812020000001c0303049010b01e0007a6a0401103581d410f02005020320343d00c00071212050f07070100d1200c545c0718114007a0f65a040040310b0030003011040c090075002c0200348061041d001c2d100c0b80060720349115003513001e5202400103020001320401100d940303043d108220b2041c80700601100c00038040c00c4501c9903212075030800030340030340501130701e201406c5008000c0303070100d84003640e81d2400c080152a590440404400080604445030070341c2c8041c640b120404030b803003002d5100000031703c03c1ca000225003410004002d400400c81c0f800c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 621330521 1250 621329271 621329281
    0x3110f0403020f0f040e030406030f1814010f020f07031d010518060f0f0c1c020715110d0e031908071202070b0c010504030e030c03061b040b040314070509 68
    0x41000e44044a8046459141d0080003002140d20030740c1d8918143d40050070b101690f005c0680000091048807101d60f020007246ca50300381e400045403072a03910045001c5464031140b0200d80c06000c9078090b001810000950703651900a050201d910208101211034400314441c4141360300f08200840100c0700081d00516a003100c80001c000744034410384503010108562070a00075850740303405d480801d40544c48103070340d030001411021202e8000480c440b40c60301c00c900d14000040b280ca01c140d042140a034006007003c40c00c15403914a1507070320f02801d01c208480209680d00300c050400500595040316202c07010074141c00d200345410128002558507903011100c110100040c4441d08403251740e074100511102c41040250200c0c1410b02c1c2c0c0c0d2003001c1040300420b1940d01c10304103520160040784247c540c01c8005000c68103040d00d4504400c02c251b4180c00601c0003a0404040f04000c504000d5481d407400d1805490b40c0744030016030401c3d0401e81c1d6410052480054014040091201408040300c07000e00134030f04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 621331771 1250 621330521 621330547
    0x13030c050f012111040803040f030b01170c040b041b0f020609013305271003200f0a0807031a040213020f090d050307050d110d0c05190308070311 64
    0x124404201c1ca556031134440d007001d031460040e54060903054003034035905da981e1811200e2401580c0419280c0c0190a8000a80200c612590003c5400c215000d421f0a0100204000c014620490920381054a520044030714181100305500d1030221a290401100b00e8003000905e0400c2c0185502040e0703240058408081d040c40900055100400d410202c01c00401d00c043c0e60340c003640d03a1040e83c20960041545995510f9101001c00c840801c07a800402c941d00d8030089070300a080c5100280910610302518400d0340800d01d080f000c2c20302c018004403070402d42d200100c1e119043c1540300c0b407050f41043d4014030030400f200c0955000d50021100004040c00e10f40c00049003800282c5c20801712550010319201d101c402c1206075540100d00903c044802c02240c1007003900c940c04000d0072505c500500bc00e103003c0794011a900f40d1a42011001000f52004509050302e481400311b0095460748550f902405e440350360500c0c1d080c0024440d84c0c03054142d081c5004e02809680841d0f05000c1100000d20560103045a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 621333021 1250 621331771 621331817
    0xa0f0206070c0b06043c060b0f0c2b020f01061a0a02010b04050a020403120f0905041d0609010e060705070201020a202e0309120305090313030c050f01 66
    0x10700400030b003c3d0358440600041c010031000002070a8414000d400c41803022409400600b00100c44003c1004842d08400240486000740111201c446003804100c41e1001500050301c1145003407403c440c41140001440721503118448030100780302941c0080550300e20340c14020413001e6a000030003440309074223081b01b42c0d061121403007081140c810041038100c0c042c1d100f50440525041c01400c20405401c2502164000c0d40c070500041d07070094160100e00e00458402c1810422814469913240c040a04000421000d80025491a0b100380121858450690814002d20340500c80c0c4200000c1c0da84128044541404c000a0003101840b50500c054001350b41c01185001100d070303005ea4505500e03520420340102d800d9035044400e8002e501810a42c94001d850b0441807074541c4403c40c881350a8a40c100c044058502c002002490303800a004540b03402400b0f44c018075000a001e600340c80c14500e5100390012060400e52060b50a071070140000c01460501c102c4400d0440b0082c600000b401a5070700503c06026 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 621334271 1250 621333021 621333023
    0xa0b1e06030405031b0309041b0c060b280503070b0c0607050a090e04061e0c050d0b18090303040b0a05040b04120e101e0c02030a030815040c050a0f0206070c 69
    0xe4004001400c00c60180112050340c108041038001500c084004181d41342c000f044620300039464103443d00030358080460319130410045540c40540240c1d544e680d4002605240300317500e41010f240120744404003e0426090500143e81e80f15111251074081014a40b41c05644002000c020070000c410420380003185859100c2d92a06090343d66000e1220102e804044607030040080070304600900003000324a0b00000503046400071460f500f5001040140219050a41c480000c00d10030082d80e501d5401d075410051040d08010000c0c104a4010710401c01e001c0c208880800b082e420000c100020000c84c0c2c110303aa00300310583c80401040c030302555003c525030006030024011542031040551003e01c030b881c90707583c543c0001e000785115100080c0d010b41a0304401003808280d04420f541000e2081c45503140c6581160020010012409140c0301962a002c0c09040c2d48543e0300c2121103140c1e5a1154019640706d030030b00d46e50b295521032401d003004100c3c5003880540000c642004041c8002268010710030754010b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 621335521 1250 621334271 621334279
    0x30509030318030d020f09010908060112030c060b0a0f1d070e091008010c03060501140702032505030a0c03060c090312030b01030f090c0602070e0c0d0e0a0f05060a0b1e 74
    0x2ea00111a00e076020703c55411031003500018000b02d22040c240301400500702c0a80711002441d8840c41e400b6156082409040c01c0702540c0358940300071900c00c28204407a01d024280014281d15101c2c04a40b4000194000000c0c03d401e2034020480c000342171070710414034440b00307400302e4440c10302c4080103080c060100b000501c103040041c00704401c2c41c00b4000801c01030415000030084003c0912005d800b4025034460240400c40214a414114080404039004a40d006014002c25100700585400d10000208101d07002c1c645901c0205041c1c41c108203402c240e9005130700d1100340d249540f40c40760541b000e80480030100032002c0d104000080f10702120f8141d22003a0704020540040900040b030090141c0310044030228103000c5120705004c4020f5120090b6040d40e42070b0344801e81c4440280450740c00030f0383e00310103151040103900800300203036100440d540114029540c0c0c000c16500c440c01c0c40c2030317008815241d6820085c14400c404007070703100b4000c400300259030403c124080c8402d030100c1b10111042c09402 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 621336771 1250 621335521 621335551
    0x10f0f05011e0e09071e02120d021e0a031d0a020a060522031103010b091504050714120a1d06160509030303010609150e090402010e01140d05040c05010305090303 71
    0x400b0b03000340c040048003030014110f0102894028002800c0080e40181d06601e050340f10400d0080c607102042103082c1028800344546060640f010b181c00960044140382464441c00719401c407001041c0004201e503a0b19554041400c041860104c65041c518802c1c61010382e012035407000060315410b20340d604446290500e5a10ba8000342441c0b81d000201e40a80703180004180004000c2140c100201001880183c00810213500d120061000c15402a5902e040347c000180d20196545826001036074044424031b0252040040d2120701c81c071640201103440c1000131400c0c1001080c0c1528030404007100002c400942c091203009401c10b440701c44c0a0124041e0700c0c2210f071400b554902134002c035250040007a0072680d480d03035190001001e50445000710f010b143d03e01645c08100502c600c0c140844201c0043c03030030030039845560054070910150218541805080e40004542c1c0382030b075014100c40242d10501282c0f44c601403418401d1160140c000d98141480c0c02c003446440e1500100341c80e441f501a400c0110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 621338021 1250 621336771 621336827
    0x1a1303031803120e0c150408010609151a190818031905090d080a08040519080f2101150e041a010f1707090e0f040308061e0d0803010f0f0501 62
    0x20170b2510074445990007840040064401c3e6280f18000e00407242044004c0204680360b03103908081c1e0380d504070107594490071100705000d60004140400a98000e17022000d00d07105e020b411500b4001110010800031801403c2000282c8200300300e8030412482ca20003852070200500803502e07101800203101010040045072605d4140c80e2500c41c807541581100d80c00d40c58017108030b0028200d02c070848003250103000f5044901c140c0710104421034021640504081e003080001950007400d030300143c0350004014510f00c04c0700250701002c004c0a0207006079141000003407201c41005800c41b502c0301e10a40c0a1031500384034403507200a00c1c1c41d81201135000d19000d85031070b4081030b01301c0b101000c070440c10995100f0542401403c94012194504075214411020070903513420800d40684042214040c0100b107994000480318980a4148080500004455020300000401090340300300001801c0310b042c0070000050046481c20a0814001c190580034240312a0a040000788520f07400541c113400d000c54004414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 621339271 1250 621338021 621338023
    0x3031d030f0a080421020619020102071b14010509030703030c080f0a03141e040303022d07020301111e071406090c01090b040305070506071a1303031803120e 69
    0x1807401c004a100b1a03002d00d5032818200b0342c40d80300303101d002144846103a0034101080081d403000c8850b500241100c0c200960b1680060120f6031107105081155402c00c2800c1c0020141c103048c864003200e03001c40500e85420600e03070345580d8100a006905001040c00581d0a540d00020020240c0b035151a182c401c0350110310f06a2030b140140c0540e405811408140040c1d0640d2590000b04000c0c080000b024030381d1912059010051980784190002d01080300c0001c0119019400819102c581d0300009003244007001e00c02a4100051103802d6030203100014403a003035280c04d010b6070590301d03280d1040b140780604079400c145002146400488a004010900205100198244444541c5c1e45401c2c0c6415241490b0a0313500c07890103011150200e440301b440490074042c064192021340f13a028008041d083e0810007080b80580200300100e9030000720a00105c216001880c80174050a8030310015040d8100514004d0144e81311200d1420710401c4816543d001310754422a2488214080301000450061414183e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 621340521 1250 621339271 621339283
    0x1e02030a0803090309031c0c1b050a080c0307050402030c030112021305150a0e010807060c080403290a020306100810210209090606061902150a0e100603031d03 70
    0x140192401100f00030140304048001c00790030a08409950400402025040c4024540c0a982c40001d61061080b0005961072a481d030640a001c005245030541c0c4000054400845401205581d0000d000c008054241000700030094401290154110314285c49540054041486a00c0300e094206140304103540380e0040700c8918501d101401d2101e4544403000c2d00607102c1084880b80070f001c3c1d60f14002509070105034158140d80d20384010b0040107150043c2290041c50025040c4c404074001c00001000905043e290001c1d5080146d07610b402503496100c051480c400145180d4440d0700400400c0711950f1640c1611040d281c81d82800302c01c2e0b4407540019103544262760410031400030208540040d0851840c8a0540d183c03085950743c00390383c0c1d0014015207032541600d4141d0080c01c03d0104202c0200058445494a98030340304645001d0f039100341807150310b030080e503c04c0540f0f079417a120380c00c40d02014031001c0c1103e0312420050058500c1c0d682d008107095180410b0240404980307001c01aa41d07024455 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 621341771 1250 621340521 621340523
    0xa020d0507110603040b150301050606180a080109050c010206010f030b0a0914061015020a05070522050705190302160201120207061a100906050307050a030e0d0c0c060c1e02030a 78
    0x40f141d100e140501d8070a9045506464005e4011444406032146190500903184207100c0617100c54103050800721070ba88862810140a60b208c5807403100800c04540901c5030483c0540542c004090b0500c0200000e810700c80e0603001000c074440400d000b40701240d00d100e440342d00060341d0703100000d105082c0c0c103082d070704100d511110340c001d80034407414080452a03200480b01964070304000255802d01000e000d036610141c0f40c20050403030300310030010003c9150651a1561440d590140c420389016000100d9045400c101c580401184011604c42d0705103a06172150144040c15050452801c400b42d120001c0d221200b86000b410021046040d411204260f01951320650340610b0502c201c001c480c0c2503040c20780e01c11039094003800002c01d0720806e8510400d50300c01200c00c161503542ca0342d110131314101d030386500000d00b00081c1901c0307054044003e8001c00c0360000c1900680d845d158400011702c1e00303010200e40d56000d081000f9644d0299808250311142e003042e1000100301110120015101203814180103000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 621343021 1250 621341771 621341779
    0x50105192d11010f06030213090203030912061006050304150905030d090302010605040b0a2426090106090209030d2304030b041b261606031409030a020d050711 70
    0x2180c1e0a142c018100c402e610341034070020700a24541d05142e2040b5445480040e41c010100d85c5608000714095000d00e00745d90028080e02e01d011443c40200310f034414a554180311550200f0b04001d100350100340c242001d091180350880c6507052031348440542180c100040d4141d15075421182081003030130012141034031051042031201204504002e4021702c403d114050049080070420030841c034100c020141034816165002203804015564084183e030230b00300c4002031106410148140c80d0220800003110030b4500c0000c419440c140d11700c1429100302d50312080e0310500504c2001e01c15a8081054101c20909280100540d210800c88007030341d4081d1000307000400000a40401404038403529940304500800800f100440a042c82c0d0a0310700d501d10810403c026084035100d80e600454140400303081482d01262035034011280801aa5145a4446400301e48d880314403003000c01844052691101a55020354141948244c000e0740311000c41d40c07084200031001070500104043e4104500171400b01030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 621344271 1250 621343021 621343097
    0xa090e100f020c0c06040506030106230d020a11010501050a051002120f03180c030601031709130c0f1d04050408040e0903070605090a0f0b060409290105010519 70
    0x2810070030081d480310050000c640500d548001c0c031420b00034125000c8031009400e29155070f180441c11100f12001003054906003000e0450102e005180310b02502041100307040040c4d542060141c007a1840000c0410402c081c1d041500411190b502c80050302c0458805403001d041010a4400132400d00740f2401000c24240c074040b0300301413028260406540701d5100b00040d10b845482e0b00c0c2e07401d555805501c110a80c140d011100520016010251b000825080880103d00304000c180000d2202d41130ba01c401805c032580c0d100342c000d0807079003e070100841041a09040d0b080074424002204c015005000060080c0d0300c40020404200490003100c00a019000400099080400c005510b9034413580051b52200c1c1003034081382c1c7c119004603d41181540c44100d003040d880d81caa40745154040001c01c056805a512903c03140441c803e2039410032040c4081840000d81c24410901002d400d0068120761304002c13050000c046001c0e907411031800804400c3c07d00c1400e08081828000d03003a06a003800c400050041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 621345521 1250 621344271 621344291
    0x803091509070609080f0c0607081204030815040213051903020315040524160504050d0b010503010c0c020310020c16090c080603030f0702041113080d020f0c0a090e10 73
    0x4030b0200181c0300380d5942c80710b086036201d1820f0380d00c96450300b096410b0380001409066500d400d2000f00000c5204600c8181440040c5d1180405140304482c02c4d404030701d000c01041401c2c2c540c003c1c0c448400c0c0040f141103084ca18680300e480000c04050042c6801580c49031000344613181c214150100940d0300074211a00079501c0300700800340800038cc50031989441600e001084060a02d070001004440840c034580c1945d40e84044564000c488580007000c1c0401000080f0b0191142640e09c2c141500035812a0801e52510052500310785a0002c00820450030711820001660301043c054240d085011015840303480441c40389017401903040c60030703400509400c1c00151901c1a071300514201c1c14982c407802e0f01c90b030301d05e01815200e01c651039601c100410100701e00401840e16138010400c144850940c5410035100d00c0710703203420301c1c400c0e0130803030a55000b0041c086105904101d081524400040540b01c000d030750002050a0712154000ca91040e615041d19106c0da0b03e08009140c03a081e54074006020500507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 621346771 1250 621345521 621345523
    0x70c030c120605091902060703120f06030c0504050c0a120b04140f06040923012007120207060921050a030305060109060c051b12010c05030604050f06030a0803091509 73
    0xca604030741c41030a060005003c0b0f03001050399649061051090545d540d125400c010641d8003080040f400d00400248448440c4807a10a0491a41510200080c410300318181154413044680c40f8511881c04c100400c003400c6000700a880c180003641c140740b55250205028100a02068000b46030002d140500800c0c0320156a445103010310800030b00400700707465590500041d9071619002034020094000f00b101000303030f106202c0e4901d4107038134000200d056041181080c1a442200c08a00808001c6030480903c000340c004802090880d000400f00a40303410400341005491b417045d0086501d64240400c82c904003000d104c401d9540c00015035080d89a03619010300103100076660640091000070003c0b409500641030b580c4869003280040060310b822440d5030f4400c400b1b410349650050852100e074011004240100e8450342c0141c0c4503d9100e2801400f80f00c1203440044c00c40b4070740c035040400c3c8040303600c000c154a910070340c1144455030f99a42e004a0b032447c0c0380c0790540c691a0046200c00b080780c5220 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 621348021 1250 621346771 621346799
    0x20f0a0f0b090105040308061903291f03110402040905310803040b1b0f0c0d14090d031808010e0c04020f1215040c020c0301050601021b0402070c030c 66
    0x7205100018003900c841040500b00c400c21070303000300443e02e258045906031406079211004012804850400b0715129a1001403047c3d0402120f0801c241009040107444900f08003d03502112907111110a0042e5818141081c2c041e48000341142102402d181c034142c43d1501211302070100c03400d05000c01d0900e040d0000c074500e011400c00d001680d01c4003000d4542c020002c087c4200c10307048955641141c8568907900d5982001410b145240c0310030701c1100103034122910280c44090182c0c0344280d15007843c001c0880c285060211001c0030041130503201c100e070703107000f03410f2390f15040003526112194803603440c040e201003150075002d101c541440705000a408005408c612180c01a19040d01d03140c02600044c00103a00039030f0342c1c850100c007052008400300501c0f00241d80d0f2142040032038281010712807020500702c1c0e20300c424500c01a00007640c1160241424003842d900600700784002c01d04401080325003122a04001d01552045070009459801e110780d0815540145030014100c0189650f5008003210800c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 621349271 1250 621348021 621348023
    0xa050304020f01081515090301060b0304060e0601031e0311010614031207020f100306050d0b06040c0f080a020a020309120601050310021306080a0f1b1206030c1401020f0a0f 76
    0x642d0480041d140d480b585800340215198180c1040c669100404c01c01400204180c2001b09071081c0481c02459409000f560000c06003204969682e0800e41022016122003044c120b05543c000f1004000103018140003da14510720b400820001c1642e1600b20f460310744255404072035600341400450711040624101060000450842d0515240204908100d0003140ca02a511140064030003101e402e1280d42c07005080010f103000101d0782c2e00d5500103480d90010407015100c010306407040141e6400c01b8420107a07041c10500b08034000301c203050310040044000526149456401040301d507045402003042d610200001000c01c6405480103004a070703030303c1c802d108003407181c41078140901c8a02c40c180300320759811980f20404080701d4100f260940712a5005000007810a640f240018915406c920441c0511101d04500f0115071003506c8000b4001c00304140756141c2d0347e280c41070410000710902582c0c1d088414840180d0710f100c1041c40140d0a00c11281c110641c14000c860b8000204248860445c06031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 621350521 1250 621349271 621349279
    0x1090305030601092405090a03060f06030b13020312220b031b04210c030f050606010801080309090105120a050706120c09051003110c0f010605120c0a0303050703090b0a05030402 78
    0x20a070b03601d16004039070b250481d01c851502d03200c207240b9045920500040c1f4030300300060030030907005030303684d075080708483ca814a000c58280d5194014010411a040c00344d030001c00c101202e001e10b05458002a40b13a10603201612101040010f406002402c801c3e1000389c24800040d003030105a5540314000381c80e50088540302030342d0420f1800c15030072503041c0c0300740c0301510084041c0041104115031030784554203180c40d05071088081800c0000000e902d1001c0014010321a0015003003074284100003414441041e0400708041d08103020000c029122410007604455085074041e0341c3c0c600c08020740d4240301102c1070103032030340c041c15001081d05034020b040031000504000c410003001c08140703804c664200a902400b80d00880c407a420b90511032194119104201d181d5001602d0001500c4d40c807031801480d012441d2a070394480c18100040c2c50000c10110240910201600c07230b400071400003c102010700e00000302030100c0460b0801c01d252045442c28094042e601c0501d1356101c07600f401030140d42086801b2403107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 621351771 1250 621350521 621350537
    0x1106040e0604060f1203120219030b010206101404020304020d0f050610050108160f120e011e0207020d021002010b090103061b17060d030c05010204030b101a0d0207080c01090305030601 81
    0x51613462000d0040f43c440903202c6101a41c1036400301da030b1003902400c21305802d80a00940d20002159854a034821105460000d0700040d10700c0068103100e0002d200507010038015400300111402c00080e0030400000b1031300181e0307a9940e0f00c0014215042c18401410285851003284200040001d0003400b41c03081c200d80070102c1756100011036645030100c0c0c1c440c0000c0012080e0508940c018140404d488049003450002110f10203a00d60407900c00300c111a6807a03446c0c0d13014100c0080900100440001c003100c040d49048083d801060080141c048002e02410080c0f00000209200b90b00c50307040020700404140e119603407030400c41c0c05012009a11680c9181d40c01458240324018074000000740c0c03605840310340750750f078000411034504000702c4280d060000419071280020020b01c0140b0140d80300320300c10b0360720b0304010484040c052100d030002d4049003c074541004401d10282c094650400c5800c07409a03403400145042c0c0154081c0c408010b00c2c0d5820f18107a0010141c005002e10305c1041c013a81c603908 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 621353021 1250 621351771 621351779
    0x161b030b011202031f142502030702100c0302031303260313140f0102040b030f090d0e04020f190e1201020a0c0b090a0c08010902040f090302030d05041106040e060406 73
    0x200c8080d00b104000d6041c0d00c1100c109002404246280c0c01e6070800c0100001c82d50046503803030005902c103c98100c000c5002d560301440038510b201d83c0d40501c1c0d2440c4011820000c256001c02ca0400c2811445001d0000045001d000c02d40300304121080e801d40c1e013035209400c0350344c0c1c9041c2c0600c0321002001c01614505040400d01c03600c485065038410211041010941245a124520300321748070000904c940c004d0b0401d54109000034001000140740d00400d6594a1400694030066483c0c080c11141684d00700c240b020707a581d580602e1810b50f503903040701d0040c0d440e0440f10280d981403007030b03004507140c03514640d03510445903030002c2c207280081405076005480700511620b59402c0f0300c507545d21000481e415171034440109a03440c052540c0318420707000310f0340d038001c6e143c40f040c001c0300f4140d024442980d114801b07082141441e00540000803505101406014521f50300a900c0e4003501600c1451541c2d240000b0382400415051400701c03000160203103683d0798030380784d8240d4828401c0f0b59041c003c0b402e00800103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 621354271 1250 621353021 621353039
    0x20c1005040809090a020412080c01060503070e040602030901150305010c0906030204080d1b1b03050c030105010e1f2408130c051525031205090d0302161b030b01 71
    0xa12941d40540c496141500d260b041000e130b8007024001082d855800d01012408031280c4003014400b5008005c01303a01c840d0102c10250946205402250080c0c00454003003204a640c40c3c000c82d00540d0180e009a140d568000e0082d0040c5400d900700410028011400014080d06500c00310600c0941e0b96020082500d88a080d0164841e601c601c180c107501400c4a1451640b0035140c113145400710210b107100b03200c0162078122031004240d040c1c14202c08020020010088204890003100d18150300902c940d42c900240b4454644000717225503403c01081048540e200f400d0041c090140100362100c5a0900c0c03142d0100500a40100c4240d01051560b004108104d000e240f02c681c0c400d81c007409892483c0d0410051220140c0c00f00c00d4200712030310034402048000e13035044c01c5145c000e03480708500020701d83c5403c3c01041c0c0303065002c208003918507100900403205d50104500c80800c1040c100541c2d214507000042040d502c252a000d020803207502c1041140200104c80e08044034051412101c1603601d0312890 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 621355521 1250 621354271 621354281
    0x10506090c09120c0a0f0612140f0c0c0a0c080c19060509060f04030302010f11161704030b010e07021e0705010c020d120e010f1704020d1113020c10 65
    0x1008034248203120001e0b0a180c00a240304407182a036080d107100c09a120086009514240c100d85101820b08900f8032100340d100d010003012420500d01403140032140320f1641b040490150801d221400b0860004495990500c125001c0107024400c81d40c20700d0041c10311415401e0140100c0b6064051480d0701c4016151403951586828111030f103c3c400136141440c00d5426a0100c0641c9030450b000344030b00c0d00502c514002a10007940a44c001141503442600c1e008119500c1c810690764400080c17100e050101c00d0b1203c83e172501544260200c40c0c0450049002034140100c0d8402407882030a0710000c18660303200c268660191180340c0032242100440c040c00000084140100102580040b074100703d90761040329108038540c00a8083e001c0801c090f1034040c41c0f0700c420103484000c079810000903202035030300030b2a10f01081041d10b80380b0f4902e100c601c1505031a50010300082d10409441ca03a4505214038119070802c201c400802c020540c2403640c20b900081c0d006080d039103005000e9800d40c5250382140f8028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 621356771 1250 621355521 621355531
    0x907030506010812270a03030c020102012901030507030b1003090209060405070f08040c12030509180114040b030f01061e0b03010e0a0f06030c090e0c03010908070b04030c021008040501050609 84
    0x26075041c84580c00c4518090203054880b8114117064005e001d0079925507040345030141d03009030b4804403024800d0001a00790341003c00c580c2440c0c204010280d5045001d40d007009080070007441c01041c81d4881503011030192114146d0b513503002e002440b0300d00003140c26a102c01202c07031003520065016590b00b800c020446100311140c00100e56900d06d0310141a100e0f000c03072503220780710b04202003040e601c6004480b10b02e00d180204402085000841110902d40078142c0100400d544403403078420360410200783d89204607a00300900454031295604600c0d43c060000e050b0f81784141c8000c010b49656410744005910759419200d1981ea000480441c0d4036188008a90580ba03018103e5a070a442d22032100000717110040c20704100340d903901c201000042c10b01880344002d06001c0380105900c000103844600b06011040302e14401ea00d8140000b001a01c40c3c03050741d0b07056800c03c2c1e1500c080d070303139908080e03801c136404240007540b002c03040440603ca25007018095005500a8000308040d40d0faa40a2007004007050b12 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 621358021 1250 621356771 621356803
    0x1c0e0c0301050f09032b09030801051c2f040921080402011b03020f060f01051201020c1b1201051e07030921050d090f02010809070b0d0908040b0309070305060108 71
    0x85440000d08503103000840f0806c0c00303508610040c040349207110464448101c124001040000100000e24040c82e00007206401b03040e0400485180750b40d00c6d00102c1c1141440b20041800e0340940c80b980070300501c2025012400b800c00e1140c41260302c1c1003221084624203007292203405040351315426200c2c0c14407034440d690607190000300364002041904070811030038044085210780382040c18480810300400e07008900070784030740d0103e50400040000c600b000c0d0000980e168814000d0f550240800240822800340c0391002030368280c031900205108021039080e810f419800e103028030504c000f01c9030070798440ca45003d40c0d20119480d41402101a142ca0b503c1c040c1c0701e8405c20405046801c018001144014254281039250008a0302180c09954070464140c030b07c1c1503120107010541d600601c80075404003030503019111480c104000080240030316060a190640d40b00110800c002442c003c60f0003410322100041d4491a0401899545803c18001114180682c03c0005031141000414015003d0000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 621359271 1250 621358021 621358027
    0x815120d030c0c1e0f050d08090d2f0109120c021903030804060b13090812010e09030d090602041a090406090e031803150702070911090a0302061c0e0c0301050f0903 72
    0x43c8680034144c4900010f03030302d2000d03d004503c0042c00c20130000e02140c013a52280856031a1105a16041c604049070440c00d01401007030030500d03d0441480214442e140d20042040d1815690400d03004003005480204403040d20890800f400d9045901d60401c2c61007128005128168020b5020803009684001404104404040f400080307454003e1030100c00301400d245091052030b1116015145400d60669410070002442080441039048030f5000d001640c0d002661800c11b0703881e0380d0703407031040071401c0a5943d0707a41044010886160110790040c0001190000042403281050465038011031081d03224500e00306c0002070410550084001c0706010b1006182018010b154441030540e07542c40c1c80e541170080e81c1008191440c141811401011079a0050070309604212805007100e8061042c20748408091003440640d035108440101540c0d416140a901c17031240481508220342844094444107043c903100b0040110000743c1d0748104242140240035584031034009400340c00c0d06a07400f0405030020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 621360521 1250 621359271 621359303
    0x10501050414011d040c2607020a0b1810060501020d0e030d0c020d02040908091002060903090d060b0d050c030d0504050f04020306032404060621030815120d030c0c 72
    0x140304c0f10807a116244840080c03411071440000c0c12107203118800d1020445020000c0314002a070640e4105059018061003403500384203201a542d0041004005c0458482c5000540004080700d0b01d402c4d000045e0b4100c4004109101450014110f540203440c014495102a002600d11404800c205514003401400107040800700c1121001e28040e810381e000803101e207503031005854611400b4a85801203c2003500c59981c801040340710f04900c2e0b080421940b06000380440c00fa07020040700e0328848101d500c2c140543c000c0c540003000d45003080f6600d0740082000314000a004c0c02103004072440404138207941002c40c0240d01950b840c080c030301036035401c80108054007034241026802143c01100040880d0035070007410851400900109101d0040c89001800744010803000e070180c0c102074980b0346101c503019907030072058161034108680060108454100070031040d900c3c05800350012840508a844030f403019044c0c290ba5007011502440000c1d00c0c003115100380701e01c144241406240c0c40b115000100c1c0c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 621361771 1250 621360521 621360527
    0x7052812110c03030f03040204050f070207140109150903020130020c070b0f0909010b0f0d2d14010602120403141f0c0915020c012a051501050105041401 67
    0x74205801e0018410700c0340001055500f00098408500200c0780d0750b03924545441400151503014000c110f901424005002c615034000c1079030700540d94920400c0005240030b00c0129081441030f80075201c012002e6002c0074480b580b105054064900070307250410051b80b0402001a80007002042c60300300da41039040b071210140140c0062084c08100000c03038401907121a046402c40d40200c850607a16940041d5443c004c2c2021688140104004444c15080031040000424544681d0590300b40c21507942c3c1030703100011541c103511241024400d00300e15001040a401000421503201c0c41e04510300710400000b80c96100245203604c80180ca000e40f070500703241d940ca241600c000c61b1070024550141c203d030340104501c00c480c14080c1d04461080400d0300318036800060180340644c0c104008040d520643e9035000c91b000901000081e0003803a16070340c000031303042c015203072b001003c001000c9c0c0d2942c14201c54144a0006a502c412428042075211340e0399031034006498078810340c891044c03030f01c0c8803882c0d145041d80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 621363021 1250 621361771 621361787
    0x40e04111f210606020706020c18041b03051e011505010c08030912131e0506041403070305010c2a03090e190903021605090105060403060b030a0807052812 68
    0x10001445421880302c0d00a2006544103a00b084005a01150040208607410000d454030000c05079540150ba2100d034040340030081c1e004101901d20510010b001d103412810b4482200195048425940f000020a04c4404101e0030f0003c041c1c903640c01c003005000700d00c540a1120084810503114404501c880365200340071908001d240304010f024103110451501c0203072004102c030001c402d00000d8400d00f0a6036054102803103596140100d0700c8d44606111903100c1c44200c8043e40c80d08001500741c80d80000010f4504503081c0c2000f8001d5092038075401c0c13581d82010309041030b40c1c14141103801000d003c09012128074407034680170f00011401d480421059904024140e000020408a0344a8072210030610094a201d5001203005901807411030070010b400813020300c06414210340102c010352505002401c0b1740203501001c1c00349a681d0f0214020741c0e50410101c820180e002c0001030311800141007180c0c880070034004100d01e030407414103510400c55405101e400402e42c8400c01c0481c1d40035404049036000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 621364271 1250 621363021 621363047
    0x5090f0c04030611090103060e310203030d0f06050913030c0c032a0603021321170702040c03090515070932011806050717040e04111f 59
    0x196007000040040f56560061003049002148290750360b81000d0001001c8409a0b0b000f5400719040900340b1902c80c0700c10144045003154217442c40340b840030341d018905045c40c88440c000e602d840300040142e036901c0c2d507401117a07841c0012841005603940d900c00f40301c24000100d804102003a0070059100000b80145c006000c41da0280d86071401c00e03601c07569036410984c4070043c900704e20381d1710305058050703010040441e802506440c503095013415982e007520354001c07845001d035003a41210b50100c40034141c0d500b540381208940002040c910342d846240b4540d081c3e4000d4800380c1c050307400c2040d0030190301d00a000c4e03d4060b03588100100440a00c1c203900c40e00d41c0001400391000c0181003000011100d03901d42c8001540101c0c040d000400da802200c49240800c0d14280090501c51160320400320880c0d5000d884048803202d007000c03680c948103480d05004101e600d8030710034a01c110200300484d2441d2644880b900c03070762081d108042c42080540070403109100c00c00390040b400b0250812610114170464080401c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 621365521 1250 621364271 621364291
    0x309030f0c1502030106030e060a061a0c010e03070f0b0702010903140901030b1207091b230702031912030905190501090c0e04021503010b03010506161205041703030105090f 76
    0x4090300d502d0b081c0e90007a0b00000019450700f48541c20f944061001e27a41007041c40700200a82031400e10406520f903400c02d41c040307035005c1c08a0744d0b560b010b2080d04180c101030f04a0059940d42c41c02c92034190b156540030701302614200364080000386c02500500c1141c00c001d403d031f268125007400c940e046103001c0d0f05c562041030400d600e82c0702d41109920303016110011410b600000d40011030400308020111a0040618020040380010202880e5000002c15500304900c3c00c200d1019440314145060030301c12508029058820b0305400340d0120046541e4a00480c070645100d000605644811800d403541c40300b000c2c1403a048082c070038000c8028140c26204540c400e00001c01c0c0050b498030f4801c5522804e034403858041042800704011442c100010781101c3c0018a000d60540d414618500880d000c140992802080f0000f001c501040340f80d203a5400503640103e0308907100c200c041004203180c02c64885c44030f40c401140c4581c0d000f65008402e883c10f0301c0c0042c0001040c3d0352940104451400301800d16242 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 621366771 1250 621365521 621365543
    0x1c02010209370b0307050a2a1208090c060c10090f0201020142090203040c0512030711040b01030608120408100c080f0705040819120309030f0c 63
    0x1254030b806040d510000c110800141d08415a07030302401c41c5422a10450340000103010040c4100e8100f041603d40010161a015071034030968041612198030011208141c96140c1e40c90f4500f408200c0c4858071201c2c45000706002c0345107821000d90f1100c1060700c8200898000640e400c005e8208800501448442c610440e4400031308040120115103445505558031120390036000250b5809000d51000036101840803032210032251050b00100d40300440100c107100403000802c090b000c55540c550090074490700111f507282014174100c1c48101d501d01c01d84d4058200311000c0c803400390000c401c0d5030341d550300040d061591003000810071000300003840c00300d410f040d650750011454810400620390745c02c01d131035000390f500c60a180b0b0291618216100110310141064108041d0542c080b05030741d0030051421031031003151607084090f40ca9000b10341121000340710780103a0740c0f00a22002051300312a400380c0841c8a07501c600490841c10b03100442400b4010507a810441c88909114006135481c4600500b05a68 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 621368021 1250 621366771 621366787
    0x1a0a031a1201060e0c03060a030b0406091a0702071406040b1612090e063a15140105040e330f0f0906090d0e121c0206070503091c020102 60
    0x7001400150503240c00d60341d0f0310014000c460401d524113030040381d4403035420304614020300003616414540c0802400b14104030081810080e131500001c0e40d0075070024000409540800301350002e6a0101c4204005201c0d0b400c0009803240551022020244054091442d05080c011401c149500c80604d050074410004000170202c0c0301c0d1503503881060038a944240380c1a1a106007407807615000380200d0b205a44104d086403400c600c503846904d0340300f00c4000d5070b072a0100259180c50b40d801c0d0701501922812004a40300018441030380106001c089800741c07500e0990300e403810701003140c94285400506500060303070000851030746500300c11031880b10903031310524400c0c8070300360f070340410094841c1070719003180000b072042c0d81100c2061640e0140c00c3e0750040856161107400716548000c400d00703440501c0800565004c1c15101c200c80001c2c2040103000301c0701c0d0760030720000940e1002c007501c00340001402035a01141e4140e10a1081307a00502040d0003d00f580610210301030b400300324031f00d2000c043d59401c010302c0c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 621369271 1250 621368021 621368029
    0x3080306010e01090f03030323190504061d010b01020f0610030f170c1615081f03061103091603030f051309051305211218030313020a1a0a031a 63
    0x5c2c00f941c8030f540d010a00140520203280001585c2e403070b44685008400400520b40d044841000412123000030220b2070b034031581007a0340185480d0f5070300c40c10540044450514440150418542182c00f84e00f111024000800115152441030f01c3c0c031480d001480c5010400f1841410b02a001d090082d600b0317401402424001c546154070038007131110f03560022002c00f00d8801c0c030103811800900c2090031140344000039640003014070000611f80741c80501c1e5a42c03140841c200700c25580c0c01075039000c002040018001d98079004541c00807105685030f80b1510240300e88029400c0302500440c3e038103072a01c880030100888103840a41042512070b000c843e01080c0000d000ca000d015103402032040030613441100e0300781c1c18a141000444180c1072411914848660a0700241c0400c60360303200c1c0c140c110691291100c0000302d1018981958000c094032021040c03025a005c07038404107042070b10803900340c8002640c841da2082c1c5c1c407480f907005692040d0305000d65005980a90415100c1e241c000000d090000c00b80c2c8005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 621370521 1250 621369271 621369299
    0x6030309030607020a060b0604081c11010c0305010306060b07020603072304150207090203100b070507080727090b010308071a19060f080607141903050f1003080306010e0109 76
    0x3d200160312a09071a8140155131045080c940c0c8299441d501e4103003080310742175407603241d003a4001280d036a500da1103101c2c911480183d000008883c00a0083c1c80038100c00a029007400e000985644e440c140c0000761040220003140d00041d4003500050840d91411000d0b070742c1d82c502419010b1420480041051840010f42c0248050700d0241c05454a0070300307003880240781220302e800c41303d51503204006210099403048816012241250b04413542c03140d00389000d40c108001984034904604c40c000000c5042c46a0004044503210141001c0d848007e003140503070261440c203200a054401880018804542e07050300410885000c1c9403009081c0f00342130b1007808200301c126118030b20760f01078841130803001040d4001d1900070310302c40d0a40a40303182004200f540b1484080d01079003d05c80c10b00040000380681074162040803032820124a01d240d4268070150280904030741030311015201d24005035003a802c013a0003000b40e031b820503061411996800c005582215411a0150611401c0c0340c00103076400c2e40802ca = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 621371771 1250 621370521 621370531
    0x210203090a0306020712020105061c0c170312070c1e2103050703140108060601050307090b0c030d0e2a060405060711030618030f03040809061308070f031505060303090306 75
    0xc01031752032403141465021001040ca4800c21641804184041c0da502c0103500b40151003540354800034407a180c50700000c0c420710b40d440300705900e42c900d181c0d05100d04003202410461704441a80a80e0f90794060049a900c5107910008241e5094401010340501540040d074000c3d5109032000c0300540000c8d07800100301c160042401001079158001c01c2042503050007038a1410121180101c03c84d414651500e0320356000030189810040c0120004081911916020006014401d2001e540b049000e01141d00c0e42c2c03201400d1140c075070070203d1009060000190701ca1aa14420710a4031003440703810b80248200101c082203a901c000140008903066a96000800c4060300c10415440440f05279805c0c07604080d00186140c1004d4036941c0440d04100000c0112150512840c3e40d40d03603aaa82ca18040743c040c000c0f400c00640200340840d010341d189030821400815030700315208489441d659070044100700c00c001e01005000b901c00c003840d00004409038126580180005082d80d04015526000c01d20b000021a0703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 621373021 1250 621371771 621371783
    0xf1b07030c090b0a120203010207080c06011a040b031b0408120d1107030503071206030b150310050c07060b040f0513110a050f090a0b0a080d0e04020403210203090a03 73
    0x5040081101c1508440002c181e28030051140c1090000020902d030715912540d03078407150f041c00020071541c1c294102c5001d254454a21034a9075041c194560350f80340c0074001c07665021480c00052400c21500c005460440e86000d0503580707107603240180c000205a8030b50030b43d0591001404085001042032107400c0d6a810b0200c60140c031241d003a9005000c0d6180603464205116007000903001196100c41140d90100c21400d145581d40310f5600c0850082003180c2c00680191004c00602103514103006038200f0404c400c9040b103d400070361907040c0e012204280c0c1c00031a0034a0401000c00011400d40090705110300040002980c1c024810761481030711021038608001846000c40c80080200c500742141d03210100351441d180541c100000304801452101609200702d0340c102c0003d80d4808141c100040c1120080d0a079031001d50f641048564aa40001426000c2001c954030136546050034400d407011a50045088078195407446020202c0c0380c0010311460440c00200410700803070721856624001184148 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 621374271 1250 621373021 621373033
    0x5070b0d0b1504083406080117161203112d010507080406020c16030605180a152708120c03040b1b160b10081c03020f1b 53
    0x1004540030301d60801101e071034030a002c140440240000d1a00b03008030804241d2021001320b00f5010a42d091540d4540080201005c2c0464400d9024000c80c0c100c40d2008805c0807000200e1950a841d0303200401080f01c136842e282800c0080c00f505000074541203000c1d06081a0b0a14001e081600b014440c42c1428030030185140b011807003120703400300c090324080010000c0010f0f007042c100050940d100a04058505900030441c2c1012500c1400910f110110035040101495540d00c0d140000e40b4040760340d0612840750f58208010104081001d65280303038444021000102440c0503c1c2c0140040280301006003042a9000621041485e03c1000f450140755500d0704c51075041e0340e68487c01002416080c2c000414001d020004000342501e5400401050018059400c1109801880e000700c440540d40014202e101034103110414031203500981000500e2510251154201660340119440350800140100c5010f1443c41c420343c090100a01c0b0a079030589008071a2000000c10f280c48101c6184941140e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 621375521 1250 621374271 621374291
    0x108070503060f1e0a060b21090a2303130e101a0703120e03070b0411012c01020a0c030302010c030b010809030f0c0a0209011701060e0f060d05070b0d 66
    0x1003100a602c00222182c2c1c5400e403402c0b0700c1000d60200d010100004c0400e80a02207030100345150004009032103648441601d616048111103080d03074103400c0722100810104042403104801144016102c3c5d00701002446030064101445414400d13155550382d503000920403201c0100c04942c5490040c0617490b00b071445030a00f00c81030a04411158040d060310b0000316242094400120140c0e00d1480d0513081010b1100e0b88204038601420403211300b80440e000001e4050304205545558900907400b81d005200b11401a1005440f000c450344c0c0c0c00481c049240c5401000c1e0704052070840031841040c815525858a165104480414181c10490142c0d44a80503080314591600c9902d055450074039010349a81400c0d0b007010f803a842080b81220342143c0004218900710b0080222a120580c007070701e14440380d0b03510101182d8106800f0304124255003800e1000527290034154209000e8004490044402d031146000c10003030241685003158680a5041c0001d40c5280c241c000d0620304861100c00308140300c031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 621376771 1250 621375521 621375523
    0x1413030e0301020403030e0108091e010c0e1005090d0503160602210c0d02130b030406061703030408161a0f06010e090c030c0310080a0615090902100302030c0906030108070503 77
    0x301115900a0b0710601007080444d51040710520003140070b0810b0002d0791208601c86042c0300c84d0f01c003c514541c0a100d06001c0880b8154058401503006a40310085040004100540301c40c45001800004009018a00482c030301548407043c541e00c62000c49280140030456400d0103040000280c82072640498110203122480300060401c0303480182c045130524045410544a000d180c0d40810305550104001034607014015580f0050011903041c143c881c60320340390440203001c0c2801401541c25104008802c4060000284c030b0141c2d07030140301c00d810010f90740d040b02403603018010141c80c2c254409440000c88005590001c1c018502003c0c00011443c0c031074000340a515148114034041c04148081042c105007031019282c0200f80c80200c65620340301e840c5203840f05c1352142c05c880500c0c010080d03000e08000d415070202882c800c84915500354150350303485100890340140c03000380d00560410494440d0340e210750300a550161400320284e0a01030302201040310798000340c0102005520002050017280b41c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 621378021 1250 621376771 621376787
    0x5010806060a1e050c1f0c0206010f030305090402210103053007030e060a05030108060615090112060902040b031005030a08040306150e15040e160b0d141303 69
    0x21064581d01c0ca46248440000c04042c0d00f02c2d072894000042d0010b0700c03003c510400c1141c01540101d012112100c222120000300c4151103c0807502041c900342d00a13030310a0000c0b9045040b40c7c804200359100038550f44080c2c940d68007000b0b83d039074401d90811030700f42d44d040c5c00d010f42d07515968a21480306980d8114605103141c410507481c81d1003016408510560503485103020403a405402c1428561144003070724090b07032a4590301425035440100841c00089969210019504a511400865807580c4800c030610480c094958030744540c2000400405195500880362030210099a83d80080c0040ea0303000d5860490704260061a00c0b04000018010148803017800d08004d0941207004c0c1460b480180c2d5280001c0c42503100007040701c1d1703d41108958840400c01104028003400511071075901d0880311a440701c80491760f400c1d01c110b25281c0f02191812000076607542104c45403204c00c186905007580400650004078000c2202d6482c0c185c1412000c5608121602442c40110006078000d031504c0d000d40204 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 621379271 1250 621378021 621378031
    0x706020111042c0c0720010c02240301080d0e090f04141510030605070c081b010906020d06060f030219050a030e0a0516060908030d0b0a081501050108 66
    0x6030401e07034828aa868218122412030314000b0312683c036018142e80d41082e40d0581000079035001809001c0100c000e4110b001031030003500c60196820b01040c04e034030025174203c2d80014030340010a550034000c01801d02000098219502a0318054465030700b02603865241e009801c44060387e04004240402e080e000712511500c504120f820901038030301180c03070030081c000080003e417070030700c11220302c41c00c02205000011410b0316040c0310b07200c00c0c6885405244601c9152104982003481c10703002501484c4200301c10b071a0320307134006c1c0aa454000900d41400d91440058400342c1595642c24035140011024030060148600d120310101d00346140c80d8010b0015600302c0220380030706004115451040441d54401203c0f4181802d01d03070349420030107100720020300407260842c0741c0c1d21502042e1000c1c0000011003d0b040002281001062900c40d0300c1180c400815100e5040c050380144080343c1e04180300d80120182c40c801800409010f69942c0703a80b46019104071100d480c0c01d0341c200c0140b0013543c1c001a01e43d404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 621380521 1250 621379271 621379273
    0x709270c020f0106060f170118320402090105060903060619240806190e1e13060515010c0b0411060307030506150909061306090c02030c0607030905060f0406110c01050702070602 78
    0xa43c50150609c001d807030600380d41c0801a507a142c401e80c45d04800044034041c0030942c030750f421308800c495209409140c42035405034800c06440c00006400c0c50300300119400840c0180103000151100d00500505400791000d4001804400c03001260601b01c11070707211400d0f440406440803880c00c191014181110141c40c881c000c15005d80c59080d0b03204508584001c40d209140600415a01c08900082071160581c180895401e443e0a104a0b10071075090781d09158000c1c00d081001c2d8980c8010207085002c0e100b5440c1c04141114070840c0816059159207500901034003440096078402c000285003640300b101c4440102e40d0781d000780030b013a0820061042260340540c002c1440c010740d103c001101c1c1003009101512a03400035034004105c420340e40111004204081c03091142c03200c0b1100180d1290041e04003803541d4412a03001071f025921034001c0c4581c20f900711f0050000b07600c80e56050032030444006e000b621800c3d1034032045d14038000320000810700d0000b1040002610b0034900c46c004d0038548141d00110031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 621381771 1250 621380521 621380567
    0x1f06090501051522060c0311010b011704050a080a09080c090402060f0c07090f0207050114130b0c1911100c09151b0602030709270c020f0106060f 64
    0x741e01c80f41c010030351181d401480785444582484080f01000348541400320480190f50b1300059480d0850b90b410505032182d20341c00c1c10340c2110549a0300700e030340140b11240010103222019080300030741c1a00d590070500400580c1c240c1030864440c841d096000404260014420325000c0150780300c180401c0318420000c80740c610b08c0381026000141507005410800c11140c40c001482d454417103080229000034119a0818006514412411070003500100030a4481b03508082d860111811808852071091900c100c0b442310000c050749404041e03040052801e0100d91003040300c550040304c03040320800c4141d0203030303210700b41062030003401400d000241850104403030800c800300d444d40d600000520152500e8100d008082c0d00d010100b160034600805a00d071011040f040c3d410240856a002980308481a88401080d107a403849641801c0c40460300384101d203c5012035800c60278006404c0b0340b8448400b0710484144410308c015150031125030703a002a0224076000b044e1081a90001100d1030040000e101d8074074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 621383021 1250 621381771 621381779
    0xb040b0c030108120d09021306090b120706051606022709060d1b0e0109050601090f0608060f01121e24150c05160501030b0d05030d1505031f06090501 66
    0x754a801c914128030542c070001c104110204e000c3d1b400320040c1500246030442021740c81826000501d283e000eaa140d6908125101180b81085c0c1c009541150240703004009043c503019040321f190300b01d00d035101c0f0100c0400300310b4808a40c3d41e0002c1e100b00f1101600e540f16001041645081c9a8816452300c1e0180091408000c2070f607a407100300544440d00640a0001d01003101ca1080c19540d09401034640d00714448008030f0420559031000f423050744d007070721341c440f0701034072041c0c40e2001c00198495400040c6880c00000c3c01424421140c0001090604184d0003580c003008040701521141c00350a000c800825041242c0c501140c0103c2c0708001e031308012003a0492440100d00e8035540c45001d08116842401e224145a134410381140007040d0b080304c01d40305c411510a9182c01c518980c1e106450029041c540b504400b440c01800c0340701c0183d8850015032400810b400310801402e003000b10580c000d00d9142000034aa00c0a000505030600300d20240103a81c00700d08141801c554440d000103404502e440010701c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 621384271 1250 621383021 621383023
    0x6020d02070f12060b120a0501061a070b1506070c0308030a11040b0d020f0f2107021c0e01021c180905010806061c020423090f070b130906030b040b0c030108 69
    0xd03c084c0c0141010640301c01201c08640d0382d0310903002100c010710522a991090240c1944400166010b4940446121a4080c240126400b80d00405040e804071080800d6000300c0780400e8420b030406c068100c5003070240a440e46170031021254025200c2000001c10085805118420303d011a070000340d08038146030070f000d00100c17503018862041d403c0b140d0014205584840c81400d07110a5000740d200d041c0c0c0d458824650302000d010b448800d040c03644220011954480c00850b00c801e00180302e032010b10902802850450342421500191030550184041714101c04064a0300b0740404661a00c550441d10010b103038402411b604e03944100d105615203001804040c10100b40c15400c10310803039115200200302c00350030711000510310000b94402c0c80c0082120384d403440d278401c011800a5020b0044100e40c1d50092054aa61020750307151800c0d08046010b00402c44910080c1104100301e08041459035110610f00341152010381096507031135580c000b084200300c0f1361784181e0b9000508600c5a030131545408015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 621385521 1250 621384271 621384299
    0x4090c061805060c1f0506030604170903060901150b07120e060d15031203020c150c0c0115080d050403051b130c1206120803040b07030204050a06020d02070f 69
    0x10003003100520140e0101d00d60101c0d6000035220041c24030303a0b0b86035a1260a90344649040c603098001042410111181155201311032140300c000c0c01a00722036480380e480f044420300d52915803190003418031502d552910100a0f40c1e1241006100002c3c0d005e1b200391084468100944c0100140030b070400c51070000a601d0030413004050b0043c00d212269819410028050f809103900c2d00b4001c42c41c3c8483c1070a46e518100c4503034101d901854540381074410001c411003d0344544011040142e110a560004035116000740e260b00100c0d030040340d806c000c545404142901c01d0b11007854288141c0c041c040c455070a05210b088031202450402c1480d0074510740c1c0e42034540c441101e1607035443c2920300032700700c01c1d841d10340a61074003640b6240c081002c0c07601480041c00188070f91140c0c1d141d030361400d500428200702c8080c130280400c0d04505001e0541d0303103a585029004400901407010141c00748000035003501d55142080141000e900580010f504084009103010f40d5940700030640020000700300320138022940310b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 621386771 1250 621385521 621385529
    0x702010e030c0a0809150f13061d1323060f120d0c030c0807051020070602030a090f08070605090d0903060b01030605060d0212060901080c12012d0b04090c 68
    0x3641e91614451000100c5103c0000720408103003900041da00c81103d007007070082418842a8002d021802d27201c0f841207030511003110100e100102c070340c11842014548030440c0d901c04060b0107800300308040000ca0205040c01d00304043c0c082c1004000c02c0c400d19280450040e20002c0054036942481441c19900654a0440c10481c0c8103010300703c0300007014584030b1808004c0464000388503071350314101d40c68401d44d18004c0101d07107001c0902d0042d41020b0004895a040c004a0580d00b40c50304051441c1c0360308000798005014030004a94490740800090340302660300d1040303405100d0703450700e0f480703582805015180000e040348643e0700036180d01000241c00c42c048000340c80d0845c00000c0e840c502d440068000b03046070340200394001d1b0040392071404001340703400512162003543e08540145d1502d000b407044c405028000d07031400350808402c41c8081d05007442416503c80440001040c90603d038048241c0c18401c0250742020603941c41400004603400c0d0003500605441964100b0200d07003c0d407110000003d035030007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 621388021 1250 621386771 621386783
    0x50d02010e10140a05030105100309030e010518030a030908060a02040807030f0f1a071d060d050907030b0a0203100608070c08030712110c010b0604060c150906050703050702010e030c0a 81
    0x39001a6030b500c074403140440e0440c0b10041681e50000c03103501408a80007441420310406080070190a518800d0155807a40e079415200c06a82c40400401518242c2000101580f0a03a0f514125034040c4d804001102e501402a25001c80c05418041d9190526000610b8140c00e036004000401c41c80c1000510340c01103a42082e00d1036004142407500c840c0001d0091000f6088190411280b820044464103a034000d801a0300c82c0400b4202034401071711036941c032445040e8010000c1c800d5094000381508619885095103040d6001a40c60360350309d00581d038007038407106443c0d0f41c00700c10001000b6490246401506003400c01d100b003450159001854000e000074000c6c0700074800310100d10b800c1d0107a041c10175084070988083c080618040071008481d08160300d080c0c455070030003050306c1c1d282c01c0c00b0084505880442e50744031016036107034407900c500003010b85250015558465070003000c0390241c85528060b034041c2e0340c042824100030308002c0c01d482200688070500e4200f0000c146004600155900302542d01030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 621389271 1250 621388021 621388039
    0x111030405100c1103033121030603120306050103050a0b060a030b010e1e0411090a06350a06090b18061203070c0e010e06013e0f07050d02010e 63
    0x324121100d44164038400013a1001005004090080c00e642807280700003003058400c5090395868040001c3c415202c003400d10b40800c94500841c1c000d880140d0354040da2814003080b61607995840d40301036169207181d400002d5030740d0310900c42980d040c0500c03500049108400c1c81102807440004541d446403a800301d040c19903c9802c84038a07402461241d01205000302a017010a107a002040280080c0c112454031484c43c00004841c0c0928050980e01045009481c5001007400d0040954160071101c0c040c5011000700a842d5500501190280c0f12880c00f0780004910f42c00d0002ca40c00543d20f641d0080c01900341452107030301d11600c0d086503103901e00c000d021180c0b070303030351590008921030001e0443d202d10700d400300188550502c011444140101c80642e041c0208507a0b95103030341014036406458182c005003440701c02d00c5000030b1007402e0a070b820381e51206100050720b0003025101e01c8400090045001d4000b4000c03030390806014042080100740c155040c482030440da81c0000e10705103203508100c0c841c20f515 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 621390521 1250 621389271 621389291
    0x12051513050604110d1d0712020d05010e101a0103110313022106041a0106020c060c25060e0a1409090304180f0c170a0b190b030702011103040510 64
    0x40d00184c0c0740c54143c10480d80d42e038945052410180000702e444108813000100c00d910310160010316071007155084d80040e40702800035800c1004400f00840b00355400d64a611968100c0342003404802241510550001001c006c0d112000202c1c2c4500c00c0141c1c185860b101d016400780d4a54000ca139480210102c01d04424101e80c4000781c00c2c81200300061111030406528088660f070005461400b46024144003c1d45a950f41c0014040c50402d0082c0d000581110030488031038140346026182e2180300340180d034070340b020ba8100c8044015080640c4012100c5503042004400d8000085000005054030003220040c1001d80c008034000880c603046010b542c078080007900401d428010f550180c0800f401e0141c008983c00034590240411440180c40249003414516600e4058020030801103400303203000e1303006d607aa090740400504c823210300c1540151700300e4a18001c1d0407074210101d0281c02400201a10380c141604000c2c00c440c0071080410559004000748004100c00041a40221404403004104541c0e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 621391771 1250 621390521 621390529
    0x801031a070906111501030b010306060e010b040b1b0f0705100f022a0a090209031009050a0b10050604062a03120b0a170d0806030c06040501030b060c0706120515130506 74
    0x2a105c52400e80c0d200384008070030801035011352412640181c00501c2040d44521440340e00c80400c2c0709032480c070481088100075003080000a4103101d51044480300d0031404644150b07050400355907031014141c100795400d0259181118601c1c0356210359142100030094a004080d640394003844007000391144c00c601d407003a07000804540f482c040b50050256050b817641d07481c42201940207581514428083c3ca000e0143c64003083c405c010b1141e4110300104860f03211034652100c0c0840141581c108200c04010108442d142c2c040200014452030f951204441c0d140824038600d940082c02c40d42c0141c03a5003c484010a0f03208503034002003a400d00002031810702845c0080d0a2140c00c0e801036068000c240205908a00d001c1f94003051403545d03440300d490542ea81004c00d5101e0042d0308003141c0c860020301c82800a540700c1d601100320880c0c0075124515050513503a0203444c006044e4000c40026000342c42c84442c501c0035026154019400080542d000b4841d00c000078141c00c044140240e1482d50303400081e9140c1d907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 621393021 1250 621391771 621391783
    0x50c1603050f0c0d08100909080304140703050105130302060604110405090a060f0603020903061e010b09030c0d0507051503040c0308030c16060605041508030412210801031a07090611 80
    0x4400800c6441c266811113000c0d0002e041207580c080300300702214000458064500910120683c40006507196035584d55440b807030107501403801c1c52184200c40020001650901c80c250244959400c203581003170081c64000e141c50802000140034034289103030141c6011038401070f1003d540c8200c4014401d540d8130a014001000640c0c40010b90f0a020000041e025400d40e0050020741010340070348110307590b4103807540040e00d21014000300d100703079100c01040319000f000081c0c00c0d1100014260f4402003005800030b4a01070800c0380940e4540c100303820422003440d142c000b43c540b8100564585007140743c0b64845007040c507514800a0014800040024213550703100c0100c4400041b44e000740c02000e840790038050300806480c0101e6002e9481c19100300000c600951020b4110f0766440002c51819041c2603071b1980c112048001107038003018050480401004107107211018400d50740d1040704540c550705200b54a41d115101c0300d20600100d0080c0140c1c1c070703444128102a24403505021949181900740140b03005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 621394271 1250 621393021 621393037
    0x81c0503071101090b01090f1514060c012c210307031e05150406030c14040b0a0b090307090b062209020a27060f0c1707050303040204050c1603050f 65
    0x9480c0a80c40c004104030f405c0440c0c103031901f40c4000c000d41015003040d00201d4198000202000e0b140d41420011501071210301c1101000203040d540c20080e0211a00c0d003596058030640c241da16040346c2c54012965004140c0704501d10180003070910038521583c2c40b150645101411958200c00000151224041e0308401d845605000c0d070380440e00a00c810f81d100400e000d0b0384240c15801c000001100a00d0036025020942e50819515941c1b54500594001d00c0d00c110780110fa00f09132180740c40281c40ea0741e243d8100042c078071000b100f61359480c082c0405080505603002901e444d842d1480c1026141c881000740c52448001c4000441042c1508103902100c1040303500030f980d22800000c62004040d4001640040c0c040c511583c0320b0080080c017400c140310308981c0074400000381041c0191034410b114004035100180991b8080805004000da4400240e0007010142c400e64030000a00046007801e20450307500014540007030b810310307102130782c0c03807280307014811019003000408162072a0f440740440c100c803821 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 621395521 1250 621394271 621394273
    0x9130609051e1507021c03021c02040b0d0e01180f021f05040f050901030305070b07180303091509031203110904140906070c030801060302030a0906090b060a081c05030711 75
    0x140c00c1c2042c400e56034442d80901180040807100800c0703071203000140c589801c0c2407890140340a8406038400320001e401c115110303070480c04070356041d6040001718130080c0702401c1040c8900d583c1c0c44076489007005803440d105c5080c04aa00d0034000e240c42624891034000250b1780034107400d01c40340d4980005495a100d1190411000441905203018950403400500444000301c40400500340c1d244100002004240f1014020403404c12004002688412031a80e101415003041c134107040a182c1c0b00c0114142a030801c40108040c40410b000c00e0800c8030340d08200b0603092a00c1034100e81075a0f18403030080c1078641d001c03041c9070701d403001d03100e00d56036103c107440b10a80c02501c10013040c2200003a42c0c06001081d100e00311640240d030040307030615107d8101c000c041501602d40e644940d2074200c044009600040c1800c0e079070f5036036014410000340503018038424135020b00d6001d12241001c4c02003116800f850740c014207c590001022201901e81c08101895588080c01c041b600e0f07664001e415210001e00030040806 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 621396771 1250 621395521 621395563
    0x50d0f0209220608010b1507020a080d050a030509010510090b010210050c04030308060303070f020108150303030907090509070e2d010e150103020909060907020f030a0504050f0913060905 82
    0x2d1a40008030340615a0256000d01c06580e48040003400c079070706080d000350055041c0e2041103688070341000400c60507202811004100b036403176112074201504411100000b40b400501440c416925000c0c440d0002e0618001b0400390a1509000c50f0504e80c0b0b10540780d140b500c88007600180ea000f8860030020b4600c6100a00c200e14200c038110701503900500007103004c01d803418041005820000103036010140d020302d00e002c0c40050b540054840d00d50040030781d40c8600c1801d0401841e43c40500c003543c010f001200c014883d503800e03d030000c003e50b00700074580c1c101e590200e182005030082c1c030070200750044a210701c1c005100b24001c40100c0b00002846104041441040c000107141c070440481d144034a07400305090398660491001107042c1e208650282d5071041086000c03d0892600c16029034201c92280115082150103088960844c3c10110458003c180f01240c1008a420410343e0000b285a00b00e9104251b40f60004460b0070a102c8040c2c0a00a41c0e511183c010802c4410003104d0307110244041013200c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 621398021 1250 621396771 621396799
    0x70605090313120c150804080903011107080c01050c030907170f03130608130215090102100f09020102120a0207180f090c05041d03033c070915050d0f0209 68
    0xc8556040890b9040f6210744001024a10310f130750300117540c82e02e07600c0400302d80f070b242c88003a503503084600e009615550fa4000c082c01c1c040500c2c004d081041c41814026201e801d0308001d01c1c00c403400100381002415080040003826070b00451b00e00150703489500c41148842c1764010b510714250510411007428440002d641d0031401804c0c210500302d4a44e59254032080d5079050354401d00801c031400007500a0a0543c03491622003c400140401c40410b00c110303255100799451071419185401c8481e16040c1ea10f51021095581c18410f450100c5001000185000030281c80256100403502c140c09180a00d010799600d01c003001d80101080384c01e0707a40d0901c004c2d156402c00d002c1c400918895148030b9440d02c0004041140b07849005000d018140b8061400c1da070700d003442800925240034406c88410a03070038400014699020120f08084030804000e03400d842c10031009001d07000385070043e100d00d41c0b00c0c131544829680d100049545c074003040c0c1004140071b6140c00100d0003034000d06d00b505030310902c0c210000c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 621399271 1250 621398021 621398039
    0x60c0106120b040b0c0a051603020c0415080c09060d02040e031201300309050402030703020708071a0708010f060c021201140403120c02030702091b0307080f06040c0203070605090313 80
    0x1a018501420001c482a05c603002055202e111b4040e1a0707001c03030703001c0c407448002c0070f030412030290061301074016201103103565400101103e058041d401000d0f0859101230014500400401c0030003c0281c1d4890302600b0b08200285019003811402442035803100d400d50310068050059801e0700011025960f05961244000c410340080d50b03e005840d03a0002c121140070741d6024440c0c800c00f54043d00c0f0b00d91200d0620b03080c0000717580010040d0043c141c0800c80ca800142e1424003d042c45400360408084108400c1a81746940602030f02c030700700300311003000140105100310030000210380b02d0b030410690b000124400306907000b41046510340703e9441d101d840d24000742c0402289100d50700c2a541e500e015100c0b07021100445070340900210050780309010120040c1401e1005981000d24560050780c250134102c0c1c1c10f0304a500460b0b0000024072484140500c21100c6031402e50031050450f030a00c40c0c42c0b6040c130b0080d9a400307206000740c04942ca800c08102408418000c40d5014400c10540101c105e403921100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 621400521 1250 621399271 621399293
    0xd02030307033803010b0d08040e18100911060a0309030e04020c1b0f0613031a0f04080a1e0f021002030f04031101150e0105090f04020f060c010612 65
    0x100780424105103031000c408140042e90507107100100c030f003c0c50300c4040e9410088414448a101605507681d5591010241d03910318075074284912880704241d80e641403400122038000e002c4c003000440005a0109600028041090400300109250000302c0750604d05000394206410040c541c1c10510015107202443d9154001900300e0b40030b61900c1c00003017012404d120491160204407081904403029208021410b1200202c90443c001c21810040c02490b002598a40c018210f20031040c0c1400004c00800801c40480e035201c40b61003441030002e2914407282d1142840c01400100041c1000981d080c2007030103640804680040201da0031071402002030040d241c0c0c000c04541001511a0292102d2115031070b0085911032a504007000702180c9030780d50180c4d00004040106607140d52141205605101c40888a00040141480320541c551504d0184048880c015200303a81d100d41003401c003c00b61300c0d034981d02001c01c8420740d1055500d201c4419194010039585c0c024080d0300d03d4110155040c800400c0301 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 621401771 1250 621400521 621400531
    0xc030c090c030b12100c0207030c170f0706140313050f0c131a01050705100203070201050a06080109030c0201050d0b0307080c0a270207030e0d0c0f0911030f040c080d020303 76
    0x803c20081c0041000c002071030032106824249030b03000c0d4540b021300d0012500010310015060040311401c6880340e0343c00d01c03200802c1c0c00c6100c84a000380310782056900c0411040b41c075803681c1d00207003400302e003400b10023400080c640021302e10050000000c034070313981c1700124030702c21054216080e1403d040207800c03025240d10f400900c151041811000d01901c0003410f1013003034103080781d0300c0b20042882c4024006550f203400c0300d101621940117410403260417003414001540f20b85001c3e40005507615181d8184412103008e80c0150381c2c00d0389816200e02c0001e80290580e0700e15502420010380b02c02c00c02a20201800007094000d4042c01680d00000351102e0010f00c500320040201c5070643d4640e00d07020a01c08a004c3e00c2d050400f420315070500d02c411200f1a40c000c01c1e08501900c0e001c84901c4001002c070f1803030700d1171000480ba0200940800c006109641c00b00f280500600c00d02802a110300f0500c208641c040a00f500d1a650707103000200302000110100c00380107002450076a40b580141d2580a5126002141c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 621402877 1106 621401771 621401777
    0x10e0303030106080610090602100b040e01020d0207061409060a110702090103080c0f010b0a0303050c010e16150c0314031816090b030604020303040308070c030c090c 73
    0x200560180c0856141e4511314280b010501181803005a031031010001c1e0b00c213080c0050340d03020541c21500b107408017002c590416a600050b005010006e001c1441d90310004100313414902c40d401030051107006040400007a1402c2a16105414080301c050042e600020005465910140c4c07008107502204000a4102480c6078086018090282c00a80d000c5c000852450044802081204a42c0d5540b5000f0300610450a000c41c1350300c0c1d03060100400303014000c2054010790100350b100c020310041140c11141c10300c0320140c52011103490750092031201c0101c41e03100307a601c80c02481c01204081c1e055540500903810800403400c1e40d04050f28064240710904c0c20382d2540c0d0003c100c048070080c4d02d10101502c01c0c0c6803002c0c182c11181c0341c0c0c80c19802034000104000142c1d40c0401900e0889030807901ea55621203c5248c1508031000e02d030001014451025000b050404032580030071641013040e2 = true := by decide +kernel

theorem cover : BRFrame.Cov 621223021 621402877 := by
  have h0 := BRFrame.cov_init 621223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 621223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 621223021 ≤ n) (h2 : n < 621402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
