-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4072
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:29:25.221287+00:00
-- url     : https://prove2.me/submissions/dc2f242c-3826-4a95-89ab-f71e3e88f860

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 732194244 ≤ n < 732374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 732195494 1250 732194244 732194249
    0x10b0d110c0a030e090705030f06040f2c01090308191d070602121206150405100c0506010f1d0a0f020c160b040513051302101d0306270f0304 62
    0x202400c0041920700f07000c4d2a402e4007105a85c003c3c040e080801c28030f240d011082d26007080c1c1001e030f5001241c50303c0b0b0020740039181035901c21194030300d03000000e050718042802c501160f00400130004080c8e0100b10119003214414900500480c058900260140d00240040012643c85010018600750101020529107103040c6901816038409481846415010041404c1034004c401e00c007031411040a04200c6000030203404140180720f40106219444201ea05803005480094500d05401c145d0480c0140480c06261044e1174500a480020032890040b100c40c3c0c0c1a5044100a400c50714020f450388002d540c0300400c0c10302c045a46c0c1e040d00c01ca80e0b01d680014440000314000034612140041070030b03541c14a1540c418001e20030100010040c0c2c1d290705078110300492a00d5800141692441e80828662104032002588000c1e102c04500e8901d4210421071822141e09030340800010207401495070381c0c0f000b9124013031918000c0e01d032a02c482c00c0c0c610f40005074440e020191080b01140c0f07490b03545544c1098 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 732196744 1250 732195494 732195517
    0x5030301170304180b010c1203090209010f0305030a0c1b0321181a04090e010203072703110117011401020f070f0e04021c030e01140a08010b0d11 64
    0x10441440740300e904110110464000d1440c16103481020b0740458602808410095128042c480b0580c1c05000e0f070482444e0000d9195510a5910400034000e18580344202d22402494001150600c4c07000c05003010340e03034001c00451603c200f4010990701d02d082102c1c1203551003060108545046211101400218030400350600059030f8018100d50910f0305c061031a08100d500441c0501c2540240003603404c40c5c0c0d506043e00c1028100302645c20320303032040c2d0304800215818451a40d400410550045226010598a8640701080030740d00a1094940c40e01b091548098200c0500c0810380c3c900b1103056618050612079441c030300b8411074842d0103200364407600101c21154451b65075541c050040030410030703001003e88040c6080801001ea001014090114001c40034030005003151900c03104040141c211072040d1040700a1803030000c20310581211041e0000c0c0a0030031440507001d540c0252400c2c10043e4460340e41c90381c20328052041036004800c4a5844580390701c140703c198001d80005000d401001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 732197994 1250 732196744 732196747
    0x30a081e160b010801050f04120504050910060f0804030e04020a050904180309080307051b0103021c290d0303050a0b061308060906040302060c180901080607030506060301140d050a0b040503 83
    0x254100090b00c410140d10001c202e9043ca000c21540c030f00c110406070750050380114140a04540f000c0c0c103c1d19806039800c01600304201c082882143c1040c14420000c0302c00b6a0790f00721007141c510208851440b02a1001000b0600e110003601c10b500c0e141e006083c0840e500d141040c01c21142c0700000c0c0035140c00704808900000d04424402c00c0c50307401110307440074040700402149041510340c0c1da55901c50070300740348500f0362001300401c1c070640c0e1080d0101c0701c01c1403111001a003050450034500c801000100410740c0300c40e0644500601070081d54840e4040c40400800c1e140d244c1d455501c040c0c0251200802c026045a135403445240160b4400d030182c10156440c80d0160078190400b034442c0e251031005040f02885d540903008001c00254001559a407040840c0b07d915250012041122410421400c03202c0d4010010000030802c02000a040340c85860140d40500245d129482801064442805100316140300c418925010341403208201001d944268201d034503a0613103071a0195002015102110142c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 732199244 1250 732197994 732198037
    0x30c1b17040611011409030a050c01061706070f1d06070302151918020d03140405061207122f0403080708040303021e070303080c0c01050720030306030a081e 69
    0xd200d07000045c288030303030310008a0616020056a80c0600822002085000580109045409c0d00054000c24900e211260b1103102d03c21116101d04007180d810000501c640c0d4042e075079500c90003024400c9920142d01d03242c040e10200902074654420314090382548510100340620180c03911038144980d503501451803009210f244444240c4003103100c861a508807161002c005680c4480f00400d8980d8507040a150f40c0340f00040d13085242c01198441035202102003481f11007000c401d44900e11400e501e907210402040d1040041045030342d4414925100066500541200b140d403507500c4490809400100d42019a256034007146507121001c1100c030390002003001c0041540401201e0401c005c80520980f0401154100b1030356041184000380820400d0000f054410044100b2078a0411941e40244040c0c640448003a000441c420940400c80815514044091002000f6030f8003c00b8010090096181c143e110044030340c1220180e04035208414607540005080e245c003e003ca80d2404020803001d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 732200494 1250 732199244 732199277
    0xf3c23090f4e0a05090901050d050604170c031b06060a080d051b0102030406050114010f02030409020c0f10050a1401030b040210110f0a12030c1b170406 67
    0x84040201095481150311214040609050402d90102d08081c024031690901000800c01030022619003107400c400242c0001050342c070600070100418140d40c01a030903681e41082c07040c10654440050305940002c0040750000ea038084403001481590100c03e420001110b136450304503400b0024542054051841407960841c0c00d2000035403241c1c04a8101459528281c9180d84910607400c0d1581084400507801c1c804d6042030074041e0340d10325035070000c5450b49050302e80440140744c00e008440030303040654220300d01e5620030102d910880074560302031400d01e890800c81001a4021505011250044100000350001c0030441090748000014003c1034605040708484215052903400a0f80e2039118001400410010400f440e00241c1c1510704c03508034851031a040351741d65012034600920340110140c3c484c0f61080051800a81350141c981840f4180344d40c1025400c490280d240c0001207107100300c0c10030310301004c2c0403880555801013000c0c17005d000344005803520592041d000307038001c035251201c861101e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 732201744 1250 732200494 732200503
    0xd08120702010b190e07110a0303020f12090105040302010b040507090e0411030102070c0e070e0d030f090506041203320c011103010f0303022e0e010902040f3c23090f 73
    0x106605007c84d01040c020985600c1d903160b840d01906040d00061008411519441125000812510b1844003030601e07141e400d000e002c05840c00d078019824000701000914103031145602600e855183c12030700c546451004141100028425206480d504d03404952540f002c4c001444030f00e100d071790900070481c18081c1c0c1d601e50341d9014003c43c04101041600e01c0060721600700041d0780507014180116603405a0208441030a0390f80c000076003004001c100024603003800031403504000e1090319060356410300c0303010711181140030085020640c4007070401040d845030003400610702c03102460000303e015000724600d08402e0b40203a01403208030304543c004100341076052144402400c109423707103500c1d010603103c88402c000c2c84400c19070782555035204e003502118254002c10703c41c1d5003d031040c000c0401e0702401a000b841c040c01034075030020b043c5855030560b004500039103131000b0303c50b0312034010400c0910280d0000c2c590811951000b200442266030291104001c880c45001d80c0c41c000c20b481c402c12a8543c1c00d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 732202994 1250 732201744 732201751
    0x60923030708041412070603050a0f0218061c050f010e0f1608061804080a0806030a05030307031a1c060e030a02060a200a05180d08120702010b190e 65
    0x9410a009500002c0c0d03154007207808880b107030422a10b140b000d8600294010146158000c040d00c03070804002851303901500028031440e0106410440301c078004d0155130070b910034181405000c101c2c1c040c402e41e031440d04c80d000d4004103040c0c0084199440e13000c0a81411203500b81c410000c100d009000401c014100361101a43c1f000b14a0080109401d041000714108040d94000c8414401d1541c0000c445440d201c8003403c4002c5203044411207803d107804c103002140c1c4001c84174800600050000340705400d0001300d03a810907a100d0003d40c035654451100324010400e60880c51f108420040140040d40e1301c10410619000c40803c03c003910300e2103450000110740e44c03d540e415a642083c84420712054020444948c072003401d410114030804803c174000c09684091000030415100480e050300b4082d0300c00c016003120214510785070000507500d01003200400f00341500030f00507101080403000314411000c030107400219038000443c850416200280f4003a075000300a050f18071440b1000c00c00f094003104890740 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 732204244 1250 732202994 732203063
    0x723070b060d0f06050411180a050a020901080a0b04110d0e100b1e0612090f15010308040303120b030316020a09050603060c0a0e030304032307051e0d0609 68
    0x1042c0500e40c2c80060019031100301404080d60303a0006018000000e0000c000d40c0002031100302c401125000020b001c4409460f17140c0c0c200d25000000304100360500c21107814050503158203409a4900a00d007000c0c141140c20303180c0050b165100001e490b4140c501500203012410404115002072030a0035280c08402141010310740c0c01d02c645100b03141ca83d0080c9801c80404e01140f07110140c51040411708030703c00d00d000600100d81e032104005510401107a10401d10001d10b041e602e40f00384101d0350b010410303000c0c0000b42030103c0420013040000d00030404118851801c442c01b261907501c1c1130010b4259008103901d14034030714014600e00c5c210310342601440f01900343d01800704401c0c10000086036072a03c000b0010381204000158201c5154000d889560083c48003c003103c2e80d0761b8503858002511401c980c2000b5a5444402c01c500c060748003c581682644c1028002041001740724081000c580c0460020603000480c800c40c0c000400c101e4068a054a4014004402d0032035120340a1050380322024041714 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 732205494 1250 732204244 732204259
    0x20d03030504351b070f15030c120506010c02090114040f05040f020409031106072613030320040b0310050a1a091503090709050a1806050723070b06 65
    0x649468100c00c007440c080f106800c103807035150700b940300c100d40c24200c5502002c030b01c0351440c00100c0c81512800071701a40c0307081d189410b0030000c42800b078040e03502001481c804034000340c101e1b5803000342c41e5120729071000051411a810303040071f4011640100080e0401a00c0910684041c0d0580c1045d02401c070300b40c08001000c101601c0e081e1611a030007400144024412511008813406061096001c0d02c213005021041c1c1d541401d094001a0443c0c1d146d010580110600c01540c440c03010303041d01d10f0341c0301d4001c00c8513003d00003c0b80d6508500825014103100342c0401c0220158520a00000c00380c0041c0000c20b481694074100300404009a8200c1d500051056113591810301101c040000700302082e08241420b0740c0c0310b10b601c9000420215442040c04001480032003004080440000c0000c119940d81504004503100d90300d012080d0384803404a00c2e031440b60501c0800004695510603070f4050360b10316200021102100c052074410103003c0015860b00c2c0c0101380c10042c000039402254008404480f41c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 732206744 1250 732205494 732205553
    0x3090d02130c0305061219020d0c031e03080c0405030604020d0c080304180608030a051209012003060a0906060e0d14030408151012020d030c080c0102041403060403021c020703020d03030504 83
    0x70310401140d44009009e520158002c808211910300d08401465001004403920f029070300702e050710341e1140d05003074000a801001181d2002018012901940d5028003c2d102c555516028004001e001c08000c82c0d1420711007000003601071f07080c0040e0000d00340d4070485d03502d00c120f1021402c060300e01d5a040007889800400420071916040401c0300c900c400c0340710b45080d01d5a18010800e00404407000340c1c2c15529080203c40c81144948801180f196508a07070710b21295032901d400300300301c443c87d001d14008100140700036600c0d441d190003c080d6642c418903556000e48028602c0c141580c0050740190099400741081c6c288195507901d40300d03401603480c0d185021480c0703401c4c03030b40c621900c10038006030007074400055003010b00d4400c200c03040580b80c0140702642d0350780405000900070761280c4181c00c3c1ca100c07944010380803490003007207035800b0f543c140c1d005103501640c035551031030903ca040851406612507101d0000041c0c07505541d08119078025140050546045d080c0030200c0007208404403009440c5c01606c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 732207994 1250 732206744 732206773
    0x21b07080312180703021906080a0509060a02070c351504020f0414280b0d12091503050106080916180b04050c2a03090d02130c03050612 60
    0x6940f141c1c0307860005a203000302840140c1041c184c0d800c0a50403058030900b0402501e44090f9041c1117030620741c1c42e400036586200d00041100e8003500c601001d9009032340030a800d41c1b030f01d80151250a0144400d03c2030169564402594821242e040541f410b1001d94074160100c65107001640c0b0b200300c540502030011000075070009071640200000c0c8260440070031511a80c8442e88036240d01d019140c82c1542604007031a0f80315402c1d414405200610071003214140c000700301c90141068500e0060b141e215540040d984280245031401c080c14100428403000251080c408440304480c0009514000b400f541400d000400326040180500745907488800d0b91080442c55260080848000042c0c0503400740300c60b414070300074000180540c1d900c1414242030003000c1a08000514940701d250b26000d1a518401c40b59011400c003d003221082e58006001500c2e090808074111501d152000303100503080790b200b03450712040311a034900b03800009554800f004000d040c00480c00c1e060044000c000c00001c05405803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 732209244 1250 732207994 732208027
    0x51909050f01030c06180306050f0a0b030312010302060c010908040303030207060b1c0b07110723030c01091701110706021812030d0e0f010c050a090b070c090c1101021b070803 77
    0x608010000d8221001150b408a81b001901450384143d0030701442c180104550710a20003034541d940a20314000e009003051030001308030f072102c05161804800d140e10b103070204815504403400d00203055403102030842c0012000c0008201542c400d49005131129900c0c24003d04803003500c60441d0007011440500c00f80300b140c40c181e502c41d0ba540b0140c01d041ca90350350102118405255401100e4501c1500004500440400d0107268a0354420180c0d803001d41c0745000701503540d290440ca82e40499018581440008401407448000508178400420340b010454480c0019500619064a04c50b41c00304070712501001c031803c101c940b020304580c0d03113810900000c00c03282c89203d94113940c5401607450030b00e460fa0741428420001c1600692000f08a0b0544184000d4902d503c14800c040c000f420311180482c407402103405036128243c016090000090410705008000d00f00f03000050b080c4040741403603503200002400102180d03500c0d07400d0070f5800410b03070345042d14003071480d000202550002c0c040c50780040d1a481 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 732210494 1250 732209244 732209249
    0x20a08040c0918082d0919051f0309020d2108071b03032304030f021b0d05010209091005040e011e0c09090f02030106090503010e25051909050f01030c 66
    0x8000e56821056102100c0a1440b080d48400c506805c6406030249070102e0140500060640f100c1d9501210206000071103809801101d030b100b0b0040c1c1d503401144160440c4942001c99134100002c103560f00d900094228105e01c03908507598002c1c00d01200031940b04580c0002102c42d2428448411b0900b914082c080c0011515481c56102c40d00344c441050610076080600111400d50341b02040b048148030141d0704000c2294140c020564000510100c0b510000e83c1100352600141035000c03204420302040001005480c050b40c1d959000d0010300655902c4685443c024440c08a011483c28a0b120034442a0f503001251006070b645004030b100d400551600080014075110f0701c000500740700e0f080c0c064400d002d1a80003283c02920b880030a0306004001e44c001d41c165181920381500c915583c004043c2a114a1013106000341c001c10b41c2040280c1c4000080e50480c1a900c40c00042c0320780700d01c040f4080c00400d581745d200460006504000e45a010b1040d40c0d0042445079013810303c1e40c155103a41d41d000c0300e02e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 732211744 1250 732210494 732210503
    0x2091f0f050f0f0f030a0608150a0908040b0a02010b100216090203071b0f031419120605040e03120c090915040f0e15060423040206070501020a08040c0918 68
    0x688020032014040883c1c0700d065080480d039450f8070b0749810090054008031010307100d00e40b80901c085030032100040c0f2888a054141c2d404160f664450149501070190108201d40101d014040840d10045d030704054043c00c81503a00010702d00c0c0c299030401000600c0c510414095401c81c291802440902d0031a4400340c1c2c00c110809030340c945541c102154512601d054448020840d040f50f00104034242c00d024840c01e001e580c4902200d03110b00300f41080da100e03aa07100700107281d00c44c0000700811300840440e8450841031000081d616a07800100e4280e81409440055507003001607105580b40c0c0c12a05c040e080319005650f05c1c240f524000204200103000b0300381001004041c0c40b84c690700e035680d07004000a09903044044c040d40024482ca0340d13441c198101d000031011100c0c00012090304161041485682060800300c03141e0f81c03180701d401107070302000d04142c1c0c20007010440c1202182090008045282c82542d40069514213810a5007001529410140070b00307041412a60841080b242c0c04800b10340c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 732212994 1250 732211744 732211747
    0x6130b0d0834120f0f110c0316032a0e28020c0d0e030316081303030e01140a05030a0b2409010f050403050d050901050c1002091f0f05 59
    0x20896180c0441c8803860710551000c0c1150707100c40011400c0a80d05803c1c81065044a514034400c0309480d0a1521410140007a110050714085a0f00c00e11070201c40400c01d40580d40403400600200e0f04010344451000b0b0041c1c00d0300410410819407060420b00c408071480d80c640c0340101800a5580a161481540826400c50f800704036140d00760f500060031510101a4507085143c00300c0030724080d41242180c1e10705400340f071062480c2d5a010744902c0f03030500d40040107503103405c84034550720880c000240c40c1600c0f0084107200c2e0740c0080940f290690003850184e2100c0401642c503400041c12a000940d28242c200b00901071030200390f8000d81a0f035000400140f010a01500107008207079891100384c41c1115650f0380e0880302100248000c010a00302c90281d132608040b22101d0401d84a41c0309612000381a944940d040c10142c0e032041000d003d40c0e07041490408e00c1c0ca8081c0d0340c0a407400d04011140c40865500140c019143c0c5440460103514801660408005010352100584142200a10102071000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 732214244 1250 732212994 732213007
    0xc0b01050d0305191d061608030a0e030309030d0608030c0d2322090605241204050d021504050d18050d0f060609050405030f0a020a0605040b06130b0d08 67
    0x2440c00d07192920713615104901c484107a10390080c103808032901c0c0d48000c08440d40360020181090800c80d0800001e000c4506a20a030942e610010baa20060140c1c1450740d80300d0084405402c18001075004100351001103496801c0710143d0030031100030768842c032640c0c0e10400c0a0004400f0200b200d10001c1c09908008940c0c074030002004d100b0b01070680071084017400c002355180f00b4490001c030301002601d04000b09009503855140200c12200a401100e520002c010480c0c08120f01b40e95003d00008501c0011174100142c0c01020814444180d604a8441d00080100c000f031031740c10002c0948500e1084003610060234592506900d0705221841e0b8010010039103207080a200c7c001146000910003c3e10711150b0020500705480903011000045907064200400010002d03c6402118022504040994070700214800c240e0704603480014040b0541c000e400d104ca011850b140f1541784558060b0000c4680d500d0700c4000c00810418002d200101c81d89010303540416511000340e80d142d00e40c4c0c007640c010350703c10303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 732215494 1250 732214244 732214247
    0x20a02120a0507060501050121020d090c0305030c1b090103060504050f1b04230f070c06111b0616050904090606060c02011b0206090603130b070203190c0b01050d03 72
    0x4040030048800994001044440c099204000300301c068080d14080110f662508011640da200e03880f6954450940140349060009442c0e00518403981d1440d0300155091311640c0e40001c0300907503441070b01c941d0004a0990f00d5048103100341e002d01080f805803240f5982402d0300290185a0600000d8803070b69441e00080c04004c0c0400111019029030380803a50300d019128010a5103066034191700740110308044159040300c4400034000d40a41000300300d10f00b10750750411074070100d10004011808104c6e81c40110000318000740f042c14914400c40754040c0da103810348600d219006020141520300e9902400400c504106c140100041b4408186001039a50101100180c0070b44040f81000d08858030300140015240c1e00044020400da1003038984070840047c0c0505004100a0120080d4000784104018842441c044000b5a84640b410711049001c04160301c821030309078400c5a0903070140e4400510141c2010820701b40c0d00141882d0714100214008a640303440e82c1d440306220725170141081030001030826 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 732216744 1250 732215494 732215503
    0x50c16051e040906050f0a0b0a080303070f140c0303010306050114030d1b050f0d08060603092104170115092009010302210703060603020f22050a060804060608030715020a02 76
    0x6900030000741700784e05044000042c0810141d41440c1260b14224482030281014a540801c03251044050f5096950b840d4080ea04003503007071a110b08005a1300401c490060b46c0801421007080e80100442c0c41c0d604510b031a60031900c060b00014138000107500e0244ca82d40d000074001e42068030703915261f10981c2c154102d101030b410755800000d045008010861703135034181c0010550b5006903030f03030750b02c0d040c58542600703200041c8070940d10207080d0b8102c0e489500710241c0345a526031503022064401490075a07102890101035298800c0321205075107840b0340c0c81c8004140c1c040b241c0940755010040141d406c980c0710000916541500013514a003003c0f82c50001a8001d074162806800d000614544100002c0c100d200100006c450003800300740350030310201e200d238461301c2902e2002c1303140b002c072502d800c80c0354a03102d00d074420419109050b0900202c008c40d05440700f420030001003186880b00d00060030546080c2056507101d030843c5000e40d00038460000841c245040056220265010050b5240b01c5900200d040c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 732217994 1250 732216744 732216761
    0x408032d04030803060a050d02030304120f080307031b03110702090606040905090706080f04110607020a08010608032503020a15020702030703030f0e010906090b0d150303050c16051e04 81
    0x4282001c40d002050040ca400214490081200c804072016150310402210b203001e408082c0d055401480180100c0070034402e507290301c0e030040c400854001c0e0543d80300202540215004400661111803160b600342c01c0d00e40e40c0d1441500da040610292099620b90b81c014000c101c8042d118245080105c0c0360f540b90502294050019602c0c20710003403802c0c0e0446666401a807040f60001a11000050414126100210301440d4040304c1c81d00124420030070890f41d03800002041c0e80c8a002d04100080c0c240d02441a1001081100013450700c031048000d40221481800c040e0504a0700542001130005e5030110368010031503403000d10b4a01e640701d02500003009010361040250140f00c1c91002009150b002803c100c409201a641c403003030041e414004403621316261198401091140305c09001544160000e001450b03990000058112042458081795801642c019004200005940c0704001414801303603001e90401c010000203d880c02d1701088400c1d5024181c1608642d103200540103556071504902c44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 732219244 1250 732217994 732218077
    0xc020f0d1b080f0309060708130b06030312040b060126010501031107050613140c0a0308090d1a180706020703060902061204140105090c06071509020a0b1e040803 71
    0x4a50302805543c00840d8802d65460a003031040e44005946544100002842648020440d48019605a880c2d0150a80152449616002c20b1021a240304100364100307200301d001d8246c0c0b2089043c004009011009076000c010710380c2c4030864056480e02e140c6002c090445138203103400a0f1848808032561024011800018501d000b6001032010011040e04139414a074010705803221284803104800303549510006205800c03400c0ba410820100c0c0541000e05403040c40a8501c00c102c042603aa4114030f1000180307122003404103003003800703403c80302c502c1c048502b4044480208155420b18030069918a02407000810f91502c4440e55000c648800d400d5400d00c4191600c150314a042ca4640400f2003880221010115841e020019101100010300f040d500174020308080e250003880e484500815031051aa0003800b611036003000c005860b005091303002420342da0840e607110f5400c0400108800e01c50903582c5140003040c0018000c009010048603400c0180400b40030096048806080420081600d06030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 732220494 1250 732219244 732219247
    0xc0b2503020705031e1614040f02160c090b0a061b02030709020a020d1707090e06040b06030f070906020c2107080313090506090106080c0703030209060d09060c020f0d1b08 75
    0xa4030100304007000342030068581d58810701051050000c12846014021f09003071003000b0041c24903902c518003c00c0d40c15009498050400b00480c62440005c40480c0e1600c0d10a2003001800c03c5841401d500103001c4443c0d044040c54198001d2040b0306401154556619480e001d208664040145e00010036182a0640d114489102d020351a6a1106d512401250b501c60803c0e050000004243d403085009449074244a410f0410280403100d00400181c0c2041d502e5100302400d94500307001d10305c54070443c48040c00c181b400e920f0040c07605529900140955001c82c0328010075541382d800b101c1019540030300340420340c0810004585402c48a41c4040a907020000b42203000400607100322003511001001840311792180018043c14442c00d110351400500c40c2ca0104e07040100c3c81000304000380c001e16015090803208000140181e0081c0b2041c1240380e139a040402c1085503d0291a40342051030020f0006241c9004e04242c8606841d1000d0003041620141d24122101401f107a0b0302d0b103030304a1804c0d03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 732221744 1250 732220494 732220513
    0x1290d0f05010303020c040905030d0c02072d09060e010b0703200f0111030108030a0f1e030501180203040b0c031f0b0c0f0d0c0204020a1b050106030c0b250302070503 73
    0x800103003800c3c0002d0307005020f0405e51281c42e04140c01000f01d01c60b13000c00111700c1d00c00300a02d01001040d07864441c60850250110010306040c480c0501a144020040c880990018030103a0343d003403100b43e5101e901c0440c00c003981082010790100046045440c0c15030082d40d51034092a0440d00001080261800554080100e240030f0000145a248060449000308001122802981c1d00c6001c244600c00315513008001d106001881000620241040c80c288101c941c1c98421400859883c44011440000e9503040104418000c10000c07400350003100c0b81c00c40c550b041503200c110b204c0301d000305403804078000040441d0f18085244410200c10383c100500d403041e50340b210000d007a540d209507080c101c903106075150030001d4440407a85408455013034036001404691a4240000b9420603407000003401501460288003000800107001d1040c441d400016040b815441c000c42d1411480d001024205002c2c440b54a1440a00c04031700c40d4980d044080d05681d4206107000c03840d00060b600001d03090300592818 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 732222994 1250 732221744 732221771
    0xc0209090c041d0606100201061d0412051602091902070501020c1e0a06052701021c0204230d060207030804030e01050f0403140c03160603110301290d 66
    0x4039114220803501400100760a041690009480325003c44960300701c00c2c0071402c2490080f40480d80100c0c1c034000400c1b820b40d50311003550280c99061066204100700001c000800130043e80c0144103e44a0900c541411b0400d20482030705001c1c250700a01910008020030140c2c0303440c8100c035901d0200329105654503681e62801501035008000c40503068450300c800f03910402101040542014900f6000f09a10017064480401030003000d803460090000c40382c13543d000e0fa082d04803800a81c8811400260369881202c8241c10846681104964250b00c180001d120000020070b19105094142c15040c141c00c004c01c0004424403039042006100f5440055140c040640010b04503214074060b441d0300440984400040d6041d100700407901c89051400c000c00d10004488000940b1031316014011031b0b85014003200468902506043d6200c0244201c030000c020642e854002e06940c0640309908a041d54540280600d4000c0201e011070b20b00c10082c5034010110000e04203070f60750650301c0e8505007c80342d5040035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 732224244 1250 732222994 732223003
    0x19020d270204110711280b030f2a0706020f0301140910060f032d05010807080c0a05012a06090618020d1205040810020a020601061b030f0c020909 64
    0xc100d004a081c81d0f881c1504801d41c509540700341d500901c002c0200794240040180307194041c540c15000600c9040c8440110814400040c003806500101c1c0f030742c80c10540e002281455004000b076490805850000d00c420310951039404100f020f0019440d02c0700074528000000c1d00132040031208104020000144c60800101c0401d00120280c0da1014903490744010202006445d011742e80c0031034040c0070340e2441c0da0310a51020a142843d080700301154004034640d626400c40580034038003c107031624014040348009004401c010000e82004140340c94070280032070010300c40b40c46954148030110b03046c10fa80f100c0034600d2400303a11140494401c41601e901c0e005004141c02c62096825515011070380380511401c2c00742c2c1080b02c0d001004a079510443d550b07810714002c0c001010a0400409002c0000c540804010b003080c050000000580c668401c02c000a25201c1c0c16480341040201010898404441829019044540500e4403551405903408203031020508140d00a41085a2a0400090220204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 732225494 1250 732224244 732224321
    0xb0a050105040c0c050a02191203020a0506070e3304080f1011070f060204120308011a040e01090515150c070927050a05030a17010603020319020d 64
    0x6508111403c0990f40c110741e0640c1c04d660040895004071116000740c50201c4035601c0e06030102066240f0b60b5280c0c5004441d50300001c1d4100c0c01350b070000078a07400300401402483d92040141c0b500502c11204540050041e100000c100e04440b4142608101485c82194914940c1404100c4c0b4581e6940c1d50405143c0e19208124074880a0041c0d2070f508081105074000d00c9051140032072400e00700901c0b52034002c0b0740402d402044444a9007008001080700d40400ba581d41c00c2e010340c0f40c1c00d0644d8500300300420081c102e2141c8a210500400c800e000320701503420424150b42401c41c2c005803039070700c80754140c1e1150000f09049501c1654142083d880100003802031402c400340e0015034090664400c8403109544041c560460110310301000c20382019240f00840c98440d004000311040c248068a0b414116807103001e071400007801c1142240c8640702c102140300d0040c030513450304624614061510300e151000c1d80384000c0c5140d40000e20804607895641000e00a500c11008980e6000e0300c50071410819084507 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 732226744 1250 732225494 732225499
    0xa1a091210050f0f01150c3201020f0703050304170d06080f06071b0203010f090605060a0b1606090812070e0316120f0c030507090b01032a110a0b0a050105 68
    0x40c0c002610600c403c0b044601500d40ca2003000720301d03428680701240c3d02c40102d403a9810032298610010110380182503031900f580786070010213101d0040c0b0b8005001d050000c4018074080e03004002d42014041040112001c2c40c0d010318000e40c407070702c03140b8040e545103004007804481041c01141d09054425a5030000040f1a501012658941d050001e1180c596104586900c089000004103402e408480380301304401520080000030a4400001a6011186c880c0030948040b950350f4200440e605191245402070b05505000b58101811394419900c207103039920b00204019229008103040220741070030f07a05603460820b0395840c1441c2c04d081c001c14031281906034a00c05d10075400c140003d08090341e078410542d0204002801c0300344085d204d4041c500e030000c0085840c0ba810b0040007021030382c28040480a0810f1003000300d16805450001025034869884040c2004403144404400844aa0050a481c0b40501b044601c050102107114200a80141c001d0b00503148d100c10044800c10580c0464141ca504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 732227994 1250 732226744 732226751
    0x405210307050d08070201090209061909050c07060e03040308190e060c0d02120717091c0b0403030507171501030e0304060305041401050103031d0d15090b01050402090a1a091210 78
    0x117426007242a185c1404021303400c10112030115030751342449400c1094034586000d90344080d6590300300709801ca5804aa41c80c0d48034101103010801c0201070700510813024030740e10081d03091600f9511000a184207444030484031810131440b070342d03501c0d001d04040050742100800090b2126502e03880c41d500d52000c00f400c00e0040c0206400030ad07520342d203c010354a18036041307200103050804602648196502409149a000031400303812046c000181034048c199510411610800703040138580501a02c0003e8480e005004034054150319940035140d01c01d80c014080d0414540e80c4942c10016801022841e40192180c040000c000c41e4140d011f4020f00d02503482551014580000c20904500700c840c203010040025040c4048800c1d04112610f5441d9842e81c0140b0701d11400200ba41c82c03035103882c10700ea00c5001950301c2d01c415000703009000d240c3d00d005080607981507190083d40d90010350740581034000c0b9001c01d0007401440004810020640324100303000f81c00c2c001c4000000314480d542d1284444d04078005d130308 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 732229244 1250 732227994 732228001
    0xa0306152601060c020103050612060115080703090210030b0a050402191e080610140d05071805030c040f0e120405150a02070303120905071710110405210307050d08 72
    0x10740503206030480c0c02594840f5400d81d401e0740110003a02020f001c0d80c2d4825158030780b6001d4080300344140c600070890a01c440d035040c3c071980c82c09071003903c00034100d5003030600e000010805a2911a2003920b84c0c0340500e000114508036100051004085804c0b0b81c1e0030030b1000c50742407910003a040700403046a81e0354035880c1c11130649118507140543c4503440c1d50006441040400c2403810011504c0c8041816820b00c2880c040780b01c50304043d0358012090b5071147c1501c0c0d0341480107003600103015812580031b025105007610f0402c008660f440b804207400c13a005070ba440c03203203c051035010b0780024000f980c414107840310300408a140072066002401082d20640ca00c0c10840740a0a0403402c52b000c41c0307143e8001d0001c03145542c030103070b48810600e0408000f907a2206419400584140300c444040d02c075100100c90200300883d030003031030b1400400c0050302d494038007842d1212418010303055604494044400401c004c3c0140c1e07058160011a10002c4030342d1001141500c03c0040c003146040356040140d41e00c00d020b17035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 732230494 1250 732229244 732229307
    0x10061403060a030605181b01030e0d021b0105070c080105060117100b0d0902100801380f040b040603050106080609070f030e160305030c01060801020f0f0a030615 71
    0x320a90305542d00051a41e0100009034150304015404420340e024810103c10307400403181403501c051441c003200c4000040c110b03a40e60709446030114104841000f4000504440400f96850301305000300c6aa0900d0081c04000d140e204a04503484260321464114407290760340da60a02a110170745075203000c20900516800d014204514840c492a20107920000881c61301d0000e040c03d51003900c4220009807141d9114000d61204c450300c00d0756500310b540d6692250325000a000c1e481c612481d0349079255030404610400c40c81d4003490141e83c8004c07540950760b2035510000c45030784da1055038400b4540c000c011400140701d6030160300ca117048922507240c0520700d075a148200044010f040b96900c001c20601040d42c1c255500ca940b081c1c0c50212500100d44800d01010001c02038440694404ca0f07165100059821006c6000c0c0034607801400c1a80c02903040c030f170300a0780c0040c240c00344174483c000440c40458081c036091704c60b800c10030061180c0c0c1511640e0b45020300c8000c215074810075035075480e120084550300400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 732231744 1250 732230494 732230497
    0x5030d090806092a031005010e0405060a0e10110c060c04150f0f0804030c080c1f0b0117090102210403030b01020703020f010c080c060a05091b06072405100614 70
    0x44c0320a82841080d8a0011110700b0180c044043c2a0781511400b0580d0f40d02010364410180030b0208819076951924140c41c002e80740070030080c20843d0309402d0032541142c0600005100f143c2c50965040030500782c00c0c80020303a01a000d2485113a240380716a40c14001110000350051044c1d80400e40c074900302e29002078055585401c03e1540c2c1c0002403400006605d4644540a0a03070420b120746404408444541c45811054201040380000350300441d03c86182c80f08080002400004402020700244030f003100060100c0034082a00c0344c20800303207000240408020343c100d500340760001c40d07a180010401c00700110018030840b41200440e19040000e00c0a40c0000340140450398000c1035400342c02c81c44001180c445611310300c1220391400602800c041c8480911045104403000140010140f401c4074031039141458041c140f60f40c168060100b541c464507264102c0d124540c001030368100303c0f00c80c11104400860000080e40c02d90f0310340018000da6044204050381119441d0f030751500700d55010b40300380310300303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 732232994 1250 732231744 732231763
    0xf0609091e10030804170f12040602150408040515071406041203050f07030b0a12050303100b0a050f13030506070f3b01020f030f030108070906060206060906040605030d09080609 78
    0x111300050004208140d1601c42c0b03100200e00c0041a01c2d200c0048841c11031a105002c1c4940300320f10700100c0c0a11801e941045003140c000c011448041030740c1819122030706640318602902d40161707800301c0c6841c02c80341c40d2b80c221181c4682c0b0460820100d11004545500e950040d10b04944800c0c03004c2d4912012403080c0502c90180c503c0000441184d205d0307503010f0300145492401c1c103070030001c02003001801e2440d42c2c0c00200018001e50286580745002e60004d40145016040000d040c3d50a1140082e2182d05c0b0b4203840001c024020782c107940741d03018101083c009600782c0c00107007984508800c2210060348801c032208640074980341c48007034045a400c8400c4485540b0a40f2181c000154807d180800024051082848040c01518a41c50707004a08904590080d02141e8181e2000401003200d0003080100384c0087c8291a410020203040c00e000945404010b02264802d81602002c903206540b142c0c45080203140c02800c85454002e80540a440c038001703489400701700d004400010760707074400104e46200c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 732234244 1250 732232994 732233003
    0x112030f03110a0c1401020d06090f02070b010308070c0b04080109020310051b0706090c060c1104051603020c1501060f03050603060108031611030a0305040e1f050f0609091e1003 78
    0x501d00603e5003100c400c080c0d90003d0b075245c0941c1e80660110700b400c1c03004003c0d811808401083e020f0078005001c041d503500b90740e6071114920401417040442d00070000d41e0305496000b442156038142609014810181d40d401450840c0070000340002d54000540c030022201e8800e44c242d82210500615480441e001258528550700c400d101801c00d4030110401441954450b26000480c400c058444070300d041c40300c1e000140401c041c20b00e018240103420003491500c4508032414821490104134500c01c24001d5a002c00500d42c01144030010131106001d001c048402450491036036603034840e0b0090054130b503101443c000c40c0c64480400d5403800c001c55442e0594204400079890407000d00c0000b1034a040e401c8050f81d580e44000800c0d0301c00c2d60188800203c03103000c0c0e03503699110383c00c021711a41403140c0030306216990504a03128220840300c0c04142000c440003242c50b0b4242c0303a0800301141d290312451014941c001945030820680c0924501d0042c51540b0404807244180e41c0d290300d183c0e0f41c1d40300380000741 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 732235494 1250 732234244 732234247
    0xf140106050a140301060215010b0c2a0409080307031104050901030b1009060b0d0e150a0f020d180b2202060a0e0904050d08090d1b0c0e0112030f0311 66
    0x640d50203035004040081140c40c18441103c01d203607000546400030b07001040141c2007030440340959510b5040c640e0240000c071201902c0c241d402c601885d40c82000100450019201c90365098802801991302c244600c0060414004018585003034155544116080000b10780341407105030800e42081c0644041d210041d00034140360b400c0d03864492014600409140c0b4480c101800491860054001c4000400441e0080307034981844103240c03015100401d486203155800080900e921002c1e0b050f1498216880040c00503c500c00e01c0500740191190f080420462818542451085c0c05141c0741c02100c24000c6403110030584500f1800340120307410301c0c802150301318180403100c00351902000822010b05541031402c84021100049004224110703030980740d84d04400e1100a01c0c94111004652240707111002c1d258452206102400002e04034070a0034226030700541e650100407600c9254005010803d28000b4690783d038400d1186485901a800c4000440c080300499603a4007034042e807900040c00c1d0351800e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 732236744 1250 732235494 732235499
    0x608030703080c1e07050c131b11100e0304140603010303050d02090a270c08060a03080c0c060403120306060e0d0209091f0603031b030221090613090f1401 68
    0x102104d4010510400b907950b00920501c5841e2215002481143c0c45400580003070401481003000c2100304d03518040d0b1403802c141004c92010b200030011a050a010b09000726800c0c50408810702e400d005845001c401803410301c0303a80305500004040c0044505074281d40b01042004000c0c003145000c00e12000300440d8050188029190b0f45801a0000380380140c1421000c6544004030000402c41240740034a00685803109842400ca50103406c2c95414030341484901e50518502203442800c0d01c0c80b000d0b10070751021074240c4070700d00144044500098001d044a444a03140d0410b130290390121982d00011919201c4001226030050010350310081d0006c08510428509800740000300200504a603180e00540c2d9482c1060303c1c0301001c0059081c240b14001503141d045140250040c00840700d5010940b03500302d000d60011342d000403e01c441c0c1c07541c10091121014100d841046a000b4503500c01e610200100b40b0311302a503280d41c044800c461003000c0505c000c4c0381841d1250708584072040340e08188200d0030010b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 732237994 1250 732236744 732236761
    0xf0f20040b09060d0e07060903110f0303041802041d0610020606060a0f02340b0f16050a0f0302100f1e020306010c020a09090308090610050405060111060a0c03060803070308 76
    0x41c03d00004500350100c0d45a11707000c000c0e07060082d00c0c0c1200b40803903e40312043c024003600c440c40400250f0203865400c8040e104c88000b030307500e0141e8454800203a00b18240c003030301c042183d019100245991711019800c0b2a50328a2426180811140c46014078030610b00c030003a080c40002c69500804010f0b010601d40070710003070100d80301018030481009502c80c1040c2c0010707402c40003543d040071380200c0d90a550841009840c00c068178045902a11442a052000400100c041740481e840c031102141220002040c501c3d00c1030408a007104090402d07101c0c00b030302c0410300d0303001308405a1141d6000420050804034401240c11116003607201003413218111141c401c94203995000710780122050504403a540513680c001041c10100e60041d482250b11160440d04050300700e10707243c0e0011011000307842180740c11182110103406d141306a62085880c0d101256440e4065030140c00f2103a4110300352165894007900f45005040c00d014080000b903d0301034002a900b40101c1615403440d0305507174055503911840003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 732239244 1250 732237994 732237997
    0xb06091f1202040e0f0105010305011d1e010e0a0602130617070c050106090e010e060f010308030c07031b08090a08070602030d1e15060221070f03030f0f20040b0906 72
    0x2040383c00c50b0f582c41c03100c0c00045042082010407414100041078941c10740c5002800e4610784400c010075480407800084603482c01041a04585940001e80a04020051304507405455010305040c0c50340950080c102c14000550000c00981044011450501c0c1d5544411120100e203001c151065a42c2100032a2104e4810805045020700600010030301c1600d0b581544100c880341d145451061b07542e082c1c054000e00081c05429032011401e007142550b503245880d000b07440d200c000d009070058040000e890003058040c00398a05aa0080e032100070181002d490039605640c020349440c0c2c4034001d0020005541000000c050080d50a0b6501440c00c01400e584281c000e000b54940f82507200b500083d14008a114902c200c480f00720292031465030741031800202900341803118407070a6071901202424001410504201c60150f40d004045031000100380c2070440c000e115060b00c801c00036042628210402460703402500d500050200c1055240f220b64041020500c1540310b5035008600a01c1240a1854500b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 732240494 1250 732239244 732239279
    0x3070c121707020d0914090712020d05010311040f0605060f07020f0303070305040617090a031416060b032803031503060203010b25030c24090b06091f 66
    0x42006100c00d00590014603048202d8480b00140e0211204441e15076000701c040000380248110304400044501c0810326141d4014500c1050100c0f0307500b103916140303080d4103d40030031210307000400075540c4910301200d00500c0306010903c0b5038201107210f0540599841110200c0302c00405a501d0310341d58800211503500b01e8007040c3d0303001c040201102d40c503840500c000d00541e0f1003944c03a15030321030404501601302e0140340e40030b070040100f00c03040241e00c0c0c00000d00c0c13205490301400d20751011b0340014a16034991046c0100511281441d405103c2008607035080b61103030300070840a803444900032007001500b041034591112104030102c00c1c680c010038065448160740241c0d02c0e01183c001c03070f03e036124201070346e2080e4800300040344d002038000c0b10b4560000d0000d0b43d13901101d552890041c21500c00518244000038013410700c642c86140062400d101c121004203010212805000c06503c600f071000034140d049448600481c500c20005944e0a018002520382e9811900701d03404007803c2140800e0711101c0e42 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 732241744 1250 732240494 732240497
    0x6090c0909100f051006020a080702040218280503030a0801050d03030902090c0403060b010804120f051c09110909151b2d0f0a08041a0103230303070c12 67
    0x542e101080202d015001848042c02c40104903410722448072041640d455001c0011034011920280014000d4012594603540450b0050380320345101d00c850f44107144008403d4ce00000781c16a00240101c810100c0802581114154803655075800501d5200d01ca203084250000b440c820042c0319914000c9510f00e5154002d290000791090300d5408181318070000e440401c9c02c040c0c0072900300100141405000340c1d920007032815064508041c1d0f0f401041d00701c0200b1407802c0c8000c00140f1006030b4420403d45100c031403c00c04048109070850340660050511500a8480800f8000c088009052a000050198a0f440001c1040c0504903444100e5020050458400540014890000c035410000a882441c0c0c95907030a11203c4880c0480d250103401075258540e01c60020300000b40e0021090040c1c50406406003400b01c1d407966180b51480c184003480d000360315108034110010040c840481c50039120341100d00c040074030595800e08a540d03240001c0324102c001811115030310300000d44140300c11004e840e19 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 732242994 1250 732241744 732241753
    0x19200c070306111804060b030a0c02010e0d120b09060f0904051002040b030601080708150d0c15050a02070603090c0504090201050702030a05010b0f0402131707031a06040b0306090c0909 81
    0x40b59141001e491a82c1e400401c0320402188510700c0c0640c10240680c036240071501040b609150903110002e6000040400250036501c41d026038216002703401c4104808401d0040d500d1141c9070b03400103001041c11045002500d45000e00c41c4420f806c4c1f1001060280b00010030051000b03014104105031404020300442d0309014a005001d403003c4540060405807050840b069103e24200000409a04d0010480801c120420b000c0c0a040142d059142400380c000380c410102000f0345043c80d1401e07105d21780c4207144800d8450000403419074880b0103409000881e5003558191560b901045050310804074000d80b5407002d444082006182591050208620604040c0d041180390b80010341400a079400555441e5100c0d030a94500f49029001c480081700c040310f0841c28402d20f040951003c5100b8050314030030401103a070b0178001d000308206003c01907511240b008048400b81b02490020001a41d03014000c0781011501451443c0c0440d10034402d4008000a00045100310104414864081d003810b407079000e0f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 732244244 1250 732242994 732242999
    0xe0619290409081215010f030203060f040506031f05071704032a060f0b030c150d020c0a020303070f050616080a0903050c01111e09130209210619200c07 67
    0x113221140314032a58902d01c480c0740390700103d0009003d450b0b050b410030080520400c100030032655103904601c0c4510781542e000419680b8440030178070b402d10360302c1c00038103c6d21a002c103504c80c81c2990b08030501ca00a60f40c1d8400e0000580030180242c04070907038006012030340300e080c0003c0c05801b4181d000c4040000e54001c0c03031249400d4683c0300441e100d40544085058580e210017203503040030020b5804c49402541d840100901c8403240c4cc0e02405400b5600c1c44a540001da2104807220411082d812035030010b090781e41d103020500d00b00e520301c1e82c01d810031940f6011f1180040e0007030324a8203030203014a40c00d448043e0301c0d54941c0a80401840380c41c8046061040038171070101303516000d101d0f80d0f20740008110179030358070b1000c0780001c07004005c0078042400b00d83c03040106a000d0b458200307904840c00316400026803180030020004803900ca01c41c4200340000000703146100a5000004c01500a20006010040821420418070144c03410b070b400a85503543e00515020125990000501e4a2004581640e10064 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 732245494 1250 732244244 732244267
    0x30c060c080d0917030f0a0b010224040807060e06040b0109112a060106120b03010c020d0f0c0f2306100501050a0512010b0901020f1603030c060e061929040908 70
    0x104207503921501841b44500b008071011040c401da0200b104240001d1800e00320324440704d2655000c110603107401040000115080004040c151140c40e50320603420301504420b944d0030b40e6141012601500ca0906800000400303034128815909111071140c00c03a07182c82d107200b0716100b07095804240f101c1b480312105010181d24005201035806852941d603000140100b0724401700036140041815407090b454003003d4a8950740004401c1000807103070500d050034007816a000d94a984c10b0b00005000600c2d00804a02003007007140811a1070004001d800c0182109440d006a6906080f15501a03044e0344107828005903010b04041c011280d205c2c94198900030b0320f6045680f110b00d00303a000c0004280042031110391584c05010350707640c3c0d03800382000f8075038181140d001c0c00c581c0d403036484003500b4030482c4a000d0013480500d412a070507400105c02211045c0c284409043c100a00c00038115030018501500c001d429000545108800d84200c150281c001a0200c10003005000500044590013000c0080e0350700e45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 732246744 1250 732245494 732245497
    0x911090c0702130b01020d090510030506030f0a050a290a0e100218090c030f0a0c0e120706180e0f0907050a080309090a05010b07150605040f06030c060c080d0917 71
    0x2080341d03c1c000c501550a5000645420b41c07080102090000c038850a01140e00ea00c101b01013620320b146000315880d16404086410000c510000c900d050096a1004091200009003510f0300e07480b800842d40d8031002e1512128002d901403800404c0c4044100c04255a50500c0d00007603980100241501c91800e00d800c0d002080340d001c40d8110070400d00c420041401840c20501c059807002220312981d246141c80700440c40750344002040032907100e5894030404102849602500b000060107000304810700e400b4404e0765660f05062007100005a0b1140c00111030031400d001102c211207004070800b466499101030442c40403001840b50300144246080000c469843d8450b140c002d1101c280699622008501481501c1d0349c001c160030103150404004000000d04202115000754018404005200080c1c4155010341100e0b440f0755441800c00c03010f065032622951140c01200d100e50344000c0e05655a00d016681e04500502c06400424140b0101100480f02e8000d80102c501c40e01c925082c0b00f07912440390485 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 732247994 1250 732246744 732246769
    0x1f060b070606080d020a1208071e030e010b1c3c050105060a060c02010509040e070f050109051503070c1104020a030207140106030c091a03190201120911090c0702 71
    0x25a511042c0412505a040c0101940d807802c901c00b17401540c0c92511050003036000310860400b00035000000482051098a000c0e0032000c81d00d040c00c4a0080c4101c0040180c540710076407400c40d501c0d18020080e10700d0111b0034800d40340d494040f841e402c2603240d110103d0340b504c1c130307074042c255080080c1e42002000d1611105404010740e003020101130500301d003089421514001c2815020b0782182d202800140d42002c11b030354289074241b030305958402204022030040d10340d14009040c00d00c87c003000442e1248075440000306886003030380c55410b00c80e030354810404003188400707a5803010300e420404646818440c0e281a214240643d0400808200c2c5102240403a801520b0350720010341e0200f500d0f0b040101d810861802a0302401c002e1050340e0564840c220000000d205075805281c0d1a00320510010810b002d0072100ca80080c00e40b19942008120a041610728000490000b100700c444540089028844c0d0b2a505030482c20303a54044003240140098501c001c0e00355265003174144510300042c2d486140072070b803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 732249244 1250 732247994 732248003
    0x7090303210b0d05061b031b03090f060f060f03030f09040c0203040806041505151302211314030c0a0609110316080c010e0f04020a0c08030709060f03020c1f060b07 72
    0x742d1b4a000f04c001224038000003404001c44508209122100c10003514100041d105040c510303549480e41d0780302c0c500d442620180d03042a80160b208118a048a1805aa2017046c060b01d4019030320205104060b220700c0b40c0d00040c0320014003840220000e04080e0305c8488090701900444e4038242d00c8407905450030300202c1d0210ba118400d180e9602c00c140c140e0240d550408810790b14078041c0d420100000d402517030303d00c00000c240c0b503003c070350b000d441854035055140c481c1c103400404a0600301000c03094428680245d00f0340e0500d0794600044520440001100c48409044000d882036200690761280506074403201039501144030801c41d1001e0368188190724102c01d155880840c00d524180902d0704103c00a00280d0502001c02d50035410b5442c2d04249006400040f200113030f49290020f0207442000400b00040d041203000f20030810b0b2140c0100c0e020051b00c80c103440d050300c00c80404008030203070301c1044200030142d0400c9030851556011020042c203521103a01c2c012032410384800280842c0d4200c0c10050b903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 732250494 1250 732249244 732249253
    0x903030105010f0e010516022202180a0602072108030106020a021305131e080c06040c120f02040c030e010c03140f040206121009020f070b07090303210b0d05 69
    0x101d580c10280800c411411810001004111480080c206000781940703c4401c8140c0b071240d40c210340e036840b242d404000d0240c45084000d03411215060094002200c52800b40c18610700c58241441c1c0350710704500b22100b5a000300790503414034903e84004500005413519810b1760300a10703800124442c000c0e501038a41c1d5401081d540aa50040041760340c00d00100868107481e02e403d20102212665080d07400540005070443c0c505058100300c02d6034252003178081d001c9940031442404c14200450140e0240b40125041a1450b445034420444a81e0350708004040c0010124035400606241d0400c0a5814050400140004400c905503094440c00441c0b01d000a598510055101a00918464018400c240d10b4120b500d800d0780480c101c0c0c458800d14480005200000502c414000000500075201c000400d64440130000400b140b190083c03034044584464440000f403240d8403c1401c9412260075640340c04e4440d00405005100401780d076150345029845001d0072120340c440050b203611080c071800080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 732251744 1250 732250494 732250499
    0xf021204081809040f0b1e13030c0b010303020a0b0a0c05040302042307180902090a050d1b030303090c140108040b07021e07140607150209060d0e0d03051e041202070e09030301 77
    0x8090040000708000444680034010f921144044a0110750002200030116104230316414150752818004400900b074000440001c0704055002c2400003c480c132505030348035240c81c3d40c1040030030703074010078510800a6070501040025160a4001d410a005582c1140b10070031041240011014070440d0540c0c041840c590b00032244103c1e00540710010020000114240079102000581100c0540b06041c80b50101c4142a02845491400e20032586404215602070680d01d207006405001b07000c4050782c055080e07080004160102c00d4a0301d4070a01e050f036560040d655650b030380002c0e186000e0401000c5120f250320342f102c05c510540300400c613005004000c204240c6080c0800b41c0d1812404c0240d80110400d00c8620009031180c1c24400d00005003c80250300c80c1c114002160035070051b81e09081100d410200305204404010803180704200042d40e050080f40d4400b0021507081070170001c041d101c3c0c10b4500000780030500c84c0c40380204052031441601c01c0d256440412080100d42910405a00c1c0c0002004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 732252994 1250 732251744 732251753
    0x809310902010e040b1c0215040e0403020106140120010f020703020c1e090a23130201030f02030c0d021b0f16080d05271905040f021204081809040f 65
    0x106512803c103d4003800f8560300b410104001070070600b040c4444010b5551072000f107603074030704c1c90441d07031300406516984407903a4211f50110b441c0240c03019030155180107000301d9111304900c28900118010385480c2c500e03c005104c07003000300c207804415110555880c0d400d1a0503108500040540c0e50107580100300f04413540e010032100c8401d4004c0408060221401000c26459200e461a03005107800d50001d42c1980310700c44006841e0003c2001c4000f41e001104000680c40301201100b4128001e980400030b4502101b410812880190365103a180001446000c2d02100d003a002400c0a00004900c21143c0503a092410300e0304404142030381b142c5d00b080101c03026624010340f08200a044038401000c0040702c110f0302410500c2103402c26845010880701a0044918031b6904490389680038140c1c2ca05100420412507810b111409094401d03030401000310010710542c0242c904c41c0300c8901c201c01d8035032181d0766000901d030b10119101569a0321354001c07114a0344c9054185203e1400f070903400540f5049880c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 732254244 1250 732252994 732253007
    0x18051005040512010504032c03060c030a05090c060d11070c090203041e1716050f031305031b010309051e0601050a060807090302010e0a090204080304150903080931090201 75
    0x242594541c0c501030811010036400503000c0c4070a480844e103404004410380f2804100721442135540c0d003601c58541400600c02c0036000444c07080352372a038100200e0b228601829241c0b4120044554056014003143c41400740c103500c8070343c1d810207004215140c1052942c59805000191344124800c540c048100000e0003500e25070504041d444400600c03c14400d584d891200e80040e00041c00011000f1406024510044810080050300441120b0381c0011280340c4a44d80d0f032004c02c00050000e00c104002502e8100015002e40791004004d4089195004400440081c5144281a80d10303105130741c80d0f4203514023044601c140c00000407018107119030424050050042c1c2e1342c0e004c0303004c00000b10700708491207906c1032440c81501c0d42440c185007a202d440300004d408520b240c2010101920009000894810000052003118082d5180c00c100c4904204180c44a603880e21015200a0b002c02442c142854140901c0450103181c0480b8000c0c1010201c14410302000720401c140031550350003650003035680040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 732255494 1250 732254244 732254269
    0xa12200105090753010b0f0f01090e1b04031109010b0a0815040f1107020301051005030706080a0f060608040b100f0605030402030f0a0c030b061e01180510050405 71
    0x71058032800404960803010144c481da901401c42e0112003c00d041c22900b610400c5440038130501154401034044566009150418407180b00f4800020310300741a007040820036100035416150390340001c1c42d04040c02e12410380140a641c2101001034034081d03640c0000060405540502510100740035900c0901284c0201a0841c001c101801d1002441095010116551148001c5d810b00c5030882c1d00f60101d400380c00c21150641984d420120601039110421000d0300307082d40220b0090125032a0140e101c4041e40d400c2c041c058068100c4902800200e014016558000a41c00800121980042500c6040326000d8011100150048090000703115510405540140401d006100c02c02d10341400f052900c0b03468400c281c00c1c448040300241c04d41d6003e2010310f454002070400c0c1e82140c005440d0030816001e4a020072501582004040740c0c0c642803024404801880d805064428414000d006450714a4107149410500d500e184000c211030312b406400e03047c0724001ea198030340c9980c245801c00040c001c569 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 732256744 1250 732255494 732255509
    0x20303070809160311040f061404202205100518120c010c03140c07030512070b130203030d0f020a11030c1c1806090e0a020702030a122001050907 64
    0x80703c080240403d2085400c0444c0e030f10400048288107141c0104000d050302c01440036803580740840000380743c42c0040703a0218800e41141c2c200b210f01c0c0e040d90480002c00d440501c0e500c0740c002c140400900480c0c0312004105c9854461301458249540700c0c00998260340740b1541d8000a4000b04440710030090544001028201c01c540d03103031108058008a656400d50501500e040140c4603d00005041c001c4080c10100c001c034950403a655600b41200395620081c0744030445944c80780f43e2607418401030706020707200740390b50100c060341c6a5100d80a00b8020512a400143d1b8103000400c05144d00c45c00c5c078891603515004010016844030748407a00500303440500c0c50081d002d40c1040140c2c0c1485000402e42c42c840540c00d075503640d4800c014010480c1c500e0300d030a0480784580e0390001c0c00f0500715041002d00040304c00040b41c012460b511007080d101607000d01100250140c1c01800e022000403081004400c4860441c0350030342e0310148071079a4080039400d892103180707540d669900780001310784144404009072904 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 732257994 1250 732256744 732256753
    0x190c0f1209150f0b03031801020c0312031303120e25030320010207080c010504060c11060615130f050a06020601030c230d110424050103052203020303070809 69
    0x1140c030380304038481c002032008503110350710f60221144800c83d5104a21854000c0d0440340c88140d022004070314104030518190251003852820103c03071a00155401c1600c803004441030039919280040307507400305041011000d2040300d8900422a694500c551800c400903c80200070309250090f005040e000700c2c00007541c2c105200b00c010700c04243c0000c1c4542020000c855041100c0380852204c40c02406143c500501c0d503040014109107240054008501450240204000206400c101030754806452310b030070328482d04940002041460505400c5072003100c51583e861030280050300e003080450b038030b802200b03450340241010301c9a42061801000a000280018500e075419500d0b8880c98084c20310420010061b1201c02c2e90081010906030109480003401704100c0b94060718144200e80c01400305507001d5071520400034440b0710050101c51011007000d90302d0400d035003440011001380030001d204a81d040c0e1655800d101071020100c800c06100e010b507024507242d0816880081081d14080d1468460394031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 732259244 1250 732257994 732258011
    0x30105070c033938070e0a0807090b0402091c0302031207171b04050103020d141e07081b0918010b0c1203040f0209190c0f12 55
    0x4205118010064140c24604499040245040c004492640420b8150402005001c0002d00f2078001c0003101d0780f240e0100110511680b66440181e6160b00b5000c10301c500011a12041820399109030340c001e009445c010714625410004108080541d0f800740a05c3da11071002080700b510704e480740c07140404007100c00b5444c090310741d400100da00d44a075001c1c48101c030034040d0b0101014020400c0311030b18031a2406800d8140340c0f041d00600030403440190511707900d81c4503000130721100c1301c90350b5454403a0240440c1d46c10582410011802500400c180b030440741c1e500c02d0b81c2c1781c012103124601e510034044094125141c2010404803040c4042c050980c40910000300c042c800d281280c4845040d6042e42040343d40c4d2a01040000a40902945c0039450525100c0c2d4001141c074200e420300034403808030041e0890700b240e05003074039101c214030040307601601c0c1000b400e50050040ca08400c2c010f81140b19044050791a24110701001f084a01c6030ba55400442c9103103061003111074102c0c00e6024100400c1c13004000b01030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 732260494 1250 732259244 732259247
    0xd080924040902030601022a0a0608090a15181103160e01150507140c010f21020c031e03060a0905040302150c13030503090414060a090218060f030a050603010507 71
    0x141d0b00500c21025000b000040e081e0f482000f410a1070224015207d0f04000c402d541c01c0c040500204030a40106105000800c5450203641091301540b40d1500515160000e5242c41000d0707010407480b03041d8580c4848100081d8400a2104040c00c0e000320114041c0200c180109413030004031040d140100c141072142080f22a03900c07203002d8111051032642e1502e81540d00f030111000c1c454643d004080070014003440c2d52200d000140881c100c04203881e0252924171003541500c602c0d00c6030456900c44035900024054002c001c0d0040c00f9400c006400301c03414203501d00d2242140c0740071411410403925000c070070840e5520380540b0481c001d00c4002401c10860030942c900079200c2c2210510510301c801c50602040c044400d02003100c00315600ca0720701c8009643c1328685a074603544402c00382481345d030800200190710f42c1c4c0c100035180242002800d040b401841c00034104042d400036500000c4480c01e01c9815903054540c0e8000380355503200d4000055076441d00c03049690454202628050090317241800b08000207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 732261744 1250 732260494 732260497
    0x607061b1b030c0302030f0c06040308061c11130c0512060a0605040b0a1101060603021c052701020715050124050301140a0807121e020f130b0d080924 66
    0x39802d4a01441e031032038942810f920f14812a0308070f501c07200000030303625414280414410701452003030340d4500440d115181004a408051400340701040e070444501400500400f81c0c0031006d50000d004815440c881800c001e040340d104801b00c4000ca6000134030f0710b103081d6251241d15400f080c100d07107543c1ea030303824030030000c0c040d018901400622603000244800c041e03000fa02d4031600612044001e01103103403207041c000c01940001d000c3d485580409c1f0355802e0580c0d914001c2d503100300803130385040c810030f844180e400d00700c041000700024865600b004844046468404030402e1780f031000138040382c954034080001d410700c1d40d510030b181c03029110f103048640c050381d026044a0440e5860741c08802400d0307092000507103900380b0b5882401544908000002c0700c441704100d9800041c000d6520711680400b50791610200c04402030000e610007510345040516280140e46c002c85d0007083c09002a03020811004505038208541054032900d80110b800000341c6880c00c01420424400e4008070742804440c49a00010f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 732262994 1250 732261744 732261797
    0x4051c050a0203041a1c0606140c06151f031a0102210c07080307062310031e120207080f0c0303040302240f07060f051302010309110607061b 62
    0x4428148001c0b0401c03170b801d0098802c80c01c28810001203507000f240000005011a00c1070b200415030761106141c5080240058230340c650b80321b02c05451560f451201149500a81d5102c0d241e00c0f80003810394410b4200c0031510000301320819140081c50000d805285400b10740b000c91554110f40c045910b0040c4041c2c409496085115507075400f540b03c111001805043c020070f84c0008006100100b10403082c41069040040041810b410002d20220202406c1e0030081c0c0498981040c4003550004200050402084041000d22000d29460380e00040c1d9075600600c440504003801a40301c00428030040c4014403141c086681c5007001403210111020100e601c0f4011884007a2203010385c1c400100080d01030080e60030031f0759032950f14513503207003100e07461810980c20200083d00e42910b07101038181805800d1040034020710320030040142e030050950044010300200041102e5060010705c40300001e441e807801911089100d070030f0100d008640d482c0d4204011551942020400510069015075042c107072898525 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 732264244 1250 732262994 732263009
    0x3020d0c03050412032a020603220c0303080a0c02030306010212130f06120b0405042a0b030c0901020c040c1e1103030103030909140705030c0a03060e04051c050a020304 74
    0x4034246030308090b00c440c01140d01160710066400501e50170141d0054110722414811403030082d020900400144803040342c144000d4010000b000460304044100f001d01e0b50344400ca10704018030460660701c50144100951048011811000c1440101c1c4c0b06802103600c46c1c24148011421480d203840000d54903104044c000b040c400c80007443c4e040e00b019041c150720140240c06600b42c4060303a242002071141e5890305203e250f461500400380f170149801e01880b03014a4222410032404011042c40700842c3d01840702c2401e0070310b020b030390005190140402940c0319160401c0816201c080304000a410400d0003100c5511481c80c10450401c1990030800f44100c038512803098402900700ca11050f108030407541c50b01191444044000400c15a1292140c3d05032003046d001408140e400b00764100d0942c10540f10b940201c0e409000284254443c0000ba1105403454640481c1c0c07990742c3c0d90200b000d4801500c090321140c103d8510f011030340b00a00f4a01c03040001c10302d8400e281c20a40b80c0025100e0041d40100b10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 732265494 1250 732264244 732264257
    0x21005060f0f0f040603050d020d050406021b011b150e03070210030c050d06241d12070e0a05010e0c07030c260c0601080d0f050d0c141308060604050403020d 69
    0x8090748441e50701505081015100700000703a06d030b003801a942c0c060400782900500c210200040326030701c00c000f9201280c0c000d80080c602c1c880c082070b0b0458020852143c85041009034100a8074000d0300100c40000e19018940c0488044c03504130081003990342d038500c42d203190382c410040c40c00142c03903c200c0c46422444c0d91600050645001c1c0d01143c3d6072050300c209038882810000003154003a002d0b0303e03684aa000c000c103075043c1c1002500090360b60030346102c40c0750060012040040d95500f0321180c3c0d00700c206003020070750300800d4484e980d0b000040c41c1030b5282d0482c40d0b030383e50052104003da0104a504042da1901942c200740050794000c00c4200085001080000903812030032415802c41c500c0d80342140310400030703611950309a0b019542c034039003403240c0d04941c81001000900540900e4902240100a03981d151601d00d100740120003401120050b6010080ea2010035141c65989001924000c4042411440500c0c40e0045192800502034100c40c451858001071000080d00018116002c8100e0f00b00032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 732266744 1250 732265494 732265519
    0x2010209060f0310081005150418030f051b01050103111f0c060605150a09171504050f030c15011a070f0f0519140c0d1b0b0f0a021005060f 61
    0x1c4a000d00d060740017220504c04d940d41d00e814a00580c200c90b00c0303540b10941203150180d92004100589605d0000e540b05200081c07106400b10703100c0d1810151615650a2a0349006680803100302c00c051100c645405a942d90741c010303c108186241e0850820004032058512014100b00044880c210040150144515488400c040102a0304008000d18008110710410418040200043c0d07200c0c01c82103002422141c408030348242c90400c10141c8494800061298030349882c903d04200300701800035500b0b0b21038004561200d1030100014210440800c010348105079092690054900c0c041c1c0012040710200711103030941d03d00c0d034070641d4880c640000c2d001301510103d041a210311522090050f055005081030301c142c0075000c007400c1c0c2d04648508400c048a02c030781e0102c180c40f000805643c543c0503a8080c6004041400e6065480300d0000061100706600d903134810307085a5502803811001d8090b400306071a12056014048503000c081096414051840c00754001000c11810b840e140f0711454000881 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 732267994 1250 732266744 732266761
    0x90f061f0902040e0106080609010f0b070201020109050109080712030e0604030c080d050403110f070302030a0206070c0e13030345060e0c030106080f0601050123030f0f0702010209060f03 82
    0x810004000c1c100c0d0865543e40c407001500d550f100c00340900d01c0130680b030f40003050850500200540c101d90313060030034981d014281040042ca551051302d040c1c0c1150b48540c800c1c6c0120300280301c2d000c0014498443c655645880d0700e011814814072410700d80502d403501160801d600404141140c0c010f0b414030380b162000c1c1c203514180740c1a02600c01c0c0d070084d1625010030003003096000141c2c200c241c0c201c0c0c8200e4100b664103c1005540706000d0200a4041c0c110728212001810080c0c0030b403180714400d0030801d02c0c564075a8401e0740420700031142c0000589504d9001c505041e014482e820101604840030221140c2d180c01c1c14102031007080303d03541d200b10b200801d41090a0340403507040509520240903c254038071150725983e14007c0c004070034803d502e044c10010344e81a00046000c000f5200c0c1004c0c22030380c3e2070700c00191800160140d9005004089000b1300c5402d01030785000b144141e1003094a00624104010306101021009007480190383c810070a00d505903076204c050303071100e011514200d40d1342da071040003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 732269244 1250 732267994 732268051
    0xd1707021506120d0e1906050d0f0605060706050f250c1b0f0812070b010308070320011a0a0f090b0a051008011e210218010f030b090f06 60
    0x840741c8013800360300041401254803109100b55882c003150500610441c0da40c1c541084500c51003404081f540411450501010903004008020940c000c0001d8065440c0081101030b0b01c004011501a40d4031002c00c0880032221343c0307040d00943d000180e100710448501444004108048040c02130004005100741001804003011904038850910042015030b00c585a41100f1903034081c40c805406603000e00400d1043c10816681300a811240c582c4171030346144c942000541c0700c001c060b410000284a00402060708041060203054148000104d481c00b400070f9000701d48041c602d082c0b0071a4805420402040742c1c034020002c0d00c803814000102802c441c800a46c60b5211603109541210b182c4100b502400d8005032041d04941e180d410700b00ea4140705010400100d43d0600601c00c0400013809807080d170b52002b00e0101035891001c0c02c80c5040f51100c60652180e56000d0340295644080d0351003d00070440c48040c02a04805c10400500794030003c40c04603611048024964440107005140300c054507890401d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 732270494 1250 732269244 732269269
    0x22081605070f060203091f0807120f020f070b090706021c170a0203011e0b04030b04111e1002010207080d1e0501090204170f150c1b0d1707021506 64
    0x1c1d8090342507543d00d03000794894104101c1944590400c6a0314018020040c03000d800d2103040d43d41e400a00d68070100180c40218408031682c40c07403075803000c0c1000c052140748010680c90151040090300c80d14986440085100000e290100130741083d9000c0001940005112410408025140c001c0306200c59045401040e8401020208241c0405000d02c0000360341c01941620703203050740b2680500c3c007000105064003061147c422078075010401000031861070300200d5003042c4034403c0103403001031810020700811524514408140c5a030a10104285400c40700c507000450540029030a01c030003a00c0e040c21074010f03071404840d45c60f00c880032110403111501e00b9a13005598a407080007203585a1140310000d4019015103140d500c52101d40803840c11002032614a2140204014504802c0d404075500c02008040d05213000360a0138022038003c0740d1440f08001d034842084d80180440b20b0b600a00038406e4a4a0010048035480541803000e4198003080c0100300d20661100c0f9a50303512040003241d400c09250 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 732271744 1250 732270494 732270509
    0x609040902090c0c21030403031d0d0f1b0309090b0f2e051215040b060c030d050109060e180a020a0305010902090901111c0b030a0503032208160507 65
    0x64100081c11100d64003804c440d5000f60100c402204501503200300700d201180b65404942024130001700003d1203900000c075021841e100803030545074800780c2c1030f02e440b0407407500002244508041072040d5600c242d00d0200640030315600010301d41181c40c05415000c2a028090034a52603400711601502c900840e886031030f42c05000701070700c0c0000d110b0150f00c00d070080940842019030000d8031460181301d102560000785441c000c0728120b8682e4040c01401d142c08c07070300003a0041e440d601e880074995646e8000d819100045000366540d903109003103403011250160004510540b0301041031200002c070061030741c2d00c803c04840c40c6510b861686103151a101c58840025405a011000441008019003010f070f40325100341d610003001e03200d5504280c2038644a80080c1403070300702402840d285010074070104400c1400100001001d10b1500d01281c203203041030b07000b1780d19540000f040c46040c01104401c0018194400e4401324010869501c1e10601d11030548460740d42c9610120b1601484014002240204200e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 732272994 1250 732271744 732271759
    0x1509070f0914190f180507050909100305120406020c0a08030f0a230712020d08060f0d020301020307051e09060405010f03150609060f0206040f02211b1203070c050609040902 76
    0x490b800394030382149078014681c1d505101407080c1c00c0c885c0603025641c064551a1a034500b4000e1107070a011072214010201611040d520300c00101203882031240c50141d4000d05201c07540e6606005c1c001c4c0c6400e0058540b14003413400f05804000440740481642c1c001d200301d184c40f654072011900c04441e604180300d6100742d1007070000a00d1540960000c014241e040c0310303866030044800352010030381e1581080318412011982c2a800140c007450300c010703070b074042100c014410041c803215034010170308a07041111000042100064110740720402120143c50ba0a24040c0b058900400000172807031900440c07007103030f040c014040f41540440d4043d030032600c4410a9030340480303c45513139100020300b0340d121480b460003c00c84407502c14580c0792007ca4614800c5400c00740d080110411a0b00b48031900850421080301c448210401e240c21020501001500882c0c4401e9154030080380740030040f201c400c03a070041d4500da10410918002610420302d14013118000c441c06502c8441450200380500714401c0020340c003400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 732274244 1250 732272994 732272999
    0x41a01060504090b030a022101020d050c0d0518282010050405061e090604090c0f0801060f0e0a0914010306050606070c1404141509070f091419 63
    0x140070018008440d00d00c2024442e00528809041d01e0b062800c03006500102036141003442d840f044909003940a02e03c4d0b00040c6000421911002100c8042d02c404c40701c0301000440b500c0c18081740c028a50840a50b5000b15040034600c024181d5a0351113154682d801e004d07503020b80c0300484546070035101003034012b085d418400441d840e5141150510b030001600c620001e40300c07000d1841c403c506880035508081c110500d050000081c401d00590344818040c0c0109081004960580304c040250000f003c03d400e000c508000680782c0070341500300411490040014550040088642c095540180500c2c1810328407151800180881c1d01000950042241e0030709029100c00b1030f191038803403241201c1c080c480c10000b90b1102410400c403485000340151410844400512820305c3c2c3c0c11440c03100900007440060b18403815906c1000c910011a9880100004050302e203140d42016036030300d81d00a1a6141925080400d0200035200c0002801001c04050030042040c880e9256200e081c0400c0d111980504012035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 732275494 1250 732274244 732274247
    0x1060206160c033e19030c0503040f03080c281e0501060b0913060509010308030a09022101050a0c08010b160b0a0e0709020406090e060d1218060e090609041a0106 71
    0x151440c404002c0c080c0c2e003411143c404e1602241070031a2001d0014030030303c5030010342c40843c0c03021556002901d10340410440083d0b585042c01d200c1005512665000781c582c1d24a40303035242461403019030303003d0140901d85000c0201d04450260008154080d520505034001c001451a8807402e146000382103618210001c581c0c04058005040c0312107040712010751402c41c003003854081d6a201d01ca210b800c091982c1c018030024085d0b002841e80141241c800240c441ca0a40014030030b074180440e01c0c4248090300000350407a078000e0040c25809140f000090007010400c940080c5001014800c0c80e203c281d000c11001840c214061030145904e404c0b0281e40c246080501c81003001300000e6461800030b100300040014081d400d40240c2d012a022619040c000e00e00d404200310441b00000e0a45a100d00f0314024400002e107002c103180e2007906250740f1940a5080d1403050175109806801080611042d207846210306d80e0784034500d0380e03c1003099440640544881c505034a8050007524070110289503d0300200302ca5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 732276744 1250 732275494 732275567
    0x306132c070803040506041712041203030f05060f040b220b030c0904050c0112110315013c030b030f160905070c110a0b13050901060206160c03 63
    0x810004280d510650703882d45082d83e00d1040c1e2103415040b000600c410001c100c01080707010241c2141c1d10035910212a5011038400f00e0b80150440c01d021404401c000e4285940351140c0304084d02420380400403810024002195150201c1c2800d10640c0c843e41d100403e41c60382d81c3d4455000400c0d0700b0001c681041502c00c4400343c090406554040d105440c003d45581c90715045040c080d0350010041c02a55504400444442107800351402c411038a604d0440400c2040da40110b209032442d0f092581181040340c00144002001d8446494101c05000c00c0d41c0703140c0801c074a69100700c12840001041d03240c5d03240c00340c02400d00d607080c00c0d40c10301405071212052400802c1070032850a524008400c000e4864407142c0459100b075070034100103140c4001040000e035030000003510584000300070303455165aa0350740c500c055000403184d1941c804191010001810290340942c0900407500242165240c10302e403919003c10943d4182d01000824440d0805060040700c0d48141007080e00c150b81190841403408001c02e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 732277994 1250 732276744 732276821
    0x60418050a050f1f03080403080a09090614011b060c02060a0b010c0320010906050c07060b060304080703050d0e03040603090b07080603030405191205150702070b030613 74
    0x4003030502001410308010340c0304440c03140f400f0210b0b070307440754684c0e007050b1000341032507480c0c5008001e452401101041d111000380009512504440d41e071021035541c01404a925a4003804289040030424024420406080942c0c26800e00e0903071815900000c4196000060001c06000e19140800c0755120950100e41288a031280b0241400384851400044130441c2c940071010700081c02230f218007000b0700c0e00c10581203c010703800d1002003000f0040b61294003c5030001d6900700c010410000e10002048101e004040e0b20580403075401d4150700d01034440442c0c0b8420040000c082110000f4124000000c60b880b24203043c4d0480c080341d4031143c4649024004082010f020384015a2000002d90703180e2050903158403810740a006141060310301400d10081e554242e091011001f1542008901c04007d48030301040c9a003d5401841412454042c1c81d0142c2d03800b404130030440d00044804d00c134180071031040341e8110b1001d554a40c5081200d0b203400000740625003518a808107c6140b981403040c400000210 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 732279244 1250 732277994 732278039
    0x31508010209012c09041b0608090d0206160c050a06140103020924090601020703140a02010921030e04060510170112030e130605101e0305090c1e0604 66
    0x1080c076500740c402840c445181e13080c3c3c4c209095110b042040c10a15581c80d0400d100d903004141307009840c0380c02680200c0540040d00001d000408001302d0b130004004080c1e114403203002402060802c0d848044d071204155001505004031511620100103040111000f990f41106042002078404d04004e010544280b000f030307202d24841c0010581c100084110030f403004103003880032000c1d42001c4043c410040801800e440c154041d6084c0040451a41001050305503481006030a1600b054400035046507255041022032010410b00f0181c41c0e0b1241c1c601d4100d10782c050400145c000c503014002005480150099604440a641c03204840398000302154580001100900d5090b070f241d40a440007080310f50300c0940081c010500051040c02c1440c03060081051f80f40700401d030191280f011403d0341079880d0880000419181001032043d000c0c1c10a04181401480e00303121034100100115560340c40025018458080703440750864408450f8050306900b0300180c94a510b581d95280146541210f050102d01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 732280494 1250 732279244 732279257
    0xc080d09061416030c030905040e0a1a060d260a08101517040204090218220210080a060801110c0f062a0702030303100311030601030201051903150801020901 69
    0x81001c5500741610b03c0380e5400c8030b0f69481501c3c651421141c01070b0404090307003840101311021400752218005c10743d204040c100201040784c820f00e0b01038503000074030505417222929034083c45815924100d60482e80b5421034442e45060b412807408103030030407100741c01c0c892000c0c0018064002a170060700c1d0300d00c10440b0000002c629584c82131044c20750103080820321700059074110503420b40005480341d00d030081e0000d000007401080507400b040040901066003c00c1480c1e07081001911001d0007402ca0004400c1c00c3d0b074900c454074036408920501e5002d03990106000c0d4807800101030540d56400f407002080000024041840001c001440c1640070110650940c041d42412801d03510380050058010001c60480042000f10f446030b450b4a0310010202c4286c0000c1086904050b9400304003035801207642500a08d0040d1641c68007410342c1c0030700c2110034040d4004400400247c5c0e0403d0640780d850641010107009111643c400720010301245416083c0c09031800c00210f10014158040e00d02050282c0341c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 732281744 1250 732280494 732280517
    0x90f1303140c03030a1e0e0706050c0f070914100e1302010507021e030d0302180d1e0b01090506101722051b0306090304050f01030b04053108160c080d0906 68
    0x240d0380c0207e400711143c0c2c0310300307000c002a6100320020144804003178282c2e03007124901841030342081d11a034800c11000703031030b0410700c40c0c044000ca007250340281c000c030403618945141030442809000000d19070288920b20b58010029a40110101c0d00440e80c01802c07020282907814801642c1d1444464582c0648504500c0c0a0303150701070f1080301c80a25042c1d07074483c00910408100b20441c0250001203c160454400582928901001d03841e900d0f44141c80c44009e940c10f18140c07101311503004056912070744002e0b072203d54554005129022068014030352003150b907a019032141d0b03007040e000030508015651014200600201007182c480c5075203046265030040d4140d004143d070300c1009071030901c843d40040204000c2440d040003001d100717000c1270401003840e007441d100107000c49000704c90b03060401c0321068200811071008a480d4503406c11800c849c08200040c1d03110b0003403900840850058040d29503c0401c28070800d5035001000b0181042115689102d2490040c04c4030382500c1181d001c01c1440380d52 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 732282994 1250 732281744 732281801
    0x120601170d09030210030905070e01151403070806031e100e0c06040e1504020406030b120102041211030721050c010813031d0a080a02090f1303140c03030a 68
    0x40c50368500c01e941e074030003020705540800541150500362003003416078800c009030005105009280040c1002000c0344090b601d404c1079800601e144c0240d42c000c11081c0302424407490890f0701642d8000c2c0880c0382144150341c0d004040b0340b41031401c2000c1000f1440703001100e0785903180024404121a1030784410f110032089400200da82c1c00c0145202507001c1c00a00090002104921a890b13111688080740c105c800d4000000c0b4080303a003c0d801c1400000c0c4c5400c2c03000d1031030400c0800d080c40c13104104001c43c0b5140c40c3c42078820358240345074002801f5802c42c901e0400655003c110000c05490075003d11002d48490b61200c0b603540b1041801182d481c050b02f059080250301035030034684202801c00c6d03c1402c03868030366000c6076440c0030605d4400825400e118403c866442d4109050050011040285199403041c010000c520fa030040c072503002a08420104145c1444401051a22382d926007000380e01e8010500d603200645c01903803540801c3d44001300070420f000301960810980a0100440b400504124619 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 732284244 1250 732282994 732283003
    0xd0603020402130321050301060f03090609030906030e0c0901090e070801060f0515090d08091f0f0201060e160509060715140105031902100e040608071526060103020912060117 77
    0x3017200202e241803004105903030040001007041034907450002007614140d541e02c802c0f12021a0103400040040c1000e00c41e42d6003600c02c8020303200b907503401030001d403582400180c9158014056488a29142c1c0c0424258100c20081c5d04040c000a10080c00b0207520307244052220840392142c00d00c124420a0400013aa140408840403104040c00703e148604081d2031350f60050f80400b00e0a500602034040096218410603180102107016a680000282d2420802425103003035030482c0e080c01c1d802c2418440820242c241d400300780c4495041090303d81a100f0005140c50003403020281560b025030031440c0c8000c2c56640718602c8040802e100c1111030740c88a0605683d03188801c44a00380c0c49141c046040545000564007050354011301e048446503000c2000304041c2c039001e6020328801c3d4071001050000940d070b035280803644900e0345011502d061011580310405698200104910700c90f41000c2109640320ba0100c40d9131440242450081100c2c80b042540d03601c10074403030105000100e54200c00b84070000704 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 732285494 1250 732284244 732284303
    0x81902030c01110a0230010b0301051807170c092d040206120a1113031a28180302060f0c040510030509030904060f0303140a050f0d06030204021303 65
    0x140144400090385d401e100c94081e00e404c26441b0815000301080c0c101d007070712400108942030000003155000c8140141400d6400c050310b80e241d031421286003090b034144000741100444050001c602d414030440090b0505001f80555040e40201c50700c82009041161041800740e4240d4101c41c1c03500c800050320700026801c1054500070f5000070100305080040001001c0103420001080700000c95040b41040001d0550080041017071000d02240c042051081d6a910810220303007154041190740361030b00d00e44022080401136903a11400c041d8143c441c1d1803540c0e0003042500039030100481410143c1c280655a902d080b60101c05050140001900c448403038410745040300c5000d04000c011026420050b000303844000c200c00b0f520b110a100b01344c06a581d40c003030000145010044c0094490642c1030003030044020f407600e142099010040d01000f90fa200d800c81d886040061000b0340ca51106944c00c2000e4030302548065031040c00896443d10312303040d40b64404110b91150f03134074206048401c448685800f1660 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 732286744 1250 732285494 732285527
    0x271f050108010b0705150a2306010c02100e1305371a1e03190f030c020d020d032007030506010b0f0c100501030213140c09010207081902030c01 63
    0x580c01004288412800342c00c4e070600c03031415502c8400c0312600807400c04100b110080c10791034940c80012001c03900101d66012040304000c6041d6a85428000038000300c580d4131000780100c960421141c40140300300c1c0c02a40c01c1d400100312202c690440036140c0b011b40000d07203a4580a1801041c0c01040c0342c03569880ca010a12100c00384003420351034902200c000c048419100c066150140140704d4261381d401141420303188500401440514001c041c9842e004c4611840c041503510a0303415404140d5003102c0d01d02d025810321f0000c0603d0450701c04200b60702e200d400b00a412000c03d408543c101504031080c1e02191030104d031a0b06829642600305966120329100151564110702c0050060041c9080205804200c50540700d14264111402d41d01c1c04000550610081e03a0341c600520451528a24108200c42184414000ca1285100400101c02d020b0241d240d808000103007404142d000303001c004020326222013503c01001d541d0396182a41a1540e808030710034001c41040c19100d41c0101030b1310000c1081d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 732287994 1250 732286744 732286757
    0x70c0b07060c0318140c03120c2a0915030307110102010507050702060301150c14030d1515031d07080a0c09140106120605040203011e151b02271f0501 66
    0x2d40c41e0440c40c02e9807000309111701c0c003038049140159182080340e02c480500c01429680d40d003841c000c500b41400ca160021408a1380180502004401c0740c5040183e2110f007107841c10740030784a0740e04107100c4007039406036107400d4040840d5440038041c240c420340041480a8000b80016560b80c60110340f188901ca00096229405000600c056650700c00009215405424844000d1502d620b03000242e43d89810b416925501c0002c00416038586409500c0805001e1501003500508154100e41d0141d05401c20502705559012016841c0e803500569868200d5040107944419868461150b01c40c645540103451418038008005000300042c403601c550009210943c0183d6420140100e421009440340c1c640180d0701c1c4d413404a01540c4a200441c02070106100200481c0307941e150316034180e0169030001d13003141c440c2c0c0f0000c100c0c9900305402825079092140442c4101c0010710000380203403614143c101d1484201004c10451071071080e0400d0165500c001c200c4003001307028950015809032402280d00240c034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 732289244 1250 732287994 732288041
    0x60201110a080a06030b090a05300c01060302040230060d02010f091d240603061c0501060b03011e08120a020f0d020c040b0f06090114070c0b07060c03 66
    0x802ca158540150803000d0206a46035030303817900080705200f500c00301041c0c0c20002c190000c100301080010603000207140303203003c003d0003203880d075035110b101c08144400c40d1f000090801c01d07801c1c00e51003c0d0245900500c215100e5600a03070040b290210900c1e040c504446450700d2104a625040000d885100c0c001c3c10b05020045982c011103101c081554000180300030890045500301030100c00207164a02e0b61000c0003039180c82d00c2109198007103420b54414203075501c060300c40151070b098102d1b9840313002612000d20714101036031200c041040c0d01002911a500c0d2031008200103005800440c100c40000841003000800c609400c40222054440c04269501c64940c2d8000c40146201404816007140150340d081d41d12900c0031420300d5001c50080d8011f0300702012441951a0601c01c22607503ea0644899242242090102d0100d100b01540300d414130026a080703022180b1741070115075200ba400003841a2083d5210911042508035400c203d0f66141048807a84140e48a84141030703190130001b292484080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 732290494 1250 732289244 732289247
    0x15030f03041a070812151c0201020604110d0f0501020403020924010311221a0f030f0c090d0302061504020f070311101d1c0c0305090105070c0902070c060201110a 71
    0x42c00f065040710040014000088024240c42c400c0d40b0440e0ba16500b0010244450100039211044640400e100d0092050150160341c1c0010341d0359020780e00410201c2c1c1b41d200c00700059901452000e00801211905480d8010003030103401074401c4900c02c0c3c640c107a00da1140b81420300301000300040e8844074080c18101003181d6210b40c020203407900c40744e100b040c50000d900c121000c200b507211080a90440101c80100141050403040c4403101110042e01414405070001071681b620000d840b80140510380008200c8040030751044403041d460003070041200016a1a001c0d49a0b40b00702d4809a5411940e60200d5513400e150003250390010245c01c0e01780ca04402d5540c195607410b008944450207200c0c4a003128500c3e9a41d118060800d8041e002454480403169025442c2080780f201d280070901c9658041c084454200c041da10b03045030325080240c0c031a917404c00100d900340200800a0300c000001d03000050074140b5a0f00403d119401681001403180d101c10040c0c0c00c1c0d60300d840c89407600f00d4080000403040c030f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 732291744 1250 732290494 732290497
    0x901061503090c090212071d0310091b06110f010b0904060903030b10020a05010e0f0a020d06020c06130204140702100f0b0a0e3312010209040515030f03041a 69
    0x20303c40c082c1d0b0300d680d9440d600480e0032600007103042020080c1010a00c178030307150058032910a40e0340c2d00003a0314140700c41a0219460b00c180c3e03480c49049039114582c440401c4040b00440740c05488105419611940d00c00d401007030410007904800d201d01458000140c00c036810f019400207400c1c040c209a0789501d4030b66640008180088003a010542d490554041c00e03520710403520607100c242e80c002c1c1580101030400900f1a20400040c0101c0c0c1d111044404500c80040380c0d240da0340780c04175201030107c2880d080c680041d208a03010f14140c2d029110402035054034841300c1d1401c10703000342e60800400d2400c00003080d21303110a841e00b0340962b220340d01880e98003103036412205030b10080342e90200d6160010b001003104030310709400a200d100048420000320484003080b07110702c400d810344c5417041c84500002200903c00842c0c40e007802140b4200f9209031b4154250105c6074a000054070803c480e18140031804210005c4410040c840e000d0308002c3c0b64143c40010949098642e01410030300086440414800103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 732292994 1250 732291744 732291761
    0x1a13031d040227030c0a08060c0c0a080d09110d031d0f0904061d060c04030209130b0906040c09060612020a0c1e05010b06040b030f07090b0a020f01050901061503 71
    0x442c1e02000f4500d1064001410180c04901080d00700380d085503d14200b500380403011801078001d0340f14040c01c101c81c400c001012500118050318441d07454400300011410f1105088000c0c0c00d00c00001400103111050380c1c002060180142008502405820704014240100742c102034002884c18059070f222170003c5030441072200009041c40740e540c46441c0416002c81d001c450540e5095660340d00820015925501694842c000310080c20040c40d000c42079024602031404040e0203000c0b500002070814100c0d042503500759401851004052a11909090790ba000490f8202da1107001440000341c6050360303001b00340580300c05448050319000542d1000340203401012507030382005035050030100441e844010b582d62224440940024607003071414030900756011000b440c3d000350740400040020842a80c240e0f500b083ca0b00662a10320b4032444000c403000049034001c0400300c04000303140c400058000035070121040b081d0780280300307585c0c603841d03900e080300c00d90300c50101201c00341c803945207005100e03a010615 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 732294244 1250 732292994 732292999
    0x403180503011112090d020703110f0612070f2604170408030703090b0711010513051e0a0e09030304030513151d04050103031b080906071a13031d 64
    0x11280d40c9400090940d081e40c2c01c1c0301c402d1080003031115241d03e03d07065883ea018060340d005000b841e0589200941d0342e0700300d210280400b1143c42d501c0030342d5900d8040805003600002c000350349812402e449240000703000e664031004100c29078484604540a0404103410000404116141625045d940301c04130a004008682010041c2542100044800c01800140003800011601c83c0d00340d20b000ba21401a0390005504c0203010300c030401c000741e108210344540900a03c3e21070349442102c0d03d60403a040700c64200b41d0780942c0003c8040140340c900e0700c80c0445558101e03036103580540c2d600600900b669042d651b84040e41c00c07c000060109000300e0040030340607481c21451050b04d03580d420482d12404030801c0b4000280c204030300000240d031076071007070722a09204490401c25545569009010140702c40c04c820304142e0b503440103000344210300c070a8440c3d400300a4910b543e0788280e4500340c1d52596038032807803259501c0c040f00405e0a0f86002c1c41c8050316140c2c55102e00c02e03100b19164558020381082d105607039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 732295494 1250 732294244 732294287
    0xc030f09181b220f06110609190516030516050402090d120c1e0b070302090a06030b0406180e070609320d062a0507120e06030f040201080601170403 65
    0x1503d9803500c1282c40101901081402034606186008111000074042d11040c2d41c0040103000c3d5090303011604103c2c01c101ca03024003141002c0c916200c0d0900c1410300154103030003614500007050100200c1c50942e1022041d0f10745100d00d0b10f800c03c2104900402030340b203400880400140000411007800d44d90078415074186a091400c0383e42d5114084e01c440c0d1003000801ccc00c0d04c400c0d44200300039002c0950700004103050641c01c2140100c08100c02681520032181050b450f50803142c110b8440c5c0e03000101030850440c1c5a405070f08044502805040d0071665143c90f4460280c0001e0083d00c0b5183d00c01c00d4444601e1a004140d071307528064030070b0510380d100485118501c08a000c0080d0342e48400c03a81c070786109a02c049901000c08842c0c40a400c0c007944420110400c9011051150354030000b00d950042e4005503000e40030064980413140145920100e60704210004188990b000031142d02902c101d200340e1390b4400540d01c241c011903042d4030aa09841041a410000c2400240540907000000e004020001c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 732296744 1250 732295494 732295537
    0x60607050c1905191401091d06150d0506030d02010509060420100e0405010905010501271a0c011a1e040906111206060c070b0a03020c030f09181b 64
    0x11207094000040d09850500c09400b00440303084800c141c08101710074207250080516150b103002c54120106030b904c040010040004600d99207410a940d00c8841c0404040d454007441000107004000c141c402c40e209109241000e030f50b00d41b0500407944030310070500242c01c1c6625180c1d0780d200308400340c0301011030403440c803100c0d02840c0c1c0358225008500001c17607462551044421080c40222501a00b0244001d0300b810010300c4182d80104403100064503405144044a0405486440a61464000911040b800c220303070b1880c0e0710079202074010103401100810a0000802c034a48002c418059003c2d08404007110384148503030407100f81d0400e08406080400c260320703541e58400032100c02c42c0c4a40d0f02204082045060400302410340380d030100c0e055452510340800555019581c0506202d520411100000c841000703500c20340503901d048048404883e101e4000d00d0202505400c241d00c600c0c0200d11032480403020f03500c9810703958025802503140340008600701c65542e250368401c1c1d829400b524844c0800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 732297994 1250 732296744 732296749
    0x10061508090a05160302010e0f010f11071a13060201051308071506091505091939030b190e0601140f03010503010b100203090103051824060607050c1905 67
    0x213890003243da910f414070800381103100150080f21400a098002d140c1e054050040341d8008454903455000760500344500c090b403170b003081d00c0d04080f500021b55610301c404c0e9034002d80d41002c015001c602403c0c2071742c008041d1949002c03030032507408544c010401480f0044003000300e4118401098813601030000700544091030280d000684203140d0201e2001503640340c2ea45c40da080c00884400280c001261080e4490a144007105451525036040440f9a0741c0c403019500d131240d01458003906842d1948142d218101c0c0d15403000c0a442c500024140443d0410340048043e140c1a20307a11441c032004104010b081d8245110b800204800404c0c0c00e05106400e5451110710b1641ca01600840c50610030456480d03040070700745400d5401c0343d10344602030f192605811024a030044182c1d10150401e280c00500b03580c84200c005103410f0154032070a43c50040945080140d10080024254401e0030b1080e400541c131a2802d003e028402d5040140568021042810f210300e0200c1032091280880004140b07802d0701d8900 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 732299244 1250 732297994 732298003
    0x1e1207080f120a0e0c0105120c04080a030c021e0607030c1106070c050406082e06150302070302070608190e0f12030405250501050904090c0602010b0310061508090a05 73
    0x10b0b0341c1142e40c506002c02100206502a83c0000c80c440c601404030000c6420000e02680500705482c111000b41304002082d0841c0402510010030640c402c41c1c0b00740405080c054540c840d840c4c0168010752440380c40c1842c0500401c1036120185028210710701d01001c41d20102d41d54501c516085a00e0404142a01510384d03444c0050f004d503500a80039000760724902010001110f83c0c41d4483c4065810200040a13002941281400641190002c640b400710b00d4a0040009010a42200200d0140310701c150440307a5166019164440c80f0381c00304c03541c035510380c2c60a42c3e00c1d0754103c0e14030740b1000890f51808050202030b00700302c162492500071140060035218145d800e101340c114030484040c402208000c1801b034100a409117030783d02ca6000f0665989180c503c05810802406100e05002c400079072140c03240c44540c4003c5400e46c02011034106140c494600034060041545094864402c20b4000c02c02e4000b02c1c0f203114111011244c42c40582d011110003554040f100504240140c011103034180c003c00d40a11 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 732300494 1250 732299244 732299257
    0xf04060503040c05040e032709070507060603080a11010513120f02160e040b010e07020304091a0a03050102041503020c07090509070f09050708090313032a0b0702031e1207080f 77
    0x595203e00c2e8000030a0b400023000e004110903822008100328260b2120b00810f604100300b0320f0807596942c080d06101c006030856038001803d20000103181c91701c00e94888000001d000c110301c002d01090711802c442e2100100c6010001d0041c5150786070b00c04e1501e000d07807008100042c40d40144c0c3c84404551001c0c6400b04220751203128258100c008020802c800c00c1449800340c02d481c480e0201030301700201d0095582c0128010b4aa80a640e41ea004402e810404443ca20700d0400500e41d092043e00c1e468541e000c3e4016115072a4441003000e4602c0300c5c0b0307020b4004d4a0301041c140d4028590546005c8041000d00300103455004c0b10700800c0720201d42010804101030107884a00c3e808540c1d41450305000300319004c02894078032550010300c8100005060110480126a04030689402802e646209401c24102d482c0c02d003107501d6006400001c40e46404e2000d0718140c0c0c000c13403d8134001c0d02c0035075810b116034001c04604d85458015810340108926004007500215000700d81507030410080380c4c44c841b50f50340000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 732301744 1250 732300494 732300521
    0xb0a090203010b1203030a020d0615030b100c1109101d0702070b030c1209010e15010305061018020f19030506030606060a0e010e0411130e010b0f04060503040c0504 72
    0x4204420540c00c0074000c1940420081e920314072507034000e0146030740f80d010141601402e19000150088280c203141c0190014100c3c03d01c140048201c1c0311405002000d50302c5450340a00009a5007100803802020841803160b000030907020f000317101c3c0081120010307004001e2405413000380d4000c0348083c034841c501c0008030303419840d1403540d050001000e881d02c3d815500a11007624100300304a60080c1c0c4909a801c1d07010951a81c910079280d50785040e0160500c07201002891080c244104880d154503240c26040328010004d442c2980c64044071001d051800d07008281c0181c400861020009031180d000704a00c3c6080e0510701d040c500001118011485542c9031200083d80f1002441520726040c00425005201102e845140807007031070700a041c455240c05094140803504260f2071207901c03241c0199090400c01e02c4800d5841e4400740ca0604000000d002c0c0c0c503a60740b0341100102d1084a414102d418150b8120039050406151000c02c69190780014002c0f624002070050002e41a22a80244008000c08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 732302994 1250 732301744 732301751
    0x70b0d0e120d1a0f0409020f03030c030a0915170903160b04150506010f03110d060905070906051206062109030a1d0a030f2303040609080a05070915030b0a 68
    0x1c40c524001500c02005100500030620280303803070140d8540c020b140721550155800b05200c0e1b5540000b514000c8450301c0d00ba0180800121114442404002011801f0850b01c804403581d03106c1c5010300b0300c004000840c8000c146101d018407a00d4110740c014682c0070400c242100d2a0040a000d400c400054001c021500c40d5803075014841000304010341c0380c846d0715455208000030300d4910002407078100654100418540d403010b2803030b500b1403a04110364803a03090680901809684807001380081c0021540d91002960225000c00c2081c49030f02100c0c00c04103480030407019034949200304003030b692100309100390001e001d2000c0e12007085030380c803028481c250b40c00c0034540725a280070000e09405100040078a2240203441e8980a40d51a1032064040c1c80c0c0084405400401525007c02c45590080c1080c11080008801d4034407100000010000c3d182c1c02d607100400c1503983e56000b44d503a1102a4001c0540d006107500348075120700c0b039000c5406000d2506000b00340715131382e844540083c90140d07034042c2c6941c1c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 732304244 1250 732302994 732303007
    0xb0301062d05070c060315090506061209060a0e06070203120c16200d051b010507050a0c0f090c02030307031a0a09090b1609061101060509010e060103060e0702070b0d0e12 75
    0x4c403408910041485003001d00403903150f40702a9040340b0301c501500c48a20b07a50000314406440d440c0c1664486d421a00810801d42041e2008944d40c110494480b203802d0704069040f050310001080d4a4014180c6070001d5013800c42c5840c0c094100a4000c00e00e03141644148a0702d01007603096030300c40f11014003030509114442c401213204408100a0862240900240742100c00000d8000544001c9802c100300000041e40158004942910079108040e0852042030844002d100c080c3c10f8000441361000c41c044040d60360741f22224180d8034000d8010000d81c00c00d2000541440c000d8110301c41c02c09031074000c030301c2580c0801d0002d40d241605402608550341ea40e8a074004200f4011040703070b0011411100b0141c00780704c07003030010442c0060340584410010444400c80600409410402c05031000403c90308032503031903240c4003081007001c880b1180001e041076000212100c98480c1135010380116806003c2990401010243e903600c00001c0049035944e907905c0402001e0300344460b80512007003c084a6483c075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 732305494 1250 732304244 732304253
    0xa030207030306050a120602031b07080a03060824100510021e2e0603080706090201030b0f280b03010803210f0f18120c0f070b0301062d0507 62
    0x1c43c81d40040b401015010014003001103121300c6039844070f90003080907030790780c2d1030707024111800303030340181100000c00c0110f20702c0c0400c02c010010b080381d000302da03504001b000e0366031000c2581e5001c9200c0d40803403441c001100b41d0020108001c03082d0301040d0b0009140d5461b6072a000f16480140314010703c00180c0015082001440380d003915200341b440603070014a90b0240d40b03008011120012112004140280d503c480314180560300701c1c1c0c0c0159040b4241c00c3c0c8420982c2820005401c0402c0101c0c002480c1c101403603030f1803034424490707241070304007030440e071601318101800c05213039864800c6e200c24021601400044660b001e07802540a8040b000185440c3c40c0c2025804448517000000024007002c1d00c0104120501c010004035071080b03031245e2046090f15003621112510600c03103951603160081401c04203646a0580c000e10a000401317040303820411184440d5a1105124002c0c01c0d00248100010080c0034821802200e150041005400c0c2e0903e0024092181d0301d065500d841c081030021a0354810700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 732306744 1250 732305494 732305501
    0x60e070602070f140a03060606080402040b0d0b0406020a030b092a03041a040c03060c0f090f03030203030f07030209030610091a10120e070b071e021c020f060a0302070303 75
    0xc0c40c0e00d000400009080115010b4201102e010304000000301056540080e40c1e000498801507400c000f08016890b00d400005141c40412602a8000d40c00c10003080300314100b0007035180c60079400400500703198880d640e885019500542e80c903020540c4411918442d55203181c0494019041d54800000c1c4079070511141070703820141844030803d50f00c1801008089040302b001c5640609514110f003190307030394601e07180390607012a0300003a100d0f6142030404008550010944207a804c1c5d81d07101e460159684101d124800c540038000100160002d1000c1003614205264a030303000003050801604164105011a01d405002c550143c100380c295a410000960148503001d01030080c2d04007a000c03001d80101080034002e03800ea1600130880150500f06181c002a40119801031080f810749030026601c02802100f40c00442094941042d511400340c0388024190800107a0744c3c6c040e0980c0701c00b881c51020107014214580050347c002d0100032040342c10342d48040c01400701d806c4c0d07524011f80356070705810018200e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 732307994 1250 732306744 732306749
    0x203160f080f0a0305031506071a1b0414010302210c03010e060303040509040f02281e030209041514010b070b130302120a03020c100e0d050a05120c07020d060e07 71
    0x3190070114000001c00c0d401000c9035441f00e401c1079042c2c100050080810020300c542003025100c1f12201101140b2441c204542c2805030b4011000b82e0891070300f0000310400c0b44154490490800680100d81c2c030300394002e402030000540002100c7d0042d004520310120103041c02c9400d01624440040140010f0000901b01c680043c0e05900441c01c1c541401c01052091002404c040c22654889852034215920000d10382045080b0b40c0f001504440003460301007180c074003402500320740387d02148103c0c1001c119070088011290002c02c075100588035922410f0341e110304901c40503205500d98001c49030003d0007403000c074003c0c184040c00030340e00c0c2482e0911001003003021342207081d0800c0e80142c0a02081c6d00103050441d01580035585640c1d03c210490980003440f940072102564010103912b2041d01450744c3c80380d00c40e045079409681da1038605031001c840900c0340c0291600810801c4c030203040d01c03040d065205a4043c5240305110324013440ca03000680791902490049416a4a503251800040000d0020000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 732309244 1250 732307994 732308023
    0x20604080f190b0402090604023112050d110a0b0103050703211e0306030203060405100e030a050f160b040b0a0c0509031002030702070509042607120c0203160f08 71
    0x754024030356280c043c0c0038000380001e44902c0040d404543d0540e10307039049644070f00d4621510711048903146503071511740c0303454028400c503245850f40c0007420520080307414540a500c03801030200ca0a109006483c59100c0500355074032882405410400207001041640c080c40c010b000401ca1286145020804001c806818099103841c4070414035606820101c3c0034802c3d0000d424010039a07000c0d07071080b0006c0989920296061281c03505010500102090400c07100100c2c2401384008000b1f40c044a03664406e800705000080c0c81000340700401881e40000d04040890f118032002c0c181182d0319070000d03141c400e403400d03506011800144000f14040784120312900909c0d00381141007165400010713440d00101c0500c1300c4015000000559032610a000100143c000103086480d141840d040000300d440c005407118018485425185404600000981707031129400042c225189072000c50485400c1d03c01082260103220340c011054000340301c221481c1c064081468803800c110302e0f1000840c070346580849545c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 732310494 1250 732309244 732309283
    0x905060135013603030504080d09062703141606020d0e0706021b15070501020712090e06060409090c0b04170709020906090603090a080315100207061e030207020604080f 74
    0x4081c1e003003050f0300c41c034000d03014240000c2e543c0e1a402c01060a02c01c0400c00e41142c0d140070502c2c0200403841d400700c16a00d00e480b001880c040312400140d85445400d140190104203d04040856103158100500b0881007005807401c40075031175521041660000d141c01880d203500d501c00c1125014003009000014103c1d480145010062072620702d00d401441e010a9008020141c1d1a1320112181011245801d07408030085603640c02c60f01345800300101c04228200007843c0074400064962450701003a0150034020407403840c1502d0312448200506030740b0030403141034400c1103000a8000540c009080106450b9005a41d00300406e4070586c00d2003401c0d00301007003182c13040c08441040c1d19400c0c1580c074406410303102c2035900c0d00d848038202e15061001c03070b000300300e101c0000401849803602036003090501802d407800100c034015003003360785a07000d60280900088583c500341e1150a50001c54440a24280c103005107000c41d103401080040d481900400d51071b030f112042c44062040d040284241c020712603500300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 732311744 1250 732310494 732310571
    0x2090403030e100608241506120109020307090f05090117160e0702070b0c0c10050d0504030302090f030303070f03050604090213061a070305070206092d030c0103090506013501 77
    0xc81802801628115801c01f00f82c2c2000015100c20701110b46016100c2000c03c2c066a40c3c5940c180658800c40345140001d10030340c000110011940c00300320558100503e0384400d41c8c02c2010185d464209038002c00c03e14440c1c42c02940300d03000d1056079000030700318a940c5000316140c8000060301d0040c3c00e6102c9500d041041000c5855004081501486e521084902400704000180225428003642101c005c1c098030b0142448101500369000300015078090314510054000102095203900046848002060500c2e41005806210383d21065006a00500001c2c07010865004500d06154034600c0e01c006540e10038040c420f14040c2880311030764149101000c1e292032581d030b9006005000b0350034000c0c02141c0214200209540c2d213104845110500005603144846041300d07003890300f0f16070051a000340188850224254400d000b0711130343c241c0140082010364603081c1200300d03101f0350ba40f542c924101c906401503122000c890290441c1c1c0303150000070403111030b1002031104101e0405a6031441480001c2d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 732312994 1250 732311744 732311803
    0x70509010903120306080706020a050d08010303201903030207110f060703112811010f050f130b0307080a0b0f0901090b240a2a02090403030e100608 65
    0x30704082e01c1e40011030f0320004090b00010f5000e0840c540120315140603507000840c5c1603600051040b02c1030701034000c40d442201402000d854541083c000a0300007503013402c4540c80102c203c0c1441a92030842004c440da4103410a100701c680090296084000940006d488028410141c2c1c080c4441001111601ca1002004000400c03511071407038020203100b51030300b811030701d0b405c1070040d4001e02c00c80003000d90b42145800380007520703054111400c0711a00c4101c08030182952103010b07403d2055903d501d0301031400d00301031410b140c66001080c4c16040110179200100301c03c841080070394040e0220340c40d01810f50074a0030750002510381981c01240100201c0e400413003241d49a0400c07034110340030300600054004100003c13800007541814060001101d019a040080d1714820043c2070580070360b9180b14500e0030740d44016107043c4100d019820b84000000d81c4001500e8080c4015800c43e01c2410001914100d074020b40f410502014041d0741100d40d659410040100240408110003401c03001c07090526004099 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 732314244 1250 732312994 732313007
    0x307032009060f032509060b04091401060210110f0d060e010b0304050a030507030c0203060115110106050307030b06130509030301031104140f1f03051c09030b06090606160c050907050901 82
    0x10507254030204602a45e00c08a154450307107001d0406254103000341515005c958540d6403051240321101071a052011140d140c00c41040c0c3e058800030380c081d1221060406c20034002d07240a060031207200350100652515a00410000c00101c041c420010500034608000075000150503444481100000c01c1000300080d004541c600c026a8075052144e1a100d8a04045801c9007075210300070f40600c00d040000c2005002d15601041c7c100440c4c0c0d070082c1a0228890480c05d880e901d00c04c441d0544c0c0f04072070a200050014502e075500980103840b503402103a001c03040c882610800da80d80051900300000500c1130001d0309013030300011302003524140005c42d0002c011807c4030400520740d80550103401d000c6110919001443c2c40120541c8541c01e41c5a9100e080654440035560381920100749649003006105000d03601040c00c6a070000f01c64181c1d80e841c10103101a901008040b41e40c0004100241c08642c0100740801c0e030350b10f0007051075407412403c242c10f1014031180940030406200080c0480a038aa0f8440d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 732315494 1250 732314244 732314263
    0xf070f2904030314092d0a060e040f0e0d03091707110405040606050d0b0a051b040603020307120e0d0f03110405010c0f06060806090c0d0c05040b0307032009060f03 72
    0x5010920507461014110b19030080c040c900f584110542d42403c1740c0c101c0000e81208101040c444501b070100700348200520301032039115403070205104500449036480c2c2036110443c0008140c0010134260b441c1c01605003031205082001c004240c1d144080380034050203e034403100d41d0840c189030501c3c4c8440c545440e4940c03030310580901d02c11903c4d000014104007843c0c0040c40244005000d2080c5500c4510746044803036000c86134030010516003c005a06200401c01d4035002800110f0040d107003508242c0210040d40c00203145e42c0c14840031190300300c1c19011520550404020010181448ac040442d00a000380d03082880002090309000480c4054900541154120340302424a44540212482c141c40442010500a000c031850000d00040d4401c0c0842d43d544a00814000e480000500030304005c1107280d06200130f00440caa4140502c0b0f50706059009080782e4200400304e99104c0d82d00d0b43e440f114045880355080103401c2c0ca00d40510241043d802591300482c048480000740714072580440c0d07950041c0b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 732316744 1250 732315494 732315497
    0xd17040206070c0506040b07060e0c010509010507050a0803191a010914031002030a23161b06050c09040608030f030406020307110714130b0d02010807020f070f29040303 74
    0x5141e0042020803c10000104030140105449503a18522050140c010307004c1a01e0380750404d00c1043e00307402c000c03031005a50391301612428200f43d41d0100440f119003206004560300d104100749600401e0380d020240d40301e485441c59045140c004c04403247d003030b518007100d4a800c1c0243d0200745e210036a0007649c40800e880034113214018500100340000d181100741e42140700b0480c800024040d401555410203c242010620b0a82d280d4440c01030605150001316014403081000601028217140300309089406c882c0c101010f01d00c0e44685031a60401c540043e9050094408005503006c4242042d014060003008208080c41c140420351000b00111702c401032008250760350020015800a018840100c020400300d011904e04c59101c1c0c011362420102a240c1e140b1400c82c40e11180b4100e0882d025000305a40b0141454000030300030390065031549405805141580150800300341c080703804101090040c046000c25106191a180800e45201d140084c8417240d800c9101c050460658000116421654107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 732317994 1250 732316744 732316747
    0x2120c092e080106061112070b100e070305060f0f03120d2306031b060702220c21020304051f0212010806151906080c1201080703050d17040206 63
    0x2244644000c05005514020760004148404540401c05602202c02d450030354640319400b090121070581e458a46c030300c03400c2c0c54807405c0000100243c56655420f8001080d40c0da030803440d940702c0b2841042c10f2021140b1400280d950400c020151400c20140c2d50020300c01d0f54105030482510340886d85032180800303507203407410000801001101d5a035121003c40c008a42941c2102d03000002684910141550180d11134401c41c00107d190084102880e201d44400071303c90740c03070801a41e081c00099034a440c607401d09040034104004100800e8050307108100a41e0351f40407107003010030101140103501d4050b0a151148140100f05c006040095101c1e02e0320419445032007070901008100c0c003e44030784e20800c0b0700041c0ca44000200e4403000980c05006440b07400c2d02c0c0c0c4190820000b030104000b1689144036a1444545041020500520b5860341107190300ea02a031070030041c0e24481020307040130703031083d03036640c5c000c5d42c0c00c006208080c810300c08401d00310b26002d0249507808070f2100c890000a0701c00791083c0b10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 732319244 1250 732317994 732318031
    0x91a0103090218011e050303090105090907031104090603020a0803090a06110a0204020f03070e0d0b0106030c090819020306100e27010f06080d050903031b0a0609080702120c09 77
    0x48100c010094241c0566907040f0380e41e100c03840240c41c88034101c080c0c44075480950b804038003481e01209841001c48184d58103800e01000e10308010100c80080c003a10103040d0f541d41c1c142c080c3d017940c83c01080500220440032484500d1441800388c540c000d5030107100290410720215035266200ca41c041c0890b001361504074a2000840c07401c07420840c520354000d521510010f58104442940c2010b14459400f94071400c4e10380310840184804850109002403600300150018006a8003039842940d400d0918504011820b8840510a10b4201e28104400750040b00440d00011403404201c05903100500d000e0b41e5010a10b4180301a10f4440041d000c0500d05042007003503400840421a110400030100c0c0c000d0014101015182004100750f000703101c4940940c0700c444903224080c07402c4510064002c0c00451070b021401103819500d08420142200c41c3c0218000c00d004909580a00d400890041e541c040d0360742900d00c104510408062261602c030b40000b403410585655038002d07240c0c4a664451a01c00000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 732320494 1250 732319244 732319249
    0x6190507020f0307030903060614030a061a030f070e071b110135061e1309050f0318040603020d03030b0111190b090303101205280b01091a01030902 65
    0x100d0b40c540030300240b001191140c14160300c50300c0303841100d0040c0c5003005050385a003882c0100c0380e006580c1d40c0e059403004041800103a4681c0c028003444070f210440d4803010171441d0000c0d003001c60800c034040c2c2c80c1d40032445c02d00148145085150b0481c003a410882c000d0458012140034150000401074045031f441d41c681c0410764021000d520204100c060810502d105040300c58481c103011402c00c0b13405040304030002c2c50b9801c20715101c02081c2d2a0b18204058480b24404211030f9500c20540f40706c0803520703400210002070040020b1a104d4210b00080c58075602c00500c40c42c0030481d0413403428440c505000d4100f0268840c603150238445078041c0340104801e4282e0005a50f400303070082402913248902c1400e8541031440d030b0700540b140c5115800e00340e6180c40385109259280001d4468009190401d00f0801a000c04001d0a0303a03001d02c02c40130744410040f15048816031f0f541c1d0301420790f080604a0301c0d0108001d500004203000d004004810482101d041d09500b1001c85040480303070605035121028019907 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 732321744 1250 732320494 732320503
    0x503031936080309031b1204031b170d12060e0402040b181302040b060304030f35180105240d0803041109070f0e04020a03021e0c0f0619050702 63
    0x2580c20480481d524100180d01d15500e1b80409844e9800103168030b000c1c0303912030000c10411450844030301708074101811070f159802461440f00345c1d1122400c0050001920441e828051714a2208e114060020000809030162003918519590441d00d460154140a09000041c00d9034100b501a50006983c07104840030888400400c0ca0b61b030066412403080181080c0c28075000107440d4800d035420f0011001d07200078081e15000c1510003c2c0880c01c01c040940c02f80d032082102440c0c801c44101288014003101203030300207030801c140c405140c840c0e420003040007125103200301650300d80284000300501c0c500101e15040c0540c82d0715412044c80d04405034039955540e1040014580b94010359407030f5403401c184c40c4c5211031410318958517000d200b01c640090601030207103580080100141d1240c0e403900c1440b00811000b0342c000b1495000f0f241e82801620303000c1c1c515100e03040842c801103100944d030303045841d01da82c505500600002c0c1d05074403035001c004d20412480840c600071400f0b114045a181c840840990a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 732322994 1250 732321744 732321851
    0xf06010605250507180b24070f0b010302010f021f050c0417060402090108070e060f042405011e0504090908090d0c0504060906140906011b05030319 65
    0x10b0724040803441003404004141d0700d048076144071541c0802e0029202c030006407030030000c981e43d2085085000490019003803602d030254900c201400d40c07800810356990b840b0b0752541d041c244c1d90703c80000010710031560088400d01700d01d03031103000034000106808218800d080d01500210116511070011074080c1c060b8400b590043c1510303059184125000080607950740780300311002c2e40308041c2000001401c0101096100c01d50360144683d045590343d0700148450b8030354054500390004d0f0344181c10000590b80d00060b1281d00480321901c4400c0c1d08d0300000509a03502c0070302004107016030920151400360002c04132411122044e002154201c814106048203024461500343c102c0e10300030402d801c020300717440407100361001160100712813a101d0003004112101030051268408a003030b081c45003490f02d4490250302c901d052502d88098941c01403a038170b1502c5007203005c4840e603002005010719401c40281c2c048114842d14010402040d40c4540088200d8070700c600a09110b000d8a881044035261040d06c0e0803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 732324244 1250 732322994 732323047
    0x50f0904020d031e02010b0f0a0302092d010b0705010c0203160224120a140402090114040f02040b1206030604050706180806070504030302150c040b0f04090f1d0f06010605 75
    0x5946184113000e4084e211400140c3d1180d60014003060b800d280041440e011350740c01800c80c0f00c440c0d03600f00c440008000b03c0d9480703580446c00080d50b40e5007c0880000f49019141c0c186185488095500d4071070309507030310005d06106541090110949a2007603840881d00280c04a440480005180d040e281c1010444c0444c1caa5000000401d460503000f644405030080081c0038041000a510743c14101030600150b400030342c4075040303100411406d24203aa4108000c0401400012103440c02904401260b0142d401441c0d030750400314032035a031340307054034541a4012800c2c2d0140c251850b00c1d50328681c58074442d0007802c1c04e1200f4074844000c03510494452802408000003100c00f139051400b8050700a82061004900602c00c080240b02c000300c801e903603280248003d0001038149810410000f0041d00009504885c0703c6041c04001104840c600a1800d68000c00340c0c0040e600720895200784880f10300d441800c04580c8a00da02e200c2c205400584036044400e03503c5e105807500000c844072036003c1c481c04900352 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 732325494 1250 732324244 732324287
    0x906091908011b08090d05180406080105061302040e0403052a03040510020f120c010b040510051906021002070218040506160906020312041112010c020106050f0904020d03 75
    0x58141c505601031075002c00980302003d030a090b880d80860b02c65104944010054000c8103101c100035000e080900740c140c110104441140002030702080403a10554415140c681d10354040c01040c1c2000100100c5001c0840320645c600340c04d01c00b400c000c400e00684020104200010040f600040000c08070500e46084110440c480b40d0620165650741c005020b11482810072a1034064130742e00000f41030448001010207083d2104160211702002d0b080f100f071a1b0303020354031046007190741e64503407181500c2645510103541c001e600b00b500b840f41c40a100c07034200c98454100c007814801076400081003d6a501c15080142e0788403220f00c0801c800072081000390074031400c0242400200440440c41e0f5214032081a01c98a01029403401200c03022098031404025070001c20010200c03c0c0b0300031701107601a00400344a2104801c0d1008100c14402640704410b66035906c01e140411a68280181002840b04880c920a20031107000043c00c1c2030070240c00248905c58407040001018060450040b002c242d910051 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 732326744 1250 732325494 732325499
    0x60b0d11010201050717070f091511010b0d2006090a12120201200c07050904030c0605060109030b191409160b04030309230a060c0201080601090b09060919 68
    0xc1034000d035500e5541c055403d240c00550550310440f002c00001258901c550401c2d110207000fa030b585000e6108400070003280440204284907400c4007113160440b2a5580c3c030900030000740340c5086403440c4e21010300c41c0007841c4581d400304003c45820b02018020311100c00840c441c000c0051401d2140c051403e800401c40da80018496007032107600540f141c02062445400407448000300c0c01c03500700010100c1c1800d40700500400e020a044040e04055120400f1207151585030400940c802108440c101c0c009054006450100620f81c0070b4642c000d4002c1c20201c010310b04507a2880302820300100482c00403514585100240000c0d500b201c4074400204000460a040201146843d114554072200304001c08000c000b40c02100342d400c840480382c1680d115000345040c8100e019181401e840b841c46130180070003c10441d50746015065009000f04d850f1100074013124030014000400040c000360500c07140e000b00b00140514101111402c1c07500b1a00301d5a18001900001c03504580301185076030360310052002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 732327994 1250 732326744 732326753
    0x203030609090129090603010b150d090c080c1002010606021f020d0c0e121f090201020a050f0105010f050405090705040e150a05010f0e04080909060a03050a030e01120b0307050607060b0d 82
    0x130300f03003d802a0360030407580d035807502803500341c6208140203500141c0185043c0f515480040160810402404006c5009125500e510600c106103400410103600302d5500700d0705a1800d9a402e10403204e040c0020b100c40c4c0e02d460307006034031910441c0e454a50700910340344021225840f43d0488000c3c0d10080c404005541154500503c10065404000d008028080c8090a40c0000081c921049640529114002500c0303500308005085101d00403030641c03040c0024040024428090141e12025202c0000b90b01d40c0b41c52510700c41084141d00c070f50301441c900707001c0c04040e140103d00901a61802c4d5030109004028800d018581596101240019490b080038000010075542050b8102d920031860079582c00e44032031a02c031100e182550018074908080091202c81d06100e8480c43c1c0c001001040414001d5894950381c0c100405400c3c2140041c001d000b10007015a0014520415020900300c100074030030103072010a0340c403c500e004092041c0000314051040142940288554a0002d4000b09844145107413 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 732329244 1250 732327994 732328061
    0x80417060405101404020f061b01050a14090a03140405040c020a020405060411040330022b050406110a02030d050301030c06031401170f06160810030302030306090901 73
    0x50072142c2c0d000f0000c1554101c540c03400f40c002000c0c0c08404c813818940740c1e41d00300480003000400e0709401c1001030044510800c0300c0c541d80c40c8001700c00d600200e10361414051510448002c864942c0b0408a00d5050100b04000012a007540c00e601d42850000c0c0d0303002009290641c0120f6002c690700c14100b46200390b4180d40460120a118420356080c00151200303420481a55074840c084100047c041c081007000c19200090a103240c0c0c0c0680e298043c08100c1050302003440d0142c034001016a1004444411079294a542c516030460301e05283c03110030902190090052040b0b10a940c05c1100441c2e03140c0004009000014078035a00030b04031041c04c080200050320a401c00d02c002d50f5042d10184001404500034010524a090f1440c06107040307a00706000c0e02419030340c0c07820f41416445200180380d00040104601070041e04030702c82c8c0207101080f42000a1182c00c00a00040800081c0403040000980020540b80c0158045440e404e4550f5008002c82c0100f000b10700d10040e108086076400f207000304c0e454 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 732330494 1250 732329244 732329251
    0x50d0218090c13021204020d170a0c02030c04050603060703022104060608120304030e091e01230d1e080f0d020301090c1107090b040b0910052d06030408041706 70
    0xe0b050f01c000745403508508124003541d5540525543c403100010010300e0300030b5250b101e840c412000743d80d2004000080200d01e401c841114030100d407064a140d0258981005a4038000f2000c80e42881940b6000003c02d44805001d42200185070300803810315110711800612041040001c05449044d00c0d182c284a4003610452181880c240038505c01050030000304021207200b150036465134201c40c00c010051002c00e0100600c00c2c021094800302c102038a540555045000300700d4005100d5860702e0a5201e074504d1a0350010852040340301c12078090002c0c81c1c558038140c0c4004152022449007845081c030034001c0c410400e9116000000107201d0740541c5041e8065030581e00c1d4040f08200c0c40d407c1d08415140402c01940c6180c81b58098141045400100d401c2054142c502034000700c0d0300385c0720a001c104450b1060b0381c140b90072410350006001505081c0004080141041130800464903a201e00c0c2182400502c0c842c1e0207044004001401d2100460072500100040040100c0451001c07240503203456042e03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 732331744 1250 732330494 732330499
    0x2d06080114060a080a0c0312140d090209010602010b0901090203060f13020c1606081b09030f03031b030c0706090f0b01090507140a120e120f04030b010807030b01050d0218090c 77
    0x5443c080361042001551640050344001d80750b0b202402c42e298440342180302d904004c00c01c0300350b4105881c18a40c800140480c041042c00c0424004103e204010074424140c000030210381c90300301e81c002030740d0300c1c983c0007411a0318100c07005980e03407249404541d0a0386000b40307154000301d0010030801c1c0f0b014964009c000e21032440042d100390400b444035880c9064918072551000800c000b0204828480300e80d81000c0d06840e230304a4600c5c002d6042c1c040380c00c10070095000c03001d9800103c10440309400c2c26600a1020300a408081d03c0e514121440350114002d940307002e8085651262104d08100000c01c40145094125080c20525a582d500c0b107005404220354060024003000c100305500c0d030031042902c40080e0b03180c0b079105070503100302032900c0207140c680c0110481d48500d0407080f0b40c00c1c0b200700051106c2d4945600041d07440f415800c10684108040e03000540300c2d80030f41300401c04035442070b0095041d1038089840341400f0106000003201174603001c0031080c203c03041105108180300c001842141c801010b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 732332994 1250 732331744 732331759
    0x903060414011811060d061e061403100312050706060f0801180c0939181401120e0d1e09030b0408090a03120801182d0608011406 57
    0x8420200c3c11452581400038a00c290a0702c8106071464940003400044180d0000066034907550340c5032a402d80c41d40410001014800e410620055a101c03000000d00111603144030b141d0304241001849040c51444060003400c040720f910826140f03d1000c85039126004081804a42e40314966542c96103410f1280604541c07130605254480c4100f1001007503c01d4105402404941c81d201c0100094030340c1110100003180c000c6c1c540b43c458051078902c1c6981c4005006c96545014030802d0240015502c62000344407000d00e001c0800c02216602c0340c0002c102e030b0030b2910b0b03040d030140c0c1c800717200c00b0b004000402c0c0c44600540318605109a80802c200001c01c4a0724800042c0a0b5207903010345550140d0300010f011114407000140c04070b80541c004289080001c1c0024000e15541c0c4c07601d851461102c9118030024810800400580f20f00980300c40380d08944100130403010350025011100310b0590120200c001100d00c034039152090460b80004000c11280e0000e0003030149200c5505200b010440d8042d204445 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 732334244 1250 732332994 732333011
    0x12211202130e0108011e0b040f0f0b01020d0503160e040219030c0f0e0a09110f0705010e0601060305190b040605030712020a080c010f0503090319050901021c020c0f0402090306041401 80
    0x50060801c092903001144106c8040d40c0001d201a1070301c0c00c291074200d0348401c1d0168200d43c0380d03c00c0080f031000070302e0002812102c40d000242400c4100440108008007402444100148401d080840f0a42c0f81010107000700c400d030200b00a40604000c00c00d12240340500c10480e41c0d0903410148201009076200e1030840701e4400242c86051944030444d41046009005000305405030f407108040f01d80880c045400c002005040c0019507010410480d20b42e5126600ea040310380c01003040d01c0c003400050400740300c42c0ca170020401e184140700514947d001512840c0c2440592111390042001c0c4c20041c0a036504552110b480c850700300082c08080b4058040d031700c00010b50650104010700098816514207441804421086a40c0d82001d06807002d1400100128941303114018110604280c00d85c813215142e804c040001380c02d002c0f5507080d000c0c0407017090780b090b11002ea000c581d000f20103504071416584001c482000c2402400386048540d0188902414001441812446c840c05d040c0420000d00c485da8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 732335494 1250 732334244 732334259
    0x8150103051b1804022d090d02100e040203150a080a050c061c0606030b030d0206040b16020f1203060a06020c0105030c0d0e06040b060a12211202130e01 67
    0x2201250590300c400c0040d100b42191400d074500030503071075220b10f512a0146240500241c101da001c6c0032031a0210001d440503119035405481d4944c01c481d1746415050820b0740b8840810540000000001d2203142c0c2144e4046415002c0c062010300d141014100710340724580050f0496004080ca40b04a1117900005400205e809000134544034444e4848058400d4040340c005102650b000742c1304002032418201c51080040708a407080400034030f520350300458481e07003402c18181000000d4001c81c0443d00f05404000106030885030307103900184030b13051040320790740b80c00c108034185424a410040d0780d003e100d00d41250404c54001641c001d06084482ca0b800c10354806050782c3e00c0040544c3c250100301c0900000301d00320500805420304000b184400728102c44159201401c102d02110100e6000c0340110921900e420700d6440a0060404082c0c802c0c240070540c1c03241c01d5004007400004100264050360070340c0f12440703180034910b084c0d842001592a00c2d0344138410840000c85002c0c0a4030359401100015111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 732336744 1250 732335494 732335501
    0x3030c060b1c06062d15020f10020a3203090c030703051c0504080d0c0c1205071811040902030a06030b07050903100b1f021f140f0402011d041b08150103 67
    0x140c00d85c941c5005807515140c024003c108130804200f007507000d48000032480490600c11030348407060082d401a80c406840b00c001e0040000a000d01211034007400e181241160310360a140c1c03040072401e03003d07034882d91062810307468422902d21060701030258800001c03c004001400d03205505095402c0000d0703c03100c040444030350080c4d12440055511071286c1c0803203103004520903e007260065210360300c11511400b030000ea100415000715080d03804000200940b0f040e00f2080d07820504103140c01d00c280030071a444206d090159000340c1508650000100c0d10b2070315140c2c4080c004580c080003c0e103031442d05100140840d040140494002c1c00380308044600b8200c284142040d03104004c2c03510440c60800d409001100e08065000c60640c41484d0303404865190583c010030040314a01c0000ca403c202c2d9654103048000081c1c017140b4860140402c2c00b0050781c004c141001d03819000200c0b03c4002c110350001801420031203030010b1340c01601c00885c6c070f1750503880b000f201c2c40303050b61100d2030002240480046085 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 732337994 1250 732336744 732336809
    0x12030e28020f09090613050309040212150109060e090a02090d0f0308090601050907120e010216060e0f061f03080721020d02071e05150c1603030c060b1c0606 69
    0x41781c01000015400e01d02c0e9a0301510b10314021402c507403c0401d031501080c01c0b07a0080654640410051081046501c2000001605401c3c03c0c0b0708203000303d103420405000c00c048282007510400c1c4200009480d0780295050b0740c103419004044000101d0142443c0e055046050801e4000078240340004183d11800116141216005400c1c801560b40c2c11b601118101803040c00098600c3c1c48205002180c5001d00241042c0b401c0304a04040d0343d42a403414004032485001740c00426000f105108000d981f0200f041d039409101ca05e080182001c100302c01e0902c40c4011381008000e0351005c100003090201911b2030201e2440000c0802e060f4207046803099a50341d4181e1a090010390103c031051203c4400081c4110310b405c840b0448140700c64450001030740500c0c070003000740205131b0040340c5d00000314020004406d07600360080b003103140c490030364030010710518098a010303002035100c2c11450030075120010420010004200308121070031151600c01c0151185201d8000b90136541c00107161f0301d401c0c4800d4100c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 732339244 1250 732337994 732338011
    0x1051e0f120426090f040f0f2c03030610090f0b03270a031d0d1101140c0c0d0311012d0605330406020304030b0a0912030e28020f09 58
    0x1050303460820083c60741882c205c125009900d0b41084400e800440c090201400540c50300403c1038500603901500e81d0710244603003a0b210750164080c2d10b08400220480f600f05400350303940d03030000000d2102a02c11112542c86100c1414201c1c0b400901d14030740401440c062941c0200c9400c3d00c1c01d001c0c840100e0340600c001c141c12690061004000068000d13011695000c02c1c40c3c00500140d805d00c00040c01840214134195001c45198011840e2503070b1161410706400b030351180d89410004203480300d80e581c1d43c086080e14061440d20510b01c0a140c01071208031401c1942034024000c0c0311808803804209100d00008403983c034400407445807110b0342070044e5416980d0140180103050480c5509034071401c208101e00c102440910094442010004001c002600c442c2c2c008685d942e00c0d514091320407820081c001c10b140c80c5080d520000203110010700c5011000356140104076001c0f00315040d4100915030000f00080c0654080404030000030403e400e024500884000248000c2a0140401301c02d04459086 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 732340494 1250 732339244 732339247
    0xf1104031a0402190e06040c020609071206140c070c0b0406050a0c080708040305060f0906040f02060c0705040c020106090515010801120507180501032001051e0f120426 74
    0x45000d600c0c01d44640d4040e000511210711204420700c0030f2400c00c2d094120384000c0741e0740310400602e42014003803001400103500c010859450040500f50319403490b4014034079034140d4482c5002c1401925040030980d5441440040d445041488121040e0351000d441100d007200040310002e0000e0328941a50121039442e115685400314a200844156031410001c44072240c00b40f0016020a5844014001a40c4103400810303076818101c90030035420701d008040d20340d940e1100b41040005051403455954466040e245151035404a1510034107040e465000150001d00e0f10800643d4103505401940031126a20820046034450215903c100c444000425010990410040100038401038044a149029206071458a91a98041c0012020855030000e5031900d41c0c1c018014401c5009804c2d42981400c502541504011780000e0140e002d104204401510303031202d6821350144100860b403030407801c00070650b51a030080c010f85640c144152010380d403003555040c03110148402e4529500f01c035a06030b030001e13 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 732341744 1250 732340494 732340523
    0x1023001080c0d0c03050f0a0317010510030b01200601090f05062803060c030b090c070b06061803191106040b07080a090e19050c07030818030702130f110403 69
    0xe00c109800c0c0c3c0454010420400010108100b40101c50036102c08501501a1003980d0070010610a6003443d00d150150703040380104110354805210a807841202c2c240070500501010041e200031012504002c0c078180450fa60010145010450301c2c1a9804524100038800300466442c3c02c03613804032003a9411690340305100101d4014805010059044000314446440d100e41e5144181d80815807107001098482c08070182e00e28062500603441010204030f5400e003581602c403807000a01c00f511880c002e050000c0d0f01190440c0e02c061903900070401800300c50480700201c908510b03c030320642007038400221092500b43c482c0b600c7c0007100c00f00c03800450b005040609640300c107061607200e140003205215601e00d0002e81c01000e410400d00c0b4031522600b160300b022500711903078117039880103105860030481000308100181d040000710342c100c1d4581c0b010f01c0741c611240040710701d14411150060761010700d1281c10303849065290005031024003500018040844180c0d0210414019404010007072003110449 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 732342994 1250 732341744 732341749
    0xc040c02240a021b06040203100e06060d0c0824060d02060f21011401171b1308011d1b06180a03060218180610140c01023001080c 57
    0x800d0b044004180300516158580b200702131426102070f5000c4664114001704419032900303100030886108803c1d001d1000785864102d1644030603005201600c80e4060f1803940b4240403045d0000740c06082c0d07410441392080740c06040b585103482000b4501c0c40c1c136a402d40000b4480d0a090320310188095015048500b44281039401e2030f4a03820043c40e910910b42021019817214004000b61402410704050f0b815200185000041992019030003020b00a00118240250092402c000f04a40c015070407519803180b02d4040440c20b1060550b119400c15801c0803041101e5041c0307102980d0030202944211440f0043c80102d0b404403c10150905030f0090060149040300c0b8030303441e117001ca0310340010210305c0f03421b4030382c0c1d60401240c00030049030150421145204040b030800c40459a2650a0401c02c61890301e001c000207800d801c00c15070b0f408104000440410700e80c080c5403090ba0b08160141d0002e43d2100c20101900071032011041180d0141c1070f440c1090018111040141c030305944208014084005142c800e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 732344244 1250 732342994 732343063
    0xb041b05180301090c051018060c030201020c0a0b0618130807032706021b0a03020f0a091107060609020307080a110409090b010504110414130b060c0c040c02 69
    0x849001c003051029042001e03503082c4620090940f0942c1d9404885007480c050244042c0c642042d034040c003094a05100070b40600307d01440450309a0b15140c55001510f00d0100d01a00480d200d10f0034901c150b450601c200404600ca1230b00c206400d4482310308166401c0907444c801407065a115140510804140e0003092100c0014003900d402400e0429900681013850803049042e20103048d40003000350018440c0c15070512202c50503030521a90041d0004031040014040d1640f40f200030f01c00c854049020b0078588034801c02900404038140c4c00c200042c0e000300303400c203180e201000854580d440c2400101d8842c0003803090b81c1c094034903079691080036500c240c46400105080918101a000140310000344d00310356004a0001074402c03c2c803091694500303818803040d28500061015100c40a1000b03209540c60352103002c1c0c1c240002c41d400b6032988075013074068008000416003a90005400541c42d640c5000020b42c41074003460559081048664003001240c41d100300c48106018061490500a5810401903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 732345494 1250 732344244 732344257
    0x31b0f1a04230901091130040516090c08060f0303040b0d0617061e100b070308040209061c08030636010503160e0702070f080106090b041b05 62
    0x240c400e01e8607844254802d01c00c4010820091030b1402d182c01d002540c240b207440140182200ba005021074520580301d00700e18010140308064512500282418020071940304d08120b030049003003c0f40c2420542405500d03071400c02000d014002141d04006418900c2d4460000c00302e13119075608003161604010010600b82400d0f0099151005103c085401c0c501c01004101d035981306c1e07400258040c5031841080300c0c81b0b00315280042c3c6421050800801ea000300082000c041d02d004449102130746d85c644900e8000196030446851080040350850425401c00e030301d0303030041f40202d54043c9240c2e555020050040d407030a100300da03403a181005170340005d040c880c00f46801030401481d201c0036100b20b000c00c9501d0200200d010005081c4040d81203001c6000c80a180c0c0502001e4002e40360f010280d0140d4000c4203024816194803802010001e42141d1003448820042c1100b41c560003c0f1079035a041107406003419002d241c0e40c440c0340c14070120451826101e807200030307035021242d0f40c40d0345602e00d0103440d00c0d000b22 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 732346744 1250 732345494 732345539
    0xe160e0d15090605010902070b10050603060105030702150a020322021c030306090905010b090a020906040302011d090405100c0207080c270a05190525050408070f031b0f 74
    0x10010b030b074005282d50141d00c0c040e2201ca040141c6944280c2410300050070301403c0803a004602c3d100074091a00d459045a52200c3c007801c089943ea11400742c224642440c50169014154107041800042070b22a001507000c5c0d009000000c90900d42180305408401c40343d0002036000d40400f001c183d40a420010103c1824024100003c29560325150740342601d254101c101c4050355078000b680107a2800d00b0300b80707400c464505001c40c1000f0b50034021960511403404003905100c2612000404a01344c0100110451006003644903136007814540b00d81d03200c020240b208016810021f0340d4224520001b101e42c02c907400c000040c0305184052082c402c1c1d41c010341e072003030048501c02c0c1d01d0148608000740c280c1e4000c558000740090549031202042e248102c004a90004040c200400d02c1208032865000d00c044075001500a070920070081b209a44620030b990005255000c2c01e003000802000d40c1c1410350869004500402d409501c8251502c0d00010a001c2e041954496030400c0c0065032007500318035540d000300c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 732347994 1250 732346744 732346751
    0x501150f200304080c0307060f05040e060604180606020d050c1c030b030312010603060518040311100603050c0310020301030816060209040906020901110d12150e010e160e0d15 77
    0x112401c66003158050341014060380c1c0400e20781d14050900b0043e082c0200765178542001095500c0d81d0052081c440c0d445544079101400000c644987d42c0c4030211002400407803809140714850611840250165200f140e0260246d100054005801030089441c0c203203030f07000500b601c01c410018560405001595441c20107540b20f01c0017031076440400090541d1404403a60080c95890044e0040940f81c2a0700024003031281544d01d2451000008600d40e0043d40c1030400c6d0110403460710310710b8a80405846082610750803d14004144a808518003103405400c4c1d0580b4050003040301403500703038031007844020601c8000300405100d0070100b42070340801c2c0f4402d00e00035140c40b215800040946503040c0c3c041d13800d51307400501c0071607940c2c1100d503005100a0700c0300900301001c01400084c0000404c00d000b111040d4503450400780303201440940c000600500710010105584480c9025450b0504641c08a1045861030b00b1040d000d002e0030034040895002800302206980b640c1d5500c2c60880c4041c45200080c5c0c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 732349244 1250 732347994 732348047
    0xc021510050a030f060606140406050c0a061d070e0727030507090621080d09020d060c09031209050906010e040905011a01120203091005060a03080c0c040501150f 71
    0xa600c510b4600440c01101540160b01c558242401143c620b41c1c020340c03c0c0030540201c13111103104d100c1500c00303d031198145291121910f0081c00c1c03c00031b080302c004000074035184001c0eaa901041c056150010480d10440d500f00c0c0d05c0302c40e95041c030341d001d480c0e45002c90040008403603950040f48040c1c07050f00d8100550081c00c0c0d62941c0e9035150071010b0300610250b0751965814460400c64441410f1728441c581110f0305000960b403500200780c440c52003500c4019854002e81815511203000400c0901d9000303104204040302c0b61801020303008a804100c92414071004d000040a104120400035030310014400c40c103c0d111800103681c00d0011080c0c513a00b00391180c1245000c60001c2c80b8040420a2003540301c5511a00180014100088200141c0070319105105021242e0400501c405000c20020750004113920b410000035581007081e80000c008000008000840510208640034000b806540034815a62030b1102701c81402d000880c501d000400c10ba00c83c0244a201e200b000540c00443c501d13000c81c945 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 732350494 1250 732349244 732349249
    0x503072411060703021215010807080a0213090209091003050c01030b040f0e0a020a060c03080a0c0c0f0f0605010902030f040204091b0602330c0705010b1809070501030c02151005 78
    0x16001c65124011170b60125206004180413488603900158851580d001c0816501c0041c045000186c4038204201c24080060180d000c1c1d941140c40c00030b0ba10516080880d035408094010b903105249031030003001c0751004a0000c2c003810710701400b40c030b07400006060050200b0004400030700c08018520b910646901e0100d210041c0c0b40b0403c0303408520040980a0180c260050011000150388200200500d80e2022400300b903120400c031707410030450600031802c8480c05104545800308400042d001a01d000705180c10026040c00c0710a0740d911488003071145030b80c0c48104504070300048400817800420340000400500e0320b58440c20460f8031603140c6511211442004403480c405030780204c03006d80c0c400c02088040404500f024450324441c4032100403101180908507448020107020302c07096250108904003040401c2d00054012400507021f8410380c03d0303452000700d620314261884c4001d4003034503e000c036a5502c44c0c001d0980c071030195002004030514a00981100c520010300c003450324040c2040209559 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 732351744 1250 732350494 732350503
    0x6050702071a130501020d020703060e030918090709020703090e070c06050106110118020f060a050d1503030f0e0901180209031209011704020108040f03020102131e0503072411 77
    0x200d1a5180590312400c51120844a03800144c02c62819507009021050846500050020943c2d612440c041020b04844612a19501441d071503a40e000706041200d0518403000c0007018819401e2030202c60100d0b9607001554100c3c0301d5a00058001a498a002d101e0f1015101000746c0100b06403034010381400f00ca88840381200c40a0300002c000611400c030814440d40c090041001032148084c00500c4034a40d40c0c0080c0c07a50b0004c044560186502068451580780544113940600001960134004480c3d0100081da1820390b90204402064141291080b005e00c10041d207140c0b441d020300341014990074064181c2d40c42041c10565006140c0820101d01c55031014801c0900b54804142c040c0c0e01c4100890014064245180700700d403120406508000c05070ba4030540c41604103412241e20702411555040403400391183c600c060360300c020000320015412415000d0000003400d4a5420740d82c1c40d1710b0b00c1c101500c0f8009446940d409100340840340c2a1290041d010480d41001d41c200009909085814141031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 732352994 1250 732351744 732351779
    0xb06120a03050c28110112020403111f0818190c030614040506060402090402070605090d18080705060a020c10050301141c151805030301140901030f0605070207 70
    0x40d40420011000c0c0b10030000000c0c0f80138190001842240208001d107040b11821501030b22000820513103c9550b40030f200307a004c1142c000c050a40d900c80e102e04001c140f1440388200c4030f0007540070400c50284444210f11100303c4003070395910300c0b9031900c91682d20101804240d01281c040e004201c502020100080ca554240c0f5108030310000b000d034a14100714041300d080420400c240e40030801000000f41c1c1c04a440b5a2044085800603180c1d60a200420000d00403641e0040c00300d850482030024075038000a4582d00b00340150f850300b0800b1800030508103441c180d4410031019031b001c0b402c180b000b40b8140d8003030310800155204680d1a012400c0008035409581301c1c019000ca42d002006000304100340700741c0c02c85854259010780400b051400c091122000241c0301408966006001507003051a5401842ca0440b40340e81440b084c030424148181c07603500030700c101500c40007a4295025981400140c050499400a210f900480420340f00c901c080c0030010148403c5018103500801e0668104018401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 732354244 1250 732352994 732352997
    0x60f0316090f0e091e0a170403060f021804290d0b0708180a0209010b0d0905032b0b0307030201140409020d0e101a040e0304030830040b040b06120a03 66
    0x303a0401d6003459081c8040341740039801e510701c01080603074112000103146c40c5555105401196440c450140340d40d00d07020300d40006014a04042b40d2a14090080d00501340b01c03038006500c694104a40020403080f24080c20400080a00350503440700b002d11150a404840c03003014000c0740414071503035103d41100b40c0c100c41c027901164011081c091218504030954002920600050100c030260350006034266105214600244900040080b41ca02c4550820304529a0000c00c60381c40d0a4881009081e401200700c05018551040514401c84000c0d80941c1c8034010340a8080e0500f9401d68004403410f013105110b580002d1000c010005181d602440102101041030100107021705042c1a480e02f080c0d190100c10030303070134101200750442c030614008001000804480024000d04c00240860031802503502c0500b001c800440c00207a5003d100c500da100c582e0301d02040c249403031040c0704000307504032040c3e4014082014000c00140090640c0c060990044001481d80c95400303c49801d0780d242843d032140450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 732355494 1250 732354244 732354269
    0x27120503071b08100e0624130f2708090102070f03050c0429040218041401030203011404050a03120b0603040501060e090c1f0c0f050c0f060f0316090f 66
    0x1418814401c6181c482800c4ca428010b0411400c08541e8485010f400380460810004440b10080f805074501562141c0140140360aa503d564910000b0100e04d01004811400c00700300b04803610405603011040e400680c0001c0301e085880d2035102c03c9410420080d8154130030a100414540c151401101c000d45c4070303100502c011040346003403205490304100302401a0070300301d2144580100f040ca10040c03a0005031030040c1c544c41c4051210076580f040b100d9a9411503d400d41c180c1d150030314880e429042c0d900070f40c002d0120509013210041d80d803e003110090005e80240e01c21100107071164a5055070b0400c85000400c0706201c030720000c0e030741340d200340d504503a075a542d00c1040000840146a1f03a902c590300d113025040c185001000309140e80d07030309041c0d400c2084d241180560064040c8642a44854001d5040d080c5240c2074900aa41c071180f4002c024811444240c40f0101792a1010442c1c5400d007203112024115240c1c2c50010b0109120b49107103200b0701c07407940d801094042130010840020081610200d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 732356744 1250 732355494 732355499
    0x18060b0712020d03050601020a03080a06090c020109050d090501120b0a180e0c0301150501030f06150c11091e060d051906110a0c1b090c05040627120503071b 69
    0x10b490110780b0f0042030107060810080000d00d07038000c26220000c60301030038018415034400420700b00070039886d044a010a4074091a0900c900d505501102c101071048048450000d1410b105583e49480303032040074002072918000105512940c1c002d007000000c05402c03c01c00980740c0c0c05150f0541c121309481848d1566901303000e100381804010b40f0021084c10b4000f00007200c0c03811620303a59540e4a000e00340c181502c404244009800719804940140b2203111800011001341000502000080505807030060b408141d54001c1e03d4941161401a140c1d8072106140c225480d0485905010003008a035200d0701c00e065400200310103000c1d080c0240080c1c000b40244618034038000040b101d0b80c0104c0140000c06001c10b02401d904000085101c1d500400c41d0554856080198101744850b5001a2440c60030800701d00282c81d0450042d0080e10341d19143c00710519690b0149a803407444c102440520587c40c004100300e0704070103244c040710660081040e24601506500c03040e00b40c1d03039650000841c004400904 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 732357994 1250 732356744 732356747
    0xc0506220b07032d0c0203160b120c180d1a0103030806031e0303070810030c0b0a03060501030902130b061b03040305060601020d0206040201081305060403020601081204080718060b0712 81
    0x1807680704e0000c00203c07940c500b04900c0110060303c081101003807051002c2d165043d503800f001000b4040e10130b02d2050451035120a0b46850b290030000c20130a01c2e200c4800030650562000b02626180c040e04001124900700303440400a40315409a4261080070984c581082c08048a40c0301c240610f00907110510329040020078036181c80380030441044001036020f00d244800101004981c0c02481600c0c08050b15141c1d1841c4000910342640b0082c00645204000a2054024800b6060300744064408111680d42c580040d802d481a1880007507122240380350303540c000c1c50f080d0700c0b1010020700075140506141c112400035107480600000c0c103070705901c003140801c20054100718650340410280b014141d103c484000180d5a1100940001d05000302640002d040300d00d40c6101c1c010b200e82200440742031b400c0908020303456002c00c3c000d04c0b00c280144c0c402c210082c4d0112040f20202c51071540100300451822000c461446d0030143d09031a015190748000a803003014501409440d40103522018849507564030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 732359244 1250 732357994 732358007
    0x3110c0d0c0c0801141504060308031b0c0d0206040302012009130204080304080304030c080309130c0e0d0f03080606090303253806100806031231030c0506220b0703 72
    0x601b58032503400c000703040c40051076150170340b60800c0c01503c2039030100045c208030365224004c800c818100c038810004002041d03940042e81174080c6009400800280070b0702c0b003682150450301070003020071031810420410a1f01707220111042c070701140303400141020f0b21107030340c075003180d002da480400c07150301c045824018407003e1400c42c801000440021450701d0005008a0040695180c2c1014410780d26044291a58001c00151400e4800107042c500442c01614141c40504845001600024a1103001458a0400c007044030380d0044000d006508128140d0300641071028010013440c4c080070305140d1400000e0f490008020382d00c203110014141515500c1d2600e28414640b107200303400d06403040c140f0403a40c49a201360b500340d620514004041741c0d40d610101e0b00e4400c071540c1031814150005680c00b40040c03885000e60710b000301c4100c0c01006c6840700034420080e03200c6010262a030110742504120303e25203800104844c419a5201040302101c4142800c15654554010500300702d00082101c205580080c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 732360494 1250 732359244 732359281
    0x16120c0203120f16120603050102070c080f0705061b0c0d080307020d030603080409020304082206030b01261902070c0f0501030e12030c040302060301090c03110c0d0c0c080114 77
    0x18100d1941e4030304001c00040040007460031308180b00d4403954a02e00a44c13543c00c044055600800250b54800e842d260101c0c07100300d41d11034480c483c060038910705180440426507804031000201207508203040d080c000d120360131441e410f5101910540110240c2511101d0701e62034000c0c020105c2944910341510080d007410602003c00040600d0410207000150140040d02c06076604000010784030742e1a03281c911128440c0251240c1c039400341051813150b408002c907844d02030310700641e401e11660040d0300c01175030300c0d40320780e4040c40c00400341660f403418001c5100710595022281d044501d0410108480110480e80b0103002a120084107050a21844013141c0000300200020300c0c080103c4480580c501da114100d4400711050040000f0100d41c041e904442170354095500207040302c0d07995a40724400b00c01032801c1c2c215980401d0800902c261014a00015600700e02490f4000d8004802c9608045070034862019003181c840c9620708006c40c600e2002d1091108003110350711700808505114441407400e801d03c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 732361744 1250 732360494 732360511
    0x9021206010602060115210905160f05040507030603080a080f06090c07060e0c193305070501110a031d0d12021c02070c031b030201050316120c020312 66
    0x9030040220660015810341111000d0b4100040380d80b0110007181e02c02c5225034a50000104015aa00420b08540c0a038142d988601d04a078400c0b608085002c46681e0345209000d84204510000c00c0b00d03040c45c0c0c00541d4006441e140004149450ba5120f180c10b4001101c4c460020710203400f00501c0c8e00284040580244c0200c80c010124a8401040720640c410520020000c40c2c6840c000700d940ca82c1004803034000c020040401c107d41c0315008002ea4108102e10404080428803903e0f111150503000c0c08a01482c0c281a80c21086030208030140e80c80c0c1c0c440b10b0110750640d07032030950360100348030800503100850f5241c0d400f01c2c034007121000403e111842401d840352113030000301c01144141c5d005072040043c81303110340000d038503a880701542c80c10071402e49540c001c441d8000103a90382000145080b40040d00d2050302007882040c9098211412a081400000c0c0172820070030214800540c4082001c0c04228140b600308000e0030194880000e80302c04080010240c1d02c04100e140c0c03d015030010803544000803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 732362994 1250 732361744 732361753
    0x6160e0a0b1303120c0f020616051c09090209031510120807020f01030e030901030b0f03011b1d0d0f06020702030a03020c28030201080903040308030c1b01020a0e010e12070306090212 80
    0x3192280980f101c1d8941b0001e11402001030100c24003001084418515500704080c2d540c211412242c0e40040c4090720940c000061400b1404522803201d4402d881c100c00002c1d005001092081c0c00400c04260090103005101c051035000048464a07410001084c503c40c1c42001e031540c1c400e10501c400d80807000b90050601d8141002c94400c4040002a0b8031b0800d024640403030b08842c3d20b804910059021400c0710340550900701010079501c01a86001540c408079074400c0f02d6420390040d07581d41c000c40144110761280d603c00b54100803c2a20384550145030003907030f0044c540081d542c0007030329000401104802682184c00300f02c001d49010b0050404401001d20788100110585165400301c80c07440c00002e06101107040410010042041520051507214800707a40e641441c00280c6801d4000042d0b4a01c003c11101c100c10000906000780c4001044a40b80c0140441c800713801901d03840c0304221030503000254441c09030000081003240e03000541c00f0707017000101c020b40c60050008015080c4048035a5a00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 732364244 1250 732362994 732363017
    0xb040e180a050703021f0c06051503060a022a0307080f0c0307050709200304080309011803030509100614091815060a080102030603280b0408030702060906160e0a0b130312 75
    0x1c0101d50681a0b0750301002c0050103032b50740e41913440201d044683c1140c00d48102e0007002004022603000308009415015400700107048114401a0380301901c82d2104c1d590401d0025200281780304015240110190394180d00f8141c1038001280b564118080075200f81d031251808004406080c4034248001c0c00c10b2511051201c3c03003051000e186d1101070300082892100100168513403000794400024810008400448030441c3e04005000e88000e42d41240790b4014805540410002c074402c040c1165250702001c802c0a00e020200000c0010017032080c11190700322240e80700688418030107690061a05545d01c419418a50144449030b2000c0d0081205a8810800c0c440742c0d9a0006100203052505444121a81458010400d403e0f03c840c80040c131038003804003448100116500614803510b280e0b03003154450b03501c50f0940c1c0d40d210710984075041c107054426911180f451041031800c070000005841301c2001a5240b00f01c502d10307401031003c502d078000001c03000c3c010441004005074a0b9901031511810b01c12 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 732365494 1250 732364244 732364247
    0x24161a0a0f150f0608041a010b03040605010e04201302040b121003110603070e03011107110d11011b120804030f050418020d0f051602160b040e180a050703021f 70
    0x10940141d000f4880c01700001020040080031021002c00f50440c038148659450030303001000d400941c1c0484615092100100300b8500390642c1c6413189030480c0340d0302d414002d03428500b01c104180000350348c3c200c0da4400000c41d840246000501c01043c6072036401741d4900030326644000513000035110300302004012030100701040807600d189000580880d4616501d07110b8880c251070450011040a406500b4204541c07088a0a0030203010414000c4030f994030710351040c2e4100301c628008048000c5c0711504084001c5401d511030003408080130040403640c04803590981314a4181c41d00700481d50000303000c18040004250380202070300d10f4545941815070905091440303100c40e803d0094205100561f01090752602c10b40079401c03051b080c80c43d2507010000c90411070500100d000c446c00e01070000d4450721a842c00d80e80b841c502420101c0c2c102d07078001c2c0d04190610802000ea82e0020b403210700303030010181c03c0b25401c0c0005d100761614a072107880100143c520f5881440361480f0381c0485821362440c0301d018008100d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 732366744 1250 732365494 732365519
    0x40e070f0609082104030c0b0702011b050601060e060d0e010e3304030302090613170a050c0603091c0e130b010f12180f0224161a0a0f15 60
    0x4500740f04c001c00c20003104000910380e0380a80c2c0c0c0043d0110204282c00511840e504c001081c680b030007a030340e080c10707010002059110001c01d11b000820a5008400404c074080c89203074920140d40e401001c584c40e180a000700c1c00d0a440c00c568080c0034596540307290f900b10b103404002c1c082400c02c0f802040c0061403481c0c10210f51910360a4410205c00d0004400907003014404c1d412070b0200c09004007081c4d16142143c8c0d40c000180003030700440c42c00c3c400014030030409500001d40c40c00308561100080122014120610102d0b802c003030040121880350354403501c0c9d40303003a06030300104c42c80156461080e640a0a410441d411213a0564a01c916243c20702e0b602250364003401845468140741000c41e0b005c0342c04419080103010a110b443c18211512818000f04a079201e200800d06000702c506e005c2603041444845054101301d00b1062201c0c404100c00e1180c038114003289510640240000c0030518150790b001e80c0d0480044500003242c03680c61070444d0311f94180784611a040d150500090404504094840850307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 732367994 1250 732366744 732366763
    0x9050f1e1507050f180a081603060902060705010204081c090f0b0a12020d0b1503132009010b0d0e0703260415050405130203060f0d11040e070f060908 66
    0x7458075800500d106000b1411168903482408010355901a40c400b0070074002e0b00708034500d1140f0004d40000800600011700f900c01000714540035816039245030b452100401218a040341c0141c828009040890028800f40c0018103900c000740503040c501d11800809145c02d05441d03824000314110034443c2407004c2040d0307820380340c803140003170380e14450703402d080d038091f1012400509200d0001503203801c50101741c1c000400803041035485540e07000380030a298000d40000c032820340000d040107422001060503442819544581c191121004001c00004107055034802d030032103058103800284802d054010b601c500c2d020707801d080b030141c40c80c907046075a041a00d1a142d07040c41408401206500d90881030390080381d00034085048102201041c00c0b00182107900144592840740d1008200902007019a0007240e104507402004242d070000c03640108081c00044500503101c0c0000380b651210f10707449a1080790018009040100401c038548140c2308030481d840d8000c0400c0040c1c0613010450160700040c045003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 732369244 1250 732367994 732368023
    0x10e190c171b01021c0905010f09081908130303090e0f10140f09040c0302090f13030c060b030a0309030c060c0b0f180607030501150305011805040c0909050f1e 70
    0x14a80d40140c0105d290507a10190401c1010220110051260b0890056030883d00d003a240c3e040d041c20442e50555607200e9903c962509504021070b29821410a810801c260398800c0307031640e0900c684c01c00e12048200e441c0d002180030420110043c800d01010101d156480804584014141d250007800c0e01014000b5203d40b641d801c2200c03100f0052a0b8a511060482c010045c00c440181d2030a42408121484144800c2c1d010714042000b240d03031203005191051181e07001c0c81c0c2002c01c00170256401c540c902d03007961040c1c0e0000c4d42c8250050190781c083c410b0401b007030b0083d0f40d03917205103056040c10307180000c1580c407501c148501d16089a00144050840560114108180c0034855855122805d00313038802d28240132603401303503a003008603042d015449603060310f0100e021400c0e05d1403282c1094080380c40038018000124840905840c10180a80260783d029201d09511130365a40d94040070015220b000304112002e400591900200300300420182511044c070b4548030b101c0c1c1c02801140c1d5284d0f5000e045640 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 732370494 1250 732369244 732369283
    0x1050108011506021c050910120f09120c030c0606080c010f0e030d180302030d050a120603030503040f151a01120204030c0b030709051003060e090c03030a0e0102010e190c17 76
    0x14618000c0c011f4650403100646040400c0242090003401c5058040d0a06c04082c034004224225509510501c0c64003640990b010445a0b19244161800490390780100c00700450702e100c8100003001401004010100326000b804050b0345000098110300c10140303003401b00b020b802c0c4207a6060342d000412508010b020306000043c001010340e020003007030281d040a501440746091140c0c1c032980c084c004120354070081da030710304681d40d801d030b03022081d103c0c10311010380014414000701e40452400401140c10300d11680208010344d801020340404e40e0003070404c80384440f201451182e45e0b96080407044211690303d810840c50541107035127292403200385006582040a0100c0000c1a003400303401d940f07015180082c030a030b0601040b01d5000b805060b45004a1000862010224004410001c0c0700c1c421440002c002d9400d0100c00c1c40c00711810f9010441103070456403681400c0740000810b124980d90405e00e0b104048641040b42400d0340d04072010f034403000b0020356220070030003410b0300030070f049110740c00816010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 732371744 1250 732370494 732370543
    0x72906012a0c09090308010512070e061017010f06020d020c0307031416090203060a05042d1d01060f0e0c040e1504020d0c02010608030708070609020a0f080105010801150602 76
    0x8074041c2ca0140c210501051810015105041d0480390890484604481d081c0e001620000300c50780311402449580446840c80001c07401a240c00144100f0502152401c8a000c420901e81c40c02c1d491001c2c3d00104c0950707000003090244e40c1e03040c407103440500e615000504460408601007903980306240b10140c111190079221030b81d40c103c2403058000300e204c91924182840e03100d4501100a50003610500d2140202880024075804d007402a0f0760400342544000801c0b4884020f070403c3d40160f00e1061041030703600c40e5103d00411024000b40402c01c0300e44000544182000b040011548043d0003000c0c041d14200200b040f0207030742008031015100c000088500300c1e164403802102441a00e844698828004036010404250a500c0f4184d45a42c80c0e00901c10260741e1411244c50f0b1042d0318000e010410b0800541c030105107141c020708915840506003106407070340c4071414a200d94003504694500c1e5110b02c010410140f00f401120721458801680300c88951818501035a22042c1070700b804041200344040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 732372994 1250 732371744 732371753
    0x20102030c06090c040b011b0605090f011805010b01020109080409020f122e0501140c0a05010c0f140406090e07090918020406290f072906012a 63
    0x1a07a0071002807100325959400d165021070740b1400380204060245203484181100d541c80b80903500a103a8102102c41f45084031a1624805400020400c800e1442a4103101206480034454082c3e20100d90a54810141a40c6042070960783c1c1c80340070720b046a0511400d04040b0342e07070340b0448003100d40304c0c100103a85502c0d0442c1d039251409030003c00040c01001d8010044420046281503c207a006d0145849001c041f0340540312059049000302030002d100320710b100d400c0e81144401082e0411202e0100c40d03038030081e80c1e01c8a09541c40c1106c4440040c41144038108460342100020803c0054a07007414101420040c0040140c0001e20480c0c218454040109009030300441c1e2a40c044c4c8030303200090260161a50a034007030503c403064201c0c012850f0800028240741c811010303030030404140e01140c0382d1880a115012a42e00000c0703120300a800100098400030742e002c0c400b4102b5000b500c1202c9002c6000c08524190b040006281d5814486041900055a813000344041c44a2422003455010600307039061 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 732374100 1106 732372994 732372997
    0x3181b040e010e1e070801090305030402010e040e0f16060804020d023a060b01020610050108090f100e011d03030403050928060807030e071202010203 66
    0x1481001490550840095400c40d44004101c040300f0035401d40c101030007410b5940041d8581d8081ca0039801060102c440144554002004406025207019182d07103c020002410445032800741d0613150b403141e211400c1d60b4401b20444074043c00d4180344642d10700b0101103000d09011950b5000480d24826051144183d5001d0310025040116a0a00803403001444081d00144200311042904ac3c254170341e16480b41c0c0040070a0220f202c0a4103210048a01c2c1c8020581150002c0d010088001060b82c2844201c40c800e103440c03402580c401c02d0342ca00f008086000c200c550f01444d0180c0b0a6604c0d15004110021510f0000300029040318414070305004618030f1024480d0018800a00071174080c00c0540fa5048000d8150f459406140508000b09010520050101d8400713100074070a940c0d0120500707034440410b00b000c04c040001d02198540d984894822021100400e03003405003164401d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 732194244 732374100 := by
  have h0 := BRFrame.cov_init 732194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 732194244 ≤ n) (h2 : n < 732374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
