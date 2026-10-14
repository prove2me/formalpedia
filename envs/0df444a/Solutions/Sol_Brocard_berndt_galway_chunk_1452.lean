-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1452
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:03:22.934287+00:00
-- url     : https://prove2.me/submissions/efc57d5e-9b84-45e7-a3cb-6a28e1202108

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 260971223 ≤ n < 261151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 260972473 1250 260971223 260971241
    0x203010f1701110f0d2703090b03071e020109051213090b1c0203161202090106020d09090203070c020a03050102030106080c130506030c190c032303011406090a0306 72
    0x18514030346950140d0007061054040180991011910f0070b150503241d804940d1002e4800c254807036642205980d01c2000319002819009040002500d161460038000e0209185030007050318038004200303002005803c06601800d034044101c4180b102042030909038010008484040d010b406200b40240403c2100c0d0000c00c4140c083c03901407103c185c1c907000184110703581003002c2508007001d0884024042050481c21811f41d01c01003c4079081131420258207a014a01c0d1300c0b400306103050001c440114a030044011780034150a100800c1d90340d0304200002c0281c99944540c0648603070020101e510188141411680c07550080c1106000d169a803034010b000758024410383e4001182040411441c900c20422144420113690007c0030243c00c1104200280d480501a40c0d6070304420410f020500a40c100110364103000c0340ca580b03842e4003250030043e0a9072000340350714400354021086014111821809c0c2c0f41074401d450000080389560704041252032040c3d424681e070003004107400104002094210441d8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 260973723 1250 260972473 260972489
    0x6090115060201060807030602032802030601030b0405090d0c0507150504050f01050a1710051201050a1d0a0312060f0f06120207030917151602061f0618090203010f 72
    0x401d550320400c80c00c075200703805042a150040c040410114080d9005150410005462008803c0e41400369503400038560702c91200b001d130080700700009503805100d040070030030f001e8506101034a842d4101c561203d00319420340c07007072020707821030700d028080304100b60303400b81c0803580844410350300c02e03c0f025200d03400505c5101d101c0d0f0b480030110358040d48540b040d151000c00c1038540301c0707422480c488007024032607009041c546206075145000404d6602c2c40398581549400034000185824104a610300359180c5000a8a00880c564100c030b80c641070024006590540500d444004003181a21440103030510798820411207404110111303080f85441c80b0381084440360f844007040301da00c80d03150303234142d029900000d40400e141302c03405c1003034038040804006001d000c441541c0701f0001000319501c00400948540c216601c1c41c06c0c0c080c0d100d41c3c040203001d07000b62200000c1d6200f4148084005080002d078001c44c000c100088201a030306012107401d40001e02038440e410b544941e10740e0b48029045403541701b6646 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 260974973 1250 260973723 260973761
    0x807060c090302060a05042606010e090a05102c190807080301080607090603060b0f0a020f06070518040b0a090b06040f030506240306150a08030f0c1c020c0d06060305060901 76
    0x356100e5036071091301c92350452802408841e0700c1c00045d0b45034100004c02480f01402800101d40015800f401a00d0554541090000f40d4450003040c0c1444a0711070f00c049480110b25103090300864900140310300780701d40302e608140c814044901d040c4103980030710b603001032906101000108004202041e114480d100303a80e144a0031654840e011400c0d60b0841c4158807114504210458440b440e010040c9080da40d940100c074848129403600311b20304a41140c00308002000820004031017041e581c13001b128038904035010300003800c043d4000b680300c3d0214415980495a14014907603192583c83c1138600400000b2007011401d40e59050180d01d424045a003000c1207441d0440ba4049062801d1a14207038030001380042c1026a143c601e0710003511015032541d6480103040c0000144c40754100020150212030400f4681c44240e81c2401d145003842e201081c0c0d052401d0300304003460080e03002a209000e510104c400904966583c00c140000741019000a045070080004020512005420940340e204554011311 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 260976223 1250 260974973 260975009
    0x90e16030c051c091e060e0105061516020a0302180a0b060a0807080402030708101a01020303041502070206090a0909030905030d02150411040207031205090a0807060c090302060a0504 80
    0x342c02d886000c0d0300074500d8031100d000c1903218981d50300c140d600d144209480c403407090b010110342c0d100c1045080102d55035615015025501c08003070041c80c0e04081c059410300d000c1602d150a5080d43d0091104650b18030003180d01130029941d510104500858000e03064820b86d01c00c0c24803000c1404021600d22842c2401c00250304000e080c160121071903107511707503030320a40d41c0c9880d8412541c1d007201034000c0ea418410600b0200d072a8906124401681078081c0b80083c0d02841c14680c08085030100201c281550000c1c010803000c50444105000041402c1c0f50040e0748020310b10000b070710f0703021710a49a60028501c01c1c0200300c0390807030303030001c08402e000307498101c8440d0b076407410541c0e074192103003c2500580100b455550490036050b070701780d001382c8660804c001005d105000310317089030000b40040e000150603078103040000311940310359600145814007522050803d0749914140c0d201e40c4200500607070341c442c1c001190074415011200a15070040190760359007a4110001c040d504540034074a02078805400c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 260977473 1250 260976223 260976227
    0xf060a02030a02190803010608040f080c0d02060105031b06030711030d0b011106010501020d0f02030c16050901290c03090315011418040f0302150108030703090803090102100c090e16030c 82
    0x41c12510317600202d810300d180e0a1800403140c5040142085030701240d83c22907040040c003d10083c04074084480c004000000710010024a8014103070f0011b170080d0043d80c0c1343c216081285010380d9000006131040c40c1d5070f0f2a40b40e0211480c0590700145009408086041004410140c1290510400982e5552004883d5a01c915160202845228003580c880410790016074010056900c10b40490b0040c0c030308100803800c2d280d0503c41e50080c89002007000c2e4909000030725090030528058410140e01c2e181c5407180391080c6c144400c0304010aa001c800200700b500c44880d080049400350f601c042c040e074440f80c0ca8412800e010302000c1c00340700070804a50100c04d982c2c0c1806121508040e0020108203460b0301c1c0c0d921103a080003c2c0900580460103011106600c070103a03503050030b009105400007541c0d07078000381c10010551005504119000d0b0410082a00142c0e03000841c20200389040c0b02c0010011509541901e40c00000e42c410100c1040c1c89040103c040d50622a1005c101001d48061151209950003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 260978723 1250 260977473 260977513
    0x70905130b010c03030c0e041103012103020a170714010614010c030c0602030a020403080403050d02011505030c100207090905031308070608040f0201030f050f06040c14180f060a02030a02 82
    0x403060004803c1c9040c440880e01c26007080603070061b2030800e128080c0c0b8070300c00b1406644800300d040b02850400070040280c0d85506801004181000000c40890100b42d58001d4445841d01c00140c01c40c4070b02680040700d01e15003012542d9240d840215400c2d030408000545010f40050300c68026112510441a402035016011601c0c645505554510b1840c505a0302c0b207009400c00381010605641c00d1201100143c6071000070409140070b4401040c2902207484000e007541c1e14841000406c031003c020800541d100040c294118134404c80710300c030364032600c007000705d18000c06c0b80d1003449414288020b50051100200041245407508031840444980320044580c1d2803210307110383c500081c0b61400140c0840c4a20321541049441458081a603c004000d100240c8406035403800c0824040c0c800c0c0070351442c0a109001c610b51141c00d109801c1410f604201030180120240209916050003000441d0340d00c44888840002c2e00510040c1c848021032402503594112a5035117016124250103d0010343c1f038001c07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 260979973 1250 260978723 260978741
    0xd0504080304050d060b04050405031314180901150f0608090303010503060c0711100905100f0503060d03020120030f1503030706020a020321090c06090d031b0b07090513 74
    0x9610701480c3c030f000c3c0000818000e6094608a980308211102941e0382c0c051030b03003d540103800641d01d0341040100c0500044080c0c0c800708840c41c042514a000751074090308081d8000050000d0003643d65100303851130251030202c074202160303a01c0390340104041502d08000c1c3d00f0f5440d0342c0d4444510361b90380d1204940d6807200703000700c0d5855482080000c80c1524100c0081c02c0031031045a07511a00300d02040840e04125502c08900081050b17400c06209038240b540c455100c480f5640750040340c0d0345002402821500c00944910b00034948048200103143c002d412a1401d01000083ca52414007040603501b1682c00645400c22031005020120b940d408140e581244440ca00a000d10301d0212241d9900c8001d40c050050350b030a500003840700c80c41c00510310301d10304c8000614012a985a24003007000504000e9580c2001d8030644007401641c0e0f003038840da294141301641c14146101c0004c400304000c0707900038554000806d42241b1808202351a0f42c0310b0185011140152070701008080380702400816550141 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 260981223 1250 260979973 260979989
    0x3080108010b04050411090907080d03051e0f0612010b0303030a050a05060a0605040909031e0e0a08030a0e04021e22050d021f1407050a1b05090406020a030f021b0d0504 74
    0x24541b03044903c0c1c503950503034000d042d8800f1581c0040d5202607039403c03c0e180504000120369210100600100281103135010b030b1000040341c00aa10b484558100c401c85c1c090921409500d01c10802060402c096110341c207100001030880c1c0c0ca13460002040d5010300012200143c0203424200400d04604012000106079038403500c0b8542041c2c00c0220070344c000c05041301c0607810088004000c0030120560100c14800e541075544900e42495004c091101881e1154450700c43c6501c00c0114088055101d220a25451000c841c0940d80e82d0444070401480070390128602410403000070490a540d1840c150b038540c034103803103294200d410340d03400130030070048d080c424007075007002d1840cad040b09071081c0a88a140c107100700d40c1400c281321000740c01e08403607942000c50101c41950080c282c1105100d400529415091941c2c0300b00c0d000e150400000c10f50080014000030250303600071410041e4240240c2002144013008602107459081c154000c0d08400340700c462041443c001e940907032114a1144003110180e132104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 260982473 1250 260981223 260981243
    0x40204030c0f1e21020405010315110301060906050d0912080405010e0109080307081806090d020f0c0d1509060911040f0b0a051909020a08061e01020a030c0206130303080108010b040504 81
    0x4050001d00021104c185070401c3c41d6142e90001661a403207070078040d501900d10f85c03e4200e041c0756040308072101d41c621055503400c14401003200c2a80230040c1010f407a001d140c4161100c01d025901d07005441c400000915411101030724025203580480e80340e20460281c00244642d0b03450700700460072038000b054040d00d41c120070800540c81a0060301c0a68024515000360400d03181da09090b01d01b0100c3c1520885a590000e03042c10101c01e604020302c0344200c80c50030290544c190b6860004103074244c400401000300400f03400d910900075940d80a0801c07640c00403000d10054840d80381c02c9028040440c1181e00c03440c41c16100c1c1c0030701961449000c00002000e400702d000c4a007000708108a0a00065520034191881c0c076010a041039140050004e00740982c030307100210b040c130300c08021085401d644441030f2200707140c08014541e0b034000341042c03005030541404642a102400415401d1003a0b890f03001c454104114008101644004003604840c1480000c2000165541c00c2006442c07059401034803400300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 260983723 1250 260982473 260982479
    0x1110307170408030402041d0105090115060809032a0f01090b0a050f041103012009040506030f030a05161406040b1305120c0a020a0603060303020601090504080a110309040204030c0f1e 81
    0x2c59482300d00c0c62004a0400c1501e440d400c1c0303040382034600c111034070292651907098084203840941c40c51030250041c5d0a0240c1d481c0b9110100d07a03a28003841386c00d00041000404c0c04030909450503500c03140425a00180d904604c5d40103042400703001703034070303800c941c202a4034001542c50841442030034000d81c401980c0081988450b1944a00940054003d81c0d1555032605007081d002c50355042414003110825521303856a180c902000215440149098080e4210605100c852500402207881c05501424901d4450f140004000d401c40c4001100416201c030702540d05c5106440010bc1502c035912880c120009983c0340409045001e2249500402c0c0c0d50140c00e00000102546014010403500281107035030007111500003540384845607104101080c0d03600424801c2c9941030005074003420f4507280c240068106a61411a10302c502c9402c1e00420071350350342c03054540c1e1042c0120b952450b0300510664440b504e03800c0c14083c101c5076124220102c1070103980040c8071120908440d50712002d0050480b56585 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 260984973 1250 260983723 260983729
    0xa060e0d02010e0609030307030e040b0103020301050112020a090e09011d010216110f090415050a02090f090411030607020706020106080c030c09070522080f0a110d0201090801110307170408030402 86
    0x502e580c3c01640400d0074026542591002c0000d0601d0b64041d03901c0c0151850000240012921503030545410140108014005640c00c280c0c81c491540281e01c0c01039440e941120204c07121881600a89000342c034030801c0c40b5000405400125030020340c490340c0340c0000701c41c1c017a0500302d100d0040503103450940480c43e800800d544040304410140003801e5007085d01e0005002a4841d0341c200c5044440b00700d203540e03183c5840c60ba0720500f81d014a02e40011840c04002c1c40010302d020006d040600d102e203625400240030808109400e000d07841000d01152854108614040c2d04c8020502660006610382000050707203070000513044400c2c00010b0050b01d03d9140c240c007841110b100c01817120003809020801c100d0b1035201400b0328010419551124a00a820070400c907040003110b078040e2215a104014007000704020260161004004803040d40c1c08155a100580304080e060f400b481c0c07154030749040483c0400c0c0303107002144620302a9131313071a0205603c0d100521159105489c0606000c0081c00020010b003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 260986223 1250 260984973 260984987
    0x50610150513080d020d1b020112020306040216080a1d13150308040f052701060e032505181e130807121209080d2a0e0a060e0d0201 58
    0x348440da141d00040c0d032078140c03c0b407424056008020040e80300941055095501c141d140f900c02c242c1102e60b480c00100350300003c140d05807800186004644c0040461070664075a81101c811251201c03103880c1003052420480e030b10350004903002001c540503c900070048041e0f410000b04400c801000c00c010408045607010003401c114007521034110396408003002082404004d08028040b00c528554210b060906004200350202c0004103000103038101c00284802c0d0f120402d0540f030082c030301502290703c0c1e100083c0c076200808110302ca40c00080d008903840110a56024825a41c007a101403002625075900c0302e4030301c582282c0c81803048134000c080012030f548214046400c6000380160015103c69a12104007603401102d0840d11101c10b040d0200c80c140e00a413889415500c100d908107c4a15070740c50b42105c5101d0540d481c0c03d0140e0395042c5841c103c4480c3c0c00384a1810350640c0c0007000c040d050b040a0030902e14401814400c4413000c2d000588075118104506204902400c0340000080940c0156600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 260987473 1250 260986223 260986237
    0x20c03030f130e1609090225230307140307020108180a12020c09090f0c041104080303090a1a13110102070b031314060c03060d0f080301060c0506101505 67
    0x140010342070000303c140700d11030301c240a43d00304010290746030112100680104102c4c1d101c000194014801d030300000c80507a003141e64440385000d456480c182d0500d007004c5124240d1070001c285000001d84120281000009000c01a02c43c60314200055010400c0c0e503a64004d96000a000036140030010314000e503404620f4541d40c0c00c10040743c04512840c2c0e6404440390454030070400503404281e450941d46032413005590440188005440d0742c0800803034585c1c4441d2a41c502a00079a00d0751070942c5000c5920044900801c0040e040e6908c0e424600d04407511011070060076547c04507641d044409900d5070015540c0250b015195144580d03025035510494510b869241d60f041d4020740790009480038003c80114844c402e0741d1004a01d0761aa4038210f006400113004c08140741d40414100000e0007209412a81c001508032207403041c1c0c584034903005444a01202004001510100001400c1c6401281d05103039503103d501910034968078944281d2000c803a070312130b0940409503903010051844c0944014030382 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 260988723 1250 260987473 260987497
    0x108100f0b1c050c0a080f040b16020c10020105010305060705030f04061a03012d02040b0406051c0f020306010e101e0306120b04020102071d0703150e0f01050907020c03030f 76
    0xa40b01c03446985100b211002c40e03101d003400000192180d6240c0d03010b00c0ca96801600032060841c41c2c10162941580050028030380c203820811101d44646690007081420003030a4001e010f6811101c841034024003807d001c3c80102c41070710821012403c01d50252007a00e101d094042d40040741690f6030b131128000f80000d2818001901c001859500d0562000e0044183e010814038410040d01c1c01c420300c007031400c19020000001c41d44140403d0050b4000c90301124120380c254a0419121480000d800c00d410384017000541e00c0a18005800700a00d6007500510700c1031600743c0320721400c1016401403010030300e4540300d4000058403000121750b52200080b4164101102c520300054500d480b00d203004101c032201c4a05490702c0c4251010401150b0303042018001405003000c4003014a0050110140159405000007007410344a01d82554070000300d5140b00024542400c07500414104494078014103002800361a000e180c01500065600f40001050203945401400039843c04210302c9003002d241c0c00c0102c040c44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 260989973 1250 260988723 260988757
    0x207020a030803040b040c170712021c0605150f100c1e0503070b16090b07020102120a0503070306050604080c0402090d06113403081e01090603020108100f0b 69
    0x100b0460700c051885240b0400b43ca60150a190414484a04856000c0d120314a0b05c81d48040f0082400300311503044a02012401a0340b074860300c0001c1c408640e0311160042017002100079400c0c00702d60381000d80104024000c514491001a09102040c038001a0894004000520000b6540e1040c0f4560b11064000c9425420301d500c0c0740d40310a0840315403030081e95140d00110700c56040c4804241040d4100a0110052244e80c4100030094108642c5e403090304201d02000c40d0040039a4001d01101b00641300c92603400c0d60303400d40f448020340250016141e4800003490000c0100701c5041000071501500c00280c002c000400c2c2c00b1081102a5108908103900711000003c9503000640e80d010751109600507100203911000c1920f1000302080052030040992540940f040307041100e0340030030f00c5940341c061824480547d14000d400003005c05d840581a40408618000680340040e54080c0c01502e10076a40c40c6800e80300c0c5101100c000d441805001001014031008110000b6010020b100c02100e2992800b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 260991223 1250 260989973 260989979
    0xf020a080c0d1805030c090406090c030b041a09030315010c0501020a090e0906070c02131808030a0c031b050702130f020409050c032707030507080703030e0108040f0201030207020a 79
    0x3100350408998081076034007015070011415008591400002c0c025400702168514080c00070b50384103005a81c1c1405218254041018481d40d81c1100f601150080450081141c0e40c1c0b80038031204104a40c03c1e9000c80060201440068032900310394003c6800000071811078840c845480f09500d102c1d0790300340c14400c410503000005002030002d40140300050b09c41c80400b510f442c00c1510f14000c01820303036515801c01002c015079541c020a03d40c4181e501074030054003180f0b04c2500513004005030300b01504415075041c0c40c0c00801c03800b18021803103a00350708020300400401b418250b003a103028500c200640c4003100385c1216201d101d40081c00c074080c001000d904003203043c0b01c1603d0403101c0842001044580000f002d004035040b038010150003100c0e06116500d180b4101c4403294200d07401c11415010141c12605119020b41c00300241e4000d56081010345100990752001107590701110701c0100c000c5009101c030f0700015030141c00b80314822a080301141c81d0903103403030780114020b40c484141241c1c051201c0c2c0c004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 260992473 1250 260991223 260991233
    0x4020f0306040221190c060905031203011a0706021b16060e1002010603140f0714010f03050a0e070b0d050901060501092705011512021305090421180501050702060301060f020a 77
    0x1011445d40500c059007025400c01200030980b5401e0340107d4001d0b4458a0040d40030300819044a04513030701e07403140c07500082888803d246188603550024003568004a41414403a54a4018405a106e03150896121108504801d080c0c40311070b10038480403030b1000f001c0c640c1d641840005c072495010144000205140c4a03503071460307003844450034802241c0c4403c95841c4424000c11810024080b20a40c046c000811500000c00c0e80c83c104030340b0780800d42c503200840d84165a6402c080b41d581da4540503200b405455a000003aa50480d0308200303039240c100340c0400c1101c08103206880590300103075100401c4606010700303070040c10f00c1c056024041010104d40001500e40c6482502d001e008200d204003010760707000c0380c007d0076a00e096a41946603841001440444231703a03081d20740b080b50b6083d40c000000d0f0b030310350400803485c20482003040304851020440803002070303000880c1101d80201d880034940712034883c4011103690180e03000003900321004100520209000d1581c03095029620b104803140c000c510760707035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 260993723 1250 260992473 260992513
    0xf0d0b0a11030907030311030315130b10181a041208120f0105040e0601081b040e030403032d080606072103050a142512050c0304020f0306040221 64
    0x15115013100509004050b0b00146150040f1400705c000c600358286407001040030640310760703400d11810440010344070545071908000c0780c0c003900038504000d2000c4804082c200340111100f030a1400c10701d100c003080c00b51595242103807002d5540481424642402c070060800c0c040c908003928004024018880106807491440c0d01c2a405030564043c0d9515000078841a2170072544070300625000880180720090002840d80c002080d1403e1908400030034a01007030081c481006210110300000401000745034111600c0440301c2a401a401c078190301050400458086d26032046000a4204000c82d905240c600e000d400458081c03c02032258460807464045061442d05090010171b0700c0b24104503e011b15446a0001c0880c201c0f0030181d94a000110940800420020030f03039400480c2e85001d09080c420060b0400c118000392080141b420094001200f5410482e4102c1c803c81c013015403030003e82030104429009640c06401d034108642c0040d911201e083c0781c0703100d1b48114410941f07062b69001c01a41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 260994973 1250 260993723 260993731
    0x40c090308030123010224310203190305160c0509090a0201030b01110303010302060d0e10150f06120c02030f0703081806061503090109061e06050f0d0b0a1103 70
    0x700f01440c4060006112a404101d40a030301d06540201007c0042010074400c490754a8007210026081c41c0d0700e01c02c4181e64500001c1040003a140142040c1c80090350000c40c00d41002e00841c12150210702200001100244009000700050b00511658281d4108c00810240c1140303d1150b0020007a1900089500003104403100c01d00359205544500a65801d803240c0e111900084c40c0107804080f410000550380e2006200c001d0041c00002200180c0d0032040d841002346003d01c8094404940300d0072080d4000e0301064504254174065050002103040d460f90790714003207919940391040034002000c454002041e4180440040d030100304480340100c152000103024883c400e8403407500508107801c840785006481070701c0b100b50340c2c08038040c0500c80d034070203500e60b481d0002d09160035501e560b00c002040c0036045807507006080c0b0741003081c20f004100b6482521b102c9400699000c0100700c3d5500700b0440131012403903909400944c081d4011000c60a0f42650507071042c468800800c8441c10507007901f8003540111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 260996223 1250 260994973 260994989
    0x6010816140a150f11031e0d0b04110a09060207060905060d0e070b13090b0f0d030309020315040b0f0c040b09030a151d0303040c140111070b19030603050c040c0903080301 75
    0x401c01c41203094005c00e50820480000d0700540c1454000c0c0c54403494561440006110701001003400409001507800040e05001e000c0d200b80140b803107040761400f140d00071444900106160700b50128401c0c0c030000d0940100c07800c80e03032404001440d003410301502d41d01c2840d0b860707406900c540e08509403500410124004050b08031810340e5641d000b003072145221200340c00200501cac0c00c103440000c00d5a5801c5030b4030503030042100e084880c5071302c614007980100a1103800a4160103204e042c4509008a0a121842540079002c820b6940d0f44000c10503c568404985002d07100909110902c1444030a5018002c2e00b02c002e41111810390040c2c48100070300c10300c66580503d907a104d2840e0031006003826429440e0300d0300707a40210300358101030f540d41c070041800780191060700314038444500050b80308a5200c03404800000a45042c581c5404542d0603a50012040c440208000800c480045109100f084105c90b04100900b0301c05117200704200107001c0b04648042044194180840841c503803100540c000c105007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 260997473 1250 260996223 260996237
    0x120105070e180f0403050f040f060c020a0e04030c0b090322080c0a030312020d0b18010f050a030507150e0a080109020f040207020d060c02010e07090501050306010816140a15 76
    0x300700000b80c1c02c03a039401c000702180e400a0100300716800c3e407055006581420140c2e02d03418035540141c41d5003c0c903400310f80e40c2c030017081300013404d10b0300000c0ca0340d2002d00944800c18034a482c2c08024412400584001717001441620100d0007180e5881e51031034018804605a80c6000100b540c0000e01d1038120003610391861580c3d03c1000300c0c80c020015842e9080d010750b0300031492440c3d5180500040d02100c210350344180c0001d81c668120006078402200b103880102241d43e45d105000d09a41004002d0064000b1001048030202d0180342000c0c0b203208481d030100040c0310103410b06650300c10440341040c2c8a41484007003800c2c80c8280d610740d10b901001c0c0047e2070000401f0030450041101c0744850174115400b641c810056100907071030344a00004515000500429541586001217004005200d00c801543c0245070000c81c28003082d8200070b0407075808500b141d00f145d0701c5068443c0c4070030a460b86141500345c0e00004000c00860038a52810348907004013090207290b0742e01010051903a84806d210001100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 260998723 1250 260997473 260997497
    0x10b030402030303040f0311011409011b08040609020112061205010605420307050705120910110a06181104050c0415020f10020d0c1806030f0603020d11030f03030f1512010507 77
    0x401d1142e44400c1c0202100b43e02c00b421282400b405806001e84090030390ca460300e1041c0b003035902400c292802da04440c141007092903070300d4054003800860f9100c100c566509109000070280b07016a0100d000905020041c1c008110b484980c40745003075054001e9001601054000f10f0b0100300902551103266181c4401da61080b031441c0c6030703040210400d1614504803044c491410307075880b565240c0d50301522034205100c20707035400c103001b900d8079400580c028030807810140140e620310302e00d041751461988542c480c0310304c2c01d210720208020b0710004c8904254640c4140010004441c000c10082040c00079801603500d040b180c00c080b00d00380a81c1c0e0b442c241c3d110390001000031041240c0e00c503005644419141c0601034640310000b03006018094443c4600f0140c4410051003c1c0303070707650301c254019079008140001f48407851a219a814440c100b80c030b4841c3c020318030a400308107008400c80380f0910708009404410758560404107907849003403800d281c104540c800700c640100000d102d01e601484890701d0700300030a59 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 260999973 1250 260998723 260998741
    0x30903070602010e07061d040c02010c030b04060e0402062109070510020f0607080a0f0f0c08010e13030c0609080304060b100504030c05101103071208010b030402030303040f03110114 80
    0x329076840341e800c580c900201608400d0010541900340c854034034200c0390034101307105c4112214040e0101640c0c80740c5400b42c54211030350151f001c10002200341d1001c1c41100a80300401c021200300b40b05941000100c8030004006141420080802e07444050f503a4001009610f840c0c0c01114044480000f1540b29038006c4c0800c0c544104611003055281c40140000221000300365112800601064140141000403c0d503c40c51900511524035032118104080d0403624100405401d45c1c4580c1c2002c140b03032000109852800d21000d9101d00f022a038898080859940c0845069100e0081500d80c0c0d40c1c2c0318600b4000440d000011405030b80a0500401c0e005404010018582d144d54841002c1c44810001040040d5610056404584045071214150103a5020503281d05a010703840540c02c2c000044d200c020050200f083c0b50340320340d203030b600d0345502da13201c0700413a6140c44151406581a401400000c00040c00d94241d240d48034420710b0401e061641e9415400d003580c1681d5200603036030820310100010340d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 261001223 1250 260999973 260999983
    0x50403050601231207080d1e0906020a030e0d081602040b010305161b020a060f0315050d020424080304060215070f0c081e030601021605063405030903 66
    0x80350009003e4141c040d501d0090ba890844022618007071511407008200c0c211081c0a030000034001501601c90820f0300b20002445660300900018601581d01c0008500e10300ca0200d0382c0c02c0e24055001040c0c0081d0f00d0305e0584046502070841c640c00001ca07401d210004541e500580801800202c9000f4074468610401c0103964004010a041600d00f1041040c200400408070015400c2414090041003401c5d9041400c00706c100000703500a08a10130006807650300c164071a0b003000716590f0402140410500640c041c0202d44140340d0701c5141010100c0c090302e807503802100c9601c40511f104002910300024080303601c0041e031140701039800c0814100000c54060125051441c3c05240b100c034a440c041c800901420440c0480008024103100c0131030400c9075034011241c0200c211086225803040e500f95151a40d48207c0d001801401034907031060755003403412810410703650001c01e200c1c20013400e0001c00e417001141c0000100304a0145000c0c0c9011010292120750705400f940245644141c0981454541 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 261002473 1250 261001223 261001229
    0x804082b0b0102101512050a0b0c0310120c0b030a020702130c0f05041a0a110f07140102032701020c0409082208060c070201030b030d02071e0f030f050102120403050403050601 77
    0x2d54148030365080c3c0e1aa501145030140c482c00c050048010341b440c01c0451510400070300003040c4801540c280041070f41150007035441f420507034007882d803810385656030081340c1001000f00070b18009034007209000818801000d0741d0b01c08040c0c0001820a54141c002525920003a04400d14560381c0740803400a16912140140d20781d851410440d02e890f00d0031301c460003041c3c240003030950322140c00b14002e91b40d5032141c501891206210421600e0407000ea0030750603202c0c2c443d441203401110076030649249079400072065403890b0100d42d01c1e121200d2103408488025080e041c0281e4114052012a0300786540d8900c100050180955400c54076015028a840046252550b88442c002004003080090000014a00d64081e0020b11100e860f6001840141c01034039140440c0da515001da01d0003507400c02c0c0d00250a0781160641c094114031004100c0b2401003804043c01118909500140107002048011001111682c07242c8001032601044601021000754140c40440000d040080c040040c81400c10405006d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 261003723 1250 261002473 261002503
    0x2805090f0102041a0703050912030903150c032403010e070801050717042004020f180103020c070512070803040807030c0618170a02040c02010b040f06060804082b0b0102 74
    0xd441d0802d80130071815490303840c035800040000a95041014420019100202d1020300711079001009000512b440c3c8c2c10280d101406403207510b607082c8140011104490045801c10680361a545500b103802d50315400d1b1042040308918100080f8000c1d4400b48200d140b601013410150140ba4103058640707003500c1c800b40c61001000600e460101000c9444d403822600315074000780b58030402c0001361242900d0002190000c0d0300610210b250800524100020a07141d0481d10141050b007040c540150102d0203401d00d507800c2ca9001840a20171810040640f184605031401102c44c00f580d600c1e4414616402908a00320981000104004000c8840303c4100a00303054109048004e560079080c40340028244221181c07501c1d90010000141e800f40030034030f2100d8020300184270150358110003074041c0c035000720480c3c0101d1405101e03801710f50692280034240c500654079804682c841d502c540c907250b0807410510704160403840031260b494400420202d008090341e180420b40d682100006403c1841d82d01280b18 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 261004973 1250 261003723 261003727
    0x6160201093f05070618081c0216030b0114150301030302160b0301060f050d021303030f11030c0c0f120d0806040c020118081803060a0624080705032805090f0102 71
    0x8002440890f0040640c0c0703840c1b800e6028545044000b910f01030b1280d0145285001d942246651000c0030301d0640c0c1b20050a40854282a0301480c2c08001e281480c0700152038000514014041035030380c1c580f40200c9080c002d04042d1841c070700c501e005440d40c0c400e03402140940d0015050b0091260b4400c40c07100204482d05106007076616120018220007035000c2d001081100000c2c00342ca141c5003950564180700010440044415200e14014042c2171910f012a00442d1a0030444a6045c00000444003040c200001618a20f907a11f01402303644d4030410f284a6219510b83f00321070b40c4910400031800d00c91030b65034407901c403401c000342400121401000c43d0b60459040c405a407907081d00000000c0811580650341a544042143d01c3d4001c4401d04824641c0c5402244140010000e1a03000071059900c100344e03511560000308a8035000c40c0180e054038001ca882c00000604503030196014660225030100408070203121500703d07481004424001401d184e58810074840400e00030044600119001c4000314 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 261006223 1250 261004973 261005099
    0x90903090a06050f19170a05180a17070f02101d0108151315090213090501050918010f09050a2001120203040507082e0207020616020109 60
    0x40d443e01c58000b11120450300140c0d0101506d10a21008502c0104055a0075881c1041c07102003019000030b680d00030941c1d55008001800b0013000c03540c082d0707203940044104c1500f4001a00e44040c0d030440d0400b500c000051620050151721181481c0c2080000d56507916058800c125141d00b00444024210341004046010040f00c03220780c04141c15541804c40b914610f40c03045240c49800752088008290502000c05c800150390300c2c60f45c01030214443c008821025003501d0b000c040084400911076158071540f51008685600d842042801d0301c11380c1d030400410755159400180042d07401800c8201c605501c0110a0000d01c0000b03502e01c1e0300c02c498095080b880b0050400020005a002d1154512a95000021808101080040c00c00510889007a190107030780c100c61150b2041114540386083c0380826244261080341231003102c058980c000c1400781040e07880329a400441041c000b04a05002c14440302241c02c510710310070388200078082413552040c030b04145044401d1480310003850f000c10b04400005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 261007473 1250 261006223 261006247
    0x5060112021e122d0307080a140f190e03070f2c01030807170306150706091b05030d0903080d24150912120e0d02090903090a0605 57
    0x219030800440b9805140340c1c81400001d4056007844900c0c200601c81c0540855040f40c03440c0304828401104003040980e0f64055019076201e02c500e810041c1002e104000c2c24179001e01900d89c00c81900c011600c16400c05080744e508404990041911705504130411311100300c215480038181c2001d900c20345c040c0041920b000401401c2c0100d50180d062254020500b080a03c0c0650140d0351486c0c3d00e505105095503580e080c40c0565600481013903824051b201c0d400c0030500e51060880e4091030020f0010b1a40c41b092502683c40c5800c40241120b003c0d444034100d60114001603082000c44404043c0b801b0700511300400c251400d03861200f06020310407803507020008540c065007038414440f840c034000300d004c0d60500000740501c40b5100c440e072030704c0300c9210002c2142c1c840c100701000400040d4441424940d140d0200d9030788042e00110080c43e0481aa04802c00c0c14403910128501700310141441d14614070036030024003c0034045a04860540c00810651118a001d6241e400102500c0c245907281403030a842d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 261008723 1250 261007473 261007489
    0xf0e0a14070302160204020d050a0e0f0627011401080c040902060706020306060c0a0807060c09150f09180b030601090c14070c030f12030b0603130b0619120506011202 73
    0x80310040c03503400b00d00b0310f11920b00c0c214291113072540100115600c1e800040c001009040c1600c5c0111258600300c40c03141103600028801c0500a80c050080281d607032020001c8203444800c0c42ca4081e078040c0054403200515090081218a035405560102e40e581402d0a00e40740500c0398501500c41d901301f4008c2c0c00545c81300c4045942030f541103940541d032075580501207110b510803402060890301c203101c0361009001e5040f000d048007910a600903c42c00c0c50103e000c0340d8003201b41c000c4100700c2c0780a55002c11b042e4050403072a1252401818516850f80e0b507404141c45540c05a01c0218981d9100c02c50703502280740500240e0301400c943c0400704002000084001c2c1000090400303e528200001030b050148008403a02100451b40121844020015443c08140d03a82c4040e21101c086410501c4400c4580b4014064030b124820000c4070040d0f002842c0c40d5039520046c090030154005d80c211038072600202000700004040c1041241032040c07410185885885c0404c164040030185684900c01e800580c1c0f4401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 261009973 1250 261008723 261008731
    0xf0114090909030c03030106090f050f06040608070e120d030f021206012625030e0c0d0303090f050a0c06030903120504151419020c0c1005040308040f0e0a14 69
    0x10000c0c05562082e00c01840e41c46161382500b22888040000203503113500c83c03549000d55440d03c0c0e031000e480d81c4d0b4031300f4019441000e011455002c1c000303000c01c4c807030240706126107030344807803607280050103c0c0752800440d000c240190591199500641240c400c0b054060141e20141140c10500710f25040010401c0303100050044c2a5034100201000301418100d528804284112001003401c80d940c00c012001000540d0740a000400b034910040300755803030a009109800d80041c4240241501c106c000c403c101030811008803c60074965521011408205030243d60703540c10340710340010880010141019040302da15540004109414105c441c8000f81d400b00c64204114080c000c00301781510350740b07006411450f2803000c0e91860f03403400302491050201a2074050180c25840c0c1c000c280b241c541031050069204440b203030810303944548102401c40c1000190888400705031329045041684990340d56036180d101c0e50020303160085011081c003030312185142807504203000d40000c100048082000d0420804010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 261011223 1250 261009973 261009979
    0xf03090a03140f010f0c09050306040c03060203090a0503030f06010809120409020f0c030d090c0807140f1f030507170106020a11060904180b06040612060e0102071a04020f011409 78
    0xa19000603403142006403c680c0c912010092040d0b80050004400a05000301c0c0d4000194004c0c02c009028180032480c540038980000464450504507225000603601c0034298180341d10400106130042041072010b140111030130b010160160a10400041440f60050700081c05608a201980400074552080707800720341464501584403186241d9800540c000e111500392180030000310385c2011420f991205640c60300c5200b464280b1a11225441e40d80c510a00400030109941c81070b202446c6000c12521400d028000c144021025150960000c82e040d15981a8046603e03241400350080c2c001c1481480001007242030f80c55907241c81c2000750360f0b61010901074000c4192101514494a64900300c80ba80d460180047c0142c400c1d1f05000341c0404c910305010340f084c4e0081d9002c100113241a0040348100c500075510a0b58840c400d4591000801960041c044a076500300180ca000612030480b00390ae110914071179165514140c01400700c1c26405610490420410101c4584205207420030750350300346c00030703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 261012473 1250 261011223 261011243
    0x1150518031005010308090108180703080f04080118060c02011a010c02030c03190b130c05090a0b090c0a020609013614060907120302060105010c0f060603080a020f03090a03 76
    0x1401190910300b0407845403402600300400402840f10000040402040a9a0340390042da00c4102008818015030b21600c4107800a031410008a02000098034456144110591034150749aa000382141c0340041714551710309200f0004020b0009a01c54100003460500081c05509042c0184c4003d44168114803410b00200d01565004d548007008504003d40019040f00c804404810300c415410031a000300b2500e0034100c034006030b000302070903500500503507028000a4a03503003050200b01800c0002840490807039611607403a5500d51314405018000c4110385115030341c404c59104000e0a0450040080e59160b04121107054191908820116080303205403201403085180d00c44a08059083c403000307040310f070344401c2d10300250f0000f2503d0341c0640d80d40ca0880d52540e51f40c0b004d45482c4600648064090380000c0010840d550062078412100c504c202d20f491640f0000d541c03150b00300d5035682c101756140707200031074010b811a80402c068810300c1c0e2004002e50030003022100003100135159000c02040d0402d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 261013723 1250 261012473 261012517
    0xd022a0c0f0112140a0213050f0604060c1523010509040c090b040204230102060106020f0318010c06021c0b12060408070206120a0b0109060f050307030c110f03070b011505 75
    0x680c000c0c2a144e41600f5101a14148680b2140281d000ba10390081d049422150000e0146031030100a081064050501400e180c54410180e40c010f00320502518910440240b007240b07074502d442140120079103445030300a044510340c0c0b400b49201c070507001316009500a04c14040810040f800d61400c0307491248000c60303006100300129010340035960008c560900c110301c00c0b00d20000400c229004c4002c003a401c90b8010f82c4d980e00100da80b0311001d8004a00c0f50810000140001025120b01e4151754060400b107425269030303543e020407a4810701d1072650030402c5410301d03c4103420502035803100d00402ca03401801e104101114940b6030401410041c0b0400d03000840300d0454032440b040d203010044616078500f4600d008003880d0007078500d1080e4540050043c800201c1c1032805603403048200c08040d0768060031903561103820303001041e2003d0f0040030300402801403000c685080040122412800c3d0107161140034600c3d182a0151040e000000302802840c1042c0750a640302068600001040c807003039880d01c1e4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 261014973 1250 261013723 261013757
    0xa051e090d0305030a0e030f0f130b0a020615031b121509060f010509070f0804110406090f0e071d0c040e040b04031701030c0501050904020d022a0c0f01 67
    0x10510312400d4118a8180c115018940c01a02a6100c0d9464101c00e102c400601c00741240c4900c41d031040d401c40c518050080d05203503982e02c0e000d000640b190350400084240c0f41c0384c1c2285982c010800c01c0c0016030042c1d0800094820341c4c1d1148420340303819001040c0319000f805c0840d09040c3e0820b0801c4c01096064064101d40d241006202d42141c0d6404e9400d10a080401c280740e1285400c03505403207484c40c203600006139410a8251300f1b1040805582d41001054024811200c414000d0310950b0140d10145071121380c0c1c1d441c2d100d8070004160321400028403142e001003400544d45a000a84501c0c0c0000c10204414080c000c51618000d186681c03440c0155600c100e00301150049420105c0700100e80c200700401c1080040c502030117903010351181144c003031442c080b11412040901004040c011b503c8003c00c51540144050031000d00014400b40c184190502a00c0817038004c50f2400b4800c2040ba500000800079105c082c0c1c00d076500840160900460300c00c0480c0000c0d07020356180f4108020b840e84040c00f10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 261016223 1250 261014973 261014977
    0xd0c050c0d1b08151006080606181206010510020715050f0c070b0a080a02091318020303031303080718050904110603280e1f15060801030303050c0a051e 67
    0x74080c5902c0c0d29500751a02d00c8a43da0f503030300244110507040c144011a0f4004d240000000c12a80241d440c03607455501c201c02c1c407184ea009130104030013844404480c0020303a507a404c0d094000100b80d0b0000c000c150316100401901c40c01858020382590031920b4244070000d104020542020036070304016580f0108081d00016503c5150300e0b04c6041c0c081c03440080340452105004109282c00d5554804450303d0f661400401c178800c0440040d0701c102c80301d0742000c42804070f8200000800700c02c02003d4844229030007080c21035208445075940c8000d03180036181019000f50805420804c94502011150401c041a81302d06002d07004241c03050744540c0c0010f0401c00041e0605880007000b5004a0f1a8101541003170300825400032240c80c0d80a1018004c0c0208040740700781800c5540010051a06c85260320180803100d01a50000342d6a035100c16120550303c4048605400500300380d42c030300c2202c0d03145040c001c00325070003c0c2000c4180e540c100401050746502c00191014a5400c1c4144148004c10750f008002c14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 261017473 1250 261016223 261016253
    0x1a060405033705030a08010603180b0601030f02040e04231506030304030602070605191a0d38090319050325050a030e210d110301030803090d0c050c0d 66
    0x2003010612031900f00400880078084403511915802d009980395103080d016980a004001d041e00041003880b00031a520b15060303508410181400910400328900034010f0742c1c01038104101001040060000300007441c40e0087e828039050681004a0040c03130013050321064041c492503002089100805c0a540d81030044400865100c10700310350791129480c0010103010110b451040d031142480300c843d0b801c00b10303002e83d403001449001e001410311080350810440307103200340c010744448245804107c2030150b00d213242d58420031031a08501d41468070034511800701d800240302c2d0803190810b214150030203203040d80d00c40301190241801500d81e0b440090711000311070185201c0d54510315071150070602c10b80120050a802081d56400d1000000c1148000e66032190001003008011001d06901d03c012002d1001c0c000e01d408031030002c0341080f078020f002d561540081c0c0040e1821140001404250b4608025448112040342094000442117490359500e03041100b000754010702014000308104000844902c40c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 261018723 1250 261017473 261017563
    0x4150b03060f0703140702210405040903030608100905070302101e081605040f0506090d05010c03050f06090601080105010f0c17070b18100908040510031a06040503 72
    0x3262901d010300742410a8140c643c44042440d009504c082d84a44a00951041c56035400601050442c9011020b000340c9540c402c1501540620000c5426030350b9000741a1070f203010f5500401e140341404107050030480c903003104c3c04100c2d1400ca0100001900403c10004480d0100d5416108a00441c4155030100c000d011030707401150503111202d030f055000070b21f02d40210110002950b600c1c602000680390b500c00c0380201c04202103140000c108518005d8018240b804014000c5107842e10181d54103420366900f0750740d40c0003003030700e880400c0010b03807611141700d40c011000c4815a0b035170b05116001810001040c043e542c10490400c14103007440307000780e500307a154075031100002103001d40f450510500c9800151080b00d4100000e00407d00d0303081e000c0071440001b0160b801a20710081000c8840005281da4502114920402d0100081c556104c4d08014000704581d1004500055800d2840c485034180d00b603e64480c100601c810301191714001402c07082d2000c0c550f64001501910007003000d034405c001c601540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 261019973 1250 261018723 261018733
    0x20d0207060e010501060e03030a080a1a09070503150a0e06100311070809100207030b011202030106030b09030a0f0203040f090b1c050a030f080f04060f060e0106020c030c1804150b03 80
    0x1030b00c020154070240c102c5400740c1d1503940d009801c204264480c07140c0310b42900028506e10100704503110365405070312126400c030240c1e14071040100101d144103004407840e0000c00d8000c01041300706005200e9071a0741d444c049400d00600c9040420380048060302401603070080b1164038007a51114029445140581d062410b00c1340c403001ca174542500f096014601c81e9010345030202000440e030b400010744400350b9900c000341c00c12680c01c00002d540034810074202030340c1c036640399040000818007254050380180741d00c1010b595100e881c0346015242200c542201d03406c40d441048104151211010100180c4038041d101144032003012000601032a65001e003590b101204020910421500090908040c0e10031307250b00d07001c0e40c86000d0a0f21280411114101c05540f1040050001800e680c00418494800c0d04c0000300c8035115061702000c01d109170044030140c2e00190681d0110b00d010040848801022141036003000d00c0710141400c0918050401010011030854012050780c03a40c11040d0f5900018040311 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 261021223 1250 261019973 261019991
    0x30305090f1c020c06070b0606030a090204150503060601020a051f021e040e010f122904030503060a0905060a09090c09020708030a0608010c0f051e12100b030106020c04020d020706 79
    0x103806000d0510b01ca00240c4a400ba03c0f03512400c000b42590400c1d900b141045855030303141400c0c4825940020521f40d55541c0c0d829102005a40790710a1000c0c1d000c500f070088100d1070900090604d4510050a0241507500030100d0200081c80040c1c0f44407404070b1442d00041601c4241054000f074018010184050030500100385080321140000d00100e030503110b4100310b41d9903108480f400c44032041c09004085620701c1140301c0400c20341400300020b8040c003080c10800030200c400314503000e201603408400203040001440000d01e80350829401a188800c400c210b0740c102100050301c06403480c40b900c086c290b290f8403000700b8800304079a0b2000401d009074040d552007000f0303d42070010768030845000d80301e02e00c0c028001c140101c0520404031000c440340c4440d0500000c440d0240c0d000c0d005100100c0b9600040d40200d000b406050000d050903201c80300c920865800c10003071800d8161141d4200301c1483d842400100440c1d940060f80342908a0107650040e0b54004c2c280307000c4042c1c402ea01b8090405400c00d49070b4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 261022473 1250 261021223 261021253
    0x31a060414041d0601060807110a0b04020f010509030a0b0a090b0a0615081905040206130909122d030b060414010201060803031e10030501090309090501061407030305090f 75
    0x71580c49802c8804200460480e15003200311000c03044040b0441d48800c0040c01981d006140d05a000001410b20620b00e040003009646008002a0100d4071000f000091001310309104000b020295001d00b002400d0880726000303e581d4071800390002c0c00705003000d0f01043c803c400b41d902c160310868001c890303c0e400c0d00d059264a0041c00c0705109080350a02440207130681e0074440c002d01405213490500c26080c0040303100756100a0080036009990181c81048580303c04165154074600806102d0170108450341d036814a29102c1035214002000c3c004102440200c0300140d00c21003d443d055407800d00c0240c103c005045004080103103005411110005003c5a50491100e5a003942e520903802445015103450049841e4042900c0d6901d03c07841040c2c0043d405040d074124103500401058001c802c141d540d80f105401d54030ac6e1202900450704054092200c030f0494010f150140c109401c0604c8100341d02d000a800601c14040d016080655407008103c08081c01c1c0080c880080319101211018204102a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 261023723 1250 261022473 261022499
    0xb060f282001150b0901030e03030106030b0a050f0612040609020301060611010c020c012c0402040f030b0702030f1b15160f1e030c0c080d0f0c081501031a0604 70
    0x6400c00c401c0c900741c04006068140039412440052100c3d4541061800c2c00258058010402103030605d034660420940b081c4c81000511300030101750b500407030106d40d800c007484145c0640380c100340d024503800801e801164a8183c2180c82d21121200700ca540744c1d94a00f881c7c00101104003009501d9401d10800040191348075119a11800b0500002c101c44802003406903583d20103464014003148411000d1303201e01c0759a2403088200c12291510280c20020100010101e9010350800300281100030700902c01d000030150b0b0709902440d9800110300d4255400303134000300390240180303240c1c00c08403110a010030b200c0d081c000e504071552901010107441c01c1c00d03610000e01e2901811060005581960280c40007407082ca4400c01c00c3d0980b0f00300e404020039111341140a015020b482d1420b0141c00700c40080040c9500e40203010703107400c208000500c0c071680d030000000e540390284403204001722130081c0803a000c0c2c0d5540300c614005003403c000400720428504155160304105100b0341c0544c0200380010520941d0314 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 261024973 1250 261023723 261023747
    0x50309010e03010207050a02100c0b010b0403110303040612020f1b011e0908040302041d06040305071208060105030609070e10080103060c0f1d03030d1a03100b060f28 73
    0x98007040600201c007854200d02540e28003421030f51110389040b0260030310540100c0700c2805890100524400313620750940d895402c5e40008100d10001400700180141c05080d801520811409180741c1880c05600410304182d10040540080d0300061130483d00b0f004a0445a0642c1d060160f00d1540700d5070b81e44a4020704006112242c4c0d180ca0006240380030311240300394000c1e01d600c90140303400c0905680900c4020802800e030701100040361641d07080d48440410070b40d48030304e103e0340c2e54a59440482c50071564030511850040309211081042c00002d80e001400d9a41c0040b007592140e811b44d48883d000c0b41d408828a081c2034005640c840101080c5a000c9242c030b0580e400780f0424072031440b1040c0e00710340714003195051ba00040c02c3e0b09030319000680c2115990080030780c01000c030b034200641100404102d6902810310880c0c05e40c204028042c505007031018003201c0310f242c03d04021180403000411098444d0440750707a0800000036001310b41c02850355985030701e40d510752031300310048801180c043e080c88901c00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 261026223 1250 261024973 261024977
    0x6031e0105040b060604121e0f210503010506030103060902010c12110f1506010c060e03030c0c010b040e0d05090301060e0907230a140105070605040c06110c090c07080409060305030901 81
    0x740150401000312400c807410540104810b12031070700e2341e030303904800d089003603100c0c070840c400c45c0010034913600400200e14000e9183c482d1410100311100504880f042c141c0c3c1c203110043c130041040d0f03984c10303041ea411650402d00200d68041c00c1d200403075801e0083c3d8030080015803d4a03000d2192580328031600342804101080341c540504c0542c40b10f0b51019280004c0c50075401c1c000000d03406511408291080a100d200e01055071024000303c2c0d420750300f0031150141c082c20f0219031f001c00c0c0c0030b09000d46042520155000c1000f050368054003134032240d5508060091000c0001c2c056076540782540483d00a212a645010b40b5040c000881078654501d031054005403082d0488040d0031000d1350481484d00e510003052820712030300e444035602034140c6e2300e90388078180501844144013180750750107814480c0317101e4202c0e911400c0c10705074050149103100d540b00690b94010540b0b9541380c0c40780141141c000e200d0075001070721000c1d94901180da03403084c2d1700b03c11171140c1400e000008204001001d0241000e0036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 261027473 1250 261026223 261026243
    0x10b090310020306151b0d020a110405060112052e030201230327061003051209090a0f020c070902040f060314060d05010f061e08070e070806031e010504 67
    0x46281c26003a80003d840300c81e400184403500a4a40400e8002031080e00c0140600400700c0340b000760b00c542421a90404c035000340e0812030343c0608101d0003400030400c2c820121030405c81410a840001d001441e200c200e40403242c1c3e0741e000f00d082030800c0c0d07400283c03038424044000104201c01802d026200c400d8481280459022032810030800b0f01d440c404070071038803a02080340c1160f0381c001044141c2d00b8080d1081920b110310310b0078019000c4040c03143e18030448a9485085c0000e1862900501d03140d2a5415070030301940911000d070617036072400030481e00581340c010301141d0b6040514030b20009111300740d9041c00a2007820000500d1602c02d8008c5d00844801e95884401660b403100d080d41500c6100c032015110f80e407414001a1700e494002c580102e014007610000450b100e207521882c1c00c4460316040303180c0101d00104c002c0901c01d191070400024007004809000b08900e8081d01104800d0040d220070148907a40001803229201000070400e1a0080c1034080202d5440c3c1d61070a0080c40c0649050b240341e180 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 261028723 1250 261027473 261027493
    0x60604272406150c0f080d0b03070e09032703060f070e040912052b0b120c060327010603060212131203022101030809090f010f050f0301020c06010b0903 67
    0x4580308000849496203c0340e900061411411995032400141c100e0740c2040b054000c0d0007080702c5002908140640c2d000000d1003101a1040502c2c100666014804e910300c0201000308581e0080b0a0710a5035850000343c41d244140380103040c003a04086450725406115203410400c803188005d0b076940c020305072a220a08c1564144051000303035203c00300080e01d8164002c45c111135580c41913004180300c44c845404020f160301c0e0760812081600944021030400b58444420405910300160142d043d1070841000b80034183d180d8010038518000203002e01500c16a902540b0f4500303016007040d0000141071802000015100e1030081c0081d0004071081002c04070f41000107028060740288100c80d10340040307107441e00d1103500c0303001c0b00a5840780180001c540101c01848403c4030158207114081c42c816154940c954110b10140035448070024081c10b4403506080040001203088140b2000380c0b00b09544c090300b07100d14600440e0191007601240030491203400000580410b081c405403140d003038114152100b00300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 261029973 1250 261028723 261028793
    0x50f0f0a03060e0a2603010e09190309090c020c09040605060d080a030c140901091806121505060114030a05130f1202060604060305071202031207060203070e060a0206060427 76
    0x42103100010006c00c0103100c0a400b4040c0c1941c4407001e02c049a0b9107140b0f1111203655109414003c50100344d60000034029a000d6000380011400c81d840100b820000031000110318001c041e0014103180c1c3da403c003090182c0c139821780c8024100d070040500c03592070704000d80003001001e1000983c40000d50080c0f2032000742d032109086034108a816034403414100e050040c01c40c003552400c5000e20302160b0f105400202d56141c0491640350500514440344090b001c0347c050307016554020900c904005920746e15100b03060028058980005180a001801d82d4410100e038400d58040100038100c0c400c2120800d003004003074110242c46400399400d50f40340d51558000c0c04143c540707900000b059604030101c1071200240c0c0304501c14070320780000d01302ea002150500d400c0e0010752102c3d0090792203640010070000140e401c00a00005440195a005c1c46c01c05240b600035110344010b40f03920710941c0c07901c0780c0d0b40c61080c0d8041204450102120204292402403030b1008500490380702500340060508007640d05a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 261031223 1250 261029973 261030023
    0x203010501050d0f24090e06130b040c030b161106060616020f04060608250f0804060b0916030f09050c090c0f180415050f0f0a03060e0a 60
    0x29810b0315418104852103080101414600d44041c0314540c0d41c03465951340f003140c00d80912030a40445410404903050128040948880611130000b5500010130b018080c01c920251014640e00580c905065427541e1420b001540c8241d40003910505000007880030f0148030030f2400c038600b2800d03120309040c402d211071341e192640403c890403a4000000e000d04441740459a0b0307031402c9984001e0080811199840000f01191441c5d00810700141c4404108440342603803060f40541104114800000e0b100241e070010510040c0111400400c80124003041c10401150031825034079800a00004452406011020310f10300d81c1034a8600003402c0c0780851401002610400c1540340d0450003600c8225104410300005441c0901030510b603082c01c010824511880c0009000407010680056222076800d608100070b6403026115440080001c480c10001d9a445094680d011001500c1c02415102176000198200c2402e910141c1814103040104007210408201c120f071480c881c04c0c04030b01081c00052030f07803102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 261032473 1250 261031223 261031229
    0x51c0b071b0c42030e01020a030b0102070803070c031211120c070f030807020402030612100c2607180906080a0204110712030519180b090d020307080d0e0a0c0810020301 74
    0x10080c000e049100342189090903020f071102820041070219130810300070300b2a403003e880040006d54031040c0900540c2c2c140402c07001401000000c40c18512941c484050481451200614840c039005c4601c16050080800c03114240c0c0d9030060b500380c810141d41402c100c3d40110342c840c078507014040e40410100c49000d0408180c98004d51080e05040181c1d007444001d603c050140d5512070483d03100008900400c102c801c10300f5035003000202c0c801610030005044d04100804007941140100c03009400388440541c002c0d44001c192415100c3d0000059604880030300d181c111041950501e41e010807000b40c0061940e590b03034400d8408105200010003c40c500c0c0c0124100201803003a42a0140c42a9209030001600f0000c2c405030443c0346038290b5184802c42e03c0280400d61042d50409a5a041c0409610034550140c0900d01900d6070302c9040038020f40364400c40304000d10207000402c0340420360140394015024103100c40c040712074003825030400845244440c450045684140126040464400d009884c12 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 261033723 1250 261032473 261032549
    0xa18090b060d0c050d0305040b1306230a0305070e040f051902040b0d0506041805150a020c0a0f050f03041e1d0601120b0a091401051c0b071b0c 63
    0x1c3c1608060030802c190000042c15820005c0601021801c0c0212000074205800002034512020745840406415803d81400d40c80e1283c0400b030a107118018118121803074156189000182541e80b0081550581f00d60010250041d00d040d09031240b6101da80e108600803600410380200600300030000d0010ba115901508100d4001804807100f00c000c41d810054010303500801c049058081c2484424428041031801c0d6400d9010340041e60190201540d0540c100d1200c04040d440e10103c0c07854155122100600200848003000b02e120a0102c1803110400b5030410005495840c1d54a205411381604820008000d500c0300c208002444040c000d048001f0012020b01508241d94640c0151050086000d070340101c01e0312440c004802d941d4003007284015085e4000c00040515030b50300b403440d4007207050b04a00d0040b40c90340303d444480004103641103003081d442000c501d80d0356160002104d86000c1341000406001c4c840c950501040b80d44032100094600102c25620400c0704030b42d45685624100b40d00d005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 261034973 1250 261033723 261033743
    0x12090606010f050a030603020310090605070e0303041203030e03041d070809120304110d12030608071409060a08010c023d0e0c09010e0103120c080a0e0a18090b060d 72
    0xe0b400b4020070150222180320f040005a00380d89801203800d00d51048480150660751340401410003c4901c03501c0e8006944c0d282c586041045200840d5403841503004001d20481c829000d1003c1600c65003114005024210540b07845555070100c0c628400300382c00380026186030712800140c01c1d40c81800d40600c00c400c564000c1070284404240c000c2e840c1e001510036901340718484a10720070342e202c142c9036034041c0f8450b0140b8218900307004801400c0f19040c1d003005010b600074640c2044040300c440821800b4081c203d0714541c19031644030000d18008002d43c4801c0f40c550a18041041c09500401c90754640c145000c0348241c9101102842d8450805208070010704060340118540c9103512940300d0706110810400b1034500c010b1010000d220360401b40d0048101c0da08036001401040340a920720042c104440c203045060303000c5c1c2e641d1400319000d0181004100010314000840c5684c940e42c12200900010280010441c1501540b1000d0409620241c0308082c203032011801e40d082c07102e03010b1201e036084401c00c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 261036223 1250 261034973 261034997
    0x60e06090723060a0f020618100f021201080102030a1109091801022104120306060504090207020303091201050405060f10050118051017100e0f2a1209060601 69
    0x3441c0c414100070b58180c0000102d103040c1080e02c1c0c503401000032484544521070310700c0301c0280003850700700000e03e11080703005511a2174011210002d07158401c3c4041d808081102c00c0102c1d40d92000303005083d0b5041460300f60800001312100d040d4021030150b01449824051340c0c03400341100100c6e20403010040c1d0020041000290310708000c4050582e4441d5210015240242c01000b0301b0740059040308044041c0d035500c042c04100401e0605051a144950174248046440c0c82d02c00380c031130f018030710491117401d4001921000310f40d028021280011001000c8810640b00900344074002c03d400c4804807038520440c008922052205030940b407060300301039850000f4078142801150307000c0c0301404440c16503d908201007030b1903030b551240420220480d03682c802c50040d16400750034140b0014006210942154400b0f0140e4100c40403410ba0020042c2172200003a19240403c020101401c81c074101c000d1280c01c41602d111001a0007489820424820903086807584000e054480800f070385c140b400300302990011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 261037473 1250 261036223 261036239
    0x11010e0907030c0c211b05060610050403120504030b0a0504020f0d02060903010e160b030105030709020f07020a030c1d09060a15031203090c0902090112020c010204090216060e060907 80
    0x1000ca5042c2e8503003004040304564804882408144614502004101c0305041c0e880c2e219006c01d410502030010b00468542d41d440740b17074540c400038040754015549034400c00511405001107900031a0300c601c8200942c420048024083d030403502040b5034940c0d00802141503629030f03002e01030080e80c0081682c0381d40d100b54000c011002481842c1280c10840c103201c509503aa40c00e10a1302c0f015001080509046500d041c89642d24900c642c2010f241c208081c801402152000903074072080c0e4143d03840041c7e6444100160baa05400b074014005d5100600300070100402c0071443c007150885411010715030020741c0f50703140741448140454900c1c0b0154050390024010035501c3d080201154010341300c03000490384948480034000b600000040109407100398610811100078600001004543c004604140300000003c0909088240b100a02c94001c103440c403a6400a60441d401003c4000086640c0c08640704d030503800209142043d1412864001107181d03502e00440c4052140e44d0540240007014100400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 261038723 1250 261037473 261037481
    0x30203040b010326030403231912060f0801020406021e0d050d020d0507020c03011d03030411060405120309030706030c0f08090c0a030f2604090c17090307050f030c030f0313050d05030411010e090703 87
    0xad91402c041e2120800550059480c4407a0007516800002580e0b8605002001c0d00d40b44d01c031840d003d40d540700b01044010745a000300d6040017141851408076610b100c1340080c10040e000340e07032450158a203081c00f8011580d030001401c2105602c06d6000303000290312510030381c0100744000f1090300b96800070070000f00005c5e10b01d80754940d401c0000340035a041070b44800106080c1c0c1c41500301b00c00303542c0c00041c410416280c2000428000d00e45403078148400d000b001c00c020854103201c4d848600744080d406c00f02e0a880403d1101c0381049102500310070050303a403420410440b0b81e01c154140d0b0060f626104010008841c48103219041a01744851403400d460315000390b000b81500781703a8000f001800c10344030214a205c10038440c01160b10000854030b4407a030742081c0d42018103410101406d80e004011210501402000b620076088030f0086c059201e43d151f500520310800303d0b040081c0307107015490038002d00d00d800c44040c41c00343d40100c8200c0402c00420300155860006405203507480907505000800d034901c00d400c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 261039973 1250 261038723 261038747
    0x709020708040806010f090b100f030b120f0d2604080c03120a140a0c1409030a0f1a09030313110d0b0406050115030203040b0103260304032319 63
    0x6a481c40e00707980e0760340c49090407002e1b00850440d06c010402042070701214007d42410000850f15030a0030860b5000240c08014007815101c24942c40b251100d001e9955103181416109500040d01d090780d803085041912002a084544003044030000c203c101d407100c00e00c070b10407201e5442c0c09000b91926035465048080c3c00080f82107005120030400b0000480304841d003240101081540800d241440a0404a04041c02050105580d20701740074410b409a0280440c0c0200e0a00b0030074079903c1000d040402d082a014031800742054007040160710812154401c42c51f881c0384c5110a41010340c440f04442c5443e44000d9444541030011428040c02107000e440c030590a0301001011421001883c0ea03d42d02142c00c121001e8580300d907541e00400c13885111400b001e61851092408525500d05655070020b2001c1c18000a071482011107001e0480d288000c0150b0b460900000c451600d91801e880d00410200e14a4858806c9545902c03039140e20006260650f1114102c06000e03003024880200c0860304811081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 261041223 1250 261039973 261039983
    0x30606091f0b07060c020f060406050c040504060e0f1012170c010c110706030b0105120c0403020616110a08030307030e0c0406060201020403022412070e0a0801140a050907090207 78
    0x7101c5a00203100c1d810340c004040041c4055212031441c00c2502c03c0300c01e94200c4d0015904410514a5000408610340c0e622550110000400e41c507080c1c0c269060f40500d411098000b842c2c09004140803903070280300c912403107000c03543d0291655116652040301d081d611407441c00341000100c88002030f0b000060b001c60f0401c0d00d60130900300401240241d080d00c40610024001c29142e03c0035800c041000d03c8924050400c81c18144114191000001c01500c10003c039035000803d900c001c514042c1c0b004088400440c0c00901161f10740000b8000c1a01c40303006510100c4060001404c00d01c130764101041d0b45022282038401640c11a0b0702c143e81500a03080e9007400791000d00403090421000da03124414030015142583c00142c0740d50940c8103101c0d8001c40d40c029034004016017001c1581c02100300007190a60030307490240071081d49030b4000c1602c0c01c0c3d800311466a40f10003581c2001c50344000540c1f1940c90315283c031480e0401030711040803620480c1d005854184640d003140d00305110b4a41e168004240c0390748a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 261042473 1250 261041223 261041251
    0x90b04091707050c0915040c3009230c03011e0c090305030a031a0d02030a02010f050d020403080c1b0603060d0201140a031d372316030203060609 64
    0x100d00080c081d10046440744001e030785d460040203550510380714044d234443c0380f41001c080b2030030380e048410b10080200d2000642c000c41000c8620340000f460b004495642da210074846d0103043c034072121400d0082e02140070306442c49041904009403405000d090750189400100c510a103001d0f0100720080c00c0484101c03070500480e04030000010718100300600710441d42e90b500040380000040c81c107a0fa0200d94128a210300210300240006d0390340820f0340b004c035560909020700034400e925015610b900581340b0000d1403910118000041c402c920000b425801400c5080d00d034480407403144c4044494454050341d81141050000420909011f01c03d01c46803401414509609000c1c0301c130b0800300b07500089400780066101c00380c1c0003140f10001d02c018520600f02d4040e041010b10354525542c00d04000490090000c0c03c151030b14107074040400f0703036410307030b80c00025401502a1801259040982c2d14100040f184a4805e00c40ca6419010b2042415a84c0c01805014581c80e100700f00207110101401f08040c51003a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 261043723 1250 261042473 261042493
    0x20d060803041a210c07120f09050301091122090c030b0916090f020d0509010603050105010b120a0c050c010f060f0b04050904080705030912071503111611031501090b0409170705 78
    0x1604000c7d02d401e18503902c140c5024294a00140b120900350b22690280e814010120000fa0020305a207900303450507075591000c3d0300e0910850381c0e08015652258030407454130a0441c107101c0041354040c2542e01855010b01540c450303a85c46a13440c88d808803c0110204a202d05004a25070b46d00250114101c0d2031025045c81e240c0c0c415141110ba0a989942c4269542c00301002041000c0c007409004001040085044c904040740086040e60020503000c040b0ba078440140c45160702640540d1003051440b0001c00210000c2803000000380720b640203c0180004003500000d11440d08c1c8111000d80350041d11842c00c645840d9030700855030b001860b04407114007003032100710702546481d4181c030340b180a00c80081c000d1501c0d000c082c150b48481d092014040506000704001800041da04a0740b841034100380c0c510384501c2d5410500030215441e0385140d8103010349a2000040303100460b1079030580d1401c510810a0090540802080b1030b401c050081940402e03441c201a000c0e1078601a000c000c2c003a80645421983c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 261044973 1250 261043723 261043733
    0x7020d231602240405130c1b060603080301032307080307060e030d090f030806030c010801170f0d120605060703020607180306110c011404170a03020d060803041a210c07 74
    0x501c001c02d4083e42101003410403241c0742600551403041c02c0c0440400540540410050004140002ca0319620000f000d800f41081280c0d8004002140c0103014561256100e29103525410710301140340d000b920a10303800d0001c49401091403003c448208006624003200c1d69505e001521001e01e4144480c04180485a28107c19000d40b082c000e100b500d007005e00440602c0c028000f080086c1441340254030110000b42142d07000010035054910381205e9a080038200b0066500c0d00c01002040c0c00c03e80100306d00e03c02c62a4201e0313042c40752131070310744000d00c01103403a2800d0282a0049902c043c0040c1d0081740031800c00c41c0078400704400d0410090b81c407906c283e01d80d11000203546040c884200c21001c00640c4141410b020320492545a58016144505080a4440c001c0b0350240740307801e19080e24000b4043e00440d010741e040b154246100d680501460359a0801c03a80c50b60000c1c07080b41c51071f0044d04c5035000c80500c3c0b00129904110444140c1e40030502481c0861501c0c0001001080036000800c502008030ba = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 261046223 1250 261044973 261045019
    0x110105010b0c0d0f0c1e120e030c060702130203060102030409060602061017070b1606090501052e092705010b0406150c0b060102011407020d231602 65
    0xa09216959580710400440c2d85014403600e40403042165a03051510001c0e4000701120050307030405040c889100701041041900301180c1d100510681b4400003a840843d00105c020740c880800f2010340b2240360610090204074070070250002e6001c140f820351840100f1290f4084c2d03030441c20610443e81026100c400c803c080313403100c0d0084030159001c0010081c0c0951598842d00c0a844040f0441580050342d2806903500c4040e801a00c0b2408070200340b0100c078106000f104600700d500300714248065900c90070624001c007015501d501c003c0c2076102000888414a4080d110005650b4440c0f80049180c840d0301e0006054503c0c983e0340c1c044400710201c1149840c0c00c5580400e03800307107000240380c40804c0100401c0380c0c0503505c400360011b45408140005500181d0003030096410003000e51960781c5101c0100e00601610030a16154000d183c24030940c20343c0000c4900e900c0c410394540c441c281d540754003002d05244042c2d1000c808000b08108070019042010706200c1814405000d086082c100c1501c3c400d520 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 261047473 1250 261046223 261046229
    0xe0609060a1b0c230112381f05070605060f061c0c020c030709050406020c0604030801030302060f042102120301420804110a06050702010f0906051911010501 69
    0x4600954003440300c0c5640713804251104043c2a10401e07469454030000c0c0040d090072001c400f0403961543c81055015261860720345030400d04030840c83c1e1038200750650961580380011070740034410071a401402c040e200d4600a699940a88071542080c8080d581d0202801000300410781000010782c010700d6984600002e40407a02420600328600e4500031031440480740f50144030000c650110014000e981c4010680c10700303981c4610790100311030740e5604080000c0e1242c64400f82c0a44588002c1000b81640300c4d1116040e00d20075404e40e02d258031109055165604151005003514240c98281d400c0844041101c0340c40d1055401903074180c0322071009442840c4c109034004c40702c0001c005210034100d105c410801b522a0030500403915201301000085001c2c482e400d44190078003211030040350902c0551003004400040003000305c040540c40b034100901c9030f00144000c9011400701c4d12100c180d20b0042c2e441c40180d80565079968145204036402007041c1202440340780c10f11403444000041008280161406 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 261048723 1250 261047473 261047483
    0xb04140603010b030607050f0906250510020c1c0e0901060e0a0603090503030a02030403170a0902010915121a0a08060403110304080d031d0607080405010c0e0609060a1b 74
    0x428a41501810b096a890301c442e00c1c800d400070390070006015001800e032910081e140800070f8542d000400464130602c602070003400d00750580b07507002e80d02c61220003142c030707141d41728000740c40c10004080303009010fa015081a1780800c0d006140f88584103888805508044c203401d1a182c100c810140c030114005a8003a0171040c0040d160040200f0541840e0708000c008003900d24081104d24420b4940549078000505542e800c01e4000002c00c040c1440385148d152080038442c0031032007a00380104031718001c1c261410200d01048103004002040621107040c01e6460500d5180d280e20b401000103580300070b00c4c0300c140c2003a00001e46044d4400b1511000c1c8003c024000540040c0f1071810a4100600030b0654a21001d025034404c01003400000004601614580384034200800c120040b903080702c01c00200c3d250b21481a00c40e04040140c45680a8940e601035805000200140c4098620441380041c03407100c0302d038101034100704020040c104800201340d6054075260038a5100d5110441280e804014070341918 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 261049973 1250 261048723 261048761
    0x50a030209040207153801111005091b060304061122140415140d150b0f0406080309011416050307061a013c050a3f0b04 53
    0x1114003c540b080a82141142c4807450000c015000702c01000408191022410114110112007d9011300000601c10b5190f50540f404008061030700c41c01070100b103440c4942846115107818903203402820250a4100c0a8031452640d80c032600c035400a07100c0200d0502c9140810400681038040c0700c04242070100c1040000291640b800e644045042014a849071080e4a0802d48407942020044000221048be400314001c0150071000200380c0030b1540b00103003e580514007000d004041c564003d500b1204110741880c1500030030070a00c022140030f17001d9100c0503031081080588a600038255400290600c1003540d24158411603103c08045010504840035403000c60208200f2805000788001054442e0340f8a85c1aa05400001c08030388006c2d0019500c0d0001c1000417960b007000030745a0017022131078940252401d00c01d0400070019400f4040507400180d540c02c01d0552008001303490381d401e40076020b040390381d00369034020800650714011500703040c00d0340c0d804041002d407558020004801c01c1c00b10011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 261051223 1250 261049973 261050003
    0x20304030b010504051e070c060507030c08090607120f0204080a0c0e22140f0601060908010608060c1e0d09030c0b0105061204111207030503031503120703050a030209040207 76
    0x4074841042c0c00041c8190305241c208044080c840b42c400d6001a1400f0030303514180c0f40d50354203a4080d0075402c000707005c10b42031404002009415810210b1402d903190303a2000c0725520640e40b15280e00090f0341c15400140b1503018003904c0c0c3c505401150910310385d840d005290a51f2011640c0c606a50301400f00d560705029141001800786406c01c0960055803d81602200c40b9007504044494122610003803c0c544048000c0d84a680100442800648171000311200d5584880024140223201c0c40361000c00d600740000400e140c803001c1141400703446680700c4681420481c00d046e103e018040c9000ca014820140300e20751010b085130017110f0f2440c3c0a51202001e100311030404209c1250b0507040391340034960070001c401d0011550b9800315400b540140400c0240507800740042c3e01034014448103a02c0e4415581d010007406000f000550103401080d0103242107091000500d5114a9904444500c0c0c000c1449841c01190184d070003014440140c0c94010b1918444000050498100410a03210130040341c040c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 261052473 1250 261051223 261051233
    0x5100b031806010b070b01050d110627030a0314160803010e0601020d03020901022a0301091a07030e0d080a0f06091e051302060c100203090d09060504031a1003021002030403 76
    0x407405003aa000d03080d4035005d02611240d8070600c040c420301b40102031383c481d00070034059005000202414001d01c407030740d100e44094016104101001e80144103400e1100520001e145c002001d251060b815100d548101081c1070100b2503030342120944151416041400b10002080c2c00c0c01140a865920082c14060608000091400101c2001e450602d48100a031030926a00001c03480d504201c0c41100100d10b11174112a0102c031558a00ca0301e170950700b03003101c100800031580c0c4454100070b220300c00b0b41040c0c1d07106901282a13990000c041041d503008401c1401c0e0345442101410b078014260308020519001c4000180100c5030a5440746607410741d10100c07078403440361030b1107803503600751110900303028500303140c1b075100c0d0340c0020040004d10031900080c580c08080d1090180f44c400321088481151039203040030304580c40740008ca0035040014502003000c80d8260284082d101945c2e00000d181e01d031103440010340310034000c002c1c00412015011840000040e42e82c6c41c008003401380ca40d4069922103284d841c0c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 261053723 1250 261052473 261052483
    0x8060702070f03030504050f01020708010f090611210702070e130b0a0506060a27030f05100606020a0246080715030221100e0f070f0305100b0318 64
    0xc1c5000c03501002c040000c640e120007035a0507a50108c0f10f101000724070b10010b03494500a0f60010b040c950a0a022141030f41071039005203116800341002384040d507002048541c061041e658082c48031607550313800135000030f50480101c0d8400410b00484010790344680300d101a807041100c0764403102c0040e800c0c140070403210b6204290414840705003130110341003900000c1d402d4002c895892007001030a88004540b421091610310f030400c0c191b02c0c0126901c0e20703818040b0744411003031f405032160301c1401c81c030640c07401d258800c1404442da90b0f03001c0d1501c0d6030103500700b2003d8480103070754a0650783c1100384501c5601c00380e180f0030a6407600340c080007140103c030008241d03800200d41c822115500708000401045107607441c2021280d8440c600140d070f44071080704820184500901103482d07001100d0400caa12900722031400c05890311400200d50a0f624054000c4545400301c070910300050b6049030780320b071080c0071340c00250b04800c0401d20f001e012501c4070000e0078070340c000b02c4240c2200c81d000c4001d043e040d002448 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 261054973 1250 261053723 261053729
    0x705030d1a0405040b04120c0b090d0201180c05010302070f140a05010c090803030c030709121202060f041112010605180f06060a020706080a0219020a060c180306110c070806070207 79
    0x35043c002d0380313403a44a8012048008001514001c003403024000d1103445180c03010451648100f103402c0909185282ca603440c9080c030301c08401b5610303001c2112110005031004980544c3e000f814207858505200045010390080c42c0c045440e603020010301000908600c400c034800c211524010204080c07581131050a6446242e10803007800300c442e2051291400110031a0740c40441014034966944a0600440e44000a0361060040900c4c1132804420070110810700201c1e03100a40c200e829580340c0f121170b4203180806640080c0b44c10a1341214122600f44210b200d0305c20345400d0000182c0c0c80e666808a090007650004802403c20312400f00071182c0004a0107030340045068840c142032008005002c3d560b03a030a4003506051190400c000340c4d6403280c80d01101c00c0d404a8039910000f04a41c145c010f9940c5840e03074402c80d105030415100d2000f80744525544580f032203004a410045928544130007005000c0c40c541001e0392501081a240e400d4400c1008000030a03912006100ca0320701845c009041080c150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 261056223 1250 261054973 261054979
    0x1802070b0c03070c06180b04030207090f050106051902011415030111040605030613090203120712080c0406110102040f0806061809030307081905010b040501120e0304030f080705030d1a 81
    0xb00500c0900ba82c40010401c081d5441040007620010603070f05001d0503401144003c000c00d4042e001c00040641c08681c0c01d085403850340090001e1a010800882030703400900403400010800d100603480d000820300391010402c028000003900d00c500d541800007a500131115460090520342e030300701c40c500b070900c1544005503401280c03071700b001d041502c028070f54840580301504c2000d40d001514406007443d48004405a8024104c6030855146241c0300348580000b4400c0d1a4001c0e0168003a0780320380200419449000303120022460907080540507100b000f01c2c0c10242000c0d40d42400041407100065820b80f014040c00401000d40c0c3c83c0900801850074524040341c5c0c0c0c07422901d004c0c000311140000c1a00d4010000d8201300c2c2071741e40c44040e0820020540e8004402c0d8034200300000551125200061041d03d0080c0e803049503544610f075a40e418ac801c488145030055000b00300410100782182860501d10344a07a400c030380340c0900c9850383ca155030071000c401a5115aa40c08110580301c41861042e029402a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 261057473 1250 261056223 261056227
    0x18010f0204051005120a09021f3f150b0c07080c0102070303230d0912020f070f03060e01020f0f030901051005030a0327030c08070512060712061802070b0c 68
    0x7541031702e0401c02001d41842e0120362120400c41c219540c417010651200c0484070f1000740203402ca00d0081102800031410565441c81d564107040050807048070042c8203102c40d04444800b200d4042c0c880040151980782c20080310441808a28110305400400460000f140103240060078030385c500d4100300e80011064195031204a0400001e40c20000b03040110540e045811103220074026014158814881d92040b45890280c142003000140686d002d04290f55500300c0b844450070203089a070b40c0380a401040e0261380c0c0780b02e0810000d030321a080000c001d00503000160600c0540807007101c041d00001c04141392030f1008410030441132802d225403544080e040c001c0340d8078140380001007611800d4441c4041c00308510030b140c8143d000c1401d6501c451103003d0a02c003004090340c034200b003044182ea13400b8803001e07401401c1000416161601d4603000d141d181d180500340d81e03292100241c60407071121070001002d585038900083d403401500d1083c0551240d110000d6925070151412aa041c0001058414000b1003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 261058723 1250 261057473 261057487
    0x901170a060e01060e070305091501051e030114040b07030b060f071101090509090102090301051f2306270111060112030908060a0e060f091518010f0204051005 70
    0x1000520004441c1c10460006a42500015640c00f5098a4001400d11451a002d00c000c2d0780d4154407072885900000d003640c80d400c840c81e013410702482c42841180e07071100e00c422907440c642d100c13110200700c4080014000181c04203910000780d8019012141640c032003480300700300600345800d070060000222040301c7c1c05240076031140080801c2e00442c940139000307a6401040d60040c0c4d0054080101400c0d0040034a2594a042d1580d5030103507024220071806542020f000c610b103c0d105808080d0f98503030800640c00540d0600d1038042580905041a82c0222071074a0200e0891310343c1d0009000c00c1400746040c2d62a025207210081c10380030004001d904000701081d072030110340b0020070441c2c1940c2080000c041c8010903410122520485030f040507038140281d4040c00007040c904c0d80841c03000d8103468143d544680e41c2c00c1450b5044642100d410001c6c2e00402c07034244825441c0d050190f84403a2030842c2c540c8034401340c000d041c21030701103a0b84501503c0c0d002506102380c4c034052450442d1480c0c1403a089182c810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 261059973 1250 261058723 261058769
    0x106060504030f060e0f030d06060306050f091003060908091e15090a09020409020306010207062a0f080c011e1112041103030f070201090f03030219060612110901 71
    0x100d0782c84090045034012440e030301040701c240c0054032401c803a0002c0f0740032900a101115240e070302c910150700d905460714100140941c000d001e40803c69030010000b071102c61070a024800558002480024a8681d01c94080300080da07903c9045c5215009101c02c1d5101c40001c41070241a040500801030600c24801840c410fa03540c3e510040c662000006907552160622800f03c1d0203030005400454405001140108020b14a40d001d0340c4900c50907401c9460855454409484456035218800d80034502c0c01d0700400d060300980c5050321900c0c8160100500404541c41d24100c03904000340943d4640d44420840903880c0c0242d4400d031140700c103142c0030401030f07494010b002c813280314190800c2114500d88d000102800154001800314070300140560341d450214110f086100c0d404031900b2800704030103107004101c003140f4203002010340354150000d01c00e020355440040240c0c1c20701141280c400742c4484001c1407000c000709096102c2c03840340e01c980c00116500c20400074110016001842c40e032003850a07020905c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 261061223 1250 261059973 261059977
    0xd1110060b0a12060803070b0a06050a0513020a053f060a031b12030807030e0d0c031d0a06090302040e01050405060106270b090102010c030902030d120608150709060201060605 77
    0x41d03040c00c0542698400300b6040700501016804072110340004031f0400c040c03100e40e6928520038482c00720100811900da400300700c24040140035954001d020701d00c86401d01c180e10340c0102034280c0070b400d2141c104010600cc68812086008005031075401280303500904881120f5405481424001c2d42d454528251010914074100f40c4005400e2200c50010f0840801440207220040c00c43d48035044000241c608000d41002c2055410500007807512004441000010911101c5528259a4864038500613101151240c801c414900000b074101203540807a80c0e50000c01d44000c044079100c803444c091550040000301d03400340c00341080341e0b41400100f10000d40d01080480c1950141d081140c0035040c220802d0140d0182508500c880b411518000b0512545006c007401462800341e00921142d48802003c40642c0c0d84004001e4044e4004100405100d0040711a4410250800e038001401035803818464a0003841030b840a490384078040501100c3c03680042050040c051500081c495640341c503c00034014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 261062473 1250 261061223 261061237
    0x2011b20010309060e0705090903030708011503020c010606020615150403060507020a060c0e090705120601030e03130b040f080d0210020706060806040b101e1202010905030d1110060b 80
    0x28021406030554aa0290f0311808041d80c01113000c216501540c5501940c0c0c00e4580126449030003014000346000c103001046912480d000c0d5250075440c5d107800b807400c102c80e407008529028176400744050704640c07100b44074040c010500c580c01400316080c40001c01240f2045c00115501903640084200742c042c400b0411202101e40c01140092540d5940705c0072810050720580080c070079070802615440142d840b05101350b000034100e4012805494000e0300781c80a00c00c0d00e50781c606401c04603001506642c083e034010b80d00c02410305d003628070f05081022180034003c880c2d048207420080110701070090282501140c3d002d040100c0007004405100f030f07006035982c0900b0780c2e15146640c0009601c1c0402100d40c1021004001c03507402c981c07081c101450002201c5000311884c1e8042c5900500018a4010030910208020360100b80a01d10700e00b00401818155840345080c0c0c1030005008002a0546007007080801d00300d5a6a0740c4000c1128420f4146d0904000e900b10619280c100b41e81403203601c40c400201d81d54 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 261063723 1250 261062473 261062513
    0x11030613171e031311011d2701090510060c021c0212010903170c07020a0e270319080105180a0905071e0b0a080109150506031906090917030406022502011b 68
    0x12144a585001000403112390030380b038224900b9400003649050039000f0764007035103050700704219258440004488420203000069409a80480032840b00c4040b450808513150000d00390115565600044500391841c800302103000a0140c960034a20103000301c4040e4020720a85020703403406081390001000340d5803a001d600c00070a1840042010f0800041020141480000d44850000d0707290050b15242c0c1c1140b0850040211180b00c00c620340c0d0f1040f00598169100180009200b045207a00c0380c21884004152a035503950312152400820020005c94009214040080d41c110f00080c402c50400003c9600c40c0782e942600344074440d5495040000c8505549081c0000905c681d249800750346c450b8050791003980c00c07100c000148112100195008202c1980d100e0080c4040340d0b9584551080b960901d00103030103845511011240380181100854015000e04409410800e1007101d009003a00b59503116000544003c0d615401c550700444140b00aa0b41c039001d400c540820745d11004d40401010f030101c03407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 261064973 1250 261063723 261063739
    0x1090e0702120d06031a0f070804050d050912071712040617040813030c05040b09040b06060a1814010f020d0806060f0d0911030613171e031311011d 65
    0x3001c090b0711240085d60000b0984c00220754a104500800e80192240c2c0242e03070039900021030041c041d000031401254048000c0150600e4000d003200c941d0007182c4c200354030020100700c203012910100f081801401c2c2c08410481048083e940452403c07151010307035222044103000420526402c40703e0524403000750744070a0441d54840c40c180c68617224800307584101112401e4040b0500c05810750590130380320305843c200b1005011204110213001c0459000f04000c0e9404000b038014204070700a0010340d1498203000e07000103a81c0301d603203403030745800c3e003007404000009004003502e5a80103c07a0031440c80c00780064008640b100c0001130030395070300a02c0203000d1000041c00e1070400d506a01111042403c10500300400d03c0d80c0e02e04280098928100d691203072041c40d002c10f00c1d8244c40380c000704020354400c40d141000c9245601e110881e4009685031180000281c1201c0c0760388400320011841000c0358802401d030b9404614180b65600e90b8801e020b41007040d19841810081140e4112000d07502040364152 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 261066223 1250 261064973 261064987
    0x15010515070210020f0c0a05030a060f060b031302040f020301030b041202070b04090f0606050309031e0f12100906080307260f04060239030a140a0201090e070212 71
    0x503140c881e24400075004031400b203404140c2940400c200300f8401c550816581c00d42d64640030044081800c0c050380c1d0745034022030074180c0025000c1d40018154501144045410341c4c0e506504d403001e80048410550425841103008210b1a00384101c408207071242d01c04504650550300d80d200e40f10f10042000700740c1a20080000c00c528001c205e254002c1c102000020b54454858104c030018242e4103623030802c400d04081b0003180c1a40900152841041080c00131800c0001d00f0360461600820074245003948082004803460349030b1504004c124030407021030040c0440c240300d107100001252a070f003e00251440c0000038400300801004076200035402c540040e0100c0310b6401065908038030022259241200051641800425040500b08696498081c0d648036144075103da0b541c0c0aa4041403c05070700d180b168040d03050b02d0201040000c21000e4101c88070840c2d90390b142805440060002902c6600c009600d90856174420001c8014140c0c1c102c04840303900386000041e5aa13050300f54100d0f81400085901 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 261067473 1250 261066223 261066259
    0x8060901050c0f2b15060207080102070515180604062703080a110c01050907030c0902090a0b0705010902131d280512041d0106030e0a12030605040501170c0102150105 73
    0x11529444c0403101c1000f503500c0000390103121542d1440703501e016008150300050440300c180300344e0700c0d0242c1200181080314021500c607412504002c20409191484e4100000d44910420507140b08030b118490000346024a619104042100305801ca44030944070a44400000d40c0729103c49e411001c009400706045440002421150180c414078443c698600300c01c01801610010340c1c4012207010700300200055403225002c4050348a00b10845c0d400c15164182000400b185000a2203504e015038000245590726138001451076909505c0c105030b55880314000d407424480c890b1940c0c3d2040c04200140000455003203000c0512603143c0e0000c01840307280e0001d03820300c0301c28003814090905000d00a99600d450300ca103004101541401000500b00890020905500a10440c0000d40a680052018010b96950300980341203004c24101015140c0d04005003039103d50140c24041c10190b44074190b07444191549600e0040041ca0090455026100c070250649108039054195030059601c0e88000c80020781c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 261068723 1250 261067473 261067537
    0x31c080a09150507030b01081b090a09020a0f031811060d140f0a0b0d0f02090a110a09050411090a030f081605010e01050115050a0e0f0a08060901050c0f 67
    0xa00b001c5140c5031800300105581d4425072041e0800d4070f082000c0040c480044459540072550089901100340d84030782c0c62002900a403501074030050003492601c0e203c000400c1aa0401200d11010071921203e5100141d018003aa43d0032500d010b43d441464002501d564415440070450107024240c00680e03601c610000e81c00c0750100708007526a10140e800d0640040700d8480d0201c0303042c0d200700c0c41c04107078140b00d141c014540c51405411800c001510000d0b902004141c3e14040d2003a11080d95a0b90400400d845110107808000c942d41c03a60b1103068504414072040d107500381d0402c19541e900b08054a401d81e42c29090100b500d4201c005420042e03120301c1c00d01c1c7d031403013000c101c40710310b040188040080190542010120400c000003d100c0e50340c5c0c1c0c04000300f41102000500c130109105000d040f00a9204505803400840001d11031222458502c020070400b05460704820080d800c11001c0016519090003442d4214013100c40e41841e20a481404901c50300424080080f40c07a00107418446050050403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 261069973 1250 261068723 261068741
    0x30f120f021203220c1809020a0e070201060305010e0a0303060f0503030a050706090203010501030803192a0c080309010507080f0402010914130e0705150c0a02090403180303020c0f031c080a 83
    0xc4d00450101103400c041380400d0a80c40794607040411100e85021140490040c02174403507000c0c040d00e1400d81490700c00031a031900101000110f42d65094000085602401180c011410b14000384ca000445814010261205500f02c0140780410460400040d2070001c1201c0b58007801d4a070040d01c80e9442e1900300003529000b10044d40c903608160012007400001c90046000c0c01e82030710b031044d008034009000e906941070784200c1405c0c401400c2c5c0c4144101d05040400c500106640303455101040c8503622422580c0055801481130f0303549801304052550040c0f60759421803224601c02c0000d1400b940003c24034002070140076181c06601c403c441d603d445000d510210417604090610689074060b10340b0780d6407102e500c44c451244944007030414041c003904044480d111158805000343d03403105d030203000c810a0054011400c2140c0740003500d04100600c841c4c44013640c0b00ea80907201c0c514a50040250080002c4101ca12075000703641425002902c48041c070226103014100300702c403070303642401c1040140701d01c030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 261071223 1250 261069973 261070021
    0x503040f06050a030c02060708010311180405010b0a0f0b0301031506080d030c0206060a21020a0b0307120501061b2604080f0d08040c0e0603011104030f120f021203 72
    0x840400c1841d0460080c000c050800c0e0f13000c1045101040c4120390303c080940380f04010a46d1079005001081503c4486e08440703001429090000c80c0001401c0e101c10801c0700c080d1541c1e503403010740d59028640040d10728010031b8140074075402c082c200208a00203101c180300041003519504ca1400100600b900108014500d10050b682d03100103104014003c0c0c60030a14007401802a400043d0552a22020400c252100c04482034104080442c843c0030170001001c080e13a10000c120400240040d00c0d200861049440d56655402401c00902c1e000664034180c12010601c00881710350103002410440c44044c0d02d802c4120072480d43c800017088103040c1d0400482c108401c0b00090085005403001030182c4442c4c40480890300f03608402d0404031025401620014281c1c2d9400108004030302c450310081d50815001000000c03071500010746001c1560003070380121a007200c202400741c24041c421500d031100c2005800d06c4140b0f091000c41c000c3d02c0c3c441c2103881030100407010010440c411040c2c00090031241c010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 261072473 1250 261071223 261071249
    0x207050709180303060e070f0509030c0306130b090111032409010f24020c01050a0e0a030b010302010e030a032016030b18010b101b0609111201060f030f050304 70
    0x1090602940b400910019000b19051005c0002d0001c4544807080c4500355031741da400e00302c04007424200c03401d500040c241603041c4030711f031050b584941c3c0510105001e00f50b1700b804500110202e01d051151302e5001044501c09924001d0034507019031230941142c1d030120314010fa68002c40301e0140e480c80060350b80ca20245c0c1143c1c00d00004245030505c01014016a0384540801d54403010038441100707071054886400005801481c5d03000919409600542004d1030181083d80344a112500840c5044020f580261000f040030f0b001041556081a0f058202800039006401c0008280d10040c01449000015080701d0b088a018106a0b600a0024a80d203802c180d5106000c260340e410a00ca086d403054407c0c103200c0000540040343c80130140b02e0903950980142040b2a46171007503030140c1d0803448403104041c40d003411018050000e066449183d020740d200d07503100003000340e404003480b18800c050040903410340c1c50a5418421040d2109074201240d60020244002c541540340003800d6000766448007039540a8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 261073723 1250 261072473 261072491
    0x120a050a140c09010f1203050c0f0c01030f050f0c0a03060e1e0601050c06190608010e0715030608060411010309020a0f0602060a050f15060f0f0318010b030706030207050709 76
    0x1030030000403084407240d0101c0e02d076442800d0400c1034141081c450f80844060445c0c0030094002141c920700f0000b4000c2c00c0031030401c2e180c46c5440b81001107000c01c50b45950480d00c0ca05e8025030300341c8113528208280712030030481443e00c5204000c80c000041c1c0030b03104440c40402c0844e0360a200f604201d010f07000001010383c090501c0d007035040701c614040d1007900e280e80070000000e4155200710155010742240c040240b0441d01c802c213004502594030300070b80320a0790b140d0002199400003401035a542c03849106c008e08803946840f003940641244101410205030074000c041001400000b12a0780190304080c10800c00c0110800607402020301000c001c0d00700070013050000d61000244541002c41d5610380075510250745092049049a0b011a502a0401100c034042170b036414a5507420420300340301420451601145a4401405403c110b51031207043c0000020803c6000c1064180e020030315000d40240480d04200c0d0000392111864099001010b070f0100d400740522400300f140d01e00910a9160420240070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 261074973 1250 261073723 261073733
    0x40213060509040605101407031b151508070603051003020a080708011b120b030703081b0c100804080f04050901090f1a0a14030a0506250203040305070302120a050a 72
    0x4012248a44c3c40d00200150606240e0320040303501001d82d841058074840036a205c00507400c1440103608001e00c003030051043d808003180b0078401500810000900d10640d00302c40c0d0076210718a00240400349105420410341c800041c042e420740340302c0d0402143c295a0003080030b04110040d4800303580986615000100ca58021403110203803001c001c0240710144c020280241c58415590102c0b0020b4041400c4070000002da07402040243c1008040d15405607603a10b0362806030b008100d40c82c01d4040c4500048520000c00c10182948100684050a0041ca1058083c0c80000f0041c0f001e4200c110000c1c001d6416048141194041d120040c94103040d56102e00400000340076070261841841e1038011806d02260b0010f1880c000d080008218014141c03d0420340443c0741101120207400d032003411421000183d081c489944140d80528503c50b8902c480100b001507401305881c09415904104010320120b5000f08800080d01d4040d20300d00f1400c550030761707098034107c0d0300c103c080e10f1070213048010f104100b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 261076223 1250 261074973 261074977
    0x504030c02180c04140d05100c031a060a0302090105040f1d0a0b13020c010e0118111f0c020111160501140909061201020c0f0304030203010f0203010b09010e0402130605 74
    0x107000307584081c14015140c640c2038070b10038140c030a10032115041c0000c0200003140300120703504030005020381240d0381d05980c80d90700e0001d10420703841c920760720b07120100c070700310350511039403034401d224451080c0340e096008003140d034601c03d05081408060300020b40140c181d0003031040b01c00505240360400000c583d151303030302414420708042d80b0758080301f520b0100311544000e025400100c2c4005001c0001080140e100d88000d50003800620711035500c6116a8103500c0086c4071340a0341d00c0e1610a4088003000c02d01e06908030100401055128004008080805500e1501a60603c040c581005114030300540010f03075020000e0b62030210f03c1d204010041c010f540000c10147c0c21642c0a8072014204401d00990383c14a0050135007080c0c01c90750080000f9000e182c6100c5409448401d500010b1824a20f48502c60401c9942d21108040b0381c00045e0402c11400d0034412110b078440c504c0320440c110b506000c405c012501c6080e01c000e042007050305140a9941c1d8680c1140c4111406004d070307008003540d07400050126 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 261077473 1250 261076223 261076247
    0xe070302031608150d06180809040b04090506010e1b071b0b0a1b06180302030301170d0e090a060b0409060f05030105060102120f040515030906090c01080610050d050403 74
    0xb0b86500807000d07845500904609004003600e0101c04241001d95091101803480c1d4038040d0349554075000c2403070361309030759488a100160049100780d94a0821205020569200c140b005000d80d1800074503501180f408107140e4151001e5024103da16220030701c0d1001a84a0a55551130803000003170003034100b110703190880d00c02c05242155806100c1c0e0350b05500b0070314003c000314407002c42c41d105402400b84120307a161035411442500b000503c01c560030324801040e1800c5200b28007681c0000700600900c0c2095030b00c036008031007000041a0341086030328014003a450302210180962a0203012400010441d0407204c050040e20b001562180d5598410802814041c03084020784506442c01090500b010b0080038030480040c1c000341180325090307050070700c560301022003020b40c003c05020129280c0c7e01c8001c0b5034110140042415201c0c1440c0c8015070501d000a0040c050640c8132860301441039070031881040e0700600884081c04501020003080d42d9078071030007645400340c41c6014100803c054001c0005010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 261078723 1250 261077473 261077491
    0xa0309030806090606030a0e240702060109061401050a0509090a1b0c12080415020307020a0c090b030d030b060c0610081e0307080a050f0a1d0114030a05100e07030203 73
    0x8079215841030020a83d029103041ea0040340420005080d8070705d0340c0103107241d0950102115075204030640380482d030506507010300b4101e02580c018844043ea0400420340034190184c82004081d142003598101d01000d61025030520070003141b0f4100081c065000d40751a000c010b44901001e14001552030020030301900c842007400c800d505c820040d86e119172400004241e1001c040e20440c5991001900c0d0104001d1003155440c9400302132101c000c1d0640050350180005070000c005495440c90901c00012694120812070b510b000350b00e124030360740040c500e034044c01035003000903d00800300d0100e81c0314807403103401c1c12961281000f88070514904030035913011224810143d44800c0d9440c6a47c200011058209a90940c000c4c01001301244201c0020701d200350190070010318146c0b40c41030724105600202a00004259002d0705450521101c0600b0340c2002801d2130300b442000e29848641205001c041c24840d0141d0780c07040020590780c105000c4801038003070610a0b01842c6010701000f00658401c41d01016 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 261079973 1250 261078723 261078737
    0x90b091018030203160816060c03060603020c060703091419022b031412011511030306060a0c2d0c05010206010b040522060f240c0210050f0a030903 65
    0x8000454401c00c00010750603409145801054030080da141e60f60b02c07800381c07240c0740c0c1080640c0f03038400c1c981d00000301d480c03081c1804128032403110000780465419030300c00340505004100000d0300f0380f400708100342d012503141000200c400850a1135002d0000d001c120000c01c1c8911074405c51540b640c050f40080c1e1510032201c0c01201030013414202c2e251900024940c6e010344081da10540064060308070301e10b82c0d903607040d41d081c00d0000641c0010301d51002170b803141a116001ca10300c010101d9100140f00591940440110701d5400c1801c08626140708000d055010021043c8840c0304120f58103a80110316804013900003400d078041c48409074201c070508070444158010010000e4507500100b1014104c0705c4940704541803a00d003600307114003a030b071848403401c01805082d580004840301c3d1107144060a0303024140801c8505189440d07103031080b40c03a145164902040b00c00c0d0725691b84903101316881981903072505402c881440040e41e0754051011014140d84000c6980800707140d00d03910100006000e5520b643d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 261081223 1250 261079973 261079991
    0x6010b0405090103020904050f0615031608070b071401020a0f091215050601030e0109080c070e06090a020a2307230606010509011103190915050d0f090b0910 69
    0x9405114510610350401003080c010005481c180040c01c0d4010b0140054030305600804490f5410050f0850b6034004044031800205844d0070100002c40301c2c1390030201d04807895401d10b54019034469803445842824140042c0b003008004410400c060981080c41c0250b44841c9112400b415000b41e140c03804000a507903080004101907081c01e060309081e0881081c40d815141205010040c1600612030b42c14580c59104420b05820240302d6082600d0181f1030581c2c950707046960413030400714264004180f00c4c0101c0140f1100341d441076252900449108401a524840500c2c1681ca20691a120702900000507140506205000f17009002c0140708441c80c1550b1450b8400c0815074850314110401c440c0e0241d0001041d07540a94000d00c0c07140c10506090451a9082514501d560712400ea45100740008642403448141c100b2400320180c1181d001408000c0e0312040000c01c0c40c01040710310001c0d980c0782e0141303500b190810b0f801080c0040e0427900e120060318080d81020f40e0740d40030b00315107041a86450b01038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 261082473 1250 261081223 261081239
    0xd0221150702010e190201050313080703020a021302041a03060a03120507120c110f060c1f05070813030c0615030f0b09030a090306110d0e1c08060a03060c030902060c0c030601 77
    0xc01c006942040c0c074000310390082e400441c2e280c0c1000b42010304ac80280070340d4001054044d006050183e00ca41d00816442c0941d2050041c20b102030598043c4860060005100701c420303004024100c0c0e10002c404d65220398400c0e0000303074100150380c0040d00c14074a10023174046d107540c00401403131000e02a0020f110254041d4004650003c0071050242509640041c002c026141c40c250807000100010680d50501403130454107801c100010030200481309000003004084001c90180c640d0001c2036040500d021724007440f1100504282c030360010204038a40c8100c02c100071169011080b928207c02550100c99101e10304080700c5c1e00b01b020180d8400c01800d0000707c8005001040720040481e0b81d54554400d4a55981c4c00082c0030f9141000c0e90b4103c0c00d0000c1056803aa40c4201e100d00380e03440b80100f284411300105403582e02070b400ba00b4007c1201c8001041003584880ca02081201c1d03100600080c01c00700074000318001c1501c1d40000b940900001042c42c54400005035020280c4412400c0d140140d81c1c400030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 261083723 1250 261082473 261082483
    0x90f090619030c14031204050d05070807061d15040e0a06092309060108190c03080a093b0604140f01141905100516060203011a090d0221150702010e 65
    0x3901401e1200b044103101508102700001c1d24140305100b11124140c58903110790500003907070001400105a14a40308610b40403400902d4400750a44100d41400d00d0034400d820b00744224055413514401a50218039034a4407940490000d0030001820800081200d1080d2000c0c0c441d6040c0048085101c0c000c600d03400c0020601ca81283c448400804a0280007076010340c1c100a030b0a4151519203100c00c2c0080420340010084c90880010782e9012086070600001008145a0142e05414981410300d0f001900c1d03003641c0b6000c440710120394045005e55071000054082c00c000c41c00c044ca188111010f111407420500342c114140c40b02e550816401c0306680040c8004181d141c0302002c0f8038003401c1010055410320070b490b001c0e0b45503e45019881c0807540d60050f280441a4482112840d1b0f00100410203404c2d554841210100f0180c01c0c189801c0550001400b0101c144130064416034030350200c0106104446c00e14441c4030504019202c80d11180c0c506c4a40c075200071501711001d54289801800380c40c5010503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 261084973 1250 261083723 261083743
    0x6010e04051014010c0c0b030603150f0105090a06030f030e030f12030408130e1501080a110702220f0b040b0603040c09110f0f1905090f090619030c1403 67
    0xc1c848000e242900c1e03101140f04a460762410b224200d8115000305030000e401001511082c1c0d482552820900280340c079020203c480011980c249006204900c0c60000d0500d04540044411611703986800c5201c1009080e250300080880d1700c1404600209604400303e614401c0b400c8042d50390707540c640101e203038441c02c60700000c0040000400c0000d0001d5060f4024143c54280801b0840c4000e4440c240020141c00c140c41d4104415038444002c4e4044da40043d0300359004180020034045444039000300c07035103170003a002c000f80b051f211600ca51011501c08001002d05070010201070085c9400001408001d0500340d8105000303d00304003840110b810600101e0340a59442010f042043e86007000540042002c0c94006403404000c020001d8406800c40250030709070b02da401c120396590101b1500900002c5100800c0f81448021700a090b240d40d11103600381c60b0b1903010350310b000300c03907840d14002a051035148641e00c2c1e001203164404414402c06002200c00d85401403100104500954101540c0b072501c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 261086223 1250 261084973 261084991
    0x8041703010815091501062309101d0405010f03061401030f080315060d02120f01030804090b0d06110405310902030a06050a1a011803020f0111010c0806010e0405 71
    0x244900f5440c0482080c203a01002c00e20650b0021402528464103800d0203030b001d20006000508102d5076400002e82444455101024161900d507800012842d0310309444a42d40c00c1c081d00d95178014203500d1500041800f010001c1c42044150384030000002c00395618042510a06d14000d9840385600c00e885000c0d041c0d94010110208080181d55146503a600c010101d0414004285070103503162148000f0f020701031102c100c00740e16101c89041665980100070074080800c3c010030010000315550408803030580f0000100807405200381d10210300c0715411808000c1146241070302c00284010761801030030541c3c104580c01c1254400b0441e031021400359034108060040300656085a030801158441c2ca40301d80701509a401c0410141ca030442258000c4500280507500c1d00c1c1e2850052070b5030122640048000d08203a0300740890041c150000304c0705804024000c050f8800c0c1402a68006c0b41c52102402c0d6000c001d010012100c0802051408262041070115800c250b07500b4442c070b080d02aa0f481081a8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 261087473 1250 261086223 261086233
    0xf0601050906040e030715050610020a030906140912030403061b05090f010e030a0b04060b0a12060c09080a030c05010c08190c050918090601060c0b240a06080417030108 74
    0x10030400006018860b00d004c038030300c001c020500c006801442843e045d4111007000040e10316040090201800c42c01640c20304642110f40c441c00002c0c1c1112b90320060f00c0c0d491070440b00230098442c41c0402440391903959a4045042c0140740428800040244283e074804c45007800b4009001206903860302c951850300012940620103004a418529034030802e2890516124440b030160101007801c0c00340f900401e031140b0a0080400013030000c107008926880c9070a80f000c1440301e10b0044e40c2e00000c8281c0707000030600c50301c642d0101081803180c00124090300d0504140c600681103440e0141140600c1c041c1203030154208611919000d001d40354252090b10b0031820300c0e4103010020340c5078009180002c0d0340f03000c0c04420b008044160715040c80c03e030391218030f208a10642d410201d10080ca003000c168481d0b420042c028480100103601c0407015a041075104400da82111140700140400c810151841c0350016014000010707641ea028117928011030150008100a18420483ca00030784403d000e00c207400c0d440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 261088723 1250 261087473 261087481
    0xf01020c060a0e070e010b0909010f050d080306030c060a020a1a040206040506070606240206150d030f090305010c030b012303060d140f01060510021633020d020f06010509 75
    0xb60f00410161034205055400d0700b0380b00d41c3d904d0740d03d0b0300a0b00301b5035034084003041c1078509044c40700a5502420841c44407440e440c1c6840000f507611a014100148050b0010000c1403840c6c03010004460748036401440d0321341700c84905000950300c0004940a603001031a100424030361400e6044040e01454001d04000e25003030805040c0611a8401c08084642941d52100051318132400c42901c900c1d82960b5401035021000c0603402440c0281c050100c1c05c4001c1620050011a6644005518050f90509000090030707102c07042a0b44040d510762010300355500b02079418040c59450b600403409580c090300e406107a00c4904070080c0f107030042100341c40d0a0710004c001042c1c491a0151002006510500102a108004164490400884111320380807070f910b07400c0a0259251001d00014068081c1c801030008a8550041c1c0c0940100751040404c14029032000600c1d00e0100614404551040e0114003034000940800035a070341000d04034000103000b6580c01201c4910040785060407902c0040031803044c0c0d12 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 261089973 1250 261088723 261088741
    0x90b07110307060c051303060f0b010203160209060a120b01170307030f0509060f04080303040203150c09010806010e030318010e04020f0f09030a140d03050c030408030f0c0409060b0c0f01020c06 85
    0x50020040405e006080c40183d89105000f004180514400c0c071300414070301c10214a49094403145011241990814003c0501659185e440d1548040c5c04841c030960075203030907000c00e03050500c54101b0003181412355402d005201d0348042d040d0403a40e201400d10925841039007000e84034021080002c0004480064900d2250711031005040d4219008007214078007046024010202c1d0b000c0d0388401c105030008410041503180910020380d00c01081000c4910341c1c50800009280da2160306803180c1800000d0001c40d0f001d91194070851090030004c5d08883da00c41103d908503040490f000071507400a001100d249089042c203009940f800569010a01d090807e010481c00c000d8000d601c1c6603806100f4000d1090104a00c51221541c01c02c0a0b4081c040011840700f0080550b07030014001c0c1d104880800900c070001c2c55201c1140d9100a022080d40d07400d4440352610f10480c407643d44007940540c04c1100100300c009d018402400000314040884109805964045090703008105450000d178100ca0006801d0310 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 261091223 1250 261089973 261089981
    0x2090601180b0408070f061407030c05150a0213060302251a0c04080601050102070b091903080d0e060a090215030403031401060f0e010315140a03020604030303090b0711030706 77
    0x6421089410700a0b21640e044003981c01c0f070380c0440040d5118040410900c80c4a22169000d0003642c03402074406600704170410024800c680d00203040000240001045c014280240f10b1034291103402c0050f0b500784214680b02941003070001c2401c10b2280440013500d94000e1007140e884101e0340440b440e0f40911024159866070500d2010713620400e18204101e00c030460f90000510400707044a40ca070b2624201400c052810005070007581c15035001102c140441c01144e81511507419044031642c0e1400c50031740032100748031100d80c0014000040400d03510741d880041d80155500c000840c040b030301c040d0348860100b800d850001c0f2019421080460b5988a82d0a02c00b004590103070080c00d0100303014008500350040d240003648100001010314045c10100c0d6405030010411000c2482c050180900d502c10b000e166842c10301c02c4a002c1d50031800144c1d00c94a45480503c021600181a00e40301c48d81d034100900a03285100b0101d031100780c13a5001444040c050b501039071425802e84010740c2464020303500d83c4020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 261092473 1250 261091223 261091247
    0x9021210031e0819171302011e1206030602041d0c030604051806010e250206060f010309021801050114040807180b0409030e030609011a04200307260402090601 70
    0xf0300100064007581168034600c41c81300010355901214119050380480c540b0303501920041e558404090b640703001d070383d001000b1b010340124a40110b06003805950180c80c40c440f03036202c802c105802c2a00000a0021940c05041107640000060329601446440d03034840200440e1210302c922001d00108050382070907400301c1d500845039075920300c42c0200811005e140900990044440e480000d0030050760241000c6c05500c0d01b000054006d0b5502c1c900340c0041d4403030200800041c0a00504840007210340e10a4124200d05900a00f101451701c0440002100041c805d029141c0894400c03180c44082e15801c901319011910034802030450241040a8203c60104011040c0c500c1030300d540c1c081c5100d5640e40300c1c821049209840e940c4c8007028050500d0300781480240589032030703454140c00328410085250800d5200500300c50000e06403410707658a80340b0030b00910480c1c1880c500030041100070342d0000012259803985114924504004040c20420032000b00e41c002d40041075080881c1d440e50107000343d0551 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 261093723 1250 261092473 261092483
    0x507020102070b01030501050405120a0e040c02190602030108010c02030405100c17030c070302010c0e0a0303080c0c0106121406010302010c150912050a0801120c0b0304080c010609021210031e 84
    0x14058007500c907210000402e805c15212a59140d040c801089420010b04606189202e00c0b242401b4510300094494541d03080300502842e2500400d0315814802d1100c80442d02d000c0b200d081401c51b19041c0500250000d024455640d840c1c252580e160038000003d580c21102c0003440004083c2c0f0340c990481d134010031003000319030901c1d10803803e0849070320880286126844a1803115180c0342c05042c000e003900c4401c0303010700c10300c90005151003050301c40101440a03a40c045c00d003000350703886041341002c02d0301ca2030b100140309500e00f41c40415440c42045616610500451b03942403240100c4c90410303100d00b000c0c03000a0115400304000000500b11705410004044200000542e461003900d440d0300c0825038158010000f0800a4030840058100048a002d0b10102010030030403061940c560714625414000c0d03040d1080044005000c03c40ca5208443c06044040004d000080d620b15010740650071050503030300c60009013000544001c4942d1444001c0301c4e001410281c0120a44a0685010501d01c6007602c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 261094973 1250 261093723 261093727
    0x4051f09050109150c0806060a050a020c0a03030206040203160e1602010e0f0705010320090616060e0d08071701062015010312081e070e090a0e0d05040f090507020102 73
    0x106500b0f1254008503070040e5000d1040414919101e0308030341e40b4410388814005000d083c00080c0d140c00d000e0b600f4003000ca06161b980c8000c181003c1e807401700c2114840d5031000000f1004820107a0100794140101d10030707000c0340c50055010344260380e200c540d801081061072849000a00d200d5010100422800c00c6000000700032407004a0507080185402c030400700e590202c0800c010659151103034203125956401c1d4165005081c6200020303d05c036410310203108180100307107115580c147c603103001c0c0306580c020002c02c200034280030104e480701c3c1007440c15804a000c05001903d882d02a100d45c41040294001c0690300341c0c00d002d8280d03112900c0725400d030000c0340c900e80300700340c0800704204819010640b540309030950362442c6004500150200006820804844144510784020b4201d6403044007201e030a0164958401c1c1088880e05400c0c07555560140c00c010520250000551003040440700c0d01060714015511002c0030385e0035200da4414000c2000d414103040100124503880f181d009996480098 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 261096223 1250 261094973 261094991
    0x2c0123040b060d0c0e030d020f1203060414040b06150405091f090f0e0c0d0515060409020d0303020c06060406050105070311010b0306091c03060e0103080c10020c150105060304051f 79
    0x1001c841501d40c80102140b0070010688040c0750401200e01c03842c1f02171008000850020075200d0301d40d560320301c2180c000c0e8804008520150398580042d001a080c481c00d10074540790900b0404403520082c0c4440c1e0242c4250b8440405e5403013400b007150b0541d01c0c0549520b000d07458210b40c41264a6981117031015003001044080341c0400a8040d01c07060004819011503401040c030603003414810328403074492041c500025510b00103040031699800728155141010351954030707207011034080c0c507400c0f00081d07024070700040361010190554040c21b12aa0208100c5580b1340d80c0d40103100440b0a24001c99002c0355081c040040064414440b22041546400000c10046041d4011074a042800e440c07603a021707007100c510031020410305e00346240360101515050007036501d0305480310f20046c010b020103000e0314030016025402d90410008140d034009240d00c01c644c2c80110404594840c0450300390215003c4506000050501c2c4c0f84081c0c030b001d00d4209016020383d54012900b080c0d009038060b50f1030161901d40003e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 261097473 1250 261096223 261096247
    0x50703020c030d0e01090504051608100e0a06060305130305040b090303300c041a07060b030a060f060b12070f1704060c030e010207030909050601092c0123040b06 71
    0x10a00f20b0710750f52602603220710480c0002d4180301d025044207002c0c5103064100140080c140840d0b410340c3c0c0c201e061140c5207484203540382440540070742050302c4481c00f01040c03010048103584403201726500f542e410041074a4404a120410407100006070004900f40300c11700c03201100c10000d21444600a003180e01d042c25100715009080e40c050618000e055000b84000d0001049140c1d0b11b50104204840e18a410708014864040e4190005c00c00102c6e580440d01070708104d542d601400b001e4100800b21400c2d50791b103151800203008080816142941465400601c00320b00c80207485c1030b1003070055104400d6541d902d080301c0d0107041d065007104020184c968009800c0001520310b0285010700c0b0301080843c0041d01c00f80688200718071401c1c0076841040383d04042684074410704180c541d180c0011a8546403080100c0d014480da070810b604800e0399030b908110084c10220080205000801e07181d940713030398400618800310004141071400760035205420100d4a0280d01c0041101b100400d15801d100b10f603642 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 261098723 1250 261097473 261097483
    0x81b060114090f010f0b0f040b03191a030303061c0f08090a0e010803070f03030b1c06050108160b09130c030903200d0e03070504090b072607050703020c03 68
    0x458501080c2008024030a802c1c0030300e1265210720000b0f85400360794500103682d040d8001501c103003040d10401191041034039041c00103c0d00100300c0092042d460b410001c1c0550762030007039030a0b011f07800391038000300c0c6c02d0741c1040c69010707100804010040d42c00c1d41d40741c20030310106c1144040d00c2d02c0c02d02f2030120b0f402e00040c154074201030f100340500340e02c5c0d458140e980300b40300841752580c00080c0c0254030000104250340d40041190801075000c225116082614a81074001c2e001100d207613a48034901c2c0c00e0195028200d0302e0040d0311507000e20011300030360340d88080294549000c8241d404103034018110070b00c00c0c0b0700d00300024900164042c2a40e0038007040301c403250046075600410340c0002504c4250040500d41d02c0850518500320203249041a0544006401e42d01c0360907032039200501c0024441c07040c0c035540500c501c03070040c18042c1041c025070074240b8115680c0c0508a403a04042500101e075190a035410030b1503070050101c02c00b0754043c44e469551054480740c00802044045125000c201001620309001d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 261099973 1250 261098723 261098729
    0x4060b070507181e0b0a0801061217040b04051903150b1f081503011b0305090609010c1409040b0a081c080c030a0e150f01090c020a020904081b0601 65
    0x140100c1d07401c1c03c00c2d0700c600b0114241d2442801d41408540d406015456007210a20041c0c000000340c52900100851545115035008100e19482d11000041402c101109880742c0351041000c1c815242d0108802741e42c0340954000c00d50b1225060100380040d040000c460302d81c003800c9102040d201030b80c80c1c0e641005002000800044251110b0444244e420800c202c40c0b46000b1303012040300506071700309001f007203003030020b1050401c2c1d11141800c940c151801c0d80000141d034184065160040c50014002d8040e0100350740000440c4540d000140300f1510604c50345120500d680e54448800480c0b000b101125044483c40a40c815070f14114101c2640d215410740703004080550140010b81440e8103a04000c0c020400e0220920266108000036120b05c001141c1d4003024001e8009141d519400040c1e1a0100a003415007560241031b06105100c201240e002d4100c40980314140580c0c403004030120b07141c16910344001e411100307213404240019022009000c41c11086220b09030141883c04070140b40c203100303078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 261101223 1250 261099973 261099983
    0x3080a020304032306220b09031803120412060b061801080601020c010801030204050408040308070b010807050a06020a06050613020a03021317120906120106020f0c040c1d04060b07 79
    0x1410410031103502c403144e0740b03204590032402100744c0b2081c82c141c44050050074030440d007a01032494030150343d00c800b048003c030350003000c0c1c2501d03841c0000d407a81d500d900590005030300000042204007940350001d1401003c00c8141c04040c1406d15145401081c140e6901040320203980390b1041040a032110310162904200000c42101c4048144002401113100a0b01490442d0021003001d01c4c56604030805504495060310001020350381da080441007402141c200521000002442c13400f072010412089041c0c801c144162aa0b9076591000c2180c41c851510501e4007503000340c203030a0701094403680301039440740780900004d591804e040280803ca80c04500f43d6000709070301007207006000d11131072030b16009002e45140800c109500b5a81c41aa90400441d400105940000d411501c1d80c80e50800e4929848940e8990348880d61120000381d00d4800d4032003240d08500c1900103284451905001f420b1114619880b891009001080303503803803480c40070002036002504c88030000ba000f00d07082c00030034485000d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 261102473 1250 261101223 261101227
    0x60a050303190509100e2407020f0f0603010315140124140301060507060605040605181b04120b091b0d080403080301030804061b0b010501031d0d0f141809060a03080a0203 75
    0x39030200000d560741f41401c2030110340a8540210044824811031303031441e404443c444602c42d0094005118145080b0700c40380c00c10f42c040b00000804c81b40c0e20100c46080d007201c0090000801410f161815000c5c00d01c1441c60071103d091044e514040c0e00c0b540e100c00380c0c25500d0059820503040040018591003a4083c1d000143c0c0007801000703100091040030042c20088609000462800c4005230a007584010700e942ca04041c03a0214183c44894612074000d0f0812180745138466036103410002d0b00302c03891902a60404600340001e01180000720780c40a945106c0d00c400315801c128141406010003a003a0201d0b450a02040080040303200328014500840c81807540c6a540d0b8101480241000022803103221051075503903210001890b04101e050540e5428a4000703580490700c6040260302d110070300ca10034030f07004c1d000244041036440041d8540040e0769444202c0c4511095191420034400e818441e9140802c1035600348491510410b0150021802032009038007035100e40720100700d80e0100c1d1640c2d000d030f800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 261103723 1250 261102473 261102497
    0x304020310050f190908030106031119020d0932010c0614010303180305070303080c040302040e0703060c0e060403150e060f010609050a060e120f120909060a05030319050910 76
    0x4d10000c008000e44140001c0c0050f110940d1000c0b010700040c001c01081c149ca4080d0441c50300890b400b602c10146000c0a41980850803460180d114103091500358001050743e1004110b90070494413041400e84071035028240700140781100c4099a2040708240c0c108070500b40d0420110302c541c007810b4200f0a240140d40a203516524000d000c0301e6800040021005030034108001050300801ca03901101e0301802e00c00c030340d5902c0c41c1d00403150f8415034000940c07061900c1804548a400029104141d900c1040c0403c0608201c8a00740e03490b0a103c1d43c180c0d4030007820441400000c0d03004450000c1074410080202c1e0303207404521040d0601c00d040380c4080f981038480004000d00c50f40040400c0c01043c00762030800145060030802004001d0500b0058080c2c428803408404c8508108002110881ca14058514060642910b065140d006072203440c803030300d2000702050991520030880c5040b100b0060041d0300c0d003003100c1c1d02c1d1104c010b81603d0342c03000d000c01440325201039151400c203d0f01184080daa00800011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 261104973 1250 261103723 261103741
    0x80706050408010e0606011d03010b1005030907060305190f06030b010b130b03161d0a06032a0c021e030703060209010f030515060d0e030f09031209030703080304020310050f 76
    0x300c58621340c07020b640000f081c400a030340c0226020351218621603000d6030406070400400d000d00703d4004126000184407240d42c952551003000346014030401000d4481c8550350718404c8042c0e80c000c2c1c90080c01e080074084404540038040e404400c8500a0440c0030551581d82e40b85c103903100c00e00b6400b50441100004024014461501f910070103405944282411402d100c034409421140e00518541031210f0031030050700703040310f00a244041c81e500030000002c3c0e940f0340e440140a03041c24600108000c00030035603c0300c0008481414a5124a29620680460015000c0085e24800c0003118848054501ca5000003034034107105200c0079601682015940c3c9040c440014040c5484218290403d03152005003c0d040800c01210309440700110382e269114002d005120009008101030740d02d0713510000030400c42d1502010054030742d10030110309480414680d1001400c07584500b824050340340e00581c00500000306800c000c0d6802c00c4c0083c1c12280d50341080115402201d5040c2d0785001c1141c220300400040e05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 261106223 1250 261104973 261104981
    0x121006031a0c0304110f010203090d050c180103120e0a0801060801090b1302220b0901090501060908120d021c021303020f03190206090f030a0b0421080601030b010908070605040801 79
    0xa000c0b4506503186107066120880d0400400a01c2841040c030034400c00c0490307200b08280c50750100018035140c030300c46403803030000e40d100c80d22504540907908510048400000c10380c0680d0490340c000b6640d41a03003001c0070382240c510711003504803907020f0754a0a000c51105000d101d503401a200340000080d012480381070a08010310010040101040400181d10041c5c03038007100044039090821498407000d000d000520301404890382d4150b04500c0d81000001c8020054110504039400e0f911010f00c901d840341c0445440d038000c800f120054520410442403000304903030003031080b05100744650785a001c03072103489002e0360b1106604c002c0c8004070140500c15032401c08040300500d00110002c0c01c103582030806903405a031600b50041c0c0720388008504030b951500c07000110146900d0013825110001c80f40d1034107a407940310607201521809160105075018899201c07521641d5401502e4903261991084011400740901845c005d040051041c40001c1825080142d14040c201c035849182c1c4071410101030500711 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 261107473 1250 261106223 261106231
    0x106030c032d0509030904020c03090a0509460b0301061e050f0d0203011104030b0601030614060c12040807090b040b091902040f0902030f1302030309121006031a 71
    0x4121405154001601007110520101101c0700700843c4039904d0b2580f00341140240d100700d6811500004203808003103000700041101403000c40e034410f407031500d842c180000040d08455103c070907903503241c903400011640c0c282582010300603d14100f05c0010b444550b03031004074070903600c000389031105011190f41c502800340001500c0c0e0000403c0c600ca0f040080301c0022a061b01c61640039144442201440c0c0d143e50200412940e0080c00038040b2440d403001182087d4080e01c01a100101c0070f40c049280c0d58824010a02251300b02d4200358081e0f0004000c1103495404400c910680d4070030300c08180c1249102002520042403150003814086140040d81c83c1039650505481c3c0c401e6180101c0c1100c56076806808a410100452019114000c4506480001c1c401c5800c41c03051041c800d00c000400502540086204a6a00d41e4070346694484407000012010b03030780e000940c10380081c0052289400d010203c181c01520b50b10072103039409035038105a021542c1c25041503d0100c2a40300745840000e1401c00700f600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 261108723 1250 261107473 261107501
    0x308180f0d02013c0c031709060103060506030a0614100b0f2b0504110a08010e0601090203070c0b0906060328060c050c01020d0f1505010e04020912060106030c03 71
    0x22615030360b030000306401060b0034103480c0440144200c050b5824120040515030a0b40a8480c1082d20508405080c2100d0420114001110385045428030b00121001c94050b08500d00100283c0c0d003907584030030180c5401042a0741612585600c0c00218015028149155a2100c0403072400d0410740d1f101c01018210303800800c214002041382020100100e0300702d5800180c004a1215141e1040c249840d1080190b0f883c1580305041106100501482c2d0190f0481d0b503104403140d510841e0b42d681900e0030790b8a0200207a0707260704000010002103180d5001154040c4031445c0c0720107454015a6004030056082d10407117000e074044010000541420080a0800f007585500a103086000c80304a604421002c03500900e41a110b903072020402d4090002d035801c1c0d40c0c90070020b544445444c096000207040024120780c14500740340e070103d100f901c1c10b000003040c1c2d03c2c180d442d000e002820f1410710006e58044213960b0b40080d2494518508081d041c00707d10b020306415503000c035004180503c018142c4000821500c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 261109973 1250 261108723 261108739
    0x5100902030a2907021b040b030d0305060f0415080f03030f04030c0203070b22060905010e0603040f0602030c07050709150e07120c09061d06070b100308180f 69
    0x159400103080100690300c403440d1554034200c4140b4501c0500c0a810001e40d10155000b03115800381c01040030124a960007041b03e080103121020403042d034800050309034140e0407480e02500844c0c401d8024560150001d0041c009180e24603000c2421100c05180d00214605542000d02000c0c50600040171354503a01c3c0029419414400c0030800101d00c00f80004042c400160143c00440d1400d0005d280207211100d04562a100388002c1404107862207002d035241c40c0d00c003180c040f6a040c0900307580e00c20350304180d6074500e65000c804244045948094000c4d103c3c00c00c40c03100790002812500083d4443e541c01005980c482201e450042c0c1b8040f855080f06007034a05146008040a41d084259030032510407148203000d507220b0314816600d20007181e10301804107081000350050103400c00341400c00c442c1150742e000c9000c04031405440142e00c10a00b034940c8502c0400a04002c11003404416821010302c00c00c4182d041e903650781e20203160f404085080c2592051403442c031424545101c0d4050300c1c140603203100d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 261111223 1250 261109973 261109991
    0xe010509090c060d0b040504032714010c0602070b090c09010f0b0706020304140d05030105010f03020c0601030f150f1b0e0f0105131215060b070c03080f0f1201030510 73
    0x640b01c0808074100e40c00781d000481d2020301d050403500241c803044405841002076042505004150b400c180ca06004890f64480d01c411032980d180b641102160901c884518030100d0b0300e001120072087c0300f0801d5512507005d0000c00b020aa542c54a680155a440010b240c0d0f80c0600040c080d0008050f40100c2c90101e503403000b008030008036001c48403d103521580059880e030702da01d00080044000d90503400c1c80d00c186040e00d165107400100440c1030f21801d803500f00515251410031410303481499030348005a081040100005001000d0880100d0320600d45c080240b285c118803a8102d51548545040c0340e5100e04a100003140b1a040307020034041186404101c41c2105030100c5c83c4c14076640e40c490f04100002800071082807003848001c4c040c00000885014601d050700300705190034141081707040c1c640e24010b030006140b038500c001c03a03000c0f50b48040003180480c40c1d80c86051050f0490484418001410404450903021140003444000b0b078104251880d035045042007403501000311281d00c2024500340040b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 261112473 1250 261111223 261111241
    0x51002030723061003150c050412050d0305150d230303090601090606110303150a05102604020d0b09032505211c0216030f0f0203090904031107080d03060e010509 71
    0x99203114101d12000304200340e954071f080f2424826607014030400441000e0747da0030020040f2320030045a03a19a4113210a0b2a0b50600c400759449401045611103901080840003440c0780c9111200004080452049880424001030440d4012600071010307400280052064940c01d00c948400b415481c54101041506c00c500580c0c1c80c44094040c0500d103000025044d031176503c51301400094a4003610390104159010009000c0440445949a03104808111094a028120801c0d40701c2c0307070024502c802140c00c548440e103800714042c00003402c900080008a0901e16001d4681040d600031144a440d00f04413800c18905002021800102002c03030311074250000b04803002544c0b1880c0c81c94618441c0c0414401003036000b841041c608196140350000d0003400c8c50f42105605e42c00c8020341d241c0498180001d0b40803600c9218045600d0f81c004241804640464800e5a110814103442c6040320b80258030f48403030074501090f12051400180c1c6610081c0002e0f5101d111803801000d0a640c0e420480c1000669 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 261113723 1250 261112473 261112493
    0x311030105090a150f141008010308070501020d060e01031b0b190e0d0605160807140c0f060c0a02010b09011217221a0c0601051002030723061003 64
    0x341e40c810015030b004115508415444905100e0b01e12518405040da5070007000c20b081114820358020708924550012181071000340700c100440c0b02d40d103111040e821755844400742d810903030742030354290345c00d1004c14000d480500c20807024246c420042000e540c0b4614244030304881410340245080b0231640100468803450301038a140150420340000100c0d00f03103104803001c0074064003582d8003c4850b11044240110341c0c1c003041c018030300440e12007840011034400791003c11007903ca50001030b0040c9028946510342d44003178440b82102800791001c01e00c43c041c16130720b0140d00b9103c03039002510000301c40c014a6024400c0200c003082c20b48070208258900b0b020514841820900a4090b2071002404010080380301c041720081c2c1100c0041c0070b160051400d4241154800e400390380d401c0d403100c1d040000040e8500c030a68102609450003009142e00b4041400500c2407440da1500540c0300c144204800249850002442528002c00c05400c50341c0c0d00440c00c0c07070088007400002c40e0f011140000d2000c1100041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 261114973 1250 261113723 261113729
    0x9060105160b060d050715030608030a090b251208010602241b030a0606021b06090d030302040b0c03070218010f0608061908010519050c09011101090204090b090d03110301 75
    0xc0d80b4090350381e03500200301c40c3d0003091002400c50180280108490300310039183c01c0d03100815a801c11807191100395076a604d100720399541d40400c6849100b00b041195400c02014804d040c502ca8100c500301e040082c400884043e4403c5983c00c0180c411094810752008003940107184c81d00c01054081003404a403c0030002500c0c24048910640740000c040d0050625032001c100f4410501c80c8d903074600442010000c03c128007401c00140201f402d0618a880306180300340c003000c0000c041ea81342003400c504001c408010802e080f801d0680034000041c681c3c201001400201410501860f0395900300d10410602805c130440c82c44041c6040ca00510101300c8040c0b4600548055061400242e01d4900000c0e07521811011002c214050210004c159a8010b40085003c0d41c03403c00d001000c81201c000ca0011303140119810380c14018180100159036200701c014603c2d80b5058000021a00362503004603054400031481a120801d9507010b11403a104c042000070407160b20b82c80c0c1000068890448405a880184 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 261116223 1250 261114973 261114983
    0x6110301050f011206150906090b0f031501030605150d0608010c1b1a0a020403140a0305180406121b0602010911010e0f040911130b03030d05041b03050c0906010516 72
    0x401ca40c0c5104591120011b46400d40e02004010040da0009101c4500c038002c2000048400d1000103001542e00156042d62405807026803d5a80d400703a0f0b03411103010412403a0406480c0d000001e03040e2581c2c0380030f80e034008210180540e181c0440000c5001d4860a50080c1c00c668900850300500c60b07404151341e04094840d032400b650407115030a15052408a402102d100105040700340900880a80c1c01882240e1081303c07036001c14540d10000c0ba0f261400342c84003501044040101d0a0b45190320150b05015201c01400051140c0c2c4440764101482d213690350031100f4141d0100c1ba02180d50440001e40000c0200b03200078081154542e444254a0140300462411b0040302d05004000340d40e22154200042e4015000700071150f21410000d0503c001014210700651800321489801012400740001c222000740c019440c00d15903e8101000304001031042c2c0307504103a01600c111441010094000031800b9600410b2410440c00801158900240565040c0402041000e50882c030094517030001607004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 261117473 1250 261116223 261116237
    0x90601030213090c02011e1404061d060c04050315070c0f140609070504060605070804030b1b040b0901080703022514071d010605070b0f0606120a02030406110301050f01 74
    0x1490a100c80b100007900850841810300c01141800c0f40d05500008040c1200c842d03c03c01c9102c4080c0480480300c2c1d04800025018143c0001408a001d0303421010620840c00c0d01e84d50b5003403038004040d06100c0180c0e80700300b080800050400c12442d041140d0840100043c2410586050804024203a1005408000c0c10815214141c006100581c29201c900200c3c21060342c1d11850003c0d03a45440f0100790082c58811071619101003440c5220b4800e0f41d46990303106010901e020b046490310041c0031001482c070400303005480d422041641401c0003420041c590250481d4030748842d10b0014050001c010041c2d0704040c81804041c1000150000c92a001c2d112224031010720700881c01c1403800d90000081c00d05803449044000106007040401100741a00090101e07201d90362541c1d4212641e11410301c01800796500000841d41d502050b92650f40c00c030100400746d61408600309800351080004a03031041c8450ba000c000c00091120901612100303080c4000f1961943d814032001034041d02864280318100707c26 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 261118723 1250 261117473 261117487
    0xf0702031905070c060c12020c0d0803101d04050106080a030c0b1b030108100b030a0b04170c0610050f0d330603060e0d0201020a0207030f15141806060906010302 71
    0x1482c1110040c1d90441038680403103840b103101501c0c4035613030482102c10502c0003011110541c4081010040c5d88002400f00c103904116071240d0711140c001400843c104602c0400010b00756010010420070940032805040d030905c6c180c1421401c407451035100c800103820110300e0700002540491110310f8142e0042c00c54806d6161264403021041c011090300c0c1108900000110740e0480000e40856060001300701480140030000c103168913494852001040140150f02080001d521650401c881c1800f4244290901c14504540c0c3e1030280c0c00d072024860241100b0007800a814601d0118054501c251100c2d04e05011580ea240c0340c2800f180b44100308404060065000003221010b13160b80722820110a002181e1607040c04001801c7c05002001284180b4522114542c01802503030303020951030700503050301451522005064050ba407412030702c01c0703c0c0d01110300030010f452052a072820310114101c60340d4600212111082c4420020341c1c0401d901280c104081542c464440c654414000c1c03a0151321008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 261119973 1250 261118723 261118727
    0x1e03101413110d060b0d15060f051302030919080415020c010210020c16150e09010b0306040b0f13050103030f02030c0304091104080f010c090e16030e0c030706170f07020319 76
    0x20303101200c5d550142070780b02c6e44818880108010070a0024036070341003050340c6d0307030b458488600301c050b10409030000080414100c030540b181c1e01456000302c0080640300722945001e18ae81c9075019842c0200c03600c1c0c001040501c04120010601c2d100f80c1001e00040c480c440101001039134921511601d00911500010000d0340902d041c4111061034100114420360540c4035011a41030740e60296001002860710300c0030401c079181402106048039100c0c0c0059180d900c4641c1408050701d1000c0c02550072011654030510903407210b81c6034441e59905a90001015411482e00600d4035501901c4a41154000d0001c1c034100304000c02202c00310703134405c400042c0150070b401301074140e40513540c45040c0c0303400b03003054410084070190000700040d80e240d51500c2e42180c90750340c40300c3c003184141c03645811446003a40c07000c1403034001d5100d00c0700c0b040108212485030b850b000c0000c1c0b905203d40c21100c0000c40d00c0e40e09540a401c210702c4103030000c84010400040e454440d400954a002d4100c40496030360b070318188100c8042c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 261121223 1250 261119973 261119981
    0x50106061713053313030f030b0a03080c0c03011d0717120f031503070e061c05030a0306092f130e0f1807050f1e03101413110d06 57
    0x10703481c1c00d05240012050b40000004c0d83d591114116400d2008001074403190684501c04c0b10310741c1c55180c100001d90560300032001000d0b03010b12150031111480010002c03440e02e83c0903114080c802c800810082c46410189801d43c4c1c51150040c3e1801d817034040f00306040d00c0100f02001510442d03248950840000c0048525003081c040c0005141c141c0020040c01b0111400c00942c030510380c20a0241c402c608180505a035080789115200d8503000741400704603280f0f03006213005500764908605001c401680d89925081d584000a14030100e80d9402c820041d8400c0350003880d83d10351840850711000c41d007684658000704410480449454400144e05908080005040014050184865910b4036062030411002e0f40d0a4410300035200c85000350006184bc0083c003082a40c5014041841c00d06c65a803c0c41905c5080d09805082105c2c540038924060302c00700302070030700807400c81000308010402c0402d614101c0c038040d001e102c80e54803030390007007010070400c3c100000c000009859880d000c003401d0a140b0001c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 261122473 1250 261121223 261121243
    0x40312090302180c070b281505041b050a14040f050f060c0c090702030904090f11120703020105030414150708010b160212030405190305010606171305 66
    0x500100002450055401800003050380d100381d9800c0001e41d14a036041540d070b401241c003d00800800c10920000400303030001682c1013a051201c99840020480c448000183d21400c8010041e0b074801001d503925070a100a840180020342c0d0801081354941030745060000301d03084450520000151080c8954403803039203c0340b45015601c4550b115901c4030186041e45980f449030b2032141c2011a4078140d03618040080b0741d40305040c07070001c0006030109001c0c406c0d4001c00819400a5000900c0b944a4070b0321240034010220384140d0000c0700e0b40303055140401c0882d00000c03d1038000c0b0300940d1400c284942c0080d001c01030700d40908000b40c585d5a00e02d400b400c144c40c00c03581d102060180035000c0d2582c420741080c0c079014285540f968040d51b84c0340d04030640140140700c0c0948110040071010009070070510030071004034401009992a01e500c803004607502c2600702c0c040c0c140c0e540c0700c51000c2081c402e003842003601a140c64a85031030310800745440b80900f210064104030030155509011010040c08010502c15 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 261123723 1250 261122473 261122483
    0x20102072c01080606030106060e0303031512011d120a141c060602030a0f0f020a0b0a0609051f090903050714150a0207060e06160c0302010e03031302010210050f011203050403 77
    0x320340c3c44100380ca0312040b09407005c5d4025828442c01182a40c082c00d00c00300c6041004d0010b60941c3d0f1152100c2a20703c0c041c800307003500001c807000c201400403400e003e840f07901c604e8501c10403000d4200c5e0010320324040180c0318000300b001f0305000c40a805580280b02039035a0f11024049038403040c01d2281c40401c51082511003104518207100052403d402002811024116444603148a80900e10a40390b01400d801d070707100141c205001c40c40c00204e181c00850b4010a8108002400343c4d11901c48104490041d070b030956107500050714a0003900805005403000c4c1281c5c0d4007c2c00400798036034010b0702c1405824401041003c14a020038446001080850200c00d28100c0409903407d00c00c51180c0294000c1034140e85450805040400d41e060000e00b49000340f5040309801c50500d5080c804480038000e01d60118219503c030b6410260702c0300108040d5000b019189110008211144006840c0c0040b0b601d20010080c1450100200740c0c1c4401d14250440e0301c00c0c00b064000c8800c5290880d240d100741e07000246 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 261124973 1250 261123723 261123809
    0x6062e14040e0403020606090411120a060906060e160906030b04090c030c05010306080f03120601050408010e030318010c0806010e0103020903060c040e24041512050d1b02010207 78
    0x54810030b002d640701d01550007a0241e412540b1203d003032080d820002c54001e030544071104505809030078080c8522001b81d1501066800d070384010783c0e6070000d42d2180003041d947d0580302c44007484841d001c0c513a00c6401804815090b0102d80722040c001e00244c18610854082c160364040451950300c403608a25113540e4401d035268200c1c0e840740340510b100d180e14000d090001c0d01c0c02c1408100160002500010004943d00550030415040100402e000004000c40c0c104071041c440010035680901400a401510fa00619107030700e0700111205075201514800c2106a04240c0040305013900111030741d8100c1020310b010340700c404070740f0f0051303010703105605440c1d415205007010088030311540000342090b03501ca2450024561146483c141d1a40811001003400d8021985841a24503056100c0d0720342c400c00d6042030280e16a10303414100a002c2034003040d640360300b103000e8101c402d55102202038198102455100001c00c09500000e5690340300f8001c01c004049501e80d000036541c04034000e0014800440c2e8044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 261126223 1250 261124973 261124979
    0xe0904060f0f020c03160c030c0f033e04020f0a094e0f081306020601080c12010212040f0c0e281b030207030206062e1404 54
    0x4801407040e40300c0364418500c0c208040081d60704500881d032195041c4401107041100010103000c1e254100c18040340c100322040341c00800540b281e40e01200404240703c940034411300c0c50900c80d008561110051510300e0140d142d0010708900960b1000b1040440d0754142904a2440701180003803003100c0c00d04041038404540c1c003440c5039001c0c0100040d18810003450303c0001da02140c40b50b03001c3d030345071400a15a1540e0000c0c4034004415402c8800002c01008d1405400c01c10303100c900300e400c5001d4054445020016030400c0c42c0b88828510001800988010b015035071601002030340341c1c40c0041c4024460030009010340000d490075010303280036400c10b105421031402c180c50001405030f4004021286216007000005d09004224400d5200c0e416198140c2a0394912195441804005071903002d500340c2d40b1030a85c1800d840130040401000c406d0384005075a0303401c4d428080d2404c2c0008000d28805c588908044c6d59283c418118000c03440c0ca044030a41001c0380d052826070351100400c24215040502103000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 261127473 1250 261126223 261126233
    0x4061a0304021305180708151909020a03060b0f0f03061302040603020405150310020a0503012616050f04050105131d03030a0606030c0203031005060c07030602040914180d030504030e0904 82
    0x91040c1031810704a826042d03445c0c1c81e00d41c8451690300240103c88182c400927410b090080c07201d5900da2802080010040d01e55400141e1407005501305550701c699445c40500581051500100a840101c802040e0150044006540c440004200e007036401c2c42d20700c0000441d101c42d00461b0245600500510643c03410000b06810840030764621480703441583c40400c101d042c41e2088a40e030406542e6843c0c9583c1c21b01008486441c81c0c01e001ca0420081002c428071018400d01105c442650607440504000380f03420100802000003c0650344118a4031004120641d02c6100b0118090112400410f4100f2065640603000c03035246003400032400000104540006141e0100c0c1c20b6030300c00e850800a200c0c003200220780d64042218441201d580d0050240320500e09400176020b020262401c5580e21902c980c0d40c003059030080e5102c0c1c01901d03203584498034844140440c140e44101c145120b8080400460400d580da111100c00c070805142e80c440c085800d042c880c62000306c42d044c002e000720307542e8213191502c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 261128723 1250 261127473 261127501
    0x170c030c0102180a0e010618080d0f02070501020d0512060d02030d021005181009050c060c01020c0609010903050403060c14160c0e060310050c0409140f0604061a0304021305 76
    0x4403080701180800244285880380d600e00503200c070305c494074080f61f0030030341c080d90b00d002d5104104084900704500010030039410015040e0824455070303101404006a940a490034a4070b400c0141903420200040b49540e501400b40c1e034140744007503041c03801ca850300c9011075a40440c07084003940501415400000e000d800142c1e03001c10f505210f1080181c0d945a411024011200060040964010314807840d0a190716401c0251035034040c00503183d401208100003082a8042400715040c0c1e500480d1005001d1000c0c440b55601c0180000240b02c0e2802541c2c0092451149000c010b200e40e980d4a0348a840910800000219200f5a00303800d07614450180300c208000c080250480d41444520004224814034540b1140039800150050814035010060427015100041c000d2010000502000446000358010344400b22510840d01e0128100910700c40030010004020a00407400d01204011146803203070443c0045201c4034040d43c9949a501c0003e0482803007003000d0500394104070a11010101141e8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 261129973 1250 261128723 261128737
    0x2061b09040b1c150b0d11130e0a2a0b0c030705010c050712110613050a050304060903032307020108040f02040906020d0624080405030f0c0706030e0316170c030c0102 73
    0x701200c0340c088004c4c2c10020740714084100b541020f50141e01c03000141d24040b070001c002100a15050b00c202800e0211710860313180031080d81e90f0303901c901031300d105100134640c40d018440102c44162281d0b0414081160615406100710305000100040c80e600142d014003e0b40c0142c0d501000901044190b64401084c03900000026269018903103043c1d0b030081d00491072410113102d508058125541e941542c1d1140080b44103003a5014010641c2e00030000f4401c0c0300a00c041d04990b100c090350641181402002040003042c00816101c01c402102150105501a103421990902c0d050140d540d07945031008a080001d840250013a0502030144200a8650060078000c3d0312103a040210035949e800c02280d0b514425040003102420515182115201320381d03607a03019008008681c605210489601d90b168003010749040560400e02713050080726854002c0d80c0c00d91411800940c18805628200c0c000100d42010007060440051f2003a0f02501205050b40e04580007070050703c4d1100305040e1064081d40c0569 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 261131223 1250 261129973 261129983
    0xf021216020f011b020609040e0604080a030c110606090403031d0d03050a0204050108010302100903080c0d02071d0a05070207050a140901050d080a0e010c02040204150e0102061b09040b1c 82
    0x15034014203544031301c3c04461441c504080844840210f9028031500d607014a0105401c40c0e120030403420041c0080041a018510841c60181e07100b52f194001070440391041d84103000c024508c10f00428100d0001a06500000700f241c0c406400d40b81e42c81c0c03d800929181014805c84046074a07007041120000c00c03a1120810161014400d035038440b9858003c903c9140078040c04940050010300241c01c00701e6202c0c030312281e5405d10002960312a16001501c0e0010071424681d030b4040f508020403264180f280500424a02c500d6500c40c2d0f81c040454810140028842880e0300d0f92180080c012074400c02c40039000f400007800c2580740b02d450710550042c00d420804424000c100383d03000010741e41440c1040c200e80d01d400034001414030090601c12180b02e810020424100300748990302c4005a07607a80300400c010303c00c103d080d98001c1c2c1900000340000810100550540d0400001c10030030840c426080044001035640e05642d4402800000d0010400c09a0480d00502c0c0007010101680340301d100c10716158010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 261132473 1250 261131223 261131239
    0xe01061e02031917011e12050a081b12190c060618020d060519060f0e1806010807020606030309040b030703060e0705090903040501090605030a090b250309120f02121602 74
    0x83d441c1041b003400c207030303007102c803d420b8020007049451391521032104218858400d64401e4501038450040a411a0b825041c407440e152000501c090020030001202c4140603503083d0504883c1100a4000e24843e038410081c00f040154010400004c0e602c6100541007207030f080b01c020400c0000c848002c0d007092510b80c41c01c52800f6030124141c5842c80304401c00c8001c140d406030700c1e1030420204448010010a0300c206020441c503210f80142d0724030a244480300900e50030640e040c42c0c8000010400720001c0d10000a5401c44010300581d61000300c1141c42c102c1041d1808501c00982102281c94504640c1c0007a16603485d0a5442520110108a02c01103482c03c032001d04054846244003034407440b5600c95a80070503454001000b000f8014005107078080429a03000480c0034203034407004200300b000c540c0d62207101030070444480740007a24803112100c03100c540b908101c00d035640e66411050361840355800c400e10010419401003203108008050b00152450725054441d2200ca0800b045101c198204921402003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 261133723 1250 261132473 261132479
    0x1030c02010b0306130317090313050d1115070f06020403021207080706030c0903150902031015031509051606080a1e09030e10050301050a0e01061e0203191701 70
    0x305000d80c02c0e085030014040c01094849003521805200e05400c21010f00602000401c41c0c1224020034034803c0201d24099659840102c0205150b44969000144501040c1928201294641c1c1c0742c41e41104007581e803504004000c40b00c030300707050085010050000c28410340420400030f2980203031080700d1007900c628505240d01000e007501d84066000b1424540c1c0521400c203c480c3c400c2d081008029070604000d13200d0b58584d105c490600607600030781c101e000d4460380100c085040820410f42c140c481e0610400154000016558031510303148000741002e0079200740c036403901d074240c0d026050300350f401021503658001074480c0c4280300c03415200b00b0700828280707000907050b40381e01d000701e00c5264103c80680300c0140b15151000300805c02c0307986c25401c010045114100075111582d40708000d154a840782031b160340c034110030000d0441c0d840e08201d890b0b500b03100041210540001000b2040c0518001c005034803c0b120b00100c1c0765000300302c5200c448982d10000074130310540049202c04208a1898140381c0c41e84c07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 261134973 1250 261133723 261133727
    0x4230706091e06080a051b031e070306060c082a0601170307020604031b05091f080d05190e04060f1e08061305070b03070206181c050c0102090a0306050601030c 70
    0x10140320700c41c04a550000000c032004040d41c070055102000d840ca0703844002483d80b07547c1c901d4100300c800001c218003071055840901c51341c20005910644514052207120b00f407240080c0015900d0000410031480032072126055034400c2c140c251042420000751450b1b122410600780d60b4102803184141d403808034080c13900c9005012045800035074000c0c1006141610b9659541d10103c40c011603010342100c0801c0c00304903541c2d49036500b07020740c58150801000c00b0f490003140b070401c8907035840345009500090b52400b000d80c0002c250381c210165804c05900b00c02102105440381d50383d418425610078940700c000705184500411903c02c4c1c88410000054091003a00110161a900c0c0106841a48941c0c0060840c00034110417442d01d038880d40545503c0c65541d18020000c0d042501c1d124090b81140040041c0586441e4500d0080c0506034002c10303082d0310801c5002c240301c524240d010100b10002581c070700000803d4044a00b00c1c0e40c060803051170306a4900b00071000b040207542a5000134144480d01c00d4a40c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 261136223 1250 261134973 261135029
    0x2090903070309030f080903120301050a06050304020901030809150a090905010902030f0117120d0e120f0405010810031a0402091608010e09070e041124030423070609 73
    0x30b07415200c00002c1e50460f190b04c0c07800c50484504846610080114400d1914140030580040d102e15042c161654104010840c815800f60000020028188200405a81d51441503411640c1250301d103a603400c4000301250920504030000b030b8003118009051010b20b40d20101130011100b0200040117540d0300c030b2040600b0780c40107940b00d281d8003802e04010302011011138000607000e0389003011111116000e211f80c031519041030034200c203c1c50341c4d0440001030600a0181100410031a9081450400e0304d201401c100d000f00c2c09134904104803280000e071320304640740c0c029010390341296400f08501103100001e00c0304030040301c00b00d00560300707500482c100002e682108c805051060b1601030642e03003029903d418980c4000c02c042d10500c5072420020300703c00c8880615003c0d500440a0080051248041c4444205001040c0442c5040c11800380c04500c00741050b0307a00642d0207195a503410203221200020210004420091401030702c900180da15005199107080352031021100142541c2808107524203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 261137473 1250 261136223 261136237
    0xc080601020c010f0302090a08030702040f0203060d0f02151209010f060f060e0d060207120e030c0a051201090c06020304061101020a0c0807050a0f151b201002030403050702090903 79
    0x582c1c81850303030960660144450814160041c1740c01402c0100e41c000003294a441540400100d800006050341541414040c582e880e812000b410740c614100580882c0148001031006001c42400d2090b9900b1540c5d03c180c00d240110603411007586409002136210207030b842c05d5548a819610b04900c249218000740140c0b012500d0f9014620004c602d4200c0071b0b0b4840b060211055440612500403000154051026000050190301503888140780b8601c060100d03500d01814900ca50311202c1102007555501950400395070064441e100b240d00440c0c003181c054900380d80002c0c401d00001c0d8010410b07a5000002c1d20448066030b4940004641f2455072034201e12842100360001160036040001140302a00101103651041c02110000102c1d07454180b24580815011038803840303040340c246500c0c925030003420b0600590710110074040e0f0f0805406040030042103944144094045012100715800384854800600ea40b041503642e86070901d00142242d1110700c0c01c910130880c410204440000c000260785075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 261138723 1250 261137473 261137477
    0x242701020f10020a030615030501050109060908060a1d0105070806030c120d08090304030b07050d0f0525020f06040f0209090313030615050301020a20240912040602030c010c080601 79
    0x10100c040942d1000fa41c00750343c44100340b58403500002000f02a0f5041d0b00403040950760b00164650408000400d000102e0380160300700080d040303003803082c1c03600800d449401081d4803500042c0340000c6016000d2009005a074038803d5407800d020014241c0d00105501c0c071075074044055860b0341007640c0801920020000c00d111141d40410624003901d4051444d140c0c12580380c108607030500c4d980780c0c0c441c05800c8080703032042e00040c0302140c010f04221440c01050082031b084981445a032821030102000c80e03c03820903602e641030a8141c819803450007030180013114904c140c00c0e6203042c82c141c28051500e11240d14101e0082e0510030000f50171090200943ea42106840010341c00c481c5540c8079040609004810804943c806900010395a6400d100802408506031604455440550304844100c3c02903c00044150440311026601110001c0e480c11003d6001e1060502034803201480c501e8615680300300e00c00c400f00040c000c1102a0000090305414403141c000b03015440007940110344409007595001c0c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 261139973 1250 261138723 261138733
    0x801020a021011040b031006140f18010311040b0301140d02090f07050d1a130c0e1903050703030c050d02070e010905041b0b0409050a0506090105242701020f 69
    0xc9144001c3c3c0111144003a544003003811302d9151159003005a00030f48004886140c182020030140303801640c004d40034aa800d1100e0300300114a41126141d108044200e1a8840180b2081000e80c0c0240d0003110b00008800d071241d10740342c841540303407141c1c0c1c000c1c024240c440244514003005840c103d01c810f4500b6901419480150300c6080c4840045140038050710b06001d0148210001000a4800d101050041d490552540c2507014240840c031001030480c030a00c0c504000024035940c2d0031071864241201d0984001400c100c99031007107080914607401c00ad21a000701400007041c1a48100c2c0607001e24092030a075000d101800c4000d1341c1c0e07100325100d00000741d817200c070040207202e040360b001a50090080440c9000b0601c0083c0c0907040750820703041501d26410200c1e040c42000d06a204041e401030072070000308080e08000d40000c0300c11805105003446050340400307000429812010602c03c0e03181d2000da05071240450742240e007035040248011b001d59500b003408040c0c40d602c0091030312469400680500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 261141223 1250 261139973 261139993
    0xc020f070512071809050d090509070906081503010e06040c0608010914010302040c0c050f0303070314061f050705010906060306050a2003090f030d1d030c0d0507031b0c09060801020a02 81
    0x43c003841d8400e13103803400a5035100c0e81c44010a030248800007201e046640da407545a070614041000e8000c02a01e00c50400100100c2400910340011805400c420301a101100c0550848006809404a903030b2402440c00740344180410800d00072031402c00d4a4080e260480c85a80740c040c0c0004507081b0003102c1ca075051907180108094142035111a0323641806240641007504a41c4440e4a4030a04c03030468103183d0700c00000c104040340c0c148584c81449819450004484c00c1c1040060a402d4071147d9109214010001440c3d81d1800350302103900341503008001340040321941c10910300901b06880292003280c2010001094206148901c0780104802c03140c1c4450350104c84800c02d19900020884d43d8079101d45440380100da8010800b800b00700407802400300302122001080c08182070300941c42104c5501c280050017565001241d000320300c5015141190302c8a041c2d0800712181440c4070904804158114500310a0050401004080e00c401013401d10200e56034451032800c0744a1001d60b940181c00840c030701 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 261142473 1250 261141223 261141239
    0x7050f040303120209040213030201021c1706010504181b110a030804110315150405010501050406080709090903030e0d080c090f0a050603160305010501051c05060406090c020f07051207 81
    0x10031020404420018103040c041d1700803074203e9118244443d5001c00010042045690410101c10818084507040803845500b48010309440082c1c941102812000c800003188d503445041a41d000300003000b444003841c00129507000051590b132082d00c0f80007401d00021b45c01e1030300500700c1c404042d456000a01ea69040c544045441090140c4101c528501040d41c25129075410820038a000d0350800e14100103081104c202e40881c80340c40410741c01a41082c0041000340e030080241d0b4202d4a25007000c1000b561a43e108840c00301890708201021460b20320700c1c10074035915034800c220030303042082100d09884403100d0030f803444401185c6d1000c088034204800b101c54107003007104501c003a0001d09a0a04240c03210000b81e10380e00200c800c2030701c1c0701c611011400c070103500d400361900418003800c280e0300e090004d441d5403400c00b811074210502c4e9501c64010603825260350f4000c40c000c044168041104590182c402916840e031220710079071500c61075201043c01d01d0f0007894080307451407410040112610341021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 261143723 1250 261142473 261142487
    0x708070608010603020c070305030d0605120c01020601121505040803070807020c0f040f23060316060f110c0d0804060306050a15030b0112090503070b09030a080a1a0a03050102030f07050f040303 85
    0x11b441180c000c8001c00800513004202814442c0800b400110b0458148010320141e80c00744038605140368440c044c41c48959801040c181e0650b504c4a0b10600c0d14107903400c0c014000600b40d14510350780e03440c10041005024014000c2c501403d503941d0b46c8200c98644c08001c9079225410000c083e07200041d0b4100000030300d80f5500c0340f6490309015001060146007841c030500407003501e80c04c00031005542c004029140c0390074080e101d03c042080c00d1800d20582070034002010100c9004600007400f11401007001e1503002080801e803401c1e40244002c0000442d450f1807400ea400511840020a0038040080742e40c0c0742c8107060105403169198060181052404110003810005900302d0601c140441e080015800324010000340700d000d14001d554402691411b0481c4d02e10013414035105400034001f600000354411b503010b400510608001c1801c005041c4583c10030240341a140c0d82c0071008210000c200081034025621421240d03d0f00007031965481d10070b41d0540700d01318800384011400c00080c00003a000c0e5075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 261144973 1250 261143723 261143737
    0x1e050306180402090606160c0b03100f0602030f070804260c040606020a06020304060b0d0f170307050d0b12100905010b0a050916020309060703031e020c0a06020702060702090414070807060801060302 87
    0xb00d00c809011f40c82e1101e0007032018070f070002ca9000e440003003048040079510b50060020250303407469000031803130508000e49a0061451031810325100148050034080380310305880260460007900350f01074440001b12001100300c1044000c1e18007911840218914003842403004aa40c00e030040d140d4008540d0b51071000303500003801142c0071036032840e00b43c1c61031311450880901c0c40d101e050484602203035030814581030030400210017902d00c0e08104115076139520400f0784002d16884103006c41c28008800014811020304080f001e0648202e801a042d1100c45800c400c12490242000304900c0d02c4060601844021900410390414801c4000c04c06101c0d0311800203240000d02e2040c2ca00345038000c40060500da02c40d10342a0002501e900e90320071400c1c0d06407110344040440300000c40c580355201e1806030b2200c0d6501000f80226038082002c106545412080300ca0322030740140b0032821486c0903d8410404903002290099511503407a0124001000052400981d617051316404000c1c1c0c60004210060350200d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 261146223 1250 261144973 261144997
    0x106170408160f06150f060509130213050418030c0b090712030f1209120c0c0e040804081b0604090e0c0a030305220e01060804031e050306180402090606 67
    0x301100a04581410841d8850008070510b500f4504101054441c0010070400304643d21501704441146032807068201d03421401c029459a4a60002650a0b044c00038100111400001d00102e0721006282250640d0021501005000f0380c000120b40c00c035450741d20003804a41819945c00c00704000301c003000d0740312a1520403540c01da81c03105240c450350f1840030011008140300140c20b1107135642101c1e0795110340a42c0c0c107003000103120689030081c500303260201c1c100a20001e00d80344020f0100080390311f0041c088562180340d06080c603250030306043e48030744510140d9000d0702d068401011420035102494180040c0407600381400c0115900041049050f050b0242c800d041c4070b600f441c0c03240e0904000460007034965a1300c6166400700032142040d20b9449441d1400405804d000e0400703003034103083c1520017518040d006035550380382c140c540c1450f8128240c409020a01c0c810100c0341c0c4000114480ea00541c2d0401c0c0e07039003851300c800f160804290b078020341c400081c400080da20b04115026003442a003078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 261147473 1250 261146223 261146227
    0x40e0307060c051315120f06050603011418070e060f2a0601060504030312050c0c0a0c14090402030c01030908130806061507170304050309040608030307030b03060106170408 76
    0x65030362802211064036045001c182c011903441c1100c2d9030030003000d00914620250132a14841050000c001b6100f06014280c0690b4462406c0941c00042d1b11800241002a1445603203503181d40c1c800080401c0e100c43c0f54441c0311122a14003d90b000c44000b24040c62054031480c29186e1024200090764121141c0314070182c0c818402c40350b8100300d0031010780382c0601c442c40250800001c40995405c00c1816000001802020001040007070f9209080b000d03000804e80000481c0d4442060000c1c071442160712a0401e807043d06549001d00103031148580817103c0f070280d100201e2042809002c48480102c1e80a5415044885030700714650183e00250b50b21846140d0242c508001000502580141074000c43d24540c0b02000308851410010843d40340140100c00d170908004030b9a6034503488440003514104803010105c04242000b00c2041a00e00821000300113000c07040d110380e4000e0762904200e1321400040d081601062403410f0125286043e00c0342661680701180721850729808140c1d01801c122901502 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 261148723 1250 261147473 261147487
    0x70f0f0501140c3a020607021005060d0803010b030702070e0615031003171b060c190e09010e0601200309011d0301020a020a051507020a0f060e060c1e04050609040e03 73
    0x80703d032141d8851420400305002c800d00c4a15424103e001d0584003134150350000c0c0500c60b030240c00244002e80030020510100381617490b6400706450000310600100b40141c04800458010900c0380694410a40d542c01ca031041644c1d00f012264104003130747e80b00d41000100c07503c4503901a168004680c000710145442e044141d50795281c04640e502d4036400c5156050220740352451145908685820360100c90003845075050080c44401e462082c50901c81d40c0c0301101424501e0140a00039400320040014042c0e003140da0340c0c400e04640b400084444a0019914903141460082407528002c01c030302041e00210f0a0506050041d50184601c4207661184140708c66440b80c6903034240004c1c0001c01c04c03035002e80310525503441c03c14a004200d1924031401c7e0700c80f4080025941c0d0009619034804d821070070006010446043c4640101455154407015014100070400c58920070001000305105540b40141078540c400d0f5002624060743c050940d0001080010320740c94038103900700740380a00314041520300d4080703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 261149973 1250 261148723 261148753
    0x30209041b080c03070902070c0b031e090601061103030f0106110102280306060507150b01110102070f030f030c080a0213051315050901030203061f090c02070f0f0501140c 75
    0x1d003035880386141d81d0000d254443e40b800c1c14000e0b200248a000b0056003000c4140d80d4098424182c2d00032000d0603003001c00001c80b0b420808206601d40380039014420480d0034000300083d1a0402401000b0100710b00d101d903180340071400002c8034030441c1100c00c0c05013264200a0b003110ba00c500c0a420301c0c0039640a01004a031050b00e40030148811025254008000b0084100901074600561008050280521006020407241c100350001841000030005505880e0320050342c0c80d0310100c9044c0b186601c041201c608010011130041c0e10039000b5202c0300e501c840301803070450a4800070503601001030702d80d40218002c40a9600030700341c040106405010010f8803070010a5824910304600e00d4031035156070341910f160704407405680c0940780941b844202503040d0b80200c0d40c4c802001d0003000c01401e11540c0c118902240d0500c000c040d0072841c1c4180202902d0760002545c0754039038080d5a4186000f0070b00015800b2040c5003810845c0d8040c0c494111441c030303108a04080c0d4108442d4034a40b8040d480140c80454 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 261151079 1106 261149973 261150023
    0x2030301030c0911040f0929131805150a06150e13240315050105030a0201050a030f051311460602060402120a0b0103020904 55
    0x310101a905000d104a46c0b02c2088030610710801f10b59103540e9089094090312084054000d01c01000c42c5080d0341c0c041c40503069210b007035802c2459031110b5642065004400c00511f4208400311a102c640c107001c0713207601074040344850700104140160144103d002070185241e644103460715110000c0c3c0240710907034001344648102c20b0103440c41016030700003000c0c01d1000007103d08203070900e8058105119503400b04507054407040b010700e0300003843c40c85054100e0f50010f00a1440c00580c1c1c005545950260180100b0143c40d49201d80b91681c4034006d282c018088148502e100006c103003002e2000300b01d50300c003580c46904100c06030b9482140d80c90100c000900700c4410b088041e0f48100c502c60140080c0500e0042401003680001601c1d40c000c0341c02071007a402990304070504041a0701003a25402425001006410b1110040c005420022a040d500c1071003001e00070b102c0303088000520f01c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 260971223 261151079 := by
  have h0 := BRFrame.cov_init 260971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 260971223 ≤ n) (h2 : n < 261151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
