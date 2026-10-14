-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3177
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:53:28.725755+00:00
-- url     : https://prove2.me/submissions/43de9cbc-f5ab-45d0-8008-ba71ce5ef9d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 571223021 ≤ n < 571402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 571224271 1250 571223021 571223041
    0x1b0e06060a0f09030b09030c0c1e011b0f0605010e130b0601051605010e0a15020a0801140f030a140706020c090f0702030d0501150e041808030717040f0c0b030c03 71
    0x3040c03559007820f100e07a2140d5203554281180d40101c607148129000841e4100600f01c04001241c4c2401088920040000b51003628080c400040e20341d9a040107038010310403140ca2020500d201501e904040505596011400c200000d06070a226540718180702100041c00c1e540701c0107070100c101e0790002141010b40c440900446172a0008104c0c0e000e40181c0525810001e0f90901c50b1011820300ca0000d00700700265821710003080880c81d2000070380300f030041003014840f950050b92039040d101c984001000d050501c5000c42c4107415500ca40c80c0d0540708000482e000e01200c902c003c1c00c0030380c005007182c0341c15031981001ca84440308002550b42181480d03000c81c0051090744a0760f680715041e881281e0a003904080c104042c0c800c00e90000c1180e8440c1d4513000442a8400500107506906581c103004c0c10405e0031100ba0765040c00c440243c50480084080f03070250313105070404000380c1040c050604190825003442c07001410041005ca490407580c00c4009041002c0e076007503e101d40c580c2c1d0403440c00c1d50398102510b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 571225521 1250 571224271 571224287
    0xe0106140d020a06031112011e45050f190902030303040b040327030b1e130809030304060e0a06020d02120d1b120e010203090a02040207020414041b0e06060a 69
    0x18090b446d400d01088640b0389080c90650b00030100188001520409541044a02d80183c0c0051141010b000680c00f101424410700414500318800d90480c80140707844684007200c2e0280072000f4540c206400d01261030040700d019030244010b48500c250003907408403000c003101c5030950029050340052000601090366180d6803988a400f904160300c2c40c00100142c00c1c042c22406501040c0ca880c0d107501802800300d804c4080d58846912a6540c10420300c01010070074a840061030310504d0003010b1414800c0020354030a540600c1000340440c1d4446442c1c1801810034800d10365030a0050710b0071540024207910004280c47d05603501d4001d000c49070a0700700040c41d65400443c600740c606803506e03100c0c4004041030512a400f8019507545040980b07041012400f0341d8008911038040c5e81c014800d0094030f48010504c2e80711254102d600594500340c0d44042070161a141d1400c0078099512010442840346443c0d2180788064003081d04001d0a403a00300700c000c94841501e416030040014840300003810300503086 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 571226771 1250 571225521 571225541
    0x45090606091c02190e01180c0c0848010924020903120c0d090f06031e02030c0405190f0b0d0209040c05250b070e130e0106140d020a0603 60
    0x500103114084e0300c110343c054030305900c0440c40700340b010010800421400c4105900189100041c403e0801004000781804120040500549030014030621030401007501e20104a81c44244e010204540c440502e42554450f50052030010361544460b403140010f11030360640941c4502c1d0100e03205a82188003503001444528414019401c105400c01c1d81e47c100b021507540d243c5800590759841241345020f04003c281515001401000c0f8000e100910200401000361a442d1030001500100c00d45542da5104820351615010b51001080c807408072405402801500c0c01a80c0320003401485408900120301240304031149900e0b80181442007080410080c0060344c03464030b007d8100003401e000a411101c00001260200e03d0001d440b80401414010080c00d00780e108000303020001d400e071546552000b0003040c000402441550508440d5542818494810782240d4200804030f204440300d4001e01ea94094000300701e00001816025150042c2400c0140390302420500748035180032410b4000d0902099 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 571228021 1250 571226771 571226779
    0x15160c030501090b0709050904030207060f0207120803071e020a02040f0906021c0501090216080c010603050607050c0601050906011d13021206150c0345090606091c02 73
    0x48000301045090003020328140c024010b1907060b08020f4000b40c8545025030101e07006c0d05030102000040ba40105583c001c49001e800c02d50a82ca40b1a08100c0c07d18120fa001508211590320b00e04d400e001207080a1442128142c035144450030b10441c0071102c034900b012a600040c0d006001c11001410300c0e812401110000003000314590100d5a5100282e13008a010307002815501c51040c91228064026617004011001c002c5182c54032004858201500103200076002c1040000e01d1601039909500600080d5042000d448842c103000400900b01d070b004080e01c012502c00e0038004582440c0980c1e03524000d10050f1190120a288042580000d1104440f03160b840704000360035041106140c001042e46200f0110041124a8180100482c00c0086008a20288418420410f88010000441e02d032000b0441c55451003850500000d24003d090681d403030088403405a500030003d818036014407105030111030651440d5a01402c0c0701c224040c141c039165100702e6024080140c5520800203401950000e8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 571229271 1250 571228021 571228043
    0x30b042a060806330a170a0c03150501050d09051c0c0b061009261006030b0a09020a030219120b16080c04090f110406020313060c02090f0619060206090c1516 69
    0x2012003a80700c0e01110070f840303202c0c3c82da10348d01c02c80c3d9490b20a0480b0713110001d01e03103041d5500f00130000f0954000c3c020400c5159039200811000e01504201f400f01d5424070709006810300081000042c8101000c42c422038000001d0800f1411b945400700f0341c0c56034040640e0740c48201e6440c04041000f40040c241d030000107502d029500070411002401a525501846500412103d285180500280200902400d0024501164140140d85042c41c80c412030360100c8120041d4681c1100180c100c440356032140c90b01014500c02d0310204100c0c6c1ca4014890481403c0d203c24031841c3c0c2c1015110045c0854405183e882c0411044c45208040c2e8006906036510040011f041481100d0b441c840740d10031f40040c00980c1c00401d680b08420420813001015141a14085a200c0ba80b0782c08501140300c0644901d4115409000055450300d40754000c050100c0302c0a058070340700307580e5078000c0c5d115682a1111003980c05429800c0c040c90034400d901500402c1c041595174a4158148801034000448400032a200302d02c3c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 571230521 1250 571229271 571229297
    0x50411040c05120108070614041a071e1a07020102070b070f0e0a091a12030a080406270507060507110d0f020312030609010f030b042a060806330a 64
    0x507a400380c600b039002801c102c0d01b043d0018107240c40310300b004104123000300300071300614400808c11800d82c2501c08a081d00e94601d071900104441803850840707983c4c1c0e800d071480001c0c4141d090350a40030306400d83c01c5040c19100c5c0705049082c0d10421901502d0320b40844003191005204051541801c1d000b480c101040c01c2ea560b001403805501c40e8007143c24552144400c900f02c10030705840303583c150001c40d03110421400c0302404503100c1c000c043c010010320450760006001d101c032a4010000e1042c10f01a9120071520804c404c1071349001c1c05000703854510440303502041441c05881203a4200742c02881e0070103010f1000c41005103103040004112a520400880a00103840c1044645580100c0e6152181c80b0310344941842480c4805910460003210160760800c0800c28000c00150001e401c0320070380704001c1052240d0740b40001c50400b2074851540701d40000440991001105004800480c1d81003802c4c041d10020380700d10802d00390400448801c54010104100c3c41e103004183c00032150070850a10040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 571231771 1250 571230521 571230547
    0x60b0406020a050706030603170a0509040608030a0f05180925110d08010302090703020a1110021c0209100f110601060306140d051f0209030303091609050411040c05 72
    0x2103540000c01590080c20103104010050002001820880c5010480c1e81c5c59510765001132616040150042c1e00b001900b100c400b031082e411509062800351090210f1303556135901a5496110358180400182213011801100c3d00c42c00465045004500d100240d941c07681d802c100d410750010b07202029038189035041c1441811341c10070080140000782c8440c1a41da03000c000b02400d115a1502c000204006000140f006a45102c5c103941c00004031702e40142c82d00072a60080d00c41c40075404202c01240303d00344980301c080540381c0050012070b500c054480903a004009000059000d00c1d0303c0c1c00d500c5290359000301c1003540b048694440349001440c18040c104004403a081c00c000e001c1c1c005800191b00d41e0000d00480b9500b003190b9200000503604040c1a420039215551541e1100ea0690044407280e550314900400c2601540d5840d2300013003d0f282c0e40d0070f02c2589142d0750301125101a41c14841840b00103031100e41480b87c40d00c61030700321804981840e0940d00b0000207000e8504902c0c10b000003406018060b081d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 571233021 1250 571231771 571231777
    0x90509010c2a0c03032d0f110c030a0503040911040b04031410050a0614030c0d0209061908070e07090305030316030e15042a05060c0a0b0a060504110313030e04060b 72
    0x80179442c4c4100202c0c42020700928200d05d03030141c1d0720003aa98810f0740c000300c1d4040b8008840d554189044901018054807090a19803000100d66040c4502810700081c410003100034800c4901000c2d003044110f66076000d11030b06010f0b0f4406c600c0443d1b420f20042001c107400d22600321144109134103030341c07804d104e94100341c1c02c6500582c1d007800100d595030010300108d5100c12a6822210f0300710000d108885100c000200d55003c2544000d000b54010b10101d01542c540c40711a14449001d0b00c1c0c10640d032034450910b00e0380c500c0c2034030401040c0340200020580c518054424502501c0e04600034602e56a182d03994803080305c0145100e03004241d920000c26245102c00e100b0310040ca40710107807184540c2004d0511082000302c0c02011841460040b0203211245004075000f000c44109942c15034540010340130b141c1c2018441d00010f000340c2002020044031440c0c0d5481002610000c0700c0400c11058003e801c40e80c5030008407120050310044c82c464030b000c2406403c03040310305000284045425901e8041d108e805030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 571234271 1250 571233021 571233023
    0x10030621030e0414040f05120d091205030f010b090604121b0504050603030406140c070e040c060504062007170109031d090601081519090509010c2a0c03 67
    0x1440340305010101940422910741d5004101d90038806400c00030840b40040c100504024190381400d480d203002c0003c00e0143e0907004d5050084580c41d0f21a814000c0007a141c0c0301000c03140d0602e20101caa804a00580c181c90142d4a81801c0501c980c0c02d00c030402e001d59104449007a070002041c8400110103071015081080148901e20f6410301d8071018501c03403403454594000c644150300b001c00700304003610004162400c960b964a4506404842c20000b91203510510211a1407400b903400c010070581020000503004501c02c0a40c01c0e0116550101181c85000b070f40103180000300c0103000030080e030300380052400c000010f180a480d1150360381c400340407442c0105507411070640d4641300002d0501d0341107040480c902408030081c8080d5428600051401e400003056181401100c0c404038909400701c8401e902034003000341c586110f0703000a00d1071800c07041c40c034856030340700380d08001c0000c540c018180102e02c14280503441d80414100240d00080d00c455a400b50402d0103171031ba02009000c98054001c81c0021 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 571235521 1250 571234271 571234319
    0x191707080304080c070f090606020d2307060908041508011d040f14060106030f1811061b0d09050f121518030d061a030c0901030f0e030c0d120c020309100306 69
    0x7441c0c549c0103400c0000e00107050b0180308402031101c4446240800c5c2644030004000c50980d1004d152400b80000c3c50031600140c5010b5020802054000340303a0142041810f440c0c80d007480c20ba0707075000c0b030340103888c0c04180d070440e001c0350200850001002050071509841c440e0b440c0d03090740701074405ca403271070704074243d0196001a495a0144c3e0741607038584600c4595410750440351400b1360254689071860310b0044610f5014420000398401c0a000f0705144411529080096912082c1d55460080c0030102502415101d140c042c60011451b00e0034000d0b000d0036400c11005044040340c0301c090400502401000704040d140c00051100f10720341c2c10302c000c103132070865103200240039800e15110f100b00c0040c2000b8a00c3c3c0e100100b0900c08841c00c07540030f42d0380480003445c011030007100022142007e0120300d000ba204920002c2003a0102d0a004111100e480c034990b500d42d01100b001501c0c4100380c44900e621075025030010400c5030624148101c030448112107500b40890b1450b51205582c120981040411803a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 571236771 1250 571235521 571235531
    0x60d0902121204031b030203190314040e06280e040b06090915040f150c180f0608090106030b070203030702210d02090a08191707080304080c070f09 65
    0x4501d00701c0d12040014035210000c1010580044101e0414492400090140c001d00501c406408070601441406140d01a050751503035417081c1c0045801c42d5a1000403000b10740c403141d10040f0085a181900c1c02c482d45c1000024241d02c400c001d020105480076912020f180c0d0048124041c00501c0c440c04000b0300004031280010b2a045c03c24543e8600054240d91080d5428404c1c42480c840001d02550001040c210b000d0301502c07149052211001040401409180e044090b6101051958407400744600c0a40b6640c413050079501d0042180e00d018029a80d817624540820f000482c85003843e036600c004031000000708182c0300d403034910150001300d80c0d10006901c000208201164140b06018040b200200081c0c0c41030350100c03461071540980a4203072800c0341d010442004a07942d200380304008000c40c4080c0c440038041800d07040101c1e00f2290b400d540c442140c00c2c04500030030b500011180381e65004041242151102c0c1e42d81c524540c001c0b14041d0740340c80b40c81404150401244503500080415910001e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 571238021 1250 571236771 571236773
    0x250b10031e030504031407081b01031a09012d0f0302270c21010602060714070b0703152403061410050a030213080708010e03040617070509060d09 64
    0x70803603200290700718028400c4082000002d401805440a0300c0d40030f9680800080880fa0441c986201c9138803040c0d2511a98030803410714240080e1090f5036010a0b038080c8402c040400c1040c501c2011600a0364029078040010060044803000000300340b1100c40008440500019a183c0c1154241d00f180d0550705052000b002189410007019800111f052800b01907000800c00800903d44000d1069018a42c001510031003920b9440340007000080b6080b004402d1750311104000c0d0340384001c665038404180120103e0442c4580e110a540b00b00e80c1c0900600c1140d9250002240074086d8a0341546101c3c01a030000703d000d014043c4100000c076201045140b6440c19414014180c2c0d10903400700c032000010300400282915034003414100c240d2581040c682d200c8549204600a01c101e140c0344e4038945e803480c004210050042041412991154000c0c8043d858020001d40c891065200390000304286107030074080c0d5048161103580c0b140007414150b041076060404a00164046a80c00078540da6405601c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 571239271 1250 571238021 571238033
    0x12030e07180b0f1914131a09012306090a0e010b250b0a0908090307031b080c030d0c03020a0204091b061e05030a090c120303060b030c250b1003 63
    0x10f02030b8049800c40455a0020f00014940005000e103c184286080c84e9120310b46070030012802c4c00710035480821400b2125005402151400b0305402d00c1080200000280d000020306110942c48511000600003002c05080020079484061940d400c16520000040c1200072404c125000b0030100c1c81080c0e952115808462100003043c0c0a002e403241c0b41c404e0940840c800042860780110900c6000030740404904005115005040c2002c0d40751084450200030032169070141035116045458260040c0d498819440d01ca1543c00305294044c1d015590240e0814480e5910b45549070090040e0380002440d5004281654500c8505465020a03242411403043c0000350303070b100070000ca14110481c45101d190b500c0f00e4800c1e00c1001c00801c0804400314026407610350000380039984c0012100f80b210f55800469680d807441003c00e60100746025400036014040720100d03403040740560340441c68491550740900c00034030380310301104941004c1300580c40092622450390380140d9028210224003451460700b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 571240521 1250 571239271 571239289
    0x180b070b0a0c0504060f0309060e121e190f03020f0a080402011e0e0f0f04050f0601080a05010308031810150f120c05040209010203280807020a12030e07180b 69
    0x1441c10084204400c000e1715500c9140c040b04a1807910780880e41c4101405c040d40a411058180301c00c9016151700d20207501c80010040009941c1b0004007940c00318034007141c034410300901c44510420303030f40e404003100c0301807103038000f80d82051050a006003041400350480c00181c11000301030021440d07082c2030006640c0c10902d2030304495811007642d0610514490000c02d1a8075020045016100401d16481c0a0360344000c01ca50b1700d10b001d40204054902400d004006800079241c15020640c240702040c0341000ca40103840c180e9400910076403454039041c11040b00b1a20002008200380144420a81007a8040c06981c4441e0313004840130300503600340010140502c0300d07940201e40488074042d611000501d83e03c1c1140c03c64070211401130b01d0310312500040c0c3c1548200c0c044e151031640582c865101886010b9442c00d120041591030900940d40c4004c180d95130360241401401042129203650426031181c2c100f041ca2002035003d03503242d641e0352100350a050090381e0f0000080d5480e8800c040c1c2c01d081c07401381c2c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 571241771 1250 571240521 571240541
    0x30402060d05280524030a021314060306010b030103172109010c110c10051c09051b0d1121060103150903050711011727010c050a180b070b0a 62
    0x801c0201d4101024404200e1019103d681050b007888010400d03151b1b018003031121400e402404840044c505040c40e0002403551454056042400d94041100381c100064014103941010903010720b10b90840e19203042c06c0c07003185e07420210080704201034429900d110400542c00c5090b60340c03a940d00d04001d9500b03400d507050800304000f0401038480306155080005034180e0002410345551048070300a50045501e48903400701142d00403042d617007103440041c1c02d0f889103c05a00030400e0361824040c203c071511200108041003a07009884807412004584204c802095030b1200400c000031103648101e4111660124000c5801c1e250080b6004006004101d0f019440050481904001101080c4d5024050707000d5400081c0c418440740140c401c2c01d0340100d840c055100d010300000003aa1902102030402e000980003400560020207100248416050042000b091b01640344c0c0e60410a1441d001c41d402d000c582540700e00c07000c0c2c00c0c000144250b51400104041405038241c20b00924040740d55506a640b074510b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 571243021 1250 571241771 571241851
    0x609090d0906050706021210030c050105030613022206030c02071401090b0c160b0c160311040f0b040c03150602150f07050720030705010302070206030a02030402060d05 74
    0x10860a99a000145505449450605135160655818500020b0146140350000f02d040300d001e12001217040380100d4100d0340704103203070740425460306d0046540e40070039155507030020b40d10320130340001c001c040d00a80740c0500e4820000d0031880e0000f2030940c601c28903510a00c007181c2d0340c1a5611203564140081c20140c13000e20320700006082d041c40002c0015501d4860840d402101141003800031030300b440059407100c40c0807100300415481c0d0007500b0080d80305c1310804095110b603000101c031040d107003580c2c5400c580d0081c4100304009504003e00c80070709894061040d0442c0c3d281c003120429a520300c02c0c0c50188200355030015032000701e140c0071400d200726500014250b600242d0116480344032050150707485090600c600c20a03466148043d1094012440010590780304503181c8008801c210541c3c1c280c403c07080782100e4000703943d440190100d03c101c50700690084400c100140780034032241c000b150043d101a107086c0c5000030104000045400683e910007550051085130b800c4841010507042c00040c0c001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 571244271 1250 571243021 571243033
    0x7061d0d0623130f0c08151608250c05030319050609010b0702040207030c052506090303020703020409020a170327090403140d06060503061207051003052508060909 72
    0x50119805803aa5500501c0207444c200e083e42001007007080b65008200e180d048540c20740d640105517800040c100e8040031000101d80c40c83c4c0c0d03458450700c82c0c0d50003800f640301500c00300003205030020300d0040704032500c0d82882070350964a000203404200540c861440320007908695520311404500b80c1d0409005a03102e09a0b1000622640800200b1502600d604070340050b5504100e20302940c1b550b248140190a9000e000700754210306003140d060803420302c00c07191041005c030b886400a036012403036400040d005038003008041c07005040990150820070b00040040030501d030340b0b0405113280382c604001e048280d0800b09001ca1414050b6040340d000f80d5003130700040320070802440400c409440042c0b000d4200000745007848030f007400910803210506056682403142c0b07500d6110240003980250b4101e80506819030400d040d641002c2404410b60344024140c500041d10032208402030800608001d0f0700c0d801c510240e1440312172125007a26206900c1d220755145250500801000c40001005029181c00c50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 571245521 1250 571244271 571244281
    0x1b1206050105040515160209040515011e170c091003030807080411040c03090602031003030206010b0c1c1e121508120c0f1014090109030207061d0d0623 67
    0x8881c03400b03181720702d02030558440c2c520029880706001c120380080e410108490a110520101191700f86c05003d0707100c1d481c0780e141da8410b41403406a000c4485200c4c0182107030400e022000c000c0da00e02141104000449000e01044400603110420a680d81480d0383c00c0381d48108101600000f510b0782c0844241850f40ca50302e09500c8019404a030707a40300138412643c0b09900954240268070094140c4c0d08014219180d10300100421402a1140000e40c098441e1600020301404014100d84140000c5405042002c1c14550144031903501c1407450300600403901c2d06135004600c1c0c0c41c42c410140b2015175070381c181c1d2060110700100321107010b0441184c000300310f002800070500000b100310420301c20320051565099540401400d0941150940c0482e0003405800003005400f40c11010010700c010802d00102e80310303c203440f4203c45400c04000c025800801c01000301600032003203144030501c0d4400660051400000043c0064044035080310065600c00780b030001860300a0740180d2810800a44860134201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 571246771 1250 571245521 571245529
    0x60108010b1e09041e0204170f1504170708070c12021509030c0d0602030703060605030f1314030705150705090121090203100606021c1709011b12060501050405 70
    0x8081c1c03880b01405000030801c00c0c07921583d00a42040c1d401040400c220820800f907000a503106101307421100001c02c050241401c800320b007040c2c071070710803170b000b00010443e40011143d01c40c2d004000362814100c8182110070300480000a01801d8490f144407603840d10940741809003407003d50010b64541048440c40da00686130354400300000484040107e4070741d00c80000213480e2940300300c00b07036402581d584642003c01c40305801440c01940240c5092250070741b90308044605020440d22080c0604030341020034950b2490a05040700a401814038481c00280790300c0391440c680c031551080783c6941c0311200c408600e01000e89100c0d004166071078998a0156401c0009188200c4120001c0a161001740b01180c1502e4940c0004c0340d0540c0075007961070140361420400d000303020900c030b03040c05802940c14001c001d801c11102c440030380a003501e50340d840c0d03419418400188100200981340d650b43c1c1d103c01030300c03409402a42c815003281070754698640008120300082541d64a90106051050a000c00d02685e0303a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 571248021 1250 571246771 571246807
    0x21f0e0604030c0510090309050307061b0b0403120c08040506180a0803061306060503010e01052b06091b051201020a02190c0e010603060302041d0d0c0623060108010b 73
    0x18151406581d101d2860400605042070301740c1541209182002010401d42c03c8904078003250001c805441c2101e0f600d5805070341820000c00307080b2540e040c07514010001484400002c0e0440c2c06882c084041c0640c0c0c0c821401103851b24600c40700400d0642c0d00700820000f0030481d80b40e0020351200380d20300c00c000c0c064038a50760b5440c0120007011480040000350791515411400c0f0101d07001e11200740b0a081e40c40402800070b40c42030080ca0b40170700045001040310b08041c00080c0318484008a00c10001c2c05416000c042c0941c3c05404450541d00c405d04000440c130441c890205103156010f4000030075182c20104582c540c5215400d107003590061180c81406900400c00d40c0c1030146845910645040903d4074034900ea503140c00c5510840301c03440000c0b405a078947c1c0a24181c134402c3d10300300139043c02d02881c58889403250ba00e10003964032504001403d103110780d40c0c00b1520342c840c07a000f240c0026400c0502c0d04540041c81414031840c0030f07000304a881d41c1e0010860f07006010301c00c8407916045c0d0100c00c003042c42d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 571249271 1250 571248021 571248023
    0x111030c0a032003090609120d0b060d090c060e0102161a0d06090f0b01020a122102030a090302061312050a050c10090302071d181c021f0e0604 63
    0x10401041c0307294450b00940200414090241c1031055499280c601603010b508260380c0d4803070178400c2c48002240b0080c00510782d00c1000c83c44a0a0342084040c3c090364000c1c0c0300d40803400c2c0d0451001d2204051240d0a805940681031003140202200e0b4100b003401040c01c0e2500c1c070802d0455210020f141311100555602c541511201040e1408101142460407040d105110b100010946009000101d0200c15400f9208000303040c00c00b441003100c007100480e9203c1c00d801002c1c14400e490802d48907820b00658080400a668140380e805010480c0e40ae041240c02c1101d491070051380324a002401c1550600c0348a6000060000c04040400b240e15810780320752a501c40c00d0240180000d40d40300007800f072402d480040c02e210040b504144c3c0481090340281610b404102e01600c41c1d0701e07020501900c10380390100700301a1014007a102d940c03030b10400a4100d2020100c85031078060a11a0b0404050149076a43c51400d107800500850410030340340b40c8041c0c40c03500480c00c050f1038034841103030034071010941940107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 571250521 1250 571249271 571249291
    0x91e040c03021c0e071205070e060f0108180f1005100509040f0611272d040209040b0402070c0611010603021e130c0c0b0a0b06041206110304030305011403011103 71
    0x1604c15640b8182c5000026045800044450100881080b03000203da03400c1d200d03100c907642e1362174070b81c501809201c0007510402c5001c01d50500c00140d50105005240340607007041411a00b01d40e50642c190350400000604401805403a0410004001d40c02c103152001440f050384e5042440c41c081d00c885070a10039441d0010b003059140c031400b00d06a00c0c01c00503103903030034000c0c2840580204851202102c82c0c103013010060048010100040c8024480c2d101141c51903400000b070004e55031403804000081d4010324a0642c001e599908999040d1620b1000d41083d0f8452a03210f4000b41c09d0050180420b0381d58a01d42c45181e061050510042e01c0d4500100c92844020180b94464005c1d803000400881107483d020404d00e2620310700040c8240d105158001c0c090161113400015112040c4105c2038640c0d41040c503800c488104420411403160b200c261003001d0041f00005650100c1d0a1002d16580c401da038180c00081d01c842c0144451000004246000d00c402c4000b000314009040a8a402d1b005c01022211300e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 571251771 1250 571250521 571250531
    0x1060f0b040312050f04120605090c010219021201060f061b11090c0d090c21021c1a0a0227011d0609040204081605090c04030b0c091e040c03021c 64
    0x1442c0c4c00b4009a0b900601407118007a219a25042102654031140c0d0064402c036092001081d070599000c6a8071051704011713406080d407a846c048a84c2c00050048070f08a8100503641d9241000700c2c801e1084102504041840072003461404100411441004002170140180500181e0016030710300100c3c01e0000b0f00b43e4054201c0d94403807a200815000e544e04c0f000c6540e080404140422454100c804c2c1500c88941440550080d05126195814903000001750010400c4610104ca00004030007400918440c661120f05007001842d10310b20600e0035101400d104d0f401044a01441805d0000811602d94041d400c6a010947d000003c0c82c5aa54480c0183c1c241c080d640703409201d440b1070b012140c0c07480c0080c0081d0355031903682c00000d03914480c0201e203800c0c00141000200d81440c00c0c0c0d40480c0074602405166042c1411600da92042e0300d005800501e03540300c03c1041c407056031621580400545610300707880c400d61441d001031009494124081d81d080520410880c070a610700150150300040350460300242e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 571253021 1250 571251771 571251803
    0x106090b0720060a020105010302010906140906030406090c06081e04240204050a180506040c0f1409120a0303060602030301060f1110090f060614090604020918090f01060f0b0403 78
    0x82e5094041052540000000810f504610b0b015001281203074801e903a1110584d80c0d5100443d18100c500002e500741c01e5007044590f01514090000d15041401580e00007550002a03842a003040c41940c011404074601a0401003c880c40c42c104c500d0106018421042c03d01d096600c1c6120b040d08a0001129030f1609420200c003100b450381981c0180c400a440000310075100c888400e0090321941c0035802c00760400c00000c010742414000c2d1512141581c845e00d05c50509020301742c45c800b13210502c10384800801c2c800d1002c20303610813107410b681c90080301c003402c40350030b0f581030050584800760002d1081d940204010007200742d0000c60010070382600c4c68020900088801d4182c10441d10b4500c0781c1c1010308180c415001c0c0201c131311542d201079100300c000300866980c90404e19090045d00400d00d0744400300c20300240d05410950000c004500c0700400b040140000c10100708074166084d519944568400000040450024801c60001c2e2502c0e002c0f42044501d015a80300c6a4412400020003210485035401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 571254271 1250 571253021 571253063
    0x31903050711010606030b15040f0e1902030103080a02100e0601062102030703020a170105090f06030f072408060f010c0c0e0a02090405071817070504050c120106090b07 74
    0x1c1c89042c040c1c0003d10645540381c2000300542828020140318040000d0f02952021500d0304440031500001c8074041a94075007008030010510090036804c40a070800d001c86071084851000394060340c41110302c1901c40409090080c60080500c0340c00501301c3c54101240140d01c0000744440c1180c80303514000440d4880c0142d8611252240348490450900200c00c0c44040c903010780141c440000c455642824071280d094020360810020321a01d50001507800108907550020044c40f0740c8010041c044600f01c4400c0c00c0303080e15000480c0d01c10107003d000300d41d4442d0595402500305034002550b00e001d80c1641030450001c0c0081e103811380711174144010031264100304980c0f400490000c0c0600c00c803051181c90011000401303544203400107440b031407514001030440d502820500e44203500c9106941075040c10305050b0b640c81d03403400c18501064411410002556070311401180c0c8101c4415081540312500300001c4c0340c0c107041c181c004506002e00c80c1000d01c080c8816000307079030b03486411421548510b03c05c6a95a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 571255521 1250 571254271 571254287
    0x2315060402161226010e0a0204080d18090209130507090806100602011d100905030d06090f11090d110d02060301060302070b15061c180f060e0319030507 67
    0x101540035040c2c00700805004209403826540003183e100e0b024660300456010701403822180d40c5101c09000c0800502c40098890511903024643c01001450305440320700b4a450074015805078030000c0c9200380c2c0b0b645800c0320329641300014001c02d00709500742100c0000055064202e481410b002ca41d540c1c0003d00143e220303554400007002e021003543c0042c00d2242071085004100d0040801660919552600c01c1c219050010f10701050319000e000c90000d950903110241026843c01d80322413200348010481c1140b0b901c100710042000050000b000c150311035099003510840c850014000d0000e0044621a84403144a9806aa400300100b4035140daa5000035014581544002e9007001c000b00010420300c0d0194005d00c1003078000c010b2000c59941e030900d201e8049080001140d0403920034068025101d8020f020f01d410100380b040b01041c502c0e1000b8842da8405544c0c03409903400e208a40c0401c042c8601445244200c050103006141b4050000121352004030320504510101951600010b400520036601 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 571256771 1250 571255521 571255537
    0x19030c0e063a05060a060c0b060d0c06030902030c030601210f06050712051b0f0a020f100b1008070912050a0203010f020d0b19060305070207081204032315060402 71
    0x905921209401c2e40d4011444400c214894518a0700021460b685054803c8008948595171000503608456450400d04a800780605400c640c920701c100700000d03030a2424001801c0d10707607000580500c032401054501159407100902a81000c00140508001048644c510038001c1d041880402c2721850803440c5101c1c00741d0003034400340c903000c14801c1e801d601c42155589800d8642050000342c484400f64003089034140320b45a02c0000402104030140c802c040500751122060050340c14507030444100d1402e1071004007a10341120b95810240182e850400c09981c0ca0259a1400300901d20b058600030b80b41040d0ba002e1154104803101c03c5000b0480f04100402c0a40d5001d00248500e21a10703072400c0c041d40103812411141c6040124021f580d0505003030b00f60f207031092090a030558a190040c141c000b00005401c1500714010034001103a6034a0801802007142c038200d60304d542c0d40740345003008061401204e5007902c0380152440000d00d9510700244078400200e0300a00342d00e546d11000c0010b4024071448070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 571258021 1250 571256771 571256827
    0x300915020a02160510090e06030a3f020a11062215020a02030307140a08131e051806130e0303041514040605060307050d060219030c0e06 60
    0xc0e807a41c0070354040b404007042484200840c0406032184100b100c11924100e0703020001d224000c1c1040341038118858a80c01810142c1a200c059686481c0c054009503d140c407981410385400b440b5040c0c00c0ba0202000322442080c0c0c2c2001d0341c201c40315009441b0040f5a0001e025101280c904400e1952100101c600640c40084043c0030034080440301803c2841030311480540410b80001056810f0000c124805a00d500a010710b00d01003480e543c1c10360078140d1100c03d01151207240361013400a1107840041c604007a80b44119190b007031900e00c501a09600d22403034425060380c0ba0104005a8450905c41e42c074011800c0c0c03c004059071158089030341c010000c14420180c1c1c0c10120703860071901000c001980154000d0300c2520702c080c102c4075807070141c903061048810101900c0340020041801c95120b607800030001000c0e1880503950f40d000503100d4034008400d41d861540060511550040d00c40d192420200c503050600c0f0210a070345018190b2024050102d0084500052001040b880c0c41520610281001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 571259271 1250 571258021 571258027
    0x15011518180506130e120f0f0c031b0d090303032003011202040506060906091003061509080118030915030f1103090706090302030607030c1209050d30091502 69
    0x114120007a200944280340140e5185106101855440c0518108607017030034001c246c8104000380241d240d034072222a50f0f050190034095071f243c404950780145041c0d07204800039500d4401c1d103600800c00740100f2220181503445a4203d1451039041440d04040380d400d0309000075903c4032021449400003034801c0c074084983d0000004640074040d854a0040c66000fa141080700307a80314420302a8030312640720350313079406035082c803441c1503918010045144054049c40d000c1150f030750390320314104000700d402980ca020510b030050038024a0780910441c888840400d005501b043c0150300c026010640d14068000368104c1a250640454040c0d0880b500c000c008a000b004022801001181c051b0425a03c800007070190f010005462403040652000b41c80c1c00502803e80c0e602c4446054009241305e0307a54405019400c52058001d56640c8620302d0080e0280e0090030a0034009100140487d5603406181950090f0f100200c00107012840c54030a412100d00c0000340750102ca040000c520300484441000140c000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 571260521 1250 571259271 571259309
    0x1030507051216020f0c030a02061e0708250b0a0b010903050f01052e06350f01090903020318012c040b06040b03131103030a030e15011518 61
    0xf039a803880e40c0d81c24070350030340302c2c03a4500081c0207803511402c1016581c5540f00101100140c5409002000e5290341c0c0f40b69920b004001c000c031175910741c0040301c059445442c0843c00c0c0c2c02601208008210400e04a039200c404407a13295518207403850041c002d0070542e503440091091507402000520080c5801c071084520601000b500c0343c2c041c00044a109982d43c20048010702e45501c1ca88608501010300d8418141d50782c00e048040764013240c2c801851755440310071100d0281780f00c1c0240c040800c0342c0d0710460101880c23034000c007844140700b8181c0c09039408601c0d00003420042503000c03056a030540701051405a400b602440120303140e00d01e058071041c01c000f00040c0c4103400144451010400b27641510103000d0394805104102803800740e4031500702030b40020000a440305422041c0c10315141e11031507044111900900210385160000ca10650200e65181c010300894601000840313903581045081d90310030741c10708803182075140c040c844003011f0000e81c03240c8240155485c40c0035406844810221380b000e01003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 571261771 1250 571260521 571260541
    0x60a2409090507050d211e0314010e100905181614010203030c040e06210304050a050a0311060309030f0706091209080325080a051218070302010305070512 68
    0x69044221103e10800c000040c103030900310b4001c00600e40040607617502041c50000300e18025580e00d0281d08220b0003001c10b94a202c540c04440c40e4451752030ba00001c1c800b060604100708010306820201024880d242003020a00e4a075040500b90f1320100404565521400185440e40e0b43c82030400d00c2d90b00074080e06500034811003071080e0840d014410018840d04105d4016038484c803055580d000650020401031003001036030b5440b903030495009000c1c0322540710f5207200000311001c005540305264000180c1000189048069500500310803100802c6c01881c5582e2285006202c210003409600040b0025404000c103000307a68586140d403c2190340c658280c90104010a0010000c0351960381c1d002c584005140700d5801001581d98070710042d1302e480a0402d0308501c4030305050320612050b0340c10039140c000400c00380c0503202510341515802c3e1548041c81415a80d034030021324136118040942443c0203000d0000814030704582c0c0a080008a5440d241c0741110103100b4113002c40e4808868405000302d01039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 571263021 1250 571261771 571261781
    0xa0c1a0106050c060a0b030c0d03021905010e0d180504051905090d030615020d0806060403050f161205030f030a0f0518010b0607030914060c0d02010c0e0f03060a2409 73
    0x1082030700b44c4602c3d0390f03580002ca00b01d03889149865015440b170303500f001a03400c02e0a91405014007900444110021700d2070381c6944c03503000500c1242e080c2d44802c80481605400c00519188292508041114004803400c02c11813145510815214580785d502144101c4565940e80311810754034070b4181322500d4102042170b5904042c5203580d00080c500040043c0f003002c07420545400c2d050303503170213024a4004054100c2307030b07004040c00003544a00100800000284108600d07171303642030b10801506090a224110009580803640320842d5900b1a1051100060002c0102c407c41001304034482e0320303a19204900f00040c0700d142a09110f00745408180449000600180280290103000030301c01d070442201841500d00032228010007041801e103050085200141c1c020074004c401500c140c1c00c1c60710804e50549062030121400016075524202511090360180c50211104010341d407907182c607148030300802d990300c000400c1c403091250341d102182d120701d180c28400d20000e807081000368210b623102e05040d07000300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 571264271 1250 571263021 571263037
    0x16050102280e01080a2f25020f0d080f0c010f11030907060503150d060504110a0b1204022718030a080f0405070902040f050909010603030e0d0305070506010b030f070809030a0c1a010605 81
    0xc0f04100003205110441c0787c00d412041e6024026490030341c0300105000d000b0542020440f12140184010b0004c26003203000780084142403c004902c00c0d82410b8404120342c0b500c2e8000102c4001001041a85240001c032102191030342c0c5415907481c0e9a8609010441032016001607024442c200190180000c642149004e107000f980304030b8042e0b10395420410311086e140301d8820006000d108141e0740c450700180f0b16910600281c840d581c0507201784800c00b01c001d401c010300e00407041c000e810b2114040d50341c0401038010201d00000e514028a1081c0944032410040290444043c210001401c0040600c0000d00402140d00255140d90301c031400300c80ca800a44c010540551511380008041c100c0500400c0110394154690511112140050002645000360150b0038000100040d800203901001018000c114540190f41c990403d042c03080c020f010090195070800005d50140000c45501008882c00b5609905200c1400d002c50729210701c01001c000900d0403180301150001610390b4008004141c46 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 571265521 1250 571264271 571264297
    0x10c1a0412080601081603020d140a060f0923180708031909030803040201030203060a0f0303080601110f070513060b03010e0402031c1416050102280e01080a2f 70
    0x40d40e20b143c01128880400c8900081122030100c4240e03080d8020ba0061400105000c000304141e420546280c64929080d40c0c466162682c0e00c004101c0c1c99810034014002d0500035505008140c503480d9800c41c0411030b2203000044250310004200412901c01001d0105200c1800f0f8441d600d0f65814810f48035000000d001c1140d5000340500d1980c140f1504c800303420390307038410700340387c00c5031604d0b00110002e400080107075030480a5000d0124842044015000065110f40c1d21880f6901e40640010014000380c40001255840994002c10541c004201c4409032242529485501ca03504c65911010388001d50160942600000021445410200280744220300a03811100c3c8a2a0300410600b40310950140000003402590520408500803004280c0010b42e00d840e032850090545440c1d0072640001c40490381c40101907219140d00300c1c0c80c5044c0f01c9031925420100107400e06c040018281c032030010042ca0000c1d0340e6511b40e19082d07000d91040350403403811285400b145801240e9040d0380c4d40c0402001451 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 571266771 1250 571265521 571265537
    0xb0109060c171819090c030203090c040b03010b040207200a2409051f0806030102030709031103070e07080f150d02221e05010f14010c1a0412 62
    0x101405034000400040d03200846103180002181400040d410180c408010f404500c800c4424039a5024060120200c0d00c0541d50902407800c1441c408440b0302e019034a003418010301c10080300440104091300500f10684010444201440c006801084282d0859a10510106002080c0001c5207018042007000c0b4010394110300c191010000242882d11901282e105504016803080503040d041d48003084c51410001c240d1074a4100040404003450349000760000d0f040341c2c0900166100032200d4100209800031480c505000100030102410790101909071a800c2c80e06090544041102d580140083e00e04085182080100208070400c241c5213003159030105008030f403102008006040c200a4000d00045240b903040c2d0a00514000c8a88810200001410320b0701407e0070718062184103015032450461000d20082c0800100c86d0107070044030070703400511801c0c41484041e10071032800d4002420101d0040802d0300d005800390f0b51007008034580c0d0009000b4401003180d41c0b006c001c01449130341c40f040c1c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 571268021 1250 571266771 571266779
    0x140301170f010e03032d072a031b030908010203042306070c150e10020c122113120f0e0f01023c0f01110a05030606090120010b0109 58
    0x400ea5003940f104403d07031341040004c50010180e050340d07034080002e41d0501c00d001001c10300c0e104030303450006c075003040c08035100c540140b40c002a03e860300041c6c0d803c1800000325009640c2c4004140440700c501c00c0500000d2641d202e000d03d401041c0d080004c18502e4000e65603485c05181c400762a0000c1c0026511280d07178542804455040816800e200b145503685801008109443d030400c6004e02c40c240d1b425181e6110b6020301c3c01c0e482441069405102c0240c050b0340d8043e10000c42c1d18141d040d0083d03160505061014807048000124001c03001d21802400010584850049841801c01c0c403400400088030040184015904100101001011074460030440300c0b202090007070040004014034016004901e04289a03c0c0380802d036000b080400c941c03010708948000c85501017501406e415140d49e4424484410201d40c2409640316800aa81d085030419144002c060b20900010b060f16120340004195a0703005c0c1d1049450000e40e48000036841c40343d8810004c11402000e4081405002031076040d4041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 571269271 1250 571268021 571268023
    0x8071421011205100207060b0603070801080d020f1902030c06070501091a15010f020708070f080d020708030f0c0a062d020406020307060b0324150d21140301170f 71
    0xd42d1950480c020b010b0500c8030140c448000d41c4081802c49025aa9804010380c50700c0303820203588200700c582c95414403035040c840118600ce0081c6040b40466000e0300403001c0e2042c000c0392508601d05580411000b8008610002e400c01d07940130760503500040d010070b5400912034150441c0a0060080e9440070114240c1e0200d003d2a9004031114003c84c0f400082024843d4412403004c241d200c8144141c0d400795841e005490704120f013560184107580c0c481c0e5030602403010188005500c8110a0004102d0b07a864400e10076228041d50309010580c460208403a03e6248084c0207040500d6071004041141c42c5030314003100807040380c14072601e04d02902942c1c0055500c54070301c00c480552b400c43d0021418100301c0e685107000760210249154150142080c0303101c00081e0a00550b4443c048000c01c0c0f09079103040c0e00340c942c0b459542400c4510409420040e64080340007880d03419420405001e40d41030242c0300500c203407400303068060b409110390800000000c05650340d071444211108124250350000c00c00c1107801e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 571270521 1250 571269271 571269299
    0x5010c020d1202090f010f030e1603060b0d05060601050a050c010f02071101090e061e04020a03020c190209070815030a060c020705010806130c020a1202060709080303160807142101 79
    0x9070b800105e00c0018144075030180c4030700000900706150100c1d608082c0d82070399013040031114240e10400c000c0c480c180200402c6001e0304c0156031083d13590b00541403054441d290b0324540640591b05000002400005281c41002141c4056030101c000f0b216819900070b07100002d61094000340c0d411008490f10040360b41c80340100008590309892030040395242c4d00d080160b29512018400c0c034031b1080e4071906280340c95500251040b50404e440051300d4010326038140c0d08003400344010000810752040c00000503540c4452a07604001c0b00c2c0341040071680c07101e015921404130910401e0389441510b40e100c003000740b190082c1d00507a48590a441010382e030b400040d070300d910080d100203500414514204200c0038041d070040d00c1e90400d41c811031707000d40450b031180142c110f2060001c2c401a00100100050540c100711184000c0490900540c598501540c00480c0412910800410010500003085480b40700c2c100c01c00c810307101191140c2d41c0d0340e500c2845465404928400c40400d0b00c2410000030a240c038940342e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 571271771 1250 571270521 571270537
    0x80103030e040e060a05061801030c030b0609090a0b13050f0c1314060d0813030b0a0c0509060703081503191109040222060e01090504021311220305010c020d1202 71
    0x800e2030b44c030399906a8000c0c00d0007e083da0341040c620a16a40500c2c0c01c84241802180a203540d07100307003400d600b0005038242c0020000c50241006005002d000c0030700049030720034a5000980d5040d01d8030340c90540340c0c2d1500b0416011304070703200e0704a200312500408070300021455402c86064003050080d01c000004c1d103501e010090f041c0f259040000d0081d040c4130345a80c20b1a13108001040c41c0c40f01c245070118a50b0503940081d602100140b0401034545214800ea4804884a0401c581080e866500285691054910007010002c6200100b041d600b0403680040e0b041704000d0582e209000a01200d00888030a484140d4140b410314040d1150f9040500f082d6010340e0f005000000050f00a0000c40071a4208401703030a41c03240d4074807001520725111542c9601829245d0b80129450804d8010802030814074190000c0792441c2c00107500303040f0302000c2100d040c82d0301d0f8a03650b80404480c01c00d111310900c242c0c0c0041d066500b00051074581035404140509100016220008858103c007500000c90240c5c0700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 571273021 1250 571271771 571271773
    0xc02010c020d0e0f03071d0901140c0417010b060d02130f0f0e0910050a0c2601140d0807030206010e0f04030503011a070c06122405060903100507080103030e040e 71
    0x350f030442d0382400039440790b0603030010f41116a165600c03400340303460511826404400203014010700060803403e0251142c010310302190f0381c0e03003810508a40d0310a449684244139a082c0e4031214101900c40a4018041da040000d107266103440c844944030000c0d41c0708001082c2015440407000c62285581907d01c0c0c10b5502011074081c1c207030300300380c264840450046c20002151081caa41d100e00034165001e028032a5034150008a8642e4020304007900060300f0700f187c00e5072041d031020080d000159100c45a0304440146203140300075121400800d00a0101c030f44003401541c8002015400d145e000500c8034100d03507a495501000c0e0f51203015001c0c9800007514001d002403803c01c010802c0c2c0d0300850b4a121856008000a0726140c0c2d1507450052a14042d401480445c00070b8004c4050f51a041c803d4892010764500164842194151840d0740e420306400b80c00e11a4901003840c04a584040040c0800380e0801e00080000d41000800606014003d00c422000220801c600700054101802803101401c5520 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 571274271 1250 571273021 571273037
    0x17120a05031f031101081e0402010e0a050901030c0f060804121d060307020a14070b040e070212030903120c070506062e030204141f0305040f02090a0c02010c020d 71
    0x241250698030180c0301032804010300502c68400000b16a140e4000d5101e624008644041d94001410380740004101e50702c60031003005000c850943c881c2045a03c2542441d107403003480c0008001418150aa410650b04228400c00100c00c004410b47c981068a203041e00c045900c5071384030b000b240e40c1e043c201c40082010354240158a113150091034201c3c00303603218070f00b0100c520100d140072a8198008035510030059120419400900010303107024013605058030f01902c915130510304c2d94415881107210303900049402c4400034404510900c9040151340c01034244903643c0c01c0c0110300d16030741d400c42c2d00c0c0b8401a0041c01c0105520b48102d900700c1c1c401c03030f44c02400b400242e0f449008001045003010b600c007071650703103803500654800a040d00c09194041c050b00c00613110384c1486120080c9450828629000f001054200107000d801030120220034816841d010400e59a2031600c4a950041218025081051181800044445a00030030582602c95000300328540076400c00300e80c0d85924492010116180d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 571275521 1250 571274271 571274287
    0x203040213020f210712061419120f030912030804060c0207090e03041a040602030304150b040908250209160c080c0c030708010c05040905040317010902041712 70
    0x9070007910310f003090000007504000c4040c00c1825186001c00b80612826a8581008440e41d0469854460300c189032204001c16810701080115403161400240d115180c658800396006047e242084040e00c48000321002d020140d141c1100c4044188038101e011941621000c11606036404003c01d80301d0b01a0782c1c00344151215280e00c030042c4010070f0200e045001e8120701040540f880c0c062910140d812030025940e603440c2000703858015509040c00c0c406550100010801d15500000380c0e5001074105646d03210755082c49062400401049141c0c80c2c100b410301c0c480109221000b40a840010503003010840300202c0c040031605d00785100a4000d62001a05011602d65000d1101428418100342050780010b0a00c0d22400c000b82c210b41c02104060340404c07084803071400d090003518010300041c2c0c024404883c0c2d000024141d03010310300880a24aa8410000301850712408143c0944d0441c0c9600c207442e0358540c00000080e5005001b14542409548801d031000321001444494100072082c4241c145148 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 571276771 1250 571275521 571275559
    0x6030216030e0d0f11100e0d120c0b010e0a0506010315030602030a020f070b04051509061620010b01020c0a060e10030e030a080103021903050c01110717060105031002030402 76
    0xc4104683d4220302c10340001d200140e4000b403000001e0340104914480800050100700c50b64280c43c41010810079440b150b080d95498054400b00d440d50300c41a41c554a5854402c1192821402400074207104032010001813852500070038503009100000c0180710541d5804019426521f4050010500c0b224013801000800c4080d4095500140c03000300c0545002d04028040015411895007550700040082c1400200001000010740624181e9502c2845207022848251114001081d4030b04621082d112031500a20440e1001814504282d0055070415024200c5000349001a5854007502c80c0000e6011070385808103d0301c080300c109a0700c07220200340c81c5007400901004003417808103140d00ea00381d404000c441032000d8180000c40341c1e910010341d131560040201c084480c1c0000358155000c1d070030034004140003142421100c0400c3c01c18054400856a0b038a103804040d0303011000c0f00d0481d40120740c051401180c05812508110111044504803075624001c903c4141ca009501080300c1481c0307040041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 571278021 1250 571276771 571276787
    0x150602030909010e060d0512070b070318060903030e01020a020309190f12050111030c09090601111e010b060423090c0703031a120a0b010b040b030f0a020c011503061d0d03020904060906030f05070603021603 90
    0x102c91d21300401d900c2003c030121402ea800036100e0398003680020401c05041c0c1070441c4c403040814540c0031650105440c203075220b0301c40340090081d07015200c03540e50b41d0420b01ca0250080e01c83e141100c202555a071278441e42c2280c807a0400c413030f610f104081c1500440d42d51f42c410103440312540900701c003030400400070310b404494812a5042169940d5201d03000c0c04040d41e80c240103400286004110424a071806020031600c0c1040c840d03119108a4040302880418403014040d50142c503410300300003400350001104000c424056280040e1311000010a00b858550049144400940314168588040e40c0341d100c010580d000700e001d0307420039000910004800c410200c0c070640d003110991070014980520440f01e1400e547c1c001c0800f03404a140c0310010400c000c198803413a11605d50381806403404801114a80d42c8a4000c2c9888400701130300130642c2c03800344e038560b030024004000f1094100216680c4c2e1409a08029692000341ca1310b0284d01d000140c290f00a0084401c20341c0d00308040346041e02940ea042d0358000f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 571279271 1250 571278021 571278023
    0x103050d030b12060a0e060703050103031403040203190c0f3309090504050d0806030a05070b031e0109090501271b18150602030909010e060d0512070b0703180609 71
    0x6001c0c224038180314400d0099034040c174000c080204a8910003c00c0600e031a602921540c1018600f20040011a60044910301e20703580e80e801c0079689481c0d03800002c1c50b15550701410400e201102c0a03050070840c25501c220300b19030002c0d01c40400a69601c05010101104880c0d00701c4c0700301000c1b03d660040d0544000c040345032503079003050900c898641ea894003c4840459084404e98424592454004c2d00142d20310341c010803c50040c0410341c41c65680681710a011303c14a8004030000c80454004004402c041c11621240040e5803050f40e07460b40300c1406442c201800b82d0b115480c110700c074100314260f112990b0354403008075041c030380b18821642c403642c14400303a012040680340055800706d84500d8450a44805802c420070115a24208101185080c0040e602500941d0300c01c102103c2c05455030310b81c91b81103c4a41110510b0b41d61070101283d03400780d401c60002e005000305440c000d1940302c0c40c8050155903000e500c440c0f000e035413140c80c01d0342200e0440520003040342803640b0303810019065400c91100a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 571280521 1250 571279271 571279279
    0x21306080607270b1c020c2505060f032202090a09050f0105070e060711060c15100302180910110406030f020a090b07030201061a0301050f090103050d030b 68
    0x400e03038502040d03051040c1a60780e4000202d4207000030301040d101c03800c182050710004088166061500200011500c5040c1e1303c0c1c114401501e82426500c07070341c0d5050321128a0000d01b40c541c00307074220941411241e003071100c540c0b80086035400450941041d80503104008074511500b440e42d140d140c06491100101048145c100000340079060051300c036001c3c913900411034401f010600440e90300d095420600c100030020b000d68541f0f004c02184660180b1004a03486041c2c80d0503594015a0402a100031000070903e60010b40c0000e00022500c0001400509250110242c00c3c242c0c46511031058260030520029601c0b890f21000c080b004c1c14001c4101c4c2e002600c101c21121000700095002050302d20380d0705c0c9110701102c0483c0401003d1707010300a9804c00880700c03d0440c5801d50744a0003409410340d03400703030121421001c51030f1030405000354040d1000c0c0029043d0307103048501e10110040c00d03038003d010300ca015440c0a500c01140d4102541000d0507030f030340b00011301110110900101e00500c400f0950344d502c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 571281771 1250 571280521 571280531
    0x61317120a1d0d080a0f020606092202040e070f06050f0d02030a0e0f030319140403081305030f03010501030c0806010807050c160b0d180b011e0905091608190213 71
    0x790b6880d08480140e0f1880344918a442c0c141007400a855011280340c0603095421110030031865548050420b81d020b0150301050075000e400103100d0070201c44458000390400c0c68800c0c0c07942c0341e00000606ca011503080203250a419500c030281110b07640181000000341d1031092007107016440c0075402866120542d1500001e042961142a074a08404880589820b42001080c000080a8025000301300c0b0511001070002e0103160100f2110320000810250810103a88040f43c0445806030300c1c002907a41050880c1e81b285c3e548141c5141030380c001e100b0359011900d4031415032039160040072414403c460585a920196540060554003a444004500303601c1c0182d00083d100300702e00d20382e50000b42640c0910781c4d46908407a94000225a04100b0700d42080c40c00722191000544840e180e281551440c0c1c6c107a056520100b000002c410001c2e402842086081c40100a404a0001920280048154a5024202d82e00d01d0070a88400710501c12143c10054070105402500300407001104070320100c03000280b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 571283021 1250 571281771 571281827
    0xb010507050a061e11070807030e090103050601050f0121151e050405130203060114030a0b0c07050724110a06050408180901061205090c061317120a 65
    0x10914244000880b070266840d0b1102c03111002588004e4100802d090007040f03080c0a550b0400618020020001c05046000583c5010075110f00340d880e1103000043c1074000700d56103d140142c0c0300da4090240c50b004110820b428540c0b50f01ca03404e040100b95840030318107514444401080080c082181c2c003201240032685000034000d403200c03000309071500b8040f0700c42e041e07030700b000e0801084e603c2c0034102e000540001c40c0712101503035010800c141103810319409040c011843e1801329082818003207000d800004810100920048087d00030f004951255066443d10b0303031120241e00000c82c981d07420b5000c81d8100c850843d502c0380a1071111903040402000c6800401150381c8180a40d01e080328111181314003c03401003143d4001d181da002480c00c0480e00001c00d51306048005251000d458400e0b06003988910208010040500a000344c240c00900f10070790b40c5004040d519102511881455841824203402240e481c002184030541c0840d1864043e01e480c0b81c20f00c017194032100c4210780e50742a40880710100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 571284271 1250 571283021 571283023
    0x606030f042027010b1305060d0905010203070e01030e010c020615041b0309120806030a08030c0d050412090f0506041514180a0602150103140a0501020708031b040312030b01050705 79
    0x8211030798030102540c40b40b5450f1001c50740076441070b4040c0781c0441d41440f0241c5100d120601c0382c81501c03010b907111074a8040b03880d2020090990b5160141043d48000103109800e81e0084000355410003e0301d052001c598403601881c2207542504907800160410700124400d064000c072000c1c80540c1c000e2012030911009030300c0d0001c40080714681d2011176510540d103403c0000388600b051070000c40d42032000441c074110303010030303104c601e1a80c00611880001000489450008054601d030b103041a50800c0185051310706171481d261034000440100e80803002c006103155241504505884014100c1ca0070507240022184001200c401900f040c800913906034080460400040c20440c0c2e00c609180d2450b02542c0b00784450004560428000c640190744641c1101c03559040c0d1604483c0d101070103540390301b2070301d031228140b0103103240041a80d400050551309010001d8040c41c003802040b142803040c80320201c130000d45031043c0d1200411752001c09507034500c40c1c1d00039030040750b10380c0c01810654904010f0303075109 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 571285521 1250 571284271 571284289
    0xb12060f01050a0e0705030c0304210e0f0607020a03080d06030b09030a030609140601111c08040605010503060f0f06031908071403090d02060f09060c060406050606030f0420 76
    0xd4426403000c1401001030307182c000d460500404000c00342d002c69003010140185144002040c10805c0d09000000c64100f108100400c41034110b46090012210f0003000c008148000580394a40304181c074004070000c62828408486e2a05da000b00440c150a00c0e558a2a038135410144c00c600c129a42d40ca400804590b0b0140d9042c0b1602d900703009103a41d1501c4100140440d6080c0d04010b0b50700340743c8005090301c070b5512402c840e0402ea090030240c105215400c0b81c075203400904a55141116032a0340c2c40c0c42c925402c1130405025502c111380c02d00003030ba00d5405041c0e4a0030103c1e4a903141c000304030040b03080c2c403001902464104e18007030159020851464100502a011110212190762000074041d05101c0030402ca2500845820080c5d407034a0274036070020b580091154406445504001800507599010784101c420070301e0090b12454449010306811030b29002d080f03d06a544900b0500001c0d0a4a4480200c0e072080070760004598a80e03d50b82c803145c00030301c1629400c0b0008040740703041121a50f01d103804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 571286771 1250 571285521 571285531
    0x12060a11160f0809090906040b0c12010506070c090e100e0f2a042a020708070b1c0606030921050403062c070611070803040b0c030f0a0521040b0601030b1206 69
    0x301f40a0400e40b80000c1521b00080034100340c043d041c407044050703c0c0d40c61540d40c1180c01c204d40d8251126520704106d004518654030044185240600c9072a0006000c9420340d003c5030100402c003c24000b20880036154807810f4030100c4142c218600c0b40e0001280b0040e00c0000d0010a6541c4a90f0a9040c1c0031030101d410072842d001c40c1400c4a9440f60680342e42c04c201490a100c0c2d88050041d140c500807023159a40081c0c020403000301c002084200d595140c12644210540410a051045030340e0390101800910240c0001d441c130704400e03840e4aa0710030950701211750507580e550302e40d45441c2c55a25070030700034115903841e9501018070180714115070303000c2058020501c100e10090648640381641c007820442100920f100980c2000c082081040c001006540454098a92140d03417441c40b400f10500310300c2400c0a000c00c0d0389011802c054201c0c3d0000207084200c2075000105100142110310900c81d5404039801001c200302140060025440b940008204041c0035080c800f0712800100e047c0d081c00c208807030b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 571288021 1250 571286771 571286773
    0x50901050103060f1b030b010c0204092105030f04020d0312150f08070b0f130b0c0d020c0d021c0203071805060901060c0201090303110c12060a11160f08090909 70
    0x1030052000034891426034843c4000d0070011241103a82c03030b1901205000b003817004c0c56a52100c040c0b0a0340607080020425034002d104221010b0703d440c0007071403000720354101c843d8080301d1000c0d4200305014008480c000c009003038511000d6900c9508204000d5a02c002c01c078100302c2d080c44c000e21b1000c024000d01400b11a8603080f0807480c0d0419940c0400e1550310f44c4030208580c0101e10420600c100001211101407042d0030b00ca54405035202c421a599110742e0084409080018082c0c1c1011000300b90f100040142d942031b541c420f0340344405c04c03415003800d00002e9408440100d078110745a803641d203004d04640c8040c2c142d4580c1d6a880440300d500420344400325442607200e00800000b4a03043d5000750140c1400d01380003540c03034040d40000f400103c19000060610070f14401c0c03080420001c11000c100e64000500300e105a1299108190301d44005841507950f540c2001a1302c01a00c0100c802c0e181c4158904814180640d440d40b250b10380c4038442001070b600b44804000700b0209868007014903214a44040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 571289271 1250 571288021 571288031
    0x2d060206180307150e010f0203010b040e090102040b1c0e0a02010824090106030b0109290304080c0102181801181a0a080706021006030b160e090f150102150a020c10050901 75
    0x1a0aa800d4407e8004018051481007006125400808055805a070140d01208001d55a83d074000740c0203100d0360f04543d07590900801c180300940108540490003164540b020b01082040781440369880e111040001e001c0b0f08440300054990740784200300403510b002e2090600c0c19241000204010236020303041040041d0302c0e15401c0c515940c020b04800014000291960501d01107141001c401c0c0c0340d15400b450401c036002000c10706010b000c3c0d0659201044003802103588580c03c00c0a01c80c0c20b00d80f51285c1c0c0c0074004080345601c282c0c4000500a040381d000000380d807951120402040300510416079507080c0c09003501b2003408a512150014400307030203100014240f10f402c046010303103018030188802c0042414014144002030890307440c3c40d0844000c0b88002c2c0070984014068030b50f000d21034074264110114004000b09030f2084d00e000d074000d400051242e00041d41d001300498841c0080103607c800740345440c0100b00e282c01d80c0c4e80209400c00c1e415040d5071030340300d000c10710300d065900584600c043c0d1380d150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 571290521 1250 571289271 571289291
    0x40905030a09060518040b12060a020405150a27080a0f0b0903041505071e050105040b070e0d1403070c03030201020c1b130c11072d06020618030715 65
    0x242c0740002070051418000d0030001080c030705210301d9aa14901c5401141c54402004c5c45840d8a4040e07000d4150300d805441076860300004200081d001841240e10604407182e8840c9040358200c11a219401296643c51342036000c0c5d00c42241044d40000c545c00a0500c0f90b00000d07004a080c01117181c3e483c032401c0d04a40340e2900e4109032410300340242039404207410030441000310180070f400407800c1c41e90034241903807542e0050402400e030051000e044005000307403155200400c4810f500c020311403481010700003603070385031600221490050480c1c2c190700000341000303483c0030030384280c1812090340464086034038000042c0e82d2843c4010301c50344106d0261b0b401142103490324000b8450340c2030503014840030104460b100800902d0f80045400c1404005544034036440f80743d032180ca441400c2c1000d00c0c1c1200e804034ad4400710009051440003c50107905074a40c04940441c8800310100b04984141e40102080d4544511000440001880e45515071100700250030010b43c801c0d100c40b68070405002d0005042000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 571291771 1250 571290521 571290527
    0xc050c130b0a050418030f0314070203070c080105061c0519031812020a030b0702122d130308030c09030a0b040317040803070f03021e091c03050409050411040905030a 73
    0x305403c080e10450a256076038810942d150000988540c1514100c90641b1000005500611701c213982c0e540c0b11000031003003181807034001000309440b5106000038500c4903903070b484141c220342040e10955030044505000911603610300c4071054440e8050025980c001042001084016807081012000308014035409840d1202c1d0421150040448021100e6400020341c0094461680d9000090031801404080385000b80b080140d04804840c2c1c0403516030b140d1103011070403201c40300c2c0141068a000301401e5105d038208000107407145601800082c0b1480e07402c0d40c1d5001501d030002031250100c0c1c2400e02600c09165000c1100903511805010b01111504082c10000e1085010600611501d00f0020a00c40025008002c4079800111403429030800303000f41c031040b4060702c1280000b0700e0001804038580c5001006900521000c0404c42d45c5904c1c1106036030700340e2031001102d4401340c040791007400100440d1000d50020b80c1c0c403a104a4903036001c40f044900083c2102d026440548031944041520506550 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 571293021 1250 571291771 571291789
    0x71110020a18120503091c0f061a0103060f060c05101e0c05070c350c0420160201050c01090c060212130b0f1327060e04030c050c130b 59
    0x1140c03259040030300464840560340e00c070f069001401032940c8050b00107248124404080750075032200c11294003062301c0c149100505594000b111800c0c6000c1c481000301c2d8002d116400c01c50b8844105d03c800d131803500f41c007569641c00401095605000d85803050800507410701c1184c6500741c80c070310081c003410251980e02048030301e001c01810038000304000d0040420780c44e0310108212003038802c03010007000c0c1680e620003903112034101d02c141c4c080c841011004910008602c1c84030b0224256400c10410011012410142d100745a02d01c1030340201f0403480171b502c5007403118004558018100903280c601d50307503182421034040c1007055902260100c1c042c803480b68140000c0c0c1c02d40ca0000c51050612094904204810751144a003541e0070600050851043d0200390039185a1852000041040c3e96501086c620083c40706d1860260150140c015205e17210042c8213210541e48080d410700015583d0365000d0344d8200001034103a90921aa1040d01141d036a068000303840c416440c00d010850581400a12915007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 571294271 1250 571293021 571293029
    0x6170402060d110316230d0509070513020702041103040b01060e1f170105090c040b0702360108070605091e0a090b0f060a170a061505091e0603071110020a18 69
    0x44103406c40b0149402d410b4181d81051803440703c0080d040d1251002c4a280904551096030081140b0011104080881d40600a5540203907014055107656000050303030b0344004c4900a01e41c0721410018440288030740306102c006c1d000a0310055400b0480b140c1401c0e070400c40c03e841d500050f007072001840031205011100d0300500042d100d0100605101c681040140140e004415400f80c0109000302950355042403032400c2801e00002a00c00d402422191400500c525806404a03012400001c2e040360001400f00840e0381c0780e5504e41c00e01540c80700300408044038400c1d14950000340009840c07640d07101e41901c00142444103002901800344428032861201283d0814071034001440114442604800303072102070b04605240760400c2e503c0b405100001c000c10b407c00610f00d456000d019401541200040600800889480e0301100310b1031030300e081c0c030070341151010b8000c41c0500101d00528001c8039100c4040c00040300781c1d0700703240603000988100e8101200d02c80005e00f2166580c010182c04520300400342c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 571295521 1250 571294271 571294307
    0x10031a0103030e04020706090f0614130309091d060c030a232a0705010f0506030c030a14030c061003170c030315041805060406050106170402060d110316 67
    0x50340c595140500382620380701c1c02d940035a40000720b075003c2200b260300040d800e42d0300c5043d025100442e030502600074502844003404000004001c205c2105c81592030f0524103525a4551055508004c000c101901880703420090881e0300c104091125101401348a00c1a42450545620391914000440560f611403080c009600210140040600d08002c92160311040c12442d80318040051a9554100b440c00c00c0200c08009010641d6001c004041d00000103a41442c50244010707290842091f0b00c6001094100f68554028902e40000035211046212080700c1c030401e681c1800c00c3c1070559818110200c6110140c100812414070404c40c003003403000d18916803491514103011003120080e54034840905060551000340e20002285d5a032500310750f15811510400c6040380301c00d481c0c516a91002079804840f06424800041440e505c1060300200c0c24030030361040346050701d5940a204d101c1e400b110400464603103031940d030b5a02c84003d00066001b0045c182c001401c0a2800000600000d4008000320748 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 571296771 1250 571295521 571295573
    0xc03150602060f071b0b0103020a140609010f0210020a030e15040c09020f072420040303120f09080c160b040b0a0306030b0c04081506181e1003 63
    0x403040c0e00107100d03544506201c805001c0c544a4600a4484649440748900e401e0300e81c0e04c0f00c1c0c00300901029554100d9200740c400c110280d44035030170303202d6100c2020750789600000d00380440c0595611600f4039080000860040e038414030f0030000500c00b60b80c0040c1c0200046904d41d1441152004108001070341c0d5000d8501c441482d041c16941c410798400d0511942c0001900410300240e81001c0504880c4400e911083c0d8442d156041c204d1410908401c0d030302040b0183c40c086041035803021003203031031280d840c882500e41d1070903046540030743d011a007188034560050754031a600d030101c020500c5075080240c000c010007034035a00c8031000c040c5041a95101c5081422640c40c00300301030800e2200b610191170506205a8460200c003404900030302883c2d0016014400480501910306c0b880e500401c02d43d02c1203010748510f0b0300c0c1d900c0850407a0070b0507259203400c8625801c40c030f100c1685800901e0740000842c0c4d100e0fa0024000861208580010f0314800048080c1d03440800420089134000421181d10301d00d0402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 571298021 1250 571296771 571296779
    0x90e0a1e0902011b1103060708150409030509010507061404030e1e09010303080a02280e03060c1213080a030f0b0301054c140307140f0a0510030c0315 66
    0x205140c800030384222904c0d5900f00d030000304990082d031050410f00c0542160050b01d803104004002e2442507420a0600342191507183c190b0500e8043e03440d1103a00740d100e080c5003040050044461b03900c8514180c5130260755102c203a0101c0040500340780124040e07543c15181100c01c000300710001c040218204055101540644040e03200d5100d100c0c110f0f500b41c00c00301c02c00e541d0141904041c0c85130050144041c1d80d4440212050344050b0400c00403050a41d4440764102103110605643c0c9401303590341801100c0c1400f41c01c1120501d0034105600000001c64240707080d070709640704203164001c1c0f005040030984030f03101000204550f10403982c0b007200860090096050000c8402d401c40d11003400c0c00010761428130112103584007035800701380100c0f000c0001001001c400c4494001100365015025500f80002c8503510a442c0001c0d05009450b00780c400a81d0542e9103e0130440039103142689290000c1e98200001a80d5403080d5465101807920349002c00e070661340100c01006c031030001700c40140e00e880b0a4010b01c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 571299271 1250 571298021 571298027
    0xf04060e061206010c110402070c030b0108030c0303150307080f07030b0a0203070c030c02040b0312120702060c042304021602100306080a0308180f0304090609062301090e0a1e090201 80
    0x154010340f00b824610314222050910a45840e44200c8480d00301d80005025130030403899000100c00c59001d1003540b02c141c0d07200c1910540b0b81c401c401d62171207075a000340b020070001c10800d440e142503280000d046a05282e5143c10702c500340a074010314500715810000381042401304540c9002e41c4243d03000021491351500c08009000c4141d00358000d0b041140c88d8280d0021520b0700d60003202c41c100d00608640d48200c80c000f01403096400441e00031000550f0710301064800c0d0001406601801e031703040c1250b0030036081488195501c0240e1240004141d0051082151500c1b10b1009018050003040b2041c510095401889492112034480b0000c051810000b000071010105105850780e07414540b0f90300f1522420b141242ca0450992803801c107008a407144590400008024801c4900740305051008035540c00c40c0c202107481034411940160b208110b4242545c0b0001a60101403005052a14019890b10041080300200322032108a043c0d8610102800c048100c0f103645007143c045009010071201a4002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 571300521 1250 571299271 571299307
    0x7030309090b150c0c041503260f0307030516090e060f04060305010c0203030405100506010e0103023a15120f021c08251a060d06020f04060e06 63
    0x25080e549030800340c0560344040094520004840f40c2c51344400385000381546071020210060311407440d10011540b582019900841200c2e0009420340104000603508545c603400704010070003c3d102006619110b80d1400301460081c5000c2c0ea002505240010030741e02e40404210000c404d000c04100104540d0380b10040a56002c0b5099400f143c1c94006000414003401c803a4200500035402d003143c5038100341c3d00101a52046000d80121180b100d411025030044501c2a140d050018584008240d001e500a8008000305a02064034884081140c01c59020340040f0300704440110040a85002d40354040e0b000c1c00050030440d01800360707050328203e00b824000340c0d042c1c1d000301501c104440300f501b5136a803a41140c950351084510f00c00c07000802d00e001120f95112901c5030003159048500c100c03103c48401404a00d0355032019030000e00b00d10811101090410003002c1b980c2c01149210140000360300f600161000144811145031207171304021000c1c040071181c506840c021001401083e200128080c0b80d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 571301771 1250 571300521 571300529
    0x421170106050c07240e0607030203251b0303120209031c020c13060302040c0507020d11030c031203010305011a0d0605040303020d060312030c03020f0403140304081e0c0307030309 79
    0x1c40d9503074000d500360500b029250380c03002416000020b044416178100c2c1c0b070300d481c14001d25600c3d071052007034035401c000310b40c000c0707510180c0140d2051010040004a50074401c40003c100c4049140c400c1c5150f8544222400c0340c3c03045121500d510004000301078002605a0001590032400d500b000d24980110355502101d6403402501400e21003a051003038002c1c04000c0c00c4800140c03840b1a02040700c800c1e04040c05046c402240607500e4102001c0c40d0600c10360940700d110b0b50080c200c00d41d0780c03001c2d120380e071004e1604840c6c16414012054845001c0c0c2d41002003518080c40304802940300e6156080c0700e42100c9902c0300340300c42e6000c00c1c5a12078441d03031400945d11000e58402d0002030251590304040700240034001020041c075107000000720030300c444d0400c8040220b516035000d20880000060442c141e00034029005030421041c0030510000c2e5140840c0040c0b00b040358201c80c02d0550b114052403800c0071108144003074001070001b0f00100c10b030034004030b204500141c0091102c149107550040c5414000d1007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 571303021 1250 571301771 571301777
    0x105030a0f210c140726070906060c020306060409050606010c080c031813090209060409030c0602031303090f050102030d1812112802010503060d0503030421170106 72
    0x210400411880b94114511010300000502041da600c9801501d80c41c07403104240d8100c64448004024080d00040d030206441180c002c0000e020141c0e0400c1e40d40100c0d446203010240542c610118255855100b03d0000b03080507603500e02d09908078010b0504002c07011306000c0c000c504100c040e90103c3c400090322a0494002e02c1d02c801040c00c50f003030948a60248241d503581ca4000002e040c007112003010600f03550317040115081105140101d02401c02c5507040c4c20005d400c240c0e440000340c064a441da212441582c02428107030303e034507602c3d0b4030302d001c07a801100c0e03500302c410480b00c0c808145540119240c000d041c0075080019070b5828500040d40c5c074003410008201154445c4017100d0203001c91545c0d8801c00d9031001d61400c0040c85c07000003500e10281c1e182c010110307200f0308404008100d20008142c840241d4909450307010031140c0c00440e00390344010110717074001d41d42074640000281c040000758880d902400d9a054901403515210080425100c2400208000141d4846001e03005004150444040381 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 571304271 1250 571303021 571303043
    0x1030b0a0e040f0318030f1a1003060f02070206030f0a200d0b0a0b0703020703200a15260907140f0910090204030503030a0e010212010b0703030f110d05070302030105030a 75
    0x13203821213600d20f40300420f0400d0705595074000100f00e010b030b2000d0004c0d442380115402590b0044981c4c1c20942044540744200c03503c0351010004160540c0c01180080c0308004003514003240c640215059606c1a1703920300300e0102207400c1045459040c45000744505101c41000e0f401d01103244003c4c1035020f41c0081c0302d010355a88201c03040c503944804801005210517040c09440348090b0402039103c0c144c0e84800c3c3d40c8104442044c0c1c0810312801e4407180c1b00b1000502e0740420300d082c008441c205641c45c2000c10140031485140440f00e10004080b520800341074900c505803450f10402c80740c01c182c402d0340018445581d0540d03c0138540c0c0c030004414046242950784100075500c50b565010608166445030b400103200240120920802200541c800c507040032060022441e081c40300e5080307206042042015940c54801881614042d00042041c603000c1e15020071040b8070340551400f00c503454101100d6034100000d5039040301e60b10740112680440b0700c0c1070460440d807400d000304e82c480d000e003400200890415 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 571305521 1250 571304271 571304273
    0x6030106032a0201021b0d0906030213050a080f071208090409020321070515011d280b09071e0509040f09050a05100203100e0601020c1002070501030b0a0e040f 70
    0x115620a07001c204a0b00500e40440d41000384c001d40c0404116080040019202070031040005451441340e2815620340b415245042004c400035000081d40d003890144a05000805603586103000c0c1c060800240540043c510840f050352801c00300fa480002c859200705400380c04540c1580980d0b405950a85002c108540c6910010b42003191003002c82c034000740483c0f000e0010400c04c00c05800c54500c0f86044404040c00880c10342400b0b034003481030100e005150200d41a4085880168680240c0202000510f01a0000c440c00c41054114090000541e0321204601d651520301003154001405003804100514011003600c08164450703001014040000f80081554403a58042848510013036010031070b0503007034138040340c0b11404040305039540d1094161418040d0460f1007268001c0c841e80c41c0318000305240880d00b04200074001d040764158000d007404509141c84500d90241814001d90140c5402408d00d0009030441e038448074034900a00000400340100300e11510142d0b08150003000010340313034100b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 571306771 1250 571305521 571305551
    0x91116050c0d0303051e060306041b0e0a15151e0215010314010507020d05120c04090e0c0a15080a09060603020604080607020d0e01080402090414010c05090f060304020603010603 78
    0x12000e082d001010900c0290905a26038001e50003020a00300000388481d045580b0700341041c003500c60b030307a050b0010380c0880c00140414000b03015100030844c291081a079500c1103c1e1b001c0c0022500c1c0d0f20341c00c1c0c95021a01807110b40240b100003600510035805a00c0d02190030060030381d500d40e00c0c2030030081d04c0707001044d4503c1d000b008020842d41e03101050180d075617168549408840c502200d03c4020b0340c00c01c0003040302d05001042c58190030034036a8456007404d410603103521694101910152401c1c800b000b0100b1009054050400070f00b101c0d0340140441d500101c24000c1c0200103900001816204c800200c5104d40d00c2406950405407450010442e0065810b207400180350a40c0003e520a41c0010b000234101004111a445003129800742c8520708407140c416524050001c0100c4d000444400c0050014540704c062190858080c14607000c0d9101440720303a5084032452580704000c21008900070405e8580140c0000d082d0700203941345030031410158080b0b40321b400180a04414961200110b14a440c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 571308021 1250 571306771 571306783
    0x3091603081b071203050d06060318200d030c031d010903060e0123070201061211040518030a02010b130c20010209180402090a090210200607020606030709111605 71
    0x514400c200306104d40603d80030345103034018182100100e0030038000080d007a009224014513101c0d00d6031204c407020703050b5561090003040890301030380c030006614401c0d0304c548884140008892082c0c891410500340c1d801d0260004544013000b210300e06c01c4941144c0c1720b036400208201225400303500410414110340e5144e02420010444004039800d81e1810f1035002c0c0e0310340c5840d0050a00f03400800c500740c0c031a0501c00c0c030800a003002524406e0300400f051641d08044e484150b100d040b80348000e42003460074401c942035030b02c5107951000607034548503502194070b025440b0301e03241100c0d50405c0012042590025004540200d0040d101071840034a81000c0d40e420340456004407001410018402000901c50480002c01d0b1303410307401a42020000340e2981c4041c8210180f6a03002000c4d10b42070051140704660f00c0d0010740304807141c181d40c40f40c141040c20041080a000b2002a0060304152401600349843d11403941d200034a164105902c4240300e00e6103d0444080200c1c9066020300d03100c043c05d0852902e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 571309271 1250 571308021 571308029
    0x151b0106150822050307080903010b131d0c28030c091512050c15090a0b04080c03070f1505190f020f0c09010e060409050607020303091603081b07 64
    0x204140512201e042d07401000184600003404400d50001600c0d1000a541141c9020042c5076a02c1042880081104003020f40481c4200500101c0c1800350340010510030300261020524054890480500281c244000c01d8003299140001b840300708003480015468440d511400e02d01c142c1c80614070340c906544c0803048006150424010919a07540d08c120100500850720002943ca1010502040800b0700000981e09030350084014081d060b5000200089800500c1648207205010007102550f9141c0055880060040f00920740d00c0e545044801820554986031360303842500480001d004d410b0140f10701000b0340701042005000c4214544094449203e9401ca0454410081a0703011005a215403c00b108880e5607094032a981c0701f800800f50ba8000c1000c4540e0b1049001c130040c4454466114401d501c000010008585442c0640703c2c24200001580d189005800000803c04140403c00162140c2d49001d075000342d1240c075640312488140580381c00301c081c3d9041007250030145203080252002030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 571310521 1250 571309271 571309289
    0x90308070f210201060605030601081603060513020306040f0603020618010c0204060e06011403010f06210203041209080604080f0c100614150a0905010f020a08120a0b151b0106 77
    0x10302e00540140824001d045820790041d8200070010034401d1007201a00e01642040c3c58507000354a07460560184412410345031020140c1e80d06002416a80342d0b41a450024556030005980381020000c1c070080d00c00385805a0503440c01c2440400051301c500e0115040300031010013080d03400e81204c004860709501400080d5205003000c401203280c001490f0f6081c01070300c0903201d56845620a031000b171080d0009100c2c06d03c010f05180e5080000600921080380f00000c604511b02b0001250350440c1d0490b001510165803007510840e00e242d000b50002400e00140c00600d005100074949a51100b009111b5048085411032000c6001e07408441c0400c001c51060242210a0240c5034941001c03074101ca00c04101244200c0c07004500d00c20385e41a2804039000305901d5560303051414140b500664072403400c1a0540c023144075049000c40420045000b0707240000c8484035041352401c004800f0000d4503840e200340c62040c0445030302e0113132010040c4201c960600b81c641d44040070b1140c08a0f0903006080d5070740302c0a62 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 571311771 1250 571310521 571310543
    0x80a020d060b0d08042c1b0705010905033c18040911030111040503070b0c12040b28230c010203010b1201170a0f15090f05010507050703090308070f 65
    0x10041e02c1343c090300a0f20031400c48003805d001486c0d41450700c0014102112800300c92540450702c111100c0c12604460780c1c04421061070311107181e440300d003155240101503907c1d40011404076401e0782000f0800036942e90b00f01c5102e140304812004041220360a0b889011110400645400705600034000380c0c64030360008204200c640003d0074071061200010344a68070951130400c012038541a4903060b24280c8902a004100031404c0a0010310583c1c0540c5261205100d601400c03c4080302410090018000a148a40d2103115044050359011940c0308402100b1050014814203a54401d078036001582182100e02c5070000829024150b9105868504105500010001c101411341d60000e103030012501044450720381e6074158000c10803080d80c00d034bc0c80030b800c0000480c001c0b69005c505410307458040e1144043c1c1c13110900d01101181c40013032040702d002902d01844c00c1840f2080c030800780d0000407420003e02d810015540202450702078000108a0b050110f00030302401007070784400c010680d00c0880211 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 571313021 1250 571311771 571311773
    0x21507121b08071227080f0703020a0302070902030f0f060f030109030c020906030f030a08090102042c09060c0a11120a090e010501021912140f0409060f080a020d060b0d 74
    0x46044126000d42c041030000413424544000780c4101c0c001407080e480700354841c051589412041d07002020f000d4a48080600c00002104110f0000b4200345d8801e40080c1414401d515003c1c0c1881d4040d80080c4105105004210840e0703620b40085600c40110800d092440e034035440050540000b503030202c1d41541c0703030240200416810903620100c040c000c962400c41c5039141800c250342c031507240f4581c600d0382e003052003c1c128884c00303445100e40003002e420002d418151103c91144012110201290b4405101c200c0700480f007080f000c40079041500700014090910740488840c0c41e40c0f140300d1000d010482c02140b00418078030180014074040d49254941039440c82d890400130641182405405c0c41c0c82110000010346600008046c0032078655062008120303031650b01c0c0c0c103070b10000344140207003800a0700f000d00385000000c0005010026101c07100030303111408c0002c040c00b00c0e2010b03041810740350541002841401c40000f944103071507604442816401000f40380000140a820140750380141d801b40c0140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 571314271 1250 571313021 571313027
    0xc0d0c12051503061303020d05070311060a050f0f0f06060a030e03030f04020a15020703020f040905010c1e032307050c1c0f03051918020d060b040c021507121b 70
    0x20b1807040007201101c54a880b0344101c0c440a104000c00100941e110040346401c07103001c0d10262022502038206a81e8620b1440e014509000c4200c0d240140507640c1d8042040e040142040c540e00801818807001640c80e018085c80071612010300468480d15010800d40b032924840e400c840d07051020602541e880342005407140c0414101070781c00301d102c0d16840b0700c00b0500c1c5114a40c5c407403058a8983c0146599403454003405003030302ca20700c4020380107030b211100b103404601c00340190354800e0242e80c1c2d002c1001c100030041030b4461441014584c100360903d030a405440d1a03001e507428501d5040c20321b4a00300e4646660036140c0c4d100703c00c0e107401e1a0250802d81110240c11030406403c109071512230703007244440e00b032040301140c004690050140d020203000702c01d01a0f00b075010804100720ba005105459020390000b80900440d030390f04440349511640a0722450800e40285202380344c181c0001c04480c00c600c180c034081050000c081c82c0400082c01800301e00091240c00858081c180230b900841c0d8108104401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 571315521 1250 571314271 571314301
    0x3051b1503060f1324260606060304230c120106030c030b0a020c12030901060f12030f0e0a0b07150e0a060b0a0e1807080c010504140a26060901050c0d0c1205 69
    0x480d00940700100b00c07240450701d1b040c0c0d268060f11b0440c0a0442503484200304040c03500080c0080c1c1c4c0c4080741110941801c842c4c022140d0104080000800350840d004007008003e002c18440810703164100b800c1000010b030902d26000a803a17000c2c00100301e503902e8400e040d0007402102c600c1060392107440b60003101d980600c0c0066001b0303681d040084c0a1907440321001100702c0d81c0c074850311241403070507903026010038070a00000523001000e142880c8008902800120303d51116040b154a80900007803920400c82003802c41c0c07110620742e0205100c0c02c60142c1d43c903034071000c1d0140050710007a151b900300d200c260341d0f80f80c820004e80820381d1420b044c3e08058120210034010428440001d1058940201310000002800804800141c1d103045c946030070003c9440b907500c0586015500001424004240b4401d0791070740c20700740c60304461a80041d080d500c50b164030b004000b07003540800342d2501c01070003140240401110304d003035040040415640d003a05c7e0111074095200d0201d403046480c240910841550040038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 571316771 1250 571315521 571315529
    0xf061107030e0a030f0201050c100507120b04090f0b1005030307060c170f0c181f0f05090d08030402030a02090a06080f1203071803051b1503060f1324 66
    0x114600700d150b800500240114030302001c4d005104102814005600c50402880340c9074001e4290f82d0f0302c0041c000703000c00391142660350300d0129a21008015170f0b20300390b200b03070b440da803a04450620510300d55896203800d0302007012016100911010002d0720b40300540304420000c08000d001c4030354480107401d10000418509120350009143c1d6808040441000c469042c040c3c1c1c1281c40e089030366102c0300340e80051940044400080e170a2030040b150800d40d10000e14805e1280700c08c1c20700b402c40044060040c0b1400810000e042806070900c41c0600b01d407200340c0e100c540d071940041881d43d04c2d100e6000007482c0c0500d90300d0095015000c0c408008440c1120303008030084800301005c94030001d480c516040e4440045000840304e032034040c4000780903207116405d90f8030b62029030150f0b4400d0039103a4582c0b42c00c4c940c0a20000541001d52030400400c0c0c28010086080e2020000110b1705508001000034a90035a244240d885071002c840c40c41100056540583c519545906020032524410141c0c80004801442 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 571318021 1250 571316771 571316777
    0x30e0a0c09020a1b0c0e1801060b03061005030708040807080403150e07080c0102150601110604030302030f010608040809091f03140d030e210d051801060503010605010f08040f06110703 81
    0x1310010316203144d00c41244003998450b900801c02c03402d1a280c1040c075800202813840f600515402c51007107540070f124410242506040d0144d5034940201400180b0070313105802c2e002c0120800802024951102c0f1a640003948031100d5503031a11107040c00009405243c01c05840e20090200d00c3d911f03000b89511081d4406005401e5a83c0950f0b5171182a0f1a40580140342e409a04141c5282e5544620050041e90111050602c4041e103003401d450b40b440d00c1030890f07044020940c004144007605601d4a800e500501003890a100740d460585c1d20381c5854054464a40c0c0960349801c045850b01e000420021000d070100a40149203550702d0a03c5648118a000e03040d00c203000315403a4120080c407070301804980423600c00c02020907014000c000d10f0b171600c03541400d00b40110305001900150015000d814022411801c180105e41d050707903090307400c5952961050b480303070780741800800c030f26600006510a00412030030040016581c81c200422120300c80b0703c0003420f50f45000c1e02441018541d40c050103401c0d00030386d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 571319271 1250 571318021 571318037
    0x40e09010b0f010e04020c070b03040b0405070509160c150f090c080a0b060618130504030219030f14160501091209030b0a0504060b09180f03040e07030e0a0c09020a 72
    0x80c0500185200e9210b8103400030306002c0c818821030400d80c0050400c1d13003180f4201e840003941c418002040d80c109440448500070401e0911041c8241042560090001151840d4050a1947c540d0b069400f40000c850207100c4040100014000003e84c1601d00200c010403d011080d07070040c99000600340c8840c210740e241040e10300810b03602c10010f4044100b9600080b1000341d40c4404c001c00180340c12415001c21014401d100c10215038555801c0d001d030040030010046440e0600d450081c0c00c1a8803000c500904440010307120011236071020449070601d4103424060220007060030380c00900d2003060b81119078044807030030082c01c0020540c0700c104441d0080c080200000f10403070007110134010780d120141603403d030000401e08a03520380d840300c1d8015110300700003e0521805804222494070442e0084045604c0d6185954000024401c40040d2107058015514083c1000b008142c81304024100c18200345c0d4442100040140c100b1904a001da00545100c401039584d2800307170007951020442030300040f104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 571320521 1250 571319271 571319291
    0x604032003192703060b12010e0d0302090123030a15081f02070b0f060a0504112502060f090307060e01081506040f0e06100e1f090b040e0901 62
    0x1006407060542c420412040c00b020800045508030b09003550f5038030300c9940848542c0b00852144140c802948599804690040c00a003000460302011140c0100381c1d042240341e140c050070114048114902504006031141101d400484038400d400402c07040c4005032150b0b440b14070740381801071403150386641c6007031050341d008040101241056204000c0c40d948403909620203281d000e8244174040e40d00d07040050900d00d150700d840c17001480645e101804100003600784042d5061424202010709000d035410702981049155070781c2c00b071050305101c28030080740c8000e0b5105103868100083c0c031550000c0010b51556a41c100e10201c9034020380303440380b080c814640c0000d64203000e84d007000741c0150b0584030b12500d9550503100c4041c0c401500300c4c0b0b5501250410000c0b9013241d482244038081c001105010b0341a20300071041c0441062401200d0080c822078070959030f00c85d03842d10050034a0310300007001c0c40800643c04070207a8402c0550742100311880301c04180411b80500d540a4507100341c400303100902000d0b4407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 571321771 1250 571320521 571320523
    0x40512011a0a120312021303061d240a0b060c060a06050d02090103031209051b01090906030203061303020c09070305040b0a05091207080d0f060f0e0709052106040320 73
    0x8640f0414004a03440000302c8086800f0f2440003a004802c2c0b07801524041e16403072040c030301c070b54943c00880d407690390364107007041c0200554100c0812007101d100401481910380b519600c991400c0b5000d6080003104e80000d5031a0b1300c5034100e0710601c40080c010a45402a44440545521044031284140c6140c610001942e00e403a0041040c000c0d006440d0460603401c68038100d030080560f411032142c99031540d19110010304104003250030381020040300090550404001440e004842c3e00c20480c1034101041030000d03035004519240c004120380b03000601c01415280980c00c00111140d043e0344240380e502040780c41134141d0070042c407940c41020a04050b69843c4013220481300150303600c1d1915800707040b0701510880d0700401494038a000e0202c035410007195000c640161078001004241607a100c0b07000301710b03292000d002400945002180280b4074a000c5400402c0e119407446250b00c1034188619035140900c182d822001c0000c09070055401c0da01d441e040151a044074030340e42c40a01096255000c8003100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 571323021 1250 571321771 571321789
    0x415020f0f03090a0f1202070b030405191a1905070203130303081b03010305150c04030f0803061507050616090f0506030627060316051014040512011a 66
    0x60156416400c04803488440c0740e00307410051960300c692013483c4502004c21015800c51011510070b144c00d100e400c010303030790003800c10019a01c1101c5645007401804000707080850f4a00f0102400701104500c801030742011403105c1030700800714102d04118414010040d100c902d100c40b174410100004d1210352650f01c0e003240d4031b1280d8405015940f000c00414400284113000d119000402d152505a40882c40244040f89034001c0c0d02c04c86d41e5030302150121004580424141d07601c11034261155080501d1a01d0310221107500d890020040e4000100140075035483d0454103807810b40d9441150f8035600c0c01d2501995820095500140d0200303181c4654403114803c4500c002610100090900710341d1508040c8240c60f040640681c3d80824512001a4100b180050304101c01c070901c010503415007080360601d03051243e21480350f03d28030038101c020f10080d202c0d04422465406036180c15001c04040450481840c000d0740c10a55100300901080205404150000d000500000039584081d01016042001e001c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 571324271 1250 571323021 571323037
    0x50702092802160b0c0702030a060209151914090f04090f060c020601031e1208061206101a1201050d060f060611010c091a16020a0e041502 61
    0x60200e400030340c8060058040552941d42078459418030701d00705014100b60382104030b103002c0c0a010303000d941051000c03088182c3c0d0040514507585160100c15004240c035840003060141540b40c00140762612a110404001d4400544040e61a02c3d222460700f0488445045180d050000e00301d180b8015294030020201c400c24800180607041c60350b41c1d48240409010381c0d4000f6503c43d04013241c444040783c107901515900070203076030180044e58118a01041040000220000a403243d46c141e44002644a512915030010790b0401c0020782e5210000a0419a8103180206460040307c0610800400708031100d030039160000218450820184801c558130700034096036480e00b48010300108458140751010b0140540146c8001c5260403403942d460040d82c030075501c102c001841f051858403d040c4207105201d80d41c0070a1400b10312043c03801c1255104052691510390009500280e0043c84503800104019034a41c0070b4400c0710065038580c0c0d4100001d008a40c241c0d80302844c1c408503003808000d8400c4510301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 571325521 1250 571324271 571324279
    0x1202061b09040f14010311090703180201030e0a230c0d050604020d020d0501020c060415050f04031110060b040602011d190c0e09010f18050715030b0a091a01050702 72
    0x10300c00c030700300300107403080100030404141e46190181031403045106550195000b01d1603030444109820501c040040020507200405207040701140c2d000e100d100103103010a40901c2d000c036500038a281503600b4450b00c2c0100520341e02c42803e20b0200900941c0203134075014000005c1c1c41559048109000c290c01d50143c00820039045000014018a4000c0840380014005072100d10f000602c1e90703c09003264080030008500d030380030000704000c11108007081c0308151580c110074441802d02c110308600b490000b070310042c18458207101011a0030402c1012042c0585500d030306100e0340c1e0751507210881a6001d40101030055080c42000c148841806e110002c0c101c1b1070078004c14807c6503a140226401c0503099048130002428440014075003060719035a4011003500000080b100b02c941c0090741212001c012080310111842c80d030a002c120003013200c0c011108800c40b0300755201c107241c0c4110001c15140d0203585c1e20840003040844c0c501500d500c9040249800f5060404403904c2c0c100548042c050003000a505c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 571326771 1250 571325521 571325527
    0xd0f0c05060f07060c020f0f1515090a090201050c01151707030812100504020408060601030539070f0530090f030705030d030e0c0402040b03070503150901031202061b 73
    0x254103038494542007480c2d00c1580c8447c4111f000c210b0030b0482020216040354850800720301500303100c1003c80d41150510070700c110010301c9400458203905000b0204e4055995441d404015a4060070403100080c48a04c020400880d003410b11140380310060007002c1d481d030307030050300c40e90400d40010390181665000b82c0c4c0981030054140020303a511000601c5145d071094440c070005504e468500242001d8800c00018060903e000070004084a00013002d11800340c555a20010881400340403d46440016000c1032090380d050551290703c0e4494028000c100c071040c4901d00301800306c00314040c0890305000140d60200e40c00c0700c1a41c60851b500d496a682035000c100415041458901e1151215203409010340d0315196640c8006030174000742d0904030b0007194440f11b2007200b4110500040030720b1182150210b007060b080000040144c00010000d20030701c8000000707d038088100000340d0400a40041207040650b859103041c0d2408141104640b015100d04004104584d107010b2070425050303848030341241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 571328021 1250 571326771 571326773
    0xa09110f03070e130b04031d03150c071a0705040e07050408120705010e060f0727170307080f0a0906110606090c0c0a061401050d080315010504050d0f0c05060f07 71
    0x180010f8054822801c2e203c2e0310700c20100089040d94030912072402070715852080318428142a40585400c41290b20a41111580c1e061044681c1a103d42106104005580f1503c90307151400404442d02e40115000c01c050f002c0140e05a4800010b00c1039230510f25541801e501c0b084000e8516000f80c0c0078941103600003c2c0c0103400d5091081c050b280c3c5601503000411070b4086401c80b142000c0f4107442070600350031030b5800c21215541090303050f10b02d8030121440d001d0142c1e0b0309500c407000d07105901804020148000c035080c0d001304100151407865409c88074080da82d00c00c604180c152540724440366400300d02104e0000400030b002e8404141c29a501c00d0140c05a40d681c2c5080206c9030074024201d810340b403010710401c00040801c014043d261032040768009aa9034040d141c0341c02c4107070160311082c840d0341c03100d00c810000707203c1ca829240c028440040b21409000c040707005a505000e50341105800c11840000700e030510280704060340c0d0a50280c001414002d032034205000b018400c1c52882e0300b0b005401c204d514 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 571329271 1250 571328021 571328039
    0x70606031104150b07123513051209040b060a030614040921180803070b0906010f15030b1e1e061b010b030601151803020a030209130206030a09110f0307 67
    0x10001d0200d26000030000c810311f03501e200c1a405030400c891546005040000c130103400c0c600c0c03203411002c0d65404400c060768564034103030313104580044101d05180218030f41c020b640740c46e0440f40e115400140441c1d2a4643c0e0540140100345900c40c3d0b10069039202022041d60a10784140f400c004d40000001e011542c103050180c0d501100070010200300480000b60100180388100c0701000340c1f141e540030719501c1807981400102d982010b0640243c1d074200c07100400891040079424022502e20104044c0a824240d000790020040010401d400c0400007514510003003050810220004084038944d200b1070815560a203a03414880b910343d00501c1c20000b0302c2d086110805040101c403482c40000c1070013611107000c01e04050b401c4c2d00034101742e0791092507540321540081109008901905406141134076503000502561007a00c4040c3c0120140e1000c61914407a5400d082d17001c40e0041d01d0710f55281024540c4070002d00c5011420785032042c500300384bd452071420001081c0c00200090040040e117081034020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 571330521 1250 571329271 571329293
    0xc21050c21041412030307030b1521040804080328030e0c010507060b0a0605031006020a0804180b100216120c090b220225150f02070606031104150b07 66
    0x403a1300000b540e80d0f03065002d400700000c500c910303140d039408581c400701001441400030810400c0728003114217211003100d070080900c0c004041c42c1348041d00007a035210307401c0c5502d803403169405c081d1040c00001581c1c080106444105c110383c120344d10b040380e4070304480e15007101250660849048281c21040c0c1c2014290301c030f00d01505401e40038402c0010031000047c0010030400c079503401200881e4010040180c07a8005a405034001e02c0d02d80060902a4501c0e82e50102e54451401441d1480c2e801041c103400c00821740e4054425510003810840080700d0b00d2801944d83d54007030b01e9060000c05910404184032101d01208800150b1091407181c09a0030000d0a00103803c41e20a102c2d00041e2440441500452040084011a854010041ea21060b518900c400d000841c010340c191406c4250b000b0001030440560200d80180745403000a110400080540203440345203c003401c0c0b03505159000c01403100c445000003013000101e40c10440d605000800e5904120303248241015500140b094001040004840c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 571331771 1250 571330521 571330559
    0xa0b15120106050c0111120403030b0909070515070f141b01080a020a05130e0f0a02040303021f0b18101203021e030d050c03181c0c21050c2104 63
    0xca00c0c0071115101b480e4540200040228903074180c410f1005140d0148030f40b5040341c206640c2c0c004580b60100c0d55640c1e441c0c00303100d9a400b5520308844940d06a8160058894003a88941d108402000ca0304107403011620b100381d009840d0041a00ca0051010142d030b5400039020182c648500c0d17a40c501c00024001e401c000301200500104000011030301c040c0400300005860713000c1c002c070600e040168131307008da0130f4005080d0301e40c16104110a10202e50001040300300004002e82520414210481d00405401c50f820780c20307002310b010b5105502503130300d128500b44210052145502100d5440075010003090000782c0240140c4c000001c01c0c141d080c0100207410301094000b00305c1e4584080401868212502100c030880880c4004c42808010000b244001c100d1008840c01850050390030b40c43c08004502e900c2c00c1ca02405100f4203d5002c002c0c420040001c1221400d0383c043e40702c103000001500030342c011072301c620650141200c02100d44052000485c4482c40b541c20140c145410007501035143c0030b048503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 571333021 1250 571331771 571331773
    0x301050115110f031209100c1202030907170a050c09130308042a03050d031e0e070b1603020607090f0905150d03030623030a03030902060d02030a0b15120106050c 71
    0x140b5004550010802010f05119031100c04041c2c0c42c007910283e0500c407203002d003400719604008d0034807410755000b104a00040d030b0456006030799403244050549803140503441590352080c0b52000d540c0c510b03008240b5800c0b61303014206480c0500c21300020804403a00840320201c1c030072800060403022901c50f141e102c0d032280c850700444980f520194040340c0c4040c600300403000d20007184c3c0014010800c040c8403050341903001d82814480440d038200213403039032040400304809659841d0b401510040040010500510014041700d9580d0b1105141c0d080c3e9000803002980036210b0711006c0780c48031f41301d484081d08076a624402030312140d0604115601912029000a40c1e03545041110340e030650340d120525003454440e842c002029480c0140305441d103c80070b442200180404a906441910089070907486564135150026080e1181d1002865a020b8440118640761011040250702480d50b0f0002c4d4245600b150b0703080034950741c251050060b2283c414402c5440100030010028a8064405412030b001480 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 571334271 1250 571333021 571333033
    0x20a0311010c0501110a030c050c0c060a2a120219080306010e090f07080105031b090c071502070218130b061311090f0102150708040f080c010209030606030105011511 73
    0x40c40f440c3c00c0d950304018000407038800164064010782c140c82040c80c0300d1464106a41000c2d002c0e103d070b540740c0214041d8240100000249140854450080355481c9410802004032044052034170040002c3c211804403848140261000c100d01d0002400e64512400c144655003070059030b42d55400160806003009062082900139103a05170f03604400c2a2003005040881d81d6140303849040100341540c184e000d07a000f50001d454900465682d0039151003440c0c002d48216165407100c0b006190584903040024242840004080808400d981c00410000c0c3c000c031592084402c00240700140b03010203652880b500750a01c5103e90001c0c000280c0d103507001c9402068049544811441c64055819903c000842e80c040080d900c265860b00030800062001c1c00c1c4000c1c101d03074001905c4500075400c0035106400703004603c1d00090030010800040105590b1000e942c43d1904000c40840d0701035004805182e120f80a504005599420305214040c101e694480030003144048001c0283c030020b0704202d4030f4207140070ba0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 571335521 1250 571334271 571334273
    0xb03010305031803100c0e19120f050c062b0b09011809170a020f06040803011e0f0b040302040f090803072003070507030b0a020c06073606120603020a0311010c 70
    0x6c0c410a81c03004942e844601d040c0c2c81e0a010009100070020420080070080f46051041c0d416002c02030945a41c440741c0540c1010090409501d06503a41d0744e8103600c10750024034282c0d860510480400c0b801031407044c003107203c02d200001d10259802d00103d260000b50410041001ca0740c0264030407060030740c941d0000780f843c540da2242c0030302201e003000f8000c0101c030010b0040030183d8100600300800c0381d458054510b5041a030380e18101440184103c81c1100c00700c0c00203106049041c00d0600060030782103060400f540d40c1c2d8450700c00981052000340e10892800f008140d00c0c0d40b0a014008005a0000b0000d00d50f40d0b07607040580e40d0010100304412034522504410b6a000d0041001700303030850203a00140909441c514002502000040c400004680140f05412601c0f4000034485d41003c150f0800c01e090428469503204000c2940215003015588000160704161010002005480c4070780e0319080c02c0b203180310442043d40c0c9644402500100603046c100301260140d010b5003e032100514080c0c05098807 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 571336771 1250 571335521 571335553
    0x80d02070b1810180201080402011e09031101021603120509120105090f1c0c170a090e0106021908030c221503060e04020d06060b180a0b03010305031803 67
    0x400c036030080d41502e040151841142080040088000030f0450a2000080a40d20070382d04880100780203040c0840240400c0840e80100d4140002003c4480c0d4004200b400d40402820f40e103142c442511103d614002a8142c2d5101287c1e8414610380040140f1074a881d5688421003400d10541143c104002442407141c1591104582e42c1c1c014216800844d1500b81240c05906103880e407543c840342030f4803085080580c0c6200525545c1d5545040c1400311a043c0182850085140007008001440030001171000b4181d80044c000020780c0c044488452060f0b07240c03041a40d442e9121039034280b0000131121600700180d20360004503849607008024906110400329005200c1c8403c10489000078056401441031003240110380e542012140340030b114840c506040400104000f41c030107800b40146c85140001d2000c0f64000310018420a4561551103c0300c0d8105602071040d150741c1840b8401081c1c001400b5075142080d07a05803908640958076240905004c1d29004d004004059058041d4010b0b4007040340d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 571338021 1250 571336771 571336793
    0x904111206010305070909090c0512010203040b1807031e020301110c10021201030f020102280309050612010501050d0b0d12030b0415090c0e190e0907060804080d0207 73
    0x805004280e1200e1420500200100d0020702050400d07150108001099a000d40f103a0210b94542200152448003414860001140c541190303811181180407800c02d640154019407055000350500602602c42079490480c0c0007400703070096480d034001c100900100d41c14860901c5080019080000264419400309083d10b1984104540175080410400100d103400e05c2003800d0443d100401310314010b0300d000230480c000d0040c0400f0701044c40103440701c400c590003081040c010700f030780b103030340026000d0004044103c045000e4800c03000a5525080001d0b5401c00c001915885940310a00d03610304c5e8240340045400f40c005c400710141180e01c032260704440d6110a80d00382142070140818500c925590380c0c001e41901d0074210b829000d10f281a4545c0d001c0c241c0c1070b00180c181d500290340860311844a400c21075103c0c21030a03c040d80000c032a621105540c040380d6040d4122080ca00700c1a0556583c020090746030540c510448000c00c0d002c80015000984120040803c42e92540c0c0c01800c04000d0345884602070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 571339271 1250 571338021 571338041
    0x1e020c0d06024302010c0c03060203061503041a0405100218090c0a140901050409021308010b061305012312060109091107060b040603150902090106090e1801020904 72
    0x3590000345403c0c004096214442800c4150100d03906000400312040d441c0300c00d071222400c2c2c01c01c01c084200304580c420b9400d146559002171400c601c4d039807070b410070000a41c01610b005200e0703800441c0310044102d00b03400340c034422904000b80d2108002c200d10565069107000b071049801c0c1c010210744401191951029000403031044480321052175180302440044030000c3c064460a4009022404045034001c080c85040c641544100b51200303841401601e8501840c1c000a100d04d001140640701134207000310060032070f00d1010090040c4c1c2c0800042c40300510800442030000740e0801070600095004400302d000007548041d48030343d0b20302d507011440c1d0306030003440c1000069410401400503641e48140240003400500c10304001080c185c0c030070103005200d0b200c80144019102c031520090766403581d10600c019134101c10210070440c8101100d40c0101071030340781244a15014000450070b01c0c0f0400c420002d680d15500c600c00f072906c0f02c58a50501541c000415400e80d9000c1104090035161801016800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 571340521 1250 571339271 571339283
    0xc10050108070e0132030a03030f1103100b03130f0308090607050f0406080405070e01030b0403110c0603060d0c150203040302090a151e0902030403050c0c0d02011e020c0d 75
    0xd50410390040d04284069100e4030005012200500c400072500021100b10380d417620006980c10b0314a408003504440e428103075135140c0219031110303052540580014000c1c41c0441020820b59514140e460340c10b010030744560008441040342031110341c3c446401036030440c1780512190750704401e550b254041c0400c0802c00701d00048104040c42901c8104025907a008100b509089082800c04850003106003d64864801003044000c0400c0901c5818480440a41722000c2c100100f0760b143c0c1020008001c0903541200055482c403240d01429102041e8016801c0008007d42d256031504400c00c08480d14401d0141d4910a0903200001d4602c00e0000c040000a00354010719100c2c0c1c59401000101c0900815040c0400e050400c00b5107900604101d0209445480410407203080f9524815454107402d6000880c0712407000007840103158105014000341c049400483c2d101e442d0000c140480d00300030440003808210407490040c543c114119106601d41018412240d2500c0d480380052003402504c032041d182 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 571341771 1250 571340521 571340531
    0x50c011503110f0d03121d01060b0c120a020304091d01050a0c030b06120403050708071202030409061d04080d09050709090507080a030e090c1909080f0111160201050c10 74
    0x141803012001e00c06810881d144804041340f03032006400c640d10020124041641d0b100d030881381074032620719014041c0d0701e14001c01059849080a15455000c1c4146074010b11440b120304101002e0001102c0c0f18824039809103003480c1c5070444400140c03044280405012240b400c1c0720000070400d11034030b40700e07804012002c18a10300300c501c05000c17a40141c1813680185810408200300703500e002e1803140c010340d051804c0e0f682d8521350301307014955004403680200084005420441c42c1d99002000e001900d08060003001055641d00b4041034107820085030450440102002034003188103400039140d07407400d0620105c0ca980301661001d04154080d081011075a0751a02d0b02e030f00340001045150082d0410304001d210342d026a4402400c034410100e0068441d42c4031500240310690948151070031140c6060050100038111017016095480c10b02603c2e11f18420380c0c0340341a444805004e4400303c648018044d0340740030003c1240810700c0c08a44400e0b814002d04005040ca032880400c8100f0352110000c0001603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 571343021 1250 571341771 571341803
    0x12090c06090f030f1103190303090b180c01030b01030e0106030302032104081909091a040c020d05070f080405090c13050105120f180d020d0e0619050c011503 69
    0x40c008660460081246038610620000d191540040e02041e0032400c5c01030700901c43c0c0c0000303181c560318484407035a40c1003c5121504054054020f14081441503109130102d6550b04c20540300700150701e07142c0400e984462400016540650b12030b03008640103250100f9110484041d082c00c1d41c02d164400c0740140c1c40080c1d003400c4c42c0764121000d0b4500e15440501e01c25410141c03500c44103030183c100e080e81401c0c181c40d0004a151300138103402008007211001030000e08900085a10440c1002e1130290191741419030300c00c00705101240998101d000b035201c40e0305010075907e448140d88a006012582c0c014100008100e5965104c0b42c1e6100c1c2d828030600702e6a600c640d804401d06881d00b0b9101e00e044c040180034074a01c08a4100c4041d5101140014050290303892200f0103a0078203c0c04281d9000c0e00425680700b441c5540800d00d01840702503510b8800d0080140c100307110131441851490800d64040440562240d0302c02c9008060b460342000010a9154400c4004100014545d004582803205040030721 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 571344271 1250 571343021 571343027
    0x118050a020a051e16030903031d1c020102030d0501151403220f020d060b0324010b0c1006080304030b0703021e090604030f0c1707031a0712090c06 65
    0x9584003982036015424500b02c114064420300070140f4410a28950551500100d9201c070305603080c00c00310110a81139032482c1d040c050b001d24010f0000f50b000034207000f01e0500303074484805680142c0c40b024084180221070030000c880c02004040c0102d04501040041d603040340441c1c05031a01900c1001e07601a103000c3c0040000d82014086200e0142141043c410061801190302600d546200c25469100b400d01403458001050480f02e04000d60001071829484140301040c1e2041d10080400d404a4a442c0040400d080302d8030250111034250b05c3ea03080050050740c2d040c0c00509070340400c02c0122045490513100410541d405c0d6009640c03650b00225040013400b0070311002d80d03000602802d0440c0b40800305000005002c008844c0345402020002d8042180d8039104220303001980c010211000340700306d40c40c001801004a10800381010030100c141d0b05081e201003070f820102e941c8290f035581500400c1c90500d140306001080f40c003d00c030300c920300d8200f01d0f0424000c0707a80c014031559090390310070b0038040b002d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 571345521 1250 571344271 571344281
    0x10921021608032505030c06060406080c0a0512210705010501090216021005041d1501111f09080403050f060708161209020d1a0105010806060a0305060a0b030118 71
    0x31264400000108000e008000320440346900d600c4289451000e07012041c050113021300110040c03a07444002100041c14a000c1401c0e4040d1000721010300101c1e03541ca01c030340e9503840c145460725440304840c0350412092805500401503c01c904090b05d150b6814480c180310350428900140c140c4200c001129810000c00780f040e54050152064110304040c0360320800420785a100720300a00440786100c3c0300c0d15050040c41684d004000f250141d82011444180402d07134001e0031b44420004050741002c2040942c0108407070700c408000c44000340300400d82ca50302c00c60b15882512242404907a0b504942011461080040007d540900024012520440c1c1c00c140360500050182c2d0812404905000c0078040058000a81d02c0e500d161038514a1024800d1000a003042c00000317621423161711500081021440c0c04111007440b4405c0003040d83c0e46d400055840742c0c02103c0c402d0b880401002041070460082c0c0c015508600094221010181c40d00b1201e0f903540d00a070401401127404003401c0c045017800b4015 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 571346771 1250 571345521 571345543
    0x1204030806030a03091502011b02010b031504020102150408090402030a0b130603020102030405010507050c040203151203120f250e100918050c13150e040b030d050c01092102 76
    0x4040c8541280c44c004d082d942c4500a456a40080881c0c914242e403007508600100b501307840c0174a40c898110200a40240190307100300303029000308101c0d20306a124000c40d41d8402e64042e0081c00040ba5080c0ca190003042004000b150b00c0c1c0383c03c0c0480719050302c1d144003451144080640010320101e10300200800f40c881c00b80d5164203070f41061420310040c0d80c044245d4007242e41c282000c948801c07583c03030014103110756081d056402c0351010081104c454030710b142c80316080d8815134018a00750300003258541c684c8100020b2800c2c00ea58080402e0a042442c0b120076170000e81403002c09042241411003104198255031002c002a075241205620b6181131003200c9070415441c101285940d150001c0a0703401c200e40c041242c5050f55a000142074947c07660110307500074844040080c038403603d440000480354100c0d540740e00040e1072841480c00d981407174407a80c031790b50f00000c1c0100103406c45408120b031b0795801100510700c50754039190340380700283e0507240e00010031140c0400a10021501e080091800e05a001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 571348021 1250 571346771 571346773
    0x30c050a030f2703020103020c071e1505030c040b0a09050303070f050c0d1106220b04140a1211041d07080f0102072109050904060227181308120403080603 68
    0x3c0007000440b90101e00c0c01c00c681c1e0a08001d40c44442c008812810040168401500c0c0080000d68909038400010014103490441c48070350212101c00508448501003280e8080504508200900040008074041d1411084c90b01d407240105844001190a6820142013202c9081110b080901042401c1c407011840d40e0f82529109200c4e151034a41401c1d9014006415000d400006211250356420900202224020308030389101c55035280e011103026030291055200040c01380070f4170842d43c50907203800801c452055548000d42ea034251a004550890310a0581d4400d075105440701c0d00803951021b0701d65555006014002d00c81c074103800d8a041442840280f00c5907407040100c840003d82c0c050501c0f83c10340403848492810503070f0306025202907032190030080c0d0203403d00b420802002455002413103058400c13201113540400d5092051414500e00010940c00703d82000c1c1e8010405211151301d50240c1541c0b25610f9440b12501c0c4d000707844d8001241212900d1101040006041c2c01044c1c1c00d8020038158 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 571349271 1250 571348021 571348067
    0x40b0a1d03031b03090604080a0501050601260a150b070b0a0b09040f060b04021204120c03050a0e0105071a040b010b030402130b010513060e150f030c07030c050a030f 73
    0x24000a8982c46110f58012030114541d8580d01d031420104150b8588040240c4243c0e600c58036048501c2c4e540d004500100d95960030900003030140d510405003412503182e0031000b03d0095180c00c00c00c2080c001300a2503440142d41e540306600c03020100c9034150008010320318a043d5940c147d801c000416240092003090031608001c0c40300340c103445800c10164017682003c55003c6800b0381d40b900030044c0c80001601e652140c00400c203013060980300741440e0701842c402e10111a00188112080e6100c168005029010410620200310014099a0508201030052404c1883c0c40c0c0140d17101c01c040402c26024603030000c4004100000c00c04020440c902400d070352048607055107441d900207584040c0c050549d0304910348a00c80598564058410303224154018100034541c5921010b00801d21842d14402c20310801c4a80084040040f1700411a0065030452040030325607511007e604449030f2000808500300b003140140400404d0080c0310f02c00b0740902c01d50315180f1308642c0400c02080c800c843ca548060f40d00c055 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 571350521 1250 571349271 571349327
    0x160312200a0e0d080703030204050a060c110405180a050a11120d050f09120a020a060525080f070503030f07030b030a0209060f06041d0a05060108040b040215040b0a 72
    0x40310607a4200011450b082d00000b030741c1000300b4250b000409008101610110300b0008154142e0040c0065820903200240b0307c0b692460101d0351300b4161280500003602d002040f201d54201504501e82c820300b00c2d04940901a41c2a454a143c401c01e071009503101d4210501100c1001005483d90803e214122a00710507010051012919800b03841440c406108001915040b101d12002c01d50758a102c1c018001550720140c0840140c4135003103034030200c1c4030b044c0c0d0180218003d401641600d101121290108080742448503146100c1041c0c001d00342c03034051051242620302c40c41d40d0000c00b84148601d01440e00d038103060a101619002c054601814142000041710343d5860000381003054075011070705400326464060100721024800c03d4826041180010003086080000d01984040030b101c080903035440e40c406104004075042525140d0005140b42c01080210f080c001c0c44a41040c00103000c0490b000c01c182100403582d1041d44003082e11340000c61644c21282d0080d01c100400340c61090760031001480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 571351771 1250 571350521 571350581
    0x90606140319060612050109020a09020f0711041103100305070807051807210605030606060403020d1401020d1b230a03020c030417010207141b040b06160312 69
    0xb04207075800c18106405445000d001d4503401000040070b100400448001080c00c01c1406890034401c103a000e00391445002980c0607680c400c0342c00d801561074416050102e680d0300c0c03a00f4400040c141950003920741072a2071a075043c000c002d5001d24900e40d880000103195140050400341103600c202c8054001131402c00080d118800d611b091030201500c0d1450540d035466013500d5000e030f4118551401440440880101815a803081c2c0036038504800300c0382d559540d0b40c1008070700c0c07180d800000d4008404c003140c5800681490460790403c19541b0003d401e00311204074000403030f08021405018135000422440783d49401612100c04200b032141c40e48104020310b812000248034018a5030101540064014940c1100b401514007405441d520b0b2900ca2104580c102d01035000440c040e15510040180c1d060754043c0080c0c1c800d070382c0310600c0d00102011080030070000242000100c1a810010400501318184403400f4441c03411880f9490301300c240111580414119505583d0042e40c0b030a90f01c0d503503098504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 571353021 1250 571351771 571351783
    0xc09060302131d0f010e0c0406030213050705040e3402060720030708030a0e07030c06030c1103030907060f02010b0a030b070915020604030e010509100c061104090906061403 76
    0x144101003c03481c41844000082140e0940c041d05a0b076010f0444007164220741908951a4496440700700e8103440c6442c02000111a410710000b5400040c00442e4907030100d250300410b0340803e050a2890406a48100c541c000903001c440c01c1c02080400c00100c000c47c11001011542c01e500c444400b074030018010806581c400000e89800280054902480c981c41044082d0300c5100000c001681d4442485252203601600140d40d221809030a0060703481d48114006100421603401841080043e40380c40300a8004003013441900e01080003610030380019500c208021400346002030b000303040321840c10344000c1801001040180859052414002056071607598440c2541e0300282a00442e0715504801e8079100032a034031842002078201d00701103000d6000f0849601c40d0380aa226400d03c1c020b9903004449520800413126804000744404180051050300100d0b1800c0c49074000140742d803031074100801550429846010440e44482c604000c12201e4044d40000708401040030014030151000a0740340d078 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 571354271 1250 571353021 571353049
    0x60c0f140d111b032a0d0516060c021005071b060b0d060c08090d02150a020c0f030d020d0b091302010c050c0d080a030e0f070b070501061805040c09060302 68
    0x81d89500e0680c10b500062000c40740030045002001030220950090a603c039000890b001c08250015804c1c1d940a0031a2034081c884112540d01410084c40640c0041c1c4158101d11070118480b040788074040f00240003031240070102ca1203a0024403400c482282c1c1c4c0c1c0c003500c0004100c8020007038103406e00708030014800144a60306a0200700400c6000341d01c0c01050100360020005880c20341000380c0d0015480c0c011700014014605034003541e924500059050741d0300c4444414009404ca407000015143c180e50341e0142c020400c10340151420104c5415201c1e00c1c54000180c54440c050b80000c40505030b070002c0c42002440c0740e040e102ca14142c50078043c0c03054140718405020381808507055070307030301005414002202801d0300108810060720f6141041805d5411100c1f900002c20b00d4078203170f0001170000180041410740c00000411420f07091401c210000d40061900711070355921100c0200b850070102e1518800d505600340300081c0e504d07150400902c01d13001d95008101c45840c1c440180003503140c8500742403602d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 571355521 1250 571354271 571354297
    0x51005060901050c010f1b080a05100e0903090d03030c0306050f030c0105030613020301030309031e2111030412020f0603010608070e2d01020105011505041e0b07060c0f14 75
    0x181309400d59080c0504000444c800201386483c00300d00e05201560b134441c442040c01d42d40d1f403c0656403061682c00300c90301030710544848607102500300320444030f07a4038441d403040f28101070ba81400c03401408a05c2d210509682240481d840707800c404103d550522902d23005050444101108011041c0813a449128032100b850400c01e000000510b9502c035400a444001d884a804542d030350ba59080080031203031203000031143c045075101d40c0400f00c00d200b80542207442d08100354031150030344446403030021358604003490148441000040c00400303060018100400354114461818030143c0b0410011190501b46580b15520600c018401c10384d000402a90202a074107290114080e038500117540c0503d11701189031126441030514042c0700e08010503d822200030780091005980b00c1c0005102c00d140030f1815030008409001c01c102c0b0190340d00b9134075500c0c01540380030b545468440000d00d0341e07940584415920760b602d0b60800300c1a5a44500d80b41400022441e24013140300084207041200d100d191032440e09 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 571356771 1250 571355521 571355527
    0x20607080c0118031107060c0506130201201f050702030d0e0307080c0c120102040503030901080a090507030b040311120403020d0c15030f0e0601050d140a08031905100506090105 78
    0xc002544400c03070383d9000c0c0036000f80c41c02051034001d000e006400c2d00107645008101d000100140200d6030000e00e01d40c4180a070019664103d80c80031a020010810790400818218500c814410300031000c00301610341c405408040844030300072072030300b08004c403202d612881c2c0000c01c00c425a0110507903040d120810004210b01071300340861440d500079000e0117007440b4800034803c1200c000000702d00003410020307600d0340d00040000f60000d00f00d010314032a1170f800d5001002402590740c8260400c50b0f2081c0c589800003045545030b20741c0c525001c2aa00103d41e105039180500c000e058210268280306c04554008085c4110180c0009015025130310001340200d120590785010801b03158000000740002c7c2100030000525108000e0250101020903034105180030000c0c019814041b8295041e10406808810034821665031288550400710700e124160041080c0000018000b40065000e05aa00000031001c001644044211100904603403145030031204d0801036501d6a80075100d03c07240900305951 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 571358021 1250 571356771 571356787
    0x3160e0907030c090b2805040b0a030b0403030203040213020a0c02122e06060e03030927041a0a0504030c08030c040e01081c14030609060604080105090d02010c090302060708 76
    0x22070060240c0009041603883c00700411802010b50150600c00c004a0302c0e980b40861500c150000202c8007054040f000454032002e00103424590403810510101030005003509c0e41e240c9800801d00710544088000940000c10b020542c076100c2c40c4112144e4060000314a0940400c002a202410115009010781100310740c0820068060184041004d440300300c044150308220b480404281304900d4a1108501e007000109843c0d1040300b0402d100c002c0500154908102c100c10851004080a800540099242c9209480841c86251a80114410b82440c40c001070485c007011a001c00091096030914a010700300070101c0d520405220700b20b80c000b41d2603940c07500d80c00701018052080360490b034005c0d1991000040c101c80c000841d802403154502c3c0242d12820760a03000c540105600c0c0701d04640d00801d002050135840d040c1075542d0860710060039686066511502542522400c40d209000f681101c0880c102440d02801074046429407490000d00107421070b80002c901b80641c1c840540381120202e0107003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 571359271 1250 571358021 571358023
    0x1090e150f03100509330a090503070602040303120522050f1506040f0e060403032a030e0c040c02120706060f15030608030306100e01140310030c0503160e09 69
    0x9801c03140180c2500d03100040940da1001030031041e5038080c800e1084421181d021b20500540c1407001c0750341078004401030040410b0662070720003d06115985a40d0303403510700001e4010001800c50318844c840c0903841e50b1640c02c02505100300b000340e088a0600307100801c0040040580e00040003820025001003c908604100e4a4000080460916442004800d4150401c20130405225031811907061050909098081d4140ca4600d0074000240d4030000104000a000f5080010912402c50785c0c0e0a01660040041c41200095010503010035601c03616401d60312414403c011803c0f1040d00c0501a01084010013980c0c2c1c0404241100b0340c20303012a44d0b0007004503030f8200c0c1d00208003100309401895210b2600c41c03200d03d4058400008640b5002000460351004020b40344501e1006100c0c6180c0c840740b1005031500080c1000c20b074100104e0b180d807010340d244d405010394050811003900d20b06003800c1d460428001c171140d41180788280c1c464091200740b00c400c904858140d801050005926881d016001c0d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 571360521 1250 571359271 571359289
    0x604170f0d0c0b04150b060a0e09090304241806031a0405100b090a030b0405011d07030c0501030504080d0c230f070639140c060c16050102040b0705070501090e15 71
    0x190b02c0100080c50f181c9040d4403030300d81402c1c0f8102b203070840159243c240c015941c82c8154441c0309200e44030b2002002c04090320f004c1c071300c140f0015030902640441c6a80c80c18034454070a034200201107545c40070540f20380400b08100303420760101130340c1c100840d042214602c0501c00c100d1140c0e8032040030007d04412a921240d8011000359408440c00d40103083c00d01e000b44c00f03892400c140050000310000395880441c800a80c44045030742001d801d1043d94185801140a484018004d1710080800c001840e25000f40c5e00c6865031200340b0741d40b05138100c00c0e5446541e81d8000000540529643d0038800c00e032100240008588500d50b000100142c0c174000010750340c030120030540001040e01a013000010114011848400c0c2c091156915110401c1a070584402c45014484503400d4513800140018410501480100505d02c44040060074030344280c0e994a080e41d1054008140e911008034201040040c01c0041c070014040c2401e14113801030410340010213442c030041c4580408459101042e0040d1512081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 571361771 1250 571360521 571360541
    0x20d0203040b0708060901031a0c04170a030f02030a08010510021f06180603030f18120c1502030708070303050709090f0c0908120a0c020604170f0d0c0b0415 69
    0x1551246001d042c144070032001120804045205100001c00c00d00c0c03c00b0f5040e0581f43e0080c0b0150319040d4000b102454443c005204800700c4c20200008203d40c5e0010501d80c50101c41080200742c211024a8000c2c16034920401c0c203015980180700c00140320341c00241950640f0b500b525104654510224102c2c83d0110030094064500300800d00b10424207072070b4100005659181c1d1481007210010405072040380c00620001d00021050082e002d25548102110004440b002052000d05902d90b0315501409003034150031aa056a1a5010440d190b98070310f610556121034000380d82070003080d440c0d017131052180802c0102010741d1000040ca61031b014a001c800a0583e80c001001f2042c0e40c20b44d4a0014001c0c0c15146011407401a0005020200000d000c001c291012602d242007982048003520002120b80003264454420b0101141211888802d405244081d100510285106002190800342d413809509c04100a0100700004500014aa00c4c0c11070760064a0380b0044200c00d00707400040c1803640ca = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 571363021 1250 571361771 571361797
    0x9010212070c09150303030c180332010f06090612020d03030e031303150c0912020616031701060f020d08060310060906050f0f03330103051507020a0c050405060402 72
    0x614210307001851107884c1c064a00c01d8404000052200074107a40c0014030303540d10230408050520030310004600065045001c0079514100c90014122010681781c3c0c13950304010300460b0f55482c0e40c0780d44403e6a01910340207080b0b0f05010400740e4181440c1d225038130341c0d20314040d0241f068138403004101842a40200c064510390010b9075111680d0400c0c40316240a03600c0269515503040c504c9141c442024031800450310040d442c0c2d6000d42d460859007458411914601780c7c3c1c080018000c40040b10007043c00e2403185880780c2e5486d80004034181c0b00004428060300b00004010b50000c040001507000549a8100c0d041c500b08419290f0395540000d141c150000940404641030000002d058a82a04054140c03041250030300e009032501401e005003821020889545640b00d20400743d182c0015003410344002d101c12031106400c048200d143c00d0b0f0800281c0c0100c5855201c12250f030f1090b4184a010b0360003406500c05054040d403a900c0d2031031404641d020301d0388115590008039000b56283d60455445458602d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 571364271 1250 571363021 571363031
    0x211e010b070813150c23061807030b0f0115020601080a0b10180507030f020a0c0813030b040b0a1107050d0807050c070b0405091305030d0c1803060c0e030309010212070c09 75
    0x1040042401030b5201c2c2c203c1e040c0c40700c0310a440c10a5250801b02000807503907401030080d9a40d002c2481803484218480d110765000301c407004030110718254942c0c0e114480e800252502540350035840c0d441c10b1a8242c1d8032045400443c012701c01d51a000c41d01c04800340e0000d288007015101d503c0c02a08405031b680c484c151443c3d0740b03030309244c1c4940c1c1600024800d41c81c5407000c11085020b5480c54050744101501180040d005001c544d0005105001500400c202c440f0681c400c25125034800030480303401c0e502603614104071010090444405d018509606500041003030a00707403541d850310354402200b007000003441040400224014416402d89040045520072104000d03035070416a07a02ea8024020b60740180c1070100003e0030003070140070110429038031000075032900c4100c41d8288001d20301200e80c0801c0140303c0d42c0c0500d15034104a01c04002d18080d060008841c0202c80000d80921188010540640c1081c030080c00c0d80e07038000c18140d12150540c100e0341d55410b850b1900d07080c4400c0c9034000000c01c500e00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 571365521 1250 571364271 571364309
    0x2030d1e050403021b0f132a0215060a180f0b100f0306080609120c0a02030d080106020c0a081b030c130501030203070b040e06060a05211e010b070813 66
    0x2103a40206484280c1c20304540500400d000d074030040c0c510020f03001800c050010080400d2076102000c940c1c0c1c04046412840e0050235400c4601c914000d628006a00c825001c1d16025080e80f1800c0e04100c0445145c0f03009854410202900402542402000e03650b0b40700c06010703051503070000d002a07a00248441c520003400500548205046130001c80041d00d080004511000000344031801486c0c40030044c103140c0c580d10401c03501035100056900030384c09618801d00040c0c40c100010110a40640c6840e8807d40c1043c000038580307429028414880c0708101002c224001e4045200305600d890003001910a4500747e01091070060500303091508241c42500c08400c403031b1143d2045060328408c41c2030700d619607610b4240c62a00d000340e00a511505003000041055403600714003c0002601c1420710600344040d850289120301d8082041c010005108800c1014480d101e9031003001c28204510100703000d50600761040004e008061004004010009004007207165401541005200b076000e000d49030205 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 571366771 1250 571365521 571365523
    0x42102032b0f0e2211040302090604090314030a021e16150902060d0603020406080312011202010c2102010507051215041b020f15070f0e0114120103050d05030702030d1e05040302 78
    0x10200c80003a08515205c0101301544210040741c084a80003410001d40d0740340e0300c0800c001000f1007002141071020340c0d07907200b11a9034800b01441c8034103002e100051b1100c44602414801c0c00403100c4a00c5040d00c1009128145100801d031602695000380640b00d504140c41d007140010940004040c0d4014800b0401a00600b50750300080143c034170035581805401d93700c4a40b96503e0044c515040c1c009006d00b4014000340c0c0f20380d82c0c4600c1481c0145421310b040120303a114018403094022070048411040c0340c103a070b40c1c990240502034106038940fa00c6440d00780d24031b48040040001505e05410000d255011103460b0b0b0711a04203030501408041203030f1586039000402380d0760340b0340c0c500490141e0284104110003012455003035407080d2025154201c0000c1c0300c100031101e190520410b00e0501810042d070b04029101840030380000440070000300032650650400c240f600c611411508200502001006680b0740e012003a150010021040880c0302025490081c030800300601c1000909880c0401700014903034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 571368021 1250 571366771 571366819
    0xa0c081c031b0f02010e0f0f0c03070614030a020f0a020a02030c010e01092702190201050c03040c170a140c1201020301031109101505180d020a060c030302042102032b0f0e 75
    0xb23820001c0300c0d083c006400502d500d0380c000348104008111018486881c40f902003000715400011031000600d0042040c00300c110030341000400800590041500408500302001040304602c001d081c01a00c0c03006500000b00502c1190084008840140d41c1a601d2a404034100489551000f40155112010000800020206400080015070800700070401503000b81c4c007224000c40d00801501041c07410f0182c964510b00810703e440c030385172140d802ea5601142440440d245800c41d041b0240c421100044208009640840040ca9099204100400c0003941200c1d0340c40c0920000c5d2800e1000396944884000000800e50002d80244440d42080b249254441d00800c201d208066001e030702038050505004643c005844c0c02034011012101c00d1200a0040c20144c0880c3c1c0710b86805464581c40710303801916407449460011100003024046411444c081c0812019802003440020340740440624001078455491584001e010b034480050a400748030b21681c0804080c0582082c1d806002d1300d40e0226489 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 571369271 1250 571368021 571368043
    0x821032208070f230d1d0a03080306010f051c0507170708070306150c020108060d021f08071e26090c030d031a120a0c081c031b0f02010e0f 61
    0x207544d4441618010f24035880001e1610704c204001c00c00140d20403016101071410094100c0740c42c64040c0300c80070540c0c51064481c003031481490707225102d003000000903103d15051f031400c2c01405401d10880d507401c09100c11800001c0852040400c95496101059800388022140a004090048100300e507064000300e266000b40420ba50400c801c50f92074641041200b0a00780b1440025690301441015620412040341c0080b030003007075141c0c0c05286071700181c121001071100101900d650850310001603002115142c3c01084ca0400100f010b4810b1f40d54644a80307901c825006015104291882014a81c0094100907400c1f42c04981c240c20311280450b030b034508100e20244070344a07000c00340240038428010761104030003050b885da0003e00982c04000790107080400007a02d41c03054400090110700301044900c01088400068001204d890315490100041c4003449030031b1604100e0048070515402c2e6516035850514075115002c4c0850800482c00340808448542003032040d25800008180c0c0400d0131400d00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 571370521 1250 571369271 571369283
    0x30d08010602121207080a02160b010e010e0f010b0706140a1a04020a0f0e060d140a0b15040501080a0e010614030f0d20030405060703090821032208070f 67
    0x503002d81c0788071041ea8410905215000d004c07100c04180e540d80600707401c90f0802c4d1402005800d2a0f0864400d2414050520040e2540d0000c0c0c401005410a4140140c1c0980010540800390789044d039043c41c6010070612681014010000740c0109002480e801284030f40000082c0002a0508106901c007820420040440503480d0440d00c2c01d031860980700b29610140903480d01c10518640718020340d448000c0c0002e07160003490400c50350000c4c00e0140702d1080c10260f1a00c4c15510b0381040c50035941181c0c0d403030ad981ca003c1e00d00c802122403008880b03030907601111000d192104040d913901e92508068460111441200c0d800c000c408551100408400c00e04c946058044517000e40e41d0407030842c1e4074a0041e1588001c03800c140c8490300c540766101240248950740504032450142e441b0082000f940c40700c5170540000d108030708140001c070018849039200b143c080c2c621b02c200100e50403a086982c40040c00325442040403d242e0150140180003040205421200c4c10f91110311030b0030020540c0440500072207003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 571371771 1250 571370521 571370533
    0xd050a0c09022a1c02120a03020406020d030618050604020d05040b090d0302041a0307090305070803030703060b0703020601060e0f0607060b03060105120a0602210403020f011a06030c0d0605030d08010602 89
    0x1082c10440c600c5a80700300f0360b4000340039841d01c0700010100115030843e00e10840c000c0004000b80321440d4030040480c0369071664010390300c0c1c1c5050380090810350429224001c06041104c100201c3c0c00703944140500300a0305a0000301c80d16400005802403103400c03003581400342803004100070302c8007583d54103100d10109003d850141103400001c03000c070f20880c040ca000c55000050715440609405d0040d5501c03841c0f0b800c181600c940c4a071240ca290010740d82c052840d6078000410048070703541c54081d60000b070002403c1103083c0b14180c0c0d0013a4417580140107404c1003141011052030b040d983e100d100c03d884407000d0501a0380e416a420300e9400b80c09072888050181c0319400000441c2e05003150407048504024029050401d0b00e42d56034400796106680201d15561400301405a19800c080307014000c6103c0e400402d0000305090005081d548107501040201d4400a110401501d610049036404091011400d5403100d1003910100280b0300c40c0c110581621480ca0520881500000464141d480310340131241 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 571373021 1250 571371771 571371817
    0x9050a1209210602071703010f030c0f080d0f020106050d0f0212070807060f021c26060a050f041104062703030f0e22090b06030a030c020d050a0c0902 66
    0x1148034040003040d2420b030028409002c102c01c4e50250540078071540228021031a01c0d0170656142d0800e8115000000f00c50404000700000051441c00400007440040500e07172070451f20b9034a880101c6460400d00c0800700c041c800c800d100794040401340400034141c140300c450a003401482003041e564124090901104404a1420001582c8003204c9141e002000102e08100084440403858a0b1407800d521400039800d44005450969546407540c075038444078005126070b0f4066a418081088410502214040c02669241c2241c0001580c1c400e0300c5060f1001840d0020400070b081c088035104400401003008568030b9407044010403082d0b10804c3c9100b8240c2c141031481304030002884000c010034a411035885001d4050b1810503038080307005218003240341444015000141400000300005035a800c0524204034180c00d2103500510140d00400881905980c0035103114801e16029120300404212101013020800c1104d04060307009403004d86965460107810b010b0b410121010741418100c054002c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 571374271 1250 571373021 571373039
    0x12010c031808160804080105010e0601030c03090308061203070512071505070903060b06070b011e140907030e12070804030308060105210903070b04111203030c1c09050a1209 76
    0x808215080b580051400310842c02c800d410303400c00d04085482c600d0501000500341402c0c81003600802241107040e150b0b1800e00300040c1110400b00300e10f400e15161005160129038840d8400b85d0001041d41c04111014814400394030350f01070800000d0042c458881d08444024542c0060000c4038424880c030042e25104161001c15584d04507038680000d06210401c101054098004021410001d03012500d041c0721a01d4840c40c0e20400d03000030021541036003000345a1400260100014507130781c402d00c645008042c002620001004d840041007545031160400e0500c001c0c03060040c04d500001d103155a0340c000f450040c02c41c0d0003c0c881580403803140c5000a50550040045841400d05204041c40300a81010385442544000e4544507940c4000c3c01088006814149a05c1c004e81c0900d0030780d140c0c1f10071074042024200c807130f42c0700c030496030403c0c0b09000300100701600b0344084140c180b8031107018600b85000c250080c0003141d0054102e1040408640921051341e1422440c0500c640d180d240e0b0342c0e00d82000c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 571375521 1250 571374271 571374311
    0xb130519120c050c040908040306021602120c06090609040e0d02060108060f16030c03020f040e010e150d110f10120516020309120705040608060703050109110301050d020d0212010c03 80
    0x80c0050308100c0c858401391816900c1604007521500c0c8460800e900e139181d090403038111080d500807070030340100c5101c154900401c80221500d55540101894000400850954000e603c00319000d00381c0070600310300c50b07903d0740c201d6004150300c401110b0120280c914025507920081c0b181141501910010600c0b14001d901520f1041d5550225601c2110b080344007207000f00140e28244040550910507084020411401072004103c256030360070103941050b2980c0601d060103031010780052180314000005440360b110035a20075400c05c464030186002000801d404400b00e07800b45610500c44c0802d0396902d90401d04481d141d107864001007042d960f407003462010b45090003000d0340242c1e000340880740309403a0014060003a001c120b81034030455039540340818240c840d503400001c1c59402c02010040225498840c1c3e9004020000040c0084c0c3c00d40010f2101e00d1006024036405140801409030940d00e806180440d4103a0241c20202c0e15080c81d4283c40c006e0a08201c035000080c00c0c000c51b859068504200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 571376771 1250 571375521 571375523
    0xc040618210615081b0d11090406020706050c030f0f0423070f030c0303080705031b0c0a050a03051b030405100e0a030507090b210a0b130519120c 64
    0x42001d04003095004466a0020101c003115400d440d106101c80c0c00210f407000c0703c003d100700001041000c1140001d540690700701140070340155045804000468007008040503003000036101d4000a03161410100047d1192840c042d1800c1d04000038440c0c1d4160b03020040d449242e01518141c10740d01c031103c0c4042d1a06043c1c501500c40290841c02401800004024007002400c2c00100e42403207036194103403c24000b0a5105036443c0c000000100249500000305607440030040c41d21514600d850f00300022004188042c0100c0200302281102450b18101b0417245035540010807500c1c1d9904503d03000f00795038005103010800b2040151440c1d91000c001065030700b640e070700419108140540079021241842600c03551030703018132400c90000c0030600038050380c03000d01104400450a11541e00602c182c034400e4001e4034008c4031040103004a1030302d012a05d80d103026031045a90190391924034400302e000c168900b01620b1400b90008002481004003620b00183c0c0c4204001d0a43c0080500b05590620000300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 571378021 1250 571376771 571376789
    0x702120a200414010e070f0519050a03090209100f1202030c09060301140108010c08070e0609040b040b1507140a03050d0c09030b1807090e07031502040803030c040618 73
    0x161140748046028200d61500024100045118104651109400080c1d001c41c440707001c49000c0c03254a56200041c91074010580c02c100f0b00c0c1907030605191a60111507051107040007000304509010900c242c0088900c40c0c0c0042400d100f504102705c0d03598000d0214810015a80104c450000e041c01c4150411080307541c00070301a1000c1d090401c188900501c00034400d076810356a03680d400a0840d0000c00321806801003000014481c8200080a0f00002c0003030052424056035418003015543d5040c11144240700070b442c04100b001c804030204010f0070850408644c0058188168115616944c01400842d4061250300c1d0304556080d030f00c01d84070340001d50080e00027038080122024002680c2c10900101419103000018595241c45800f280e180c2500c0c1201c102d1203602c2881030490f020400c60b0003401800700b080010b540c4c110640381e6a0401880014084026089010ba0311000d60b41a84c0040141e441034076580d00c0c000800300075580c0036010b0003000c580040c048159030b2041035503500c1030b125046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 571379271 1250 571378021 571378043
    0x6020f07090e0705040c0f0f03090f032714091501050708030c0408030307030506010e030606010915090504020f071a10061d030a0605090f1501060c0f06020705030702120a 75
    0x2884640150280505000b19032140c041c002903140c846201d00070210040741c1d126005001c502c00002c0903560086115010541001c04450204680d50222000c040e89424818259010b000101c501d501c2a2840421f44412a03000012807000083c8072a01c1c1800840e8500c0340c9a589480c42702140d220b1210080c00124240140c00c0000c00e9400155040092012018101a950031030a46103074802c80b42500002d4407802484055600440e001c808070703908502921a80c0350040000b00b00e000303d882980c0c0101010152410114011100040a400301400035540d481170b05142c400a41c1c8940411942c1031608107080e0701c060850603d0b103005507418010000e0843ca058012600b4018810900d80c90541c4150203e08940d4104110840b06e4443d181c0400c4902d0b05058081c1841c14031041d19000380c2001038070b4101d414a1100381415a01d003428404200c07402800c010000c20b29484009040728800613103002448800000340140c11301c01c0747c156400d80c07984a210380d21446c0a20000304001c07014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 571380521 1250 571379271 571379279
    0x100602030f041505160f0b010806070c12171003030e0603100e0c09190e01061d04090c0b030a020c070b0c0606040f0e16140d020d080904020d1407030606020f07 70
    0x402d40c8a4103951301d0320908014014400e05650340340d40304215508008812014108074180804900402005010302031501e0254230141107848400d60051410420301e941c040c00c140660442140788200400e1036465192500d001c0c050f44c00c41e404164003040c0c450400e941c45140c46021070f8462008071280184040c9007051108400c800a44000c10810050003120000d440c0c0a8081c03079000e0800441c51942498814102454001a04107004001c9e41c07640c82803207000c80c4034000c500c658040e54005410101c5050464001d08190010742d45c444000052000310103450700a4010100c0d15001e580380150b0310304094146218807519009690803c20005540e45480d510910808400180114031480d001c03820030700b0300450b9090704210200c81001440719240400110a02d0401918130702c00d4a00705800086030812074540041c00c01000007102c0c3c0300c07511640c040e2a075124041070180032140d00b02c0b02281100004071031043c0081c1c0f8016000801c40d2000401a8550310100040c012580c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 571381771 1250 571380521 571380539
    0x5030c01060e0435070807170405012118032006010521010b061c0b040b0d0f0f02030304030b01051207031509081b0d110604021c050a0605040b100602030f04 69
    0x7000032400c4131300030f03c405089500b0302d00100344040c850100c865648145103445890388600303541e0740c2100403040c8018412030b60495400203034101503410850441c840b00003503001910a00141805105c000e048500802da0403217441612000c9100c034081c810b10400440b5980d42009100d066802500f0701d842a0f040b1203030081182400007504008602da4005070003203001540040002d00a0b000840442044c030000ca01c1624207441e82201c3c14800340c810000092882184420058100080618640200503204c524000e2107940902680c0d182d0b56031341000c0700b814a0911940c0d000b0301d094036000303921800c08030380703242665441500500c0c0a520744031080c00400103020304403481a01000300e400324984264124196100d00801041008030140c0c1c024000003100100881c60f030300010a010069490408040381000c240d101c42d00708034858240a4580b104005010300024641400d2106000402040b07901c1000a8421034500030780d02c0c11304a03641e104450900f030140005020078055004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 571383021 1250 571381771 571381823
    0xf070e0f030c19060207080102041508100314010902040506040207020109060e0312042619031b0f0b061905030a110103090b09031c290a1205030c01060e04 68
    0x1001604551030030303042e0008900c07101e8100c00700740320340602c001c4204000c0e9130401040d009400000f00035418180f8004c4407407044c807010320140050007400350008a00c1080c008c112801160807030390b004d0300a001884920300a0a01d41c0e81070f0b00842c10700c40001e46c02d08003802102c6006a06940b90f140a0b85045c80450340304918280701a0706000d840107400b071008003140900084c096418000311911000c0810000c5021515107406045d0003c0c0b031441d4038020304512240b0501d805042c0741c480100f0018410f1750741050408014190309010941d08140710313003110300b544a0a0103458030418a43c501c051030600448038820036500d03610140f00f4000080010024074207080f0306060204140110ba66105101081114207820640c00400c9250402c2112812252a011181000c1090031004120072240062031441214911100ac88203400380d1501c0300154018050040c0c03903101c3d03001502d09141c40e07a01a81007a1040d40c00c0560205013800c00380007aa002c0e0340d01c03001075034201004000c0104189 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 571384271 1250 571383021 571383049
    0x1401050f09062d091f091e1107030807090f0303120912110c01050316260a020a030f0506010203040303080a0e0a08040501260c090d08071a0f070e 64
    0x540385440d41d16522040703807404a850b082d1850781c401443c02010600980402c018180c02241c1ca40414110403001c5405480e010b80c2c102e40c0001c10501d00707004060300010352a50742690391600c5c0c03882142d900a00400540b4000d4841c2e69040b41503250613a084541d21840d00420400d1100040c0030000a8050022651030419068022954501c1a1900704c541070803210a600030400c140034074030b4042020302040d2000b0609003045400c41c02c05010018100c920340c3e04100504c011402ca00076501c0110884078004a0031074120b550b00d1030480e41000c0039401810204010900f00301046071409114001d20b840f07100306a00443c2011301d1601d084074002800f40100c40340540d90441455050401e02940242c58003900c5c055035100e1600c0c0c0014031101100c00c0010080c40406002e907005540030000f03d4101c0199000c4540390f0011900103059003100e004005e080758800110380c03042212201001c08010742c900c0014020341d8682c00040c1c50703070320103d420701c00040c922a501d1200746010540e5007005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 571385521 1250 571384271 571384279
    0x30510110a0509040603080c0309100809030307082502010b1c0f0609080403080415110a0b06210714030c010903030806010309170c011b0c0b060d05010b130f1401050f0906 75
    0x15035a03a20b94000c1540710034102341c145d41001942860314105402c9200440e003e07481c1c00501450301204844e00da0002522031030400c030560010800791501c0c003104041507031800307600605064403088040c0c000c1441401180c01040710b440d0f04944020030381403003148039400020510240415503261001400500d0085401080511020002c10940d5000d04040d10405c000d400c80c200100001404081d00a041d40c60598001290080041c181742c166581065064841e04d071100e0446062118903200100a400c2d217205d4034000040f50b1410a01ca0f0340c49840941c152020303078921400440d01c1411038000079001c01d10600108040e035100fa44401165130090f0f41c0d4018000b504d0222403070a60049e1030546444e911008580910b0641c80e1000340300d6074890401041c0300c040c40d50391120948009008030701c2850456580000c2c04000c1d085400380b00401040440205100c2c1d82c0c900003000d050381403916851416103508e100c5200c0045c07881c142c80c00100620702e403c251108101000c08000c09240d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 571386771 1250 571385521 571385531
    0x10c0f2303040605030403090b2a01020f0d15050303070c062109030c021207050f060315041b030c0e0a090b03070305060703090b0f0411090703090c0f030510110a050904 74
    0x120000c1840500068240c2d80d5840c0c0c2e481c1003904000748080000e40007540200c200308a4144800c0c070040c50083d0345850b580291842c0c558600301140240645503010203005400107882c0c0b807007080e903405201c03060003402030801100c0d103503800c1c50303a68058100010540c6c840e851301481280d01504828406c0c20035140780c02400b1300e000c1e00101c1901c68500d4103e011500d4240f6010451030140c2c0040c42101000004020040c613100c002620501d81c0c100140c041d407000804201041407a110f04400c0401c081c00520940c8007180002d0203c501c0040c0e403e00003840c16101d420424800d8145143c01c40001380042107071800c05501d03400800f40112501e0780361081d00c20000000e0014020244141e40540b000200450542060710300c011009265008501c0c0f030780d041000042c10504407440c80341050303d688106981e40388092340141b234020381c050f280b6400b070540060840d0b01c1d07200e4082602d104034295008813400c3c060340c2c400d4901d2003000340f545600c10300000307110306e1284005c0c0c40103010061012070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 571388021 1250 571386771 571386833
    0x3062103120106020607023702030d0e100e030a110120160501090f090e0708070320030105040c030206030712020708090102151005060307030b090a0902010e010c0f 72
    0x4516800304112607403124100c0c1c01009001e4040c00f243c5d0348480d650002e0300340040030301c00c4202070b205040504240406148000b4407002d0305120b100411503809002c83d01070008070500505240c0c0340343c103680e202e4880700017403101061045a020100140160050090001c16a40c0c0ea41900401c8411810850f21100b0300082d1104203030240d51450b030310700160800301804429169003041580110707040c0202c10101700310540d03910038000c013181e0841c40009100c1041c60310040c1070107015400700102d8070501d640401445102c00494024580207992403205591403402e00d42030302ca00b228050f040c8070074000c0070000760800500955206103d407414403030710030458000c501260801002950b10003c08a064031441d40c04000c404161818074850101078504988103814542c6c45002d2140a6907001c00070400c401d001c0c3e08617018000008100300c5032840c02c00c1e9200010703c4142c0c000da00160000303c0e01032142d4021f01c0d041c0c03072068000e45214409506138583e0f0342000240301d0542008400c69610308 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 571389271 1250 571388021 571388023
    0x3070521180112022107170133050423030604030807120c0e040f0b090424050f1501033b060c03010306050115050d0b0d140a02090901090305030621 65
    0x3010483c1c001030118400d184425960340d0321700030554401e2151881b00b00d41140c1c282c0d805641110605d94881c200c103042c49400c4c03200c0c011801050142200c4014001901b25000300162081d500c0c208001442810382c41c141c081c82e030001d03011098040d00110040740200e0300c1000595440500c42c24185000b079030b1003000000316803005009000040f5203180d42c4846140500500c00001091f907000d1003640c484900103041010041c0004000d060f1200d15060980551030f245030a40510031400c0280345800394043c844403008442070a101380f02d0303207400010380d1700070f10407103014401d0084203a10718081803d448650003000c203407010640784003000345c40d241d440405c885880784681c16074641d00c0f5450352402d6000e441060304041420004105500c014607849002e0304d030800d00001c0081303665401540424030141e01000082c00e0b554810042d00c0c0003010000300e0882e2240b00351084020340ea1a8880c0038201d600c1c0c000014000b84081020840e07a1a2011034100c40006600c0580030070180c0407069 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 571390521 1250 571389271 571389277
    0xd060b030702010e060609040b01330917060c03060111011e0207020109301109270106030b040809220b0f0105090a1a07050a050307052118011202 64
    0x28005039190642807404140505c00c0580001c0255040140d030b0034a0707540c96105404c140519100c4540300a10148002c0044010062601c51018034448403029410300904003030141c0599625440f01080541b940f110000d50b480c03240d100b011525046494140046507003201c0b5041190320341d9246c02210300e51a4001514081400d410040165140514400984001c2e41688a01900c00c13500000c034042400300307030340c0700881030092150620f16215860084079540340c001016401c100c1440400454074048042d01c5002e1300c100314041520644010010709a8845000080070000b00c42c0c0440c0005890802801d5501d10051403050344080000c0c940d0006d00500d1103001007140c40d024200c80c14101421100000314080c030b00145000005400700c0c00b03004042c8128092270001e135040e0072200d6a070100361070b4030039071141c01c2da19842d44a090503a0b0342e41110905403418007454a400c038000105100e00c0d000b202c18203010508020000500084600342d259039103061024495001018a00500c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 571391771 1250 571390521 571390531
    0xc11060a022d031206120d0210020a110613051002042402211213083a020c1209100e0301060e010e09010c02011e0b0f2d040207080d020d060b03 63
    0x203c10710340c600174040040b2000100212107060f008842048140f0b40d001c074008401c4141d0000c05a501c241100b400c807030184241106001c075025080602c1a00c1c49900702c220303405030045045528820905266104920075489031040d0451048600342d0a4021070450340724090303240c019250440503110110036000101c05460003a05e40c0080c04218889000c411603400207103055000317240100e117a40b500013900c82d50415003d03548100340d440e881d01342440c83d00609140c0c4529202d42900f1149009030103908500c0501340c0d94000d00d1251081c810b014400d813400c20400405250f1401c40442c1c0a54001e95210580340d010f5489040c0811000c0348204e40c54000c5c20051910895031a112002d02d0856402c0d070303a0a811079050241000044a020700c00e0490034080c10b40010300c4008003000101c008011110440c0c010001001030508402d0b0582c0030114410a1012030114200450821040307100e0240028005e86060156008a8419038050078000000580c0094055111aa04400750b0003c4803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 571393021 1250 571391771 571391797
    0x308160f230c0f061006180504150b0d0e101a011d0d03170f0f061908060a0b09090f0a0b13021809100b0a0611030706020a0c11060a022d03 61
    0x505c00300419849901c00200200c0c9410b04903c800c0c1200c03443d1000d0b0500c2100c0c030482d2218424070320500b00f4195100104080941039545950000074000508401509010386004101e58000700c69180e0142070480902506045587c0340900015a00c1510101c605070141c0c1041003140942e0302e41070002000280079840342d426040d9080040116900d0040c640341445a100041c0015024240c20349500300a0449010702000b5004100d203590314000d5125032401d100728000c0c803c0c0141103501c8001e203218142c07851001503075001c40d403581d80c1c2d811005422041c3e0002e05184081840203001d203405c480d002c5004134030b0a10075000140300c034130060346600f100c8070114107100c12020304024111040e8007800c0305124082c0000c0020300381c44039601c00d40c41030007903c00341405059818422101c03490f40c851021500c500034410000c10705010071108a48070491100210064030b400415500c91034a41e03802841c40068100071003182001002d10601c6086040342c0c0d8880000c803d001901088000304 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 571394271 1250 571393021 571393033
    0x415050d091b1502070b0a181d010501090e07050315030a030809010f060501140304030201021314010f0311030a1a0d0510150f061d06070308160f230c0f 67
    0x11030b50203001a00354000903141c440014410295070300404c0c2d44048440321004140c842644140075104200780c0c2c001c0c400300c000803000c0072550110005500c00584c00c1d66003020003680e2a2001958140342c2402803000360800c840001e468240708200440e0300c10000c95a241141c2240c20100c1e00e85009104120041a061000c00001060074403a401d921202c00d030061101ca0700c0c000001e003a110070509192a05440000020185030003501114070440b200004820f0460b510003003040d20076203036800c203800680403203c1206018402e004000c4907068964060f8599161010f00000074180903800180301d00c1c1d40400c240c0980d0710070364801c030000d006034041c02040c80300c5041e035421505011009031743c0d0101c800d41402403000900c4e8003030590301c5a090000920147d251400034000660302c4240d4040310014144082603405681036005000e01c8c1d080c4220034107028401d440216420b00101c00113045051241d2400c0c40d080e045d0046401140c004904d40b203503001a0f5401d1a1014290103904da1002e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 571395521 1250 571394271 571394303
    0xc03040b0d180b07031b0f03020d0e03030c1e040302010503010b070204060911040f0e040302150a111603120501080d051c0501090b1809100e0c0d110111030c030415050d09 75
    0x10b00541005451b0304190800e18842402c025000300045070844007090750104c0c401c0741c840e602d640009042d1070341d0b030112911783c5450a606c1021b13620603011015114003528000440c0741c000710585050741c0d816107601e82581e082244401e0350b504070320402d030390064079004c0018800d9503504c00d4a1069802510880d5580c1c01d000d0021070051080c2d01c0300c000b1203403031010440800c2d40802d0070f9502e411006110035880d10f031100c100d0040c0c121041c920401d80300000320f800603e4500340c8115115071090716107841c140420500f210480307109105000564009000b01c1c5621403060b401012016907100c2d1400c0001000010901101d6090300841307105035880145841524040750888258014000c030210f6514020316101c6d05d56080c880c5030b190b03054658100310700680003400220074520000c1c0030003a804000f03040282c2c108814a205502080c4a0175030032064500200031245010010001117251629151080b81c134005075030000d408021086c0711544105001c0e0051030740041c0202c4091500c2120 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 571396771 1250 571395521 571395527
    0x2180406090b10091a0a140d0204030b01231002010216050102030a060e070e04051b0319050a0209031504060b030f0a061a0915120f010207060b060c03040b0d180b07 72
    0x40d4407010018402c1c40c003010040134089007405d19500c1da1361400c2644650a402c000c1d5444921022210402407000c503000c500307504242e01030030440740a004000c05907643e40c00903040120920010b0b90b031441c10000400460700301000c04c03082e006101c2c400189401000b50820320101c20359802115180d400000f88151142e80703019040207413444548440c11407c04240c0030708250380410140b400741e601c03400007a205407001e0302d500103800d0205842694900d0400d001d45a0a12840c00c039540040c41e00e00852034403007203407003540c0510351701500515404008403440044441d004100301c82041d01c0f0000b411464400b032050305040c00312000140306100d514030b00402501c100c500e200402c2149144500c016940d816078441d00074844007000f0100410400120714854007071661560144510b609135141d0000550043c10b072030f40203100411a981802080200c0c6110b500245405a4400e0100b8401030943c4001011442104800043c615071001480e24a03048160001d0720400200e404101d107840d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 571398021 1250 571396771 571396789
    0x513060e0901020f0d230a020702011805010f0503100f06020d0f0e0d061a0910050f091e070c0c0909350f04050a081f0608030d02180406090b 62
    0x160100a5080013030241006450f80140c0d0141d45400e030301d038440f404400095042c2c25405420500290065281c220044d0000e036000c200c04a0001d580c1680b043d1002c0f02480022090f503205a60303111000f910300004441681003c2c02d010110550008001401e41094090a00821058024150119135408058406880d11aa003428070181a0074050603603912a0309488040d4840c20001d10b0881248070340300101408400310380c014904c1c000b4800800700070701e104411220308842c108007502c084400d100310600d0030b4883c0148810240e9114000b01384005603a60321500170b26101e000040c0a44030820b00880d1684000c0c1200d580c0c50440080c0408180e038510b00c1641400c2c14040981c600c00d07140711904507901c00380042c5030f000c81e40107283c0c07019008880c01054000d054000300c0b0784400b241034032000603581c0c1d6080076013140d43d01d28101c0d03043c0c000c0d00c0845074010040c41c1842e40d9505014061362052451404035138039010704e8000e99460f840380c0c1c0081e00354460002200802e800a00002030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 571399271 1250 571398021 571398031
    0x213082b02070305030d09030e120715020f0c121009060203060109060c03021b0d14151303020c010c210806010e040e2104080706050909010e060102030a03150513060e 73
    0x500b0460052012502c00400c4800c508413441001419071170f10f0400319101401c041c0100d038080702c2d406115048190005010701500c0042c1a035001c01c0081e110144ea96492031041050789801c6a1004030750341c41d005012801202055080d180b41100705504401254190b201c1110495408810b0000650b842080d1401170310050070501101c103105c3d10069620130080c00d9a10103a407600106140c1910740111800350b541c2d00c464200e43c40d40007000501d4603034602d000070078100a440000940e032840c1c0e02241100054064000d01740881c480070044460300c08081c42030b10034405d207602e84952882145c042e40f0550145030758a10003810a00001042801403019282c89141071114800451001041c080212810804489029040035900510742d026a52040070103002d00b040014060380c00030001e005280b0100c0751074116030788400441502d680d0075107035980107a1003880324442a40c000e5002c0039040414801c0180381e65a250009000c51711408580024aa1900810840c80702044915500a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 571400521 1250 571399271 571399273
    0x50c03070203032a0a050304060c05091005031f0303020105070f080108030405061806041d0c0301030c09050414060702030d1506020d1809020d02120601030608100213082b02 76
    0x14200440020741e07a00000c4c054469400000a00b000740c0c2503180f04510700a058243c98544903041c4902c043c0c2030b40c00c200e800740c82150038641090311052290781110403810300105070030140310748844120f4040d00300800408003900402d00740f0781807030903203130791040107500c80d03400880e5a141200c0b001b800608080e00a400b400080f070018000500c1c0401940e003038031070540c1d0740f5441d042c1541d4820000d2600c1e140716500440001408185031440c0744044800e810111583c0300c45498014407030460788024400503060706041101446258400e4000540080c0545010418404408403050410b803058444a000d40d10000b080c06021b030f558001c1d143c1030400e40d200c2c402c0180c9401c001035116075064640707008100701d00b00201c0448104981910180810401c00c41d00c420040000704020b5100120b1140d00400940020720f281d84640140d100782c2d50181c010701961000900854040d42000224518802401d0000b041c00c4508010801094050851007004103521003c40c8481c8003008210b0011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 571401771 1250 571400521 571400527
    0x6030f061a060a0309020609100216080c062a0d0e03010c020703110111030d02030f0103030e0321160803040b04020423040f03120c020d1121130522050c 67
    0x459502c1d0001d407807250145007004141583d55200282841c401c4680160b40180080400340400d6030024007404c0d00d06440c044072041da80c6690308640d81d06100310609030b0007141041199000f08010031303a6856510210f00c0740b81000c15001e01d1034200485540e2407030008004552492440c07609000300d0042c86507a0000d07141103411a11a9403c00002900e654148100c40c3c5520a030700008004495005107210b03400c540780d0619503a6014130b4002880305030000b490589070740b51280340204140082480d2204c00c52420090590001071640013144c201e9a400010024400070860ba000158402c0d842401c800c4c0c401c0c034251041204903015008460f150324088409680240c2d00840b003a40c01a030080c000b24014003040c03500310f410a500c84816035119040503204501e20b500000d017800d840000da10790700c40301c60002890b141d80307040030b01d02030460140341c0c42511500d5040138010817090124108005109449801082d50a20030800c050359461130f020401000d03050601c2419007004940a109103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 571402877 1106 571401771 571401821
    0x215190c021302030c0d05041502071b1205120c0712051c020f030a180302030105010b040e0108061608181f060b13061202070606030f06 60
    0x401100896414600440742d402684c1c850036102082d941880800130318a00500405003003035a0205501609440340105400103210545c040c0070031200c501e03079403d0720107000d004a41c0080600060790010200141c4003107200441440c0d40b5210680303504075809034504225495000054a50460100300e08100b0b012aa001d05041020f1030000407131044c01044c0c0e15640440403501464000f0841885000d0181e03100448005204444080307250f169800b0900b190000c1c0c0041c2c0304007502150402c00142c10503006405044504007504107410310b648200b42401c0c040813501c080c0a0000f001980015040680021160800040751054080840521480d4140920741082c0034146000030070300d021a2403c41e640c1c1002c12014280070307407034842d0849002032101c1410032440d408101c0300d00410818006c0d04003440c0252244060008130b890104102c0c1e0012014860500036a040c0318 = true := by decide +kernel

theorem cover : BRFrame.Cov 571223021 571402877 := by
  have h0 := BRFrame.cov_init 571223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 571223021 ≤ n) (h2 : n < 571402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
