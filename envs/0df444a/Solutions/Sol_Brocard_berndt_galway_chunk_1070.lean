-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1070
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:06:18.315273+00:00
-- url     : https://prove2.me/submissions/bc33c6a9-1ed8-406e-ba41-61840af2b38d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 192266187 ≤ n < 192446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 192267437 1250 192266187 192266213
    0x6061b0b270a0323090112090c150309030201230708190f0e010629090a0b041203021e12180301090804030620091c021e0102190302060103140703 64
    0x2001c210241e10a400804d05111004a040b208081d114144414580000c000301d40c444628200d055443e2036410a02030303841e0805000f0041c415008666050100c001406441410021009503082012580d0005d00d004c11900880908501080c034035554881d00310383d0690050811001d01c80d041c1008560b500a9009085a00348944000328408074104203507401c407483c50b445100410382e10344c8100203d144284000e03001c400000525902c2e469260000703104043c0503400f101e04001c0000340040d00802078258146510b0081e000d5603118005900300c0c1800c0007120120051907002180134000b00100700014220980407801510440c070103500120b401c407154050151810140420300b001048071901a00e1503401240340701a8010300068000e040da0300410b841030388502d99068003c20300c518007075001d46003140c000380a500d100c02e40e07641c021007000360804100d00500400301032005400c2c01c003044285840d8140e0080c00d442c1c0c030b10b485401c3e40c0c0e9442035510786140203001000010401000c04d00c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 192268687 1250 192267437 192267443
    0x40302150a17100f2c070e0303040906061701060503010501030e030702032b0908100c022406030f011802100c080408010606080f090a08030c071506061b0b270a 70
    0x142c64a091003c4050541e401e58800009074480100d203540e4400010041e0741d0080c0121701800b02525031000c191074040c80d259229406100206001807411642c2c0c0017801101c04c1d60302e40c01c60842c0100c01c1030038600703000d00501e00443c004000412165103c2d5015240b05c408560989040121560000382083d0403103001011040c4c5c038420f1703a41c0040e81141003580698441c2010011149404035058440814195801d59a1348e00c2c100fa456075402440307031880301081024030205140201d03055110750307101911464000c0c230a506202045c010144940401c0c6404465600507480075a420000a980549a00350420400c0901c80300000d1240001e00081c040c0c0400109940782000340090000000402d08660009010b043c06400031000c00c1c20811103421401b41e40d0780f0365076402c804003507101d0410000c00c8042c0c0a41e582203014030540c0181d0035503d040da140e40c10300c51440d90881a444640301e0181603449003002080f002c0c002101912002c0b00c24004460095100703521300342c00c0c200889002e0f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 192269937 1250 192268687 192268711
    0xd020d14060102240705030a06030813060f0908070509060301020c030301030b04021c1a0a0617010605030d05040302091501031107030e041b0504030b0c070210020f0111040302150a17 80
    0x400007940e0140003611000c1c2c419094084603c180d40040c02c0040c42c013a040005000c0c00001041e012805600b02c480503581004a45584184180d80180c82021500c41d00d80001c001c0030003000050300c01d03120300c0100c1c1c00d1200203025142c205000c00c219004080e00a9070700d90341c00c0140055085060003d54000e41c042c064075241031500380184022200c400007001e80c0320842403041030006601010500030b003140d03050505001d80d02e420080000b040e898002c04060f2012a02c5401014815040352050707075400d9058443d003007070101003035480b4001c502000b94072510490000740702e00c0c040d41428203030303550524001c208551008502c0c641036100d24015000078200440f24440f03030501c0d0082d0000845240c81850051409140060071800303640401001d294103840880c0b2030a20810035245181d8006010703101d1030a241401940c0c4000c0c48200301c40a50811142050306c0b07a484081d601107a8000e000c5190000e0580c50380301950380314056103024003c01c0c80e0b203c3e20340101090110311540c40d00d410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 192271187 1250 192269937 192269941
    0x1003021008011d0f01090203090f1207060e07080a020d03180f0e060108040b0601200f01020309060f010605040b030903161211010e0c010309151401150e01140d020d14 73
    0x2007000140a0100500680707240c003c240001c40a4100c5040c0c1103840070080183c4070b0301e800301c440d4284520504524658800c0a40d07807803140e240c10300200307a094450034003001940210b5012585508080c4620f1406803c281d12a602500704540000320313461082c90488001a10244100070300d070116000100c540103090401d021444011000075040315090a1010003850250360360140904010017103410070042c440e56080154102d50304c582d11343c2111082d1162003c031070f000503000390011101c1d01070a02c50240821190b4502d010498180c5e00c0c0d42e070342d031071626080c0001900f0a41c40504503006a100400c200308080320025042c03a8560b102311a183c1c0504072b4510000d000c943c40021000d0243d14212501120200c005041c0e0712941082c00c012809110f00c0c2811804801a500070304440d50801c40b6600c8080201a1680c1c1a00c084046010b105010140210361840c80c903544180810107401c225200d842e03181c0d010f050101032160015140c0181c001003942034aa4506080c503440d031000003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 192272437 1250 192271187 192271199
    0x210605100e0901050112090c120c060f020c0108040809130f0c050f0d0b040207020603071107060e030a110a150309051009020a1202030102090d1a0606040b0d0203100302100801 77
    0xa036500414603030345401d01140900000040d00c0490600c18581802a806c030500584802a04003002ea1500031120344030342d40da105400402d11904020407219188604d502240e4580581032082020b80c590f4000c4c80407024280040d12140e20113001618840c105210303920317071076841c444000c2d8a6100d440001c10800c1c0251241c400303840d0703101e540394280301e8240801c2c0c10161100007950206084520003041119250020800910030810f0182d04034400208005009400602c0f01082050001c00c4900231076965000721402461036180580c190406d90904010a40c001e09054550304014442140030380c1c0c034100320f09040b461541c02030209450f072045030148001400284150b0b24000c030309010884c140d42c00149900750902410000c0d00d504219071055440c2581581e503005405001001e0310a00c0c0d00308100c0a141d604010310080d00c07038400007020350820101343e50444041450450420004820550107500010004440401440000030250341d5554001500d0561910740d01d0455043c04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 192273687 1250 192272437 192272449
    0xf151812031b0c060f090305070c0506040608040b090f10060f12030e060304050c040f0209041b091208190306050108010b090f060d15030809100e03070302060703210605 74
    0x100c641030605291201c2080010480c0442c848080341030710b0002101202440c0c00c100502201001c600b000b031404256400305900030f00140800c40c01007080c00545550b0f0402c00c101e0340b00f24010b0300001364222010900080e90b03e00142d42103405202a070742e800030400390b900e1a2600f400c0b00300d0051600c0741d40c204203200d500510a0040c0508403000c0c145c10b102c503140609501c15400f82c41d4060322001000405001e41408242030301d1a0052003841003030400d031407000107500a0740089205520706030300c41c1300b08101300e400010f4402513034985040b0a850b21f070700309802105050342540c108004105000f1030442a58024000c103101380c4001460a00300000108900e00582080082040412040c1c10a94840d034441c0005181101c88551b180540c40b411000362440002144540c10b1300c20f03000c401c20000c0c4018143e80700f01a107003040080c0c0165412104541055107040d00354025a00c14070142c1400700003003405900908000c5220410001000e44022004a446885640d15241840540b82030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 192274937 1250 192273687 192273713
    0xf0d0201020a1d09070c210c03030f02160b06040f051915061409011b03080103202101150e010821120a060b04081f050c070f1518 57
    0x8084000c218003d660201c0c1018201400701c0b018403003498208000c00030214058065400096000c1c0091020417101a00b038183c20078040700420308000400441030002d2099521500c28088044100b00154840c649040006066550055110480e0341e000b411903000300707800b50350410041c00c424440f072284181103990002c054549040307a41020841e06610040030301c80c00050b00c0030141c0c1d81d0075000040e64100c4031a4020742d94102c8100421050540110b0902c0c1202e00800411640324410320341d1620300c00c0c058a180d0760003a00400707903203821030703c03075108001031030f48200009180502e22508096408440d44440c1d619654000144500c2506212080e01c80c003159400613081c80b80360781d24191500070548084407040d06100010705450894000400038000b509115640303e40b580c4009460b180702c92000c1c3c00560f4951480368809810784922031142400b030b0400b40c01d104c000d0b40e50041007120024140d400e050000d07011a19007040348180040e810b031403045085034008515028001802c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 192276187 1250 192274937 192274967
    0x605041103150102030c060f28050703060605041503021606050c0403031403040f06090c050a091d03040e060d1a0f07080a05010e1b1207020109170f040603020c0f0d0201020a 76
    0xc01c6c0304540110304009045e980040740b4034000c00702599007010106110010200701021240e00240084050090745c0c003040c0201107d40c0c2c240042034803004c0c265503600c503521401540e000c1c40780480910520950181c030020300d401c0d03682c40800324282c8540c4256081039641d44440c0d03000103400c0041581051510243e103890181060840c80c0c0b58851224160030403602600c800d403144004020030544d907213281d000e01002840b040803980c03900c60010040040c00c110302245020f1840d1003004a100100345c03021107881c1096070034203541d000207115038161041d4040300c1c80388044d034550000079030110030180700750702c00380c03010f400392401070001050403034080c007072090003440d00d0010303c06c0f0701c1142e0300076900250031000e0103801100f03a0440c0051744210743c071100b200c0402406200710030f6410340054080f01c2c09078a0790701c862a40400d030820b49124059407074039055020002049458040e8000c0c0c51506034000698107688403d2500c0c81c00c100031113403401c0040c1d5001400c00c1e4116000105c4440140c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 192277437 1250 192276187 192276193
    0x91a19030308040807030e030f1c090305060403051e1c05060402090d03030506011107080106170d0e01030903050d0c0c02090a15030602091c050c0307171b0102010605041103150102 79
    0x12450700c01501e4041c01800203059864005800d0007818000c40700c0c0c401e520340c0982218003000b0882006034036252001d4a142081454804104e40d007482000d11034141c0350000064130840c0c6607075400356615400b1144410711203902c94100c5d005101c044010b484101c03024440c2d84d510303c0b1040e50400840d00010815880303030340b040c802412a41c0b219400c049040c1e61500b800540c41e1601c030010b07604006c801c2d0b0401614032454401003007040040d009501103800403840074041040e882000ba0710b80c40c0e01900707100011101c0780e20107031541c0300b0f81080c07048074081c2c14075601d4410501000001d0390f1200341c840002c10184552601182044011140c0c8030350282c04c108072150101c003160000800c0c0e48806889185c010501a00c103983c1d01904043c0c244440c10301c00801401441d0054a0b070078005841c52080c015140c000610721a40c4a0311091088184082c1c001154051582a0103804070b00c1090f04541d0781d6080401c164603544203001810f0044001d1545030b04d05a28404044013180b150581150 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 192278687 1250 192277437 192277439
    0x170a0203090a030f03020409020f09030601080607050d05150a0e0f090313030209060a090c0c060515151b010501120606050609010801060c0f060207110108060a1505070507091a19 78
    0x1000c90800361503541881e12000c51a413840045010f402560041d43c0414070000d01043c03101040d078024a80d00b402a400c0d6680d581e40c1e0519035444910480e2100c011070747c20003902440c244131790300c85030784040d00e400d42e0f41081e0403490209810f0201d039000484a10030303003000d019100d4641c0b2100c40d4010701c49002103103000b034455241618012a84002400f41c090903010440640e03c4c6400b00340984403041040105030f103221001040c081c404d441c00c1d242c45160402103280b8080070640507041ea14050101252100000c8541f00070390310498070303000440800c20105c980580c1c280610381c02070840d440400440100ca00341402190b000c0c1e401644655030030094100d181e41c0040a603411107042c0e0901401034180e0741809040d003501104000c0100344000303509820000300458043c16104282d03120034841d522041400001000c5024680205001c4031480709114800d1000782070880c8101c0550349102c0e914056102611442d000304c00301c55807800b03541500d6040a1030104202641292413108c0c507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 192279937 1250 192278687 192278701
    0x1a0c030a0e160b1804020705060708010605030c03010b030c0706050103061508031939110402210702070302031b090919080d06030b1e010801060b1c0603080a170a0203 73
    0x40040344180f001028000c81e894081c41420143c0802c0030308003810545da20401071034416140c40007210101e0102c1c139584004529244a881942c0c400c0009007045465a42803008440701600000c28842e00050f081001400103201c500035540214400c0c1000f00366a441000056140c0d611900001e00303903070052185281176480d0700c1d81545089194100130b54481c1101741c41122a48107150403040c107003400310b50540d8070344070564410b680134020342d1f00864402444080100740d11407d00158003d900c4402d48442c58800710f02070a401420a0044a00f610303520f0303002c2404d000f80031a00c1d5969500103042c1c41941d007010501c04d6800041e40c400740240510200c450406541c050030043c00208010401a241039181d038003002c0550741008610742903140000d0180c1600d00e91b80003550300040c010b40001030854050044034155403035407281c10b05011340c03e01c3c80b0a0710382540c0c00005030706448010000102d4000401011504056075404400300e170b51445880003000081c00c41007100d07104000300f042c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 192281187 1250 192279937 192279973
    0x60f060801092102070f060503090607171f050a06080a0e0d090315151401020c01020f100f091a040c140f1905090a09060f110f071a0c030a0e 62
    0xd001c3c480c2c00004508446410204e150400e076410031701e0405121140401d10540010180d8400d405070742c1124525a510101152030f8121000e80500d011b114202248030325410314203900503024090401c00d0741903501c5d4009a00c08100e036004c0342c0400c040b0000e0050311910741c000c030120309001c0c40041a03231980051000b0141a1035100c040d040e560035054070942000b00f908080314143c030500c840c2d0991921404202d941030140c1c07401c0c50252048101180e800c0d400450b000c4507000b01d4030040c0201341000310700c0d4005003a1810076203841c01c1d41c58500c50001042d0388000040c182e00f8102200940c90300e8a00318100c90a41d8000800c800c00902042001744d4408035034149450082d11200d22428104140b40c0001101c0d4016942c070825400c03c01c01c2c012401d6000702e5403907014510a104a010342c0e110601150b6080c0030169030000200410b034810500f42c002040110321484908448500348882a28540b8041e0b811980c07030540003061003022038403030043c1100d18203c1406807410102811030342c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 192282437 1250 192281187 192281213
    0x61a0403031103090d03030501140d0503031f080703080a090f0e040f02041419060e0907060c02241207030203070c11180108100c020d0c0204020702040b0d060f06080109 74
    0x81040902ca8039841e0602050058070801d980280900795400381705c0c40c020b8042c000c240203c0f6401070960010300300d070f0b1410404507180f003904000a103103151109000c5241e0740b00707440d803503000c4445a5107000403484d0040054000441c016072400d500e66045503401050190304d5802001303801a2140c00703200300c1d5052114260082c3c0d001c111010100300504c0410090a4880c01108100002a007084641e1080d9444588500c0c111402080000d07111800028100380075146a40d96500040d01403100314002e11800b01501d000a11800452000c101200e050030b904100301c05403043c021031600030780451040141cad044030040c02c0650940c83c1182e03000700000d540b081c0113000d40e002c040e034603003064942d80f07551013102c080803807035116139030b140c0e07030000d03a510311071300d4844180c62803d600c2841140c40800c10b010b4148655841003181401c503000c00019402c07049013684d020395600555130079903450903400f01c031051042c8800300e1140300c0d00c5a05000c0350740d150b2040341c0780d9040028103400140c8082c4410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 192283687 1250 192282437 192282443
    0x8091c050d0503040606031b180c0903020904020301090c1215050f04020411090312031909150507050426060a110d0519090b15030a0c03080a020c15040801061a0403 72
    0xb40c0c0701e41d01e50401e031000e080b42d580054054801c0c60b803490840500615810165078980c8206a80c90107000050070807a41d11400300350000d1a002828001440d0505005811900003400030818000640b503940e01040c007030b03100d01160b4580741c0c4203a0400250050b01f007034204081381e00f040186401c11480305228401880248119901c25201e81c4105c000410b49100e070001504481810244001d80c0e0303902e600a07034070022202007180024480302841d000d07010b40154071801000c0c188496042240142501804101c2405002c5c0004108424480400b405824031800d10700051059021140c1c10300902400542100e8107105948440028075001c03504505420344000810303588402459440faa8146d140301101400e20780200300303100480082c0c500803811020011030200c00305e804c050341c23000624030040860444c0c03801000450659400b41c45c0c05001401614084443d25000031000e04000c01840548034012130140b01d00781d001d11500000d4981004e42e8600d19a061400840da400740344401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 192284937 1250 192283687 192283697
    0x50a06120c02101e0b0301020306151b0115260c0f06130603060510050405030a02040203060301091a070e0f150a1206030b180a0201080103140c06040308091c050d 71
    0x5036025030b01c2040038000403c2088420070036202c0f0100e130600d01d05480302c2107160315401c080041d001c1d07281c103100b240c0c001c001c010054440019480e0301318a50790404a0401e194440d82c0003224007028080c0540b103460040d40342d01260702030804009070758000ea0103070440b480c00540030529040701d00001c0c09c8004684115000c9400d05403210025286128401051840d281034000028046c1d401d1340017482a203004035031250442c0045841207810340258464154154000c41c15030015013841c1c0e0003075403c90b402500110725250310751560000d640290010707040d054913140800c6210f40e40443e2006c0c0c0f00b10200d41c22000900300c1000075603111752422281820820000e080c000d054014290760482c114111020302005659041c05100510100c540c000d4080d00d800003030a084001003034005c1e031660705854000c00380c4d0858071002140041040b0752a420300ca08170030303550341f42c1d40d41c8080d10003180708084941da18075070801032003103490b80a101909807401c041036070302c001003000c10320140e180c4aa240c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 192286187 1250 192284937 192284951
    0x150702030d0e22020403031103030c22030503031501030e0f0a02040c0e030a080a030c030c050d0c1b0f02040c08060102030706051003120509040b12070905090f030412050601050a0612 80
    0x3e5600b5124606452951008200280c800000ba000b034130031203019403100300304500d604608585070f200c100d54101200d8403c011030b51035600c11402d90078100c08401000745805442e95a01880c40d0300c1070301c442d141059000c0c0075182035a8903014515003410044082c0c01c46588141065681e007002d000c000f40f00d141c403000c0d4903a81d507210390b101c003c5080f0010700b00c0c1c2c4107c003a1305251480c0d5000c1c0411000003803c00982e50307401d038020300964107901c000d43d40d141c0c40e00c00b001c00110700500040c400001041000b4240b942404960400b061406015021051800c42c0902c1000104d515000f501414007414004200300e0381e07000700070b40311103a4008801007400c0e43e511038440086415504002e000d0b41c0c40181411516074031401504403060705075820803007480000b04110034a134122016000c2d65000410512160f0042c1d00400c1d000b5000704121561078404000c05070442d00305d81c004103080303040f110303038041402420060300717005040950b00c0b0302059041041c01001c03050942c0005505640710343c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 192287437 1250 192286187 192286189
    0x30711030705061206040b0301050c041a090a03030c0f021005130e090604030815030d03093e060403140102031017030313052104090e1c030b06040902070f02150702030d0e 75
    0x1034201f4000100200071910701154540b2680c1c00601a108100c031150103002c0043c1c17039000407915503090080a021a0303529540c0c0842e01c0e101400400c0783c0c945448158880141c5428102e110102c90b191545902c600f600c5c0340d0300013035007415030100d1001c0720041d0038132910a41c0412440d80282e010314140c03a071592120001e0070344d1045414660b806126480007400c0c81c0e94181d00402040d44141c2c204808200c0214243c48030000c5e0001c0f003185501603007007803c4503080c0b40b1408016240064903041c180355890300c4101540380300d80c034114802c3c0d400104210500e00c502103004082e0a91180010031050010b4150381d40717002c010059040c50131032400d9130061080030001b917404007040d42ea03107400c001e80c1c540e07180019411512880da0380a04056052520340404102c2000c2c2101c01e014004802501940c200d010309821508150005403c01c0040b944841d14002040d6150180c0088041c1201c2881801041000a090f201e581c1c0e106020301001680e01042694809107030745001480b07601920 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 192288687 1250 192287437 192287441
    0x51b1201061514040b460809060402010f03050a0f05090a0302060c030106050d02030c070516030309050312030f070e13020c1912030f0b0d050a0507080102041d090312010803071103070506120604 85
    0x1011100d40010f04046c2c81c040141e81002e40005885942c1d40515070307215030000f141d40b05400d03a80240455420340d1032007071040c842e50109034480d540c0100403882c9901440c40c482200c1040d00c2884041d0410b074100000e058042181a42044031851040c0ca103614043d402080d5000307075041300c1405900000407030714841203034081e506c2c015000010f8075000c0c00d00e151145203a071503034030046011a0781c407000003c5614001c90b941100300c0e05001102d2840d40c50750190528601d004008805018013540f400203941c485144945070101d00100040c1c0d01d10b1107902d075603c0e0840d0441000c150740f0142201600103901507100054401030b605000c9511407107020510301400b82ca07045180c05c14110900c0c441070010010743c8416043c040c0c0f044c1d42c81e45403900607490a0b403213180aa1060161380100b01d010401d130f03240340180d0010000091700e042c15010350080351000401e81c030458041e4000f02e80213050002016103140480c00480081c0308251610b401304109000300070741100480d0030700e800216151155 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 192289937 1250 192288687 192288757
    0x1151713020d0b0c031501050406020d0c0c0806090d020705060403020105040302090403020a14030a0905030f03030609280f2a050a031803111207051b1201061514040b 73
    0x12580700c2581d07180c1480881340c0b54104403409101460105000c0c2074a5000b0300c100c3e01034070b015901424000064600555004c00c05030340440d804000103c0c0000e10813000d20100303000b20030000182180c1100c03580300918280c02c94104c14403e00d0b04000c00c0005070f8025040713504480d8140d030b40c07201e980c0c1c45042c20303030500c05242030290403502074401d070720018980030008107000780c901d45840303c4094139035050541e0780610078007000301d5600c1040450300d85c0c540b161540e540304c072004514400c64003d034844090341a12708821b640c8200c0e120b9006040401580c007625145180c60300c138031070704a200c6410714515041d940948a0038400700107403006a03540300e40c00c920f04070204034185946410b8103280003000045554102d45403401480d9001003091410000c80e851280c001004041841c81150341500742051007a005900c456180ba841c0c08080d001e024600040100f018004104441030101502c8050035030314003400014100018809102c81034140c41c40c035800a5904060441d52444500b0100f0b12 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 192291187 1250 192289937 192289943
    0xb040521070902040807081f020705030403151a010807020a1203090c080705010206100807030335040210050f0409020906072001030f0203041a0403030f1401151713020d 74
    0x5000800b14120405800600442d2403280850328540d40c0c40030b440d5181d41c682414200c42240f034543c488980c0d80540c000d4101d05000d05c05030f0789485d03a65900c00d0030701c1c400f4070212480e0580f610640341c0c07a290554410283d849080c01d115519180c4003400940f0783c000755400034039400843e0b00d01510140320b43d2181903203da024600408851300e030b100c050345c0e500103440303140c0c01841007900181664502c800305a0851f01c20000502c1007038219901a9528048103048040318003480030504540c030020300021503075140034040c00100307003040d0040c00b40300c0c00d8459560f0103210381008000c0700c50b6205c5040382c00710b442c1c6110050312240e40b00f001075034510984102803c0440b16000201085440c144003100403017098904110f0713051340540140070381c0411500904114440d40841d2602500c080003680e000d8860724001a036101304800120883d0b5076510500401c45040c0c0050248648040041039940064101002e1084007029025107000c1c0c02019044c102c154016003a0454a03101e0004414543c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 192292437 1250 192291187 192291193
    0x1020a02102a1403070503040b090301020906070b06120f19050a0b240a05090406020a032007110a030c03030c080c1f0f06050609011d0406030b07180b040521 69
    0x100e10440c0300d5492100035010f60300456000c8480f842d0100000440310000d600c200a9801d040c6051270080c1c40d90000c104d100c1d0555002c2085200c240c0e540f000420701c0c28400c0307904d2031040c1015010700c41c100a071020312200d190702c01c1040d00590304000540e640001796192240111200515100c2d05190350304c00d00070311000452051040c0c4480a08101454100306101c403041c80740300b4003c04c01003008a02c500b90700b140e800310120b4085200c076001080003a0700b03424007040e0050329107004500d201c03100d400f07801400000315040d07080102e80c0400340d82003030b0100c445c00c18460035511034000320701c1ca6100041c1404035443c040360410a801c2c040c0c6424001403826250071b00c041d64240505481012821030b5924544150060300701141e21640090300d6005c0d081380c3c04c000c0c10900548451001d03003180c019400b070b14041400655164010705010f1440b40721540018101560042c0c5130040007080d4403034800142c84140800c50449007a80c0849804441542d0140390440310f011307082a420410040c140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 192293687 1250 192292437 192292487
    0xc150d0c0c020603163209011b080a0e0d020306011203021c0906080604050f0a0f060503060a021201170d030b0d060e0d1d01021b040b13050114040b01020a0210 70
    0x30080c5c08942d4452822921401141411103138114141104480c0c601440c01505090040300d20340800680109a018140701c2a400a203041001c02076541600c01c1704c488100262030030300c180d400752000031038403019203035001001039039400a5150b58050040e59160142c8980910506100700181040e8108681d0401d0100c2210035005202081c80d0181502240510005c2819402c142c0b0515205240d40c204000c001c0c1c0350f00c00d045010346048a28a40d015071281000b0034156010311030940210505140141c1d198107443c040e00c51110b059220f9403d0003d41c15903213070301c3e1601203601280b10b80c06160010305100d9403c00545071102c000c801030980e0b4645072a40d00b44400005120000c8951912003905180d0344010f04000e0780e00351031401e40140c00142c00d02d409400780307215001c0d00c04001440030518111071404644441121116102e20f65140c4004101e40000e10300d00c180080c500744c900f0f100c00b107541c00010f95140b08480e0024001c0d41c03004a0700740c80740c0c0304144081d0000a0b402c1124190 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 192294937 1250 192293687 192293701
    0x92404090507090501140304030e130e0c0306010602010c0f0c0c0e070c0b2d0901061707090c02010501032307090c03020703020f160302090c0408030d06080c150d0c0c020603 76
    0x91000719402c8002c502050400309040d801640000f805082440c1103600c1c2d0f65440d9411070303000207038a06881c0c020005454448000115008885081a00c034009196486010b410149414410f92121040da4540162268150b501100e045c4185e1481d08010700030750803518040d11071440d5907005100707210360102072109440d400016021428014070b4401300c5078031500106c0c8040c115050400011242c4000c1800c040c00c03803002020b510145000000070b400f940c40c1c03101070290040c41c0c03003042d8039081007409000038a810b2069004c0c00409100030001d942c11030783c1d240016071b00c00802030302225100030725071b40d40c620411a15028003526a800d0062170490200540a0b410010044002d4003031031b40401d80030307100000d1810364481d40ca258020003a02d1078084c40f09503400981440d401c0c400411001c62217202c04c10042000721000e007070004031680307030501603400c1c61344000b085c512810b8103168208413900035905130303420f16081c5600041d50510881c410f44900c08070b5800290000030100810607a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 192296187 1250 192294937 192294941
    0xc03070f050f01110303070c0201110601060f0807030911010804050f0a0503041d090601030f05030d050106170c09010903060b0301180b010e01050102030f03070503040309120506070318020609240409 87
    0x448030242c03200740450018000548034501130340036400182c2e00c00d0002580091140e11014445401810100305112507552828146402600510302095035109030701a0701d41d0103180654021480d00d4100030404c007565840100c5a1a6203500d410440010080340611009102010008800b0402ca0324600301601e0095200d030414800c018040c2644003c0c074a10450503c038452181300c000700034049507030031551100c14809a071a4260f84031310003485682d034404524031680c0d02804103600c40d440c0050a0004425207a840103060111084050040401c1d5903007148140e01070320b03031000000c1803503103440340440e0041c8541e40100b200d24020011070814040170b151041d041e24480108100b140c0c2c0c0340c200580e40c1e4800d00c00c3d407020401e010030020354410311500185800c03a01c40d140501500303649104400101d0f00c0003900751280c0e08039100348034001e500b5114100b02c008080a0074005004542c0020360580181e0301038600495035400c1c0500340000d01c5000040c600e84c001007c42e101c0317440f0080040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 192297437 1250 192296187 192296189
    0xc050c010c090513020901080a0c03060b070507090b0406060c150213091b0504060c14100501060201050901060e010b04030201230f0a09080a020d060914061f0b0c1c020c03070f 77
    0x1c0070314407280c84c40070807030f45500031100c0441c4103031103441013030311010300780303001440800f01031000c06030b48010105a85107154000c0000034002c1c2d0040c00c0403400d08114504842603080c089200d585425400c100c1f55820901d210409600040f40383d170109040d02101000e44181443d46c8950b9180e01c001127a0540b0070f41c84003051100035403203003100e500d481c442a6442d1040740110b001155032040c032500094210300c0b122014140d0103040d1905020080d5064050f950280c00100c0036075120400c00885210901c24100101a030b098903880315490428170000c5c0740b00f107000190402074181c20502d60300094400f402403d0a001001c1940c403c4246560a0903030805825900003038032000ac0000e500c0303400030704612016001000112050341559503038004022929003182d1016031840700041d581b8043c090341c0d2040503034901c00e0006850000103020041c403960000e030000c0000780056546c1d16000110b02034204007607044584c07420085030341645480c0d640480070754544070b2107c0201d290100002c1c184 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 192298687 1250 192297437 192297439
    0x190507020a051011031b04030b010e0604051303050f160b0709081501151d04050f01080106050109080a021014190f020c010f0f09030204090f0309061407060c050c010c0905 75
    0x10700b0303c483d0006080700760743d25000c0c01546070005001180000c0d4285900f446a0201c121001d8a096075070f50b00c13950865030036403019000940700c50070000507061034022298490001000c07a4425822503501030418040c0b030200f4500500d002c02d41d0120380342ca10303240e51011078010a100303078141b030305040080050b504c070300440345540508464000b2130301105001d141660607600c900380038040d03604811103c2d0301007409045a080c4110301040046d07101d0340700f424050002540c0e04012903040603000c90a40b0190b5200c5410041813a03000c0100c400d0101d481c0315096070407989490040c002c09030454111110741d0f110311b290380d00000d520803c41c01c0c818025140f40001d80310b50b8214001c1c0481686c03030b150301521413800b00c0c4151080c0702c00288139500d40e000c00040381c2003401d0b150307803240c020070129020810b0444140001d5200c1405068214007540024069440c14450b854101c04031800b46001e4050014416515028580042e5000b2010f8804e04008000200440d5891500080600406210711 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 192299937 1250 192298687 192298693
    0x30510021809011a0702011718070821030901020f0a2714041e0c020304051c020d08070303110703120605030303010b04030b0c0903120c060109091505190507020a05 72
    0x840d0840c10034440b9a4121040d61100f688440d115442d0000340340e00c602d0b0102d04000885c4c1d00d02c29407a040d191540c2c0545903080300d0341482843c4020b2030b03292001c1134012044a80c4154120b02e03070003e120b0703072044130200c1010690780c817a03c0715010b4501a005042c1d10072500c0c0c0000c2044140310741d004103c42c10460341885410070480d010656041c0f9200e25025030301842850944104e21410503420400610800030041c482004804600f601101c000c90046001600005020460340c0b41c111120110515a0449403888a88a90014142c844151001000701c2008904c817410305020741c3c02100032408401417a6501e0784180350003041e000c07a01300c0800c2020b01d440404101e81c240001070705d050340c06605940d4600350840e1184448140028800700180b0810400c1d12407640302440b080119006007414a80c440509410355414450160410341c09180b914000c500803422588850041c64803816000a035a2290000300d001c082c2c00c981c1d090360b01414001800199a800504910664015016 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 192301187 1250 192299937 192299977
    0x50c0402040e0712050609012304150807090b100c170301030803180706051606110409060303080106031803031a1207180e0c0418060905150603150a0f0603051002 71
    0x85804640c01962000d0300100c860b0018842e844503074000072705103207039003200b00c4400c00c406000809071103d0503015000064240d00170003520200300030f0440a44032690040c00f07113003041004111480c0540c044c402c100301540070700505000c0220351070100e02c90319030380c3c503650386da1031381800d0b0490b50081e11500e015035045a003004070548045019030541e10717280c0d182881c00428035840710440284000130384940e40c1e1105564143c00103000140014054080b011602078510304018100c050168041c1d001d0508080e145003404020182c40600c00da1305080c0082c2002981412a00450000280341e4000704c0001301909444400280c60b030403a243e001c2000d01c8000d900101c10203070364048525540700c0d405490142c030546131680144d88100361013000719074581095250b240540309540307030540d0150040000c9424841b80b8200c0c10394092400d90080c80d03000c006007c10414108000d05908085580d2080c0c645000072a400410085400404890501113500d50b030000a610403140b040b030040701002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 192302437 1250 192301187 192301217
    0x40c0503031c02180306040b0906090f03040b0f0f030718080c010801050f011b030f180506030403030e0c03030d0519060503030301030b0604090602030921030121050c0402040e07 78
    0x2118502c085800c0c001c95000c96440000c00a5001140700c2d409079200c1030000b40e1a5141017001c07520443c061101c0322424100318620702d00b08040500b5405c46600400307107500c903182c000802c40e0222152420015034135005080c100c400c3d40200340b503582c9900400014802459403000e56181c1c900811840a0401036035020850742d20a42c02d50a0350116040d400104180d1400c2c2400520050060414421007440003005141107680c541045010a50481540c1400c1b54040d00102181c3d06100503020403c0c00c1400140c043c0c04000c1c0000e04050300c425040010050510200000141c00f40842e501d0b00d611049010143c14220707030f401302c2010507040b261140c0e40c9074082d4000b1500058050343ca10f0742940c50b2129400c8009020740e8203e501d40398000b0000c2c03447d100452180b030341903001e80201600789080411100342000c00c0748400c0c00900040c0110803022a8a901003144c181d8890f40300f1441c1d1910504040c3e022613610380c014808903001811191002c0610b10505645d561007440e402800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 192303687 1250 192302437 192302443
    0x60c1814100c02060403020a03080403050c030606180402030a1401061d070516030507020612010501020f010e190c0509010e0603190f1205090d030306092315061b06040c0503 76
    0x814141c1e101072204401000c0c10b00586a042c2594005841540391607100e8003c03c91040860f84122010f9400245c00c000b8000240840135180b042103000d0113240c20014005010704c85600e2841403c800c02c0c00c08541150f03010800c2410a036803080f00e10041900d86008580280b02510440210b90b240d9005102049070703a440d098416402a100c042c18015203030404480d401d41ca12080303040c44800c200705405a650304001e440d8407802044d6405140d03041000090802c05000c0100100d68100415480b10001c04102c41218190190005004140b02e060103040c85a19500141e003002c07501001003001c20341c104105208402c150300700c0d00003218801d2400041c08034400060b02d08003006030304d040050030a4280b860401c407185499401c2c00101c00001d5110340c40c041d000c4001c05d983e48020066190203001e000c00c4e42c48000e5459000d5540b41d14500588200102001c45200c92260040015074030001954403802604028083c00c86011540303039614201038405076a00401c4201c0065075141c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 192304937 1250 192303687 192303719
    0xa031e09030206030721090f020a050409030e22020d09020a050904080f0d0222030201020706051602120a0c0801050714040315090302010209040f0911030307020904030e030a060c18 79
    0xf819840c550740d00c0442c1181c0d00100c408100c1008240c8150940b0400010301400702e403a40695018290100c180c0304000804e0060783c40940114148502d03140400d030046043c1c04c00f0442520680d0034860b0a00001195010949500c05564400300d400f441c10869680005040f80c421b0303d00320751654031041003000d08402118020321a4404201c2200c400d18000b02410b04805e2510000d070070070075050322540c05080c0190b1040b0f442622154204155039040140800074051030a00c01c1c1350000020000c00e8250440e0350280c007034202c2345440c0e407091804021030764205070040041211a91a00d20050207848240c3c0c068001558010686882403040b0044030200c81e40f040c801d0000e2814a80907001030700301c0005c26002e65509004e10715440e211030255100c0d990441c540050f00207411b1621111440d10068910301961041c4500d60040c2c071340005640d007290701410140c03034004c0c0c1d0400083c944509488000d25182c180300441500c1d9030400c200d81c00148800c02c00c0803586440c1e14102c4072404072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 192306187 1250 192304937 192304939
    0x1b0c1103070509040f05070b0a080406060b130306021c1506020c090709060806030a060c02070513020f040303121b0c020306060108040c050d020103061707081209180603010207050a031e090302 84
    0x7803c004140007816a142c442e1030244101c050326015543c030514412550003050300f5601080c020b0b03040008000a61107090003030030b0519100386c10139411003120300240c855408010001a4000b03401305614009800c2c0604664003500248007100107100c0522001d0002e10441026103c0c8944007200c6c0d290480d5960720941041e03a41350146407030200112202c48000e462590103004030b00c070000106445000301151b0036581d4006124042c81c000601c901903d4030b0681660091040c018001c150541c1b000711401c0300e0f018640640f00c00050088100140188032010100b600c3c1a070201e404076070000000b0403800d0088060b52029900c200065826071000c0f50010700050f06c084081c07055142c90092100e40a00616000640d03c0d1561035003540040c3c0c03900032910307030b52000700204541c0c5010446488158030b802403060501c40c1d540c010a180345041c454084100039940e002482d1030f2400d60680300000d070440c0868100e181c1c03d060280243c842310803105e01401178044003011080c001c0742d030f0714100d943c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 192307437 1250 192306187 192306199
    0x9090115150e1e180709050111060a051f030f0c1d07050f0c06180f0a11040908090405280903020a0b1f060527010c1101031b0c11030705 60
    0x34544200002501452100e5041080100d41d6001948680301300c02a00e5034a54140c810b40d080052010b0080501a44658104034617005004a140b4000c5025600310350320b02c901103070940398200341c50300e01e4411000e141d0000074102000410f0001800100388244e00400440340ba06442c2c0e600103650031421000c0c4243d003014440440d40091160000740000c440c40c1c1d0441d400d09614030101c80c10600c0903200520a22022056a03a880b50240102d2601c4942840140060000356480c0506000c4105940e031040d07586903004d0b002e1201c80c01c115032901c04014020441d5250980c86801410040e600444c1201030400d0802d03200701041c0f2074050f41c55090740003030001c1545075849030300c8400000d0000d6295a885851400352a0f01020800c020305002c0c1c031983d8a0f9075034a103c861018080c0131805000c1d6030902c52094151341c0142003804000d0b0400504420b80c81e00f51700603406031040d04100c5403500721000708941e400d41e00c1201c03441c295100d00d0688080720311303400c109030ba905440c0c0a00740d4094 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 192308687 1250 192307437 192307457
    0xb071d041a010c110406030809040501080309011b0c0e0702011d0c010e0f0409080f07030f0c02010801060f180b0c0111030c1605010605090f160903030e04020c0c0909011515 76
    0x50301070b4003000d051034494008404100884d802003020368840340d10840d94032801040fa020580750901400f03001d015100029814404030b003000900c2c00000d00c014865a0611008407003e10200f40034010162010444c1e082d200c0c20005002070081001c00e03211480e40d90030318a61001d50300d0204400c1c1038058140d4901c0402070b00d00080045400300410010741c0550340350b00c07160002d0750007400b61000500d02003000b515400d0f9800d0141c008210017103003500300840030100c3c4005130303004101141075441920704104200c68400301900c9a00d00e600884103840c0151000140040007000202400f41e80c2400a004d407454803080c00b201400140d60140407018180400c0b0b00c1e0000c00140c0050650144002240a9a483c000710b610000260348e83d050000038001042220541d00341280050701c0d041c1f8211103001d103035440051081a21aa000e44610b40004118003da10308005032100b040000f0110780040c1030440d5428020b081c0400e410b154000483c10000d00520040340b0709407503640a0b1280c12100f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 192309937 1250 192308687 192308689
    0x40e1909120e220e01020c0d05040f090209101d030a0606050102160b0f09180c270d020909071703030a0c0519050d0906180c080c13090f0b071d041a 65
    0x41c0881c8003804c0a10342d824450801360352000c1120900d20000e5403a400d03600c40c113002c0854810409904021401c1e4010420714000d0b4170b0381c045e25540d0408614080f040c00041c0792045e03c2c0900003d482582c1403003144400001c1c850158483c00031078909030221444c12440d60803e0a08000034411040c07626410b0154121409000c001008031080040181e5060301d8210a1242441c200340c42c00c050f01c07000411041c0011010a4281c090300705207100d20404203114100142d20035a03010b000900031100480801c2e00200200011130190034110400b00e00030366440d0300156a40c00882d18101d0180c100052001210b00400444a408420750041803908903890400e03903c650201400710100390361810010042050b40c41000d4a00c07411154111030810241030561802001e030708103410580007144400c94a596900d1661500302c42014081202d105038102841c50824010020780340403605803c109055601140504a2040b191550304040c0001400e0108481c0d5240004e0140b000b850032448003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 192311187 1250 192309937 192309941
    0x504051308220308030702160603020f0a140d0f1a0406050916020709050702010c0f03050702072912040c09090c06031a0a0f05031b0105040e1909120e22 67
    0x101c1001150000b280716540ea80e04000d0b40e01c01ca078030200580260704a141407000c440d1042c4001c01c800e00c0d055040c00710b01903501d0014400c40a000b800e03c52100400d1034000741c2c15083d10380c0300380c1c509420004103403000036020113040c4404400c4d144101e0344552045d107141521920013541d60290000700c850341d07240000241444500704441c06d511914a0002c0c601c01d0900400d0f204440d42d500108280e86011005000e84804814400c1498109410081c5807030b400500f0200310307011003400c0c5048000440080318580300e8005400040c40001407541c01801054100310700840c0b14514400000e65a241102d04903080d201006102ca10350030403c00001d80300c0d4211440d4080090100c01000103a4070000d09420101ea12101b1a42d031100780c01c01651400f44107100500352550700b6544100302080c002000c0d4400c5004840c0c500103441c020880354520325140381100620b02c4410440249503003090b01c0014485001c0a00140149240091905004008c1c100109902c0034481101c0f08001007180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 192312437 1250 192311187 192311227
    0x80703080a090501060603060509070914060d0e01240b04080c0f03010b031c020d020102030609060409080c07030602071709030c090901090512071a070f0e01050f070c0504051308 78
    0x1510703444032402c8020540070700c2154010300c103a48000694619200c00d21910308d40c001e21550902140c0d4508009007802c507840c5144004007118266131700c07120f8000f920020149860406019882d102c261500c1d41c4c21140310b554040714644c12022281d980d8030200c285481a8011a1595045006c00040c40d092040251150311001000400c5503007015003c00e1510707184803521641841c1c1140000013458062002c2c01e036101c0a42300951451234003402080c210304004e482c2c18040e0307545107881401e204016068031000c40b41402524821950381c100308d000f03500b242c142940c804010010a0308481d4a40c4101c40400d039024010702022144a41000712442004042800b155241c0e00c1541c002603051103100d4082807c0768a0b141c80700d4680c1000d01c1020800d8107140c04891040b000c3c4600c0700e0708450380d00b8110032689422040d070201400129050300641c0391040d4101c401044d1402005038150044050347d1080d50100410b6903807161503001020101c50141000302c080020180d0075000c0c24900c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 192313687 1250 192312437 192312451
    0xb0604150806011b0606060305181b01050c0607090302010909060612050604061203020f0c030718230114011806050d02070c050d031701050f010915090b1603170408070308 75
    0x38035030540992003013a4407448403204403030f00760355100140310391a05440b5550b0008001104690500c0c10205901e03920b0314203c0c020440142e10352149205684610100c8120550074000d4580c2418078040141504280d800101d0100340c0300c16000c0f40c5108148988000c8070f43d03580d00d120280044084040060402a10280c1c000e525070002144000348401c0d0040024400c0c0e004111040e030030510107060510302d00180c3e10036003150208019105601001d6060140c010500055803060002003440b08113103240d0301000c0381c1800b030000039407511200c5e50450b0740780c007a00c8140880480b0108040468041d000d894003080c02400480042c50348e55002d410f26902c00d424465855491750005010940d40300811800a9841c01000f014100080d1000b0700400342039030350a00551040d00040c1c407010fa103026604036168200071292602e0700c82c0c0d850a0080c486403081d940d481c40421104800b42d80360f04010b9010600c41606c1c140e200c0d404518071449940c10407100350410405030b4080311042c030050084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 192314937 1250 192313687 192313697
    0x61e2105090129040f0b06070818042c0105070912030e03121c0e100c020a0b070908250303030506010c08160b070e010207051c0b1008010b060415080601 67
    0x148441140707483c02e100e0a401e0031100300068012000400041c2c3d1250403c2c408410b0628446031082c0c0c44481c107690901e40c0c081c51b80d03070300d60341d541031500748098002020981c072908007207400280b0f2100e0b50103c2100061801c0703050348031b0842040b8030b080c2e450566001c40021071100040012446c0d09518181e50340c460301c0c00c03461410410000915120400302c0e03000d5200fa000444c0403445076003808284c4141c542e030906011303150751103003020340340c10701907050300b00d104d465800042d440c902c00d11000d5203850740081da282c00c0d4100110b0040c01c01056015003482e52041c14a40009401601007610305c060310420121040350070b42e40d01320003402c0c01070505410b0000368643c0c00d001401c2c0c94050302030801044507803100540c2d030741024064000701034071100c18018200c18044107a68041000340540740156000c3e241114041d5410407160b54810001d06000000014000424141030b501c0c0100c448400090204003840410800c9034841c0d407003035500d81e10001d44020011405210401e60214050400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 192316187 1250 192314937 192314951
    0x90a0e0901200c0f0a0c0e0402040212180c010c0c0302040c050f041403060109020405011b0c09090f110303030108031e0f0c0a0303141506070503090a061e21050901 72
    0xc2d5059070348525800c20000d07080030a049044403410403040c0106800c1300c004001032142c0ba10382d03004000990081c00e0150418000240c01c1d51280d030100d400e000d0301c00d41002418030304584021920340c281d0b941410540075042d840b82696102d03544803d00180c0040092551750702d5031b42080024100000e007501842821722881c0c041d205000082d100410000680c190007642e81d00404d400c15030140c000c401c0d100d01c107010a01036640e101c24210b000b0702034800315400340c40e03040c11b10030320f040c00c503502c40b4a0150500400c0300030082c000301a0055103200c3d003a003844c5c0f15004030416440340400d0040c59401d078010b01c0007901d800084900b05142011a081e010324041050b10a103906078008a02000545d106500341c0c3c04059043c4030b58002e50641031080303902c904103120b9061034845505010307445894040356850602400380216001c10344024903424011307558043c0031305aa240c60703490440e10428035a11940c024042e8010001c6111030780c0200001f00419000c000c01020040c4c088202c940d41c0d059 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 192317437 1250 192316187 192316211
    0xf030c0906040f090305131a040b0a020106050303040b04080601082b030e1203011d070f0c081c090b010801020307050702010c03120f0204090e030c06070516080429090a0e0901 77
    0x2141c040344c07500a0f903d1a694000c84001c480c80c1d64000c0e804034800316110b05080c1000503c013016034041e80c503952003141c1e07a444101c804030f02419441d040254036000c0002c0c0090ac950b0030700010130880d0034420507198182c0e603400740c50f07440c0e00342040381d100f1820a982a92181008051011014805078200043c2c513040391020246000070009541500781c0c0c4c008014804031202480900070a0001444200340380340260006000307180a00c082014020071288e0f5100b04502d80041c2c41100d0907402c6907501d101c01400d401409010354580c1558034500410001c071703d242c418002c491081d815500c8451905581c1c4c1e004440c00088402c0c160108418203030b50680d100558000d008280d4480007001d0380365820404003d0840c0c076459000c0410b603104000049c030f041d6000c039205611022a0514a4982c5106400c0601e00a82e0b2030300109000300000b800300707510510304501c1202075000a0b01c4080d9800440c2d180915104207030000e0742c0308080f0001001002d02c40307000103034481c028100100304400310380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 192318687 1250 192317437 192317441
    0xe090618091903050706060e1b030709080f07050406120c030809060f0a0201061a0c06181c0201060801060609050f0915061303120215070309030e090405060402010305060f030c0906040f 81
    0x3c400140c800601c0300c1c240b01d0760b40580c82c09000380c540e0440d06414811130800720b0590458100b20044004400183c002d401114181c0040c0880400e450003030740300c05101515141d00d40201c521451801d1030205d800c04a0b803892210840c0d00c00000743c0d0b61420b5454800b490b402816951354407a01c00c101143d4403882c1e54000d401c410300700307400210f120360030b11900006c1e140c880a24007803400024024102564800111280c00060035054202038825004c0f8486c240b08202422044424030132100daa9099030541c03101d411111114002c002107904d5250441d0404a20701c201680098034501e1822236207000c180349a003060101e2500b503041c0703281501180440d0400081d10900030200001001400680d58040e440c00500d40f01030680d80180d04108805584013a0110041694941c0b40c6401c250040c0754034180701d0307801410102e02e840c1c00e103050703a40c0d03041c2128224002414080072401c14145121002c0800358014003921403040c6072818468482e8004081c1680a92120742c034042c044103038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 192319937 1250 192318687 192318733
    0x6030d090e07030f090f06200a051206190b03040c08010506010c020f220603050105010512060424020316110a020603060d1e0f1704081902040e0d0207060e09061809 72
    0x141c00c0408d44500101240c048910551411010f24508112103038070710b0340c441c08403400581d605903404400d0700e4110205002083c011000b40106801900c0400c03041c50400180d0f21031403141c0480a141e64072122510b082e80c209441e00b0340403660401d40c0500601e00300682200740d030000382050303040c1414000f014000d8107002000e1601240e0300e030b00500c180320007805a6409464280c80180c0102c04000c1c03860350310380005201420203031001942044100d00740b0500c04444500c1c000540d140c0c03c0c11490b018505003980c2c26030700450565048500ea1031004201c1c1502c0c26002072200d07007140c0e239000c24840c0d040c0b00c80204551075042c10100b070504490394003040003414010319580c51100c4044c9000001c460000040d401603160902040000c0782000440b960b400b4950315030409494101d10101340901440c4411084038026102100107265000440b10304170f81184d40c038001c06001842c280944410140d038829007082c071f14110707124841514400142c00104075002c46549040c1c1c21001d100c0010f803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 192321187 1250 192319937 192319943
    0x20030c0d0e03010c0305040b04110d0512030601030c0c0203250b0c03040501031410290705060403080a150506070f0c06050304061b020a060e0316050606030d090e07030f090f 76
    0x1040e522040a0704007481084801c0c00c1314203080265050503128090f2000b8014001420784084c000656103030703100d0b1103810240d680d1003000c81d02d0f0b11b082d003c40742030590022500307540007916042c0c80c502c0b03907440340591700c0030550007401510101703100e00720046202619144c101510090000c002501e200c420f0010882d82d41c0080246480e0781c1048001010342d041000c000761000c40c2d440a000349075141c0c0541004030355130460301d80d00c1440d03046003c425485148060608107400440d8100034082c2c0402d038603105a2003551440c1d003c0d6543c01400049408414035800c408611001c28003003410148020400745001300040d103400c02d1150303207a100c0e801c2c49800003c0002c0001c4240300400815004200d031a07011031903028440c0c2d050070740096480710ac000e8083d09194480c90f0185141e6400e0003140c2c080c4491104000540c0024181780d913640c54240c035280c0c0280300b00905004042c2c850b1950300c06840390702070342c21180d444682c011000381103040419406c4035628038411000a00c820b0300a030003644 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 192322437 1250 192321187 192321197
    0x31f17010608010b04020703271205060a05090316030806150f0433181a040602100509060115020715090501180e0a0f020c060727050120030c0d 63
    0x4101909030f401c0d00c000d41d11541c05036005103e040d00103604040d1010030704004000050030040601301d0030744150b096034000040d03031b0580c140d213406110000c02e09030700c07801d00c2034424007550300e6050002e80d81e440348112180c4038030540107880700020700c42c152117508020004c0a403007100351041c480042c0d5900c520401c1041082c00a02080013040e029441c42c25029020704c01d01e1072118000403040042500001c071400c1102e02511082d00c500b002192002810210a035803440340c034480004c014551060007908058801c01a44003402081401203a01c1150b030308014028507403826144104114600d6030840650240e04408035a00d0300380b642092041c2000d42d42d032442549888005094203208039207049101d009880c0c140200d186846000c2c0d000f040c0060005986443c8088140080c0120200b40b54507000b07440c00d0005040c0c0c44045540c0480060900110208001503211201c3c0c1a40c80b0f024041035518445039a140b800010101d0408610000d40f40f030241c5800555080c4212134100a001c40c1c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 192323687 1250 192322437 192322439
    0x7030618021206010506030114280f050a08030409050601020f0d020c010905010c230304051c111206060603070e040507020d1e02062406040b030f070302040b031f170106 74
    0x40b40803a110481000d009002e08420750424010030710794401401200c900040d901c0f081d440e661650303a900c84032000040061441c10118407101c01d903004092145032602c035000000403999180c0540c3d010100c4401100452401e85802c1c1408040c250040c207140c150700a6059441c070002050003d921038841c290302810304035542c0c200240070200150032241c100101480303201c1c0011072400b10400004c0380c2c181400042550400410f2031480740e500900d400002c03100b04090b0000303c0d42d000304c055510400c1c500d407102c6420f00c1406091898112412465032090011402c207003409001907030000c0345850f0401c0c060410030082000d85405445001c0140d00c4074102c0d0084030362280c1801803400031040145d40519841200942d2003034054038210002c1d440c0b08084001403003060302d1a2a25001524454950fa0b4603001001d042c1c00c102c5014903242000e00019441c14800d00c00c4a0547d40782c4000a411501c0301810515154801100100e0311200e074440410900310704c1c0c024403400f80480b0000b00d021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 192324937 1250 192323687 192323689
    0x140a0b090106030e030a0c170c0c03010509030903030301090c260f0601050901090303050f0c1509160e04060b030a050f0c0109080a08040e090c04111207090308040504020a020703061802 81
    0xa040c0c1680300b18201442c090804021080c0030045466060b0540350061004420f0704010703544051403800700c451003000141100050300c010882c1401d00008400800450341e403003400310745922074041d4683c0c0c5908100010b10520410b54030004920b1414038249194200b0018040726035450451607921460300316007000715143c0b802160319440740080c6061f070b0414050000107007506031180801000e00001107000700002d0100c00a450b00c66689a048600e10703410714606203401503041d60302e80040d00450005a440803184a01581181d00c8031a410b490f503912903c50000400c3c460300c0a5501d8014015050049001000195490b010100c040c1541c01030f03090014180c110903510401c900d130403003c80c610104107030009540c2118900051340035a507490500305c44c24080c00500065000c0d150200d102c0c02c114080000e04012514000e60f03008030b49841d101030f00d52400c544030081440e00704010034005410907801a10406140c0c1c0112194180c0f40d6441030196042241800d4203101c441d01e0350780075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 192326187 1250 192324937 192324949
    0x2206172a18041e2001030b100915180603020d09170a09081b19080105040c030c0b030f0a0e0a082d030106080f1b1201091a0319020103140a0b 62
    0x110f043c030a039a40501c1800780d4608541e200c1c01103210701655502c0c1030145582c3d0107504280d601c4400105041c681040c81400901852540c0c022120041c2d07640c4c8140c020180102c2400c40c070040f1403011081c982d4074003039048020b5406181d00e070500c16210302c0000002a10a66010300c01503103081915114080d4140003003a9403119030210002e94000e9071042c02c040000e41d150450300b4001d441206c5c1c44407412407060450b41c46948a02540c1d840c200811040c440c0c1d0001c0d06056a101d6148240b0a40d601d1507030101c540000e946503180c0d10490743c0450003039150396000c0c18441c2c140000390361403200b1940344c0c0b1100b5001030420004912044410362504400c0030341c50003450303501e05001800c5504204c802041c4007001005e005284803c20b002c01c0116044162036210040040e5000d40c1d2100740e81920120001c1c20311460703011904024194a0300c1c855103640e801e031044080d0040c05407031000d030000100c0c1e0826101c2a030500d9a41d0f40440c10b11501003212134420b2021000c0862412040307014001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 192327437 1250 192326187 192326213
    0x21905040e25030804030f021c08030f07090311310b120115060302090310020c030a0207051f08040804090204031b09050f130201030b2206172a1804 65
    0x2000b81c008500a100180300e440580e010b4a4009012252000141c80802d081c0010304d404121a49901c0040400700301702c081c01144a103602511580c1d46444104054544012501009091401d0140b88590a0070030342811807007080140b110024400c10281e851391200d06d29840c48007040e1311008904100d0402080d034200e01180f28008010341d40381c00402215040c404d0007140d0805800040c0b416599134204224900d0000c0071204668460a00c0b0300f95a8aa201246402c05030158203000603d51501c581c80c8a254000e001015110301003442044440c1c0303400400c12110b02d207047c8804502d0391302e1440900080e511070084032403100c00c84000000c000740590322201e1864100380400198075684c03109540c002022030344807840981b4a00c010b070003034085481180d030043c402d401d507041100341540c40402004004102005840d44610850716650000c00b5141d10380c1c1d01500c44034862a00c0c07460408894450040d10140c0c001ca0000083c68080803e200c684041051409110a12050074140e070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 192328687 1250 192327437 192327493
    0x1090503030f030105100210051003060b0f0102031603051204030206040c08030903030412020d0501110306040b0604050f090603070807030813060c020109050f030a060e030c06010b0307050403021905040e 89
    0x18146400440c46030b48502c0305000322401515454440071025008003c00704101c0a0308100b0300c024940030107a6140081988425100d080c101906000203003003414800b0f00340700041c0d0180d031900e00c04001103d83d00801c1c100840c00c0203001c0103000845158001114007481c4213602804850625040c0312080c42d140d50403401458008220b00c1010780d500008580c2100d101075110f0710b00102c50300020384400b40d000c2002c0c0c80c40d4203110b404500650326000451183c1030072070f001c001e84100d0105005080c000c500440740c1121080c0074085a614081c3c1140c0d80c4800d000302101d03155a00e0380c0301e80e41052080c1d0300840704001c5c003058054202e210005140081c0803103103050147c09480d500001c0c4548079a200305070084502c05d101c07011a8a092003481c03186500240b0501c851b582000c40c013540c0c1e81c82411888480c1c01140004140745881d0390883e4051503c0d5610142414155020401150f50240c54040101c40d4524001801d46a81c00b4400042000c00f0141030f1080300f4541681c000c0c40d001c0108 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 192329937 1250 192328687 192328693
    0x1111c11030412020918011404030207090c05030406020d0b0d0602030402010e090f07030903110304081e03041a0f0d0e01020a030608060106140c0102090303040e01030312060e0103330b01090503 85
    0x50004221103201d141c83d81d40c040741c45c41000c0d10f4004007901031000505040e401e65081c41503054140c8011403085000328420340c221440c4503a1484200f049030300441c204030000301e0403c04200868919000340c106050000d00c0001d10001c460000740c12008c980d0400c40300e41e50080200f005544e0406c01207010f4100503100c85880c0e02d05000d82020980c402045c103c03e00d9511203005060510884680b410020301c0d8046075034540c0c0b60100c60784d407030000403004120700c00d0096040a00d80c10120546084072a030168000c2c2c4401d004459803003582000034500c00c031000a0100000304d00050266040203125240010303602d41c0c04610081c15078400390400643c650201c0010445640d10a81010278544441840c03030311241800f40c8907000e0f10405800c01d525100c0400c002c1201d4685205150403240300b81c40356108200000ca610054801d14403c0c40181510341d0010000300c8c40460071058406002e990348250703003008050b02d403040f80c841181d07044600e07a1802444c8255070801040343c0902811401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 192331187 1250 192329937 192329939
    0x31703060d0201030203270304030204050a06120f080903010c081f0b091207030b0106020706090f1512090606080115050d080a030b0303070c0e220b01030b0601111c110304 75
    0x10401d0705942200003410907600000041100c50ba80c0751611103c9101d28410101c0b2689801c01c2d50343e80c10600040c0e00c224580008600c4403669481200704a5581c0d22842900c02c02c9038032001e084040510301555071003010000c4080c0741d54280b04440040e503550312000b0700c2e82070940c00402c0c0d07070381c2c612020307048005000c1080c802110060b0558171201011070300d0345031961140c1d5016007803810640c0005c1030500e4103030012a1080d00441d00d802928810350b280782041d944c900d021040300c01244074100000400603a0507170700510500140012210307651010918039201e98501b0102e1ba540c0c1c2c0a01d4899541d80100c44502c240ca01c2001e004000031103420351010300c0390712114141c0c40354108c2e139400c0c95960a903072603ca031002d0081c0c45400c0c3e004940700725440e42e60072810308a007104884480a903599505140c0e4081079481c40c4c620030300d400042d855a076a0079544c0b01c48807913202501e11414003442040c18000341c50700700180e200305103280100189403585410301074041c6142c0309456450341c1040c40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 192332437 1250 192331187 192331189
    0x30708010515040302040203090309090f0f0406050c040513090302010605030102040b03190e100c02120703050307080709080a0c08150402131a0604060e03060606031e090115030c03170306 82
    0x110840c15903608541482c4507190008a462151040b680700075001400441045800103010021b400704202c2a10f609000b80d03509103818200d90401c036440300e00040004041408100745522954ec0704a105050a02e06a220000106200c600c0c9240303414590320744e00c0d170000b010307070a028000061009078020350030141413008081e418000240000c04180d0078150b503482c0f45e18160800782c1007203042c2c0203944c00c05c074589030104003a040020024002d4032506902c2103a00c49804e0803280b0702c40c0c15503185419915440e00c02c6401c09000350034801003150860022032914014051040c3e1113100b415030103001407800105504054001501c0c0341c00171029030400016840d045212441500d59020000d012207620748981c0912501911450f00a800402d010800395005407803174039400422001c0301c641d59508070400c8107521049810404001000d00440f0080b0365003910283c0017101c0354000b01c0c0440300c0054110081c0459807054402000703030350041041c000f91402c1001d044859880070380c40e51800f50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 192333687 1250 192332437 192332447
    0x2130b0306040c030c0929280c080703050c0115060216090603030516030c170901110d09172406130209011e0e190501110f0703121e0507060c050307 65
    0x3c400c880005003055947c240322107c0d5884807a00243c064403150312130b49210402c1c41161202181e600c520a0040741e1501b505004802400c4055400a0402c0c80c001140c3e9046410342c10421240f0b91964948c9403205030304040441441c080c202a50080c078427424a04101c03400103003c2d50051640a00d4000140082680401114a100a074100c904047c03415450202e070311008144010709003103000e010020103d09950010300740031400340c0c1c411028211100c40c00342c4428210051031701045040b031007040498041040c100301c041d0b000003a604005012103034000014010489100704200741c0d000c10055180082c00c0e98001034180504500300000e50b40040d040e2044030400d0136528401c4484150000e20420820120341000782100d0b801d06200d182c024003e00442c000c0b50f004c28801000c0da0b1070f0700c0c4000b408008541a0300000d000356490f5840e540f00306010070003031004121a88a0000103520b1445000491281c17580d28660341d48041d041040458a007540e141080180401c140401c0c2d035481 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 192334937 1250 192333687 192333689
    0x60e040c050d05100606050a1101052701020409090c0e090601030503031f030203010905060f060f030c040506030a08030103030e0102060a06031104361a0108070308030402030102130b0306040c030c09 87
    0x380e4441490b402c1a0400c58500511801c581d10340d03908101e400301d101d56002c00904425201074884103015072040d04901d0a80e4012610700700502c096260b254140a01d20400f02040102c0100043c541920346d9202001c0d43d40e07815080e00c000350741000070040203040c0b061256002e2a21700c00ba00e40f0b54156581c4d1030b107a00c0302511843d025401b04951401e40540d089194000f954020002c01c0300c000d0b00d01e07046845000444082c1560b000003000070307090341001004000140b1000700581103941071403040200908010303244582600c500c41801000500d00402035010b1030003512040706450641c4002031510308028800c06a0728141a0104001481c030b0a91095034901150b012400900349004600601c24601110720494010503640400340390150010841038041c01e0711043c1a96680c42104003600700388280845540305140c20404034540401035500540b00400140c070305101c410204500c4401a00303d100590380000522101e0718091003103417154241030405011520351110080d20440301 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 192336187 1250 192334937 192334939
    0x7080610030b010311190e0f180a0f0518060717040f1103030d020405150f160f0b1602010b0108103309030c0603020711060f0912010b04060e040c05 65
    0x8490960b0140c0c0c0c040d4006405030401040320076152044200e5102c0b400b20407118210128100030088045424541c400701c490004c003406054640c41241e0b10590340042c000c1c10000125a581204080c0405c076008190080c00c04a500f9510f80e0b4079205404d0408202a04840501100644103140c0c1008100042c0e070254000b0b00c850505410f0742000340c50210740d107000503418040041c7c05400c0c02c485d0343c0944207507623054619008030040c1110301207080c4201c0140c5c0d40000b2052040c140000b649100d007011300c0c1c2c460030141030300354501d503100c1280b00750560784c0301031020412082e0710300140e091140300c0c040038092074221078031305001540c00841c01c2c1a0040f0641c2407501c01224102c0d03155003001803480103070032014410369440340e0070013070502400740401c41e0003180c84500020700ca2f03c00c0c0261550141c10000e136501c109040070400590341d0040d8200c2e4411102440402000c0c0e070b58000313403101001c03003900214400340300b0400c101c100c0c0d41680049248100c40710521002c552840424000c1e150 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 192337437 1250 192336187 192336191
    0x30e06030c0c060f2e030b0709080a0305040914060d1e05070312080c04060210150302040203090c15120a09030201060e0103030519050a020c01140409140f0708061003 73
    0x986444001881c4a04440c0040d10f224080a126078403440741e055611a140740440c82108240020021aa036100c8a041c4803402c0340d601d40520200d48100e01d030542088050800c1100709964071845803c10500350f1058003c1030006c50100000351705030003014103c44030040c660007246080f2000404121350013001404a1005484000c0b41003080034114600b40c1d00b200c00c0b40c691958910381030704d0700104204c488000404d00030201e00e944200105071016280641c0240500c601d5501c3c00900a10010014507000000c0c00c50000c0035880b00d00c0114065000c03100039220000066090100d00501d200d041e205140040041001040803000100d03086031000b240490b12407841c3c1000c03400762005401065214001c0780c000010076420400400e9140d5440c9003160b070303101c3c1242d0195214010504508050307004030071400c0742c541c4502d400e00340e407590f0900f503541004e40b55100c1e4011124400d100c040c3c59100762061010820060a10a911002c58500144585024004211005400400320301455 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 192338687 1250 192337437 192337441
    0x71202030409020c010504120512041e020d030210050606090d02221b080906010608070e0d0c0b0403060b03030708070f0c0e15040f1a211e100603030e0603 68
    0x144240116002000d00c440b0641d02c030709450703803100e000b002c040d50119107090754210a500f03d203011741c0588049001040711200ca564070798480c140e200e0503800a00c0824102843e1240041e6102d00342112914000c0c3d0042c03000c0c81c104082203048610140c000341c400d450038010580340359148641100500d030b0640e910b200001d20382c0d045111003074650903c02c541900788540c0f000e01107429080d2407021340702583d80016907100c0c3c180360780d1506028084d410000e0005400264000e0190038054a100e02c09010194140e109488002581b6103d800090441e00005020402c0c070616000d658260402200511700d041d425680d843e40620803c0d100900038607410712070400740007007000b10030010b0504185041d4285081602c410340b04442c8011284102d00d1b24054110040c694410700c0350141074001d0350803e0000040400078201d03100c602c1c0c0c0b84041002602140700f00c109124240044414880c00d82000440301c0300c0c41e043c0081e0039208a80c15103042d10400100e82c0c458450011904103a40c901d550b070b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 192339937 1250 192338687 192338723
    0x60d0e030c1002030402131b050a0c0605010e19020408030d050405030712030c1b1101080604091704060807050c030d0216050a0c05040608010921030e1c120c0507 71
    0x540628101c420060254a10014032a42030350011072090744222004030760950880005012103109001a000c100d4609480c81c4805008a00521401450b07041c0210040008c1d40d032101921000d80000100407035001c1806002400c841c0d0f00c800060240c0f0081d410281481d2b64643c0d01d02a04240d6113030f681e100c1c40401c06004c400d004862489400030140441c000302c250740a4098885002200f0000d50f1003100c150700070507103006582c95180e2208030215040540c600448007144003811090713000da41d441e80d800000e00e0075491001603040000c0c0c0345d512913140c40c0001c0c2c034282004000c0c0c41400000c00c00f204814001104481071444614001600d981154001030410000107070020b00728454240b5078410b1280d102e2051045440403281400001e44800b01c450030791b14444e10080070114040501812450040008030000140c0d1030700182c000c0091141c280381008036209041c081c4503000d0b02c590300c154407880145416280900912021b42c40303aa0081207886445006040e451698003c0c0d00d603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 192341187 1250 192339937 192339943
    0xf0721061805071e0f0e04030e0109120308010e0a0204080a030c0510050f240d02060c011b0507030207080a081603030f110405040f05060a170708030f0306030f0c060d0e 74
    0x140d160000300312100d883d03c4003c81991004c210344040300902403044d0016040c0300a410090945448262080140c1c03119502a692190345c01c810605000b42c0d1800840d002d000000c503511018002e0b40e030101903526000e040c01000320003030580d400c60b6004010600000350005030101038980d042c0b922544003000e5003095424080b030500c80903440c6040c9400c2c03140d004d2000c1c4c0c215006059402d09400c081c5144840b180e10031440266440d0808400205040503150030710183c84001ca00d1030000c141c012900080480d414030000007407001c00c03804503001d018194104062805030419100516030429030384c44072990380c014022628113003103544212008242c0b00303801800501c1c00f00a03040c444036440c2500480c0c039402c140100f5016524014041d2151502801124012400a01a40c0e01607041c002d5914201410b03154440303040c481c0003400503440c1c03010401048203011710f00e400b0380c81c0e0904004140c180102c5031000c01c11035010940c1d000781c80c1e84000407075200e00311400c0e00041c0c480801400c41c1c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 192342437 1250 192341187 192341231
    0xf040f150515090906041104020d0b04090c06080c0a0210050c090a0602030a14090a09020906040b0a0801090e0d021b0a03170c0d05030103030905040504230f072106 72
    0x800a090105001d1940c108001881010b881240c501015503138a100d40303980d848040b18003400d0100c0b00d505030b88080c1019401401c601031001008505450040089000d0703440c000d10844440c40866400c0101c0e07940b00f1041d94200c10b070345d030b4000d03d44005040029a6001408481d940703281d6144089002c6800000881c3d145802c05884101e4103941e480c0f0285d101d0300201c44400101c0c68503406102c002c0250001c4a0044400400351103942c0d042002c0c0c0070081d0000c1542a07003041040001280201019000d49881841ea59400c46150304254144007a69405e044518280d40110148001e0b150045000740c400d0442c0d080d4020004060700c0051400ba809500c042c044032030810241085030b030328600a00c070143c0801c0440f1101580144101e0302c0e4442448003400250803400705000701d182c41d40000350824050365598052041240d6041500e0180801001117a1b01940c68512200c0052080c1c00c014184003540c40210102000b00441410324144000c00072540c50500300e41001101582c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 192343687 1250 192342437 192342473
    0x30803220f0b0402030606101b0f240c030203010303051e1c05180a02010207030f0606170102120a1802040504020a21050105060a060c03050901141606050604050f040f 73
    0x500004142c280011185410344082c2d0080c018200054481c1c241441000e02c21181940c2c0d00702c0ba0302a100e2882c141c00540ca0307007119450200b02040c0c0100300d10b01d807072841c2c002e084400000c5802014084404452020000c2402c0c14018001007021a40001c107032002c06840380c030b0b284120b240003520032103240300350010580560078070022108641e030705901c010701c50040240c4000103c944040030780e41c0c0d000c84110090040e80003080c10300000380f800c140d0b100558400c40c40030503415103800b0014408102c0b000c011031560343c04911000003001a020350794220404d4103080002180410a103401c1c01d840e081302034003486e01e41d4041011900d61520400042030341c002e04031541440a807600c0c0c141c10701d094050b2440c1d82018041401464000d40550440c4d00c1519071101d0f5030215601a152030b081815101c0c140400c018600c12034005200040c4404410808800030800c8180781020407500080c06240c007642c940001c0080105c0f00240940d00160000407203079a80c00e0700d00d880301062181d4814a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 192344937 1250 192343687 192343703
    0x60f0e060307150c0b1b0406050f0d05072d0e010c0314040308090a0b0a0c0b06010e0a030b07020d050304020f0f03070b04090213051e30060702010606050403080322 72
    0x40e0043c0380d40400c2da8401284a83d81d00e4000d612070008080900394140060300c08010100f00401045025500400b01024202481410000060312540440c0e100304c413041c0214001c901c03600d907420b10f0b10045403004190800e4140341c502c0080001002480e0366a00a410310010155074410b2500603443c82c00020380c0d401c05184c0d22038407442d240b0a2504140403440c00740a4604010440300703400d006440c1c410791259101c0149007103640f01c0044407070001c0c1505040c800d016030700c500d064954131803243c069401041101900d0a0070b600013894000141107034000c02c0014014400140e80744622280c4d4484100c030620320700070500c0f00181c03c1816992011441c08000278001940490703640107800742410a030500ea08155413141481038045c000c050f07540d072100d0001100c801600c0c014910300f90f0070450700e01400401c0c00704200c441080d2a280c2160032107031b005000b0818a55824014503014203002e2501c80c0c2418616568613103e40405041d0020303518029005000040546091180594200d86a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 192346187 1250 192344937 192344969
    0x1e1308031501030c170c0f040b0d1401050a0b1605070b16050c06090f040c14070803010801061406030103142118090114041d0d091503060f0e060307 65
    0x78122101c0144800240840c0c00c0c2501c44a1050207032864040c03007900c1181d00301320795450399040900f41d071080f4085030589078144000b040d00381c600c0018100011142d0740006002d1070b400c040918200c016400f0921070f03542c04109000a01c0640280c81e07051200346600505c462061070101d003041210381091050502c0030070440210103420032010512801842941d0b40030f03240d413045c00050b2190003e101e42082c0200080300203810180d000392075803107507860811040909458848400d42c0088401d545019011005100804082c0b003120020810b0204100b1200d500790049042030005101c00390800340c0812000c01c04003070502406100400007d44002a50041d00079030a01d030b08034003500019200b101e42001502c0c142008254160349030340c800070480300e00140402c00503140503502c8840d0440042040184008100922280c4180c2030310381d40c00d9281420582c2040000d03d41c1001c080600b010342c00c00a00540c0c42800341610300d14040d003000ea584a002003481e19149034040c00d4203240302d900d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 192347437 1250 192346187 192346201
    0x20406030b070915090f15021c170c0702100503070207050a0e0403030e0f0319021f0203010e090a080d050c091806011101060b03010b071e0606050f091e130803 70
    0x1540d03d040d80d582101c841c201c0d100c540411a03a00c030b9036002d01d40b5503480c241d400384501104041003a21078812441210351036461224000005518000b210001c64000c2080d04e01010100344400d6000409880c418106116038000a005510a071707008014890008003050044c1d2091084201902c0d001e820b02100e107036a543d081035491001c40c6d00707400080c90004442e8200301c0100d150030300340fa44080154200040c0440d1b20720100003c0300b140f025031145240c1e401761041c007404a042ca1500c41d100c016160740c9800d1000c00036803002000c00b2500c0d0005100080090f0309141951a00300c01c8800010705541e03014500503403032007410200c5903c4507518200580100c800c180103441f540c020790301d458800e00348120047c2a1001401021030f02c1c002400140040c95002c8098850b0343e01a0841000300004010342040c404c0f00164103070b0304070361501020b1185050034401d01c00d21101c2660704024500c1d015001940030314081000703140d50600440480c0311540c1880240344000c2d04030f880140c2d03d041c882 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 192348687 1250 192347437 192347447
    0x3080c0409140f0f040f03050c0106051c0303180b0109020d0207080705010b100e01170903040302190305060c09030c210717070b040b0a0503090111031f15020a020d020406030b07 78
    0x210107856030011000084d071500004038802e80910307403241055007000000d5078141c486030020440c07030720309640c1d40708000752655404010b03220069251a00c80001107182c1002400c0c1c80c044c2c140d0361041c03c600454100043c0c1010541411180034a07070040e2500c0201e40e25001134450740e24041e00742100480c0b200d0520070194000507000e00d00b150a56817203081c000301900c0010302c103145079012400303000c6121040d0344d0034003051740d100700e4130025a442c2540b2980010740c410450380005110700c0000006200f002002c210403038005450907034441c00c0002481c0013913507410072a4441401511680d1241d54100030626600a011188100f525050364880c031107600403c4640480000502c204000061042c00140484c0c00740c420700c800c400e140c10046801507031127510142c010304266617103419900c007105400b0081c40c000c03200f1504c000d0100101401c0c044007002560071028403403020650f901a6a6000110036600f40c6d4160740212203828503000003130040401d6440034104001d21340400c81c101d075100b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 192349937 1250 192348687 192348691
    0xc050a08030c13060801080d030e01060f030320060c1801020718020a03110906070b09190b06031605090a09060209150405030f03180105070501091a0105101403010303080c040914 78
    0x10100f60550a41d20031046608410a1080b025140c028200624000f441303a00070f00d0450b400c80b400890543d0b82c3e5034152000602681c821760000b00c9402401c00e00e050f0740b0464036116122070340207000c00d041030365001890344118090340504d032003010300604441c0d000f44070a02c0100704120b4400500c0034001c00040282d0300080003500021f00e890301401da1001c942d001d5803801d0310081c240a007003508655901c00280d1014050044911494120491114881f110881e85c58401e900034141410103000b41460000c0840d0300100070700040344240179540f2503c0c01c0340d83c8035644160100f80b0516a00301440280b0444107259000540341c2e42c035003080807914000b0411600140c08449600181a9980c0d40b6401641146c1c2c100d4540a914599258401c0c00070f440254001c000000303050040d5503802210140c01e00094100362a541c0040141e45098032000d01641001d01b89481c01014040e030010786840140402001e205c2540c001c21b001c200040c050b038014100c500c100300603006401100b0103841000b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 192351187 1250 192349937 192349957
    0xd0302010f0e070b12070912050a0201031802130f0609060e09060f0114010302070215130f0f030503091306030203030f07170a210e1605030d030203090307030c050a08030c 75
    0x34042c0105080d440010240100c5441d6911941814040002c1180b5220f020382400300f00b2610600120300e14900051004c409445600140713401d074420710026040c0d030641c000d006002250b010041c0050385031b01442d004168500140000d007000c10844130402050560441400c03d85401800f10b0b460350109860f0703000d140604211903690703880e80000f1602d030900740100f8680413255084031b0419402034000d462903d20050950740d0b21003002d611005036070400c40b41e28000013180742040120400c0a00c044015113840c41070300100a00391786500b5580d215040c500350003148004200c11045940b580300501950340142542d51350210201d522009420524040c2c40600d40600381c01d9082400300e003103c0b1030900720380311103c5004c1e02c0c038044c0a0313100100b0041c660040c1c94a412071754841c000c0c800da400d04a84404080600c81c2050141803802c1450fa5503c42410710410600002000c00010b82701280c0c2d051502058a0100b441c040f0f0400304101c000800118010080c418000c0340d441c00380c07081d080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 192352437 1250 192351187 192351191
    0x1805011a0d080f0906070611091e031504021306080d080a06050f041d190311010510050909010204090606080121030504050d081308160906030201020607120b0d0302010f 74
    0x1116000c02401d00d40d0701d41d009210080800a4100c0700d40d034007024010015009166a0800c03842c1d03110700007515864204d44040c0100064805540c1ca80351003541100315400d038051b00c0b46012540030075075440103040d0740c4e0404040c2100081c110340c1c1d08664900d10a9182e0003e00c42c01750f4a40400e80d55202c082c20400208613100d0010700751070003500c10720044400050100750300440c05010b100080c030300d20030200e04045282031280562001006250080c08444072040c132082624217009201c04615642c81895034140010321010711300c10380c0b122050380c07402c41e120507641d21402003850081c8034540c0005807140c1404d800044842d0440d01c894100d0b400b040702e9294258103522a10360a45400000401060050200740302908109074584403040c807a8000e05d107802d0400c0e0304180ca1034100e901030205680304180d10340c003021583c901c800062100b0201070203c0740c2594000b0f515a00d00809070b400304218003002c91108069070b00700700280c001c0500908800215810000d02900d1890242c510703d074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 192353687 1250 192352437 192352481
    0x18030703060926190807022104090c03050f0109020313050706020c1804030915020304050607080901270303080c09040c11071502060c2b050402030610050f1201180501 73
    0xf140d024211200000008200545410210415103541c80003408000440c401c00c0001000c040d120003216805280b0b1642d00c0351102d2030214100c060783c210125650070181020140207130014078196082c1503600d280382c007585981d07030382010340da5801025401a056206400001800c241c0100755840140800d079060110415070320f4034003104a01c01d0b54000c00051204600f002f103c001c070381f11400200141d1058a140c5540d0360000f880b035804c035030401c1c5da40c500002210b11040d030700f0072000c200d00030603201c1c800c1050300b03292800c84146940317110280074486e030303c00025040228003040b01e40194006204209084003440300400d10342d07125848400b54401c410b40801c08120120284900b61211342c0101911b81d40c008449071182c0004c0c88400f12802003610f040b01460f0000d10f0119941c2081da0b000415160600425150000141c000280000020700030310040e1540c0c240d403c00907009860810700c1050103850203004042d14002c03140408029043c0208014042d0084aa01685040d1266201c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 192354937 1250 192353687 192353753
    0x9290708090a030806011e0509041b05070803070306030c08030307030b09012106020c0f1b010504030807020f03070302031902090603070b0304020d060b10051b06060105180307030609 80
    0x803010981e1041c85960001c6640360000784035540c0183c0c45081031500100c0008240c0c080400580304941c03e601080707010071140d002e8201481022107240c4844200e050450000c400076001d4421100c019210160000000740240c0c041e030041c8008660140c810721129907240ca0540c0c40340c0003a102400081d0403c0000507161400004581c1603c41503a02e183c040c1041c840904004090020115078943d000e0002c6655458284041c0c1142d020400240c20314050042845c0801c100703440b4480e05120b0140428408a200241540c407025030685181c84601c00f1740d80020300d02100c660000b54980318620720300b54140800300306149241e109035903034004c41d11000c04254848040f40103411620405000003009403400c0140c9a2130180a04400900d0072030410201b04034080901301c03000484d40000d2400003d9403040316114202e081d003400350070b09013041e0000800328070403c0d060304aa05514060b051181e80c080c805c00000b1030784000200907250385841c1c164240c0484803c250f031482403070003041300380c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 192356187 1250 192354937 192354947
    0x60210060b03180c120601030b0907030b07030c0e10030c17011206090213090b01030209070e01141b010f0e0607020607052502060705060109060b0403050a02090a092907 74
    0x81c0d51445164504640d41d00081c1400481d5203404402288240740c40c0301c95545841210048008004025210035030460030180134805004e8030382d500c90752003001d0802c042007201121580064035860701248642c3c0c07030b80c0200c80410b0362000440d4030007400b01c203d4001d141c1540c4196409a4aa202c6008050047c1140301c5042800d1180c00c241014407040d01c40001c4c0c545c0d0154140c140300401d03859852080c0407085048402210f42140d007508a00e006009500e0a0581c0550207200c61a000d442c40000c000003c0c0403040c0000095000c00010a1854000c1d07404482d405000c017000008024400c03881003410050840400225414000c00021460007440030450510a064a0711030a2403d055603521261442000044402140450301170750b0050f51150008c01c1c02c90701a000609907541818009000c82d0300da80c0c0942a001000c00003000056008540005441c0d0111881c0d041daa4608078118050010f6080082210100302041c96001700350f50030b907501c0b483c0342c10003500301540c41e0103064030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 192357437 1250 192356187 192356189
    0x606090b0903030d09020402070b0702031206121c020708010c0302040504060b1204080904150303080411040c020d1103090904080c01050105060403030c021e06030a0903110a260f0703050406021006 86
    0x1801d904208864600058145c00c40a192071018000624000c0702e600e0f11080050f05940d0300c00180c00000d6034041c848101e85016401110450301c2200c0a2000c400c0ca03940e83c0c01030740f07a00303040040700410010054024800d010007410702000900903507142000003002075002c1d00813148650b10300700c00400d4180d1004252011001541210a05901c668540d65070a400240081d0b900030f8440302c1c080c00c250807180c1d0300340085100e034682444904152420100c1610840000d502036481c010a90382c0c01a070024601011f4003032420709489544040b01c0306811440760400c400e4201080c8418001040007860080054400700710081099036201c03004c0106a1059110103000102205001c50140c0f805281ca10b66088840d42004522001e200208890360011070360242d01543e03d19140382816000b0400300741c2c0c10035050140070303442d500e82e03220110701c01c003c032910f8040812001c41c17020440042048441d0703602c00080e01520f0b6406480e00600c07550107401403400500807001c04011400c0b050003040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 192358687 1250 192357437 192357439
    0xf06120b010f080316050109211b03050316020c0d0b040209010f0b040510051207030b040f0e0607030203090f0313063b0604050405090105040c050108090307060b0111100606090b09 79
    0x6141107917000072002c5c2800010000d41e0380c0d55079850b5100c00500c210101901c000300c0d40e0010541d00001020151020205084004c603e110070101c20300084e610900704c0754000340c40c2d0a04401d07000000d50491501745030300082c3c1c3c1c000122041c1001408043d05000344140d10032519010107a880c0e04280c007030807849100d42083d04101b80814480c510f04180b49480303c080e94a070aa00306400e8900c060f495040036105803011a80d150404007081c1410300a030f100e50000004103100012142d503440e035882d0700003404101011f0307001c40402e4507104284201c1c078620035070500310381c4c548a50089041040315a44101000705400b40346a5400400c01c1e4800c20000b05062030000352154480510340e40d91104848242d4440410400131030340d07680c0c44c031500f0302901e00203000160915051804942ea86031030b41125050060007070800403440c000100729004540d003e400450070b411860010785115907c90f6444829020310307100400d40614560100007120f5440d96818010781d65202c21000621a2120311 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 192359937 1250 192358687 192358693
    0x40f06052107030b0406080705090a050622051611060a2403200906060304110607080f03040c06050c03041e030c060801290d050403030f06120b010f08 66
    0x20041140680040e1000c180400c0c010800000100040d0300c41e00000c0320b586010954424142d03c29003018410100a4001c04005201040c28000051503040d0024207441d0003035142c900065a9498207000c040500000c0ba110902280c29810b405010b8082158404105034600b00c00740c1c7c1351445203411043d5096517802a1416403030b0100d001000e0a9030070144403001040320001e240001091040e00c0041d40a5204030001071812500e00c00078091103021144103940c4030050201d80d90b41d000840303400940c81014240ca46200d4404036203d03016481307001e8140000840c01030050040b020007544624031645149407055100c180c01d490502030340504601c0d81e40184418414003940c0d108500c3c1d01071070135032803d403060307680e50380c03200e0510054220b01e00090515004209480e45038601d121802c0c000010303140c17241c0300550554601d000d85044103001a46440100703080c94025446150b00b413810b80c03000c1c060903403180f0310b5117101030781300100302d03807100c0d88000019541070f8558000081e17503560005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 192361187 1250 192359937 192359939
    0xa050603040f03020109050715110601080c1002010605190801050604050118020a020703050304090606080c0c0a03050702010e12010605010207090b0a12031209060c03060b0a02120a0e0301151406040f 87
    0x2c00d8940030742100c04506641d030f120f21041c04100d0400402c001004805258005000c240500a2035100c1c408140c2d082e0340c0c403080040c421180003066403030190788140d0311120b46c1c40c51484120301600702540081e8000c490501038002c1c1148641000058500c3c01c002400507454200a10080754001d10a40c0c81860492003200007000301d80d0010450709046104071101d05480e83c070b52905582c0654482c0021079514881004846d40145800364000d601e4905581016864610941c42d02ea42000040030010000307081011a03005510107030082c88040d1002d900040824407042c0205894041c05016200c1c81c00300103032244660041441c401c8003c3d240035803075490300c9003401c2101d19401046044c80b88216411441840500c2450b104502a01d408520640800405804c403441c1d90080e000c05d5008004806030550001840e90303201500b400107996610300d40804403422840b42d00d01070350550804000540c40500d50f510a020380b400c584100d0641551401080082d00c02e62141c0040c0c0611510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 192362437 1250 192361187 192361193
    0x6060b1819140f03010f0b040605101707090b0705010e06151c03020a020904030f0f08011d0c0c0703050a06110c12070317040302060412050a020c150d06030506070e0a05060304 77
    0x700b04460000040d009104002c0d0100000b825201c2104417040e020340d0f1008888003610703181c021080100317402c2e1982081d40c0340500005114884041b05d000e02d448100700807503034040c4200d44540041c400c240b001a110343d1146052406481c03551206ca4082c0b1604ac086900c00c040c4021400d200400106102c24990070704000208070206004260b0550081072820700141c0c480d680d00741d200e24400c0d03580b805900d08100c0090400011904ed940c10000c40000521003852591031449003d80490380404256946804500c220300c20621110468003130100300100300080000c02101312480750301d061110182c0c240b0f8400c182c0c001c4403480e008590200504121074450301005262035400f0b480c00242c40b02da110401a0440300564007203005a0041c010801072200008081c0c0c9000380500d841454240e04090080d03035880d40c1a505445100c2d8981001e54102c008d4080341d01c0b0f0100c03200c091020b60307034a0070709a80301c0d4021100701011034000b0b5030f0405149031200b014001e8500c010035250664403251 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 192363687 1250 192362437 192362459
    0x905040e01020c06040305040f060e15090411040b07031b0c0e040609061404110405040309091d0d0e0909010e060a050a020702040608030c0d030b0d0b0603030706060b1819 75
    0x1034115410303550820881281c407100303102541c4101d001e902c80581d19807404000d444000445e900180402502c2e00b038180155640c0e110b240340041868034005d49540300040040d004105050500103401d000150000707100315250040e00c0014066180c058403c807454020b0000c2d40c12000c4000d051300003007941403040004100030240c006028440018500b00142c1d2007000300c911001c0c51100c0ca680c4281000104040700900c2d07c40307540b0588050240d410241c0e0003404506031070244184443d100c0b019414010041c801c0c0e0484004164102c55560481d10b0025002d10340441a90380100444800a1300b14107050080c03640305c106810080920760b41c0c684802c0001d00015101c0210580c0800041000da59540581c4015100d44005159145862800c5c285405800c00003601450708003014603015a8540000482090b0004c503250b096659036400681184a001c40040c4503910b42600418006800000740030003c00c030900500003482203070b0402150b984410840800401c0804041c00f00c01007030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 192364937 1250 192363687 192363701
    0xe06010c0c21171201090209010e0612010609050619030b150a080603010507030e0304051309050706090305120c100c14071a0a020702030715050910050706050a0606090504 75
    0x12504000d800d9100d0b280c0700c08000c0c04056003149214210000014882010040c50344146005101450404c801d1240000c0d1101485800103860340800c2e0344035664020840c1074000c200080c503103507071020442c00f14400c1032020f00500c00001c108c91404559800d10500300c40c0c075600720306480b00e481781800408902514101081c00e8124010200d40c80f507158012001e072100120b1074841e40c51a1034148145400c4a0005051004050500080201c2080088103e40584106403403100308102e0110044010f050660801801c41c03040060002e00c55521000c024150784c8600c0603074030b99403100d00d9441482c0c05100306666158112040d04400c2805941c0040581d03050788c14000e4024080e10b1841c0c615400400c81611024058903450003580d040d980c2d07165200d17100c8181141040344580100740c3d56070039800741600ca04c10f1640300c81169402181a40c5519800602d0a5004008060020095000307081c0c121181800c05021401203543c0c2d004a01c140d40340c503a00c29585914040800001e0814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 192366187 1250 192364937 192364943
    0x1020106050607081e03180c03070510052521050918090703021002070602010608070e06010513030b18010f09020f0d0602040306060b03090f03030603060606180d03020c0a0602070e06010c 82
    0x3072104245c40c803685090246204401c00549507480358504142281410400c147d0b0301d201e1340120030706100c0c40e52074420f1105034100c80c0ca0116103868940f4030a46a03c031050b6011480480200120b00410410306032080980c8505801c044c054040048243d81d14010300c5040c551100c0442021440d5030b0541c0340312540083c048080740c85207035807a00813544058a0440b0500181c01c25101030005d507809010b040c1c01000c0c0c2c075005110741c0d880c20032000350300040070302024104240055540960a50a0290340c003441d0051100049418801568610201d00801e4428294244442e000300154540310f0741103125000b0b407100200c40c1c021420058041420701d011185a5424080800884c0345441074a01a109a004103950ba041015865141092915140c54598010800c20005450225945400402c00d0700d28989540c00d00300d40f0f0300100210b01d0815048080410321000785507000451001c0801c06036000c10143d510b96030100d880c0c1d01503004400d5a1440c50001c41c85175440380c9001144140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 192367437 1250 192366187 192366217
    0xf0d09090b0607022206050f0d032102120411010804050c01050d090c091508160e04030c0602160c0f0806040803042a0305060f01080604030c260304110102010605060708 74
    0x140c039134002503103610949050f205501c441c0d82200c601034140e00c100000b8100c1180c10484503400600010000000e201b001010465074500356510883c040700c05205e9850705050030742d1039600640c09800100811074080c0c0e040e89511b14034000f2035004114803070203290844042c00a051129005427680d0b0b0106180154075950f84007007001045841e4400c5000d44651080030880c44032010350340503600195000b001e00754000c1d9030412800c40c42840d50404582a46c014008076a83d00c1c1016201001207400c080c10507400020050015880721459901061190ba42003c402c0d4644c01c8501410b40140180300303840e8480381c0420007080a032070156901500c10705224081004221f40f413032543c50000d480100840440f50244200202070040c0c552250551813210aa585001c080b00e6440d00c001d81301505010032081c0301c800b07004080d40c07051500f44000a2070020820810003241040e88110350959174204440e0280b0b141e5071060051000321000200303950306001240e1030701100e5a000d2907941e07204807 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 192368687 1250 192367437 192367447
    0x1006051f050f0708040e06030c01120c020c09090c120d0e0114041d0a0c0206070e1c080f0403020a050604030c05130b0324150619090506030907030201020f0d09090b06 73
    0x2d844402040f02500c00e00366162200e01d001003a05503210094002171080d0801980811a6644404072074406100a9804191810f0b441d0059081a07400940d40303070061802c0c42000030310031300014519080c2c078095502c80c50f0801d04a0a5903140d0300c50131048000a11800d0143c2050340c40b940da00c2c1140003081826a00e005e40d1007818103140c1c101c0552030b50018810400b0845003180b6803040e00c440507440d0016110b1440c0024000303002d545294070300c600c80e021702c00001e4104103511145520060f48444216030310048a010b1140642051004900c504080a00414141010b03405d44040326405400500c01e00d09000030010301c045980c03906000c0c82c0c0d403010014890360b070410100a5840394000c802d61a075054150448403980020050014400050480c1071291180d1040b55244910050340200c0c2d550900d00c1200c1400b0941d120f25404172020043c42811900420500b0499200340c0072203002c0031414041c2600d0742002d6082c0c0011441420042042d0440c1c4e40061003101002080180340c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 192369937 1250 192368687 192368707
    0x6050402160308070908030702131b0206061201112b050f011d070e042301030506070305090f1f06030203011406040f0b1f030902030601060f021006051f05 68
    0xd801904050394025400c00c291014150040c40c074503000b284c20b1500700d0049040c070209a589109005000f80101d840701001400b42055903c541010342c8401000f404041308081c00941e1501c054030f840d0700c502480d460110300403105110f03030192005182101030800002d40c1030a42c82400d40c03030712440004500c6e80f9114200c501c5104842c442c0381051150f85965041400f1f44c100507400104640c2c45003503a00c10320040e103130001d035200100c43d01124045144400f03070240324403010900c07445000d12420080040100040130446502c5041c044d5410401c0b2b565001526990b40e81c42817548650340c021011440d44040080035a038400104a50b0104015590368042400c41c2d021031940d00384110f00790300340025450180100b510880000c1c01c280040204600014030694100c02c0499844032000c3c611800e80f4000d4014116454000f030a0324200c0da5990303009001d00d0017241e1120018052196260584980d84c8640c0c002d40c1c2e000744c900c5805c5850001c1c880da6019029512000303100c000e02c101801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 192371187 1250 192369937 192369941
    0x21227060a050106090b1204020405041113090501110412030c05071701020c0f0705030c0d15020a0f1b03050306100909060b1b07061e21090b090601051012060504 71
    0x58030904a001410b5032500030000c0c102030170307600701d000031032400c1101c040c110500340001a0099012203000030303035854510b44090781c0c0c00390007001c5070007030700c0300c20500703107044066204449450156000f400024607030f030050800703803041c0c0c0220310007150080d0201007c81c0c89140380603641d9116608845040d6201e4024403013810344c9000c1000e0a030f400141e00e40e030201c018440c20764503881c96030003030440a04110010b070301c3d4251054010700034080048040c040c041820f20307405c0d000d45104d20442d40c8885041d8001c001d0350000003440085422049186802d082031184403085640540d511811a02c4281c04c02c228085401034180400c2461140404d8901c2244580f00080c0b2010000700e070b460040500541542c0b40303801c26a03076641c200c1c441c100b0405402200012206181a1003810b01c50034015081c2c4032083c4030028a42c841d0341e40e903a0740040802d00c2c0d0081103901e005902da04103aa454960842e6134103000d00075550025446442010424028404400420411100800c140f501d0700f021400b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 192372437 1250 192371187 192371191
    0x3011a0903010609050105130912031806090b04021908030313060e12030105130218040b012a0c050f1f031113060f0516030e060d051305010c020102122706 68
    0x284c116944d05c0100542c3ca815000d907054030b240c2c0301e401e0000e5100d40d141d00d07060110a204010a140e160380045080380c103c80c48070000568001c0c030070050a0340138240303541c048104490807406141c0340400100040b2001c0700c0081165200382c0154074554504800d081040c0051070211001038441802c558840c2040c0401820142e01012050310780d03242104022104402030045d0080030310400065031503c030110072084a0b02015100800d1a4080070012a00500c003002c401c41e050b44064840c00102c0e000801d40d01005011705c0074540d0841d12842008200a1002061070744807000740e40c403103040e03442158140070b070710111b0800041940a481c580340b103a5105444403100ba102c124824040e05403c41c5042e00720003e00c1c0b410b207003044a032a440c215480c50503d0050140000c0320891007040c2d40b1201200d0ac001e540420038811414201c0c4034803041c84003c1c274219525400c01100d000c905105100b42e804980c013449188005440380364003542480745055041c80c00c1c02e071030060071072902400c100d00c038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 192373687 1250 192372437 192372449
    0x6090604090f0c031a010804140a12050702010f1b030e040f02070516150206040b040c0b1803150723070203060c0a020708030a08010605180411070506011a03011a09030106 75
    0x4103503e030210390300804440d1aa103c1013001038005002203c00e9030b00c4803105500503031111044c0344101b00c09603940c0c0390802c00d003401481100e07400740942409900c5809454003034800c0c0ca03042543d05101d0070580b05000c0000700c6080d884c00c21003116003c00c0c400d0b40c40c4c05080e800a40b000840710900c07564603069a102c241c064a845d48180c040402020000300702c0001444054444002d5500020000b503c030b200c058400b40180d0404801f240901c191000d070300b03004040223405c05a60710a41c01d003200303820300384400c80340c4603000d40840c076005107241c0b060f5248280101d540d4204190512428a00301c0c07242d2520450103c2c07001c2c005500180c500300865401030200d9004c4989400302114020315001d000c1d040002c543c1c00030300440150300c0d003200269040d2103c40c03c1c5503403103414200b403400d0350082c2c101d41907501030305210301c1c0b01024600c4030080050b50301960030340c0d0040c1c3e201c042130000c0140c54400820080b204000402c92201e00c444001441c80a151204d850041284002400c0d0f4266800903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 192374937 1250 192373687 192373691
    0xe1e1003060e01080d09050402030c07030c080909011206140603060c0a020c0a0e0105030f0712080c150109020c0c01210b2101140604050621070302030a060615020304031106090604090f 81
    0x841581508101c031b0304000c10341204d0961030b52404100c01100703030165000040602c0340c054070b040c04212002003540d0081c02d014190444035a564811800c0e00c0c02409425036038589406c01c55800c0a845d101003074031890014004000315120300741e000c2d48a0703000c0070620086004034005544250b54a140d902c1c01050124003001c04d41d41064101802c1400620801049512034402004a400ca000900c4411a000041c227034031443e06a0326603051213200301314511112001c02c00400c400c80e446c0e001c1d1500520700c50448000260040055030f031070a10400340242c1f480e420505801070074464000400c00c0401403c8880b41c42220301619032910103901083e035959442d0400d4442e041181e104c070660115080b03e080c405402c1c41c00210b50301c1c1003005050020403a042443c15a1000108086001107034040d080b1580404281407150060545028000c1e032843c0541000341c00900c00803e44094a030001c1402c005140d0240030088160b008080850708104240000201950581700b1140c07100d110001c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 192376187 1250 192374937 192374953
    0x807120f0903020f03180f0f03030c160801111902031605030901180302281e031b0302030304090e0703060606021c03050907140f100c030e1e1003060e0108 68
    0x2020382411214151080240d109201d11860310286d030740322244860050341d043e0305070143d0201040c0300c0040305512503094440015880c0d025900092070f14002030300240c0c042610380d260350500303090301c001440607c165041400b60030140b0150200041100b212401103070314080c0408550b440305941e4075400d64480e08045071030350103960007007136403c0207114401303503030700d0481c10b56000484999005040041911802003418030011851008101605449081011103660b001c148a16009140400c90340002080c0381040c1c0000008403260550354000c000e0340c00c0c18100040040140102c500b0000e091007100d00000200d00c192180c140a44a598050160b50b00c0d42c2000c1c050160368400317100109442c103410018041c601181480640d042a8901001d18007604001400b2008450030590f20099a00300562003580142001a0591194452081c0442080d040200291824001c203459200300c501c1d203849440d00c8070300394400c281581000100c0544458079141c200100344c1141c00c0c198007000c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 192377437 1250 192376187 192376193
    0xe1005040c090e0f310501150504110306030613050c060a03020d2901120f050a0213080a08030103060e0f010504080306030106091829070206010501120507020703030807120f09 77
    0x12883d0f5210031980c44480301814000194941000d03403098554840e1021450041d04a007034094040920303070442c00a02c44200c03400100e440c21801e40c41080d102d107151404004c2c1c1c2051407025603100b4540103000c1d09060307540c441c0c0e0324806030700e0050407540c500039a2031420841d512400640b034411a565801a100c0c0318860302c1204542080391b1110700300c00043c0400c81c0c040d41c01d505400d803580081c40c040340724880820381c0401810a8160b0410442e003020100007100e0001d502504260180b0743c0c0c400d208550b0b5544840d200c402c00d280140203c00200018404180503820480e0483c0c03a440c1100c0e81e1540c82c800c4282160010b40e4121200c281c000240100c500c1e0901440002d02005801045042c0298041d00c01c054032002d8003c1480c0480c0c144e4074a04140c001c0761341c031036690700d03450505170b4500b03224000d4651000b40945404520005840d0000c02018498203120341d40b00d8005000e10350039070b1026200c28800404030010000c5007a450034500c07109004800f1400340341d45011400f40030785d10b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 192378687 1250 192377437 192377459
    0xa03021801030e0a0210020114010305010c0206060a0b031303090b0a08090601080327010212070c08010507030209060702011101020d020d0614030307122102071b090606090e1005040c09 81
    0x119450415081034848000307803c3c0411555032581d0f04850120131840700c3c91040c3d0142c120b201c800c450782200c0d08000810300c001034110180810b5140e094516680c1c541c02040800d400d580a01001c035a070610000d21501e0f141206c143c03002d4040d00300079201950700d0311299120b9002c004038000044400e01480b40048041041502601a50b000703581441c424607070b4081848031510301d50715462503100d0101050390007441207039040307503e070b000e825601c40d2075061945200b101032040510943c80c0030001081f051280c4251100c50500170601c40ca4051507400448021480711050001f41d54200300d01c107400412840206070b510104100452000c2c541644c01100341c5040c00c85a0098004104140000381001e0410420149506000c55000645801c1d0207207104145003981c601c0d8070000f0306400744502024800b120155205440940c0e584810740c510a5070402c0c4541c4000c5a40070b002400032261003864181d00429514a0013a100d41d00c0000806840f4900a0040451080c2c4814803050b0200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 192379937 1250 192378687 192378727
    0x70b0c0c07080d020c09060a0e010b0a0e0616020d032001090c080606011b0c03050303011805070e0603071b02041104051801030b010b0d150b0c07060c020d0f0510020a0302 75
    0x3100151643c243c066101170346a00040f05950b124013034080c002016039031440c42030740c042c0603280c1c07841c10250303140d04004a00380c0c0b00381030b418041802800b0064491030400100c0340800c91550148a1005040d4288626015a01c1040702403012004204540c80095070341340002c8407540001044840356410b114062403055041012144c00c41010040c1c3d46e40c02c50300516001d158400c0c9031041707040a0502c1501405103401c01480c1e4040000001200a400a46001600064541000107485113001951003105582420b43c1024051001841880c05181d0702e240e01008124481e4070301c9511341c0094111590b10000384050180807801b840343e400d00740700c00c400311074a100c0681c0302075040d07494500c9020014410034003c042c000440a00c07007101500180440d1641070344803000c49884106851888e04000900303841e41c400c8840000c0d51520452882c01e41ca900508021800100c0303031248040744510b008144c82d103208880c0c901e180c25415200811521106590040e1a03000040d4880700301510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 192381187 1250 192379937 192379949
    0x9030a030f0506090c07020109080d090e06060a0c031b021807030c170a0b1f03050103030216060e060c070b03070906090e0f13030e030703140d0f090603090206070b0c0c07 75
    0x40c000402040b034941e200b126401c00c100c460f540c1d0306d80c001480125440e401e19041b4500c10f0003040c001c0043c640e045800807094540022081e40c8a90b1000706000301400360401c00d800142e00d00e00c9400109000f80c001c4038035172816108490700c4c064a41c002c0b987c00450300b05040134510400741044101a130521031058120b407980340080d040300000b013581000140140052000540e82c42c0e41c40060707945c0034254161841c0c401080c050428201c00c01034010882407000342c025000d0031401400c0d0700c02255081003914001d40303d45802101200c1445903680040c43c1040701c034480c004e4049009041c440c06588540d140b596010640350500e0710082c05294503038403846031801100300b03000449224055441d4414044100142400100e050407103401d41800741868260003543d60110034000160354440a1200c0c55085603980344510000b11440301e406000100000c0d0100d00c2070000d14800c1d0004201c480c001003013213060080503290b41400030010740d90700110150000301320034a40030134450303c001052 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 192382437 1250 192381187 192381191
    0x1d030d0c080106050403110102030702091e0c031314160807171609150f08150c120103080c030f120109140702030d020705010e120a1d1003022109030a030f 68
    0x458000e02030564082c90200800101201d61605008e910804c1aa101980c000742505c903907003441c03080d5180c800309000d03034415030769120b130000341d8031084002c1124002c4a0711411f400c042102500d41e842106850304204d4a2401400944031407002c0000294018200c400042d1400702d10b8a8200348c0740114603940341000750400c2d03107040c601d213001031105000c4500c13084011a55007000344070300029140c16000000501c89822020840c0c01c800940028110800400b000340ca845810544001d80502101031042c030084038010310025000c540544401c0c102213046a0030526059603268032078010442d50744100f41000d00410800c1d2250141030481c2d5001c91006145041c41c1200a4a91080e0a9140359058001a45d501042400d501414403494060700b5036101d4200c03010300001d1607000703282880008a14074000442c02c00080891064500024000143c09000940640180d0003402600302540c0078284e00481a9160303011461242d0124000f0b180d0300c0c003a040d405403c642c0085050a82d1034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 192383687 1250 192382437 192382439
    0x7080709030803060102010219020f070e0912071a011e050d051005220f020a0b0f03071b21030606020705030a020f061e040e060d02011d041d030d0c0801 67
    0xa40012444050742d400000340782d541c0d0745000c0180c2c00381c031440a0900c0816129020407800d00c7c0d002c50a030451040c4041681e001c00d0795210b018401c071005036070310b0110342c0140b91020000c5403071034000c0c00c8142c41490324030364445180803820010b8100b640130b1070445041c910142c0f00740b00521a100007401c0100d0f008104600940c0720796039580003440d2141191551030011070050352449010710680e8014204c50304080c1150710702094155038104c401c030b0084004450119141c0e02041c00d070b03002040f05145044c19949e841100300c07806001c1c3c0d036810b00012130002c400f01c0407400d66018200c035101500c00320310207401004401011100350b60711080c00c6400c180f0f41800f0307598012030990100e9070111440800c98040500240040c0f00301384844807204141944070070100c1c144000703441201c0440707a810100d6a144020b01c401e0035011000240000c2d0031000d4401624501a010041c40a0140001035030050086465240c8800345100d80e070290300c0030440900040190280700441d82e40b80ca8602459 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 192384937 1250 192383687 192383701
    0x60e061f0c0203030f180a050a15051c06060302030402130213120c0914010314030304020d0602070c0e0114030708070b09060c030f0f07021003060605040506130503150f0708 76
    0x9000c040d1008003007042018000c0c0079581c00f002502c0902c042096190342d00c0700d9032241a60007a40e04071182d402070030001400505803034501000f804030b41c0e4980602101d41001d540c2100d19601c001101c2002c003580020502e228400d621501e4007a02d11034500581d41e09140c01085074100003440e12410007401042a0320204004c05500011a260440d03800030b0b607084d40c45c0c14000d441d26904001d01c8a0b1130581c641842c07031103210300d0a040f6402603e00001820004490b0350720ba05c030403100a5046402d0300d018800003401d95004120f030314002c0404180e0181c0b83c04d800c510214007039010708044920204100d549280c04c0c0000e10040c41a00f00a0420038075143c0701481c0c900507172400500c942030207d0440000c20090007110b041c2466411141e0b615454145001c2154001010076400703880100f425603106400ba2140c8400d40e4080d03100c0c0e50606141c1010400e683e84100000b041081c00c0100009203510704010206451b0710000302d4202901c3c140c2900d4980703130001000c0d1410001d4007800c0c0056 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 192386187 1250 192384937 192384979
    0x315022205100e03010b1207060f030c050a0804020303090d050304062607050f0712050406110d0801031407030f0f051212040b06040e0303070804050c010201200a030b060409060e06 79
    0xb21440a081c80d1450742009070000e4014580c0c0d04113650007502c4400103ca00b08404a215000da403078944541d651660400411800c03900001d000c0b1002c81c0e004c01c6800a06405511025070007440282100e103084c0c01900850000f04028104546036400424180b110680105105600d42d40201441700084070040020400340000f400070420b20400040003001405014100d90080307400481701b07a040c80071f070100200745501c40d110b4400000c402c00d030410030b45040415610810410b036601c02e025a425602c80d0784213045403008135802c5200f0002c0c0000029007018440d003410b40205c0c801440b04215060807400c2150300b0300d8040e04c5504c20484294545100f00060781c029400022070b074256a907240c0403c00400301e444180319203100c080b00f0404600e03480350f41540b04601c95815142e8082070030005a0a8800c81c078170151042d85183d89000c100c00d10725000d0481c0030220700c0d000c11603580d51808100c80354010342101d41d4680e00c2d4041030240151a5101c160045400d81e07031b20b50100b00d6000701c1c1031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 192387437 1250 192386187 192386209
    0x2060109020702180405030c0d03090b070f050c120d06060c08040b18060309161703040506220b04080d020c06030a02130302101223040b0901060315022205 68
    0x1600c00d9011a542041d900c848900c800202c0810036a8459405c0c2410041d40c0c94210a50003031562051031400d808240c070038080c2c0010b0380e5002604082d2622690000c1e41c80da501d0f80820000c1143c00e010075003000008000c00c504045c0312609442e95003121400076016944140c2080c014003d440c0c9050700045c2210341242c040b03880030002e4580710251800f1103000c0b113204141890744280003106008032014045054100c0f0300d920042029019612000e13928000060300300410642c1081c002040300741843c000400ca5111003d0f8030080d6180b481c000381182c46156005111640c0c1c01003002d001c1600f040080c100342c0307046800203140e4000c018000600d1840020a1a6500307900480c4100652522a50140c0550303801401150490190000105000c420b079050508081c2410f82c22030f071425800d10b0250701c400c3c18030210075140e0741301d840d07088230703030320081e0940c1c102d503695003800000f003071030080e0032846080000d8025aa4440701d00c0e60b1030700141c0e00040b113818184120020442540c648d50454 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 192388687 1250 192387437 192387449
    0x12903070203040e0403120c031d0705090a020c010b040603050606091506090d14070303030e0d080408031f0305060405011b03020c100e010609050a0c0f050708032a07051b0f01020601 80
    0x64136598851404403000e505c485040d945050800f8410100349400d0340110741041994004e001c6034580c2600d82664811141c80b035540c10003200e001064250342c0e00e4000340481c045000010412950742c101283c2140c40d16841070b54079411160a20170b9a1a2081c89036070022486000b800044010000048082c4280e440c0140b042110303030050402c0000b521031500384c038164242a00c030035554034280580a0045201101b002e030088010523030500307000307849960040760454074160a42e5201615850001c4100307a2070f01071840406000000100c04100d460300c00d034898000070583c03505190102034501c9601340c0c06000c1c18014003c00301840e41c0080d2070501c0e07820300403003c50003103045c0d02c500b801014542c0200a00c0c6081c01e0822141b41e50366080100580740a994002c10f11800207801c031068055404000c1007a0170400201c1c1c101c0b9841003000204403103007850261040440b030380044c0755a010300c0c002c85140e00301001c0e10f00c5030440c1c50582d0080c0202035a25120f01206400000c0d21480c0c140a1a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 192389937 1250 192388687 192388709
    0x2108040b071b060f050109060602070f120206073017040b041106160b01060903020d1401021611040e160306110c07061706010302090906040509100501290307020304 72
    0x4420307100b40d00c00a1109802000030040300b1808070622001e8a024082c0110a6091890000750710303100040303200850300010352415005040c06502140ca103064032050303a00107000d01c080c41c0820a5110349102180700c0788000040c1040001c140c502d13400b11480008180800040f000701604010242c00d075000b607210120001c280c0c2c86161501d6048070f4250b0309504000c001c1362602c1d1481d0540031002c441805400701039070684c0e854004407450904c0d400002c4d0012400e80c00f4900094041d1005840902460000341c10941500e142d601c1e0148000025210480d4410340b1303080d641400d200711022440f08401a000142c0508003076103660005200c01070115a860503400904001c0d01c3c143d0344003400c2c000c2a80c08040e51050000c00c00c1001a2650398590382041c0410060340c001c1c4202c406540000c0d100700d2403660340004001c02000010110342c6207000d944440e0400a1452107028043c04c6001e80340903400c990021103803403a940340004251110820000c1c081c0c2e0702d03000010744084030300304014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 192391187 1250 192389937 192389957
    0x903110604060c032706170115140a050c060a02070b0604111602180702061f12020913020d080a0201060b03040b010e0408040b0c0615010c020f0112182108040b07 71
    0x882e4205104005207070032000103e80c0c0410a164000c040c0000b10001141f201c00036629181c2810001581110070804100a050502407507103100000e844441c2850a12a0401059500b03040c10448100c030315424183e40081c10104202d540c07040c43d81c12500540301002810031100701d4198500c00c00002401040c031030180102190343e0381d044042c6042707031004000c24a08003e800650f480e001960303200700ca2003075400400a85186060003801b1500f403d207082003207450940030b01042810141c100803640c21014446030241e00c135850030440151084000640d01c3c00380ca07070000e0843e50307550007200c10003c01b00248004030703052411320303819101203140e4200b1944440c90006030030720860f4441c05601101007040b51441c1400701d9002c0c450005400d000300e1044021004441550029100a602c5001c040c081e54240d48500c1e039001944aa00d40001034244c98200c03400d0031242c001d0300441c0da00e00702d41c0300c62145c0b00040c10ba40340c040306581844483e50615030364018104034018640320401c0f86080c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 192392437 1250 192391187 192391217
    0x906170d0311040b04142d10091e0602010c170103020402090103020c0f06070e0d03120b0f030a08030402030d03060b0313050a120c0308060303131211100903110604060c03 75
    0x4483c0140410105203640b01d6442040d02910340041d00300d01e10901c92070116142840900c10711040481c0e00c088803c0912200c1410080740103540d007c440c040020104000c10b00040004071141501c5015044482c840d25112000b42929402103100e030821905070440003420f60030008090540350304641c05a101e02061004800134040d50414485510034500141200480820000d001d00200ea0b9080e80000005003403092218902c2402000601c41000c0101c9004140d404030f4103601008191044035034050001a1034482295000d6401c2c10001081c0b0007107140030000c5004102c098282407111038a410b4a03c3c1c441c0c003005004007031010300c40c80c40e8800c00209114042036168880c4061b0703046543d40710010040b00484804901058160000c01c1c481d250010941d0b00792403100302c0010390141010807400c40313203100070700480c1c2c000007003502c2201aa40e15480f01900c9035003546e07082d4005145080c441c131560380014007140114010002030008a0b40200400d0106401d418905404c002e40f40c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 192393687 1250 192392437 192392471
    0xb041b0b1611040c110c040209060a03020901020f101a040b030c060703020709050c042105100b010c020d05011410050904061109040f0f0b090906040b0402010c0b0109060906170d03 79
    0x6102c0d9a07000e4034202000c12001d030490341e84015081880126540300950801740412842000a02544284148901203055110381c009080301801032042d43c1001081c64189854002c950350300c2442070340c88600b5039000c0c00d421700301d400111100700e4082c815000a600442d4940b40003418cc140501000580001811300030084c040051034626001c10a52030030070109001034000340241c1040b40c988104400701c958100d22130240b070503000009410102c0b080d00c1c61600410907040912305001c19a082c101c00b694401d01100f82c441e00610012074801e0000d05c0c82000314000411a807600402002d091040341c0319280c44aa0082d440400041c403c0424140400140a141650340c0d0280c1812101c124101c0140c01c80380d078502c40d0311001d06c00e440841007002980700c0c044074140b03407951082d800200891f03044090240c110380181001034500c00c543d15004c00d2301409810401c0c0700c5031030710340810482806116840c01401c658004103901281840c441e070300e4000c20050303113040544580c0c40b080c500c1c03115 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 192394937 1250 192393687 192393713
    0x1101080c0f0a03090c0503010b0f0402090a0315050f0906090a060f091b1e0b0702090a020f03090f070603061508070212040305100509010c02120f04030f0b041b0b16 72
    0x10200030340300c40c2c450400601506900d0011628040c00d00400203090605024170469004001c0c4400000c0c403d000520000b900010440d90740304100d0800000407a008040312042c500e08100c022541c0e21306600030412200000c0c040400542c4100308025076984041210001580d100e038011880030700b4003506101424280d40c012b41f8a49029120100601510411604645d00640c20207001040c2060451450690384590003410004010030001454034460455102c081000d0041c10190140302032800d42d041110044400e41c816650700700c0900d0200207800c01000300740b500303000c034034207250340508a040242c0c1710f8004d2200900201d0f00300b034001c1c09011188100354541d03d450f55034170300b03180f943c0c0c4943c901c0220b009441c0078046940d550041c004c1d0380d080400d0341c000f800c031080005040041a407020b0f1000301524820301003c80090b0b0710703030101440300e40a03005100c25814603007440c06160160465480755a4581c00e01080003451841c10340d00303119603000d2100c20b9011941020700c012900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 192396187 1250 192394937 192394957
    0x100f09080d050a060b030603070308070f1e1709310c030b04060b04030f03080a0e030304030302030405060604090309050121061707060c050703020d051501080606040f091101080c 78
    0x124001c1c5a03060103600c032910952680c032091005641d6070380030001c580300603034050790075401c086018404101d41000a00c5064414118032800080a440d000c0c25500800e60704171882c44a203c0d00c074144010b02044040c00100702036100d00d0803600b840024241480220354020300d0328118031021b54401ca02c013108400c0555220140704c2070002030302c001c00401218111758412858070001060300e241d0981603c0689a1213014080c030034043c0e4805407002c8100801d440011a180c00740310014003000d001850065120b5100507840f42818940b8a061081c0140b100307001d24900180200400c0e4011403040445a0a003001e00d50000044801c120341c4401d200d5624003103040001c0052031225112000c21500e01802c280c48440ea118402150803400da58409007603540031420a002521741005202000c521134012100960000000c080c41d00000364000070141c0c004100700311250605002c2c8005100d8070550420528a00781e0742e9500888140040c9410804907600041509000c3c0c0304607000b0880e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 192397437 1250 192396187 192396203
    0x3060d060f0c020303011e03050627010c08010f05060c1002030a020702030a2105030403020601051c0605100303030509030403150504030504051c05120f0703030f06120309050306150102100f09 84
    0xd2000b50181d600e500c02c0c07045001c6030070310f401c0c448160210b0000440c143c03a4044042d002586901c10040c3d444c003c04866210216940070b00d40c0501082440f442c5025001070f00c82051961404d00980c043d03468961080c0c2c0140c008012080380b072400410865600b0403600b80c016242d07113400044000034004c191009406120b841f07950000d01a01c0802c0e00400c20300d4800707407007040c2c00d1904211035901003030342e0050142e800000140b28520706000c1a02a92000d2000d140740404240c81d95026104251103035028526005424000c2c55814050a540014110011441d00e440d644c1c80c1a101407400d449001c078186d841c4e01050806100d00c0071980104001000210581c2c1d0045503400d80722407403035003141d440c814600232070801c0d4028402e0316090114204114101441c43d02d040d0060496480b5601030195690008a6080b14088020041c10300a45d107040304141010f00f458074084002d401e44281003000018040e15a13800152081042d50440000c900b4088054100000e003c1e0701c20010078100d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 192398687 1250 192397437 192397451
    0xc04050a0f080c040b031005041502030106050a09090c0e012102070b0f15311e0b04020c03040b0c191416030305090d03021c020f0d1403060d060f 64
    0x140d00601141660b031040282c9628031074050402c000c861100da101c50305034011807160685c060300e560009a001d03000300c800140d00f03010f042d0100c0490f132090304280b02060001c100b4201d01e41d0310000c0000940040b034801c000f95482018060410071842402c4c0341006481400c42443c0f40d06200c04030402582d01c1010354454426190400d440f001c22501d43e01e80915520008042170400810100e03a01e01c09089211404a01d400c180d40070182c20407042c800480c0180c41c0b00760800ca07441a0b50440c0904d410f14000354002c0c0c10b0036401c0c1c50504103064400c4d80184125284000040111412a18130081070b503920509034150704d040001c40c00c8201c0f2294140c0e800300d03040c0903150041500003200c4a080e600e060103140c0140300c1d503440900028000940074003410340241004458282114003c2c0100c0d1810a00140c000100d204c0910002c40140c00c00703400c211000034200000140307880181000410a0b0051403d0080382c04010042407040c0302c9512030f01c0c00e010859000040caa000b4a409000c18 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 192399937 1250 192398687 192398699
    0x181a0d1508030c240c09060c060403081e0c030604020c1903031401050301150504020309070806090d020d1713030e061201210807060213051f03061a0d050c04050a 71
    0xb0360031614000300030b8010030002d4169910100c1c41400b1054010030410f8094860421002d146c0d0004d410841d0020020800c00c9803c0d042001218402c910a507103248240c9440600030103100c40262042c87d002000405124030f40c07140500f500e61000040d00c0c01610307182c40c0c61a1178580075540d400800d0b0504010006401c0c1a450740280d500c241c2c8a00002d02641d03603d9007410f080b2100507540e04a00f10000700e040c0201d1905030011a00030801404480c2c0d0a13450301180b90800c01c0995056250380d1050010204254050000fa44c02007014105075441481c00c1094942d1020014502c99128900b620b60307104050003981500012000902210b44411103100b9200c0701e00300070b0260502c01c09240158191641e02c4a03d550040780c1d1094803241080001e41d80e20002c1e41222200b00c0c07000d4801d03400440c0a8951250030603907801d50511072a03400300b061501070100c684a8000310007159070480081d41c03003071a890448040c03040c90140050940d83d032284180345805150030141e88068000b40c00650 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 192401187 1250 192399937 192399943
    0x4021c030206070201051005010507060506152a0a0201021504030215180c04110703030e0312041a090a020d02010f02011104080d0e0f09220b070f181a0d1508 69
    0x303c0c581c1e039002004551100d181c445448210f5201c3e0320300056041100760002034442e0003464200c0409480008000912004003946400c00034400d411000d5505c408950407240c00049500c0410a03005000d078030840d500000d46403030140344e044440c0c1900f20080b030704051080002c01c18142e6000b0803e081c80c20100700f074040c6034a501c1d035402058803410034500340b01c0c5428400c00c101340342c9070482035140201c00e0341c0079409044080641d9902d40000c0c820310201202d0f4200c450312851082c00040d020071079045091203840d07400b510000680c3d0011900c034006840c1d900b00114120340900b400417264400341c008901404c0780c1c000801064802040008841070000307802030803c18591504603800d0360b00d00500500029806259a00c05c00e4580443c40704c03444501107001c08130b400c268141c0e11640640710310b904030005030b640e040054600d551811083c0c1d408400a1218640b84045520315464005826116807250250503911580000da01c26100c0c0c0580c880b54007202c1010b51002d0340c99032002d206803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 192402437 1250 192401187 192401191
    0xc07150213060215160c03050d181703010f0515070c0f090c0e0d081c05010e100e130b10030b0903040f0f0b0f07060f092409030206040b04021c030206 66
    0x2000d0b120300810f4884c001207410b005071042117555010000d0903990102160314002e500c00c19400d0150802c0314010003005401010580340446881442c0d9038118a85400c4516000200e0307129286d050005100c00c0004403100d0089450442d00c85414214010041030346100350200108007182c80c4000080640c122004d0804440c00301d002041340718403904054410030200a84180d0220b110803180c0000f61800026140c5800d40b1411114824142c43c014412104203801c0740d09900e10b280200030b4502c005903000d40240828415080307450800d1015603550704c4000c240201490480400940780440c010440d900a58006900081a0510a0b4529102c0c1d0046c022503034404003c0c100840c4510043c1d00c01030499100140c15441e00829010032885074110b11811070f206130301c4909450807000140203501100d40030780e224004034412030f2080c91942d44110408810b250400d00d00c900841c1e00407800d140e0294108007a8000d0365204e10025406280006441060648402d0040309256000031114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 192403687 1250 192402437 192402449
    0x6080f0a110109030c0506030c04030b090f100e0a0f0501020906041707080a030f080903090405010303050a0e0910051207170f0114041709012c0406050d0206030c07150213 75
    0x1101c0516030000440744000c1c00c1c0000707032000390b40079020410350410a005681c031026441c0b100e42866113030769501740080b0080c0c1c0e000303026030311049640c603030468180b0504410300072581c0d04002804d4640c64080d00c0c1e0781c24001c058002c0c2d20340e0840c0c00c1808002c0d01290170814004103010342c0c0383d40f43d0506040300c00c0245481c0d2200d20aa034004904130100203081205030380c01d51a054032050300741c003003181d01d0384008080c072800c0d0006100003402600d0f0360058901035072003902c400742c507907201642c014403040304184624031800d0540c2c28880b14007030200c04001594801c2e648440d400d02e071485a20700d444181c1c0d112501103c03140208038034010b8080b50101c06500060b000748144039000781c0b80d8280364020b5502078810012441071800c080b00d9180101603101060501030100302407101c00029008062054000d1090100101b444904c0c4c94400c80000d040201e441508451050300420b41c0c07800014140c660b0280c1c00119503050041c1580c402c20700c050454000c2d50b0740c00d41044070040000c2d5034880d0f8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 192404937 1250 192403687 192403703
    0x6030c040e1015060e10090e01030f02102a080c0307080418143c0106120203040f0206031b0301081606030524010905060d060602160e01051306080f0a 66
    0x124425043c41a040811120607a40e01004038980601b006400100180400240603d0850016480300902d032400d009500035501c0204101080c0140080c14500303049000800a4403101c58161620603441c040740d42c0d10940d60007510036100d162441d02441034a15180b41c2c3d210116012081201d100700500568459680b2951424848001042a01c2c0100f5400c40410019400540a8400d1402c40342400b000d081071034086220005407420480844030544541c114000014421b00d03400c641084072001e1071503811451481e00f522184603889031010b00a1040350008003160981e2001c8070301e6171548851442c480c0c2e995030364058107030b52047c038400c4c0400003418406c0c00090642c0648951441000d01d0720358070900d08110995094052841c800300e9041c1f105990b80811144c9601c0054000701c00e1165000640320b041c40300213071a0800030f0711a0100641c0f102c01c00e00c26102e840c210f81f41103680c256000350603501090100009801e081d00603184510402e440092105000590710414500030044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 192406187 1250 192404937 192404951
    0x40905060a08060c09011202091f0809071409180f030d05070e0904060b03010615020a230703060506011b080a080708060a0302010813060c0810051e0906030c040e10 72
    0x2e66a00c0300e10413111851884802d22000c0990350142c0000c224043c1c00d5440145424080c0b8001040d0360400d0b00440251a5582220805c082d0400c0d0300a030400d50080041241c1d51804103000c00002000007154000c40d204000302c0c103001c09058801e06111001d0060310240b5040d40d805a540b50030034520414213500b01f40110f201d450280e2000f02291102428074611581c690f1540405040072600040d01036584d0300000454000403030070710b06150004d6029000185e450301784810070301c84451009808507801280c00c1c1c0780020004804040343d0344030101003096a80c200c0180e4103040a01c0c0c0c1c500c84010107150b1401001148001400c405071035403609082e40d15104822250000120760158000c20051028000f5601400c00241d11aa0601c424a41d01106075908829110020740540100722014184402c0464801e4554054a0b00351008982c12062104515000c80d42c0c02c84580950810000b040c82510248028400b069000e80706100c01d0000003000c559454501c03841010751441e0070340c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 192407437 1250 192406187 192406199
    0x112021309090c1703030f0115051b0a0b0a020c07080303060315070c050601060309060507020601050a090e1905070e2202040504330e0f100c17070201090b090a05060106110111040905060a 82
    0x1d0100c085090b84d4ad807410949000200045400071281c07008942c45868a031400203201c4170001032042809010250300c8820403403141b86050016005104945c0007801045000e0714000354800c985220b1350311101d00c50300d88000076070701d0030003040380a4040c1c06400004980140c054028101e01446900104040d07954078070100d0b00c1b18000e0203400d03884681148100a500203079000b0070905408581035038070400da00c0e0303203142d80c080925070b007180c09411640c420001401d4020030168040301c4111449002403042180f010f00441d4000d000780700c1c41d95040820148002c070810500300d03041d950211909050300c1400d01901010070104000024201034003401043c8000c00d0700750482c080d0b80e004100740c01880c460b04002d0a02d40007451b08224201c0d201941082a01141030f00503681038000007449074031818400300350340c0000c107140300c690b0208049200045c8000f401318111000b900d04000c00c81410300c0c0d03041c00340000312840518244041000720742460750b03030321042c00f03500704a51a040d4103039252 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 192408687 1250 192407437 192407459
    0x303030213140a090515030106090c080903030f0412030e060a0f0e0f0714010e100f170105030309222c0708061602010b1804020112021309090c1703030f01 68
    0x1004407a0408003600c810001003030746810546d08468a0b0801060020503240424210740f12a03000418098648240016440d00103510a803c06540e4004c0c528516080001c0029030002078002804454030190183c07000380319a10012084001c801610b02c2401e0190a400140207000b505d401c4141c81d00410891448001807180280340000003c2d0104501d05010f2031031468100344001d040c8411000299101d503030f442c40b03118400d0210340b07828010400b11030006068900c00780c14a000c12000314014082075038008140c4643d24022160f40082c103000c0c00450f543c4c10305516682d2440c0e401c00c4036000d810f44400014107590340018003400d0222f040d05034003076642e0020784500801608035402091540c0030f034206a001d5a0102d00000c542103a46002140490589d00720051503896607070240011980c0c4070064078401c0d10130b6281075042041500d00403078000e9440c450480e980e5914a03804042241400d120402401e529030f101e8282072030782d0070f40c5840e07904c201e60894604141000209a04e4070f04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 192409937 1250 192408687 192408719
    0xf11090d0803090c0603070815030d09120201030f02040807080f01020a200c10050301150c0c050103020d090b010b0702100207060801140d1205180307030f061104030803010303030213 80
    0x208540c108808507216054264005420f89a107406030341c07805075160700c1e90740096000c0c0c81d46507101829442c103084110210040081c16500c04e4000113054550300d54800351550a4607442d075900d40c010946440180e00800d80f80d0030543c4402d00105000980040c081180c4040755a0b610a80701d0025009a010f401c0b8810751152102050020420a0071070342c8600340004414581070407101428125000110040c6070290a100051000401407082d005450710102c500810350504814801c9030f503541103161030460040c0c07410954003056203030b405002030300580c900c15008813020300256141ca40407400c40c0c1c0306002c2a409a00c1d07224415100901c001016401c40391182e6400c2c041c0c4c0d09028060010411020003d9800011039441002151a0220702880c40c605502c64030b03a95520302d00c40da568131840220152103508041010000710b80c1c1c441301d400f030b4154403280000b0b280302103140400302d50045800140007540301000100405030198000c0c11a01001092110a2036480c1d00074403210801c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 192411187 1250 192409937 192409939
    0x50109050d23010f050403140a0206040b31020108010f120b420102010c08160c08070506010e0f16110f0a031205090303010b2d0d0f1109 60
    0x604261040400ca1010350b07003002d01910100000224206181d190a485000e80c4000700643c0c1c5405010406400801440116624959190405c040644060f4542c0c1c0300802c0900200500d400141c000b1002850202c20103c07541440c4640b41c0c416441c0f105d508002c46d9049001c100b8541c0040359040d0f03d215144219890340008203034440d103c0d55007040100e40540420307030304008115040d00c00d601c420854403643d00c80c41506200907114104e011203004450a0b52815039151103400d149103075201c4c03441944259166101c7c08001c44000d01200e244a00f164058100400882c2d144204400030880300c0c1281c1000c0d030f0008258680c00100c80241c00183e070356170070740e82491070407000031401350400c824082800c0c8290360209011241c514107041d0414022800a914031030640d00742c0c3c00d903219464001c042c00d8004c40c207640c10080170407094403849442e1000b424852100f4804600714940f5500300c42c81b030044464441c00d140700524003602451070100c50084c2010482680104080d0958016040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 192412437 1250 192411187 192411199
    0x12020310020703030b0603011e09020306030d030b0a0b0c060106020709060e010e270102120901090201091208071505041103010902010f050706020409050106020a020316050102060403320a0905010905 87
    0x441403054002980004421024551904580c00680e41c0d01c0000e18020302d2440b01c0c0d1001030354098004003004900341c010400d0a803060090100c00c1e100092074000a42d000d00300080d4811054000403107500155016401c641000148180c508402040c028101c411a40856140070303101c1d2440b0094400c1402290b41c004120401003103000e0480032000e030040b40154855401211007111025121000d01c4a03c000740c0d0000b80a60051022a90b4503a0042403d002002018086e500003001d0407440d04c240004101e600310144140031010040b00d03000c0743d000d903244495190596607000507017011034083c0c1c3c250035101d201840c203003418001e40006c01d50503512600e001c0300005054980e03404c841d00a444480e401c1c4030108507407980c3c0c0314140c040c04064004101100d15481010303e4039281e8007086401115282007009580d03000180143c0003503140c100b151003100d95507951081d043e01811545643d00003a4582007555a02038010072080425550f8042c285407034200544401000b4482c03241c00c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 192413687 1250 192412437 192412453
    0x30105100e010329010e061201030303021b030d0b13230c0c0106120204060b040f1401050c01090308070206071814220605040b0d03051207021903080907120203 70
    0x3074801c0c10000040081418005400c0007420500c8500100341d0081188841c3c29044009031980c020040c03034914182150058a422000c5070b1074500d04506210081c10300d500801c0c2d0b040380c104a159a00b04200740c040403031351074128014511004d0507030825554001c0c000c00d6030382030583d001da002e100d918103188803001da1b1a62424030034a50001e030003411142c512400340800980c3c00001e008880040110f0b640500c0380c1c10703107401088100d40007030b8001c1c11008001c000420111420000340707002c0710a000b507003865408481c00182c805200720b5014807035030752030b101d0841c0805400412190044039158200c8203940d1b210781d402d49181c250442030034800c40c04800c1c1086a9203040c1241c07200104046d1550b01042c4041c4030404024107080c88160311103464032001c3c822803d1034450581748102c21203200000c50460388001e040ba100305168111302282100010780d11742c1c0200305011041c3e800d2019441514100c1c1001081001309407400c3c0c00381c2c0501440041e480b460304c44e05031862500200500744c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 192414937 1250 192413687 192413719
    0x50402010e210a050303010509090a020a140607060608100e01232d0712020f0403110307050a14091006020304170c09010f0602060622090c0305031605060c030105 71
    0x36090030321444403041c1d6448002c512107402070010050881c03140c001546c403541040100300303500c000140001080e0740b02c1030703078000583e4036184508101c1d90200501030000b0704200101d104c034880c2510107400c041c01d04c140090308072400a000303240d40d640c65a0070007a01804907801c5080c1c40c41d04010980552029002044401c2c10f003222130340100c24204100200c41d002220000c8940c1d040c050752b10040d80700d4080000c1d054000c41266030740032000c030045141c06003401c0b4180b96030086000250000c56205822442901c08001001c05410700030041c0c0c07035495640c52119101211107280c1c1d80200d1850022540c02c401c0444404141c81058010f5803c041c04c01d589004c1a100a201443e00e0380304058000d00c4c280c41c2d94200c3d6000c0c0400c0c00e007000b50241020700c0680f0380100500b540d030240304141c0d02d03020060104603108200b0701c4c1d103d00c081030b130400c10b0400c0f0b050747d826600054018080045c00d003004860611101c1d44461140341031300c409960700b000340041d5010900c1415085141c45a42c5542 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 192416187 1250 192414937 192414949
    0x120320030a0209130c18060c1205030403030b040501030b01140d0b07030c0c0c030516060807080c09010e06040b07170a0206040b06120307141c0509130b0904080301060909050402010e 80
    0x160071002d405600c00703104c103820f40380580b40c003050464003203a02041c5011028150040d018090116030034400019103035650b4a0003d07803000d5881008002021000c10105440398004c55642e480042090045507101d0403c04e203801c40c28070401c1c0141604c5940d80c940c50a144030041c1402da005200d6a17000d0380caa54082e00603061380b9414404111080c0c100d00d00080c02007038040d000c0c602603001840106075002c9400c030310650581080c001c1c04000e100700812a50b1140c21240c1c001000d82c01c0740e8651200e0001030f522400c84455255001034013003000300e0016408805404064010701d0500003024504103103101a00c28007104000680000002a011600241d8220b4000c10301921703928000d8450040c560550700240401c5a542d50380300c0c14140c1400e002c105000184121000451036010400d201030b00602c0354180c0c02e07011b40031411310107001c80200d900641c0303041d002800c030784034900d0030340ba00fa0b020f548240900070128819a1000c40c1190003440790b648295410b850b410304600c019410020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 192417437 1250 192416187 192416197
    0xa1505030c070201030902091e0c270a1508040516050d08160210020d031505010f0809010b04020f0c070801021e130314030c060c070f15060909120320030a02 69
    0x1040c50349070b20b805c0e00180c423010055482002c50101210002400b005500741414001d010a000345005001c040c1410b2502c44a002c142004040c0308101401c00201081e1000c0490380325850380d62174504160603a940201c2d07030911492107441030b507500d0401d0042c01c1003030705420b0050b07981069840a20b50000741701c050050109040820301c1500902b01c80d8005007440365103031202e1005370403500950407a9074040c0611000460031480702c019280c200f02c0028001c032100035040040140c40300100703a80343d1080d8010404038038003800c2559a04403551030074034a540300b1005000b641c0b0411900180c03151044c07080d02c0e18008021008106089440c81420359078100038003011000c2c9a070940000091505410240320b584a08059a11100150b5000d8101800100019001d103c01c000c00c10005210703025607101d09030701254400e800349541c02c2c0340c0300403d41c2c0d4200c2030320030b4074203103100051101c030072100d120411081e0b60038400c0c018800210310b00c040f03d070860105141c0040c8080340e100040c50300509 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 192418687 1250 192417437 192417439
    0x70e090c03070609090f06030506160905090c0a080702060112020607020316090510050d020f01110f06100311010c120f140304060e0d050331020d0309050a1505030c0702 74
    0x5000948403000080c100050741e4401c20100b030749000d040021815501802c643c00b1955030042003440e107161612600d50000a000070104204186801ca04a0041c840c41000c1c24020740814180e1030101c0078444c036a84903844020200f115440003500c16480054001c0c165081034030100035020260b130030701c00240c00081d0201e03803501401c01c450446001e240500e400130b2200402c00305003030a0440303200e107074220766411640c0103030042c9164102580700c0c8070040d0b09145d420303e0001120b10240c5402814003c501c00301407040d01404040c00105c420024003601901e00a2040d0300c0b1561300d0000540d414102c400d4000d22101e454022030380d5050091241d503c1c562504c3c10001c1203411450b804810300d40c82203400726120707555204501410b4101700080c034100e88403402e00e6440c6003481c4d0300801a2030a01c070044000425440c042c4000c03d84000814122240c2c05052a88941410700d8054950311540c09228019422808006a02e0b0301c058840000d0b001182c0f24549544c44405800c0b5290b403020a050f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 192419937 1250 192418687 192418693
    0x503040f060216060c090e010b090d050601060c02010806040b090a0903020f07060513050108060a1403101d0610060c0b0a1d060f012c31140f070e09 65
    0x100001c240c1d40d000800714004071a110340c40389100341c6080c00460f00035aa2000c1006100c54084c040f8465a007002d50641e140450940d88442d6620000388400074400c070001c0c500e005140000401c19002010300681c6071003602d0345d000d00e0740c41000340300481e111a440c030703507010300003401003900700c00260b20004a07103000b88190b8040201c0148a1840c1c032056a000c2000103030300040158480c1c00c1c07081d80300080c160900c0c00300114100503001502d2000d05004101680b403545400c52041e070340c108140c030403a04c42c50300c06200250009010032521000c00d009400350340210300024000311031a004140a450039134841a10701c0c01c1c5500c60901c06000108407a003903590f100802401e0915400c40d000c043c0c540c0d00002c098520740254000c4005070181e008440a8070031002c04007600003501d401c0d0f031100324800790100513903451804200100558401a0758030f00045005000b0603008020384c040310390300a0700162001c3c00c03620f44040d580c042a50400155810040302405103850524015402122060032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 192421187 1250 192419937 192419963
    0x30c06052a130e071808010c02070b1b070608011805061c020111100c0215060d08030606090409050303060102070b0f0406030e0f03040e0a050603030c0a08220b090301050c07050d050304 81
    0x200200d01000b515444085902008080580404c50b011076018002c06d100902c202d22110034003a540d04003c1c0a0283c091401265a042c440c41505160820100603811122401e0342c1d180c0c0684885400e0040014581000c90b841c400040d0600600380105000381c409601c0c2c000001d28142c01d4006903804138108500e000d5903810903001000307100705403808141c00140c00707080200702a10b0540d0380c000cac09203003084500030842584c3c3c90b001072501094214603031559079901e600c0001c0302e500c580b540165105241410200c10300500202651041100f80c0890311026110319502243c2e0107404020f40d00020200710512642d4442d800c985403800c1e09204481d41104254082c9041d9085a044611b81240100c10844140918043e003504554103034003441c542440c5542c600c0d20b42c54001d0014120010004220324808001c408410b00400e80c0d41582407216210100000e039603100345102403080d802e280c00b14803072072044011500003d0b0b0005c010816407481c184107545542004000f682c4800714420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 192422437 1250 192421187 192421199
    0xa09140a1a0a09051515040e100b0c0c0307050a03080d0f060806090a1707050a11011107060309170f0703260f040201020f0303090d05030a0b030a030c06052a13 70
    0x21201e000d80f4484001040c40d1900042c481d1004404440300c0b4071403000400280f13481c081c0d4004036030a9035030740215002159501400c400500c1001c0e40145000300c00000d04c62101c00700440e03480240c15046080c2c030520f0307a41c2d0080258000d114007000d00300780b6081140840740d640650042c080088010b0740884c400395035041650a1000460b600c1416400c06071441080010920301040d412551703500c4582008070940300c0598400700000020702ea1090b4503200003003680a4031440b00c80301000c03800c0f035414940750300c0300401a1024800440d151545043c031607203400300c40700689a00c640005d003040d00b401c0503a107084404000c1201d140001c160340d00d9080240c295034180c1da62244d1903109240003142803e1000a02d013940500704080c0b103400038001d0040400000c50080c0f0801c3c26403810b00d84035180d400c0200020305503103030055450f202d114060300030981c0010020702e8660150404104650360b1b50460b01058080c1c00c8000c81c6d0390084600d901104030344001407d50340d07444103444000f00e07854407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 192423687 1250 192422437 192422449
    0x506090307050901032103050f060423100611240c131d0a0507050901111e15010609060507120c050d0201020c280206090d060f0207020a09140a1a 64
    0xe00191185e400910443c006e002d001a14164010503900c1c1c200024a411014081030b00d10103400c4510980d12034290b0184841c88410b480c502c1008001d400c0d240d800c000401c1c6065a44074402d00c40030030700c504403005650001144502e03680c800c40603140d0001203500c10b541d802550040c0000525001804102c8416600004140103480010850042541e10b0401100c0301c00000b08605440d81c181002c201c0321590040030703141010300030300b0300c1000300d110407240e81c0c14600b101a030390020101110146000f03110000c0d0001380c034000e050400182d44d8880d001210001d4030381c000c2c0c00126604000c1580020004a038401010000b450203180c1d4415598810341422800030010f80107070b4021440e9014440705100100885a4806404207956084070b11041c0d442d200310b20282c8601804510f019031303500c03549050602031b81c0c031400c20850710b4000f4000000940000f01f05900800002c007000c0380d405058850710245503205031206035143e4621110401500c112074101e1200500c0010300625030b1664 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 192424937 1250 192423687 192423689
    0xa0504080a05070608161205100b03040b1806040302070608100308070308010513020711040f0e0a200603190906020c01020408010f0509030a0917070f03080703110f070506090307050901 81
    0x580301030441103240c440014075010b000761090304c0c4807003510211001550452608641f28840c00030106040d070715000c0c0d841d0a0300465012924866000042000308100130342086d04c82c9070148030b905c0d240203900c3e0b6020f07900d01f41248c005015910454040c0211405080d8040e400044454400c10b016101d60b144507d40d008218202c001c81d1b14200140038619011808040c0140c203c0340440c10310040d501c42032902448844e4440c0102da440b503004410305020b402c21701840d4031a8084644264039880c00a01d0400131046143c00d02905003402090303442c05008507070090100c00f0f003148031a103421480000800034168115107440d4204a403107036841c802c0c0040d20040c91000c0002416180c8a184202035820003401c152031500304100c0011420b4009400c103061301c4c0c500c0300c00d00c884034010021602e131440d140c1000c2703070103d4490800410040040010490070f8441c0d81d80101540c001c03248a0303583c0282c1044080c171031704043c0e0140140c0c184000030f4840c5010090441e4a5259100b0104502c0c0000b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 192426187 1250 192424937 192424943
    0x31e110d050a05070512032706120132040c0c05010c05130503030c060c0a0e09010306020304060b1041072105070609050a0506160e01020105060603010b0a0504080a 72
    0x700d4407800e003d0040c02d000c1480200015105045459503003d8415101d1144d14403c68004030b00b0310b524030101440805035400e002c00a00304c20b83ea040c4034408155146000d1041000440788080c0d5072007401d110942c81c0300307a441c60b1010111500b00620400c00a4090584040c0400880c0c02e9070002081c403d0049000e90185902c80958a03800c540744103700000c10340200b4001d910030007026420440018180364000062810161140203000003114064600e0309034541c010b00600012080c805603038000e500840c410302d41000465103000902155071802e01203c0d02040008014400c1104454040880110340e06554045240d51070107580c1d02c100c50303400e24140c090000c44c4d10b0003089101c00c00078401000598040700c0300414400002d01c02c1c401d4520040003183c40e1100ca008000d01000060036045e84179041d580c0c2460505403284005a60303035512000210400c031000d5072940103101c1c4901452016240c14556820480728154503880b611013041008070400c00000d07444800d001e4814402c1c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 192427437 1250 192426187 192426193
    0x10020a0f0c050114121b0c010f020a080609040f11060904020706240b04090c050403080c0c0a050a030203030d1a030d050403020a15020a0f06060521070609031e110d05 73
    0x10402000420000e030507071981c40e8592040004c100c9901c00249110390100450814a80c486c0407440c60702000e014103606140f40c1c0d03084c64141c0101c400d00b90046c00c0400104c0d50f68030110343d50041081100b00f000c0d20090400d4134031000c0c00d80070401d100520130305450f0280c950752030407040c28013040c00c030f9207c22415a1082e540d21149081c80381041e00340e030403000e0072134600105a070810310111064400c034840c0c900203541d2604820306280c01401640c0003036401c0302e81243c071040320b89861f0b509c0f041c2d89000107110310764034140400c052030b0407010305c1c09513600500154200a41c4018401c01814000980810300c0030211401e0310303030b03501084020040c1505954030764640346544180a02e01d8821f4019828088034146030300700315580000c40c418035940004c2c1c3c1c85450030160510700c2c0189840d03000181c11000d07992085440d410395004000d0210b132004100c90004d5a02e80e02142c2190702c6000003049410301102c681240c40ba103a00c01015640541880c00ca01030320800055001010141c0c1121960 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 192428687 1250 192427437 192427439
    0x203010216061d03070c1203091203050c070f0b07060902040624080601050a0e010c030c06050c0405120a0f0b09070503011802041508060c0c0102090405070203070b0a14040210020a0f0c 81
    0x2600f06508003420301c01c28011414400250b8450640030b4140c043c00040e4034a001201c0c082c5441641118014805421646c124205d503090003003c5600550010245110305c0781e0000f03450f030401c41e4800464407078800c2c1d9420310505a0359a00600f445003011780c2e010752100801701d00c1942c44c10303201c0d1800102130f80e00b02d800c03800381c1006031500c0f000402c59030510009100801c03840f504114241c004440910f05107204003c3d91400365141d5114040c05041b813882d200170000030b400308400038404c3d00d10484400c01c07c124401c00055482c840040002c10714414100c2c9100001c4d0304944003a0002031040c1920741d8a602d40000ca821102001d00c14156a50a000c000c020740c2030512800e002c20222108008a41f0708205006a645401030581a1400400644810440c1003981525402000103005001034244030704000e589800810050316510070820104865008078421014881c90f54690b200c469a202d8080210705e0454000f1039043d8000c1ca143e0400140f00f0300d02a2440310310900d03214104c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 192429937 1250 192428687 192428711
    0x211802030321070305010302031c030f0501061d090108102003070302180f0906190801050f010602011401140d020d050322050d0201020307021018090204080c0405040201120504020301021606 83
    0x740c101810a6080c540717071000600140e140400d86045075102c0d44094044000b81820440007480d81c00119039099107040000b00b80c01d60300001e075401110b5040d00c407100c152402420494980300c203118052080c0e0000c80c243c845604150000200c0071b600d0100c10020703542c0070700756042c40d0340111043e034000b0340d000910010454a22601040b103400c2601d0018801c1c5120010808a0901405080c483c00d400125106168200201c0c0c0780079144042c000e00060a013040382e00c502d50000c3c010040503500704075581b8050629174410a04880f019000c00c0310074000d810501035640d03c0040240d8102142d90614000704c0d0081008222058441148902000ca4401c40406414054120911507207a100c4020b001d80c0e80002030700c680f90780480e4a1000c6060b20031050f240006003404000240380c070140700086444841c0d020b4030071584040d041da090921103a0402040707500072240240031400085807450040c0e02ca50041c0d80c00ba101400062900c43c2c05041e82c24141b40030603007140d00c0c2c7d465034002503c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 192431187 1250 192429937 192429997
    0x9040b06030f0303091615050904091b0e0a0e06131b170a020f0909030409020f120705030a050108070e07210e0a020117010b16050114070302070506072118020303 71
    0xd150341c2500c807c01ca000c1c000c0c01841d0388902400703248229101c0d600c1505002c42c94074049110043c1c40c8243c1409591150f03504401e1100300c5812603841d190042d42c004a520108500f8481c441601514046003030541e51000581c034034010640701450550b001146000000c8003042d2200d0416000300281b41e00b17032040003065240d00c0a107a0162014200b48040154000162800c1e240000009a207440b140402000b0a000364030311210042c122409001d146a081002940607508415040c441070303894001c01030350780c0b2043c4a01c03001002104005060144070750000464012801045804400510003401c00d0b41c018050100c2c25030130004614046603040700c00c505505541003d01c01403580b4000c41ca444038000c03510104c03058890280c03c030302040b200390300c440300c1d41480803011291410400802802500304800c02c407003034410100413400207800354140300c10060202d0111811016040301d080043d00034140c0c2d82a00c22242d030340c80e100580d400c0c0080c0036030500725494042011b94825900c01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 192432437 1250 192431187 192431189
    0x305060901060e1503010216030503060a14030703080f070c08030405040f11070f1e0b0406052410020a0510091a0c0f0307360b0909040b06030f03030916 67
    0x2800c0c2e25101040040d40551100c0e550b00c949000081c044d10045540860301900c40c1a502124002404002004142d0171101841c02070506603036400f40161107220303c540f000410b030300565165200c4841000001c2150380204441d498801903941802d80c26074400ca4407030010303040b9028a40020800303202d1420144203104081203a400140011031801820a4252280f000b01501600071304802406020040b11080050f00700450302c01c90a80d680d040900e031807001580c04a075142e050001044000407030b0380921104450b550807001715a0152410400b645020180500a6002c0e807500540880c809010b03844c040c2d58120703804203052986242407120010690458446002400148000100130406852400c00100c008981c1c07a242c5079800d82d250118803c0b18440c400044c0c0c100620f081d814141111001e981c90355550510b6140c0100c082035008101307080d07402c5000400090086032000b41e201e500b03c07070050180c032924401216010305541c4212184440e03588010115136840b151007803000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 192433687 1250 192432437 192432451
    0x60308161b050f1003110c0304060306090c200106080f030c060106080403080c070c0e0c09040f0b2b06091202060c070201140901020f030d0b0112090b13050a061401030506 75
    0x1d6000c074103000000711070200c03d442640c054140041e0081307503a80a6442a211102c0c10100035440311040016a5a203502a0003200d0007e400c0560004078844180030300540724100f03407515441c40300d030f000c2240880c1105400382a40c41d901d400002850043c01e119a450340c0700400090b6540c0d000c03800790245041810381c020010041c10504001c04203511550301a040752039088455624503142c03c0c9460100032541004401500100c1441f15200d06900100041c15041e5030078042c0180740d503040e070100d86210013100d420131900740d040610717203000d0343c3d80303042000640480207030041c0107444200460745d42c10412903001070101e8800c02c4140e01005415484000d4a0013540b6002c0c0c1c5900080105c5c144c0b0084d410401c8001c01c40c540070b07a00a00a612580840c4011a51109440d001102c00f80c0543c0c034403580802c129000380c0da50820300740500e10005401c91944112626844801c200c03850310240144c7c0c160080034107210000c1c2c0039010f2030300c0c4070707101048206942d41941011410501c0c050880 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 192434937 1250 192433687 192433733
    0x41d030a0e030c01080f0702030705190317010b0d0f0f0204141309032c10022404110f03100504060203180d1709070e012301090303020712030306030816 67
    0x1035136a80207403065444031001084c035100d5150300340203914500410300020300c940030b4130300d0303040d0b07050132840481401c80d010740e6a00580208141c0d525007141c00a00070b032002c440c01000041581c085ca40c10100c1d6a01ca036942c0082d003d10040c86000807604142c000048410904c1c0c45181c4503e0160f008a8544071904010060030f05660780142009800300703100300c0d41d1441c100010600c15400308a030a0600f802428040c66004042d000949592001403103400040c1c0598440d01d2445400460f144140ea00100d110314082c10101040b42d041c0314801095814428422403c80c0f0303001c2401142d00a41c4107610268580c2008101e0040d14890480c03144410740c00b440e030451f012584684403040092140307a1503c840e8030b41802c02420303c0d4242c1c10a0845861070400000d040c110000100f83c1c021900c198040142042001107a01800303070312004c0e0040e4401c0d0400c0c45000c9449103610301d664420300740000c055590f5034488495400007508000918410101c501c00d001a44041c2002c640c404154 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 192436187 1250 192434937 192434953
    0x7050f040801110712050f04120804081c090f0501080f09010e031303020301060603140a050405011b1101060509060a14220c0f081b0d1107140f03040303050a0806041d030a0e03 77
    0x1d41c44031340c091841127110003c0d8034000d14040c409588101c5007e011070000380d540e044242a024044030001c201013400040a014000900d07409400d000c0301558816565245503880711080304444250160a06142e07559030411010031031030402c010180c460710241e1441c0c526145004150844d5a50b42c0001d05050034a001e404c2da000300303610b206601120141001505840b242072490061043d0501012241200c010202c140c03a005004400e42480903002400169140c0040c040243c0c02552003c0d00147c42d00030600445181c4482d4844107280074190210903420000f0859054002822030b103403655660f0407113140107501c4602e03185164031508000342c0900f05516018104034001c1c2c0c0103404103501046d400110b0002c1d40040145c00784020000c2d440782e10500382110030021004203480e007886411115500c01d10084250703411280c06490340c0e42481c0e42c0c04003d48500b87d0003803d6650040e138403034881c018084000800c10824806030021500c2781c18480c409401340ca0000c2c1410300c00e0f4441c620f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 192437437 1250 192436187 192436207
    0x90712240b06070f05010e10060f090b09130620040608090a0c05060706090c0b0903060919020904030c02090103210311160f08030c0702041a0907050f04080111071205 73
    0x2c00c98048a1340311a460601c0c0d40241406401001d0a00c05607946010300403009190304c0c2d954128800b961902610000c1c440d41d542030700c1d030454039000b400d02e07005449200010008001131000d0301300903019490104030030f200c9041120b03480901c0003c0214100010074213104d0240c0c0301d01259171203c2d41000810340445591030380d06064800744202803007030308005148001c11070a5045a4240381d8011403480e026520342c00002c00c0c6802c4001128000d1080000040004100040d042101000b0b8165030550f000c2d55001d0044501c3c1c02001a410700410b0000300d401600c030220b00c0c900960044054640303201c00003425a1040b2124a126410036003445c0c002c00481d09000212410801040481641040c0031300d020305407109952405003010740c01008201c10a41e1600c001c14001d4400ca404004c80c00c1130420700c1610360310000c00160024400c0000840b0036020300c000f022500341440195080641c1c400800b42510445446880700460104000f000c011111199010b0851942021401c00c4a504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 192438687 1250 192437437 192437449
    0xf060e13080a050405041e0e0703030c0b150d030e0f0312040e07020c10030237080c0910030b0f01090612090206040308271c0803090712240b 62
    0x3110141c2481c9000884030002d5018401300c500400c0c02a006000c0030a450341c844400461106903c2d05581c1400d1198900c3c42d40402d0440980f036154035031078100d0005440b8241c680724000d02444d82d002150210b1061546d402e4104000c640c0700750760309a0410411030610001c042030840150003580012071742e40301c0c02c21030f8081c0c07019180d002c2c1c03410359030781da59260892504911800d902c0d000401541c50304000ca90540007818141d80c04442810700610110801111000148610400c8e101207a60000603e1280d0500d9800c500112215810000c0d0040007409400c14030a4a00110fa03070361420f130005041c41a6035481d43e2800b401d1042c85d080c0f4000018021425070040701151956500801e01156148003d45000d59042481c0a8603401c400c0504c1050341c64004c5090310000c4102007113a107524080442c0c401d00e40e04a0b00010700d44803907913030340035807a01b01030120110f078040d0400108441c00030740d24092070700b0300849035001c4440038400244802152100192055400d0a20b104283d807100c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 192439937 1250 192438687 192438721
    0x429071103070905070219061401080601030c051509010e010c021c050606040b0a060f0210090321060b160c150203090108090c0913050307050d1e050310120c08030a030f060e 76
    0x103480c1c907c5481c5410302c0d00900501c0c6140340001141190400440c05c1180010101e050702d200d02003a603480b50701c82080002948840400101c901410840103500354803a56001ca202c00e01818600e580b400640e000032041c02c0c003503515030941a1321840050920504009407904544250b800b0401075180c440480c4400d0185d02030941404180325103030000354420007203542c0174010f0185c1040300000c1450014819000800e50800c040003840d50400c410501d841000c007140c003000c03d081c2c80d2400342800ca8061000c0c40078103403a201c440b880000f070b12020010422106a109d036016599a84aa030b0001d0202d16001c0c000e070401c0d6001380d0800c5c480741c51300007a440e04561844010858510a403914526601c10f80c00b004156000b16605c90070105d4001070024040541900c80c0000102e03e00c0c01160705d400101e5040a603240f00c039400b04400c18085040760030003801003603401815a11101c10380d203550b004107440d0000a658002018100c041842604042c00c1c1e0464401c03010304018034003900d80000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 192441187 1250 192439937 192439963
    0xb0403022101050c18010f1205180a0803060315040506010302060d0f090605060109060f050f090312040e040b0a0504030203031501091d09120c0304290711030709050702 74
    0x80112420100e01c0c84181c01d8086480e90000b401140b51060300e00203190001e140c01821112800442d1503103601424004a02c0b04c0a503503241c015198125214003e8800503181e0740d50f800c141403240d14620014400c42103041e009118071552420310400381490a82203045940c4000c140780240400600c1c04aa024112501190159100c40d1081c020100600c0103450203296246000c0b001c10800841d07400c00762092790240c0341c200301036503240340030790b0034244482e0310794009102000348030211030764200540802c180c0502100c104056a4410600b00d601680090020b20030350390422013004110401c0c1170303002c543c80320113000300e040581e07000c1e580340005080540405024025001981d100e0307403c000003403a001221003c2c4100e0240c1c6044101019103c0201c6806203030b082c00b10240b03242040b00d030f14481a42c025031030140f40c007018140804032030740f01408440000600d41070980f1200301a0044602410300c0741c0c00100418101464041d060b840304e04458200020480215000305c0c4ac035000303004e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 192442437 1250 192441187 192441199
    0x103110a0e01030609020409050403080732040504060b13081b041d01020a0e04050a02030f0c030a061d01090b010c0b010506090d12020a120806030c220e0d02070f0b040302 75
    0x10407400503000380c420f54001d00c1451344042000598601140c102c2e45c003403800707500c4031244d50701c512100b02c800d9806000341140c000c00240d07102070038415140e001c1c103111003480b440d03a04258403070300040c00fa00e003164007a840601c0003081c044280048005680000d00080d0010081030989010740d800424045c0c8003648529030721200c242c04910f0780410340000028182c000c554072100d03c0b0300505010040c1c80b40d10301403854200040e41440d01482140c0c02582003034107a0300c440d600e28503002c049a0005210452881e110600041c002494941541a004440780340134020341c109402c00c82116414a900e5042151018407080841c681c840d5140c1540c4c8244d0321540c0e1561024003182c201c00e60032400818000582c3d2640741034035400b1550408451142141c41c0320003100c4601200c800000b51081641500442030702c420901d0403020b03d80e0150508840d444100101a102030b0840b4401410a21f042c0c00070301461022550620207980175003100101002c4541c04e00300400c88600541c040240101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 192443687 1250 192442437 192442457
    0x702010f090515180301060b0d06050609060d0b030a150b0f091b0c07080f0d030e070303050a030b011101090b07090807180c11122d271002010e0601050103110a 70
    0x49400c03800c51342c000c2c00034009211031507072005826841d0380078180e01c1c0051860b181e0085020f103801c40844080c400020701c02c0d4200340e00702c24090020084042c045605210358408800000c2000050300345101800400013100d228402c00d2050040c0d504003850b12401284040000150041d0700030401015204000c5464040c100b4510745444182e4002c14950300c117002a240b505500040c02c802410115a810b0004c500104a4203070389450901008001c00e2003840340c2408203119600941c02c0403014980806560482c120303081c216031088070140c1e140f03c10304080007100c17034000509000400c0d90000074403070b075407800341142c0c24066840000001c1e1511080603159603441420316050801c014029a08140602500345030303584d0280c40544101d0b80b9030300c4070f800408020340a40c618001e498003010300c1e111640a0b49521a04802601c01b5800c640804050140d1110104100600056000003c00400070640c0900d4440142d000d94101410802c40e1704410340180c050382c10440e46414090700038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 192444937 1250 192443687 192443707
    0x4090803040f02030304170f0d0c0302060103380403081005031e070b031f050603010302090105040213090204060e03070e04020d02010503071b03030f0e210d0b090c0702010f090515 79
    0x584147e50056002d0f00f1451086440d200c008117a080f03500c0c10348011104058490802598803031503440700034026030400001040880c1c00c08446811001181800850200a10b200010000841c041c11342000e0b1f0318204020406400c00aa1070700940c16881c6140000c1c0fa0400099031203069160300e5001c854680c0140240d00c03010800702014114101120b030700c07840c0280f0380042200b00b550070702e40d0740185920006464140402103d06a98010301940f043c2e070300744018000a50f002900000d10317001d48840004034814180b000d0400f5103596622013808050441c20146008142d07004800410300c101d040c0b00040c0d607514000c503081542030800c035403030390b803076010554030b02600b200c40c0302d0b518510260540c2010781c180d125102101e1060001c1002c0c1c403018840541e2072041944042e00041100300b01c0c403c0e541c003d005408050f14014000c60100418004034111074410b4a0320303c9050000300300c0208540e0800140c0035000c1280c9488250356141c0b02c001415090030303185012050000264240300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 192446043 1106 192444937 192444943
    0x903070e040c0e040c0515070c061224030605090f010c20030c07060311070204150f0503150c09011103070b0906060604060c140312011403060604090803040f0203 71
    0x1642c186418406030f41c0200031301d907c1c1d80e14144803500004805038840d1025207600e80e241090b205c1050000e030155003406007000030311150340800203100042c4150b0681100c1d000500403d075900d4400c09282408510107400c0043c0d420301c00c81d06c1c501600800c00c105d1705494003003c06251000c000415840c0e000300c003130b092042e0300684010001d041c440e8004102541d0000102443c000b80c541c00502121880c994090600c29240010083c91030a122400000c00c020f034080c01c00d8282c034407920200240c004100485401021030b0840440e44242c820b8031907209007070200e0703540b03114500340518a94011242e04e0400e108100000341b140c01d10b00b0645040b81d503140c50740082d1040c40d540f02e079074039212400c402c603543c4010b0000d00d0750340380103410032802000a0f401582c180f14005017031504100c3c00915450045040000a000145003141102d0340700da000707814822480c1040c400281 = true := by decide +kernel

theorem cover : BRFrame.Cov 192266187 192446043 := by
  have h0 := BRFrame.cov_init 192266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 192266187 ≤ n) (h2 : n < 192446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
