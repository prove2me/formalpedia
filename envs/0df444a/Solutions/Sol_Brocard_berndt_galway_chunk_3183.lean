-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3183
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:54:46.614983+00:00
-- url     : https://prove2.me/submissions/85dc08bb-ab81-476b-956d-f252f1549cc5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 572302158 ≤ n < 572482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 572303408 1250 572302158 572302163
    0x30c030f05130b09030601080c03030a0c05010605090c0705010b09010e160c020303030a0c1103250c180203070f170126010f1d010e120d0f151a0c0a02010507030507 72
    0x10366440f075440c0c104221036403103298801e00a0282400000d0001000070b1404034404004002c0c50808526503001c41d26820002020f483e5503403a080300044d91303207510314114022091036882c259541c000703082440c2501c83d4480e41c03038040e4a881c40104075140401d880d058104c45c1c0c0e82d03d03285c07110a884000700c8202c04e507040043c0d80340c0400000d01101c60381d590b20201250b442601c510341441c49a80c0010303164054004031300c44401c407400e9015159035100c050b0f4840c1d14404d40c82c00c541c103926001a079107145a14400d0070445a8004113200300c0075001815400c0c035002504e8401c481c024150100407030f8142c107204a118251440c00b12203515442c1c000b400c0606085007000b00310034501c0442e01e201500e824030303810000b81642c0741c11100e00c15040c021090101410001070007100309611400c20035910485d01d0324201e944c0c1c0c1c1c40383c40101100d03010303000004115001c0d0180003410708100b000a403580070348445020b0004c000c900d03402030020901c88002502420810b4030340c0002d08040e1504d02c03405600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 572304658 1250 572303408 572303437
    0x50105070524090709092a08100b042720031002040f081507051c0f0603050d09031a0402060903100e1e06060f030709060b12060607030c030f05 63
    0x4003481042d44104244508003400803200d400750b0f101c1e0f00000712540460042c02a1030702c1d00341802d960840c103000c0c41e0509551140000010796540c0303141e0400310940030000b020ba0700c1d180e04000d03926090041c4039491440c21503031802c17915020180711241070341281c0107043e01c05820915081c440180e14bc0c1c00c0e420409001c0d952182020645207009602c14000d40000c4042e8610100308040005100008101aaa021110780d1940d00c403c1d21107411403800f0741411130142180340050281802180c144034010000441e1003425440c01604104409017140100300343e9400c01c1010030b000100d00c0815002d441e40f4201945c0751800442d0703d0788101007400340c00d407144903c90400307460a0b41c0300b83c00c10340680c4182c84006c032410207e400c40452251800d906030f842080130503620f1502c50040800242c006003100c6d0401d586620074010340c4d0140d800f041d0110760100700d803550002d8a44082c3d903c007404841441c6403030070a50300500300c1a4148005030800c6031004442c0101d501850841340c198020084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 572305908 1250 572304658 572304703
    0xc01020403030c0512030405151003020604030b0a110910050c03090a0f080706030506060403030e120d02010605040b04060e07180806040804050f040e060115140d05090d05130501050705 81
    0x82c050002e001d032035421529403060b40724002c0389401d00c42c01d4900484d84031024201c04200d92044641403040501080703070440d01e00c07a00000580c0c0301c4000b080150b01c60880c1001e00c0c076107107040e81c04484110034205a583d000704001405a0b40784101e8544061840c10304a89401c1d041c030440e451405100c9440c0e03041400c400d40807516103a014200b0f0101ea45c2c2c1c1c801c1314019910790030b0490645105450321500040248414400a4042c0340c14428005016003020090081144403900e0018803410390740160755604828040d41c142802140030000e419541405800e02d400c46840c07904000514450070420310980d8884011380f80c116100051071840100c03188ca042030300304080f003a4400d105403031080c80a82c02964070b40c140ac0c01041605000480a030010340e01c2c0500052144050b43d09100810241c090500802014070000c3c02181940180c00034140c85c24448c01841e00040100c02424003c0901c2401d445100704150a03007035074400e00c0c02e1629108149001031030301d450b4a0b00d0428240d81042d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 572307158 1250 572305908 572305913
    0x170709090c030b010902120402090a090609030e0f01020c0d03231305040609180303020901030b0603091606080c180a09020a03150911040b03060f0904030503040614190c050c01020403 80
    0x14030724140d038001c2c501d41c241c80e680c0b4080700f8224850304100354100c0400304000340151074036441060b48016420801703c2ca80a8650311602104d14802d411001303d1425002045c03182410411076039203407028001000b0200441e070000c4c10354400c11200408004a120203410480c4103e503008180301101c0200c0c90b204c080b0b010500c61129088d0080502581c82c11100141d12420750040e8419040d103c0210850351003030380c41c100c01a601010429041c1754031000036041c2511013100541c42004c0103005810341401038031900c041ca01c0c0c41e41c41a0200041d070300501050f6845401220240c0041c0c15524a00c0308150021130726800103030b4091a4120f2020410104042d056080080b08440030407079040d4042c0c07074807054800c0340c0400d890543e00c05d03800d000074405844648000c0d03802100003407140d07591a00180000d600d8000403682180041c001009000c2045400c0c0617031039400f49001c40ca03084510382486002803034035809110100e01600c910048000368011011100c410036060001d541c8c42c0d8490 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 572308408 1250 572307158 572307173
    0x20c0d050607140703360b090312071e1a04060e07290d18231c1b050706030903020721030809030c01090f02010206060a030302060117070909 62
    0x102d8003103001ca440450940c4001c04034000b110003155050311a0038511044140f0a4074044c20402020f0000e101018542d03043c1180307103681d000820300e82e101d842c1e84e041958103160030704000c180039a6010105008000010701182c64106006d580c0e880220b600130050300b00703c80d01d0705110742c19641c10700619003840184603480e00410114613100007266440c0f6514049801c17801a1000d0000c0028008942e02d20a20b040100508080100800101e00014054a51801c42400c5002100c0884500c9040700d14403072810a0303406214841406000c55601c10f00d120121030034000d502204012455841c841940010001c1a1181d5042001c17203031a60b4a4020181c000c3c01310450070303405807041c0280050414a00d4104089050000d122448440c5850b90184d81c202030280c40001540428000807110030024400c030a00c46004051041d9407044900029003004009040113019078080302c01070002c2900014040d0451303800e100486647d1a40180d09070030000c2d55003203048200d01b0912280c0a104c43d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 572309658 1250 572308408 572308411
    0xc040621080d0c030504031e140f0f0a05130b0301050d020405040302150412171603110f1317060f0f0c090d0c06110708060402060904020d0f06080c0609010c060c020c0d0506 76
    0x25120104220140101c103125804103121100000b50410304944c00300c027841c0054058004106c01d0b0354104140003070312112a030000c9505030002034000c03540002c941d2203102150003c000500390545594106004a8500442040042d003d19215070204080510070400c0e95031919410800b92524205807400311841d04192051600080c40c04001c0c0c4d10741c0ca00040c0d200c0c01141d46080c890559055240150003034038101030251039080d030901c0300c0322256441400034885420009020601d082c00c1c03c3d0210782c1c01075a0440d004545e480213041080c090101c0c6400c6400208040b51840540d554042a845603c950004250044501341e05103003049a056410410b0300e0140c3c554001c1c003c0000407103a078034030052142101b2540705002040240c1031000040a2410024001614000600382418140c030036500180d91240c0c2d030f88604014a4006012001c00340c0c1342210000c2c5019440e5000030003170781d00c01c0c0b009080d941d41c2d8000755900c14000c00102c0021040500f4a562902c558149141c03607890 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 572310908 1250 572309658 572309663
    0x27050106050f03031804090f02060f040603060906050f040f112a010e0d050f07230d1803080c101121070c03121401170c040621080d0c030504 62
    0x810b0714141c400f441c01006580c811445140703004211076025041001510611005235039044050040a0250300c841004100d034801840a160342c90b80303420801011611294800301e111032404809000395683c15644440c00c8508440129140145030403c40041c084c05820043c2c00a0001d90700f001501c0000f450004c0c541c0d030420401c14565006c01085c285c0d00c6c0c100f07a01485811106105078010b009001800c01107030006040790510f000c5507209680828680c03105840c1802d124107000c1450010000144410381524242565820701894606404c48600005003100004078049009050800c0445d81a80c035145c0148004900c00d25441d046a01c0100400d00f04007001d40c50a8460000d80961801501c0b241d890941d2800703591000c076520302c1050300d01d208503504c40c000300349005401112103001c0c4c00700c2000c00c684880c3c0c10322168035020300540d03440e0144c2e081080400c44880310310007004048226458202e014031003480d1040c1c243c425406207101103860522500c82069047e44214403036071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 572312158 1250 572310908 572310919
    0x9090f090b0c0306100c060908070c08191511070807241109010f12050108031306210c12110310050303073c1208160c02042705010605 59
    0x100d80c44202465440100c40c11381e003010340384000807034040c0718a01842031203009003800141115150b40301b0449078001c03070090340d4800b091042480f49180c14807035030b0014004001c00600032080ca5940d40e02c40200d58001c40750f003c0e82d070304c805600311141800b100d00c0954003000c140c1d544d148a142592541070088001d07210045441300f07103c04078040e4030986009c030003049203040c1049040c82c01154000d00135101e44082024001300c251501c152030250b1800307484aa8080c6132101c000980084862429034000c5041210961035a8900041c0e6611200003464114011032145000b450503103078009030400c081c0d6014901044060075111640180d070051445401d074204280d901e804040e40e070b0141c280094003403110607803851001d03440180c00540c8c2c3c0c010f04851070841c03121240f030292210120720090b583c201d010010061310702c3c1c1c00345203c1d070300c5800c00c00c10076040d4110000043c1300140c1d0b5030000b40140d540e01112112541c4502d44800d060390752410703000041c84503140c164007802a5115007401070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 572313408 1250 572312158 572312161
    0x201060f1805070c060203070305091b0f1c05030a0e01020c06090102190c0503030d140105040501150309050309060d020a170c120613020712090b030f150109090f090b 73
    0xc09624a50300d0860340340000c4030021600380d0303040c5001400003422400611480c4640440010158000b4620030b0b101e50300c0004081c13516200c8075061030b901681d81400c014030881d0400480eaa1002d01d00106c40c5c0c00e0324401082540e8180c03c2484900324240035040d40f0010449250165020400b1484c80d0300a80c2901e201c04c07409410700032940200c000c0341340035130006075080134001c1c100344030154110700810100c103959076175901103815035000d0f0407400e400e1070b2909021555040e414a1080c014041a00e042004d0b40c5041031b40c2c09180d840009007001c00d5140d8a1240500c00304105403427030322200030880382c0ea400041d0340c1e01c0000e501502004021400c0003145581d4504c10030000d5101d004203290203494076903074210003050024000e01c2998003000c01080075021000c0761001c0c0c04590700c44c001035a4021403403200607003a0a102e6204012005040003008080c1c4016600c0c00d412851841c920300340c18887c0001654820400d41082045514180003525401c40d16008030840c2e6010399020082d6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 572314658 1250 572313408 572313419
    0xc070f1e0c061101051501030207150c0c0308060d020102030a110102120106050403061508030924030403030b030616050a0e010c0f031d042009030304030b090106060305090a020109170c040204090c020106 89
    0x1c0c2d85e000c0f5080461510219613142c029400398009000c018030440d403540429001103003007001c444450400900003105542d41d0760403da0088501c1c1d81161040300c103403081d05140e50001350703039228500707c110401c1501248445411801d406651030264142c3c40c501d2a1768550178004c1c0180c003d0300c020b487e81c5003804c0701e1981464414240030141c0d00030710b000e1440c1c0801041030000d903080740e01031000d242c601302e0840211500d5032006140264441d540128116640d04209440c046000c1c21008482001440d20140503401100301c5038000d500741408030404400b2030040e52128031665002d481e0604c00083d210405030320508182001e8220402d0b20003400b045c10600081306c030b400b9551008000c80f01c5200c02132106d464003074004080003e08480c64140c8070f40e142c40d100b04059601d00302d0745c4e440d800300740182c9415004655000d800703030009240001068000038072320740c4184608207070310060907014400c000c030038011980303d40c0001d03005650b03d56a03050390030000c1100c1c12555005528164000c0344 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 572315908 1250 572314658 572314661
    0x303190c0b0f0a05070503040c05010f02030f0c010b01090611060f04020f130b01021c0e0405220305090906150d05060a08120c01180515060d020a0303080f0606030c070f1e0c061101 79
    0x48c641040b1881141ca040000540700c0c1507201d06940300b5440140311a80c1c200c02100d00620080c44403400118800f90600009402244203402080a102d1321841082c03464030000b840c913501c04102260b071001e6480703070700118440d80c1502a01c40c3c0c0022540621001c002c0f016040030200c200280d00b242c5003003140b2000140c010300c0103d0070400051101c070144120340303000e400054000910141c0700a200c0b170b81c88114185480c00e807038100c012401c0401c10000d50326108007074982c03101c015100e940710b80200202038042c030b1045480440c0584d94482c04140340340c44070f01018014000010846210070100c00356540540c0190149222030340c00d1604507011240301c0801c906079076034020001c04c3c0d0003e0400c0c0410b000c4000038542500700c600c000c4c1c42e034013507501c99070043c2c01940aa2a2100941080e02452700d1611000340305034000c0808100b0300c03400903191400c41d00c1c207a4003c0c04c0304580d0511460890120042d0100504e041170464580c0010b0007621000e43d411580c80707072a182210420034000a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 572317158 1250 572315908 572315911
    0x30709060e040f0c110f070e01090c3e030702030d110c030d0c050c0a24090b0705010b091513090311010e070f060e0303190c0b0f0a05070503 62
    0x500144452008210060181001c075410300402000030590180000c4104100c803004000d00000401d0810803810000c2c0c2804918030b8207241d20050601c85041002c0180450818424880035a0303071307080b1104801d0720541d8090039071840400d10445503041420400f4860000b02114980e0383c410f901c400405600001c22101003581c00b07000703008035050f0400c0544103500c258000103010301848240b00c031035503424084000c0304a010340720000c01c55461306181c0d01d00610200b9450040c0c0102d08103001c403100156054450340c40c42000408040c1c03c22804450501440d8004000f600340440ca101c00c11a0641095003910300584410103070350358a1503484209184a280103030030407490144012800081c0d0040c0e441d140c0203007000100764480103d4142107481d400055003258100d588144444080b040d442001411079190440d00c081c00d01d400a1b07207030300c108070070f0100426400c1c041d039100341c0c058040f0710503ca410544544151815282c080c00d4140100c1c0c0012440740b6010000382c10501900550703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 572318408 1250 572317158 572317171
    0x10614120a0509010e060118050603072c06100207051215010803120906070c02060d1d060403020d0f05040b0a0c0f05010504110109140906131d10020a05030f0601120c0201050601090b03 81
    0x100c3c411308d4060f0920f00108000351030703140c0600564801081102503811802500300141c82007200d59460005121442030014202d00c1c840d00040005ca5480e55000405405031901110340490307400140c04124908400e000ca6004109500b9000181072980840500910071038000200a1695118451901c0300c07401c4600b4804100e0341c0c3c0c001070250820700044c20f101d81c1011300c00030f180c2d15030400f000d684840c3c2c80700202d082e0744a2820031040507410b005540d00050141014100b042582c0c00c00f805038025405550080400414901e0302c2920804041c040590071000c0352030808001e042850180008403402d0318162003061242500d940b1480c1c00300110390382050048039810f6094104000c000f0044c002c41e40c4000d818108401d28611881045000d00880c1024440e00c902d00c08036a0900380b803802c0b901c0c03c00d441807103202e1034540c00608481c0c1c000041c40349001590340340401a06c6907804004040010791030403051000c0260158011400765100343c9803810401d5071446051058801220003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 572319658 1250 572318408 572318429
    0x30418140109090206070b0408130b0906070f020a03170a0908060709030618080408010f0e03032517070306210201050405240711150301030b010614120a0509010e0601 73
    0x100b200180d030b03034000d10a81d0320040906150200075140e11040c20000e85050344d035100d0020f508007503807030b0030022417004207a45280d107414248a8000218103000b2440042c02025020003200c00f195101c5052002542c0d200100d1a90880b401004910a4002c140500042103e01c0408284082c0c00204903120701850381e02c0b0440340341940ea58001428510110000d4489001600800108088082d05c060b0000308000500d000c030301114802520303184440460701c0d41041080c040c03060044000000c0142441c80e202819110088081354580b0f12085d04403041d200d29014001d50031b905401c10300440f00d032480c5848403404980d2803245078a06400380240880d40801042000d402c1c540b16112503c3d145003812054120540c0c1d4401d52a4040c2d902200c404003140d43c0c80b281c9291041d860304a21550a42060840d07045640d0b400282c0701c10301130701d000d08c200c0c251880c3d4840150300c201c910441c075131620180181400c04c011800760a094034050035a50a14854010f442400a102c0e03040b07031100701c0c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 572320908 1250 572319658 572319661
    0x3080f0106031a31020a0f23070c0902030a0b0103144605010501140309070612110705150106110c060a03140c120c0405010c02012f03041814 62
    0x108518211308071140c0000c0c0011403420807202c2c01c0e074020b04182c5601c120015030340322102e000c02400000b0a210640a200c5841002a04040c0004604021500070440541d403500a401c0c101544407036035210a024500010800c08454010307080390014130800c1e02c0c240850440d101c900581d04004848020802001c61000b1100c000382c18101c00404884901c1c446603124078080c00e651f00c50380820f1032204507440e05c00402c100d5074804070118a403000512901d046007040841d240c4c0360b903030610500d0700308910b02402e143d890010342c1c4200341da440024038036a03a4104a28006448148103c0d401e21030209190000178400d016000d0b00068403140c00c00760580b400d250b803c000898203c01c00520405a40c0c49902c0c074400c103d9042c80c1c2c0150070041400d51a01d41120340d80b0001d0400030000346250605010421080e600480c82c01000c42d824245505c80300000c41a26000c40700589019482220f0301c1c207140b0780e41101000074825a0603048070220b84201307040010003550010340030144201440310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 572322158 1250 572320908 572320961
    0xd030c02010807200a1a012d26060708070c0f050c03070f080c0a05010801030308062814040605090c03071e03230106051804020f0703080f010603 64
    0x1000c40d8820120708101c1c90310000c418801c50600704900f400901c55200e07017403903800c2c082d08a61808400c3c0901031601002d6042004c00d6400c3c40c0c03260b44e800c19150000c00c00d41d10a948040c0110040c103000d01e00907403d0186020320f1189444075014201c00c60240c10003144040344200ca8a0788926859115081c918500f40c0d9007884180441e102074840e40502803035561a503500340140383c020904411700d00070a608082c04a41030219001d002c9203c0e02001e2420003069812400071411240c05007007081f10b03590741c01c02046002e500100c005030a120349404900d40b00c5450024001030754051859140502ea2171802d0004960107405881e5200c511100003507409201c0c40001c0d43d0080e464941400c6c151040344042941180d003800c1d840c00309071106080c54840c1036103110459902042c040f0100c081d4034080010b08248115440103c840d01829411201621942c040301c5090381d0513004183c0d512482e050041c070061003a41c01c29400912103000207107040c4a4000d40747c000030015a207403004103146c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 572323408 1250 572322158 572322167
    0x2b020604022b0611040602061e07080c1902010e070e0103020604050411070507080c090a1b03050c040e1603060b1c0218040c080402091b0702060a0207050a030c050f0d030c0201 77
    0x3411002c15040c0500d44000001e000d60103081541504624125222814038801a0800c10010001c800c19480d1086002c0c07841c4030b152615400c5045814503146039202d04450041c00e210304281c10b5500c1190320290f681c01c40e4150b00074605200d016090b14001d94841c0610000c900c4203100180d07109101348424015440c0c942c1c000707000901c42840c014175007803440e07803880c0c01c000072980302c10440c1d00031380302c10012810862542540611920420024400960184400c040d010910130b02055a03502c0000c0c140400003084034083d060a555030101d40c41c0400801441038210840280040d052103070000d486040601920300e0009000782d0f0180d0400030b4041c40b8001d401040100003001d044469101d201c1d255445200d00c00810b0baa50740c1132900c0c0500600050900185c016007140e075485030f1048650404505841c44650f0450316140d40315801c3c40120b1a0900e80d4200b5903210002d41800810002c1e000001c40880310142c40c01483c5104c3c542c2000f61a180b03c00001d404142848000801980315 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 572324658 1250 572323408 572323459
    0xf09030314090406030c0b0c0706080403050a18091a0a0b07050706050901090512010c0e0603060a05060304080403050303070503090111040605041205010e0106081605031212090705032b02060402 85
    0xd0f00004190366079440b41c0e904010b00d544040d903070038000074002d1540c803414080d100152043d401d00103114182a5801031440c403500d05e80c5410442501c410180e0443d034121444020401c4580c00d00074070090303014014a400b48251102c1c0700e9051608001801581541920703c03864024020b0031205280007000d8500e40e011245282c1080b44c10000072400d59170300481c000c1e8414000c0000502286142c2c0041d18899907240c5c0a03101d0321041c403c001c6c0c0b40d40c445a40c80103407101600d0458498455242c00c8120740555080240f40340404020442410b520501461103050180024009001140d41c00c14442c4a603000b1a000103404210600015208520280400b0b10640001586c403010740340040c219502900b018800d40c00420001d1422621005808040e04044000e0041c2c2c01d020070070302c80280b2032036100c08140d04a0000085100d01e050102e02c004080c00b40030b5545400660044074001c105044100c140b002c02140b00b0583d01e4400194103216680c0549601e2809160b0010513181084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 572325908 1250 572324658 572324677
    0x60f100f030e07030c06020d1806050a020c0307030308100f06120209060d091101091a1b0f240703051b36040e0a1709120a030207060f09030314 63
    0x40720000c501d044142000f00320b00850042c4840316107942008802070816a041003500204000214200c083c0134080e00ca083c1113401905000c1e0f650461400164205681d6001641d41409107201c00802d241d003040102e803203a2201d201100c80b040d182c04860217052481e0040783c0001d01c01400026000c51981e009088804000b00441d0a00c00c500c000c02e01030f04d1b0580002c0b66144510417205100c0c1d60024001001f07044082c03148540d8040c0310354082020300400c00b842c03020f4085102c44051000041c040e140c811701c0707180140d43c07456601c2c0210004012101203c103002c604c074a00000d05451203441440c0c0105451080b000c41c4145415100c0c0c840d8000d42d001c4101e08202100043c00749001d40c849683e0380c05c100440a000f05611402c100817207850318028042500200c100b10001200b01040d108036803142030507291580c03400b201203140c0c8100101c00d00150b00c17814210384249900040c010049415941d00e81c442c0c1e650f180c404580600c01c2e84401404034181c20700090382001e440b4080e01100d00d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 572327158 1250 572325908 572325911
    0xa050d0311070609060b010e04060608162106031e0f03080a020c030d15080616080c0904020f0c010507020f101112011d06040221040609020405071106060f100f03 71
    0x2c40603103c40040300c090003800c48440365a000c000d0348658100c0314407508803104845c00c001c40ca240500c0517207102c00040079041070a00b00c3e403011061a0140c030020021400c10118140814045d400701030007864580426a900c004514010000c0103c0b0300341306d050581d11917002e8080c0c2c800f50303034180d96410010744583c3d4059000d204d41190340804101400d40f4030359009000c03a8030140e6101b99464040e40c2d0300540510b41080c400c1121040521000c004c11083d10324007003400b41e8030300d04c104480d4041c0c200c007554014000038144e052041d60700090005031540a008010584032208241c1c1c1d2021207011041080d000180c107181e03650f220383d010341500700c0d044050b0351404947d4030410041c0c9400760060080c82c5001d8442d40402039011003880d40c010380c21f0b1411458100628501401003406407031820306002c04200044c208111a008044019800360090040b030506004c00f0b0100883c016082401e40305e20740018909180800300c00c521224003405210303441e415424121070360203103102d0490a15 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 572328408 1250 572327158 572327167
    0x807110105150901050a0b1b030408060a06050f121009060603020405011e170712020d050109081b03040e0a2c03180301050610050a03061e05120a050d0311 68
    0x100401c0c007980d445951412416500c0c00d0701c9404110a140d4180c12282c01803081c0d650030f07c022090902141c00030f4504c5000c1142c00020754607080c0c6103106640000d8410701480051095951090308141c06a41c000c9604040703131000325083c0700f60009180052041d9038800050004100000e6002c1e0030011301401000c120691a600070a058a5007a0720448030380b05107a2070896040d4502480402400405510340b40500d4031031007442c0d8400c0b4a00032080700c108020300031011943d0f40403000e540f40b40d009000b07204108460900c845941c2091020703215140c01c00091041c2c901d00030080750140da01c030500250050311005050310086c0000c05920f84141d07100818818040000c00740ca07211007862200a5079030b5081c0340d03810b031055400c201d0124041e0b0b050100703211643d50b440f001c174000348100740f0b000c645401c170f0501c3c110090075656003e21a030300d000640c2c5809010040814400340d91060b5940315184080822182d5142c10180019005030440132030910203d00c60b4200c06409003a2201c1c140c01c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 572329658 1250 572328408 572328437
    0x91311070501110a030522030e01092d050f01020703140a021806010905041107170409092102210903210c0606010f09060305060406030f030815040b100807 68
    0x311078031201101c100c000e020075413480040e4180200c580c0141860a0b601c800144074070400d00713007019440c00a00b404030b4244103003c680d114945a100820110540007480c49034900085503850044031890b4981902c2140440d8a05001c00b0403514610180c0c010864286940c491410b1056224a81001c40c018010501d02680e130b03010307204e540341c8a40b01f802c40c1d8505200300003400358941c41e40041d00941c20050200c000d445603109844c0501d81044184886c018030510600443c4155040400054603010142062260140000c3c1303d50854400f403164546110a050703075104183c41034240d15146029a018408030044080e00c81c00d100a8202d802203070350001c0000c0a111700e201c1007101d0b035401283d1843c521908003d4203030005c400b800c1c4901340c000b00580c01001c2c00a1400740c1070034140c950020036a9038865502100045d601714081006002441c50002d15440068031192581401d8650500c5646020f105620700c2d14401002040710b4080f03000e0640701044020014000e1103c03c1c12845c64 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 572330908 1250 572329658 572329661
    0x110f032410050d1d030f030106081003020f0405090c090c04030204060b0309071a070c06110c010e030c0f03070302151207030e0714062215030e0d03331505091311070501 74
    0x503694a06c9106074607903060442c0100380500041c25054045e5100e42c040016803600c00c0f00001c4d01d2425070340400c8550340c0d4080d2914122010042a4000c195a02001145d1341038a0107001500e208540a025080c3d0710181204140800e0711001d001e500a058200000021060514000508039100d54146141c0d034807840d80c0c030f0b2400d030301c00c0010401d0030403003104910041c04051090a0242030010382c4030380b0003011070355484284603c00e01074141600c40c40c4803a68100800e04c0210380c000c02c0801050801c60008800d07400c0f03000342190194048003c10080d502900607075072080414802452014a4924000703501001210b040e074009074100142d9000c0080a0f40809040900c4403030106828039086280b0141c18404140760201881e00004501000d0301143d00c00c1c4580c0507140101d4034803441c5030554044000450301d801800c0020520703c40a41c201001082200c04416035140b544a01d5030060380e1600c11000320650118100c0e8034800d10900690009200c103408006081c20580103549460 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 572332158 1250 572330908 572330917
    0x6190c0213020c0307030905040212010b16151d060106080a1140140f041409060a06060f0c03080702010b030a030206040203100915110f032410050d1d03 67
    0x183ca50000299007060680044c00c840080c007080d41d0851414084601980644034180540d180d19180050411803100c206001c40811a4119200d03461148402502c0c9005010f40400100ca07030f080d20707030615240000428a581221042d4591060540c0d0380308545000f0324008100100c0d0070000e000c0d405100340003201c60400d42d142c050143d03150b00c00101da000e90352500550800c00500042c0340074851400032481d01c4402e034030150b61003042840110b0000b00503205002100c0c4422603204108009500c0001d502801a5074001041001c95200c040445c1c02e02129000880071859401498001031300ca0340c0295071000a51000041c1c030303041c03c0002800c02d010a0000d400692054080c8801d5280a120841b80480960f5040201e0405075039040004180020400c030255034030707400c428181c5980300488402c403034070200c0d030780c1c0e02d15020b403289030b0320b00208009070300150f4031400781c3c01142400007051200e18104c1d00c4041c102003041c00c1c10000780044058405d60312128001078022084100b0261 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 572333408 1250 572332158 572332177
    0x60e0403020a03021507020a030e0f03010c09180219080a1431030e0603040f060213080105090604030806240414100c1a070c0f05060603010b06190c021302 68
    0xa0002c01c03080d050003840c3c404442005148011000d0030b0040460300000d0a03140290f150900d00c1e11031080000045000132440d011a0700355080c01004134526500000b00d80560300d855190042c801e0042c4050310890107019450b402c900d10f0711200986140c001d1480c194020392918001ca4400291800900d6211007694802000b07411007a28248041092001148010241150029103101782d140145003da40d40712542c00740c68000041000e00019444800025810407070039541c4180c1003915481c20740d014801c254007546030201185880d0b002040c40c0740200d41581d038442041d2200410001c0707420020050144078a100d080c0c0c000e81d425081c01500040810707105a01c039103071051003444042c00d5038005141c100701641e94070000184009071744a9420485210307117174140c0d8440c10203996407569008060144603206a0303c0d02000740c000745252195000b540280101c2070b0300781c1840068096100c0e1102400c48403802070100500c90101205494001007000c030201c1c3c42e0f40c2d9140102d03488110710 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 572334658 1250 572333408 572333413
    0x106020c1c170306010219020303030f100b13171b040b040605040e030d0b0d050615010302071a0a0b010306030507032907031a0108040b0708040501062d0b03090303040312060e040302 80
    0x80000660701403094203551f04110520303410b008603a0380001c1c4c684c4801801c04210030700c1100030540794003124408002600042e0704007944c07030b82c0034810502407281c80d00c2140da15401c5038401a00c3c0742c8000c11700c5c0c0200340707088024001a4403180c0812010b04100384c841e5030069501c00d800904ca0f9190300030010717030010000286550b04031f80c00c1c0740001e5480ea06801e0303014a1344032190074001400000c06030303840003005010810410300040120081c0c418654082c20780312401d4036004084880100160207040c8130b10040002c00c0442c40190f096070032030321011b02240c00c042001c00204030547e0a01ea1040365009491410321010705c61451142c000745c40d5000000e03610031403035254034010f2003485002242400c2c4601d240c43c05584481d07140c900109880100030a040214003048425041040030b002040d01e541198501040100d03040c1c11007100304404c42c0f00c0c5490004854511000701c03800b512042e00518a5550780e51025900e907590b04050380100c2e03a171000001a00310111500e2402a0310aa01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 572335908 1250 572334658 572334661
    0x111212031e06030a0b1b1c050105030c0105180402120906180a0b01060e1206010603020c0c0a0f0b0f070c0b1b070501020d0c0311150712050106020c1c1703 68
    0x100c030111003a580ca1281d0a1001c5010700485540001e00b40d03081542c000e41e042c0c000d40e281a680350640528081c51881c242000c039500186070003182c0640048a000c40c070130003ca0303a8030810142e0316000c1d10101d43c04610100039000401030407065615038003101170000f40c40c0c124110418404904202c820003c59002041030024040c0e0a21341031101c82844801005010b40c07135110303408441c006214240c14030090310001c000e9a104ca4000e00500301e4010b06483c103a6075a40380280c041d5021740e5592045006148110200d0f04d0301003465429501103d40c1099401d0600e100c404044d070102c1a91540d1101c01d100c1ca000081003c02800d015215005469460b5051040c1c02c17031200a400310803100d65000003100f402166030000741c04254441a240080310b414080c2010b54080e09005580c41c018001c03034800040032036421000c00e015003401e5490007003140e0300030045d10455000b8080d0000580217800178440b245080c00005205001a080008406009030750707100b1020032503504035000c12030200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 572337158 1250 572335908 572335921
    0xa0212030a0204150905011d012601050a052205101203050a080c1e0306040f090b100506031006031e090f031103070f0609031e02031e1611121203 64
    0x104c0e0502e00704024204a040141007000203000020104507503002044941d200e070b0440c2e0321407500d00080011701881d480c911000481e080c0d000c40424094640681003001001a950824808850445025958551040040c200d10070f0282070050b08106180c07012400104491080400d055a0f035071180e02c6403691074202c49800f810070f02009002e0784024000b48119601340e12030038900f1360101c030013420b4166250b542000140c000c1000011440e4014584001e8208000c590031203d4040c6843c20102c2520550b26000c0155900c002c40d040c04005610794001c0005038003079000a030b8880440764007010111105040c040848403281f20070390380940031070040790615811072201d10321161401c010310300d8190f094031481260219501d0051404e640c40c402141490b00c100741da0001c8940901448581e00c516641c02076807500414440d042c0e12694401c18401003800c2d07021100a5007034400d0f8440038811b20f403250007403800c241c2e48064202d28410143d0010740001d01051004c400070070055a12406c124 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 572338408 1250 572337158 572337179
    0x60a03061701021908010303020318010311040305010f0b19120c0b0c06060907020705010f0e06130f06030b010306030b0411030a060e031b15130c12080913050c040603020a0212030a0204 81
    0x210030000074402c1709001071001c0b0b079001c800c03200c00c620240d90b8076034038030701c01c00049009003ca607440d60000c070307c0800c0120402006400c801422408802c052001c10000c00070016466510f509105000441ca40104034100051800181c414000c800b50008260303145d102070b601e5403100414030100d4001d4420130165242c560440c0360800d019100800000d400c140000e05500e000124090501810700703420301c0e03995124002c4440341d10410300c17107804181c0d035200d100c0c002d00035034083d60021074102481c4440719413081c45194200ca400801000454079076444041e46044c504210580500591080402190321070003034021f4590004029036840d40858030145801c0e40700203900519421510980040710500729005401c0801d29422501d200100e14140d41d01504540c8104480e581c0400c95200348444040506134205043c0c550410000301c44400342c084441c11140000c001000b4001440342d40e100fa4064400810140102c540d00040d070141c0340034035041140c6413840244c002906100039905d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 572339658 1250 572338408 572338447
    0x312050d0906140912250c03060c12050f070309020d0c082508071a1204030507020a050d0510050c090a030c030215040b190e27090c0f060a0306170102 66
    0x1010003030200704d1710040700c0350f840e4410b0854240e8107a0002d1850480303507880250307603d0010340c0700e002001000e5407803a2140107022000f0064002c15103590b45143c2c2c008240c014140f00f031801410702e171940d03641c03171070280d0081190201c142d130001202681000003c0261510f44094111400241001030034490341580b05c0e01141e864200c408100302003000100c100141407002da5000c420440041d5240941c0b09603140950718850680407800c60500c4207141d0042c00805000c1d0003940c0c100724080c5c50b030040c0000da5407006801040795001d440c01d0803d000c10360340b09503040429074010f240b40c460a600042c2c503030740710758000303403100001e6034010821450031010140e040f16a2911103414985401c080f140240205a00512155000403001072414404c1c05403c0d01e1043c014003902503030b2a20142c010903260005074102c1c5110b0030001140c4400000104020b0b00300d80281801c1301078a050091000b290410300c042014180c82e000045000c1201841070003e101d1460001a1102000b01e00d60102c0800f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 572340908 1250 572339658 572339671
    0x308243609060105120303131e1109010b0a02060a0b010e031509011b081b0d0f0e250b0903030906030f15010c0b0c03041a07030b04150501090312050d090614 69
    0x10005c210b066040404010b680e8080d023102d00c0341c5240300150410084a0866246041c0d4640c031490003102000a0054442d090010550369030055a0b220030191800d4412503804001581c0300d0800510340700d803070381c101e83c0d40b2440600d0a800200c48440105c2d10309681c0f8221926030329419401c01c0380c1e420091080d100032080514410802c803e1520020302203003005049001d04042e0110b2481c02082130f80115941c021789010200324035024403803000e00401e4210ac051002d8040d02240045035021540d014100c00d2002c0520a075152600c0c2031000142e1002940503054001800b4031001c55039142c014501c24921039122104900d040c007520601c41e500020098140100044424040348201c7c10b0a0b07446a01c85002c0c1c0c0d9a501c0c4c904000f408582c0c0ea001140380001c91000b002900c80e41500b01000c2d11505031001e1041d41400d90380106010a240640c500281c61440100017141c522162201150841e0800ca03291141078504482540d500c0301080c0d40154656940d02801c5a1040b4003d52000c0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 572342158 1250 572340908 572340919
    0x302100e03150417030a0b060a110d08041104021c0606030c1b03120c02150c0a0f020c062a0313050a050103021227031201030308243609060105 63
    0xc0d003699102003130141400d4a0f114602c02000181401103603078004c50b4595002003185e501e916510b28000e10005480c46001d010340248800d41c52524000d215442c09154082c04580c1c82c0d16010042c8802502301c2e5014180e604410180e054900da16440380c00c3c0a4881540c001c26087c60000019208040c0e484420207100125104100403030f80c0400940301a102c458800f007060380040d40c04030324003c9442142c078403440d0f40e13405001060400768014102d400c016101c542140004410590b111807403059005d0700641c00b0002d110566250702140c8241e016a03048c1000c01d500d0f99083d1a196403c200c4804000e170039029024801e604c0d000e8140c20080c4000d11b015490501c503903401310710220014126060307521400c20340c141c040c6586500103215140d6082103c3d00c03106500d60407216108284000e8000c103500401158014507030910b0401052032161060290850b05424048550000e07600e0f9680c0103500090b9100300d200e41042d070383d80c0d11210103140412381043e02c0864280030040c1c0c42203200300b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 572343408 1250 572342158 572342161
    0x18120f07030f050904020d0504050607020114010506070206130f14120a03030902060f07030c1b0312050328090b0f061e0d05010c2a1a0901060302100e0315 68
    0x114154000c0350200c90303051505640645800e0b10a9510340202c0100c164014008608810b4a01307031a0310640c801d500410450300903440c1d40100ba4202c4604810403001c194113080148101d0030094010b20f10148003a0011b49400b1645030090300000140d0024031000b0560171041000c0e03000da002c400207581084550410743c00d03590031070a990b0341c42c5034001000d041d2116050000d42d0b4814099407124119400056500d1019141c003c29110150314202d980b0ba104004580d400500c00c0c00b0741003900da001000c040c1d0b0700d8410006440c203804c01007480400c036014002141c00194045200b405c8210050300106196007a480e00e1011400c0c02810300389040760a01c100a415a20000000d0080100d2181941000d5800340410344581103407601401d59801c11862400d01c651094986079000003c17482540c01d0b0300110307a40c0c0c1445c5180d0102800c2000540e260080131040c140784250000d44100001a070141e90303501289088000280100200c0c228030814009403e050020205480c0e51000102c8207 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 572344658 1250 572343408 572343427
    0x60e030616030e0a0503180909012f070606031a0a0b010210091103071d010b0705060c031806040c1502070f093306030606020d0f081504051812 63
    0x405440c2074004154840c0c40d01030300d9910600110303820030741140540340d03a00044414800d5080150030005d020f80f00c50400210080300620404010302d4440c00d010007400c0544c0c035600071034408045152404036040251100040003031003a80010761190100200700c076144d81089201e0b840040c001c9013a10f0928100090342c0c0c0c0e02103119418400512030002d4210014202140800e9400240640600c02d003080402c0144a041c05103660452488a60595a0300c9214a01450142800080c0b1584c0160041045814140060340d8060301c230b40303603040e45006000303100703442c050060f1000d88407221081c0050001145040242c2c2072011280010306aa07494541007030310008180c411254140e68981d180402c2c1000711500c034480240005052009980100000c96945598402e000100c3c0c6880750020301140041561078503010141c5440074074603100c110a541c5450020b006a0300b01100500002e00c2e03558034450280110040001e0f00001003261884038035198141082c0c6030305500c01c4c4440003030b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 572345908 1250 572344658 572344681
    0x5100e03070501120e0105010906210308010b090d06090b07080105030c030303040609170a05040519061b050c03030c240c07030302160c030b190e3013060e0306 70
    0x495800380791102c0d1110250b4585001040e0303a0105c1001c65007048000141e4000740e8000741c05845031003105994882c100034200e4005c250085004001c101d20304010480b4608050203004080005446088030000d5680c8403001c4030300e101d03800c48150003c0300601448a502002040c050001540140b20540410340001c0d40e9000040004042c0340d1203c0302034041001c025030112001042450080d00c50410301c40240064000c1e0181d540940e0003441c6c0140034440d4000c0c40c2040300d2203a19030040410280c40e25900c40e52101030242e036540304050300500300340c0f000c00044c10150401c00c080d11105c180825404200c0070b9041e1902c03504000001440854004103048035030843d818200140d90381030310b07450b104549054440140007a024410000240110620141d100301d120282103139101c0000b61070a811034030a810085800c0c1c2c408054a244002c4e68610b0324481c070356900e081c0200c0801c202030303501164440443c0c07004059494208110340c0360002d60580e40410110041c00c802d1600d00b00750403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 572347158 1250 572345908 572345923
    0x301090212090c0102100902030c0d030f021218040b040e070605221508091903050d050f01151211040902071401141b0d110415020a080910050c01090c05100e03 70
    0x150150387e40c42461085650401011091400c09019078007410302a04015260b031624003240030150056002400c08c1103280e42c00c442046001c10047c0181c0e036060002d0000074a18442043d401941e2413445070903004080107500020700c0f003543d03200d617a07082980203004441c100c620110f6252201c880c040c001d5a1120788580307100c10892070084020b550744a00c513440c1035001c030340b02d162442119440c0c009042e4000c00418400f00054024404c903150f000d031316440c04000f4032070385030f1000e104410202041c0c410784100c00d003070020030070214680b0720010020800380d009510943c00298002400010084407015410012000c40020403140400ca0300e80144650020141c84903081d000c0302076420000000142d44100180715802c008036145031510340030603886801040241c0038080080206a413000035031114a03a44220450f0030040004140004142954004014054140400c00039401d0034811544644d0240980070039051904082c00351145104030300c0ba04101d69154903a800e5100002d404c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 572348408 1250 572347158 572347183
    0x203040c060311040306020c0d091409040611040504021b0c01080f040b0a060b030403020f01051012060509010b030f010b040f0b1e012a020909010c090905040c09020301090212090c0102 81
    0xf103048203000303901c0b880341d100342d401c02007030b0a02c04924a6a1510300198400081f0743e561905440c007a15100034550015000b202c95a0024000c00002d00058141c0c0000000408080c0c071282000d44440014091740c00c008284150130824509485a03a003080080701300010080c00e203800282040340ca0703044d400b50001d102030405544c0d000170601d0810507030b20010060820092a545a04051400a44441c4010385121030342d030800b000b042c403070b41b41c6564035070072101061015034961116a40d42005424000c0c8101c5055503100855002034034140100701c004411b010002034609000f10400007150310fa00e0103c0606458800710100da51210700035008040420b07a1114000c015003001200d5009603100c004405070700302c5808a01440714070a82443c154821181c40029903a81000e0394200d0b105264030400050004004110110080d4016500280240810b0449984808640c001e80e40203074844c0103ca42c0c000703100c4402105c47c0c612103810181003c0640203080c55000000d41c1e034086000e08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 572349658 1250 572348408 572348411
    0x216030c02280b07020105040b0301060804060b120318031c180e060109051207030215070201090504050405071a21090d030b061e0405040c050c06071b031b0c0e010f08010203040c0603 80
    0x44c041560b000c1d4050318014801914240e94943e1114030043c404c1d901038604031141420b01c0c02110081c6810301601440091000055003000700c4840500e60604a4a4a040d014050081054451800e4a0204148204640b50301400100348050305055031040e03404400c21684060038003581d60380c884000030032500100e540300c00d8464a4000e072810301030740d680000d606c02c036920904521440100080e20155000762030300b10030165140c0c140010340310125802405900203110a0001c2082441d400141032069200a82440e0b418020b90000310070002040280d00c038046d0401840c0c2608000f0070b00320075180c0c038044c440d0310404008202507008000c92039481810b004441200c10010205480051900130414040100c0034a009080c45c1d110740441c4105010b0880001d00041c091000c090140802031415118242551003c5600404031b20f001440660629030001c080ba80205001c2d020b45076070610030b22654035016100510030103070384c040742499006104200c0401d0682201204a4401c1d050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 572350908 1250 572349658 572349667
    0x806011d0117070312051306021c05030f0606030408070b040506150f180901020d06090b0f1c03030b010519030e251a0403020a090203191109130216030c02280b 70
    0x406451500510f00061f0395001551000103986038000b4450710440c052010009203000c2d82b4a0071265440100c0b0025401c2454101007003036800e020300250750050103492020305281051b40c070402e01190903107065880b90b00050500c0085880301e21000035403601190600c0e0b4284864000c260007100d80015941d40054100018140a40139011500c600e40720306820000301d034031080c0842c01000100145401401d03103c1e88034826082081030000060070307582640c110380141b03a6040300500141626681040000e000c40c0c00c00e07008204284031002e26944011507030000f01c6401d245016419605e12004a000454021904542c40702410680c0c680003d210820f10082c80640480d00c03039640000d40182c0c03c003400041d507802170f0380510300484104001542c480708228102042d00d20707100220100d140c7c20050000c1c01d00c1e00003602071505c925001e025003002840d4118a05445100300140c021543d41c541a0b011803a00b039540189600d130060000c0b110300301c2c1420400c0e4066541c010901c4e030840005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 572352158 1250 572350908 572350943
    0xa0e0a091106161a06010504270f09030816121a030a050706021014010603051504060b0c0f030a1b2d15140c0f040806011d01170703 58
    0x10303072003003500c03001d04456510041c10721042c81c5106142c10035941c8540100c07502c05401c0890340114082d490503550716040c02c2c1440314800010201c0c0c0020306007004000407030000c04200c0d006580e544c40a8560000e0001c80c5400d000d0070100c03004109204224a0060340400c2036001140c1c00c400c01d21035040081c003510762844c0b0700c01e486100c01d01d03654103100f8241603c00f08400040c03401c054410503030070348a008101c410b203042600c0044000c5180e60b1085001030020314481e900080e440707000b40340d13038052440d03981000c0380445206403c50800d40c0800500782079141003c11807002c0500301200114a0590300751001401c031940305d5440c00d810920b881d40e840c10703c00004082c88405054451444102e054030b800390b83d084050072408c90b2140b0034a00400c18175003552042c1184540d041d1005a099507884a8041150b0300c4018141043c800c24030020980000400c8580d01030888903002c220a10b9040c0d00c0304184120580c4144152210049180c0b444103000c50384404890f40040c100f00c40c807070703d038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 572353408 1250 572352158 572352173
    0x120c081804061d04021215070302280e0a050604031a04020111011407140703020c060d151e151403180a150c0215011a0c06010b030103020a050a0e0a09 66
    0x6a0000c44075681007100f02c040744801c100c07640d0286108903010800195841100d54a88840440d040c3ca40a410310028003058001c0d0024010894440030300c80c0480200071600203641c82c4041c1c1c41c0002240620310741c0640c100310032403030083c08044510500306495580d41c040000002540341906c45c0d1a8004030382164020170101c1d40c8885079000a001e43c10740140c080f03a590701d0454101d400900342001914405505204484009030580d002e00500343c109014014036038030200e000303103c00341d4928641ea4400b0034052000c2c0645050310301a10310066049407024444002e0b0400304100c000c4040424800303801824440010103040409610380c1d5076400000c461000c020640102c2e8001e990320f060820400b041c200d05041c9603400c04000c5c0c001242c00c200d90341c01c25000401c0080070808014005425190a40340c02d12049100f894940070790000c0980c10702101381d00ca01e03500351010006208501d03103180c002003c0c2505a4a4a050b949442e0000381c0d403850150644141382c4d500c400d00428402d14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 572354658 1250 572353408 572353421
    0x60a0e0904060902150304050c010e1504080c09071722080a030c030f060f06080903040f0803030114010c031205090709050702100506090609041b0509040f120c081804 73
    0x4029880c107103818205403001e04100b000480c400c004040c0d880145101d80300590707001c0e6400100038400d801c403120041d40c0700d00401c412240d000707100d59011408030004400900103084090301a00314644090148072072a42c0150224041c030204001c803446410ba17199030740368004410728511004404017201240c45c0366019201074202c46002500d000501c0d0035420440340559a03640c20400c03060284008400c6a1a50148104056844c1c40c200541e03031042c0e00391900034a45400b5680740590b182c2e40300d01620320a5015615580001c001001444030140c2051414a000c1c241035403010202c0da0018000d528030b500980d085a610000300da000c440c00c10528007e032075048000c00541c100104065602c10b1048004120141800001882c1d401d10365600c1d4000c11000c0d01078082c46e11240d41d110120160440104c880740c40d95000021140d5600903020f000342c1c05040d1040c40120a4200009200d203100c207140c0502c50655200320005090b1000c694000c803421860b0200001d80800041c05000c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 572355908 1250 572354658 572354687
    0x40c0903440d02070305031e01080d0309110307030c0501080703110405060d0207051002030a060519050f01020a0b10060906050910050f07050318090f0f0f06120307050d031811060a 79
    0x3c041215010103070080001c42c0950038908441c82c520740000404d0100945c24010014160803094200450030f0007500300f450040e114821058250b000785d00405e28142440d8000d80701d02c0e010100411040d41c0190000390407184500d02841150f402d8038800196226511800b802000009010104800b640d410388038003a5224003a00c20301c6600913600c6020350000d54060520303a21f0107000240c54600200b2111401054500b0780c0303c1b00d80b9001c03c2041640f40c500810b81035015a2004c00c0000d200340d40e103284200501481040f03a1814460020702c5080c141d0010b02c1404020803002610381d580b00030000c940030b500d02c2d00a564a4000010030598011448004d129100100c1c1d0710407100300416610322660300a03500d0400c1d59640030102c11030000700b83c500c1c0494444007804541e9856082e407106070306ca0009404449140e4000c40c1d03051440d44030308002c1e2000e400c061545004a81d16006800e146054408d40a009030903d44404400c3c5445d03a0000b441183c00041000040380078400c01c000080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 572357158 1250 572355908 572355911
    0xc05030f010302010c0c0b130f060c0c1503060e0c18040504020d0b0408040f06020f0c01030507230f2803060f260102030103030c1106030c04090c0e040c0903440d 71
    0x1001035000421308d01460040c802040008400800c2d040e114410b13602c07205420045043c0031070710b491560003103590f4810405080685480000c01d400840c00c02e564002c00a043e11540c0c1c681030b00403040c139885a5410968132950500c4103100151b501d0170003045809410003801c01c05170301c483c82c0c00300a40c03040f80d008007942c103028440022842e0300404e41070b0940100c803040d00c81001c916001142200d008490780b20120320a4051105c0f50511020083e48950382c03000701a00d0005014801110703030300400c40100581c0a0a44010f4549030010044865041c103401d060000302d003001c85200070310510707018000c070062608044821040440c135008403100c1d08840219601e503182d0500806c01c00e1060015200a070588481c00000e0518000b164480c1b0044d6416608141c2482d0b41a006003000c481000d00f002080016240165100d100b20010380010340c0301c84020350b14520702001c3c0502450b80704041e0701c510b0001c4242d1449166608080464051141b00124000092450320340c00f9000c18201c1c901d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 572358408 1250 572357158 572357167
    0x3160c0c1e050d0302150903120406021c050106090b0a031401060504080d08091002090103090c29030c030c090a080d09060e1c0308091e030d0c05030f010302010c0c0b 73
    0x75901c40041604015000d40079118540d00c0b4820302034000b41503007000300181d002c501c1c00080364421003200d0b90403120f03c40c00d503450b00a000d8484800b00c001a02d098800315170004403040105501e10503840e20900c1018140543d614141c8050240542c522030081403840020381718070954820b51210700c2622552061001d01d58487c40b0041240c2c21500030850b0a10a040080b482c00c1c0c0251300c81d42c81492000000c0090b100c000e40c6804c040d4000c80b0101c0e0601d038940c9000b800090040080402401c01c405d020100e07406002c2c039001d2004549800b00d03160a104106121078841c0d81c000720381e4482c01016000795901703002c502184841010780c0c400c140c18040ca00110310265401451001102e100390b5805454600e003000300b0140801a00c03218202000c141c0018000a0107041c03205d40c03000521017612110f1002c40c1289111ba00500b490200c4e40d00009101c031100e10701d40c8140c0052880600d0b11504524055006500108046c003001c0e06020700003a04c2e02c00c110559013030401804141c00c41ca5181d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 572359658 1250 572358408 572358419
    0xe0a0e01050c0a0e06040321092402010c030204120204090c1a0a121107031107090c050409050a05070507150f1113050f13020d0b030703050a0506010501031103160c0c 73
    0x2039402c416400d00006180071044556458044161407c1d01c0d00034407015021071004c034140d40c02145000c5844188405868000748400d0fa0310020900c0c007810115090720340031071802c02801c440d50102d26505051061000740034402400405004d401d0b07040e20001224017039030501c1c0c090a40550b100803640e2003001052410744501030050200c0f101c031a244c0480780703090140707000192001c680920310884406d0100c03101280c030480108600110390340544000640315600702c0c2c20355002c0c003c040c7c042240003604022002140c498a5440f500d03804041040e401c080000500f58441d080c4090300040c1c01c0b4002c1c40144101d64050220b030b5400c01000c00006001410482a07600080002c4041f01800e140c0080d25090107500050f020500030481d002c0001d8000c0d07440000e40048010303c03c0e507607543d00c6610094900300411000356000c0c000500c1448818a0800d01d0400142c00031810142010314003000100100c0649812004803034640001c241001c40444030040d0a0301d025144107540400040c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 572360908 1250 572359658 572359681
    0x9030a0b100314030a080a020d090606080d0206090d020c060c070b0414091302101b020a270e121c05040b1602010b0f010c14010e010203070305090a03090e0a0e0105 72
    0x100d0744903d403980440d503000d25480752240070f020744440108041000003408812154000c2207004491840084c0c2210306844101c01c41e0340d541c20a40340b5a02c000c07070081c0d5140e0101304c0541d000ca0740400903c02a00c0102000b501d503226003004501a035130110340c11108140510000000d0a1283c0d286c076246c2d56501d10f0fa17440f10020560140c002c00f000f00208510410070308803012501e802074052040030707142020440d0303046981e400c100700054030b07030b5050401a6500c0e05608005c06581c1411010f115034580112440300440f45001003091030540646039204c80854600c1030080132064203515404100c1800030340310341e080c1d4942c007641e02d8041040f04220035010304a004044422040f401d03800500c400364200c861117403905034002050b4070f11307412541c410554100340790b20410b00d100488039414150b03030030348070745c0c079040082a50003004112502e9814484c00d80c3c04428000146000c100684000d0134080c1c0a008480490798000d00048646040713400c00c01030032803c20000c12091914019054 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 572362158 1250 572360908 572360941
    0x120a09031709062205030d38040c090806071101050907050d060b0609030313092316050c030f09240f0306030c040e0a120503011401030209030a0b 64
    0x203020440003420406024401110184201e40080040c0055226603000e0001565046055850144c014842000040060014006d016019078000c140042d500240021803060344450380d10022003101c5001c1803d4010b00700000007901030b40c2c000b80c07925041d4802c44100711550000c0b5481e100701000d000c0305541c4a0050120600d03c8030080105403900202d4039180d00c2031b882444e520060140840c1c0100e0110341c03000460100c014001072401400030007007401c0d600070588154040d483c10004026128450083c13100c4e03d40e80650138521000720344410075407103c01802d02c210890b078010f14000b0140c0200c04031007100e4a5002103a4407004042000b907102d50100a005001740055900803240ca502c4e210b503411450207505c00340b418607141c01035161440e0001400250f1511520400c0002c5465503c10320807203820083c09040080064204a1401d226200e0104104070080004006504903280703444824402440c002d81d40c0d200301400a803410740148005801da01d80401400751104c80c119010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 572363408 1250 572362158 572362163
    0x9060702070614040308161e110f090c07170c0307060e030403120f020c090408030403030e0a020f0409030c0804081e0a05071a070b241e09060105120a09 67
    0x314407650311070b5802c41e00c0c1c001202014040e0f6009100c140300055103040030300341c114000c01c2141c00024480c5c031442a40014080c0c1d40f01d5541e0700d05011414810350b500c034042d010750103550084e0201c40c4000807034588100201703d03406110b0086680010807850301918030507540007240460300c610000300c0c120348a0380914811a80c0ca407a00b100c05d214084084242c1d021245c1200c500601100030503426a41d81e040d80c160042180911034407001103540304c1042c24000d038018000c00781c69140a1070040c00b124540304146546500200302c900042e5901c00e9000c4540d0004e881c00301c5c88503501e00c1c05944c0c8000b07031403004001310404600030034801c0001807031003181c40b07800d075401d03812160f60b03010340303407141c500f54800380c600c2c0c020200a0100f544500c0540741410b8401b40c07500c0c0303024001e88450450039421781d410701810100c19581804100000b84105c09140211924405003012a925810740001e0801c5c1350301030b909c4180000c0c0c0c26070103803040d29502402081f500c4007624203125104018650b50008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 572364658 1250 572363408 572363413
    0x40e040602161103010e0105090703140708070f09110304020a09020c030909130201090f0608011a0c0a12020d180306050c070c08071e0806070c0501230a0e03070215030702011409060702 81
    0x606d8004405018031801101c4c6c040c09441040d00b95298065011031400c040070790351040c0b0710009034003901045101e000340390144004001500386000c0c01c051710401c14079142194410310500001d690b8884003001251011040140d94485807030142d81140075111500780d00c10440c070300300310760b00343c101c510028028401da965008054075005c1c2200a03602c00e024900000702060014014041d00402c2060004520851350382010030100c02503242c05136861341210b402c3d14010210040507010031182808841d9410020080409803800d41840c40e001e10000e0703c03180d12038000c10b8100b120b07001200e60b882e401100c08481740f5101d1102e03554400c0c2e18402c00c03c8540540480380400c803034038240c04046d83d4041d00a403030180c03039501d0121035002e0000015100c5558405d9002d040d1f10060031900c210310491040c40d880ca20b410340c440740840312002d42c4500c581d0001c20202c001650303032220407201c01210108203a02c9031104102203005104110b1004041030241090041124002410620802580d802c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 572365908 1250 572364658 572364671
    0x80403020f0916030c030b060703020d020d2c0f0d0c06090b0702010801030b06011403070e1201150519120c03061b08150102010e011104051504030305040e04060216110301 75
    0x500030310500840300380c001414841d1808850031300c640c000b030b608500c0c145400b14200410800140361540402e40c2240582d1243c100107140c00d4062008400c03079240da090500b10104104011240c0101e04101c000c40c0c1c0c15242c400c070710a5602c1225007881d00401411342c00c41c00d1001d140c0034454558034007410011030010340c070000e00c82516400b1078090f45d90681d9198000e9107581d4a800499002808140c14400d80c00c20300c00b01e512031540074603c07580f181e64440a001100000f0311104100030000301c051030f4100207100300140c101e000150104c5505032840a01190f040200d060303980d8072a00303c410b9114070680100180410484520141c0c1d000d034500b0065088514407904066404546804c042198034000804c149202e4030220044001800003150b0300c001c0710041421105070445038845490007290a11580c280034264181e8144001d5569252500b592805002c038069841003100211140001a013084810740590b501243c9520500c80101c0403450b0481200c90420801da009600e07241 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 572367158 1250 572365908 572365939
    0x30f08010b0f1206040902040c0518120615150403030e0a0b0702090126031605070501050c1209040f0e150901061413091202030705070e01061b02120a08040302 70
    0x2401c0703030140c0d890900158038003d0992904000480b000b46903030343c8190b031445401d0160f103c1d800782201c22031302613403229580d0318482070410b00000c031409524044d400514500c00b140c070b000150316800400b1412906801040741e00003410700c00080f05180e0002d44003103400401c0640154455a10a008940c0000d540c1d031108180344ca039000d1070a0280d4000b4803100100720291b403202c2c204d003803301e04014840c07a60352040c0e25603217142d0110b41034400c00300d44c0002c000c0a00c07105000300c001505003460014509a401a010341d070319610174100500f80100014600565996a4400b0b030050011403c188a83c0d1542d105075a00c0c0c0003004241410840d1085c002008080107104120546a42041c2113424100d80014855141000c0c0b032062082a612250040858111002071420918544c020342c0c1d54481c0d0314105081c44002d40c4400300340203200300140401c940100b039541917075242440d01c1c0d1203403046000084c1d0f00304c00c0981004c500c0c0644580d031002e1080040080c0240c334029562038056141c4907 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 572368408 1250 572367158 572367179
    0x6040e030f25080711031002040e010e1803030103140718051501020d0f0c0c030204050108062202010f0516060e0304080f0a050322030b011206050604050105152104030f0801 76
    0x790b0000c01e819810000000010400c40070b038503a5079070140454009103420310310304040b6403164014010aa600e0001002804424074200e030340128140c40e0031118490145400e640d0380810b010041090811800301c1c948441c00f0015035000703100e8001c010b0043da4040a95000400068501c502030580c00b2803000f9541d4000620991422850354a419440450032400c44041800ca402291415501c41c000009a40e40d8001d6171301a143e60070181c01c3d6400c0180c49200e000b02a803044550001e580150383d00941c4e0841400303083c100e071030b05025580d0000c204d50008810b449846c024646450201c00140c9210000064810303a031a01048919a4501c80100e560b580842c3c440100b907940100803100403d510f04401c0c0e644805c1c440f1100761829103e680f4038514820917040307140e074140c03886607107030a02006019060b007025050360100304c0395040c03038080383c981798801824080990001400c0c01000301c40035403200c00b929001c80d242c43d440c201450014440d0428643d03000004d607441001040e000c80e0b5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 572369658 1250 572368408 572368477
    0x6010302010f0e03030f0c0d090f05060f0307030905010903031508030f030112020a030f060906050a050402030706110709050f0708010e07020a0609021c03080603010e030702010c080306040e030f 85
    0x50b11036114000160764100c80d5403004104054040c001072160b606480c03d1200906096441507000d0a515205841c0061000100da880030380c00d0300200d1801c0050b84c80382c104881584c494030100782e81d01c2e0b9a1890a5000d4000500006c24031340c41c080810080c140d2503407103908100403122001907400d80d035400580d907034041d4000b0003c2d00141000100f1107449076408c1d520b17410784060301e14a102552070700d420040d071b40500429103966440c0c01c912800c000d414410a40e200041c034404000300c1c1041e401196849a440c01481c0620071a1081c030180040200020030007003e1101041c031841c680340c00c0f40105094250350307070400725205a0000c00d01c08034601e09507200741d90a034018a101d000f01d0300d1300c001500c21008244c2e004940d071342590000c0083c42d07101022183c041d4642ea050340c00d0490526085615400b81415241c10511030000144e80c406104c0d40b409410241040d02d9440e0b00c80001c00402000c400e2030540d101c00a8540700d40005d5402800301c1404044d5906270324841010300c515680c49 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 572370908 1250 572369658 572369663
    0x213060e150901051e0d0c091d030910091502010e06060102030301120b06010c0c1410030606021905100603032001050408030f070905060c0127020a0b0d110d0518060103 74
    0x202c8010302c550300308040d8180f02d12076841e4580b00300101450104001412a2038152085a0010030922103400d142c00b6510095001d903a4a0b5580c00e01c0c018490780701e000f19420b4900c6404c00c0010034442612036050304016100d1411440742103c854400031340241030210f44c002d400d001e0b11b00017482560000c81901d04031a031100c0461444903443d602c2000c5808000c00103810b00c1a103000210208107500702520103412844032852a4603030107002c120501c3c80ca1007a0341c04240c100b81050065640c08201b01078181501902c000300c0401d2031821238201104400c00d1504a890694000140f5921202846010032201035410f05810100e102500780c80302210083c11944080021078602104558426405034140c50802030894891000885551003100f5070005a915415007412410040c2c41c0d01d80c13100c0700352036011809066a40401e00ca6680340c810041e15110108001d4500d108a82205c1c11503c15902d0155807071010210110062000b074030207080034040c0f1003401160200000792981680d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 572372158 1250 572370908 572370919
    0x509010b030f19020f12060f0d11010c140a030201050103020a0b120103080702130501030503030610030e210409050a020d050702011808160c0306020a020c03070b0a03050604090213060e15 82
    0x40e10441910703000c007002803400b000f2990030880383c80107090746006400c0c100000010708669080c6903040180c2c10349504217481c40350346101c41d0500064141460048061401e0910701401045400e21448540034071380560f0031406511008800c260381980198140d030b2080b40e2202d0459182d000d91159801a404141c20075242880140701041000000c1c15001c0d100825100f94100034040030001d80b2000c0e803040387c1c564404014403596161521007a41a880c0700e1908002c1000441083d03035403020207101d0364046071484810f05c050f58031007130125006451040000d101900700021410000c0d8480c411203000c0f04d10b82004529242d206004400344140222540301d48920746845000721070f03000c015580c01c400441038084000502c060645001180a07010040c0c42c0c2c001010080c0c10300c80d40442c0240319401a0b5014070103c010b80d010785802c440585000981c95880901180c01800300b500040d41c42042e00070403d00c90200c58002c18103441c152100511142c68030801d11914588441c00a035111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 572373408 1250 572372158 572372161
    0x1407051c0906091b0303110102120114010903081611010806030d110f12071112070b03092a01030f051506070f0f08070507050102060606180a0504020c070509010b030f 73
    0x115480c0c00076040c15000d000c001484002c141e484040941c5940000304402d00340480800c14150008200000103031820000d42c0b8015440700444075044050244420701d0184817802c00d90741e4070030240400550303404503910b907840003881d0b4041020021b81d0000c82e030901d85203121480d0355114115450107860040e004100020f0440010f841c04202400310440724800c0940c0700003088000c2066402c0c7c10501c020499032030f1102c0c204590142e0480350040c0c020050700004004c507000001c4c01a0031111001c009580f01d803a48038003581001140700903d004100c0300e18003502050110b4000340c6002d8800d8804204100d060201402550703401c07502c21119140040654507182007150040819501c41d036400300d460203032507075000c8405603000c0d0181d4140e540880c1c7e0b1005c0040410802d0080e08090008081514210001030007911070201d8062518a02c10710909103a10b407138042c2006004020800d5449a49150030960717540c01f1031003114440c03442d0300000950b00042d54102c07801801009070000c400e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 572374658 1250 572373408 572373457
    0x110301090207170a0905040f060b03040206030408070507180e06012103121109030709060e13140703140c0f03070519030b0115030b0315060114040b030a140705 70
    0xa4104180545429409081c9801103d2502d0020b041108440d140c215146050406010031901c2804820704081e1400109005050402090b01d40c401e504035401980d96a451800044a0040031b8008180b4400c85030003007a409552001000c501c605030808010f20040d44655541e01c540a02c0752201040c03402c1307640500c601700c00748211109402802c1c21036244002008102c200c45d034240900511000104003218180360a01c00c0360001e10040405000c003504040c020718813124054001100780c1c04580d043c10030030071301c80c404007805861402500c00303060340c80c21324402a8211020518050007111500d000c80d14002d4148058100060000c1100030300781000c1c0030703640840c221290695140004000001110f10481501801c20701c1d113541c0d411a017406001c0d0583e00f01005551180e0005480b12021200d948019607001c8800d1030445403490145440c40b60724810383d0016405000000200842d00343c6940184d85810303014000360b103075a41c032040121030743d00a030300c0461500c0326109120340d00e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 572375908 1250 572374658 572374661
    0x6110a02010f230309010204060216060f033902190803010e0702010209031b0f0904082b11030103110603060306072703120807090b0901350f06010311030109 69
    0x2a50030454000a455100002480243d504100c0f48001183c1d000a018803078240d040c4121310300004480011618203090400103010294200c4a8004045d81c410b090464011040030700d0704c00111a90780c41143d280503032000001e031600c0d40c129034094485e10420704500f500c0e00c101c0302c2d445030300002010b00316420f00c0030b114071088019001c02d04542d002d20014203240d9060000040054203142884c62101e50030050010358042c00c7c0c41c2c03d105014032404c000c080307600f01046407003032410620128040301038158461840c82d180c0c500b5144051802d0302c461039256260000f14180ea00a03503c1612180000041040c580f100310784142d010f40182d004912401e000342051480e1511154a14032050304110030800001516401907404102c2202644800c030b401c0102680c1095040c03501e1069103052042c05007551040c807045504011052210a00301000c02452051702141500040310301e14460f2100f1036181416280d103c0c000000c04049000c1d9800383c4611001d540c80c2042140c11a881d01c0340000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 572377158 1250 572375908 572375927
    0x50a050d030c11031906150501050301170a060204061d0303040803070b04061e020415020a26130906060906030e0613020f0901030b091e070308130e010b0406110a02010f 74
    0x243e114502880c4580745950a02a040040d0420a02850403810703a08004054030101c01044020365929002444243d81c4002164152107000c941c1044c01599640424601740201c0d00280106102140100348030360f11184030300342442c62020f2248862944001c0603141d1249106480c0d9943c42085018000f403460100d159205006e103400058102c985003143d001c2c18140c85c21000840c0c1d0000d0107205403c4021501c540340303032803407000b0590745000780e5032044600054881548259008002c241c2e01240c5407048131034400c80d101d024070b02d81d9552030002004c0c0001e0701901c0c0100d0054603010401c20320a102c2e00b201203e100000302025100c8103c00d90b04044825002e03030b0419400d2108000070b40755203403060f00940c41503120b6640d91600c0080c3d107041c840e85842100e010503d0440c420416640010780600352a04031403120f03500c0c440400511a5900268440903c1000b29800059050300d0f400240c4200c1e4455205d40e040506504840b548a10b2080002804180031841c007001c683d10842814 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 572378408 1250 572377158 572377163
    0x10e180c060d110c0f06100e06030604020105221707060c0b01051003060302030f060105030f030703051b0c12010b03010510081c1b0501060305150403140a0e0a0b090a050a050d030c 79
    0x394644480140e8442c1017061001e50080c0b02d601140070303c0354001c0c3c41c0000344010302c41c2001c8110181000f0700000e8956030003406c0641004404074031001154800d10701c02107050700b110500d041580c1c0d11800c083c1a40c0284030284524040c075a400140c05002c0c0d5240e61250b0750110500300c17035a0030b000411528055025454003010780c0d807000800141c4080150100b03140e0b45000802c03066160904040c0307404203468425400b034100b03003c1040082c1c3c000060720340d480403110000040c00b07928004036103412150f03a900c1d58030808540f44002c1c810b0066124401810b0198001e21241c3e881c00307002400b41c1d4039807141c078005901655000d00c0c50794480042d030058507050301c0d1000c1154208204c03580305c1040c000c426a002c1e59100010010408200320364003e104482c08a0051860141c4010f040b2110300210608400c17800654070751842e20800000b94000c0f002070519183c0c984034030415500b500400c00c85405214003e80218035403802e880c280040b200010001400f0b02c070559400c0341c0005072902c04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 572379658 1250 572378408 572378441
    0x150303050711090c0904051006050a030509011404140d05031005040f1d03120f06010804030c08070f120305100305190206091203071203050603060429010e180c060d 72
    0x144110ba649041c8401d01829030a0000b6481e903103004104011203001404d03000341c50954000801c042a004010355154503400e042c001a5665840301c007a001d17052a4002120468180c003c1008018001000c0c0000350400411140310444107a401e445511003079030403880003c1508000c11551410b40c10104401c00c403000080391402001620b681e1555040c3c41c0c0c02c0b0b480c1c0001c80d29062141c192100550301904034103102e0341a00f0281c0c000f80204c2d60281002e010000c501e0750003000d12019500f00e40d00341e54030940010380c98241c1d0501442ca2031003401124000f9041c1300c081038200d52260b1841c02500c0c0c1002c0601104440803041004400e80001d049030003010031f1141b107003203640322149500141040000b0b580d449025152542c3d610aa80300c298051500c0c0c4424080786840c0059210741c010b9001e00b91b0213030003000c0b1000009501c005494000c40f66002e43c00481e400c61440d0b24140680c0304010081e0780000c0c444401c075260b4061002c03c940080d4140112840100e43e500110708103016281c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 572380908 1250 572379658 572379683
    0x3050c011a0f01030908071103030f071b051815030a020303040b0a021608031e190917070819020f0603090307030806121b040e15191503030507 63
    0x1211400d549556041220304012403010850a040ca514008240388013441c040144d401c81d6039800c8240d000e00704002c0e00140340c0c00c80488140e00c0030002c81d80d1010f00348501f43d842e0b41305454030b4010000d0a420442c0105107a0710006241c3c20064110410241d080c482c1604a43d110000241c551158440c8130358144031340380300c40c0d015840610003440030300036000d07c4598410211102901d0200d007894409841c10201004101109021055a42925043c486c200c602c0859200e41c0c18940605d00e030840d81d0f8150540e1420146401045e0716080b82c0840c200c0526903900b0088150712540c00d8031519207150468484400350b1403d04a5240030144014280c06071901103401041e9207410864020584d0b07071001900c0800d05400924448d0710650480d038000100d40342c05210340d00da503141c800040010079214800e9249a54a4100b03460146580c0e0880303105210a01d60f0056000c0c064804500340528044260031f008003a001b03000380c1c0c40c0501c60101e5111701c3c0d0b540884055004000c1980c20b20103180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 572382158 1250 572380908 572380927
    0x3030313020f0a0305010905010b0a08150a060b0d1a01081603050903041203110c0a051509040905100c140304030e06031b04060809010c02070503100f110d020a12270305 74
    0x114403c06140180e000140c94600d07403904a0071a03494030a49445080d4000041000a00004a070a28602100c088010640342c2e50350340d0010303090a070024102e16402282050501c115540314000740e6080300c1003500da401c1c050005407041081901c216220441d035a6003002080c0c001e807c042d820400c40c074200c81c50a07030394540009000c0024002280007034821640144401030030403168044810031680340800301c0c94100025008034080712440040e80000c1204901d81d03a4580c009814560007600380c549002100861100601c1a1040350010a500b001504403c051b203000350703031040394581c075203541c0d0811100030480a90001400c40540060f825103105042d40b101c0058002000243c4400030303d410301c0141c29003505d11081e60001103600482c82006503a8000078640100c1414907400102000c12648040107007204264a40710b5400004040c075a07140198024074940045545420705c41c5001401d0340300f521702d564a540c1041c4026001d040b500810101c40c802503510905000b03240c400000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 572383408 1250 572382158 572382169
    0xf200a0c0212011b08060d060f0902030d050a020d05031003031103160501060509070c05100e0a02150a03050105220f2702010810180b06071b1d0603030313020f 70
    0x30002c0c014140d44900381c603120a003000c24032110b071546500308440c0c03d26151021802000c1061000b600c0d168030b5085012445009910001c0c200c2d40240555005880b5090060010f505c4070345102d0040c4200304c4034403032f600c0c8507100f941d02a440603030342d80c0401480c40d24101c401d490034013005030290008024032543e044044000e82303d0345110300004260a4038040401038040402131400c803e000c050341001c40040d20100308503884c1e00040b60300288403850700c0141c900e08140b096000f5005105508040c086103061400b4000c00304141d038003071000c1da07210001c4c0120b959806104d80c0b0200701c0d04040782c0c0d108000c5e03004900340380d2351040002406841609180101101c05080510303a020401120b029560f203c40c00540c1b0501401164070b201e0320305a40c0090719080d148800210f5991000141d020783d072100226900d00fa080166014080c2114000c2007a110051180800182c0403070702c2c00c0020000d1b42c00c174a100301002009141940d41d01078120b444001801c1049034404510140445c0b00d6488 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 572384658 1250 572383408 572383429
    0xa020c0c04020d0b1915110d030e03090d03080f06030109050a030c020d06050c030618010609050f061207020313060c020603010306050406060b181309050c10030e0304140102010f200a0c02 82
    0x3522240b601181c030300580280901b0142ca0303800200b04c0b80000900c078281001804081c3d03103582c1d150008040e003100e41014194041c409000b43d001404861000500d0303030001101c0c3c02881340c841c60f8803103600e41004040c2212540301005040b500000c11120100e40130381000c81c54640042c01d01806101203540f0380044810440d88070002040c0401404070138100080d0444448000300e10105142d41082c80281101000f4407520348600c225151051403501d84030182c0311905103314421a841c1803510b0302a44035007104034030145201c183c0d240020500c1c4500001c0c202560003606542c81d690860722000017619004105541c0242c42d1000000c4c092980320041040d02c112a025920040c942c40c20480b0a00741180a10744081c100308020020840108000360110002c070703503080401759040300540107001d2600040c030460001050000c1e00c1c08001e040703d04018003da00030000c00d00d40d040352804681003200e445117050030342c800e20007940764814000d10010419040540201c002940000c1000f0309 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 572385908 1250 572384658 572384689
    0x3030c031d0a0923040c180b13050115140a05090d0b0403020d0e0d02030d030207020d05070602030d11030702070603020d06030204050a02040f06090303020a02060a0915170a020c0c04020d0b 83
    0x56032030100c1000b982e03200b0081c80600c513924070980581842c1c1c5810660740c5907801110f080d0800006155240300c10b070391040300d1a9001414150402606801c010010b01d001d1040e00b110016400088414500c200518492524600ca030359080107210081150076030403010000e50007106000c0c130180401d0103904141e01c03540c4203500070601174117603250003090283c504440600858115884800503640491086c0c01e40e070143c45e00503240c0f80c4c0740c0005506000d1010f00503211303000e500e0000c55006d501100030503010440e030b0001d00c2045100a004021807108440190043e00007903018001c4600c6500204524207800c4c40c0811400c6d103c1c0c0004003118004e540702c000403940020204008076105d100c6c90024140d0381401aa4289591806519195000d6000384030b074500007445d2100034040c0c62030202400c60100d401d1400c4500010242070005501081950480340b1800101d6a035514021140541510b0000c0c1011050400901000c1d400c5807041000e8a511500c5642c52070300c1d405d0018040c5032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 572387158 1250 572385908 572385911
    0xb1c0308191515030209220212070c0204051e070c050f120301030c14060a0507240207020307080f0709092d060f06060e0d05010f0213090e0703030c031d0a09 69
    0x2442e003580f25040e0b44164040b03005140c018400210313660346035051211881c07880c1400e00e41d00caa400c0e113840000c0c81139a26504400007900d052016445d030003003003121450320a0303808000d1030711080443c0d00c4444c84807001603500b17040a40002c3e12144504804139a00d40701c0d608441c008017102d07018500b0259240b00d00d280180c0040010014080101c1c43c0344001e0890001140c0f03a1586140490010303c10408000f040c05000540c003c10002242d0b41405200040c40c83c4005c410074158400e00a50300c01c0d0030a901c24840c0c0b034030120f6590000305092204040e008000d0800c0c0786002d01600141c1160401501c142116950154404544006e203100d070000403002034900010324980740044482d041d14203410b8a140960070303c40603412070030901c8540402c030307144c1d250401706160840c050040c80018400490010641c04030494040504405450b0703004014088111401003484da00ca4040c400540001d102401000200e40200151280d1301043d181c00110058940041600079240c1d900109509 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 572388408 1250 572387158 572387201
    0xc0303090632010308300f0105040e0f030a0c030504050409030f110607020a03050702040906140a0f090b1f0f0f0e010801020910260405010f0b1c030819 67
    0x1400c1c00d00000b40a015820107101080d41961240281d60159401c5004170540b8005401c078518203405810100c42c0705c101076441d41e80740c2902580f414210030301c2618001d50801c43c80200a8038081850302003504440e00950814240c00340c00c0b60110301c850b42c2502440010000480c0580740ca0144002e0240a602c50140411424400401002c420035200800d9000b40e818003400396800702d01c01d01a9509031070007070b484051074000240100800c410041106181c286401c01145512091512400155400300400340d82d540c0b80c0b038282c41001c1c0c4024003010840380011485030700b09000c0344110072280c02c403000240d00c5003071040d40640ca07030700021100880c410003080b0082c40c5251403070141c0095402541000105008290300c4140080d180052010208102c0804c0b41003001243c030a081582800d402801c0a003081402000f400645050302c50a10200c8101c0341080080d2440d458410b040d8207041c1c8010351000c0f01d04045c0a810456000d41c00c00c02c018560450380903982200030100c1d11385000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 572389658 1250 572388408 572388461
    0x1120b040609060e060604030507030201050f0d0e01091e020622050a1202101b150f020a0507051c080a02030c07120806040506010e1509030309030f070609060c11010c03030906 77
    0xa03200b00801705e510610040106100141d00460380108170703035083c20050344404040e21414403500501030465030f02458040000b04410054112030f0105005000c004640e0070300980803d680b00c01d048019420001c2000100d240341c0d40c0c1d12208144600a480301c3c1c41e0b0310303102d10009400841c5640002a1098065501c40551815052551080c07600381089224030f4021401c1d9000d142c90075902520b40e42070b10001e2450804143c00c180080c1c003910030119030364804503002030003581110b01e042c3e90510400900260800103003118000200040e1640f00d400c0c1e80b41001d910295000a190305014481800364400080b0301c00c44409141030140c44100a518003442808115800144400e040160310038000c192601d80781841d40203c031071014410340d11003499002c20b20314841d038441150540714041ea0f10f000c00e4801b140002c103840455550341c50160b0742c1d2130215040c04d50660042c10b12441c210189607258000d80b214410b06e4468100414921102d4444070304803411310043da0200446001014507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 572390908 1250 572389658 572389679
    0x907030b0a051509040201020a1209031b0b03010b0c070b07061407021506190810020a08012705071b140d08100311011209050c040f0207030c0201120b04060906 70
    0x91018905400700490b1900b0030b003103030480c03c00354074050280040501260640e4400d0000101c210340015a00c85a00e640d00f82c000c00115041c8815180d01803608900c1203801d90240d072031421a40700650084c15a400c010010590394414400241d452144210000c0e40b90009405841134a000300380010340000c1e42940c910101c10300800440c01c41d004030340e0421490b466001c64a40043c41581c07004611502e03e08507072603d80c0640c0103080984600c114018100810340c00410768881c255858002c1641d83d40100340001244e0007800c1503103030324040d01c0c1c03001c00e220b03a0082d0b6210410b40307041c0100100c04412a8507024203e8004d071841d16240380604402032040101040308006846d0825141c41c0031032070121100312501008244007000f03a01c07008240e00c1145800200d0b01c28080803c11031015103020f80d0b443c088034012900690501841d031840382480e10a42d800c8907015140e10350010301c10350044699203800b540310b9402550b0f40c841d10170541c40d2842200040d03d0304040000da0682008502c51 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 572392158 1250 572390908 572390911
    0x1020a030f02070302120903010b041a0307081203061905100c02010f020d0801090e0114090606091302091501031509090c09091e02010c0204020309061f0609060c0501090602030907030b 81
    0x780c100d4010481c440c0001da0008811008107184940d0640b5040000c00081c05040f0589903242d02a00348188040039442c51100c0c60490b9004608039900d080d40c64602c1511881d001d00085500941071002408500b05030302545040340c00000f070969025114400036580170b001c6c40000000a00c0c2070401c030f00b15600b00b030483c150a6001c1c00104200036104900504014050280c1c00b2a03c2c4c541138045d0251009400840c1740c0c01703080c080c441440ca410003105989001c220f4450f40f01d0105000070a07842d2001050107030080760058041000341d1f840543e07000c03000c1c401c005002d04240d85d465500100c5e00300e039100840036180708c8201041d80c0c1c0960410104250461f00250001480c0202c01030010301d203003484564130310740000c15025000031800103a4089040c80d10107900240004100442e809000c90901d101c1c4100509006039108201d69030070620000b4062200400e9003150b0501519002c0d240644000d8032800000c200034001d41e45510998205440001140e4031061050003044490350146 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 572393408 1250 572392158 572392181
    0x71a040314040f030312060b0714120a1202070f15090b0a0e1e01060b0304230d0503060415081501080d0e030c040207060f0c0e040f18081c0e01020a03 66
    0x250815007000710381d0280383e029200040c2400044e0011100441c2d107034001c03a000b000c5802d071a91b00d4418030304281401a80001d41e03140e090080c3c50700d11024a640b581a0346004000e96a940d0807222014138000081d40003900c20b80f4980c82881c080c00001c0d0442c940c58a651414600c08110303d0402e00d05919030240c081d0440c2419800c01c0154400c03c80e00003610304200d11141c0f01495041d00d03401003140189280c0c1c0120905010000c100002d001c007001550000018180038400c0c400e140400d55621250322031000b000081d410000304541e0b00d0590400a2035441402001070b41c0c40d61005100d14249000c9176944803118003800400c910348040c0320744030389a400c90515070901821800040d40310041d0398402407040d40e001c100d650600c5010390181e21124070300c04081003207458007080581154640b07e840d0b880f41c0d00b440c500c4105404580620340f8004250700f400740c01c1e120742d551905c0c1150072449400750075842149a03075903204000d00942c00000b9121000503900c50308490b004054441000d8030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 572394658 1250 572393408 572393447
    0xf0c080411010309140d020c0109121502090f030610050405010f06121109063408030f040f08030a0504051c0e0907090b0d0f150302030a0f02010302071a0403 69
    0x10000030810340a0752408080092800040e01c59080c54007030109250000307031310218410039031390100e4181c0000d00180d60300c20980b20318103c0c030340d40c0240f4245180c58400003455246e080c1803084143c40b25801602900f88000c1c442a1001c1d88000801d1900a0445105d000c50130030f000c08200c107050134410780740035107031041800003201c0c1015000380ca2914800000141e0365621584500425009800d5803404c4038018030040d50380144504102ea40240103040e0110401019a00d04403054103018051805920140c600c0c03c40d9118040e001f502a4000c1c0151603401580d91500000351440300110301c1802000c000003124105420030703901c0e00c4000702000a022455041e080c0180c0d410104d82ca41000e02220700001ca070b41d03a004100da031105188c4c0101502701c1c0c0824048850610398020350490301841c0703001c02102907442e402c4807001040d84806505904000001c07801b0442503141d000d0f078035006050252411500c0d0751050031180c1ca401261260107800003c1c40109940038010412080311403d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 572395908 1250 572394658 572394661
    0xc0306110309060f0604150608331c020604080f010605060a080604090212070602030c0c0a0501091a070507030c1d040b1317040f0501110d08070c14100f0c08 69
    0x8182d940e0740400350005a07a050100001030b010396442e00508201c614411240003456074030030b0060141030094640722108101800c1d604070080399411108001030034000c0e001610030584041c80203070200706000c42130061052230345401580b5000e0040004010401c020040001c0301d501203801c40d911071b08483d1041d00708118140b81541d02940030750300500101d170002508961840050300004070b190341c1c60000e003d4440c0014800d600803000e03200022100f41a42e41040300350b400c10040c07801c28050140400c0c62820107002c085000304298005100640d040c9107402c2490f126585880c1003039000711401c0140031014407080c02808098840c0b03500f00c0040300114102a6540c04154800600395101c0b083c1d040f08910a1040c03010f00201d40c68412841240c2c4c550300d07085d0900c689400c60040700d0108056021910141400051454644c0d4407980c1e1000680c03901d45d401c4800441c410b6041d25080c5002c0e030400100350044c0040e14031040219800600360102043e940103451f00031041c20b00b88440c100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 572397158 1250 572395908 572395921
    0xf031b0c1509030a0b090607032403080a110f0d20060a02090102030d06090b0f0102030307170406021c0605040b040902030714060705070e191a0d0303020f070c03061103 74
    0x1081070100308141c940b01c0c4400c41c00f01e86400748801d0301910403010101408008103000c00d00358014003040d5810300030404005201c904600320740d00300305000d61028504001103010580901448500d515000d140054003c110703e1034261080c000c14020b4000c10042c407401500104900150002d00303420360a90041c6084260b10ba4100404007a000c980000300100386078030a200300c811440f44d01c401000801e0f00c907140c12005011341301c910b41c00391155201c080150b6000000fa648181025600c11481c260030161041400c00f0152040707a00035000d00c642440c1d000344c1c0c0c060000c0c0c10804000090028900010442550000c40456020742c5c0b4144071800545c8001c2008815141340581a0710060b801c0d00c0418414840e002003e440b900030f01d6000302d000d11104418601449058070003624503a2461a2a8119a0b5a030000c540d00803189410b04201d040c6801900f40d124045c0c2401400c7c0700c5007441003505540140300072954200ba0180038030801c0558031035807101c07000c02030700ca905519001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 572398408 1250 572397158 572397169
    0xd0c030b0d030c02210a300c050a14031c060807061b080f040905091903080a15080a02040f02030603060613020c0a0602120f0702100f0e0f031b0c 64
    0x1032000740070803c800202405646803441d602c1c641003001c4c00c5c00000074601502d120303210751a8810803070340b00c0c403040c01500c070f2910500d2003459018003a035a41c0822118184c0141d4a91503c480e044406006038240303c0040b800380c010152609540501450f90307402816a41d06401c918915a00c903031a16052080c0100d0100060f100280c0d95103041c100d812110b40300381e43c9001d20720903400030f06210300016040b03011211407000e407049174980e2030140f11a480300b42150380c03121160707004054600c8104400c200401e20840c00960003170206030b800170b003280c4845051010414641c00c00d0151f40d01c851011421402d00c0e100f044a11404640c08504500f0300000007070300e48601a0040c1d02c81d07a401061070540006035030498082010040440340d07414100d14141000e50031113140c404035001c03403000299540104843c0507100c1c54455028100041c1c00405580040c02240410b0441c981c3d6580c01e264030781c10411180744105d0010000715101d800d94001840311025540e0100c00c40d403c04080c1c1101900c40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 572399658 1250 572398408 572398429
    0x302150c1903180615090e100504060e06070e011814060c070b070302060414030a02071a0c0601081c0216051507120c06050703020903150403020f030f0d0c030b 70
    0x6240e41003045403150070210080d00c80b40c104408140540c842203800c010003540601d40b20030441c510404416520301d1840d040f44e0408080101980064007150ba58602d0341e800540d101d4426580098100c00361084246090021034049000c15251041c480280d078000f8040203418500e168811109400c0c481c0b184522441d88407002c1c06840d012404c0c466481c8240310b41c10192442003d43c0d82c5405481c10001d669070410741d0240c0300c40c4403508501124060100494a004215400810000b031800e14100d111040a10f030820b040901031010b224400407c2c80714a00800d10b1000900c2980d5065450407000340211038100103651000d1072104590b080b24800808480b4203d4403044030204a41d4903418a1042040081124081615440426800040c4d244685026440c00c021955460400350308a109844060f070345540030f148005803048111000580c4103101c5d00c140e417241c007508aa11071668010800034624000301144089c500101c51040e812105200d140600c031014049000c5200680c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 572400908 1250 572399658 572399677
    0x207090902030f030c0c0405011401170a020d14010905060301020301031a0606040b0a03091406010803040902090a03050706050c010f060303050a03020d0b090702030901090503010b0108280510030302150c 89
    0x11100c00080940d0b60030700031100004454020399a540fa00044030301d40340c0b15070f0301090b84154500000030402c403406011811410384182c68207050000300980e038100380b01d0010f10038040c0d140c0070485622844164094010450f402c2824400b4030750508448805a0700000c1c0000d001e0f81c41803004001107803081c1c9803020310080c03e10500049480310703000308429108a40104020000000304544610390662284842501900401e00d07809031900da4640c849600b031080c280c035913201740700900c410301090f0b008250301c4030010a0f103181c0d80e41c0ca943c1c55080c940c00da40000041a004101c00c00c44000030b01600300c4603c4401010440b01d030840e50090014052031100d03000305680400c50350030740e0f81c0d00c1d48110b42038180140391041034a4603040c025980c1d402104038038005802070340d00040c58181401003c0031422b0503151024560f03100241010a0b140c040012090712034503103a8095041154404c50303004021580d82820000d041d802e0207803501c0000c290b4000b00940032003c02c22100101402d07190074a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 572402158 1250 572400908 572400911
    0x1a0105030403050702190519060206070f03020408070803041d04050d0809030903011407023c07030f0309152105061206011205071728151e0903020709 66
    0x4071541001c440c0c5001d0440000d401c126030100445404031020721041c12218115501d0345019240300c0c24501801c403038070554016134400e1001c14030309400340512003450f0a075490f0050400759541c240c00c0ca0841c0e941d0200b403032504002824413001852040068030002d50300655007017824150703034040d0348505003024a402c01100a0104900120a00448080b50340050080c001986088001e01290800b594054058804d03201080d010050700b0709007003149400b60f060707100d6003003c00c4c082c03400c403615000038119140101c90020000510220002441c140203564268120341040032601c035107600c000300e2000380845410441c921491394443e000c0108907808005c505901c42c1004280d0701002c0501200990150a00100711498407540c03c2194901441c00c440220381d03502c1d03e5400031884d080925404d0741040e45811942e244501610801a4003c0800345401c411a11101c0480c61140801502c043d01c81700002e25074020840021004804108108441550360350041e6558806200725440309 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 572403408 1250 572402158 572402161
    0x31b081f030501050403021b0409031704050708060106090329240d6203010617010b091804080405061903060f0b0a120b03030a020c03101a010503 64
    0xaa61008400e00115407180003400981000d1401a440e209400100c011043c1000710708250341c038040c081d0704100303034044c0c80340880312200214440c0b281d0b5004009541703502c00c4407c005980760702006540d0082c4400e640c1c0b011010b046103070180003581d856540802120f00c0101030340180300840c501740c2e08108042e805c0840c1c02a44100d03107040502c0882e0b00c0d07030b002c0c1094407004240642480980c031034500c80b01041d1310152680341d084440d100144254107400d8001030503880d18000c070b1175802178684c3c40b0141c45454018984120001c950090300070030b0000e844d554180c4640502c19140d1405401402412800c000641d80412041c500c510000301c3d13481040404501840440400c44014200c043c0116944e040400c2c659440303c194083c031400003a203003050020b6000260741d100c80964100c00189441d1040750782c0d00319a013068440b03038040410fa5071b044045050707408000500c0d50b40c0c1c168015140c08000c1008140c101200c0401742c1600906186665402d1700c075900c0d0304c10480f9030900301140c69 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 572404658 1250 572403408 572403451
    0xf2f01030920040e120a080105030304080d050a03020d061d07021c050f13030f020306010905010b07060c02010b0a0e0a0b0d0f060908071a0f1320030a0c0b0307031b08 73
    0x5090704042145090048411765444a000400207100c481c80c41d48030681540d9072101491b03075a20944c480c111413a04908028041c9d43e125034001c1001156a03d009420205a445040704407045648410071481c0d07014100c07502c003c0c4e1466110b41c40703a40f50000c0c0c6420348114a42c40c40c0c4002c8021924200500020580b01c80440041500d070300361400e081d160299a00c070314049945400c1e28000368820b100e2140005244845400b90328140c0ea10ba10400b420021150381c1c2d40081d1004041c01410b40d500c0f260b82e0b001c0e5440e004201002495013401985003401c00410380002c0311101c100307060240e00811800000704003035004000780350364854000244412503040486c003c0c000e07a070000b0800b600c011707101380403801603803070a80c0034140c00c0c04c080075107403138400c80100b00c822102402064402c000303000401150341481c0802c001c034000f07000d5a08040942c2d6807030105e405240c01820940902109202c2417507031510640c40c41c410004003040d00700c08242c401618485d80104800e04108100440c402c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 572405908 1250 572404658 572404661
    0x3070207061112120603011d030a181d0f0709030804050d060e03030702030c01060b0304030c0b0a02090301020a050c07050114030411010201180819051c0203040f2f0103092004 77
    0x1284040000c03a1903d540c1c459442030840601610000c0c429230904065030312164010820703000c0400654000c40ca4502c0e0480f00365000d91029440b440d070600c030113000061442c1204032400c850402c8512070300d40307860001041d00d9002c6002d048041000002c1400b8000104030b0302c2210f043d0348040742d009101c511907203440409090688002511400080203204c8055000801341c00c014078400c0c000d00c4800e855884a034500c4c002224080d001070854280c410201c1c0b45521400e40214990101615100a0030042803c0e86d021906d0350300095030004008040103010302c0880042c01091900040300c00c1808104580740c00003074405000c0d50000340940c18140c0c000d40c080110702c0704204c54600e603030400d0306000400c0e400000380c25884501c08840040c03110306c00d1040f80d200e445101d034a03050442640d40011f0003074200400c100c5980030801d1200c40420403100c880b404044000308a0b000c40a0200400010002100100d03410300d420700321290000b80441c69a255540303880300e10807a00021282c0000e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 572407158 1250 572405908 572405923
    0x91503021018140f0402090d0b071107140607120e03060403030504110d080d180206030c0310080f030415020a0c060201020a030b0f03122a01090215030702070611 71
    0x258821401001e51500c50b0300044141c5015146a2840c0e488030307555181408124a03400e11558040c91304203106000e031070300340d01415130920090049030b6240b91955815858250950b010310204202c01c1e500c650122007000b10a01030200c07a032000500b2000300001c642103014171a4001e021480c54102401c6292090072214201e4900804490301414607040140040c44c06440c00e484104400002c2c026501704144001c0c86035030b0080900e13141030485101000204200c0c1214925000004c483d100541d4503400594082d4035440070b142d0340c0e030501408446400c030456004180700d41220302c45000d1180084159001c4405280181200e28803445d422400d000028200420f88000450b01081c0298158060868030070291401c101c410708d500104003505201c484460303032650001c007800c180c1820003c09013940c2d1600c2c05c02070709000d2034002d04030111501c46914024a139511070b4420706526240c02c00c10385883d0002209482c6040c4190029114039040c0500400e01c40e000340300c41c50002d4104801c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 572408408 1250 572407158 572407163
    0x150d050304090504030e01080f073f0608190f060f02071406070c020d200a1401080c030f07030507120906050426031b070b19051609091503 61
    0x32036845440e4400380008103c01d07281039000504203801d010855000f80c000901452160b402544159102c01c0200d410065846425004505280740603250a1a40b150b00202d113029104855102c640c0f841300500b00c4c1c105500c010301591101204081c1007070024001c200702d5030040b8454524420a0038070802a204100c1201c180794400560b00d02441400d001041e0400c8600061f1000758680303402c00c407803000d40c940d000b96100200d0048100080c0304104584081c882a001c0880000300c080c0009800b40701d198090312058030b003000f10740486d6a1104486a00c0150800541d042d42402c00048100850041c20b0381c0500d5900d00124200307038050451102201da03000c00900641c2c940385003601c040c7c4410f070b4044552a41c2c03c1e4504007201030804140c6010890010701904680d50001d00031100115490000c0c0c000100308101c40229190b104a188215042d00000e0001c05065250744111a00249001c1c00340e800c20b400f9071a01507101c031a402c01c8480d66540800c1d1146120345109055101342c4c0300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 572409658 1250 572408408 572408413
    0x3040209091c05030a0e07180b0a030f0b0901110f09011101110406020a060e06041208040609080f0901170705091c0203030d0515041109010e01090e07020c10020105010509040807062903100b09150d05 87
    0x4042048048901c851040c513b0310000d0081c04540105c00e2824024502c0b02c40501e1028041001c1651161080417541004040040381c0041031499a004541c0310390005401a04500d410205205181c01250b18481c0050001c040d14a01911b845880d004810003000805c4104070104007805150340000e42c0b16500455480c0e079170800003d02d2540e07036000244540c08641c080301e20ba022500c510001c07510035270303c1e911518908a104e000700090070045100c05c4050300d58001c0080c000d600c04001420300030b0850040010b1a040029001c0340311410300000520490515620300c081c6801e070340a07125015020b0a003604245031040040e0365082c046d801c191100c1490000f0040e4041e40020007000f9454150b0301c030143d02000d03007400ca003030791002d00945802020500c04030780068034400042502d01d016010010702e0406007260f0002641c4240c01d103c070b0501803003c0400503886c0502085007c0240114100300720140c01020800340c00009045401000e50180710300403e0b00d90426464009510505 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 572410908 1250 572409658 572409683
    0xa080318060c19050403020906150d110406030506100c031107080a120e09090a080717030702060103110a030302100b0f06070305030f100b03040209091c05030a0e07180b0a03 76
    0xc1040d494000d1541410b00703c00048400714410b01507000c940c2941c1e00581805c41d0b03541d40505000280d441041f10b40760302182004511071500d500d02c82d0300035220f09100100c1d5202c0c0703405d42c0101910400780c0004e1281d10710f00d800082458002c481c205003140d06082c02902c10060200700d0303040c20ba40707a02c10107650182368040c404100420204652041e031a0321000c10540085081c454a40c204660790394690f800740444001051f03221016024140c0314540d0541d40e203420003e20341207904281c1e4400c0240e48024010310402c40020650b000350141940e2581c107c500d5918000d5a0f24124a404800d9030358038555140710761104c035a1320480c044080c2c0143d5079940d01b860024640c1d030044441c1c090340301103100811165511210a44126900d000d01c4034199140c68080100640000c0c144a100384070701c0041482c6205a40c000c0345170301c0d8064440c0e079100d240c190540c405907441c00001d44180e401150b400d2100c1035281c19845c0c001969010000b41c43d6480c400031400d40c0ea12038102070b050004040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 572412158 1250 572410908 572410921
    0x6110604060e2e140601050a0c08040b0409090c0e10050108041104111e04030c06180e0108070501080c25061e0209030c1801180b1305041a0106020a08031806 69
    0x188400707182400c0c03241001303070041d42c540009807030000743c9003a0f00181e4100100700c00340b881111244201c5000d0704038030386895600c0700b58281c180e010790700413164552516030070340520114416000c001d24411400300d01c1481d241c0c2001e10030120714012941484208000716007841100c0c1d8003080402d1003e0010072113070310b024000e5110303034111601e5a411002c944e58280240e010341c0040d1011264490881400d15003000c0d425181c00301c0450602003608080040000c481e0426807416001f000303040050300180b41000001005058014650300210701c0070428940740101c022a030804070f02280c2c0c1c410f040c044861614101a1661851f0640254070b40100c45100c1180d6034000e00903204120111000c403003054081c441d40840c0c100050801c0c0741da01c4010440390340c0300081888902420200081d1050039000007440d40d013148000896050b684101b00007c128084103440901c0b00103c84091045d890044000e41d5449104030080c000080400824864014550811404810301041d11050714140713 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 572413408 1250 572412158 572412223
    0x5060c0c030a0f1407030b041104020c01110c07050f060910120c1d1e040f06090603080306040b030304240c060c110618062a0a030e010606110604060e 66
    0x41c80c0503100315111404c0d8280c0d8040c001401030131260301c4a80e01c06035076107a0320384441105540e03a81c82d030802c0d020401c4011240083c8180042d02541108060301c450b034a45c0401d29040ba2904568001c8011088505c3e9030fa0310ba1065604e080c40844201071002c2c41940d04903000400c00c02a84240c40c113048951540a40042d45442040c4260500c40c5160000303c1c1048031606c08501c0d480d011682d01d5080c0005401e00740c100c0c3d10000602680440c03080c1d5514010390445d00240e106645412011080c025170303141c2406505c0400314210021814982032520040c0b00241c1022400f401c4008602e482c5c150702d024110103880a90440020000200c0310900540303000000031401303c142c000ca43c0060a40c01101142040107a1114010031302692580c1e0900840321065542140c01c2020070bd0506082c0c40c0c5000607c4184065540825203c1c03050b483c0c14207403081a00070100384580042c044006c1040048c4c1d1980c41a001000413607030000130700005003050002c0c00e000701c0704c8502104011100111 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 572414658 1250 572413408 572413433
    0x30b0d0f030e0108040f0609051c05120601020a120305041505010e06030616020a02060d021315020709110f03061201020f07020f09060135011503150e0105060c0c030a 73
    0xd40302d8a100c0b445020044602d518202c0d0018050401e1400c400c0101d50181d202d000003d01c694210f400418645200c480940f0b41148400000b400c009012142102e1440300705411280078001425240c0d0683d8907151400b50b414944010181d50341e00040501c001540b9561080c014403100b00000e58603a1031111521004a40c0d150003031282601003000b444444241d07820034280f59018011400e099820850700754405401e890910740c0910080300041e00903c0e591004010440c4444003420400ba806405d283d91640010841860460050748842c68141298441c0000140b626980e54072000000c041d40a0801092225880818401181d510007401010010b0017291810342c0399803400100300070401c049810f40c4c00903480702103c110500b00c40b40c100404580c00621488684121a4140001c0c0d04c00da001009841c0058802c0402d03d81500c1441c04400800c42d42503ea141020141070040c50107114240c0117001c00542062212420300603e80030107001420b6442e1034a4500306980c84034517 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 572415908 1250 572414658 572414663
    0xc0305040209060f03100908090a0602150a02030f0106050a020f0a0b100504020c0c040c110a240513110a0b03040609050f03070b060609040b130e010f0603030e0f01030b0d0f 76
    0x1c2d0310049000c0e0700e0b00044a00020310000c008245d219a4450000080c10b06190b0456919005001d00044d84d5101030164024112650003061036100031001055030f80c1300500b803101254410804d1207900785031500001c0c10345075036052950b5940b101c0d1101300e2600e071540900c280d0f18010303c0d00b40b00c2041444000580500d002014402145444004203c01c030f10500c5805e42c41c40e400801649814141030f0080c90b6204805e0404007000800c5034002400d05080c0001299001c0c8840070000354000c26044458030488036060410140c504601040e079110928403000e40f60100e0002e100c0103a43d1094240e802504230610240c1e100e080600c0d050025011340e5400700e4848c0682418900710b042c0c0001900c0f0b0305a0000f549038580c1d200c0c0c04c140510359200903505d0780c101d600e9485074041500c400c0036403100700c8810300c0005130110242c50000e00311048a010b2003034003414a001000460ba0140d01801c0e400011102054420114401030b00207014546001c0c2e00001c51001c85400e02c0920600600e5150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 572417158 1250 572415908 572415919
    0x5040b06040f14040f0f020904150f090f0b040623090c15041701021b06070f0305011206051f0f090513020604140a2117040302030d140d0c03050402 65
    0x140320b001c00026500c40300b5500d00301e000c0150010b00443d40c080c02c51030300c4502a124048082942d50041400c2003800c4070305640084030004403078104852440340424820308042c080004000690b20250140d4070488003030040b00401010038184840ea81c8070000d10700c03880b04d00c0640e1aa0b241c000600442040f214002c850080c0002440142408108244a00210400c503440c00b4249200f460705030060820044003591309000c007000050340702c1d80c04200d030081032004201030303d407001d401407031901c14501c118209030600c0010440d9100500589110a1f03000801154bd0790b00c8400318000300380e8400740d0302581400746800190703285910000030156520203900303201d03559031600302e600410500c000094100404000401080030f09109160044000400385c40c8655a104801500c0464859400d809070718400808420840c1080e081c084a0301c0001c00c3d039080a156400203601c5c0c41020300b49001340550000380800d0f11a0042c1280c04442c0140750400c944800d142c2c000303000704400c890032030254 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 572418408 1250 572417158 572417171
    0x13180e1b0312070b0619030210090315090506071d0904110306070305070509010c0f021504051014090415150207060e010e0f010e041d010504170f07020411040905040b0604 75
    0x528460040710703c12600003901105507116007007407160480710404020b88040a0f00c0c004401650340660250520441ea0740e5031a8903421030030f001c00300010340c100d070181d41460100901c0000d803010410a50051850a000700e4800c0c2c104015110007084160442e030094800003000100107608440d00180c2d4401e4088601c00d698220090741214000c0d10008049907040c0101106584507603005804144030b64000314140329280c0c081490103038500886c0307144980104040c4200e040c0051501c103071111915140311703d40502c02c030b43c03102440b40502c0d26000f140c8884503c0101950154408000c084d14420302c000d41d054030130025121070303260041c0000944040c1d1411103541c400e80c041d02080e80c0003031102d905000044010340e50880004216900030f51104035604442d031141440041105220001107010310380351030481080300c1080d00f070700c150314000e01c40c003c2402440c6d01038403c3c065040e1000106a02010020a03090003598031102900c0d0030001000100300b07014100740d01401d41a103050100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 572419658 1250 572418408 572418433
    0xc0a030f090305150a140a091214091216090207060506180f0a110d090b0609040803040b090c0915030c090106120b1c0b01060e0613180e1b03 62
    0x1555642d20001d40154004840604034200c3c0015940d0030810030f01c00051480312001644405220071030301c1c100300d582d5a0109400f40821f001340d800b5820010301d0980c41c0c0c41c0c1e184901c0c000318054418014000e50504010b221910020404042c1881c0c00420f204c1019903100820006540100c03011540541002c001c03e410b42004260480034102c1155401004d44d40c1841081380000c00803d068181c2da1111180040d100780340c0001c140e031501004001c1050b11150500340d425a41c0a132109000d41011010400400c1002c0c05581e0020307449100320302c40e0740300c4100c2d041c43d102c10180141c0e44021800b06000641c03c09210b2214078090a9007911042002c035002c00c10340d41000d1241c1400f18403030310240c824503c16039010030140718005281100f0b0454200131610f488504400407280308580c41c0040c80306079001000c1d264410012a091482c1c1808140c1000c001e250354800c1070000c0000c4403c6102045450b0402c520a840307110403500302a201d0010a03203201c20409503030b40203008010013820b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 572420908 1250 572419658 572419667
    0xf071e06032708250f0305030601091e08011a0a030f0f0606090e0f07243e2409031608040504180807031107090219080105121f0b060c0a030f 62
    0x502500070710300145da0a0303d5207041c0e13016880145220b0400442c05c3d00804c0d901c00500011040e008840980846281000b20440c211590340320b0080b00400301c150810103a80d50704c2143c40c10f0340d07480001000060058a4640c0c1032000ca400c009000070b04000c1c000c1744400c0e05030301081360003542e103040f20700c0b040c190445551112643d0041c1400030307117032100032442e20001d2001c80315001c030300f46440d8a42c00d00581c4140e180034585a41130840c043d004500c0d40030f100c2101640640320388044040c15402c1503000e403042c03804104034001c03041c101107100002c0a4803030038401c3e03039400e00d0412241c01c24000b152030402099445402800c0c40f40c1e1401c10208034924040d48001c6034282d0100e9010301d0300710036231001d5482030000c0c04145400c0c420044046071890590026060f25101b21000c100e034904090000f40c26003805070000c5005078645c06109428110000d000a08421100000c0d610f0b0f54544282c00081c1881118058106030006480c040380075002403034400d928000d94a0040031480303500101d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 572422158 1250 572420908 572420977
    0x1728020904081c06030803090105060a060e0907140a120c0201200c0f10090203010b011106041103120a021005060604030803070e0607140f071e06032708 67
    0xa4011010318002000a040c800003000c0c0560314825640e285040f40d00f0860541d00c0c02d070003ca401d1400031090001000302405180e130406002c0310035014540c20008010300c41d81040d9101032040c0500c40c00702d880c047c003500d88060f0111804246035035a03030b03080d800502203411004a01c43d04a01c2c218800800c42c0c410312805210600c4001c42c3d510b1161407001c0e00b103481d04900c42100c40c502442c2e03510744a0a80c108240c40321144c00c2c10010841c18407a004040c211a040c0e8034485c1884801c0d4010a00d8450200b5030540c8150f029545c82c038002a0792010901d008140d0100c0e0064400c0003440884194001a800b02003000e1000c00707102560303032201400784034040d510004140d84c07420300c0840e18907400340740308444c0c038071015090718140b401030384440100203104005108284c004610241c070f095401e100c4d00c0b01620202180f04c85450131401404044031091146504042c0c0d10000111214161040f40009140c941599109403c0ba81070103002ca50000da0b650450004a48501300070340c82801c03011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 572423408 1250 572422158 572422163
    0xb07050418090614191116060c11060a02072a030803041a0411090a0e03041a09030f070501320f0c07090b041401030507031b1728 57
    0x91007003290104800050038018004407075007070301e40320710003030984000d01030912036642001600c1407040035040301401c6424160076900244001c202d5107441c0c80d440902d1120040e03022400080243e41007008442031018060006078038001c42042c040080303060b4016041d814040c000001007000000c82a0308041018441c41d500d005140c802040443c4111001d1a030080c010030700f0109450315010454514030085504407044400b620150782141040d02030582d02c4032030fa840c10401d0b40c00c44400180c1d0b83c000c4d40b0880855aa0583d2501492402e907816142d0b0f4440180454082140d100c14003502e980340b80c01441c7c00a5480c240c0440c043e40100700030f095402d45540482d030201a54140207a507540f111203d042c201a00708810081140100008070003400c60150011740701030050100420b6079543c44412112030f03c0303030f001440481c0d000b00f500d004036a404299045810103c0c0580800aa85580510010580180c00c1042c22001007400c41941c01c580d0781e840f02045494250785044000300801 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 572424658 1250 572423408 572423429
    0x70b13141b180f09031c0212060405071d03070b030a0b1005030f0c0313020303070308040201080105040e030f07023010090503030708070e060a021e03030601020a11040b15070b070504 80
    0xc0fa04656003440c18981046940058034a412019400510745811083c5a450202ea00083c3c04102c0f0030501c2c407440d0400021203041c4507606002800a14000d03001c00366800a00007403c1d507201e550b6013000581d00900c02480780544916040306950300a114030305040d8020704070007040d03404061041080720b2143c10104182511a25900d014400781d4100416a10801c1051407450000d65010800307005a64800c0d9110300c018a411b200040c840c10703040e4030084c0541e04240c60440c0540b40030040c0c580b000110140c9940311001400052000111041c107441d451000d41545654901d0302e00c040d440c00c0389560115010001403202090444040040240441d003092002c10f2055100d1000c003900722b0707003600c1c0000756000c0c6940022040d5007d00c0d421000742e400150401c0b07030110525003100d692400040030350704500e04000041e4a89452840c000c0aa040c00a40c000320303a6216840006280c4024000e0841c0213400d800540940d07106100643c0c0b2000c0c440d0004800e148a182141e0036282036900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 572425908 1250 572424658 572424661
    0x1060e070f050903010b06040b0d0b0603240625140303040305040e04020307030212010e12180d030c0b0a0f0e010b011b1a1003170c03070b13141b18 65
    0x1c0485040c1c0000030791560554a50042120395a100c00240c405807110012182d60740c414455008105c440c5a1740740c5000e024180104010310002443c0f44079402400e00c41c1c1c81c0e84400e03480018080340325100c030702080011003c25260440c0c0d0a0745d5180a80761040e5545070416003002c043c546d480c08121f070000d002034010407060104040c00b5001c0d9030070900c040c00304c4640d2500c9600203070081a4028051060780c7d5243c40e81c0404140070050400f000c4030f11041d031460015140300c510200c980c004200350241006a0102d070825215000c02c240d10760b0000303505403050a0550300c00c0098484407091040b01804c0000d160200d900611540e41c02d40c40507111301c281d80081200d5a030315403904040a41342d034101a0059034243d0181c1c00024400d51041041134145419440c040030302c543d030faa07568100c403403040c0000108580000221004181c1105920351a50364100c5c061000d04e46c3c6c40c02c000c04da120450700c00e980e14100090400c0c00411214445210101c01c0d10921012609011000101000300f10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 572427158 1250 572425908 572425937
    0xc0709020f090f030109352a030d020c03040312180e07170f060901060c0c050103020711060c010603020111160909020f120a02100807050904112101050301060e07 71
    0x4103c40c02104001c0d0000c605d0608036110b24401400307041856030029940300340080604403021030300c043c038070140c00d050b030400120350003041720a0250302ca0080421918506405069402c006850805040c44402d555410000030040c4d01c0b500944030071540c15240c0b24032060210700070861051180c12010101400030315086500e801035030040c208409100848880c00c0c049040040c0440c812150010300400c1c900307080703003072021044050f8000340401402e4690503001641ca00d00003070890307109103070150700c4144904083c80d4440c44000295845880009d00780307480314042d0410000c0364002d0325400041960f2581603030300c400c04050890b1a00c1d111300c106000082c0103a00011010303001509031486003541d1008202c0740c601492130068a079000f541450218981240101c504c1c161a1034410a40c0c10f100c4005403550080d194043e01c00d03038132550091080c0442c401035401b00d0030003510506207410810440d0040042c00e02070b980c029420f02c540801c18103c5804414094a6035a84000d07d803500c26 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 572428408 1250 572427158 572427169
    0x31b0e012c060a1d0115020a0c03111815030c040608102f0d0c050a0e06091201020a050705010609090f1b26010b0d020f06070c080609030c0709020f09 66
    0x4140300d602540f070941c0810501403200303000742815140340c110440c1e0750401e159828800044403442007190300403600a00041c005d103a108048030f0707011040c4220403d00742e0025043c91008000103010040074020070111200f41e40107288411010307030030399814899031020300085d41c0300c40c000c10b07013a82d1200d81400c0c20040254030540d201210200724843d12110810242406641d020344101106004116440c80c0b004500c2a42030f810504c1c10900d107070600c022000380940040101103481040c0c00709000b44143c880c24447c02d14490740d00c00856694626000242940c0c201010546c0c1c82e610b0a8001329003041c0c1d5118800c400f80d08801d0014554200366076202e2074214515090280403178542000407000b081011502104442d0f4800180041650807000d084513400c003000c0344280340c1d840c900b50150b2034036006008034010a840055032070380702c0e00744807454103810b5100e5800c5100b040104800354501002a1124417590026a02107d980b01c4140099004001d8580780b002c40401c804403851800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 572429658 1250 572428408 572428411
    0x14010809070b0f04050a03030806010f030b0a090e190b070e01020609150c0f031005040e1b0613080a08030604140c0901051303230c10020c04020d06031b0e012c 70
    0x240f0001c0c5182c6520f640104908540580c011000b10b0010014000380d03680000300e8541c403201c3ca144c01c00c4107409007000a00094510b1282056041d0740c0c0d1006c840744d203404c0c040015410000c2c0c05212181e140c910748460b2813541112410000f03645490601c0300b41d0b101040c80c5002e41648001804c80f243d010f13290361550500900040b41ea00380030855844108030b2840071b58403d0b080f400ea0310b216546044144415600c120011006641001c0340152080c4510304c0c40c010300c4c09090390383e5502c410683c0b0900c000100b55802c51480380c032501c0b0070442080350400003103204000540d82800f40354001c0d441a002d00406595001d4000ca0a000304066075118201034520070b69481c103480c0055550f61500741d14150384070f04507825450914a50695610304102030061010240c070246c40300d03424080001c2d12801005d020034402c0340c0014400c01140429001400550703000344580c01030400425040750501120b03c5200e45401c81000002203890001c41c1550103076a50310182e8885000800107500001c40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 572430908 1250 572429658 572429677
    0xc050d08030f1e0106091a0f18040216151b0c080703140309030d0e120706050a0b09090d0206011d040209100e0106020a0212010203100b0d020c0d080114010809070b 72
    0x5940c5880e803101080c81e080e00d4000d03c1c040d1034106c0300c0e031300300401c801d00880300e10b40c5602180d04c2089a041c626651104907200d00c080c2c1c1294a01040d1b101000a0280c80741542d9070700364011408160081c0214400782d0803c001e00c3d14030400c449508100d0741481620f8081c0306901081d000c4c0154808100e4180c001c1402da4440d2078484c00d4054240a285911780043c0c6490380580d00118001240a0691203002030000e0500d0050200d200c1004903c0c1480c4a1420020302250321000803d40484007504400c0d40031000818541091910102d0f4079500d02c40580c1c017a00501c105000003c0140c405c1258540e40d5100b0f021508155940d40c0074402004070207803244010702080040000d9004032450f4040c068074040d0702410020341103004208581d0f005c82018416a4410001d201c10714007460036000c125112503800c83e8444c0340000c0c011000b0301850602d05450f00550750728000140d40144818165035000140c03d03040c0703152400450b010790086440581a90003603505000c2c0482c41000b5041864 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 572432158 1250 572430908 572430931
    0x90e0f09120f07080d0c08180c01110f010207050a031d030604031b020301140907061409040b01170109060e160e0f03012c070b030705090607020f04180c050d08030f 72
    0x1801c03960303840d0141c5c3c84a0701c2c840e6055611030000f05511790110466401c0625000c00101503401444401e44415a1203541414010341801c0c0100790501442600008000e00c002151107100d98104107071200e080c00340880004012016949001441030001c2000382d40150050420369180d135026141c0d8044a18a101d101e50104011001070381c0901821401d40b41c15116040582081c11400b880c010303a64206509000070891455021a9080295540d50304101c60215078540c422006070384211312413900f03da45000e800008600302c0b0080c1c03c800d08603208800a41c0f8945e03a03000700d22248514054040b400034204441c00010392402c10400c8041090040000880c140110010f210b07030641e43d020281440c00040d284075200a003480081c0041c010510200e1440c51f004000500d180311302c00301240305110110300344095484020641c0034050000d8000c00c4206001c10040c00740e81240308049075015207030721002c40c040c10840314030426668003442190554a4030890300c0500b25005104030200d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 572433408 1250 572432158 572432167
    0x140f040302060c07060f0c0f080f04030812010302031203060d062d090203070f0f06111204030813050303040b0702041d0307080c011116030503150a06090e0f09120f 72
    0x1695800300600c92003980d1401444c1d0349140c64405400304134016664800c1c041141c8030240800d49902c14800c10f00d50001c4d0050760340c1074003894201b2500540c1c03c00b9003d51404502c0c0001468050703000c074180d1303008500f1903041070b800c0c5101c42c1305803100322070071604204000b500c100001d006030403501d032000031540c444010340b140c1102c280803100c012425880c0b0f80c0e110045130065050510180002e00842c80320254614200a8041c104503114840c1c84100702554100440b2118180300b212004400251030302d9446541e401c1c510401d8011403000407030131050300000242842c0c00002c840c2281d401c0140c01d0b0501006e50208001400d018030514000070300079110903072600f4140018003195104003901ca444942840b8114210340360141000c410380d0041021a540d029219503c890a5602d4a0681c1d600e60700d01a807942003100c224000e40d04065807040c003040b00c0e5004000ca000b524410705281e165592000c2d480c0403800e800b52a10001508410a5200c0c1645100000e1420132b52403110756190 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 572434658 1250 572433408 572433413
    0x9210e03031c1802030d350708040c030506010303090e0f190b06070b010e0f1e0a0b1915030b15070314041205011d0105061f1107082b140f0403 63
    0x400603003542d1540011400011f00031403940c21140d0300807145141d02c091504008008220b46048400b500e0078051000c2c1000080c10020a04080c4000c1c550020550300b00d035a40f4139001c0e240504500500f072141c2c076079400246480e410503041c907218402000a9402112a0791a24001840c0050f01103400c00c408100100101d20a403880500a040c50152043c60f482c0000d80103a41c014094091820010342e459205841d419851030720790014069800010b034002c480c400a180c403940c001d01588500070b040c1000031210641041e0708550305054a05100c05046002004041e0190001450f1031940c28048900070a208415854219905280341c905e000c0d00d6030182802c0c0a0044000c60700c0c2da4540e80d002a007180703d6603a01c642c5504800080c000e40c02d004000801c150300180c0c603200ca0018031030301503648a02c1020400e4a18250409031030130300c1e440300d01550300d42c0d000c9481240c0c60210301c01030090395101c8a4901501821580d10303440b800000008038450340c0d00241c1c22001200080c00040701 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 572435908 1250 572434658 572434663
    0xa090b0612030c0f0c040e0a0b01050405100302040c0c2102120307020102130f03030f032702011224050a0e010e07050d230c09060901110109210e03031c180203 70
    0xf2540304c05000f080720602d5103080005a034044000380060740c02c034014200c005032818030211b06444007110081a107907241b00014600603075a50000e54014103202200c99542c3c0c21401510b810350092041d4401c5010000c081203440c1542240100180c0c007030715516038002c4106005e103410984520002d0f140860014a4040c0c0d41c2c81500810300a01c6612000c00805401c8880345400d09030742d00342030004601500120140306c0907420b10803181c40c50040c1403011a84111401c1d204461562030030040c00d005500c2c150784400b0717910390030100f1920082d070101c1d01f4500101c4903021242c2e03161000fa000d0f820100541040f032000b07000001402030038000d2140310400d5000740030301075003120186417132017090000a4142d20805030101e0140c0204210458094540000310703582d6100a00f05a42500b44640c0490300504c2c5e01c0c04050604440c5803100c03441c01c2c08540100c621648c041c0c0c0c0718150360a45030109500c03440b07a2641ea00090502a00551444a594000c9006007241900f0f002c0d107030607990086030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 572437158 1250 572435908 572435923
    0x910230106050a09060f0c0303090c0b03070e030105010b09060313030c0b0412030f0504111e0409230309030706030506010c050601030c081002040506040308091504060201060302090a090b0612030c 86
    0x2050003c2000d24000c2d9120342400c0c014252807820310b802c0e1740080c0000d000310801d4400a4200754488128800b404250380a003001001002c51036940e91030b0403000107064907002c2001c28030030350808000040824a120998000722802802030746184c4450380f40c600c0c1082d401c1821020b001c040c59281d0003007506008100d00c11402071a41906402c15907100074102c0720500701015640b4904802d0001052114003907628120060302c800340e180601951220f0310003000c101c0d45511500f401218002c1000ca002000360390b503407800070810441074486c0115228021aa01c05426521120003040000d210307401407a000341c4181070880d0403210700d0b200c0904046090300152480d804844040090100400452401154659045040c00d040100152551149120141ca940c8020401310850350340e0f1504099641003090f4110380e1186e60794000380c06003082d80300a901c10750800c000259109c90502078110600d510900349030403642c40c0f034100842d143d401d11000d03410b440305005440300380c40c08000740c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 572438408 1250 572437158 572437169
    0x3041a0a14090f070b0d1d25241710080c0627030f0a050109110103020301030f0236010312020102130e04081606090309050909102301 59
    0x410002240c0c03401e40c0c20960003800c5500141e01100140340d48050102d080026100341d02c102d169540d00c8110701c180500800c1451285c0d400780d64480708038030040000e0090340f810400f6242d0006042c1e9640c0c4080d000c0c00351050181d00910107944142103814280d00c2030b00524281000500c81d6240303000c12148c008201c0c2d56003203207150001c00b8011060300b04900d2100080c02c544052601d406619190402d21040722108003803244105154001c0d90248046406140f01d181100c9643d442400c00034003809d01098280c54402281d103064070715511070f000300c2c1d044ea90008440c0c1000034241c0d0a0260840c0400d0303000704201d440540700f90300500b003001c202804c0003185050300210350450502d5141c1c02960640e01095a104203c42003082400410000840d4042100081c1e280d03560f0500d1f00e00c0b840b4030035005402d10130442012040180c41c0c2c0c0040040c9000395190542e0541350418000032440564040702d8039130009402d0700c03030741e903094000c2c0101c3c00c02c01c940c88411040724101036000c02c9080c0c020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 572439658 1250 572438408 572438411
    0xe031219230f0f07050a0513080a080406080a0903090b0c150123041b0809100c03050123090a0f09060f0b090c120403260a020318010b0a0b03041a0a 65
    0x10702903a4100c0c0b1209a0308035412202c0500903013440b010140c0301e0f1140241400034080c0104e04407400c560905003a0004104200c10b07210400c00b0f51401008680c86401008041400030300400d940c20414072803250700319495140ca804080c2407034071590032600b0442c80082580b003080700020411842500c2180200003460003600c2034000500c00a08101080321041c1c0694506083c01d06c06825445131952043c482e410b040d811610340326140c0d42404171505060404604005000c180964541c0c4090f04a034000d0145081c03052602001450541c0781e942c0d69544030040d5004a903101d038841d07100c40011070350740c48005804941da42e580f5041c1c0d28814055200c081c2d41d80042074650605403881644401c41c40d140750318104100980d50042c2c0000740c4050104100500c5119070401c6c4c1c07403694a0110f84501e520003d9243c25030105d4040c0d40121500d1007040301020200c0641b20050203880c41c2c0078801030a502c0068203000f083c01103504028003d0760f07809145910b0b44101669600e0780c80c06604521130 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 572440908 1250 572439658 572439661
    0x91e01020408010b06070c0b0903250e07170f070908160603060605160602070f0b040b06030d09061b0503040506030405030901080f040519150e03030108010e03121923 73
    0x14010701311041e00001500440c0c08114a60005800c111003a01f591440c104080e02c03110207002280c5440415143c101e48440341c852800c1d035640070f14603400111090b08241400c2559139010841d8040301d08920040e080d03d04202041080e103d251a0f643c4c0000ca519001003000e0ba150102c901d40703e4059286481948a00028000c05500d030140002814850034404e20300fa0800c00303055070f00d56112901401031a8081548010401e8881040024540281c426480ea0510f8100303100400025600340e0310038070030030448402c114040c40f150812114607840d0007411005203500b07001080c030120412142c5010401012449a6404000d540510b0003100110b44030320445002418071540035102070030003030040040100180c800505484022520300c10113800038030b9454110b15000359840407128150511801e12101e00b0004007071412150032030002e1020140100100361a44200a07c41c82c0c2555004001034030312285458158040d8043c500025110341f15915100028661344850702102610301d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 572442158 1250 572440908 572440919
    0x60b0a0e09011d1513020d0b0a0c031505150903060108030d0b0d080a030c11010218010201050609040201020c010f050f0310090b100e040f091703090d020f03040905091e010204 77
    0x407480100159180c03036a0b2440001e91507140c1d40e10702149401c0f007481c0386100083e030079080b170a0311444c030180c3c00780003032200543d02c0c13500024620045a9a0822078600601c400b20310b0301c01d000c3c5401611010740c0c1072000d10b05002c24031007a01d40a00312075400304030420040c1c1d100e40702008018001d0803540c02441d202c82c1c500e254607054600340d03284a8412101c81710520041102d0318111807a030b15241c02e00003203c0c206007a054403680c200480c0c54000754030114001c11101c4015005002e5800242e0080006030ba80300100705403580e0a0306c0c0a40164840c210100300346d4043d601c1800e046840e8180f1074140300e441c08071f1003004e60080314071406411040e0707001c1051026902804001311000c643c184103040ea6010b005000d403601402591040d1340369070040e4001c1d0443d61010810303580084803030103581690512403119038415290310806129011a07041c0c0e603840842d00f10200401c90010f549010705d00070009025040103408030300103000312008100c803050380020072001d02d40514005603c842c07808 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 572443408 1250 572442158 572442161
    0x1120b0d350702061215031203090d03020f03151807030902120a1a1b07081b030c100c051b0c12070b040506160c06210b09060904060b0a0e0901 63
    0x140c1e00300022400e000000c01a5600c9003030719841280303650081010782c2d030114100708020a10030001d0300b60140104170309603103d5020095100f50b2088080700c13101c51044008400b20706c5850b082503c500410310200e1120180c09050180880000306904c4c00c1d0408800c00c4100a0f1017511020003280d0365111110450071b22841500303a03860032901401010300300d5164a10b46598041c1c1030000c251106c00020700308001c803000402401040c0261640305e0045140c00e1301660b020342c81c0c01040300e580103c0a41c40c1e80f4004222004100000d018005201100903c0d03c06040120241c5081c008103210729100d0035910003401d00e00000040041010500b01c0f401d00c028101700051818007600500004d110066200c3c0440d030032268140c5650340c0e01c0e0141410100340f2020b018000b0003240d6084000651591300c20340159030040410070b104030070f5000341002c2e411194840e4819800184180c0001c0c0180b501d0840e090740f181c01403102140c3c04070802c0000340e0003161034100d00c40740c0300a13106000c42034809 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 572444658 1250 572443408 572443493
    0x10b07031e27031208040807060506032e05100f030f0c03061a01030c1107060c21081b030f070c1a010603090c0e0705090d03030b100f0305090a0201120b0d 68
    0x20b4140b070140c6082503207c03207900b48519a4090032554850f030100302141c40c06c110540081c041e058000c43c14400001d081c001580c906d0901d92401420b01d0702041110b80d603c144e001c1110030744d8201e203500c4e030f1440d2703242403003401d0818041d0340c10108640c001000c20100c0c041d0794080b010b0f120403510050311070350000d01115007c104500400ca10b0044040321004009601001d903981800c0035040302043d8074000d013000000c0c02d44011101140c01d80390031142c1c1c1044003a40a001c060bc14416040c001c50001c03000c0c5d010880e03249010050400100c1c50a45c0500c00030402d590081e51041e41b011411092111035150aa10210001e41c0e1440c000e0309015060700703d40c0240100004524460600d05001032103800740c0005144220b2705150030004040c00f95201c2c061085015101d028000e0b815200a041003102c203c9a002003800c2900003100d181c4089000d0130b449605031501d0760700100d0b0321140c500610b003859805410140080000b00460f4503070448040c2d240d0302c20240d44181c1911a80720030323202d05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 572445908 1250 572444658 572444693
    0x30020f031611060705090d1202060108100c02030a05030712060621051003060c110105040305130b032a04030b040b0618010e0412090b070c0608010b07031e2703 70
    0x40c0700300030b074910400115032550009150300e03005880d07807070040c0020102d2601c08002088a04010104240d203500440c245048802b18801e40b092080d0a498031015140640080c4005030010030600f01054011005141c00104c03d02d030440480e461040c1040480d5804c0c0c2012012840883c40d84018160700118200f48480407401403100c1d00700054183c1603e0541d0000038415034541151b131000c14403d40170111000c0310781c0000d02c6941044e040242c150b9100001000c90360350541000b0403441c0c410b4007107070302034440d1103001c070113404022421486111050000c1d032070ba4501000008040f482021405010710301451104034181020001c1082c001c40b09103400103107054601c0100f103050900307080c05911580241d030848042d008028225400d06007500b1900e40c0001c08900c800520112030756201c15a001500c40458a0b621204954018000c0703100080000307003400c031418415000a5901030100040381881001444014500d0a49410703188211a0350348130900104103029680300080d50703485 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 572447158 1250 572445908 572445917
    0xe09061005240d0212181b010e0112060f06031505090c03070e03031204150c02070503030f0c070509012304110f09030f0102030705090a08060730020f0316 68
    0x9182442d60098404801103040c52a00301080c950600010b94048415200c44a0410034142c41c2403402c0c1004001018500c0c4080e2145402c207007107400c40c486000f0000781050f19210440c046541c0112800c180d241e80040c805074650800140001914140601801417030b00c0200340c0040414000c14070b200306500181c414603a201c240880841281c0850b5000746032440e0100c8003140c0f13800070078698416186003000d0b110b1410108000c0c03200e2050000c0d000c2d10100002c5c45840d4010004a90300e0411380100d6a064000308000780103007020b9002401e05c40b01c0076050f07603d125501d0000940f244001d90045610040300725064000cd050854000d003130a600320b400b044030784101d95020801d40a40300f1003100c0440e001801c0e171040d94007040003543c4040c500c030003556a487c00c000024056001480042e0060b101040046560070000c2100e5200fa201e5644810300503100c480880381500c481c13240b8a040720104e11003207104050a00040240206600c0855034a0a010319072000c00c247c0b03002c1450400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 572448408 1250 572447158 572447179
    0x50a1a0a0e040e010c110a170a020102090603161d060412030c0b090c0a0e1302011d0306070e030c010e1005160b01151407020d080a09090614040b120709150e09061005 73
    0x2016540142981580c2134501500c4270200300c8c0990082c8681509190f0049010081045440b01400b00c05450314981d07070741544402c0e81034403103220b581c4204c6415030b015400b400103106081c1070561030b0140c0c038000c1c40d10b01b40222071920307601d611010641d07058415801002c00e0300c1f001d04041800354020302501c0414111803a222000d9502280d1204000f0b040010315038514800320600d500140d0b02c068010705443d624201a0000703041090404e00b0207001c1e01494121041c02c0d03008200a8401c1c7d07030090844000b142c1210022211035100001c48003c02c4183e15420700410012454a4040c1c44440725030202c5a00d0028041d003918000d2188101c40d0408011031001605d0ba035140d03011856010b0205030b19050302c42d9040c0c2d921000354114400807490904005101900d03048003132030004c0195810450880000305021a071000003404d00f00075445007104000c14040741d03111181c0d9443c250400c17a6010740303031040640a001d00391400ba505904c1003042c0090191022001001490304645d0503220 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 572449658 1250 572448408 572448413
    0x1080613050706080604020c031321031407050a05060c030f1012030f031d0c120606060403122c0117160513030f0b070306050a1a0a0e040e010c110a 65
    0x1148200d0143e03400300001c3e040868290303100c640540f090007101206503a15207881e1840501c0e82441803003540b28041140c00b034031007050012858a40b010303406944624109106121030b01041c0c2c04a001100c0e54490068601d012440c14030000d801110003008103662810440c1d0a5030b50080040c010500701e518103101003021104035254550055454109096801c000e880d0580c024041c0c09440071b12101070b113240b8007050001052110140e00100d030407815040c01840c00f02d540e00c4003110800e030000d800304414030200d00700c0b00303861b50b45004514202c0d48000491004640d081d038400c80394022850b07008800451507811040c102c43c00302500251000354580040d9059204c00c403502c8001c00d2040c005200d020301c0700d513448000042c3d90008106c5590410314030b0281103c0100f02d032030b0320000b80350050110b070500d001c100520454030511a88100c80301c401004141a501c1004070809100303178088090620384031401100d041c1c0c0c17502400010040140200641250fa40c40c15241c1720390071503034001c0300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 572450908 1250 572449658 572449663
    0x906080109051311210f060c19111f0204030b0a0c050d022203030203070c06081b0306012606010f0206040210080c0d0207060b04180b010b090105040317030108061305 73
    0x807040c0c004e540c9850b92242a00032455205014050641d8108800080c5408041c00070b00c15008040c10001c640359542c0e0001000b402d400b55007085502003294603103400a0038815a0f03003a00d10f041300300640d2038507039881849403040138012101803040e90300410100107020b41c43c010b4580c00340b0351300400c0c401c0d2048030318020458824621500d540590110b89107002d8a429030310007040f4004075051038402034503801e020396603810140003100e078288007071008150644150074883c010039260100340020400c403403112541e500018017540c10003011401026001031080000d000700403080c0160078290500318001040d00560f02610010341d40000b06010040c0c0b2001c002003100713000b618050400c0d8a40d1402d80e102441008000c041c102e00100d080c0e014000d250340171180491f8115400c02c84508201241c8000d01406400a03100c4c102400c0108400d4040000406e001d000500d455450075032a940e0300505142c0c1c01107803055486020005004200f010409107800258060300d0003407180d15552880ea = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 572452158 1250 572450908 572450941
    0x10f0504202a1006050a1401050a1116210b01120602070f050f0625030c030605150d0b01050c03030a11120a0b01021c0e09060a05030d090608010905 65
    0x200700034800201908010710180c015190040144500541207201c9999240d60703405040000001e20b182510000391440e18000103421a940d848801c8144164880103448076003040f0b000d60300344144903191946c00c2c0000d1100c5000312a0301c4101802035420000481c02d174011420b451184880302c40e40034000b1644886100b41182c0941c41005854805450160041d0040c00e4005194414045a0340200140400c42c2d01e03a244041d0111926944e0f064030f0124231041000741d141301d88052403190b14450b031007a00100841c1c405070801141c3c071940c9a001c0b0780c2103a03000680305401c500208050040403294002c0c00580c50003440c0c06030a00e5a807658554580c400a030004100f03a03525102200c039220b00f0404e88a01d03d080c0e09800c9903515194040c000a0a012503449005020345135902e00f80700112401115501542e076640e9407520070074420704c5000200030305202c4c2d01650a9000084942c6c08102040245445584105d2110300d0070354080d0030420184c0051120b02d0a1030104180d004001c042c21 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 572453408 1250 572452158 572452211
    0x2030706110c0d09170d050307030b01021501060c11101b03020a170a0f0c200a030b04050c0109060f0c060b0f042a1106060d1712010f0504 61
    0x75240600e03106045151056561480d031500a040c1100d06050700015070034112041102e10081445420b011140c540d44586507070000f140c014804684803d200e0740c800c1a80d04010300403280e0810f03240b11910042c0b00241e02c9280002c03007610200c020002a2000d03d021030070140da551492a030041d07009405890409030300024840300d0300d00901031501c20010030050681142a445034400783d0310990420f0741c0070182d81c1000c41c229404000000b48142c40d82c584042d041700501701d03031000140d01e0782d14450000461903400b04074011f011010803000c02000d80101e01c5540145401018a80054000940390b408242803020741541d61410382c1d0486110711000f540407800158283c1c0c1c5e840040e00c00c45843d11015041442c15107210201d40c010b040c0440e243c414030040101c4d440e007a02e001c4079081680b58001c038141d00800042280c034106031581c070f958540301d111100b2940c002007448640c0d42c0c0050310340c0041120201c004000040c00c032540703040070308400e55052040070b030000c111003102c803040c2104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 572454658 1250 572453408 572453411
    0x109121e050f0d02010e031234140721051b0106030201171306050a090501020d0f0b1507080729040c09140601111c0201060e0901061d102c150102030706 67
    0x140c1c0f50320240d002004e80c427084112121403241e0329100c20741c101640910380f002040404400b2461424a80c003908c0d0704a41c4100c844940840c807a154040d104c80311441c917000c2c050300b80324002c00b1015130810a01c8200b86a000010807a1560000601694018551201d62605d000c14868020b81c009024020540c00c01404219a201c5c0c150010040500c800043c0c002d51011604603110b40d101c1d0020108200460418071541913003008000b00800406407113091010300b004044001110940078000a42c002c2010780c400c41c10311a140701541440c100140807042c141d008100400c00e501c401000a0700c40074208100a41c0c0c0c00a03447c0050314050b005d00e040c031510150345041c0c51401c004001001c088124032807280700301403002902a0840c0e004d800c8410102c27000254001a05224840403661500c0c0c48030100c8004424160a080300600864076140600d00b0118501c20600032603c1c0310007800b204540300c04101d441700c0320860000ba203200044c40030001d41141d42c0c0c0c4c0c00010f5074402604640f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 572455908 1250 572454658 572454661
    0xf1e020406050d2a1707050a021b04020f04080703030912020a05120709060810050a0b0303040509040602090409030c061503022101020c0708070816050109121e050f0d02010e0312 78
    0x8000064085420135030380b0100403204100c0040c1c0c8000e41201c61100d6258442454a845405545500038001c03c640140d11481002c4030203042c0014030440008060801031801d000c04441103070944c000c0d08440c1241d40051020020160b1100302800140012100141c0c4100a5400101685228030820303100e01c1c0d042583d503050840610024000700381040301003040650300c03402c01da140c50410724004030b5207241c200025200c0300e20f4001c4203080d40008010b9490103040500b040071a260140003910720503800c0c00b00c200c0ba9281c0e0b10a401d016802510785ea40d5440306450300d44180c0d1300400310512400c200e100200010b803180310b2848030440c03c840507503600c0101940f9060083c040c03020000514816107100103000030003c9a01c2c015120640b080d91007544140440c854400b03207600c151400101522001c104c0c034900a0000c11109201d101040800c514001c0340c00d044a4070914240e0307807900700940f0321100301010400000940c42e140000e00008150030307041900c03030060044000c4503120b51320 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 572457158 1250 572455908 572455931
    0x8040f14011e050601020c06040521071206091e020f090606161406060d0b0c0703110d0306170106030b0103020d0615120b010b0906190e03010f1e020406050d 69
    0x4015001e00000300341d01c4920400d00c58000b2024210960308503015009191490b9600d081907012a0141d59024004107200300080f48807102000140d41c8000b01c40c09000008210426032004050398180102c3c0045031001c510308102c5241c202c841180009003a407c101c000050700c881c0c0c034106480c1c504a4100d4604d5980e00045040b91040d10007000301c4044040034a0100108500307000c100300300e40b4045611b181d4a400501c41c500d01e02c010080c200c0c004140005482900010040504d6807082c0341500c408110700e8005450014184101004240c032090300b400b56000081c6483c12140042d0001d02c43c4a103151075074000b000048c00040d000b851480784900a01800e90410303864004640448402d0301ea4607085582c00f4180250202d03a10310000300002810b2070748200f41c8541e014014411490302450800a180300720708241400c05001d00c0000c40da034075035030030b201c0c0d140700011410000c6500c10144104054910070043c060740601d1050100344102c2e0b41c40760980d6003000c0d649900003120228031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 572458408 1250 572457158 572457161
    0xb1c0e03040f0e010f050409021e010210020d02090102060a0c0e06031b16050105100e070c170d02040f12080912030d09060902041b020d0513050a090e060708040f1401 73
    0x250840b09280b000420005500b0a6900d8401c0c1224100d442c028040d40c1c0304c1b01000b040d1b4590000c003a603c6158050703000320020445016120252050045a000f4002c0c05461000da800440c04604055030100d40d02d00c803035030180711143d400507903010100b1107210b51072800f5081c0303400c442c00c0744d00840c0c1c0440000c007180485074032031903e4120599a1500c8151280702201441c0313069804a0b00c55007040301145100c4c1040b0b00e000150b42500d1450b1942d0741d603c4400300d4100c0307480c51042e00c40b0001c80116414482070500103050f0303081c0c0030b14090b0ba00c44c1070040c5d140d200125607004410024800304a140440c06020544003103150840b100d0940340b07000400507285000780525604046e242c28991420080d03164401c8059a2080d20140302092000506210483c0ca803000303503003d600007105c80e43e903803803264004020300c054405185010f19150000710b03100c0981c0b81c0080c034035140c1e00c00070380c500e0440400501e940131a0728a0074036107515169035840d46401d00a03400030006941e606c505500c3d03900030f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 572459658 1250 572458408 572458417
    0x1118330c10050402030d08040206030a0f140f10080718050702030c060f040b0a02031006030b0105041a03071e0e010c02040e03070f02041d0604020f15040b0406090b1c0e03 75
    0x16411201d2071000095030000414082da8201d200b44980806200114001c0c00183d20503600102003a08541e1900301d106c3c00f811251002c040f0751a581d080c0c0401011404412500502210080308264078100c919421085282d40255a0b00c1d8025481000401c032810442e0506428051021402d600c0790b150030303480d50144102150080c0200310422484203011403030070380700e40d00503005020262038604480f000c900c4252001c03030a8600c401c805000d00c0c0d0203030300080752030001890407501d00381c0c0c0c40000303206d105501c40c50075910320380c0001404230303060740b028041080180300115100d201d415100061b140c086012141418464149614815592581d001e0300840c0c04560540b80d13a8042c61502420700d1004000803845585008014461081c2d10310400051506000080050f9216a0200708082e1001820154000182004c640d002d10514014000800d80c0b20440c2d5211402e0030b0b8090089a070740d070001000d9000a100a0441501054010041880d03004001540c0ca921521041c1180724 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 572460908 1250 572459658 572459677
    0x61a0414031c030509011514010c020a0909050a05010b030c03060f09010912020c10090f06080a090602210604051306091a010b0c010e0c0a230301111833 67
    0x1030040c03280100e2a0513402151054000e04020012203020014a40512255004a48003c200d0242c0c8822139401030380d9654082e40010f2142c480a6642c008410540e0144002100c0d1a000401403200f0400d00b40580c074000c6404070050400075400b4400300303a03109402030400c2c882580200c00700c1c141034420751103002146d40214294001c500904400ba5444003030904650003242c2160404252510603000241039440701004032207081d02e00082203d40040203880d000c2841e41e150461000030b012880148040e40c00b1119025907040c608803103410035a0300400c1c0b107000d6400c0100700b09181c5890075200c01025440000010443e090381054a46031020000d02c1050405410010442921140c09445046242c2c0000d000c40300d5614400c50b21070008948a98120b0380c07550f070070300034500c8402000030016000c100d01c014110f1140000307230945880f034580200c0e45c40c0c0020381e48161400c440b5140011802a60000b00301d5100940c0b481c000004490080c42c0720403102400f0058000043c100e072a400b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 572462158 1250 572460908 572460943
    0x705090301050703060e0f0c27100305100902030f010302060304060e010c120c0908070501050f13030f060b0906030607050a0c0807051b03120a0305040309120606060201061a041403 79
    0x290029003e00246001d02a0743c0014030507500041c4200b8044c1c000c14880c02301241054200301c081c40358011070304062020b030884650454a0008152684221040544015607011a04c1d061282e800c0300b115509400c14103c06004004014a03a084685c00c981140c1d41510841e03600d640d05d082800060840c02c0702c100c02d035420a41a05412a030040c407040c81c0052003d41000414812003041d80c082140d072141080c0c903049000200000c2d0b0082000d408000d01c060b4000c1d00d0004c2020501006942603003044500907032240b00c44044c0b002e90300c03c848602030140c900f410a03091003400641e85400c014082400c1007000038004170407a1040c040001520751160805807150300c9898100e44074813200c020114194403659480c10503140002e00d20300d0400c4075500542c5020141e050403405000020401d4090000300c0c1d100080541e140c00150302035a00030385000809a060107c001e01303560fa02e0340928500c1a42080c2414000c1c101001ca8040340c415600d160350315004d800201c0e051044141400f41c1d04e1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 572463408 1250 572462158 572462161
    0xc0d06170c01020c1e0906061b03030403140301030809040509030417060405160b070b040606050604031a01050303090112181a04060b0a0b120901091407031e0203060f070509030105 79
    0x3544001428421240241c00380d50001034a94107011362200341c031822103205400a0108809400d00c80c0c4502c2d0080c02c068907541c0751201d4400c610520300511002e42000d680300200700024154805895a07040e0005402289554990f490b4003020b4007a0320282481141c0d5070022031020b030b50400484004288003d0b264240c1c3c3d6580c04102d032500303006c41e820f542034010f050442034003580805100081d00c40c018001c03030500035a0349400002d50300c001c004454050340c404020445d41d94036030241004622580e01009142406c8414280101041c0c0c4508d000e80d10500003042079a802101c25610030310403090000d8140702e070030b080101a20700d030180541491607500d500703035111105d0800b0b00e2149000f00020b106100001d000e100c03011181c0c3c0f249580f541c005010b4443c11250081d80560411b0a0400204465049450301041c4c5c281c405280e80312039008050802c104250029000625980c403103440b400c001c2c0c0742c0c0200f81c441400030a80340c189240354000035081401130054580d0080058002c1245 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 572464658 1250 572463408 572463449
    0xe070809071e060908070605030f070c0203070311030f010b0a050103020c010212070e0319030807030c111515240f040b0c1609020304050c01081905100e0912030c0d06 73
    0x1000b5180501c0c40000c1100a0100e0800030000301034007183c07681d5498a1559480341800410580090408001c00901e00c0300c20b00541c1d0200004805140244465079141010350105450110040d51010150741003842d040410742d00c46001100f198020300740540e81c1c081c2d900c5124028440d2000b60b2916011001c00e02c4031060384000204143c0f034054040303c1500c00703c4007501c11203a11004004001440d0280010309080c400d40208070740c81c03200e00345201c1a000c0703a03030340b0382c01d00358081c41c2d1115210802041101408138102404181c4a0a17a502500d070189c140044d5501000d44507030010303100f00000c228915a160030121802040b0008048c1d4541c103009111680303c1208001662030203550800204006901d4401c5078041e80d8400000e0030029846401510651002459403907190a404011034903190540a01c80c0b040313031040d4a41140908100140e02600d0015100352541d512214641c2d05d86403c00b000c4a401003840243c0c0b0303490b6444403c10602828907500500390700e074100391907441e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 572465908 1250 572464658 572464709
    0xd0f02040503010c2a0804090207030c020901050f1f140a020f060f13061116080417030a0c0b090709090821090a0204020714030a0f180e07080907 64
    0x10780700220001d01103450002800c40e101224410110251018407450320741c02c50610f8085c1203810b03c075007505414540c2e03c5040704100c0e0030004055005c10320410f0b44408500d040c1d20716a0160200300c480414088180004c1800000243c040701000300c04004200c011038055000c4005072152071075210368031840b40200030748034100d141c21400c203842108082600a8051b05400b482082c1004241e030b011039141e25280040c1c203400076081c10740003080021544d200403507021180d402c1d0240308190341d034500c0c2c8401c1200080385075000800359001800380c10724407540301c42d4900d03043da0840100e103540c0d00c9071405070307007008069800002d0b440e14224000341008107080103440249804000484041ca040b08207080c0c41300202c95501d0f041e045000e000005292031340c090704039a070049040e0064078010700401e5146034840203e48001c01e0400310100701059204c035641105059031101c100c2424540200c41c102850003405480512030a0400100d401c481080a0001800e10050140c4c104d50020441325 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 572467158 1250 572465908 572465917
    0x41b05032703120a1a060d0b040c0c0c1a0f0322120f02060108030a0f020a02040501030b060a060512130f02090a0b010912050604030339120902090f060301020d0f02 72
    0x1140c2c90000c0001584980301032240c038803010328020f02100c05c42145001c004240e0f02c849883c0c01c03807603075450b0f01d00d5454440b84200ca8800090340ca400c5500c00c01d074141502d6116481d4030400740e05500b403140c081c00846010546945001405c8103544030744481e4040044549010300b020603002b400001002400b080c1c11034032002c6040c5444003d4005600d00080340c40341d80900179501c00381d00410458408a03c1020f088500801900c10b42d00345889560024041c2c503070a03401034851503c1c0708103000c0d90b0f03c2e00c1c80d800802070030f560809901d41000302c25101001e140003480080c0b12700600d400e980520081d11003410081e6402031a0301c90b40c1c6040205e99000306043c614050024220740b8001c900e496920070044003a6401c0801041184d455640440107070061044180342d86040c0403826080c00803070360321000c00c2903805140301064441c005000b482c1019041c90001d40700e040110705c1c400341e1078030610135820004210850007590303101c4005c03d0181c42412135034105585803426204000c4000d03409007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 572468408 1250 572467158 572467177
    0x13060e150105030610030b090106090204180605010813060b061b0105010306110901050f0c12040305030408062410051b0604020a1a0406030c0c020909061005041b05032703 75
    0x1159142d803580c00341903a0340c004980030030465920160a1000c07a4401c90855480103d403c00810850b0700d4240120070380c0c001e94007104840041613003c101000c298003600001d46828600074142d0b04c1d00035844003a48520a0001e818250b888036860a907031a690103c070740000145c41408010400b004109000700801d1209a0326540f403c82a40826181d0604503140e255050791030b00d0405602c19000c001c198400206401f8038881c00c0c03602d05038181110050002036006401440d10355103415072050902c80002d20407030095030000d6104420050090208807090025100b03103c0ea0032425005542602c01c903403c030221400921249a0660400038015100c2d40c82130f140013146d5039a588241100704086100104903030010f02041c09500d01c03961000810340f000d80350041d0020303410340114400741350a58500c0301540048007041501003401c2c3c910001000183c0e0100642105406000c5a85c54220001e00c20001e00101244400f035070310b402000c204071140700400d0954510b410007652580048000d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 572469658 1250 572468408 572468443
    0x50402160c050f01021f09050a0b01090c0905060d1a04021303050f0d0824090f06030d020f0c060a1101050a0501031e0201090312200609010e0a0f0b13060e 68
    0x2c9079609103807020041a8906030000c03e69105e5105040f0b100148844590b04aa030307a601c0ca030704c042281000903080840c01143c07010b44650410700f44809072846210070000340300495008014503120310081780e03c04c105a40c0b002031501c11020980d100c81c00f105d00b0303180d402400401c140f201440150280001c0b603220303c0c21219041e01c03a90315207488502001c10303440401c90740c100281d04480441422102d115081001384a080001d10001d004204d0958440108030009420020070b4102000100780d0b104107400103100031122980041d990703284111146003e0f1102150400f030503402500494103201d00c01000340030901e824400c960082009100503079040501c0401620010b148900c1c40c03200b641c041c1d540380031b200d0854403003064658940d90310b0300410540a8503005c40090260000c040300e0210000f600c40c2d0f0600c42c801600791003c07000b51074038a0300000c540da000140c440c1c144c002051762004103829541d42d8080c4092084200b86c8014084038180020010381c4070b80031072000b90b0813a44180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 572470908 1250 572469658 572469683
    0xf050c011514100e060403021210020a0210051320011107030b0f010b070b0408180306180d030221040f0209090327012c0423072f010605040216 63
    0x4080703c04c1101d0b90a2140c000c1070400c400e00150420400389d00805224404880d5075a400301d41100072a0300c004000d0005070032040e1078215114481c0912a0010400d88040b10f2a0400380c82d50303400000d030b00005c6445041c840075880003690151030180a461020f400f56007290f80c0c2d03070421007a244021a107000c25107a058001150445800e015100c80b1504080c440c005640c3e81c1c0d40e03000d5142d205a507a07000040145a6140440d40d04201c4a80b24082d5890a030703503142c003c1341c495460982e00c0264001414010b00c08080c503110104103034503018007841c140280c04e45032410401c0001c0c0d60244082c0d0807080e40020081d60500010041940048580000110f0800052804c400084a2001070b00050400000c0c251076140e001d0320400020019140002c1a1140c0e00020104c521010268000c0e03803030989000784640042510f9580560705051155100b042d41c0c400a000c0700c40700c0010740181e02d00b426000340c081401d60004001c0c001c0908110741e54a217608001035140090001124211030014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 572472158 1250 572470908 572470939
    0xf0a0b0405012a030e031204050c01390c05040912020712030507020d03170a0603020117221a0c0c160302010504051507210f030b010f050c011514 64
    0x3107490805911090326804078002889044001d00745c020480c0c0c0161005210f4001642154a5214080c52091008010202c680d40015045042c0c281c02d00424070791a40910540c903d20400116102c0010000c40340d5048440c40e00454079151908103d0300646840c902070704010980841160103000e40e000c46040c40d9490710b5040d031800c0031b014010000381040c403200005040c2105c58200e51482030504146130105600c8103070822400321110300520f40c45140820030343d600412494100040d103000b99009250644e40440c105004201c940420b00f072a400d11801d02081d04061300b0061240361107550b490600c0b070401c40b101e170800071115030b16002c0c4640b03e0301c000440240c6c400441e941a141d0b50704052910080081d60175212122400d10101009940c0010790b490300341e045028200c540b04001c49900305402024245841d4051050500d00440c030405682c00c03030411007407202d5071710b0301c0c0c1c3d518004001040d01402c8205914030390b50407001c1d004a03000700301e010000880f104c141c0b8090011208403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 572473408 1250 572472158 572472191
    0x905030315011107030804150e1003050a06060e030318130c0c1202032a07030b040c140a06021c030204150c120314041b15030203010503010501060905130504050f0a0b040501 76
    0x217100c002c102c1300c0204010003e0300c020410b440000003d078108600b00d25500401f0541e01e080c2c000c403400000755a101040340f154450310406014186503d05170358081d6501020035a07030721404005608401600c00c4450131681d4880102198036190b210512001111107400f038410304a0030340890301000c050a961061070310000503501d20100141c4141040d020321030448040311107070f01c0307072000c45e0040150103c0400e81c130011890141d8441d101003243d0524200311500b040f41c851034024070451400c5e40800c10070f07600003048852064403920003549501301101c250000c1c0305a41c00300e0805601c0060648200b500a049000c04900580f80e600f108101230318101d0845400364103000811103a1000304d03000ca0303549190b001c919071b142c8558084041d00c0d00c6200d243c0801542616000a4000005011500703081c015280100407034100828624104000105040c01c3d4142210302e01d9607401c006802d220003080204c03429803141095495180441c2030101d595081141d082c0c0700d560030704100a1110001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 572474658 1250 572473408 572473423
    0xa1a1c0605030c090601020c010309031202121f0302030a0602030c160303050a0e0115351c0903020d0f23010c0e030a0506060d0c0515091c0201050d0f09050303150111 73
    0x140c0c048c20780d8800780c1d40150014040c18000b64100052860050348003000d40c4002c3c40810810580403141d0710b48440d0058070b401680c2d1503030029130b00c0d0b0682040140c070002890103050b90300820150300c903564840c0c100c1c0e0702c2c040c0ca0486941040d1783c0c1c0140080c1505076121a00900d003200e010300040380d070406c01500340c40705001e4118ada913000b40000c1040380074003141000c1d0400d45c5c0014603901700c0e50f0401d507680300c1489011880c051f000002c107100110444000880c042c29035051110320140340d600000d1b07580301092030103422030010502c0b03502003122503040752424101e0060341032540101000c599008100314113410020400300344084443d4a000100d505040da408401003200b5075411060150080058004550500025102050b50b90303543c02c2c03128070001418400c1c0e031545880c804101d059440201309010031202c05410b42d01507640070044440c0003007001e801181040e0b0300103400005109528000e0903074080030041c48020f0b502c00f02c00b803610700800d80e18890b00d842c4036000c45854195 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 572475908 1250 572474658 572474671
    0x70c030b0a0f092f03010507090609080d021c050d050106050301050a0803040f1203180e04210e011803050a08030609070906080609040204060b030709030b070e0a1a1c0605030c09 78
    0x30405143d07003912040c510320040f81c0020b2510f100c4d600c0c2c603000100c0d01350f4105a50b610086035400d10240221307544041c51400600f240c9004000d042101c4501944620303d4169443c0040c51130344cc03a10300c00c0c1c0180229803650a00500400c01c6694034a80104260028000c40f03200e010764800004080b03000000b0342d001d03107001d2050102810724013480c003400100d0195007182030001c16103c121902c2103554000b402001d141c0485000c6180924094089010a00d04ea0820841c041880c940043e8080c44008080784282400760001080e00350000e0309140135400100244250740e5107a04004000b40914043d00003034800c100c1580304c1c0c0809907100541c3d401110b00040026000424910b0b0250305150030900181000903115200e51490b2110352044921402050703000204004006c1c085444030350200c01403500c00350392401440001c025038420b114a400c0800c003a404207c050b0b024100f00c078152808902d2225017001001e0303104001c1c204600c2040d10074080e640381d0a1041c01e24000c114030940 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 572477158 1250 572475908 572475923
    0x9110607151d06060d020a08030408010519050906070e04060b220b03011d0402180c07050706080c0409020c030f07030f08010605091305100e1e13050307031103070c030b0a0f09 77
    0x1070790701080c030028003603001069071f1180c40c2c04000986a107060005002402d00f6800125042c07030705038020700c003950300a40176140c0700c0d2500040010814000c0741c1c541c0c2000d12880c1ca204a092084006005031031a9003040f0041c0d130000400c19074445d82d40020001c04440c020042c13800d51b9a038032405805020910481d9110700c1d60320107182c40c0300c100300001035002d44000d204140050444818000f40e030402c565011000d580001d020b01404000c20600004185e68a003240d040d1401c0d907412006805070b4800e00b0445034000c1410403280c941070043e00c4007510b44800403611001a0b0400030030501c444000038011501450001c6804da108a044859064028141ca1440d80080400d04018100145401c3e03084003e8407001ca695003202c030044d801003401c031402700c41f503a0241015010520000d41542405010030340403000240c1301005640f02d00b501070510603010490485e03840e080d4426008000c1c000581448003000b00302c22902901d0140b03400020030881240c562005800300d6006490292400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 572478408 1250 572477158 572477161
    0x2010e180601080a090c0303080411041a0d0201022a09010609140114090d06060504060801061409060102120408030304121d040513060f0b04111c09110607151d06 71
    0x1540950700c50f980140035844005500400794030b80403840300d2039400450009080ea018482408041c0c00e0b04601340d02c003143c0c10401d403440300d02c1c10103800310480350850041c0c1302140510190b81c024003500040241492500c500d0b84070114408811031410600c0521554045c4000300d040c034451008441641ca00016080700448044015945500310f22084200b240f42007241003144e032924060081e55078441c080204000b07040000708000d44080f5040028103a1511100700101c212010000c54004402d540c0b1540c2038072001c00407070a1440c416090241e036407001800180c01c090000045d0321440c000d03100c04013445107903182241e800040401443c0381c000c241d48140b68900d401e07030000750407900c2d200b102001c0944558405090760340d2100e656450580d103840030074280c24580925110608e034031124a25014200d00b014214918000410000a96a104180c10010048070f040c0c02464014411501d4070084c1c6002502481d1051861040504000c4a0000c0f0b49914000310000b00e0488042c1169 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 572479658 1250 572478408 572478421
    0x11150402060706022106030f0d020a0b0a0605121005130201020c101209030201020c16030b010b0a02011d06040c050a060c110604030f12080c030415051b0c01060302010e18 75
    0x7241c100100c15a11035608200403181d074130100024040310036200e01c0b041c0d442c0c6401003c2504240b81200c02d4001500401d082c004407640c081140c50400340e001c54880790640707421580d18028a190303040301d50810708013440c942000d440095212b6500580780300a012581d290700fa011441603801c00b0003409030703100f07009550052501c80740079401d4000030300d0b081904100c280c5a071410b5071000001a80980d46c00601c09613029014000101c01000410802c200d00c0d15598070b1b1050a181407183e03a0030740d0000304031000c01e98400c0d04048411801514603100828802140c262105c00c2036030120340d0026503040020705810040000d42c2225982c0c0c5130b84682e8100b0b0380300d9a400c0b00703110240a03800700c0b040001100145002652100003801401e50040d101521032002d030503c0e102914074100d8030428020000042d805601d1412200c20f040c801090320b40f40c1d446003a80c0e5100c4210340c500401400300e40c018141d07805500010459000f6614004074540c44030a0148405003060740d801400ca80e540090b80c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 572480908 1250 572479658 572479669
    0x1a070804051221180909010f1a0102070906120807061103012606070206150a261501031e02030c0411030603070501030207080d2007060213090b1f0509030a1211150402 73
    0x1404007007180041000c0e0230b01800710b801c0300c100d90441d005294180300c3d0360040e564100b004030003801d512503080020500b4010305052000d0f00520050004000050301010031040f5001100b802d2607501c0354645950b19403121400e41c2c00c2d0203100498400d0001510a44000c002076154041c810940240c107046e25090314540c0d42904443d5940d821240c084400501e11042081684a001106036603186031800d0000950525148641c41c40062040000501c0818007851300700d59043c500b100b50740204030051000c2818540010501a4090328009400c404200e444004600c140002c07010f071000640c40e04019400c038040c0000c0130384201002d100b0307a454441c150b803107103500d4110356410f021811211905005558031126007100c00540100326042c0301080580310101401c1e00340b0050040c0305003030703021840c0001003076010300030308005402c0060350307501640c00c41d4800d04003c0c00796400c000d154209400101c015a0b40003000440050001c0484000820f0107032034104409012141516107408000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 572482014 1106 572480908 572480911
    0x311092808120901050a12020c0f1011070209150d03170f0606070b070908010903020c1c0209010b07060b060304060e060906011a0708040512211809 65
    0x1100100c40700980d02030f10001c1c686070b6140c040780c010407500c2644a2020301c100c1440002c620103042da02103540d45402e4914011181c0c60100790b001942103515128040c5000001840840014905424040c0e00046036a0105180c00d6002c0700140d8400b84c07068040703000c100c26485808003c602e0440240d803000811384241401e1a008002c501a4400c443d0000c041146000000e0403c9009090160240c000c0c480200114a4286000380d80c0e220004025403052003600c0641000906450008000c04c0d40074058841591800194041d40e4100000c11600c56071500d2044410381c98038001b451007107015280c0842c564040c26943c0d410f081c4054000049600071074014010006c881d0b042117403907140c4488407035480300709092a04c032902642c1c000551100c000d825180912600059030082c0080040030f0200d104a0740d16005090f200d506942201d80031805e07600d0409260442e06d65 = true := by decide +kernel

theorem cover : BRFrame.Cov 572302158 572482014 := by
  have h0 := BRFrame.cov_init 572302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 572302158 ≤ n) (h2 : n < 572482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
