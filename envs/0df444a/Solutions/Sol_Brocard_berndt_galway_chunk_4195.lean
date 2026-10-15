-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4195
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:50:46.726752+00:00
-- url     : https://prove2.me/submissions/9460d89c-db76-480a-a4e3-b12164d4b15b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 754316546 ≤ n < 754496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 754317796 1250 754316546 754316551
    0x2a120c23011d01051603080a0b030105061c02010c1e030e0a0503030f0c01020904020712260105040e1507090e010b070b060127060e010e03070e16201e070302010c0b 72
    0x40000411403000240a40c0c14140c004500c00d4440007c00d040c4444217405031080c05003e14044d83c0740a040200954548050000200440c07180d2568902e8500040321211190540030344810041d4503c1803021a42608601c01e02e40242d454190303144007035081000039020b03407180b241d140d48203100340c1040542d07480042480ca40258001441d0804860105040ea00b0000302a10640707500e0318001e001c41d411425007d8042da00b0502c604c80e0051410111503030f200c0c1806058091542c03102c07407030700b091400c000c90700c02102c0c200000078503440c1c900d1005102c9005401505040a0365100004128500d8815500010b80c0041c40c1d504d503a40b00c3d00111503035900350030000564a0041e0a603c40c6c210340b012000060b0100750f8600b1070110096001420800b8800b440390f011350f102c10310820401a00d40c144076080071100700c25000d00c030341003201268401d194010810416204800300004180c00190022840b114250754580246600d868551608024032020380820150201c0d0400100c2c0c01c0b0ba45a0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 754319046 1250 754317796 754317799
    0x1e040f020415030902010f0306181109090c04060e030a150e0a0f050601050108071106070e04150f140a0605030609100e04150f092a120c23011d 63
    0x5040554480c0140c1200780e0b81075900020a54404000003996440120400044070505091007140e00d0b0440c0080c1410100c500d0f0394015541e100d10f000031a10360001c03642202c00003800e45a150074001c4d4421000d034050f1051401003400b2660911441c01c01296003020141c008881010305031306984080d0190000c1e40141c1d01900075601001d0020b04412002003865004000030b01d0550b04080016040300d03009466801409030600404510003400603c49034005582e1602402040a20004c100039210f05544420000c15a5001180c1c1c1c1d0f004501c250101d54120001d507042c07a9a01081c03041c4a800c0d4042e81d0b0002d141000022040d080c8003c03020340040014649042c075903518006181500700554048904640151032208490785c1ba01410782031041c510001c01c85d441c801d41d1010098040b98020101c0c0d9106654803104020140d04078800400c058440040c8890f040c1c5044060b8155500800701030042040c444141526005003000403000180c480c1200b82d28003000c5418004403424203503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 754320296 1250 754319046 754319051
    0x70b040c030c03030f080606030c070f0213060801020c010507030b06030109053d08010608190f0204020304300e281502070b250f061103060f1e040f 65
    0x1000460a808002c015400ba640d0070b0004510481c1c000c04602025020758850308042c4240304c071504509003224078183d800307058030115000600c046041c484074001504401e44c60004002040903064000f0030801220100030800d40d80c680e101501201c084020154000a0030700045c8900c0869520241d048010580c0c006c1010084139402c02c50343e0102c1130160481000d0307146400c0c0b010030a5440300c024000c01d0000340442828141e80d16510300001135400042d011201d405018001e201c82c034010320352b80280080d5035130314203401c164034040010302069102c3c03442d181900d5406880070301080c1001e03600b544c0703004c000008ca80030448843c0c4030b410b026600312000031313420000042081140c4010445000b0412500c2034800c0c019041034a41d40c400c1c01680c000300030403c21010380d503c01c1c40711050300403200c0414a1b01c50411540024000070018055881c2c9504a07010010700f00c042d510401c411100d1003075400181080c000c800115500c40600c0c800c541c0306103401c030314081e048030070000c0361541c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 754321546 1250 754320296 754320299
    0x603150203100315060e0c21160f0c08040f0515030f13050f16140a0b0d1508060c030109060b070b0c0d0b0a0b0a02070f060c120c3c0503070b040c 64
    0x8503080b100d040c0e9a02960180009803141c00c0d40b05244607001d5420300c48c0300703200e0a203814001900c08101c0d00710403404010140b450100014000c0c10303000d0219800c00015a02c0d144c450001c40408801d0380140d900c03540d51440040c00700c83c40302c42200e1103180d6000c040303070094681c1d42c28030100d0801098201c0d050b01444001c074540d00c004204020b074468142425490803480d00d804043c003001c4038580c19010710009a414012000340d00c084031201803a02c000000c0942c16003850b00030541407500302644a018880911180c0781040000e14180c5139100010803c1076981c1540d01590b200e84000200022030100010703074003280f941c02a181c4200e02407004a50702c09040001200d411194000e48c2c148000801c00c145c0031a070401500707000d4001050007541c3c040c208032014117a026100c500810102a80a520750039610420001d00c14a03400502811415050340345c0040c0c031704810000700c03221166408141c2c1907032a55800306920a4108001d10b1a12a80da20364607140400100700350b580e00c00e601e00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 754322796 1250 754321546 754321559
    0x15050906070507320109030e040b011e14030a0b030d2a0813120b0a09200310021204060c020712020111011103071e0212270405070201060315020310031506 68
    0x194400700780854000241b040d402d440c2c0980704440c20358000c3c0c000c0c0d02d807800415090360861401c0b0400c0800300c5800c01c074542950021150104210642d80d010031000c800d000d0390356016045403103260300803000c0d501c0804007a41c0c02c0725508c61600d50741c8070003c449150090010710210541c60a030380241015483c040181042c00412480c40d413001d2000308420466005010405002c40d41004044109011000c126103500f0460400c154440e22044102210380c1c0d00396408104230402844c04050039519010b60907841c034240902141e055803041e0401035a400414808549901038504214007004466444d400441c1ca0030600614190699078400350140c00c4008680510300c034074801e41c0c6a4a10440803416101c119001480c3d00c015503001e5410000440c4000c4140c4038000b000c080d442016207a07003008640e0b05c19400046a82003440d28013131100e03a603419006241034900805181403216210a4503034202d1008680d0254292160502400051015032403656040310300e00010030308546804 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 754324046 1250 754322796 754322873
    0x20a031508070e0a0207111005090915130c0f180b03040b01030c1409011505120c1b120711180106031e02030402181e010315050906070507 61
    0x308409000d40c0310b01801c11041040d03200d9190f00202452082d0305120f07084d56510607002c810b50f04103200306071040f20041821320030005e03100311b14801009040c0d1424034040c09042d5050811100c1d0048000d403d220784c2c980d4a9010b0860700100c0e5540d05c1502d03145030b0b4412589594041c000d24150070070381e000001c1000c0e074140914003a5006114008040d4511301d00a00c0f52100c590180c0702c0d01104420001d002c1c1d071135100240c111401e030303d0f018582c4411405d046440748604207044101000010500c541c00e810f0102505800c10704051040800805d201026a80c0505503009105004c0400800000030a00710380d151010070050120f2601c401035840c004d03070700c000076017007640040d07503448034100107444100c002d2240c3c5990050462440c00c15070041010b20b045003425400c0d103289400032615a43c551404e009840901014080540d40c49240c03000004407400d000601d87e03030a08000c1510301c0800700e0060b021f50350302c0d141c03d8038102d0780340d450b00407000060f28001c4462a0f03d4460030203104511 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 754325296 1250 754324046 754324049
    0xf04050c2101092114030c0d06080f010f0c030e06010314010603051b030c011b0209060f061819051305040809130906050108070f0317090d080d05010b0702010909020a0315 75
    0x1942d07103c5800f0314030454941c4c0300c209201d811080102100320401d200e19404e0403207401918020f15580c0d41d1050a020350301070011039020800b54410968501b224000c1903001061140004800380000b02c9540001c4058690141081106412200041001403c00080d00c9000d8a142c400800c01c907961f40c4410b400d10307445d00e40005000c1c80800c2e40316a42e25040c80082c41000c1c003424203540c950180c078001c911440100400a000741602c2d000305034507569200d080c444800c40242655507031010000313040d4142035941d18030303070045038829442d0b20000e2100c01c440e4207441029048070910f105000020000c1c042c040c0003a1524281088851090b48480c2d820303c01c0c04144007004203407050315203031180c111503051b13010301c2c00ca402908007840f00b4a0701345000340880f5081f50070301c052481c1c00c00c10b003106c1d4410652982d41c8840210b24100800c003541c4046c081c600f80d4030350100b0a5070303078070a6400031600c03580a0080c0000c031109006d101d000001d0340901004030a900c4d0000e61107040d04000400f15105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 754326546 1250 754325296 754325303
    0x2003150d0b010617041e0f080d0b1206060d08030c090d0305070203100e0c10030216110a0608040809040e1608100c05090f060a02030f12010603050f04050c210109 71
    0x41d40040c0203054000c1c4465a10018200d500d00081c645500c49240c0d50039841a15821282e1806409091040e15402d008030705401000d42940c41665241c80c0005102014a107130041c1c0d80c0c085008410540458100c0c4101d80142809104080a584048180e40024954002640d0610800000382c584070b11a0080a100b901e440f580c03a04680101031500c00801e40110840d400c0007010312140e180880e05001040c0161880c208423101d48809070045d024071480a04a614032585038005e02400b800701d1003804100ba61a030200c0f0b911b07100102d48803034080701c01401e601c1c1c003005000110305050380940741464110056914020b500c4402c40e00360100b0b58803c031802d52200c6004d00b0010540d10541d0705d0b020b481d0818602c0c26150102041214041c140414131480b00420841343e120300074070413036201e0406c3c0c1300703034996030807075211200ba0801e000c5c041d101c0004d15003c0000c030b0400600955a0080b60401e000304841081e4504100204a250900404074420f1b02265402203100b402401c010520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 754327796 1250 754326546 754326563
    0x114040b090418110111070b12010504060f06021b061911060702150c0d02120a0603050607030605060304110a080111040e06031504031218031e032003150d 68
    0x881004210581c0c0038400740104000c215003c550001d8002c0c111980b41e10401e08141058160030380f442c90512003d94049451300800140d10007a1f2032086003114141c1d80100d8007008505e442d200c0c50301c10800c0b01d0184c0360143c0d02a001254448200940a5003050401080c5528024030100070345d0001c40a04c3c0d0b600301207405019411010340c41800f050394010041d200501051307818009140c51401e002d000021841c0002405090038200d580484030000d110302040351160403c0c504080040c5001c0c070040e202030066a0200e003115120780110b030110b0b00300810b540d0441e1599182d00100c03459844c204e80d03004054800008403e8000e000c0d00914000301c000190f100e51405500f81c4039550f005000c68481c0d04000c2014444031801c1c14030640141d050702d48030305485043c0c140540200102041d09a0f00240c3c842900105036100c2d111890240c0f510f00041c0900303400c007030280c0c190b5101c08900c200c40381074000c1ca040030540b140c002d1680600c40001e081e00d00340b42c82c0c022030386000c80181d0640f103603c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 754329046 1250 754327796 754327807
    0x30a12021813140a0203101a0d110a080a060b040320030138011407031407061b140d0b0f0d08040806010803030c040312021c0201151202030703110114040b 68
    0x826006103d0784030444a02c01d51441c94600400940c103100da0103051300c0c0c890010b02d04010b03090100260b40d420705002d00c00300203c0c1501d0410302d03503a410000345cbd440050a01c00016505658900a42046a140780021800e007410342ea0341c00c1d00072035400c0c0c02c15043d41041d140c1c500c03180d50900032650010300d04600800d000000e45c614520b030040202c444a83c10500b0b01d000d03d0301c0d90380024085c403102424800d19444918a1800f1145140d101c804100d4203038000c02e40201348501c40d4020b004003210001c800d840d404604105807403403c440316000125070000c1c0400e5031f10202603040490514130003001315540c01c3c0c0310400100d004256030400d0320314020200d8144006617040085a01603c0c0340002181140703484135250f409072096000c01031821f280301031080e054500030800a99050380c010240404031a103504028000c2c000c0c8070200c503035003c1d100c4000841140c25546010301c50b40240c0604091411621000b0b101a2112030440c10018400603018050601c1e102810103045002c82c80d0350b981 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 754330296 1250 754329046 754329071
    0x5010507060e010c11010b09041a042402120708040b1906080304090209030606010518040b3001110403051e070302060a050a140301080a06050910060e060a08030a12021813 75
    0x4400c0005d03c00e000e144d184082c480819200b004078141102cac042d0211030265140e01d405c0284881d540007014070110b000102c0407248000d40c0240c104c410482d0441c4a840d950603000321507143c800d440c06440048034070b0101c1c00010103540380e041082540c0d4400b06680d5607510440c0d00e1903000e5800001d4039503010800490f00e28007070200b682c10003424a001801c101400481038511421944c4280c0305568425000041d9100c00b1911450003640c03052204500c6420f034032441040854500b05030780d42d482c00c40003500c51030480c42030b5001da9811000605400c0c0b03804003844c000281c03d0f144260144100d40300000140d40e60320013001c0c1643c0c07695659480321402c0d1405026a49a048180f0101000388010b200c0017100040b000d60154003c13002050315150160010300700b841d00c581c0484540c2c140000401c1c0c003140c0308000760180c0f100303a424454403951001c98544034024440c1d0400020b204c00004207000002c0d030003401200d4804154110311104040c00a0440c03000001004226078a80715500e030714 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 754331546 1250 754330296 754330301
    0x30b120604020a0803040602060a0209010e0d140c060307050706020c010603051212070816081302040e0a030818070e0916060918060806190905070603021c060f05010507060e010c1101 80
    0x13005130200031814203080034030103920b6001c0144080c403042d60207d040e003802c0e07100d450b504140f40000b9007824003006090401201c203103da040519142d1003440216001d80c10420b003140e108591a560307083c01c01840d961114040e52018842c04076079901c5500210200d0000e0040380c614501d030605055692190641060220078010700b960148442d0310201b2440c040b04540c0910700795540c1c13400e002e660740d83c6014810031100301d445c00ba4002d440c100d02040303c03080008445000c6c902179254806140d40f00040f264100c0009580301200781c0000c0010000040c0c10304c61190020314510642d58080c15000f2404507401c81940f00000040c03014a01b000b04280b40406140c6514000809100650401c00510399880b005842512102101440604181000d51040e800c496201d02070b112130700e566140c001d01940020409110901145401c244400b08902c5080211254241031940e95031401d03005440e25000300d5010340c0c200d41c0310000c1800400080c41840000c0f000b80c0c564201e01d1800c24010707400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 754332796 1250 754331546 754331549
    0xf11090a090b030c0d06020c0f10060f180c02070e070804020a080606150f070204180c0e1b0a03020f0a021c05120a0b041b03091b050619030b120604020a 67
    0x100c2e180407008482e94a0100d4040940501914020860b800a282140c003d11401400482c2c500498030041c0d8240008110030400043d00101170000a0b1920100a501d109902c144000701c440041d104032a001690000f2601c0351082c01960340d803da0300d00085488041c01c44414000401c1542040110300d400c000c080042d05114006106624084005c11001c0c1d00c00159a41884004210722aa03412124102c48046030b001c2c2c0140b110310080141e01c0b612151541d411a42e6082c20030f40441c5401142c25654402e44122901d10f040b41c0340c0303504030b0350305900150224041503020011981a880c9680007008100990342c014010700c01c03c10300c40c15000d00038032503500801c00b04020300542c0480c0c0781491504070341e0ba41c1d000a1440d180c04000f0300204441a034440400304202e560144064142d80103040150080324030040c00344194442d0f0f801441c8a0040540c021001e00580301c4000020f143d5041c140c1490900203070b0881c0040000302c0307100646100d81440d5010104120071070070640072010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 754334046 1250 754332796 754332809
    0x150c02031507020309010e150f040f0e090703060e070504020414012a230a03020f0601080309010c0803040201030e07171b010f050313080a05030403171b0d0f11090a 72
    0x10202d0030b001500030b407644144140c4504001d9174580c03604d942d40d2a01003c11318490303c07050650703850000b50000c40720340c0c026100d11411030941c030400060784008002d90b5032040031148040d1500b50301f990781c0c40c1c000b00b086001c503040d10701c43d10401240c180c030303244002e00140402c152b82540008001c4001012640540000004502c140d4802c8003600c4940c0f8003000ba095005406907000000e040c0381117001403507140a07050720310683c0000d8040c540c000c1100d0b0039519404c02541c40503038039041c2080d903a00c510400540081d8040034481d0100e01c030b80c1d02454000c0d20515021900c0c11050300000c4ca004100c0d042080504400405c1111460b4108181d646c1207a6001c02c446188120034000b030200c807072040042081c0480003000400350359083c1d40c2a148503910902d42c0e900d44400d0b480041482e00201c40890207e41201c03002c00e234030a03050f44c169110300310814610244640145407404c0039000b0485400140352500c1c51580f501c049401940c1071880000080e6031644203000421804800c07907800507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 754335296 1250 754334046 754334083
    0xc1709070b090607060b03060a05061c02010c0308090a060c1805040b060d0e190c061103031015051e03071b201315030204060911090f0a150c0203 64
    0x10440030030900c1c01e40d52440c1c0101c80d120340f2542c080c1005405407902c1210141c0c036015610401103003502561201d030240d281070760041d600001d9080d13500d1501d0504400a0701040b0888680e80000780b05841d082d07480703080b58050750601d0002d40c0e25031054071100180400860341c81035074950750418140200000380801c40b170502c2168910783c00b24095208a0a864908503120949016804030801074074040868107482c1c10303d2403400f401c024800c0c10302c0e03008501c00114034403c4015103480010660340288550130554030325502c1c009042074411106080201800418044c1d60b0100c0d012240b800701e509564400b8590324900740c1001040c06591311180007281f0366141101011035840d060f2580007100207600d40c03030482c91404c0010713020303130300500a8091b20f4282590007080c07090306010401101d20940b814071840d62648110302c00e9846005403100320b564140400001803078188616042240007400100c2d60307540f90001e607401010201c100b00c0206051f0001c140842c2020028049000c560f070900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 754336546 1250 754335296 754335299
    0x1b140d03032a0f09140d0507030b1302040501060c0210030903020c12160503010e0d0f120c0e130b031513050d0906021203011a03150901150320040e07020c040c170907 73
    0x1100481e1700305101841c0600c0705815101c0c1040010090200a10781082d841d02203480c1201c004047c0000005080340642c1c10b0500000b00300303000341c0420b00410342c02030403409006115074049004000810060381180714010007501e090f1140768000141a900340041d118000310360008440226140d8442c0e4000c0c0e00d0011f103108100b41c0407603920311400b494a031603000c81022000131940c4408144540340c1d0740e0b19001581510b945c001d45200354142d016100340310840400ca07548405c9844220440781c040c1c00c00d60419541c5240c0309000f6510031218601c45450190684070070349024412700901c4089030040000744119601000302040124a080c08145903604016071002c1998509000410810340880495507803120300fa0721819614002c0c10486182d030f540c2039403441090011407501c0c0800d2800c1000c603c482f600c0f2190300404481e68040750320f85403424901864054008288204501504000240f01e40e200d0040c14003809181c1c1c0c80c12102e04414800d11618100030f800f10280d1f5000880 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 754337796 1250 754336546 754336559
    0x1503020105070b07090b04060815010c02030325050a0c2904050405040807171e030907050d1a0c09090a0e0c0402090d0b01121b140d03032a0f09 63
    0x803540000e0380842440c071141c13202c41094480340e02c25044681d00d003c01280100c0c1660b4090034071032040c2c1c00102000d1031071038034030010340300550a518041c3d01038000300b04140c083d1100111131a90200e20320060102c00e2480d440d800d041c410380e148101c6040903000e80030070010020036040e49150308421201e613562800000c885203503100d0761103602d00a40d02d540000d400d0000e4001a00c41854104614000900b42e41c00b28102c20317441420b54528000182c08682c0c41360b031402e0207072031050021030700401015050808001d0f101c0d01d540e400b02c45110070707200850094184074402034010204c0544c0661905c2c041c00070408814001400c0407a550300e003210828032080001f50380007070680f0503030b001a0354200b13070ba000c90b100b6445414040c05001960000060380b0003801460a031030f6010b554a55800361140c0b150b00c46080075442540121540341c18030b2420307031a1200010400a129040010f80038a1b0b0780081c032400c1540c00c00703071780c0303403c0080304c2c040a070a8100180e10301030300e9145881014a4200403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 754339046 1250 754337796 754337807
    0xe0303031303030b220605040501080c0a050409061b050d0b0904050607080711030c060a18020603280606021006170d080c13170d02060c030f060a0512010b0415030201 73
    0x46010b020140c44401450780c03911680102d08a07030700c60640d407031564619001d2607000750055105032805585080000200050003050001100700000c1203801d00b1450002000f01800c62002d0136550a0380e0760b5001c0c019080c61405c040c182e08550f45a1780d440d41000c00a6904460f001e0004a004107450701c1000002072000c0717910303a03000c0d038982001e0039152101e58ac01c84a40d90f00c4405039002d40300001d54032100041c00503103503219400e050002e0041c10064030140303480c648951030081d080f20782440031450a039021005201c482c610307a04c000c206d01d0340316405001039841c10340c000005600500d20011120000e4050750000c0c02c480c051010105241140f042d645000300c40c3d104c401c10000c0c0011800354003a0a040302d8080d210f020071140c816496101c0c00d41c0f42003150310000320611442070491140342c004034515216054040d0310038110340e1001080f00402400905065005082c00004a000c0c7d0b41c40038031094000e501ea000240c40300300401803200321020b02c2000d0241445000c0d007040140c1e03000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 754340296 1250 754339046 754339081
    0x180103030311042111030d170c070503031b090904060f0e0a08030c090607050d02071508060a090905012d061a03070c0309030b010329070f080c0405180105010e030303 73
    0x3118000441130a05003014111200c40500d90302d40101d149241c5d07199404804402c050344801c5101c0c02503160b05001c207030244a0680b00078400d41013030000507180919035111100d0300310680c54551415045000007000d0f460104d90441e0144e649145500300c1d561144609000c460400d4000c044c0310081da140d50300c0c036020050040594000000d01d000d071603107a010994000d140e020044602c84a240c0780040d40b41c20f9240912680c0743c1003690500251441642c4d250702032240a0003a01c501405d0030300d100050411610b040c0c0d6030b0b40d2289034840c549005a240207903403004420552001383c00c402410300c26200207601103135128840303180c500307046d8060000700ca412010f0750a0500ca61020b502e020b0381d00c80504e034000f414458000d80000280311011103609441c1c01491504440c00c0c1c1110b42800450b581170310503000040d106010f01211902511150f5040b030808094a800c00b9541c1001604400b0014903d030382c1d5a1240c40100400c4d41c1107d0002c0401000b1005141145000200c40e65103020b003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 754341546 1250 754340296 754340339
    0xf0b01020c2d0603010f03030f021b010e060403150501030312060509131e140c010c080a030504140102130503120f031906120501050610020607092318010303031104 72
    0x411a10030b112181c0d1801091103407000340c070480e141d603501e101c0c06104070303110b00c0245c0201c0d01030401e4068462010851018950b8085103103818818541e004444410080001c9a0010b00070807012000c83c4240032420140202d11001044960446c900205481410001e90401030f00742401844196642e01c01c00354080040302c0751500701907007800e02240e510040d068108420110410641c1441656202c07a28241e030075808491001818800440341604085409881d0047c18000342101910a8103e07a41060044010029030a8290707805401c81e446100340d00e2158948071000c0045043c2880303003441c10f03613610a100f8100f4552440481c0d42c0c0c071004042440b400d610740e03d024441900c1d940a000030301400b40041804040f1841d1460084c2019101a44246064215284820f2000520600c12141980c5001d002443c1c400441850b82d1501007440c0491301c441030071181e580300d90103e00300240c100410f940301949182006001c983e000306084c0d04080741040b040c4110143c0c41c0f12603800d07050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 754342796 1250 754341546 754341589
    0x9070603050a150f03060b060a05070308041103071706010b2a101802120d120b1507080738040510090506062d09070c0c03060f0b01020c 60
    0x1140c104034802858440b03030b516203c124641000c00d41085107080b050030740344100000c00c0020036990410100d0b0182d88180d1000030010801c0740c0000703110381e420507082071042051a28801040001a09001d1242c202c46a011201410008181c20400400303006005580c07002d0720380440800e400703d020440ba00c09491041c118101007424200c10807a10b480c85100c904100400c1d11011640401c680f1b1983c01a40b10703640300300180412142c04900c40c00724480700d480b40441c1c100c5102607034015000100300c0a501a0600010680c0c58a4550040400c503224142003940d482552078800c02866445246044505501103180ca1041075507110445090043e020400f440c8e8071460444c1c6810120034440d407c4078106601d1808010000031030783d0043e039040380c009000044081c15207500c100c000120312800300218031034108504144a55a4000e166880d010041d031826454138842441254011911595201c0040902c2141ca22413100c01d010248083e1090103105000100700d04070308c20100e486e83c2c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 754344046 1250 754342796 754342801
    0xe0604210c0902091801242307150e0721050f030307030e0a0b0402041508160e090a020f1c0b0f1b210601020705030109030518060f160501020f0301091506080907060305 74
    0x500400749440711503800d13401040b100c11234100350310042c0c210078000c0742e103811200102c007600023003401442c0c21070201c071004003809407520151002100d01f11415041c1d52040030100d50204d4414000d009091b18203000459481c1090300000707080741c054800e1605c26400080310100000c080f500280e400940455000c03a032601e640001104204089c1c1c0010700600c03440000500c200c07000145442200c064034036084569031015826516440340c10002503011308142d000b140c8620300030117420844020071f81d15100c480c844e9035810a20042c00c0c1d44490038000f906081100300b2a080c00e46039040c1440459281c100803c004d8000032003120300c641e030500700284800081099200302f01c0b1100914004000340000c60300f82c01c001c0c0c032075446242012088058201d8030190741c10448200e4200d5101c8416051801c02005207401482221070021619950200101200051454041c60113401c80c0304000503041c250fa415024001c180754400c005005036401082001c1c040410a042180c0c003c1c100401c1a6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 754345296 1250 754344046 754344119
    0x2130b070510020702061b06040317010605041e050402031e070e180601020114070903150501050a051e1e040c0c1e0c05060d020306100e0604210c0902091801 69
    0x140900410481094000e0110860382000000c050b40501d000362941c4665004140d2400101d42b400d014900108034100001c10c02422443c0d0420079a2105ca2951801c25480d0300000342a40e006555240e145207011003140100104558416000394a5003040c0d0740380c0c110200420342040c0000d006031401d20110000406690007034111740102600c8075500340c8035140241c3d000e4500080d40c0015108a83c000005100c0c8115078410b241c142e9a0040070384200780e01d008104000c12002c40304401c0411040e07040d04026480f40b44000d00c03920008210002d200c1a5441030204480c0b03039090000c01c00c45000c1c28880411156403890f01081c0d400540d0017500001410450180601c540c400340e0800c40004201d01c030101282d010318098041102d0032080e0040041d4225482c01380d2402d8264030010400040010528007040d8080502002902d42801d04468441002001c40c5a200c4060250001451111b034508801050300100301d100ca016059410840c0305d428003200e516103081c02d142c40e41c540c4a0b0701d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 754346546 1250 754345296 754345309
    0x3012c0f09010b0a0303020f013207181805061e040506040204030b0f06030c0109080d080a1113050301060b070c0e22030207031506150311160602130b070510020702 72
    0x110f40300900240e00c040d6591030002d60300c1407045042a019443d000c0a48a401c0b5a01d2081100b42895004986c08030605501d0a05010010300b40c4000e010403000311410102098140400070103c020116213101b800044400c1900c90007001540f2a49440c40201c2d50900388070070f41138214005580000e595982d80020800900c542c0e000030382004510810483c54440841c1c0c03d9108420a40c00e483c0101d154100644401c100c9004602180e0055202030309000d11419803590b0044440d40c1c0420b09110001e4040d401342d0012075102c5050307080c03034014441820240503481c000c0020034019803515031591100d06100c80309010360510584003c0100d16107190f0074030a042c040b44264050110034015240c0656101740d144012124201240768a0300b201110784500350407100301c003044031412940010228000c02c050034081c401b0303c070140b0000100c48260400105840d104074070050b0b81c2d0850903d05809622503502120740381c1400c0101900090012881603060100322401589640c0c00d840022034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 754347796 1250 754346546 754346561
    0x30c080919020f060d050405010608010506010c0b10171c02120f07052d010c0201050402010503181f02040f05100e06071703190c0f082d070503012c0f0901 68
    0x20301090200d4450170400065105038019072084d0000c02a2903a210f12503400c0e103908941075800300d6084846400411030b0003022541c42888841c04007000381e200d5124003d1089103414108007030303008080c0c02c03602c000d030401e11001c0c00440340010241c0444420840c0c0a9115041d142102c1d5400460103001304102000080c11019004d1840c0d03c3c003c078000d00b071080064000440160660a05054881503801031142030300954040e518186940d40d6603801e45400d840c01c5a1040d030b50300c15810b28016032903060740c0c2024080c00e81a809680c852401500003149619500910300c10741070000c0c1c1c1020540c20403407603081160203444c110b03107900041c02c009580002030070051441101c000108484c903003403e00460740b0840c00c40410450105103040864a0885205000001c10044030210b6015581c40110200801d011000002000410b9810601600d815642d85001c580080014030503030103a0250392030a44011004182507003035a44d94101a0500640a000d180e4151130120700030302c034290030a11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 754349046 1250 754347796 754347799
    0x130c0219050102070b010e07050f092e1403010503251503150914070302030606071b210309090b0d06140a0b220e010605030a03080106030c080919020f 66
    0x41940c11508006000c0e5210900c126000c080c01d80007c18000042c61203240151019a203070b508080c200720311101d081d80024074080e071142c202500f0402101c25103000c585100c1c0050300c8000307085d20904015050280031514400060800d00051210342c4001a0100c2450240c030030700348508124010007402814283c00c8141800301490300341c04000e4041d00105100b0404c910400c440e01c2e600d0800e0300407101c042c1171030b00c0403c5111000c1141c162190700510f4000c000281640d250034100e585500d04506660080c0e10311034080f030410000342140d1480900d001c11000c100600501c0d2503034000b081c0354020700514814590310000001c81e515501440101c40340e00c00c0c01004051403645510217500c1045138000301440c20920a80000c1c01d280b03036614160707101c105818901d001d03814885000b5205100c0307201e010f99607039031000403071303541c02c00c1040354143c02500c48a1507941022001015120306001600c24441840f080c01001c20001801010021b2640f0065180321054400079441c80a02c1c50710b075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 754350296 1250 754349046 754349083
    0xc0904030e060a03020304031d0d1401020d06080109020a1703030f0c1306030e0c241b010903091d01050d021314100603061707030201050d0906060929130c02 69
    0x540220f5055801140918001d44270030050040311a001c4840c0300310045445c4e04032004006410000c1d9103804400c03d403004401c0054100500780030050211689030703200d806140c0d10381008405500302445090040c15003004e0003a040c3c1c868410b21a03aa100c0608400f001f00304d107800003400a40710606607100c0081d000024100c031a81c4000043c080d1902d005000d460f40079100c0d4030413107031034084858903001b0003e0602100140b156500308445410079580400c1210301c01e100fa2101034000c0c825401c0c013a220381c951241090420243d008000b03042444000c40c1c180d0f81d001440f91b030f6a02200b01030755650441d03100028010441100c5c1c05403044040c07003900002c0314030901000c419007800030021b403485a5002c2245650380c1c900c1080f94000c0007080b84183c2c012aa00b440907500c914020000c00f842164081108000340c0da0301030485025900c00d402e400d5403a074240e501010900c001c04017000501100556191446000800b1412040000501140e40342c41240540d8020b1049010140241c80711 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 754351546 1250 754350296 754350307
    0x109050604060507110f06012709060504030909050c030103110112060609050f030a0c05090405121314030307150f0e0105040b010e10080601150302070213150503030c0c0904030e06 79
    0x1000f41c0010381e03410b004104002e0903d8410b22000880d8418001079100a160303507440c248280c05000b00c4e4541c0400c0a403000070246d021f80d240c0f406980b0403075101e103a002940349818100107011040380d411088041d0309003414000030004510541c1c1c103680d04108118280484000180c0b09030b901d030b00c0190002410424000707100d035041003200040395019280c002e4800c0b03100702010380b1441300c400c0042400503880c0003481b407801c01d009665030051046046900a0018030b24000e00c41c3c0007012900781c0d080e0713140c074107201140e4a5140c0c0f45005000350700460401d061035541d62040140c00f01d0b141c81281e038980c0c90b2131084e02103400514a080c036110080000f13051901703150b00801024000c0442108054020548200c8450810401c407112280609856405c18001802d03400f98103d50008054081c00703d00003603940c0c0600000b0100f801c080000b0104000302c0707030400c00e80c030650000e4441e07003090000043e0310201140991032084111010403481c2e5642c03034252120250144104e8120320045003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 754352796 1250 754351546 754351553
    0x6040506070f0e012624030a030c140c060d0c0e0d050c01032a030209030c03070503060c031308030c1b0f0703060e10020c030a09050418020d030e060d020d05150604030b090109050604 80
    0x30310440351200301d25054006e02c0f01d2003416981d05410400400041c0d40030045408140d0351a01000c0c4807000c00c055032005805c810000d4129088004502400b503910713258003484a812003001c0721840b50544812501400507202c4d20f803240300701001d10381816140c4183e500c402d010020205402584041820a0101036040c0100250010b85047d0300034070428041020618001601c4022035070010000c2105959044400b50150009414811810440000440080c54610146101e010f5071095a03403960481c3e10061044000c61002c940c0f00e070041950005120004100903065940010001c21080c45900009117003602c08200200000e101103140c0c1c5540c84080000d0914442a0303444c041000d46070b104100444222008010895182c034100e00300504290310400001c901900705500d40b08028800304140790b21203521048101d03400191940300f8240d521642e504a008041869000c6e80f00b0300c04076003030f4484d03404040c158826040014249a2094000c0158564010240c4046091a14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 754354046 1250 754352796 754352821
    0x6020d0210020403081606091a16030515060a09091803200a0f0501140708011a030f060f1c03030b102f1e06040506070f0e0126 56
    0x100220018010341058000104207402a1070550340c0100443d4030b4429540404401600740085c1103c0c020f0b111544103012803141c0728143d4141103140c0b4012101d01e0000d050307803c1807003010b81100c00c2c14070300814040000381e001c000c3c1034001e03410398055a4800c054002902c04160b5540900c50f864200048840407480d1181032052451003500e415085d10400150308000700c0114944c6040d6a0082240001103070081c0b040000c441c1c091800025803c800c5031121500d45c03400c958550100e0f09039030040000100c101400c1c1c0c03a07030003192401425400c103503000a105060182c4410b1240070391020400c0160323035a19901c003481181d440c02c0c40084480b860040c01030140704a005118914560030b14088500030701d0240c000c1c240b050f42915500c010021001510304206014040f18401c007016070240c0e03039129a07000300c64108040207140500c0c2c140f81007890301130002e1880d01041024290f4088031034204c802061441e00c2424400d03101010900c50141641001035040080e0364618240700703c600544 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 754355296 1250 754354046 754354063
    0x109050624090907090b0a0f050408010510060f0f090308071b08010c030b120a06091e0506060406050114030a050903120112060f021c02070f0503030c0d0522030f14040602 75
    0x142c8080301e035640d58070003e44080b074940c450006c910504024064207d80704103044501c60341181480e60038562280c603a113085030b00491b4606040c503014071081c406035800003000000f108082c500514400e02464008184000d03510000b00300c3c80d0007040c0f190400a0381e0003400b11b01c0034907601010209990700045406000d6910501c0c010924120b18080241411040161900982002024810341c16501c2070014194200c0503150ba6500c15183c40c485c2d4a50202c41d240580030b42c00806450030b140c000c10003119500da1110307040c40b559015420041c0040030a899005022810004555841540950071071090503120300500303040c0720012a000100c5000c01c076450b805144108058001d08a10340100c2c420f0040400d101c00c45050407c644040c070360002d14520348249070070508007002d9a104c9142d44c0040c0d0b940c8510180204650600c02e0f294401c443c0d10011001c0001d601002000d034140b5031886030100942001100d600501d039160041c00c0c0e1140740181c2c0038185545071b9403088002c0d11420103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 754356546 1250 754355296 754355299
    0x2010e040204050a050609060f210c0415080414010f14013f0507182313020f1041031302370302030c040506150301120b1608010905062409 61
    0x440122f40c0303d0030650107840c2555070528820100710b52505082c0d41040c4001d0003120f1848d04501c00341540c20080c0540c02d544a000603002c40d00351202034410159440580202810b810846220004104861141d074006c07054804502e400a40781c52640d221100750203c0a000c0341300318280050758000c0a0700702c05008080603000c010b504421066858040c040c40e581c4a490781441e404200c002c0c014811601c0c0c110720080c0210b0035030034500003007850241030104990106d4644849280c0310f00c3c4004072410303100358240041031114960941102e84d1007071400c101d00c1324603020001880000b00f8501a05629400403d92024222544000032610349510100c40044074101110004849103880700b2064941c000d0203850039240310818800141002002113074031494030809000d00d03029610055004c0d141c48201c81d6842410350410160259020300744022a102c0070074410103040d4402003ca0664401405c0800d07640c540d00005520940d110300d010034044032080b00918024603803130051920000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 754357796 1250 754356546 754356607
    0x8070b090c10050702030a140304030515010303110f061906080a05060a1a13022203151a090a1a03100b03011a03030409020c0313030b0402010e040204050a050609060f 73
    0x100c54500301d0710f81c05208002509580180f256000041c1700644014000c0308890031207082681c1c949645142540c0f06003004a0302c105900140289075115501410141c0720800400316040c458a00c01c1da19600107040307007621131444030103442d040031980050380100001c104039100d500c1d403400d0640d1240070907120b01c04010311704040c6400e131100c0c980c2c100211000013000301d0a1289800e001401035801440310350400d08040140200600c242c11400018500506211004541a444007000c40b0768000d0120342c0854420300440b0141e841a03200341d4404880350300031505038183d020304d010040c41050010386c140241c1800e0a140c04007540008800b5900b10300074030009031a00540e6404c941e8011540c1d070590800c0105000c4204c3c1600101448a40314084910b011402a04412a000c560b0003c58404a4840901c4199030340004c02c1a03542c031048a04500d01407402d800281c103a0750501c43d0b2030094101142c80ca4090b03561000783c900301421340f0000ca55600c04042d181d01540f448210143d40b090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 754359046 1250 754357796 754357819
    0x90f0506012705040f0f0c120522062a0e0a0e040f020909070b040603050a15050303190e300105070e041e060e07030c020a11090408070b090c 62
    0x14201d0b00034151640e07404500c240c400703003890240b20140202c01c3c203c4448680303035035034450700034040e2094500003e0207a0700d2030240100d001981007512006000d0440e071451280c9414010f002441c910b00b41c056100c840003821a8544800c00c41c02480144009e0744032040b010b030103881c5500600e01050440d0220303114a0890b803035443c14042840161000703000c0d0100c005406005041803441581c0044840081b2007040d40d448001c07600a0b805504210002500c8005002c00c91040f40180842140500707440d501c101d09041c04039599020ba03840c40d281e194000bc04a100301805900207a6a41601030980c1500241d26110024032070329806071254000030854a10002e110184207441c086d03900356407031f0310035074502900b040007802c8141c02440c020580700100d010700b6480d520403000140380c0b44104c0d40152418210140071144401d0254040d5082100c0c030304000383c403540c9120503001085920b88100c5c1c64505103440030b80a111700090a0012032010b00c0f0a103c0002028030f6441400c983e10140c06 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 754360296 1250 754359046 754359077
    0x1505150309073807020108130230030f041d15040f0b1806100f1e0c23010c05120f04020f0d1b0602010c05030c0310090f050601 56
    0x510003101c0115868222a000f03021094510402254001d502803c0d03010b201c91460402c015568080e0a8000001d400207044045503000030086034858032040ba00c641010050300030400001d031090341c40f0409005c11484e580b4200089120f0b0185404202c00c5070b48650071005820318541c0140203402071078140a0700d401d9400507143c141c42c40b4442017008100640843c00900c4013038441a50001c641c1a100c4908030850748270942c201d080c441090881c0b40c00c1d424890705101006490072070890410580d050b01d00741c0c0d5600100c0c26124040002100c80360062a041c04540c3d40202050052184001800c1c8420141d19280543c8102d83c45100030800c101e86814280c8032486102d80728100004001c00080700d90350140c0b1405d42c0309001810807500e01c0c440400107199424209402c8076000542007882050600411500d0081c240c40e000030401d241a03c02c001e0300501001f800e09046071800000101c0000b10303103030504028000c400042c0068900301c104540a01030481e038050020b43c0c0c2c18050003c0c13 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 754361546 1250 754360296 754360339
    0xd1d150406110415050c0703080d020720030a0206090301060b0a0807030605041b1206181e1503230d050d0f0c1202090d0f05070e090f0c01050703020f011505 69
    0x21184d10008141c180b8108540a480c03981180f0a080000d005200b40000491190b90017080c252445400041e0380302118940481c090f0105100c00c5070b400c1000c2c00e10f41d002e40300020f85815181d01102d50355241d90300e1100103400740c5441e801207001000c01050304440c2a4000442e01e000301081e89042c0a5240c0710000c0c48115015818000c084a81c3d44c00c0c00104c0c43e0081c3c980e0303a5000001003000c1006034076120110525071580c061b204141d691b50301c100701c80071300c1c0144e450700041d800601031184484200d4501030300e003401d00000d014800d43c2c4d940e801c11b03540d0031081d0035000b003114402d40c0d00010039004e020b0300c2d5801c00340441c944241048403440c0903490610800d41c3c081341507118802c001910f040c00c1402034108500498101981c490540c01141c0e2080403280814440c10003841624140000041d144801400e102841d9000e203c010384208000300c7d48502ca000c0a18103a0380307941c0726013003c038075041440c09000025482e1018080c0c60240c00e003d590107565041e130383c1441c014010750340c0141 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 754362796 1250 754361546 754361549
    0x50d020f0c0109062109030f0f030b130c020a0f060203010510081003080a03090c0e06041d060f1b0309010e06010501020304030c0b071103070e0a060b0c030d1d1504061104 75
    0x2501901041c84035500801850105c0102d82107061800060010040d0803500500d81c00d80200714042046140c00c3c1d071061100c00d4071050381c43c0602c000700204011a88420100c00040c1c5175980341d4000210703042c800c01030a21890b130040030b01c407825513003400d28070001d5200b8000c29006042c00b051051025000e1407802c0c1c0036500426104d014513145440c3e5500e590440a007100400d61201340300400b0030100c1c10290007910300c561403002c0d1400c0100400045801d041c8401131100750340765981012420210703803207a001961118025003540c2d0305000d5111190705001800c240c1c4408800c0c401504030540c840000301c08141c04452503a40c81d03600590340d81c02389100c000e141207078485007401a00d24000240003050300c56000c00071200c2d0903000007810b010701038016054081d070490400491000501a280c01460072a08880c038203003840802e20b03140d00c40c4d5910040096103542e6030b5412544402c458081151429082c0c440000118111300c00510303007a1815030303c1c0b0740cc040f60745810442d008112030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 754364046 1250 754362796 754362799
    0xf0b0a0501090f0c0c030f14070305040e07020d270e0901020c0d1d041d0304030b092103070309140f030c061e070f0903060c030b1f0203040512030403060603050d020f0c 74
    0x1900c035240e590100e400c0401e000c7c2d12000c01c6061070300340060307503182c1010342141741c030940f50982c50b070b414080e8601030380000500d10800c550000c00395803201e580000c5000a8001030344410141030505452a11001e0260392003101c00a0116040001d6a481907015011031030a08080c0c85580c0035400381101c803e400c00c0440034500c80c80c016040341d01d10f00b0354444c10541c10b04048020300c800017610601d0440d00035500a5654056640c100200d81c1c205201401421907024541c1c1c8a401c0a614014890f00000f80f0762800d26598011060921516000040e0091449001c440440350304000c1170f51a83c011201c007006500c1158003081804001c070b110385130740000f040600179460360b8508046071000c49851450007400000a03002c0003141070f034004c8507003048258402050070901c40050040e00b00c5440840240c030420318034107030b01841e4003004850841c0d1049031107511440300d04d0203081c15403003a82d0004001501c0c00c2800400c10070082250b8442003220380039610400707400b0035415110701a2140e043d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 754365296 1250 754364046 754364057
    0x1501030309090218040e070816061d01020129010306050a18110f0c15010501050c060f070e0607150612240906090c05040c0203250f0b0a0501090f0c 65
    0x140103075100c2d43e000c1c28112100b54503541c041940540800c00f121407001e43d0311002d411400341071001780410010038003210300b0343c588800d00500d443d000903c291603502001d506e602c424604009280c1c0300b50008a014851040300c40c0524102c00c071070364010310f07103d080a40403904210002540d440c0c030180c1d69049901022140c00380d900e0004040f402001102c080c103108038428400c010024003c0000380a0360083d040081200e010502c1d400900840143c0c0220f0401004006030711072032802180094200e1801c2d5003085090302c6108060300ca1b10307410000d1a0308020003040e45014089001081c1d20000d801c0a8204003181d12113081c09614032043c0d5026250002180340d270210304915880710780d5035521042c1c0001e0006580d5403540103035038030b0b442e0903500710354071300001d000034902072061644608590006514141041022004299503c145c0c036443c603260605100070b116400d0745503480c80758071625004051805881c0d80300140300a00400104034904070603240c1408061080216189840d200d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 754366546 1250 754365296 754365299
    0x9030d050f0d0b3c0d02010207121704080703111f3203012108070305070204090602040602010515101d0d1407090606020307170c070e01080a060b0405010308160c080607111501030309 80
    0xc1d82804184c070b8038101cbd28400c0c40100103c1002c00f440103000500490302c0500000e40c554100070408900014a603442081c443d000e80d2069162881e480720b480700c0311b05000f05603103d4407603030a110402894401c110044a41ca8000b901c1424800850589580c1782040486410f0a03101c0060b4560105000300800000c002000c046030050001c0c04140d88020000720f40400299101e070142d8000340d00c20780240c0c1d110b0301802841d050307552591400750b105456440c10044c0c500741c02083c89442e0481c10701c1015441c1485170a944803500142c4081d074001032448442c2c2d140c900c0460703a8001600c200c44003580b4102020428510200c00c40c0d2450703800c003055036092801101c4040041d03000200141142c481c600340000c0b12901040494020000c89001c0c02c9003e07041d0400c4001d58500590a034031a5203080014800141103000b034070840d685500c0311001c40700381d5240000031120642c008090178461031040004007948280404010a25241a40c4101200300c0c104c4240201c00e00008010a001050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 754367796 1250 754366546 754366559
    0x5060f0909150901260a0308240f04180c030b010302120d02030f2b0b010e091b030718151101140402041a04020f09030d050f0d0b3c0d02010207 63
    0x9401c0190507605e0607901052201e07100441c50400741c1001280819004004c1041c001c1e0078015941c00050340407000d2410000103000188003184061300c9604c11a9200c1c1e2090030986103d02c0903030030139031004a4001050720780c2062029650309100480c406d07001000c01000f0b0000200348600d00c525035400440c10180040d010382040d8001845086000d01108500c01030045080c468031000000c001000496071401000100402c4903520341d40d0081002809006207800103403102d41d08030883c501995100e444c0c03500c0c2182c0da42c004840d0520758104000000c2096406048902e01c07096082c0c40300381100e003100482c00d00365040300c80c40308420101440081c0140c2403541100004064000d5118030381051f1000241c201e0300103e010501c25080405c001c9049d0408004008170003400e03040c403504050048070342c02d00d9882120305d1141400e8a50604412940b10001c4006070301342994051000480c0300350055019249034101c6039842000c101d0340802609140314a0043d003901a03004c1c0000c03134107009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 754369046 1250 754367796 754367819
    0x60b0c1911060a0914060901050909070302040f031401050a0b0d020d0503041a130b0304150216020a09090302010506040c02151008030a0f03060f181505060f0909150901 74
    0x110076140300e964804030031402d80d14a801043c125a01d901c0b5111a20708100d2007885101200c450355004180401c40640740f80c0e04081500c10030842250f501c07003d80d5403210118040d00441d0b118505040300248040100402400701c02d041c001803074020400c5685d10406030041e5100d01380020740221842d5080c1015051858081680c1805603045034038040e6149540b0807056034102215100c0c40300801c070001d44c207400070602c0c1c0050044000050850401c0c0c2c85000c404403245034a402c446500281401d1040600b105001e60031380c00400d8905210307620050000a841a8141200103500c0e04000074580c0c1b4192040b5584141c2c10350040105106841c4000d814035005414078801c0d48092038009848481000101900115036966041d50264004d000d000e40e5402c0e0010a1640e10f0340f041880040300c059246100f60b14401b030003046940c00720317400c000c81c01d19a0f0040364102d8000200b00001003a4540248100d00c802d4a2000c8265101c140171142040e101c0086940318051070010048101c440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 754370296 1250 754369046 754369093
    0xf0204050621011d0703120c052802040b040c08190e06130210021b01050901032c19020303030c03041e03120c02030a0e011809050a0906060b0c 63
    0x1904400c140550b24100c110800c8000142c150a80e4442031500c041d2a12969a11400c0741c41c007004107400b82c1156a03820082ca69030b0b815034100800c0d50144400e01030304002c80003900c0700c804820385c0d82035030300c21254403201198601a0b000754100134403070f101e030b0801e8400c050001010b955220390944840c03414003a08000040c00140d1640c4682215103240c2d01400b8250098281c1003184441000d94410b02105090141c4000c0c10340d08001d2600c41203072400f40211a00c84c0003443c2c03141c0e0310303030401005070010f26194203072224082c01c03658803c82c1d483d102e024512000f403070f20702100c0101c40c0041e41950300c41507551000750590024004a19403042e03120240da0401c1c441d041c40400c040d40130718000c826407019401600003038001480c00000010b503104550410000b48040d600e80480003201030321500e2001907507810400e400301c8408001100720f00e040094840480e0034041400c000803081d010b02240071060700c05518003200001c1c90742081c0101d40b410300d2408003400c120305400d000320800f032104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 754371546 1250 754370296 754370299
    0x606020a050a1707050f0c0f010519080c2b0f02070c05090c040b03041b090501060c021e030106141207060c240504120806062b060807030b090c04090f02040506 70
    0x113000b09030020f80180000d6182e00c1000e002060310003183c0040082d41d880544103141400340411012008002c1204a809608401c4c2844162038584840d034101c648500a00c080040100f0b480144000e080506006c1d14218880002e22180e003210022a00303c2c420f20000400240940000b08060300709000c109a2080e001c4610744d0819503150850b035002d42c411103048849003d06e801c1d200d004074112058001a000301c82c020046036042c290081e181450790303040a4802c641e4070120443e107100d241ca6206810f04050005c1c0045580c1d0b0000ca00008009811540b1424000c40c0980c040103002990008442c141d9a501034400c000c4c0e00d4000600060104002c81452014a82a0202202d0152038000c1e4403a5050450301c1380303020f100800e2000007400319072081c4030070040d0746180383ca0041148010400340d01800c1401401021240080c400c60340b20000a014a410003c00d0120302d1280c0391080300c0440a48202c00007100400c0300b100c0b034010006080309035280e42e00025060551085922040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 754372796 1250 754371546 754371593
    0x4020d06020c0a0308011514090f0a15110606150a05040504050c2107050f09010c0203070305071707050d060f1d0102270310050423030d0606020a050a 66
    0x1a9118201070740d1040c1c504100d41d030b01c207120a0080640c8548483d0040070b0303400c1160400317021094002c1c961410809903804591001c1109100c0d603907100a0194241401400c100c0221740d9609000c92082d100703071240e008517500c0d00c440c0540c01d00200f04940300302d070020107480c0040305400c1d076048517410001d000000c0000500002c101511107115441c000c0284803040c90315007500d0804521a58402c1c0342c0c4804600501050255680d040019034480a82d0191211f850b078201000403901144d6051010b503151141080001c11b010020030342d0760541d40d00481c0795040110030f0007200d075181100c2c032410f90071121010741400860405e5000080205002c0e40c049610461103c00442d441c0403854800116540040c1f451108804546400011940c00100340e00300e031106030010b0340b50791880c40380054107611070002030100b2800440d0000310f08031031504001111001224140e60b80c11007850641050f181c5a004108107000007040026140e00c1401800d41e815613a0740c1080207070099515a54009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 754374046 1250 754372796 754372819
    0xb0a030f020d15150311040c08010e06030f061e090f070308032206060806070311121b030903042102060703030c030e0a030815220e0c040f0e0d11070501080402 70
    0x29007074003d2611940c1003024240c02113045003001c4840c900002c20346840b40b458045104200c6070810279850461300050301011080d034507030011905009001a00e01442d010703500801699404402c0368040d00d1035098800020fa5450150305640c40282411800040d030004400700f000400d008001c41c3c0c010450250b030200c10f802400f924000000c00d050842d10310b9250302c000d000e0080100400ca90208241ca01401950011100d082a500c10410a0340c101900c0c2d1000408049203001c4200c41340602c00700e00d90340d91034283d940ca07407603800a014010041101c0c07140840201c1c0d0703151000000c40e400506180c0f80007035554003503000341401c0f0b008005142d1100700340490704109100c2c480015001c1c0e281c000d581d203411600458100642d03100144a00180c000340180e03400c50081e546640200c8000003d882c04141c1500d92070400c40c41480d0358402d080459050f105501500480907280300e00c2c044407118905d031001a10030703c1c40f0f0801d101890b84003036420096507200b85841d681041c0042d03d60340280303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 754375296 1250 754374046 754374083
    0x40b03130204200d0c0504051c0503070b1e0606030105060313060603120207180e1c030b060f0414030a2f0904080c0d0908061b09030d030f0b0a030f020d 67
    0xc3d0400d21030050381d0640404d4585111016015000c1840c255280c20b51030a03017444000340c400a08240d450303410703801007174140e020001c0410448014680000c65030176030b4680f40d070454070400b802d0504500c0384040080070512a062076800da905075040140780300c1c150794a0071f1260144141a6206480c52038498200102090842013001e00490041d4064401a1704018201d042d030b90520306004007091501e00c00f907000701030204210401c290341c590700941074002c0d400d00b1005400001d0015500c64400035a101c5000308400050045410441060140241a004041c0c40b00c2501c0c401074403030030744698400001c800406920380e68142082481c9a116070700340108001e15130484041b0340d15040000c202506080400a00e40010322900d0100152424141401c3c1c8034440500424601c0e00603040301ea02d20006102614200800681294180b4044c1e4000801070f00b181c10b182c0c0c80941c40d2552202d000e007048400c0c0020740b504080100c1c810480c1b5800d1104140080f5003d5820310111600315500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 754376546 1250 754375296 754375331
    0x812090312070f0f05010209030118050a032601060e0901050102150a051816030c05030a0309060f12090f0201090512030f03040305220e0f01080616030608031309060b040b03130204 79
    0x604e0180c3c00058640c1440c8c400d050840d01984401c075400402c0c1000400050710008000200d43d916141c0401112078503000e150512413986282110780074070a0000c83c101c3da006140e001e00c1001110300c001d841e40d9610044ea19165400706010280d00e8500014420700040d030007654012580c40c012010b16028011018145003045100010b0703610800020000d1011102c1400003400084016001283c1195006081c01c0107a11400c400e00c000c005440500b076000d12040e010301000100c1c01c2c00b100c1720038071b031903000600311082c102c1c049564010040303024100440c59501001911004520380103811403140540c0d08000c100320304114003008407085005683c1c00414606c00d443c0740c1c4c030000c00d04003a034140a0560003405108141785250040090141c006450307034000c0c200c4079258000f0380b101c040460140089420104081c44001054880240d0805881088504803081004943c1d05e60f110050340d44220711640031588828804940303003084404407200701d144010b200007080400a60030144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 754377796 1250 754376546 754376573
    0x2060c010f1409010b01050a08060a0b1605060703051003020d1b08030703030c020a0b01050d050c10091701020406170a0f0f020703020c0108010501140a0306030605100812090312070f 80
    0x4a251a540c02815250389442c40d540c000d0007040082c499120080c0009042d8001d515088013002044004105180c807070502c00405884000c6e225a40d4070401e5040c4240302c501d002080301d507841031800007503034544280b00b07083c001d040211010790a2803440c3c08100c1480325000040d42c0d14180c06c045404e9082c4910140402850300d0006191201c0c0c013414050300b01d40040301198155084540720760b000680211805042da40202c40c0742c280c1602c0c40c14003610305219881519004180d03929000715694110b000c5034100d50142d80f200c0a01d40007411910309030700542c421440070a03a42a10001400700922030a03600480412000440520341e020300c406a0304032411501d0f685d980000c52400740765052100107481d1f9020300380111076526080000300a0511181803804000e80030803240e902c0c5109401442c0110340004061066080400082c03e4413501489455144e100c0c80018110311842d95040e035800380d500074050214500c04400d1491a42e00031441100e404c0c1c480307600d040024070392100100c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 754379046 1250 754377796 754377821
    0xc0902254b05060c0304020f09190e03180f0a060f020325020a09020910030e010e0304031a0708190f02070b070804030815060712090f030809040c080106020a0f02060c01 74
    0x1240350105003802ea041202c0603115003461101042044003580b1a070050311000c4809a907620744560303a480c580c0c506012140181d6031200e05100320031000100000c041d06100c8101404c41b01c000e00f00004000c2800f05075010300c1d8004090740d0042000501600d19607410203510f0042e05e10b00b9080304844030380080c0d00c0103030154880200e0000d03800e6060403002d00002d0042c00340d0841c608140c020008454400002c41c140805480340c4045444034800c0d0050b0a10014420440740c0f50368681c43d00100b07090b000003160700d898210b00c0c001084a441000040c3c0140c1045101d00c1d802c201d400d15090142c00d106044003c2c580c0c08010342c2c00000c1d0705840c200e1042203180c0e2000b0700d9050030710b001008110040c0c00349400310700442c4264210356420088848032a0b01c03c0b989100d004c0750320b0081d80c410701aa403001c8491142c80f5000020710460300020101c1c110100d808020400e0b464030140c5085c1800c0c0620300059100d4600580004d000382c0d0300c40c034400d000800d82d60030070910044040c01c0d9032081c06444c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 754380296 1250 754379046 754379183
    0x150603050c0a1d040c0f0306020306030f0c06041203170108011401060e0a141302070506010306110712050307110105011806050a03030206190204030c090225 69
    0x410038810300303200c40c001030003089030800000c500e008402c2c40c45008400b0007801c24410040450104150001c610008012054140c407030b065582c101071009410490382d190290068901c03000241201240071461240700070809804d160400310108940100c145049003030000b0b08004d0310081c4090418640202414400400c05812204000b002c030f0406134440000e00412110b006100e9480803104419a190030008140e008a040300060902d2000038a901030188001003400c24414041201e1b410f1b80d018031801d01c05d41c1000384d40d24082d44034400003d81540286042d02c1c0c003051180c40110f802903003915200280032400580070303007110b80a07440300282e00c0030600c0a4403150f886008103030041c039048580000071032a61b10080c0d21041c1c01010800700000d000210351003680e440c1d054074003a641241103801d24540703500c40800207610903003184e04800c04038440c0002211404900c102c4041e400703941343d81c00804c44d01000407241c00c030360b03c200306560494212941c0401d440c2d45a560300e29022090 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 754381546 1250 754380296 754380299
    0x91406030d08010806070318120527060a030b030f0706081006030501140616140c0429090901020412080415090e0402150403050102070b1015080f070201091506 70
    0x10140340030690039001c0107109540300108070000b00800c1166005100307003008103118801040f0490060000c0700003c108442583c444d41e411a84000903003009441082d900e0f03802a0039400e0702d10010300e040d400550183c01004103295083c030079008500c4c20b5601904036443c00a00b003a006040c207c403904048001585801000003480326140014010140ca050400c029414944400e800c2c003911401c0301e01818000032040c00711450007d02011581d000a228004030404244894a98a020400754400e50034401500c41d0207540d01108005044124426001401641300b0310030b09100040882d03680d075509000004080701944541411a0701c40d107240d45e6510708080c0c0000380040d00100840c1006400c0c4014005001c0c0700d400d154100390111340c2150002c112130034079011441180c00041141d40082109400c0017483c84803203001306103240c018040961120700485030203082180b8074000034a840089110205280201500107499200110342c1091036200c1c88104181c0050074046166a58070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 754382796 1250 754381546 754381549
    0x24090803330108011211100302031015050a03050c0915120c03041a04170c0a0510050c0a08090307210e03060f040209100e0718090b0a1e091406 63
    0x140c06004140e0300d4440744000221000201002c50501590020b84100200da4091142e851a246a6403c00030318a01000c00302100c000d01030740043e64403000001d8607000202d501a00d00800c0381141e81140c1c1c503d8204240240124003400303000d016500c56030802c0041c0c01260311007d204ac1c0b010601580c2080d074422400c00d0516445000601c01c0d1070543c1c0034010301c00000c0503a607103050716001c0740c200184079031244c2c20a650b09003440f05075050404d00004407891003890200f807200200d4000d405440790f5803000f840d0f41003030f81c0040b52410030001e000c100d0054490b00071b000c096002014001100d08000076541e801c3c007100300301d1300c0c00d600c0d9034031090855406c1e1754882c071001d4044038103401820160500510808802c80301420013485051898006050540e89040002c0144602010401c103400c18820280004080055001c002420700d44042002c0d9a80c1c00f44040640d03000c0c01d01c8034050720740259025a034251610100744841503601c00107210115005045d21200d040728030901e1418402c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 754384046 1250 754382796 754382851
    0x90a02031f0b04050316030b040206071403270d03081617010e0609010b1207080703200a0f0e030601050609010915050d0605010305061f030e0a050d0905030a24090803 73
    0x346c218803484900c10300f0303c001040f2440054110754150344441e100d5507146000d01c0c110380d112a03218440e1101095100207040000c8400d0b03a0015030005803040000d103035041c40000b8040f42b002602103540e00020504140c0d034600c007030300380c0e03105403070140b030300ba80804500d1581185c20707449804007000e90410b001139841c00080341e60040541c18159460140c00c1c060b03164402400509040c184000000040c120301c0c0243c2003c42150114002e03580340c1b52000c00741000300d80005560307c000031009d00c00503a029004000724041c42e10003d0041485a28100030441140c0c400e00030181080030100c400110b030070140c0c210b40000d010648409803110401400c0340200e82103548030740c1c1010b0401092220f191105000d008069502001c41c400f00720250030142c015225280111006d4400e07040c0404c24441c0201d011084048030b80d0703400074000d03503c1e000c00d030759199400700c080c1000004c0c1540d08541d1400f65548114029660f0010820311602d49a80b01c0e00d40089403039482c2c090b013400c003072000e141c00b24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 754385296 1250 754384046 754384063
    0x9020406110a120c0809030102030708011401090e01050607020111030c010911060f1c02040803120414012705100c110105060603011202040b03010b09070c030e030c090a02031f0b040503 81
    0x1c00c010600c030421901e0f48540c441100300040140314207040c44070184140c410448217170400242c000e540d02d0500d40c0300281039560901c0303282c1010203402920b100c41d6100f284198100d40d0b01c40030303541c841d90a260030800e00e03601680c001c0381032000707280d01404c000c00c00307002401403a0300000000031019010306040040b900c00c0d1008070301c210300c20030940b02c43ca04000c060b92808141100318400340004044110020710403034207c50214803000ca50a40d00702c01d0700e801e641c03160744141c212201d856000019a0300741d0b0f0303241c40ba02009140c40350640390810494222448541c3c001d0342151025a00200c81d1411140308000c541d000803071144d2909881a000d0144c01d400400684190b46558035145c4950310100d84418000c0c82152107101c02d20b9030340e1b030941041040d03001c0100611b5980c01d00c070354085e00d54141c040080b0041601740c501c3c0c001c03501c0c011032480182d4102403d165469030b640504640250300007000343d051414984d0f0000003026400300710781d01900985204039610b0303041200701072070442030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 754386546 1250 754385296 754385327
    0x4091a0a021c0c0c0206031f050d020904030c0c030b0c0415090602030318010212070806030f030301080307080c1c091a0903070e13150507030b03010b030d140903060109020406 77
    0x10440d400300000c2070b400b1000140d03880100000e110322a008110b802c000c50f404041d50080c0c0c04001e200400c440ca840c2c00b4644002c0175452100559501d007880303860042e8040195000c1000400140424040d103030641a0314482d500c6000c42c01d440c2d50321045070800640c2c03000030f88103010a041c402c0c208483e201c1100035009051840d5001c1c9410390081d940d20004010b0b606c040800314132080741007400d406451188406c1d00f50f0340410f1500710401082d030001190310701d20901c500103480c8100c84000c03084034140e940c044043c0d85421b40a485040180d80710601d10280c510548075120440440c1141e4441200c0c03a90303440900e0b480c60081e083c013510920000f030014541082146590640d0700140b403004a0300c0821259034141d9401152402ca030200c0800503100e02407082410a40c0c4c00c1c1079001d640704a0f0145c504200403d04001450b08032074a848829070164450a141e40005003d03d1220703940c0b0f150085142c4c07a09066002083c1458000e0780070910007900864140a1a9003003001102c12591 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 754387796 1250 754386546 754386551
    0x30b03030910140c01062d1a1c0203040b0901150e1b0412050c3f0c120319080c0f0d0b060a0e03331504091a0a 49
    0x4250000705425a81d610710000e01a00c103011844080c0c02c3d0059410743ca0040000f0041959a981c442106a440c008074100701080036124040c80c560301003614046d80c0e214079280c95120711503c4161840e501003500c0c00154400542c0c0410300e0002c0303000451060f4410780d17000307032103040c8025604d0a48001c2c002180c50f54587d1a418072481407010b00315548135815120780ca00d9220102c107085928406c035000500c1c1c2e44a2142c0d58030511400044440c6c0383d41c01a10081e80000d40002d00e00c101c40200c801e090300700c0404502e540140080e0900241003003e842060706c40000d0701e40001040404010b0040a550b000861031220460070055045100101e5040850551030aa01c03020704a01c1615901c10b5143c0010038102c8030014254820b0400b40006042d85680d11000c29001e0404020300c414144a4811460880307030180c2c4503200c03c0d403018102c10700e1000943d120b10f80d0303d05c509401170010098441c101e00701c100c680c2e1180201e140c414014140000d01d001c0400118880e105e005080154090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 754389046 1250 754387796 754387807
    0x11508030a021b12060f0f0c04051e1302031807053a1227031509032c010215040c14010c06060305060a0f06050904030507080409050901020307030b0303 67
    0x2d40108001070140020802c2114102c09400011994410070322441c1580c0320b58010407401240115001d0300410342c0341c0e0329000684d940b02110106110f280110391f00901200c080d0320a5031070020b02c903104c81d40000c1c0011603803600390303a4103000ca81040b115944400201603045401c0c11041c809080942800d0f904240307012940b449200c000c50301c220040815104444031000003000a4441c903446c154016403d2442401d4418020080c00c400812503104514100100901d5061044621b003102c0c0e11560322200da1652400c40d400400f200e800030740903c41201d9505c0d0f4400e130100e451a007188101d01d0368401c0f00c80c54800080c54024484242a02245a201804040743d440f140c2841192a51040c600c0c0e507841e4500101e481c4c176806000201242d05100000c030070003902040040c81380300f01e01800c001142038114800c003a9410303441079035001b2070b05401080102c5d11400c000d02000f402994014a800d03510344c4080d0803140c04407040c003941c1c1d60210500484e958580103600350310343c0c218001c3d420f09 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 754390296 1250 754389046 754389067
    0x10271502120a08100305030c06040b15010f050d0609090804060305240f010c1a180c010504030605070302090303131503052701150602011a0102030c1506010c1401150803 74
    0x20321500e80701d401401010f80c0080d420700900690007028551090990343c4440a00300c95650301c50081e0380480340b8142003000580c4240003018114100181655403c04080c200c0c0010340d82070b480b120044400c00c1d1590b4000c14010428004ea444c0c0900c58108556114a040c03002411508042c015201166001c142c0440f0200000c450b4a022441190a040c0544075400161519202d4039402080040600442119400080704451281041e0150410102c03d5680f4043c2c88030f1000011501203402404240b020650980c48140e011040d0700f001881e00c101100002c2c9980c0118164290254044030188400070440070364102d00b003002c0c1000c0c02281001074414142220000380d0003010121a103410100e11003d4024420300c1c4030203003031030400f90307140c0c0002030281075040b20300d03da0032440170f10421503544004200c0d0102050000942000704180c2200e03d0012000307080b0700d04200c12243c000c00440d1140a03a0751550495070300014602c2d0744205111a580c100b5070001c605504103020000c0e64 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 754391546 1250 754390296 754390333
    0x9090106051039060c050406020d200703080a090801050c0d0b03070308181804080406260a0615030902010e130e0304060503041a06010e10271502 64
    0x8004a9041103104002054006a945007622909510480c00d501d5920340003c0310201c89540d05004203402e0054244261040d5803520640c403030740700140d001c43c0010704850320a08403141c021800740c0725044e141004400961801c400e9070420740d46100f00144400e0b41075005840e80c00108a2180244024130b45201300400f1400780450a43c003003515408810420794061140700099940140ca03107071255403016031914000783c2146800d001d4040205080584025010740c0c038800c03548590b2562615042c02000c65100c00d00c6210500d058464844144041c00e050b00100e1180d01d0150001607014900f11401d4860340032140454280341ca41030050f009070743c3c05000043c0c5840192a4404040300b6120043c0003010344502c0600c65000110340410100d52180c01540514000c6034010b80e04035038035101104481080e510307980401d01d070802d12502800d14803d8004030601d141020400344072040140560391002e2050442c1c130040c82003040c000400000d0f072070700d83c520440c0b00808240c00740503441c008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 754392796 1250 754391546 754391569
    0x227010608010807090f0e2b03021206060a02070801090b100b0313080c24010e010f0807030b040212010207050d120c0e1e1c1104051302220606050403020909010605 72
    0x743c00780c49465400e0707031034807d401030070799004080c0c101c2d184c0c42c081402034400d2a224228010307440c20f124480414a61080c02500c2c0114100507a6120341d484640c100803540c0d01008541c030030350141c0000060695400e1195203078044c050590325141d49000e00388412201c7c1c00b900006605081070040c0490410304000d10340c141c641c08008103550310f030000c0900785000006038918408000c10b072407508215030a0b464140c1210142c030b0501c03260340d0303c580e2700c2041b00100d402465490b600007030003080030030141d08a05820500142000c2c03030b0100300002040c26a4840d00c026606540f04c0c121025141da40000429044c0e08007820070031000c50b074100024100c0780100d0100c0e00c15030115818003201d50040000c2c3d0140e01000301254410200710711841701d140c3d8011070699140e075540c010a41c013810705001c2d1500c01c5800e0540000e100015900300304080305030310492034040304c0b6001003d104040750f20500000d482d00703844913502c2c1c914610400031907000040140ea4241d050140401503070b2a440003824 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 754394046 1250 754392796 754392809
    0x304060c032703092706051221040332010c05070b09030906190f02150105010309030c050d0306081e06061201090803180f06010b04050402160227010608010807 70
    0xc00c2070301d0600302c80c50b010a41100074404917440382a404d2031568a051202e82118401c24090659600c0412103540c160300d0310b603225900660f031221642101284041c0010301d56000031420547c0301d13240c0014059942403120800e5034100250100312103207080d45a6465018002884144a8444000c280c5d00481c04001c1c2291001d1020800d482000d00503142106d0b006400240c44070306442c09002d1000038203010101107116090b107a07080310720101e06a404a030340b82512515070703480c20300110700a200c01081501005020039000002403014410227180112590f004030b032090a000c60b140c10030b0b84c00c81084030690100c0e030b101e210f804408034101d54451800c480ca0031400b0318bd015840e0162500050040079120008100700c074140400e40300c210070b001800100d400041e2801c00381e40c1d030350000b805039400c414020310080081d45880d8000b040d090701031340d0400c0850401940071a04001040900400f00c0c1122035107000860f84070b140d0300740104918035003065554500916075469410600400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 754395296 1250 754394046 754394111
    0xf090c0506091c0501051b030c0a0e130908030106140c0601031707060e0a0b01050909060a0b030111040803031509010605030f040305072010020c03060c07020301200304060c03 77
    0x3030b0020303a00c2215403003020381e810039420383c883c0107403504900a0004840c2a20900003481148401c003c1007002e80b4031824508002910741b0384151f000755500c0ca01084178035804a11004168031602c10b42c0142410684a02c0b0b50700e07282d506200001d0214200344401c1904594148405a82c4060000b201c50441c4d40003041881c441c0c49070851260fa6125901d401f82c1118200480c2d100341043c005501000c0c0b44c0114080101350342c0f19800c000c0c0c24641521145003660041c0080703003082185a00c1202555401030001030760802e1582243c95641042c0c4c08201c81c1c2d013001c4100030081d101c1200e03114205008880e00c42c0550305080c0701520f207010181c54110000044400501014084c030102c80301c0a820003005101642d42361101c1c401c882c800c0d070089000e880301c81000c0700f050b070000864602802c00107002c0c00302a6100070080c5408c2d084884141c0e410340d00c8110743d120f88070020008410300220502890350303918290901d1016110480070150401d85007110b040581d50035011483e500f40780f0000702 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 754396546 1250 754395296 754395307
    0x402090d060207020607020d240b0d172b1107020d0f030e130203090c1002070315110c0304080714010801050d022b0201030f0c0f2001020708040303030f090c0506 71
    0x17060304c3d4000c4507002500009560441b40c10320403150590300c81e54201007407198804007003a00307800c191403405c0c055640240301620450001140905a017202e4010341c2425070600040320510940040f61030b6203d0803184403024010440c0c2c5481c082d015011010320700492404480c0d86c0412865189080040e169100c024040d604040c42454100d600713440c010120404440c4003411080254002e48200303001c1d03c00c420001c18141003041d410001d0201507001303401500d165481307048500c0b4030041081c4010303986994002101c90200c000d000140b109100558a4506000300e07076141200319002803131000000029000c1c16a0301c101260305660099454001d20030700c03403000c40c02c42c0c10203104d402803200031490304c44ca0581080c101940c01c0e90003682c052000c103030b2100034101224090808900021b0a1108134540180141c12005505280d04100e03182d066410248900320317000190304440c20031000600b0820b0541c1070044001640b8045400c2040b11401e51b600c0440f0541486207502484c0040781 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 754397796 1250 754396546 754396549
    0x20a030f090306020a050c0610180b04020705030a0305180f0c060f0d090308070306050d0b0a0509070806040b010611010e0601140102010f18170a020a02011b050d0f09050402090d06020702 82
    0x1c280c002598045410741d00e4104107080038001d500a544294014424240012400320154580004503011440030380c490000a090b458090034840002c0c0382c2041d0200b0103680001d80030001000100e200f81c0d000030741401d20010741e01e84240f140d2a09681d50740a41c880c03a029000214102e84001e8040340d00560301c0c207501051401600816a426034821303e03200d0b240090580005080c0c1c400d0041d96010800d079a01d070701c10030041c2c005c03480018101c47c8202000602601c0542c0c40560400945803c8030400303513031000e440307140c000c007200c00f100c00b01350840040203502d8000c403d0002d00e210b4200203004450112460941d5140d0500c140c160b8041803d5a08440740d0003035001e520401c4089409010b00c9801500502032079810f17810403108240304078800307600508803d0941d991601a940134003100c01254004444140c01e410400c0b00c01602e0a49400005108005122454003547ca0307100101d013402d03001401d80d01d802d0f44164081d41c0100f108800d507589203484020102e9012000684a030060700 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 754399046 1250 754397796 754397807
    0x405070908030a1d0301020f0906090616030203190507030c170d0f0204030c0801021309150b04120213110708031e011d0105010905010c020f040f1109150307020a030f 73
    0x9104407510b000001c0c0030300f001544280d9818641c034005042000400e03a0000b8503080744035881d22501070010070300001e4414940070004004040c030003003c0c0c0c1d003440a0680303400c106e0300301e840040300540e10024459540d81903441241c0ca89441d541003050034100507440140c85400344840080c843e030031130311550b4141d6070021700b0b580d043c000000c420004248140d400740c00039030240c042903035205803803200014249014000c039400d40c061000005003092505803008098107030762081d944920380d5403801182d60841140940002d044402404104d8511070043c400c1c4400e00501c0080b01c40d0a042d002085180003004a601e419485650941d81340e50b548150740e42c8a80d009001150b16460500020b0340e0701880e00c003000700350034080e003403680b5903610001510800580d11420703004c510110107080c05481c2c100540c074030303d1002400c08181e440041105004441d80c40d001450400004191000e07141424815407070113513030301c400151440c10200c80103951000a00c000a08020402c100040002e1095 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 754400296 1250 754399046 754399049
    0x21050a0e060709050a08010509030a0f05070501050a1a09010f06050901050c070e0601020616020a030516020405101e0b07080a27090e0c0f010e1c08251104050709 71
    0x48081d54018200904001d005454520580b442022109408a200d12042c45400c0c000ea6043c0b00131483c290940b18141d6804402000d2401484414004040420021f018440c4510344042c4006841000b1500000c020b54114503800e0180000d880180109040c2e981c1040580b40701d424202d03150200c15004803140c1c400c0c9201182c850081204c0000c55088080741580217034426000d846150b55a0f5540c6031105015400b95001a4040d00c1c40b1790200e030141000f4581c3d101c9481c00c017189000e40c0c3e00410243e07401074929005013a2020740c10040e400141110344000120200e400404902d40080c2d84102d02881a02a03c02e2000261405849004e00c44803004c0995030071540d504c5401c00d5030014200c5515102c0c15135101d0418180f244140c0d030101d444043c565008100190214042c0d00442c0da4203450801c0c2504072003031b04910301c004000080d1000c07a1600c5140c00703075901c1d002c48203a4202951507014010044030542058000078000028a110300601a83c0014144e5941303041140d041c3e816 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 754401546 1250 754400296 754400321
    0x30804030b1b19300606080f040309050603042d110f06030a0f0b0307090903031409151801020c0c030d1419020a06020c060a0b0f01050d0b060f0a02071521050a 70
    0x40f800c0380f030b8189404e500700c2d004841c21078031f55081d140d45c0c4507955020705004490050000d007109105010070300d403900265801c58018249501070003080748448500360804c081710b4400000c2c030300303440e42000701c84440c42c1d81109080d54400c80e4200d00700d010511074040582440025034071240c030092159003039404200650001021900f60607601c000200080548000035000642131201d41c1d2021400300450502400307608009201100d00f44601d240801c4000e890010000c00d03000c100c00c4115001d0000d0320302005610b0107007074810004001c241c1b4101580040c501031003640c1c4d903032400d085000b0f000e4411030781d04a0b80c190500355403004200c0c00c0c5031000b08000d00c01d501c00306940390304250000f8624032400c0711100c20090b44118404120745042c044419a0025804201c000c10346c1c10190403c0c65501c401034105820f01903401220003c54205140f081c1c016403200104100340c81f0800c01d00c080c401740504085042e114001020701d04c10002c050440401a1a032020944105040d804035070040f60 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 754402796 1250 754401546 754401617
    0x90623030709060e04050106080f1503070b04181b1409090c04030203010506010c02030d05090411030a29033304083105120304030804030b1b19 63
    0x824035009080d114060003500e002840b0000c0c2c040325170805100707842c10313a0103c2e25400415521a0844842c03618020501205040c41022000154808105013405080004541ca03100d604004000c2c2404000440506240d4202a200c2d000d042500080009011052a000c0101c1110744540181c520030301c0401600001100104884200d0300310280c0280d0303208030004d0200c1d44174040110341da407c18040203545600010109003400d03004d2001030824540151001c5014a688803180300c05070412144114140d44a1002c155050440980d50904411084021160900d00c20201e0354580850400924032076007200c600e5109600b0302d20040e007012141128111710b260611380140c8c80d8222811100401030101305075000800b602d81c00c40f03c01e000d96000714000c940762400300890014120f8048480b40000c210102c0420881c0004001460040048404c0c900f08100011109500240c070070b42480030030f000c11402364070f1700b203079418580280e45025030080001480c40c194804000701000390408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 754404046 1250 754402796 754402801
    0x20304120f050f1914060601021e0f03030a0b030c010804050304290304050a03110102120f04080903030d0c0806010f0f0e011b06050a05060405040804090c021c20030a09062303 77
    0x94100780000c01e0704c0d02c100810f5a580e0018281707166181820385805000d40c2200c2c050103034280115900120420b4140708498903121406103090443c1e100ba5284051103840d0b01c20052542401c222590400c0402e01e0200c00c2407400703840d065160b00031405508110520400c400c0d200c0b0082e007241e1135440b40c69002195503814031b440c1c80ba03903441200c401100410045510301500031411720994000c0144d5080d14403455440c00404814a840104101d6240700140801000d03510100013030030905840000c0056081e074440405489500028101d41c104010030390247c2006502c03100100880d161410303d04e840c50048001a102d0301e881386030000150f5038424668007800000d0304484e000340c140000810054a9440030300040da8412200504440401c0000704684806584074458201c001d00c10754805541c1000b854103041c4402046a0000f80703800c0800b01421340300e0140c004034042840096281100600c0c0140004207540714a1080c0040040c410007400c1000c086000300c500c1040d02a0381e0303171 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 754405296 1250 754404046 754404073
    0x106050f0d0c080f0f01080c0d08040801050705032415070201090b0c01090c330507080301030c080d020604050c0d2105040e0a0c1d0d0c1401030c020304120f050f 71
    0x702d401312411131180d480600442c5114444880d01c0d41a01d68003401b5100720f007100003d00c01c45010103a01100c688004120000c0c4258080c8201d600503503180eaa000ea403410304508c0c000403194104507002c541403440801034259a2404042c43c400a42410380641700c10f5035000580d0050515480300c0301c0d00100023a44c803480d080641c0074000c4588200c1c0d1400b502e0343c403040340d03403800e0740701130214411192a40b0f03004440d9208121040d4112800d4907025182c8407003541c0700005a00280d00031105484800700c02d10920300e0510028903011080d200400e0a403425031500c0e65240320701410310f40122407400d03890091180340364960ba5501540d1445424008640b94000c2641d88184140000c03035003000003081d41c0c12080d01501c50f4101c0c09a40305200040c1d4032085020301d0a400403c0380c0d01816074040b48000404240101e0f0040262140308881d0800000014043d2014800300f2000c54004200c140b118201e628071640302290030803010910300b440c0e48be1052904c120410b18211912409207111840b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 754406546 1250 754405296 754405307
    0x4081606020d0c09050f2809020d0f14010302041a04020f090f030a0803040605130210030b030115081e031b010e10060303051b1c080402091006080106050f0d0c 70
    0x8401a03032074204040f0707014507002c4400104600030903502c44001c05a0404c83e04c0d0800405c50108031500d00e0039002e5501c21030928085c3d005900c0007000c01e80200d02448045d03021300c541c84c0c60343c0481100303103e1214040940ca44504050000030f1003640c0c1c41c8040550301c40e02c0304c41852a48c00151045640e0281d5000e40d40c800c1c1c00951565110300d070062803400c21400e012401301001540401c02c203003107803a103999990142500410b20204410720b40b8003c00941d944103a20300111a064500007580d02c0b41c05c05250a4410ba441c203486034012011003041480300001e01c000303800701001c20a01c0341e4490662031901710300c2080c0741540c0b0113a04440c1d000307122006611800c0346d030502c4812501c070802105007103000e480a511002c1c0101e481809440300c10b240e0044507070a994105016070300d001c040f01c03941200c0c0303001401c002c80011381110100402c43c20b00407072060300841800e60000c01d0510b0200000c0501034140540800c00c000442d031342c117410000304c040d82d000c000d221009018080028000a18 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 754407796 1250 754406546 754406557
    0x130e0712020a0614030408181309060e010b0f0d05010609020c030a09270e0a02300304050904080f040e1302090f04030815180a06080f0309180408160602 67
    0x2c60342260200007900d82c0140504408840b08001c0316085556a8440e04900e0704145e860400b150042c0c0c081002a83c0c4410712000e40b1304a08070000303000426400d040f03080300c519101e00441c80e13241c80b02da0074290365041034803005170b48110340c0380540405515015014000f45e038400304509001041c91403031881c000c07000d0410400617980304003049540e0349807210401f40c024042c02d41c1c4201001603103001c55141d003064440407408403c45814180c03950200d03012001c42c10315407020a8000b185007030b001d40792040003030003643c2c440c00850405040c01c5c0050a6040041c0c402041d45a0015101c002c5c54004070941c0c2c0102100b04200004d45403400d0b55021246000904921130300c8650001140c9810450106024a4041d6101c640540d10401c000301150842107806602050824403404180c9202d018a8840c3d00300321700200d0410714044183c0e01c1c000c0520b00440803600240000c02c3d1640f64002d80c0554101c3d005584240c44c2c4503818100c0043c1309444460002520140303500c02409800c1d0010407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 754409046 1250 754407796 754407799
    0x5010308040303111b090a0b100801080c010c1a09210a0305010b0c070e09101d120705061317070f0c1a0d09050f07060c0b0c040e06130e071202 63
    0x840b4001c3c4110664840e10303a0044442e17080e900758003071903d074100101c0d0207512a00b1007000003000550400002c805101e10400c000c0080d150720014401400300380b21442459400707003000130780141c0c650740302c020f045c14082d01600d1590b442400610030032010840c002082c0e1030080c0d884c8c141901c1c11741401107940006007600110303003410000141602918101c40107a00e2040240c400710341006400103620b500a0705900c2d0900c904846880354030b0305d0f8420a01e14054011607580b0144110010034103011492a15005860043c09404c000c10008955203078410042130460000540d64079003641e60005400251a24003c04140e1008018101c088050150300684628207410b0351162402c0c030080301010034242440091002840280f080e40102c24140c4c4102d060340c1c43d01c00ca24102c2e070715103a581e03403004000941c4004040280711540b14081d401442092440340f9044c14800e00107004d910103840d850040c880b04100001c5099954480034524001c0010703583c0041e6664916121941c8440040e0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 754410296 1250 754409046 754409057
    0xc090606020106140f0f060405040608100c020604030c060b011704032007150c021c050622032f01061215050103020102070b030405150c030f180606101205010308040303 74
    0x110b03c0c0d40c0b9039142400255001070401c185c0e01031200c2404040003041c00381c1c9400100910010465035100d010b803001038420503000781010701c61503072480d0640d000c4e01420415900042e041c031011a901ca00b00c50040c079000b41001c0390980020004a902c400164003000b01094100180403c240c2d004030074032880700340304082c40040c40d500420f45c0e803114a40e104001c8145841c100030b24007680201c5010108500060007050505518040ca40d140c10304004c0460b040d070010001c10201c2040c8044901c00400880540811094603540241c9030039003511720080310b00c0b40b85864840180c0c220304040000403028000b0b1007100d942d020100e10241c201801210b07102c082801048070b40c1c0f02841440e040307a40590040c00c1c5989004c00301c5c1d806e580040c0007a140f5000d03e903456030400044e110030358050944840450390b01d1822408101c8540e9015080384031340210b003544020845800a101030f00f00000b116040c01d032640300d510585e410005c040d80c0705140c1e0304000000040c050304c0400381084a0080d11003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 754411546 1250 754410296 754410299
    0xf0904020703080a05070807081b13150906050f030109020708130e070e0409110d0212061e06040b0a03020906060405031905010e03120406090f0807061b020d05070f0f0c090606020106 80
    0x941d854102100d0844c0001c06001c00035014040b880780081c803c0008008551500c030741140006600300c00d039004491420500c5081035133090744450303110002c0540345020f07404d01c0d410f0603502030688018410040c905401162071800d01c0504d80881d008002402224002a40d903000a4441071508945550110701241000034041c2414000d4440d40c60f8000240d0503035410803010040c0c00041044140e8001002010382c0070010f10401c04030307004401c80e480003480b810396007045294451004015038000c85c00e00159a0140d11040c0c03135281600c1c4c1c1207500c9410b0381d5171007020800794096907104507414481c400d1a42456040c043e411008a8018002400030b2012004081d90364420544101c0f0301e10702080000c1c020070610351015050621542d108aa07491b41c43e11256a15001424191900e540e18080001803082c0686696007410080c0060315500d224110060400c0c040c414020f031903c1e40001c0303d04c04000440e50051095540205841c3c100754130380c4019001403030355000d0940590300e00b000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 754412796 1250 754411546 754411561
    0x4053d12020c0a02040507020a0b070e19050904020d03030e0109030e030c092202151c2a200105010323010908040306020d0f050a0c02100903140f0904020703080a05 72
    0x80300e0082d00c1c2074000300000315580c3c0c00d02c0020080200707080114000c60b0381a50018a0800a070b0b40034030820f03179441ca0090041d4042014802035254202d648070320001c000c0180d5220f548420354001d8044440c440721884608040d000303001d580c1942400c42d480c10010400305a0071006440a410080d400c80b02c81d50840014095800c0d0143c988808401111410040188084082180030380c4003801d00408103103d202e12942c1c5811510b4071001407480400d40d210f002d140b512404080003d0005444490350029036116201400050b480303007002107419040700030103c030040340004110b001c00200714542c1d59082c1a03460f1081c0c46d030011101c60103074400d80c40c88031050081115007900240c01c0d83c9010714541e10740d0000e6000200d00820140c50703040b8002d940000d8841d081c0b04002c89a80481c015000a200904101170a0440c0300410715080c81d14001c41e0f800a90b400c02040c1c0700744c1c8c0543d00c6e0a09045020b40e03001e5071162581c4036000041540406a0221710a401150156010721140c0c40341308 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 754414046 1250 754412796 754412801
    0x1050f0607150902041a130603170717210f0709060e011b050d110114070f1e0521040314031005130203090f030f04053d12 54
    0x225040d4060000c0c8403240202e452041401c481031280040080d200c00c4960100d015030f5070088840100c240a20900c10715402e20340c01d07520081c0300340c0d9000c002c043e042d59a401041000784440b610007103404150f09040002c4040c0c041d04444000241e071380c4800302000c101015440e81003218260011005c04515514003040d4014010626515030a101901b480700440305406440d401a040107900080741111208440c94003525501401c09041b883c40c610034003600081507c0c0d440119603152410441100c0121003015802955a190070034410418400c1229040c0d0f0300880ca480074a40d02c07400725603c41c1c0200041082400c001e218613000800d1300d1104110340d20894029010880c8603400301003042154008503400b94142c28584940f43e15480410444606644020513165001050003d403100170000c02d60400d8001006501e440c103034907520071181c000e9124080c01503140901644204035101e40500d04903105595100e68a55110300340751400315140c645602140818400103c2d0380a00d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 754415296 1250 754414046 754414069
    0x112021813020607060c0306081f1104030204090f0204050c040303080f06010512010803070314040e0712023609090a17160f02100518090c04321c030f020717150105 72
    0x104400c40340822b22a00520103068243d03112100e0050410001c001607079a446000040e50040b06803548502040c414041103c10140c8608409002070004000080e404001c2a900880700000030b0515250040161114001c4e202c00750390604003a000410030b110004040e04005000b562030107507842e600d170b43c4405284074600881e900040c8940000f03090314021800b001850b60401c000620300300d103482c02d00c2e02e942c1108400642e1031000e45070840c03941408040ca01e0914004403613100071424001d0942e55200342140005000d8404800780d130007c0c60030542070b143d0b0941d101c0e030152102d101604e04640921503261040b42304071840c0008141241c820000e98810b045a44810818078050380200b1100b14401850845014001c100100c1c101c0314290380c01c004034039060700f403810206920380d4030540302c03011440850080c140c100c280403004920410201103950103007401e0102d0907015034201e003010459080080700043d51400b0600003000010481c0e4a40040311002d03043c0d9807110100310708907400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 754416546 1250 754415296 754415323
    0x70f2114030a051003080a030f051806010e07031407080414010b060d0e0a0c06030207210516020415030302060a060b31121a0112021813020607060c030608 68
    0x70300c0054081c103503580c01241c000035481c102d08001c13952640c0c0d010351a481590070100103500c0340780c45200d5140c036014054110031515180701e8000c1c0312400c401d90381c5505101d0710354164081404525220b02a80c40303034010f074088140a2030203140200010b445079105813000c1b5007812000c001c079068400d061160410784600180100c1c604010f18080001801e0007500c00c0415000307100c00400020b003842c1c82d400007061a500c000d80c07601041d0420518101810b40303030b2915480c074001078402059101046031410520741c0f2020401100600200b4014501d5111065104140d200040181a000503a152040c6c01c517240078414151076480d14075550040c4980003200c15590500f6104065009020328ac030003000003c141c01d003036079900c0c8560120070345850a071400381c6120016540b038000090414003401c0300100d0b929100807598081210001061083c5851082c0200440c804559264600c8401070300189990340303482860604000a100d40010080801d192100c0007a10080124420050340034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 754417796 1250 754416546 754416587
    0x403021f0906080a1103090f010b0d121b0b0a050402100306080c100311071415040b0f1510080a06080d090605090f06070503070c05090c0403020103020906070f21 71
    0x30b01402690300e2100503005462107529030f5509082550780101440c400c0306410001c02030143c51001143c02c4503440202c1600910b07030500880702050060f0030172560f05900346840c070a4261155012804c495803030700024070482c07132241440250402a04518001e0380211781c0c0d0007490ba801d40055040b5030b042d100781b0020380c00c01e8546032000d1514600010b9941558200803a4500d0701c8501030f80d02d6882010106e664400b00d00040510400070040500e811482000603800c41c20551600004104001d0143c148442c0142c001070842024611499441201603e000d116150441000d40030320411102c52148514107070000460050010715806040200c2d185c0c000300b10b00301502100c559003c40e2071243c01c21110440c0701e0076912030800401c2100d0282e005181c454502d45001c0e104132000d540090f02c50350403042031141500d500700407035048a81c24203006030ba50b010200411014000c8102c080e080c450303c8140b00d024010300c40312820440200b04c019811084c12041d09841451282c40c0726084401d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 754419046 1250 754417796 754417799
    0x4021303020d0c0e01061806020102030f0c07050a1b080105060603130b070e03061015080c0f13030803161403040b04030c03022a0a08190305090a03060e030403021f09 73
    0x5000b10300d507891030302401594041c60380703884081c1d8003000b0a034072120006040c18140c80c0a1002d540440c3c015100f184000d5185050034894100a0b0802408652158000189180c1007003c10803072008201d0348081140555a9403c41d44048020584a010b03c594202130002c0d0707451500f0f5040303c1c4200200010b1503240c0c0619141c4184c401030050030300081c8180e44200000540d010007c182c864801c0c03030915480c26091a8020000b550320080900038442228184520b07440150140c2c6c0c80d04510b81846ca440703000b4080d1b904610000b940c00600345800000501c10b540c410140f170101030700f0207900d070600a10500580d280c070a02c001c44002d0550750741d44000c0340c0020310508030194254040c0c4101c0d006020b1110300850607420206600d4100010040580d0341824201008401042100c001e0503440c1c000400f8078031b8907030152000a081040001b03141402d079554481c10b5000d543c12000c10415a01180703e1103a882c0d00038041a80b26060a43e4601c0b20885205220100440700313580311410603 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 754420296 1250 754419046 754419049
    0x1080601090b030a0501050a09030f030504021503090309090c040f1221031103090a0201020d0e031c1107030c05090117030a080901240f0f0e0f15040608010504020f0402130302 77
    0x2c00041c414203605002c0d411071a0b0104409006d400e018002d69030f000544140585005404110307002824414141090100005640d6200c0e0014074510000d0880c0e50b2a51000119420f41c441c203240d1640c0f003503c0300107201e45060034001a0007500c0c14503003024a250744500b0148005822602c008100700c0c60300e551394800c4a030700b906400b130b485c0013402e010807126400e0000e001a9041200d44404507800302c0d48050641d82e04000080029016042ca160540300600100e81c030764105414451120181c02d2540011500c00c0050a00c042c0361360040d074004540fa4540020019014490188200080741c000300c0e81c01035028084901000c4200150f00d003c84010003501e6040d00184071240e555070350006101d40c281c0b82001c40750b0313031020030301411866070410128104100c040c0d0011601d1086414007408143c00004005411214600740d180340c0c2d684849a8604011000400540041c240f0b040018564070540025000d9403007100da211400c40d1000c144012400f442c120703801000c20b070326003c0000d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 754421546 1250 754420296 754420301
    0x6190b0d0c050910270f051504050708060102100902150309060907051e1c0602030c041a0c031b07081005070806100e0402091309031709030403020d02120319080711060108060109 78
    0x508103a18001c94546c48140309002151003c4502c010945460031482640303150611406500c20b6980c01d10b8441d40c00e2110000755505a050a050302d890340d21480340b8207550f1500c11880749240c1e06072042c5d5482c03a1100051381c982d141034440446500c65140c020409142052a03034610aa902e1444000d100c61401041030001d820742400d04500241c050210100b4901e00086120310700c40303e40c0e59034441c03031301040d083e40040310040502101c2d818000000d141d40084100d03201c0c1c0721050b07641e41e0b6421605e5142c1c0e0902d015940481c08503c900c4510140c8004140c104a201b00c03240c0e00c42140310b54402040c00b01c0c580b503008080001683d11402c03480c0c1d03403030543c0c0900180c01c0058001140c4524090320b040c100c0700459400d6010800204110580e080c001402a901c0210704015504080c55039021403003c2aa0070b50092003040d64003003034022000c04000399046085080120344082c184100301400030041a555400000c00420051a50b4072000501504070385803200104240ea2810513284d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 754422796 1250 754421546 754421609
    0x1b06090d08150409030f02100b0a030f15020a0f0f05031608070207030203070311150f0f1c0524010309110d02060708030109050708060a060206190b0d0c050910 70
    0x110070b03100b0949448940ca8600c51805454480d0f103034590407061400d006880c110b2001d030700c0f400881c01d20145c1c0c52035407143c00151302142c1d40003000800790030151400020035100152a80c0120348045840d041c001e6100442109103107140e103c47c21540740040007120035100441c0c4c80301c565090748010a5800380305003040c5900140303c1c410741e60704540320340c0001d0801c90148e10070784000c80500880c400300d143c005000e042180301360b0002890005240d6141c941ea01540d0304d002042c120114100414034900140740031141600d80d810001403504c1d40c2d00b480c803110300780c10030710b00c80201d5000301c21a94080e101d20f1a4482d081242004c00313007010004c12038041c2030700d08101e8202c2018443d034000544503901440c0a0700000c1c0c004500c910b0901c400501c2c2540080c00300303211f6607000c4000c100c01a00030500c41c3c2c0154a200c42c070314000031a440e8004c09452005030083c1c100403280c00d507506100a2503605010345a04442c03e04141d200c040c2c0c1c014583c0482c0c0030745070f40030044c0e06110400054070030070b44d40c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 754424046 1250 754422796 754422811
    0x60f0b160201140d021e03190207020112050117060615040e15040507050a0206090102130b03070c0c09020903060604060501090e090106030b070804121409041107060609021b06090d08 80
    0x398a48160400628aa000094000d600580100e0090700c08000003c1b0204071b4150b00702c00324110700e000340c0300080c00308583c3c0340100020b40c0040e5800540e440340c07511203c3d51840c0c031414840d03545d442e0764680b081d5180064660041c021900441c450340b038130800f01450408140740d81030820303042c50701e4001c070b24030041c00a420081c64074503201000c0c3c8580c01524030541c415200c440e1100c0e401d46010341041070041202c00b50303910401600d840241e400c203c0c1e2065440b003880c60b0741c413565441030556040400503400b0304104855040022444110340003018020000d4040d1105510b4400c14403082c4c56a600515001c684010b1043c8000c04010200c01e0344070088000103d0840d94a0325214040f103000d90310400080d5504003040117011642d107098a4204141c604070b014040311002800050040c0f0081500c42c0340c445400c503c0210760281a14290740e00700c0f50400c10366503609480e4009505c50000f02c000e444a105182c031070a440812038a200701c0c0002c01520b9000445081203444201c002d0004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 754425296 1250 754424046 754424057
    0x63b0709270e0f06100f0902030a0e0f030405010906050c060f04021f090609050d1101050901111921020705040203060604080109030e09090c13110903030f0409060f0b160201 76
    0x8079008080c0e07000e642d40c4070100c100035142a050b8501e0f40d605261000300045400340118804005100c0b081c0c041004032500d40c1310050b12a11910400700c007406100410036240d100303240400015803404001841259400d0f240d00d00c1e01a5103180607680c90007490300701c0005405c088001072944a46503440340e0f000303100800c0103400c030590495802010040110520024660703250030b00c0f056800190000227400b080355050800e004607540d410704c9114a004103410480c0118a4840c10703401210f4550005501400ba00c200b0386045052030b1a4900d10786043d544074071101000c40006001c40d83c903907001c280320b03406000035508000602c03010303500c05015035410103010880025107000a00c54202e065101c0d41d200350410104000304119084082c5c486082d07034206094401c2c569940c00014041440045008641d01100701190b0703880d4029520350039018000081c0e001410030740e0300002c0c000d0b1414910108105900c0e0f40c0322400603107041c041d00242e840d041201b58030009055090751809841458031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 754426546 1250 754425296 754425359
    0x60902030c180604050f090319091a190311030a020703121b0f11150901020415020322150e0a0306061d0604050c04030213063b0709 58
    0x1103502c1c06250301280c041d50200005101443c0381c01c0c01481d4000760b42000b440100d0a140080e00c0e22403217002214030080003100e002c0512940a44101e0340140703140304803a61010880086250349038048010442c62416035501400d4582c001c0c460942070109252546045544196405000b0740c4108400c0d000d1141c0001c445a60070070380e00035541000511200144000c0000c031003d000d0403400c0302500c0c02d209002d01c90300c0091b0340004850b5a00001c1a5000b5215244e48419a00911450700320350310803100400c42c4078805030000010104004006092801e4003c0d005c030003c02c00c0140d00446556418040d55502114441c4500d402d014034001c02141c0301c56580c1c1c0d2600c1c03c031400c542c01000c4804244545a407030305c40000c0b82a60003401514140118600801449014422400000c1c45000801c044002e080d0540e42f00070080e0501a0f100c04114a1150080c00c901001d0014002d0b600342c9000000040c40f0747d180c5c0741c0c0c0201c42c0368076684485400d0000100c0d0710428000d030004040140e180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 754427796 1250 754426546 754426549
    0x18010e030a0f0e09041101030b06130608060102070b0c1c020f01090606051c02030c01050c030d090503090a1e050402090402071a090c0a0810020310030813180605010c060902030c 78
    0x41c541d00c251074460204052880101030080e40341585003e10401001c0100008185203541c210050708091800003003112031080001c119000c0c0410b5410030340c00003180855020303080a409805070340240c00701e8402e02c1d030b00d44000c056032090319100689900014691001268000344201c0100d405005031905070402250040c2120440d0b003058504c1501c628007000581420054468202042450114080c0707172900829601d84029403403030b04220000400d0040380e1000d00980c1c4684401032414032040d0003d04240d43c3c1c07a04000c1025224101b45800001d181a40703c0010070a10381d100b11a824040c0380c4400c201c0203400c00712002e0b07017141c2c0800110380015449001c0c104440c0d503c480248260806096162030991628015402107100303030740502c00c0725000202991010301003440540d482d605c00095844c06a030710ba0009159030000304000c416100410089001d4408a00c6c02d442c440c0400d15002081d510248600360210306500032500c041001074000ca900540064121138480b4140f10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 754429046 1250 754427796 754427803
    0xf05091903030c091d1902120609070c0b040c06081302030a02100203130f090f060b0d0515060c0c120d09030b1527060a0b1902070806071214090618010e 67
    0x3a050710150305101045680c4414280549420b026206c0840c10305100c0b160000025a004d05401d1145600f01d00059809124000315054254002c4e144d0241c2d00341480c090701c079003203e8007a04003c203640c4000541260103010941e401d036500100101006001a024000003d0300811094210b0104001d29640800110031060040a500b210000d11500d400014001c441002003042c0400d420300c0000c1244514810681d414000d1600e000580d503202d5003a40284050342841340c82d0042001b085541d90751078085507112182800351a000e00c8501203860720307600c4020104052001c1105d405060001c5601c07641c0c4198460001c1080c003030a000614001000300310300607075600640312402d044022912605040e81c1c0c001d0f900b135400c00c04507801c1910b294030f18026070503e20910210b014014100500c2007000320004c101c0c0c1800d031280d0741040c950003131000d20700b080c80d1080a0704144062805040e00382c002441542c0070000b50025480300b1100009903104000b14002c00c0d074a880e4200c11504050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 754430296 1250 754429046 754429079
    0x70f0e1b07061b21090503030f07111501170601050114090d022107080105010b040b09060904060e010812030903090405130507180b0619110115090f05091903030c09 72
    0xc0d04c0e006043c2c0e9100324401d00113100d18078440d00c2641858034480000f0800401d907030300141410320401182d610243c0403180944050310a6101c1d1140043e0440340024200c21305050350781c2c0e03451145132510b4400c01941e45941c00c0c4602c0d4009070140149604200304080a464007510090420070802120380000d00d00c01c1c1a51078032070b40391040c60076000d0814000c00141000300000c070001e004641c54414810860300452144076586100010b450340709607156421201c2805005000f04015500e4603801101032000740103440f00f9105a18101c1c000d078001c5010381e44103410000c000e44c074000c120000c1c4400b070900178083c0341a00300d0921080f40024400c1c400c070b00192030400341002c0b0385100007041307100395151651954040c1707008119005030210302108041c1c0510b05428492000360389040706600500040304c004462400c40341c03003c501421b060300440c0d01d050580d03005004584403110b1842d211005094540d42c8844413005090020340250050341009007541000c0540943c0c0b02d42c5a040081c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 754431546 1250 754430296 754430351
    0xc01081801090506070f1e0c0215030a050901060906140609030106080d03020a030b04050f04061a12071517010909050106050904050c09010b0f07110d060e070f0e1b0706 74
    0x50341000b00096000b0f1b06000308002d140f5224542d183d0281241c6181181161458100182070400c40f041d521440e40100d000b0384200004c075074078605018590000c0074242d504440b03550a00100103002401c0380180e1003528151140c8280c0f0440003000c014059104c08185901035403240d400140e802410b2010b502d100401e0b89015a941d0000640103080f01c00d03041505220b10f241500b4001c6401c41880340702d6006501400000e241000003102c20f50050700c0750300180e8803042c01c24100b05281030104100c070481c0c1102c800f5016901030940251200341c0048044044501c2490041100300015001160344134003800c00003450544889c00318074204000c66043e175a9620496010115061000441e8010305401d0309550600200034071507a00f81c421b031000508250b00007001c2c2500b5030f07614a40d8aa001e90302810400c25040f42d01c8416071209040d210701506d02038148400103081c00c42c1e10000b84564640e000c103611081d40d013a080081c43c6c0041c003059909070380e0b4113003501e842990014945c614007075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 754432796 1250 754431546 754431553
    0x1a040b040608031c0f05010b07031803050d02030729220807140c030715030c18030c0810020306031207110d200409050703060914160f0503010207050c010818010905 72
    0x32400410709541d0451221140a1b1a000041111500c1c41080d1504150b0514141440b904801c0002c1415040ca030005407a9014100852100d10703000802000c003244543d0000300f502c102c65801e0701e14110342d4074031400c21800c82c00014010904440c400d200340020501182c0c15507040c2c0e03c0781c400d543c220740700850740480b502141d03a00d42c80c010044d20403c40c004900400b501400d00511032880344a200c003a000741902d0707036000c045540c080c4d03014444600d052000350060940d17a04042c0b266501501c180b00040c0510054002d228089000301c2e40b1810014005042900c0b003085000c0c4035074400d00054540044240c48450315946109500544a02416220f4524100007c120749a090105200340c4524500308945001a0020942208072600200e000608128908110411803400c0080b0406402090340e844055807103001c0200c1958854810109240e840b1020300d0300700e206400d0040c1940d8018850490103620651140b07601005a00d4441d80780ac82d26840e180c25200c2e000d504588942 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 754434046 1250 754432796 754432837
    0x31201150e0d030f050c030d050901050a0c1d0919020307030f0f092102010902030d02061f050112150b0f030a11030c03011719051b041a040b04060803 66
    0x5a1000841000e004100c8021800e0342d00c69078090001c00840c54000184030303001ca1241c242200c14000d41d00600702c0c400003840f144c504404403600138071003110071201c40703031900c01d0000c201032182d25503149042c1d22400b10320720305801c4400c000c0a4903005100e030320b0620180c0b01c000460300e0a4005517014522a440110760143d4404070b49003520b2008001e01e24240c5442d95020100e0703c03124440b0602150480c4c4075443d840c1080081303000d041140f5010b03404d44203020340d4903000750340010001e00c282e5040947c43c1d02500b44810710200b991703080c411a030000c0e0301510315030300142d1640d001140c01008104000360b820390724002c20003150407006600710040004010884102950302502440b010076404181c60751901c5a401420740c0018060068082030b00000400680c20402841a00c0b805123042200070902e5450f1503035031101114080c181d80003034489126114100ba0054031009482442601c110f2443d410901000f418070b0b0303404c1e551040d02d90714009003e0130217000418811840b41c4c5c4c03800000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 754435296 1250 754434046 754434089
    0x11041406030f0c01020304260105040f0b010806010501080412360e01031703100306090c0302011e080703111207020c0108130201090501081512100e1c050309031201 72
    0xa0251440d68950440740003c4150b81c0d000c02140e081d00e108001540500b04c000760000d001c001e59910700d20166182c10140b20602c4a40c080f0f500c0410303c250300c1c02030aa0780740c80c0000d072a8a801e01c26140416126008180069584404a02c074925a85000500d1112041c04441c0c00ca605045d502c803400c21b0381122041c0402103910181c0903001c140c110f03292075407440d603031354091015548000c0748118012010035090980c103140040210b401010600c000c1900b400c12401e0700e03002d840200e002c20717088081e400300340044040c41010610641c403804183d59504406402500403000c464040c00810402c0c99440403407048544e001e208154000c0000c1480c05001407c02c480152108000b085006007000060380e0003000b10060350400c0ca45400300d0b44505d01032385400881241c41690180300e046021030075280018802000040744602441039409a100c002c0d00d0ba444140d200b40c12107841003c2d0800640100001d681005803441120314064005e000800b03000c40a03040581c1000c0c5510000122 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 754436546 1250 754435296 754435303
    0xa02190f030e060606071202030c0f011a091005130917040f0806010b0301031e02040f05060a291e031501091a120703180609021e06070f1104140603 65
    0x780104200104441d01300180002c003c0d0290040081501103505284103120707100740144c42c01a1914011242075403c1301c0c0c01c2c1400b8000401700d013894130780c250760740144c64902040d01c140650350304248803100e03a04100a00c040701e03038014040c0c01c4140e15a0850800140c0c0007503050100070242c0411602d50b420040f141e682d20446a102d070034581d115038011300c6001d800d0001c032411240d100e04402ca0803540c0300c00319030400655042c041d44c0140b920b80308910314079040d00940d1065804860b140d010948800700100c5541141030050158800e074964051400b0128006000c1c11002c1c0700745001e02c03516501122019070007150041051070001400900c2542c00c40c0191028010008601d005d885010607416024000c841a1002c01200000420703c100e000c0da10083c0201a2185100f09031001410300e00040c00070301d50200d00170464036440d9054210841e45014010200410580c60003066894425415020b20016246000c900003161050341e00c5104070f4109002d41c1d1030160307032803034018209400e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 754437796 1250 754436546 754436561
    0x120604050601050c03030f100b0a0513050316060e0a050409140c100c020103051302040501061808030403030203040308070311060a1b181203111203010305070603020702060a03050a02190f03 83
    0x180203007489100d1448102001b86daa00c074107203100b00c6100b03589241240b91030341c14540c4003001d80b0000040980c41103920600501c905802d07141c081d000c0310303a924240f55441002c101c48440c840800ca109010781c5203d0b00b02d2100a5800038045c0e0440d58803a00041c003207800380d240407903807565088040310b40d0503021300c400504480c0440b904d1483c0340070054050880c020303196000341003556403c0019803803c4800d50b10081c3d160050001c00685d81c48034009000341400c0702850440d56003504001400410010440e000d82c2d9040e4051800c251541c0d40d00d0201d0b400c101d03400c80a0021700d125807410706500700030b280d10415803414003007040401d02000d10011901411440b00f0000105260341000790600000c604841411118800012003814101c134401c05240329440030380a00070090b01802822805107040ea4065015a02010b0340c40e0000c0d8100e00c00c0000003504035101380525560a4003e03805541c3c00403917188050325180020300d40410303103a1494056008034061400c0c0019180e40340c40b5070031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 754439046 1250 754437796 754437799
    0xe180a36051015030b0606070506330d0308061f0e150910081302061206012d0c0305040b1309051f0306020f04050901060f180e0712060b1206040506 65
    0xc1c83d03207040c880300c01401c40c5000242103d49000003082903501c4900445a2854000080c0c0e502802e00448401c41b5400744101c00c0d00030b561800c003039804410b018566540c070f4000102110b03100300e002d45e0241c4614200a000c00da01c07603088d4a003440c0b844031120280782850071030f40d01c24440540c60010000c11030b81290803044c6003c2c003485803450351340300c80c04401981000c3c0d0502003100d9690f202c501c1c612550b000f40c004e40000e4046041541c41402400c410301442007625030107a40260000940c00e14035500c05030400350302900090411031400b84101400e100c0c003c0c50b250f031800f81ca507004407109a006c8004441541381c1c140302001240281c0c031806411841d0105458501000f07401880401046800023504207a400648400c0f9991203504440040c40c0c00707010400c8030f41e134450020305000380c40c6900501288400b0380d115000407071865840d003034600480340e01c0c51076200c2d204c040b1900e19041c001e44801d0b560b10040402c520301040f000d46818003440c101002c03035180c1070f82070005a58025110381d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 754440296 1250 754439046 754439051
    0x20a08160f2603090a0e1008030306030d03090503070602180a09110a050f0d2f0702102f0313080a050a030507080405041b0e180a360510 60
    0x24020550320281441000b40c0003503160741c402c41010340840c21486440c807880e030300c81642074001a00e442c2d44040940b01d040112040d00c49165151304140d221320048a5071940f40d04110002240c1c1030080d44071000c00e9005004a03030418a1079541c01c4201d03841074001200011030b030090307011980f03006d600e50400703012605c1e01880390180c1307030400b40180c2c0a40302e117540510002240c403c0c206181882581c4440101d0755040c00b0820040d100740c4800d045c4d0300588251a004601881e01c0c0c00e03605802c8921503940a04624034031041302c2400c40c4d81d0190312780841000c1081522460155900440c42400b0401100183da5118034481e64116049001d40c01070203180c1140302010f003c1480840c8080c4040d0701400d1003903440001c4e15100f1500c2c801e6401c81c562007450900c1030310035080030017102c288803459031303c0300c1c4c4159240c0001c004900d245021b030108000d0b49040015650a80e503004042c1c890030b030380000e0404003e003407a030640344000c004084407810703035200254023800b80c1008520b5001e5103c071401c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 754441546 1250 754440296 754440299
    0x80c0102070b160f141219020703120e031c0806010210020c0a020405070c060c180503070e010603050718230603060901090b131d070e0f0105100c05030304030e1504051e010903020a08160f 82
    0x2107081024a0100c2f02c6c05100c4c09080700582500c0c01d00c801c06c144c1200d4005603c1c0d10261140c007800c41032055038118010300c5140203828062000b40300f00d504156880c80103214074599075003080080c201c01020041040046024800000d0081c050300f0540000d581792090425003800c080c0002ca030b1590701580c8240d01c001d0040001c804004461415111507140115059071a550700392818802c1481120f105000700c84e001444466403090713408080000d08160149101440400c0001c1c002a00c9103507208034000d00410003243d03d40d120b802c18510280920544402444c020002c5418011320405441c152081c01b16001c4810702401d8040d144803000c0e101c2a04151101c590070340814003c0f80e0003041b41520b041210b40c05003590b0079500d58000100c070342d64945480c000f000e10308814070107405503114101c0b1054141609007a20113649014260f00a84140184507811040c1c5a81c049070500a0410022026856882241c800350003904010080300d82c8001701d10304410f0180e4440c05200503078040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 754442796 1250 754441546 754441553
    0x4150303140a050301141f02150a0e1b0f0301060b03010905060607030c14070b0315100503130308060d02042c1b19050604080c0102070b160f141219020703 68
    0x192415542c01d81d4126418400c41c0000c03500021703100ca01202258003224180ca51f0560008a95444074080d1044c200300d41c441c0c0240400f1b4592283d2200400c0c0c2280640690040e0121500131501f10001d00205902d4030b62000300342101d000d42c1042000c810008018072510701c0c10b00030184c00420aa03200da1600740d1541b001400b034581444c00909020350080905c48071f840c2004000054400c8445155a90400402011440c4003821410380a0303d11a03007500c030014042c33015a0b1241529021241c140300c220340d0107e035094801044160f000c86110800380160700d8034412080200d070300c40c0c0d200d040b05200030320140081011540030f801d1980000840609401103900d100b4152200740d03400d84000e5150008180c100b2240e401c525044a0081b400048030180000e11029501d800c0c0c0079960160780b60181c0c07858034460000d9840296140c100408006001d01415440c518060401d100c0d4009503031500754100b01421701508420040401c0d80d5040a0088409804040446c0001c02031a440d598 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 754444046 1250 754442796 754442807
    0x6090603010b0a0c0503131d04080d1508010501030308010e0906072a061e06090501081c110111030a050105040902031b030a23010c051e0a030b04150303140a 69
    0x502d0406600c049038a80325203010742201007003603a0041c10740741c480d103c514003050541001e2181c88004089080d28400910541400360b015039080701c541031400c003d0850b00400b8100383c01054064421400e00050300c22000c0c4100e03406144269a080c0f00b55150590012050001400120300d50300700c14103010700c1c9a000081c9041c081c0c624a660100741c506940704601440d44500041c000d9418412410800b0503500740e4010850201c0200304101611001d060703044640900a200d2203501c103000e5001000c400c0d0454451116580c1b6100c0c0ea00c1c106600c009096071400d402041a090740801403014881e4035000745405042d040e40d0422240f58545c0010781c1da00c401c65001d81c2c01a2224207210300d15142880020b1040c0c0cac001d04480f080b4010b80120000c0d490004010141c994a0403200c1600b107031040e070807198a10071500d04e402009110200c4011103030704c403942820a1607034a4028803020f840d980a103c01844050307402c1003c003072075810302500c524001e100c1040540b40c108810064603070000f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 754445296 1250 754444046 754444049
    0xa050f060c0c251e06110c0117100312080403090b12280c1107050114071502040e09150109050705070f062004081207120503061324050609060301 64
    0x407050850310388202040d0501c0c00c3c2690000f410300343d100c42c50000703455501c4400c4401c03914541d071140c072400307220840c0b6903e8a800890702030000d00c20001c1da01e00740340058184c82c0c00c007455150f02a00c03982c2d00c4d51030540881076000c020010030040c1007000145500506540014512400d0b490310703100c282c501400c1e415400800e5281c090758804009900303060040d44201c142e0b00810f01c1040000605400a41080e03c2540b02d030040b8400c030751010419504c21942c0001c610308402d0483c0c1441c04594a0ba101029075944004400354244000540100b200100781c2c011381c014170103024210f40c1c23401c07800b00c400f0050b00800390440c10b10041c0942c1d07540c00812104410703000b6511072641800d5241450140403d009080500c02282c1048134003484264014804ca03104e201c2250600402c0d460a8052801148009007000c0110182840e85900074001140c0c0701200601d2030141151340c042520032106101c01481da80d904014044c0040c841070b01c1208003804045a20505013a200c10003e040c03840305 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 754446546 1250 754445296 754445323
    0x91b09041101030c031113140406062307120c0201030528020708070209010e061c02012c10120e06040f14150c0720180601020a050a050f060c0c 63
    0xd030354041082c503101e0303882401e04600c600d40780c9030b075607548441648860007d800b529031000c0c40700c4407a0b040b40c0781c140702d18001c07165281c90340002e2104c584540d480183c12420034103c24281003200d40e000a81c415410410050030303496560764502c0300d00004049038030061120300c034034804058400503064803082922419401840159444c802c03490700c0b414030700820a009400071114000030032498001010103100341019648940582540c1d14154184112400c0190100d058000c110203e10701801c001e84014491204a920203140c07500410200743d25010702100180c12a03078480d0240d80759006451070340c641e81000b410785003411303100c404000c4020480180358058580c8103800c0c00f401404180c2800c1004903c1140b0f07454017284c241080e41c858041100c15002d000030078051840d921420440c4c1e8100600f074041200c4290015541c07080b00542200c1c158410b0f0116407000a030104100003843d807040c0060001d0894203092645480b1002d400101f02c584140411016041c4c000340c0f0030042c00703c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 754447796 1250 754446546 754446551
    0x903140d20060412030e06130201020c061204081803060a0c021e030405060c0c0303031009060909150506060903100b090609070815191502070509010503030a0c060b09091b0904110103 80
    0x6a500f4103030021b00d0100003c602900690080140d09800f105200b1003060007a005e89469045070030401c5043d202e030303821003c411022640420b011906c200c0180c0b02c0b2070803518402c49003005980c0042d240c000c1c2110103040d0191510002c0342003a0b418841c40303070350300c03a41002d00c101c09000c5a04541c50780641d0041e1409841e02081415154004000a22006c2c0b001380c262660390801c01c0403250f0207041e034020105483d0034001c0010300741d41e503445070920064025401c414507440e4003040324041d007006481681e121209110382c40c01e1303075011b0000e48140c20030b500c000101d14141e00140000e001004090303031707c02d80c0308000f0400c0040d0000b20741644982001b062480c00352404c40040c13209844d880e0300100f4419014408500031a84054030002d85405408585400e03680d04c080103801f441c240100c6d500354005101e840c103038500410074406a2031084801042c0007200c034021485116040703a02c4100c55100c40c2c00d00550741202da15480c0000c01c207503400c140c54546501e0301441c3d0580803881c0c0c1c1c101035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 754449046 1250 754447796 754447823
    0x1505060706022a0703030906090e010603231e0a05220609240f09030e1003020d021909060201090308041721010801150806040809010903140d200604 65
    0x10203400800c8070303040021040103c0240c440b41c50aa5613441c501040700810140740c004030b009406401e01d1000c540d00c08a00c07208980c02d151040f0b0181c041c0090302d00411440c10303603000c80408020316561054858410417140c0000b1100008400e88020f07000c1c103400b51814080c08401d041c021003014001d041152044c503800b21525045001b00210340020349400c0c0c00d22507594041c800c0084d5810114902c040501c051500d02d107442003156505080200030400819146901d0b00b8420100451305406040050810741d045801c4401d80c5d103c2d59030301184c240d644000141440e041522900074120300d1008200401c40340d034024104120141020b410f813030750300b81d14511801029080b200c00800c4581c61051b21030000028000e241028000ca411030350900702046191101031000c10110f8103400001c0940c2d49580e10b0300c82d0307280c7c1300440c003504020a11360040003081076002081401040c0c0c10040882c0700100d9002404140601ca480030034050741ca5159104c4500006c08a8005400000014880 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 754450296 1250 754449046 754449067
    0x40303081b030403020a14010b03060402040507050f041412070b0d0906110a0c0201030c05071a060307030f1103010c1103070b250306030b070f0801060f030b04050c0d150506070602 79
    0x190002948a407090000041200700342d804200305890364410055212600001c00c0300b50b00b46d91303a0460407a0168025400a0058502600a950010300504000346000460811384040e540243c1101070001c0e0b458000342c049007461205290381d0307030301040608442c6051014030078161044207030403410306454103002814000e0719480000c1103510754441c60b40e125035242d00074201740d52081e001e0780860715140443d007916002d001225941540300c02d840c3c803210f00701c03010102040009441d00e40c0500c6047c0d40800050001c0b0017041d01c2ca4001d54a003400a0400c1c0109820756445520440801a4141c48244840301c0042540c5595501c40c21002c141e680d01608808881040100d601d410710045070f121010b2a0140c0c00703130003900d002c2d80d8040d5465540500550b81c60560540c406c0c005007020f03004100e8a4410304184900c14158900454002c0901001809a60301500c14420b50040000c180d0380d1408184102451400d2071494484a10729080c0041c419005441001c1c2c451600041e2600c101c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 754451546 1250 754450296 754450321
    0x20a02060403261f060806060f130803030408030f130c0e0a140c0702041103150904080c0703600e0705010f020c0a172b0f031104030308 60
    0x2020f503d221842220701d8501106000b4022150701c4d41030400110b4008540d040c452001c1c50711400002d00020300e0150407a40042c901da0154900e950092078016010490a10510066015a0203094503640b40d04229001e490401006071803115000181c0b0b218400107500300c1e10440441d0030540e082001c80d60707402004006080c10141040309031076018104185080d800d00a000c1079802602d04000044409000c00e140b44000d42d100c00d600303484501741199514000b074500e680f00e07101d08500d600305840c0d40030003440c101041d00203e8026400030300c0c80c9201441c0c600155200414240320790303c1c1c02a40a0a0905880101c903195008400c080c0380e02e44c030420104040c840b0f80310710342081040170390003500390ba2150410301550740040c0c0e01c003d103011224070004260301e40382d40051030660380310700e4041c10340000c002800c00c85c0300c54040c0e003035030880c00204031111a520520b008031286413018a0380340201000c08451060b0180340c604141c100c002c01c80641520256a0b149c20001816152048100380 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 754452796 1250 754451546 754451597
    0x60112061e0f020d0f05010f090504020a121a06010c03120b0604050a08030a0e060309120313060c0905030c060a120c0c120203040609050907050d0b0a12030c020a09020a02060403 78
    0x700700c2d0030005100310800c150350003060340b2900c5030800c001a0900c0e10105050ba030f002e205030464820194000c0c40600900d610840c1c1052000304421580d99803404407507150303142020140c3d0310b000201c030041d0094840804040e030110003483c1000109115580242c4000342a00b034608485958080500c00740e1a0401102d0103001d0082585941580c0e0303400e813a41d80ea00401c0c0f01000550a8120341d501030402c4001c2d640540e6420018123003103441c052424019400007402d9401d0000005042310224485110388058801241e5034002003a003800241071074090180304940c05807208101d03900066a00020079102c00c00103040100c0e0480316180102c44050b508080600402c00307070707074092102c143c00000910440350f29840e0148580e135584100160300000311071540104404000d04440000d80c0d40c0611003101d80145010003140d200c03c0b2281c0c80b40c409200c1200481c0041c0c88880035031502284ca500200f00c00c91040d440d000c0f118000a403510400390008007800f0582c040c00c02a292281d42e91072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 754454046 1250 754452796 754452851
    0x30c02150f0d0f06081905070b0f0c070e090a2603071107050a06050d0b012001090209060f0307290a030c110d0219080f0d02030402010f0206011206 65
    0x15201c8014100224241d4801420682c03410310740102e0a14542550042d0000c65013240c0292045000c1d11151149110030702504840c0b41c0104100880d0310b01a4101801f009144040c20f2921000041085460003415800100012103010100582c4842c002075061750654000c2141c144105101825501c5075000c059074404840d000c020810415400104007509080a008954041d999101446104002c600482002403070411419041541a17045820081c1d01858860303a50810f5040040c061501c0014031107003a516000510150701d0072502a940003001210005003403076034800004d030385442600c520f021a1662510780c21404004c3c0d40c00101d80428020141c0daa044400c000500619011096030302180d604c0150007060303200010442140c0d851078005260514507010034040d4801d1007981200d40e40d100b0040300603070145e0f10019009d01a00c1e4180582c99041510014150041004080c0304540c055401002419400c107504a45903410440020b060350302d10814411a0324441c4a01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 754455296 1250 754454046 754454089
    0xa020a1202040b03030c161403210c01060902031e0f340f081e01090f0902040912110604120813050604030905041a010806061303330902060304030c02 66
    0xf200c0701c00c000c01c3d4211641e87c2000300c0290750382c44180c00070514100341c40003901984080c0d48100b45a0310650750382010400c2c09901824080d9904013a42515480d8220191142c0c01009200d269140c1d01e0034130b10aa0910322a615075494a04450009004000c000074a210b100c0030420360782c0e0f4841048000404804044c1245800e103110000d003510a441a000d000903052900046035241c481c407044000c002815a018216442c00c1c0280d40a01a000c4000441c1503a66208000513a03851280007007882c450100d0001c0c0c003074440d50191070403424501c8181c0e03135088107040000140600f45200d07010030007428080c840342c59691108480741d100ca0302c020520300c02c240c2230200340f40e00010315500301c800c121428002281c0300034000b1024003070410810702283e207140c00714400385000f60140003107110044651259907506e0320703607900402007441d1501901c3d000d60411911b0700008a907611560001c020140110b51065000c900d8501c4010006010007103412040c408554a801d5020804100400794 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 754456546 1250 754455296 754455307
    0x1c06152a120f08010501030c05430b150913140708060613060f0e0c160b0402030f010608190f0b0106050703180509060613090c052503081b0c011b110a020a1202040b0303 74
    0x8014142c2b4401409880200c0502c0c00605c8030002c1d2240f0300d5500001410115464840203c40c00a400b15417008440c0c1c108040605c01260104024038402030030b21100918580c00e062040c0180744021540c581021800c0100c20300c480d01e01c40100c50115003100c0050702a03940c80d10300c0c40f031a500603250042d40800c1100718100a200f04e0700702903801a03008030103503560b110140000034220384483c407440c01c40c2d4110280e8641610a10301c3e0000400380150304803039981d40e8a540300c09080000340c001001240e0081034200c2815030190608030001500000d0f283c08138140300019590020040c8554817a030f0300002c50404100c0d11480c200c00030890007109000c480350aa00c0075105422031558600d0000c00003120321001c1ea10104001b203031641648404c0c1d00d9894071010f070381d5240c1d802c04d01041064820007045030381181c00d2060709040c2030100400c009041d01702d88010114290800700b0102c1d81e029190030030169940044403021074599485610034058588003160162040d5008194540804104d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 754457796 1250 754456546 754456657
    0x1b12120106080f012301020c03160e010905041a0c0d090506150f1005030606070506070903061d1c020a05031c06152a120f08010501030c05 61
    0x212141a15800d40b546000d90b501c3d40101410030009224610440290740881700c4540790311015002e0498061050700c8003045c001c2d0101e0314005603c254035980d1440460304202040c8200c00d604d001d411840e00a00c820305060700c403540c140c84180c050f01034030412440802c5c0441035050454031f90a40c03020080c441d44400b400c1070350301c0c3c8104481c0745800300c00310044414540f8016001048100000707000c01c401c41e0030b100c42195a500000c1c0110740004081200f1400b06a08102092103440c4a58030621920f055140c9182603800105c01001003070110107040406a60115440300310b10f613030300f43d4490007102d58981280360003200440500039000000f0191010109415103100d40406204248000c3d13566002c1903840c201e50156000c0000c550101c60f12404054908601c1010000c0503402e41082040d2181c0030300c0c4800d00d10711004500700c068041c0300380390040c44c69401403809080402c038401d8070204c054400d00c01c5c03010b180e0354110390420100d96454024400d2442141d00d0606d0600000c0000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 754459046 1250 754457796 754457827
    0x6022a1f080f0a060f1a0c03030907031104022506020415030b0a0e070801030b09120301140103060806070c0b0408130b1b0724200313140102031b12 65
    0x32200d15181280500288102109001c4e41044901c0001da41e103003249090f81c40e420444050080c080c600008001345000310300c080000d14003408030f28016100051a625010740000c044038140f9020324014840a84011502130b012820b003001450103414184040c80d010000b44030304d80050840f08003500040d90090f62640c8401044601a1058400c080c3c40c0d0728813840c5040111001d800243e950f200510014240e024442e401c00184011100d107801c60f00170480e1550001d8100e21040313803400503006440e40c0d00d40200e80003442c480024101e10308004000400112800718090200c42d00007000c1410425003000300d842204041c00062a602cbd02c40b01c440201e81d004900c52001003050481540c0d0f2030381e011502d001142d075100b640e5240000200c4c40810a2042904108140002408403608110707682c102c00d02c0c03006660000e03640e5204d01c10603c2c0201100e41c0c1005060410010801000d03036000011120700103120300443d055003100758101468101280007011041d00c010868030b200c048a00e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 754460296 1250 754459046 754459051
    0x1e0406150206011226091e0108060f030601061d120d120203150d0302010b0a0b09030106091b27090204060807021614030c06070c050a06022a1f08 64
    0xa030309403030140c4d0341c9294141d2a030944680c050020002c0c89004045000050700c2c2068a4a91604080c20300c0d001c600045c8100c190030f10b942000d401c203540c26513a55a0f00208069214208030352076910a00502c002c00d41d01e01e014084e0b0000e104041082c400d11090140201d01c800c14018803210001d51005481600d6081e23108080c00840d007540c1254100f0031290007900e00c11043d9440890710303c4035072803c20103010404081a415035595020307142c1c0341d898056000c00a0140c2c01011a0398540d541c091600b12003017648a500da543c030b08040d81d120708940c1b0307072101740c1e082403898121500d8140042010130700c604403040400d81c15015000085141c5150090001c1340c625840e2514160790309042aa2034a1901011a007042041c070720911207402103401740c66140402404171303031580300c3c03c4010803025030103404140d0340c1c4020312904000034a84200310501804141c8050550358642450459011f00283c807005005250380701c0039421900e881c04801044d8a14581166030001c414101505140d4107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 754461546 1250 754460296 754460339
    0xe06130f081b01110c01050f12091b01020a020d0f080912010e1e100c11030a180801060e010b16060f0f050726130f050f010605090c091e0406 62
    0x150710b075602ea03543c051084000111080c1000d00004803800004407007640c00004030300604a018025010011511001244100c01c840300801203010350004201c0344803004028181103511240790500185c903a5031090303040980c0701070842d0503071000340740c60744c11401020b0300c40d60410241d4a840c4500030054102e044404400c4040e82c80b0b0803822643d00040d02c0c518401103060786e22011300312050400d103901506d004003444c503203d00c02e01780052849040d80c1c4041c00c01c03400101403c0140c00c034002c0800c17900d0014522003000f040502d2400b0021095444c051140383d0403080081035202c40c5e40da0215031109080c0d448001041000c035061812802080390b10522445140741400051800d030169220b8000740390303481d00740c3c80600380742c401040405000400c0d0005c0a410104a000007a418244030500c0c103119401520816005990240c00c5440540c0705030310070182d0b40300784140b042803941140c1212000341c55a0241202c0408074182550510400300e42081c07911400080c01e40703031100c44c561111103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 754462796 1250 754461546 754461583
    0x142a13060b19260601080a090b100503100c1b110409200901030221120d050106020d0503101203020a021206070323060d02130204030b1005060a0e06130f08 68
    0xc40480b1003042e1410704001d58030300307030003e40416407540c0500066940b00c101400c0c046503014450f61a0f001c010401e5503014060310410742c1c244910319060101020701c000380d0008100803c03110000a08410b0407140e07011100745400a92801d10482404164528a01074010b010b42101403400d014420003a42d90301c220100003a0500f002840c0824600c0d0480390010407181002c0660102c2010a24800030441c1c441d1184160700c0c0072800c0c44d140a4804000403280c00180c03076140001c041d0509514501150400ca0b042007001250404180808181c0c1d06040b0510041c40030f41c0740603460503aa456020b0b50003480480e0750b00c45120001081813003071165580c207100d901c0c20092100604504501d000c000d803940302c000240d45050100e0010760403400100110490f00c800040340040741c3c01500300741d540e030907008100564038060b1403401c0c000b090203a42d003501e0a244148002d0566144d0584030780314000010b080389606020742d82c2d91019190443c880c0350303550359a6400c15503d40952101459810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 754464046 1250 754462796 754462817
    0x40314040f0f060c120e0d050a060b0319031b110301050907053307061b020123040201050a2102040b070c0902190302070201051303142a13060b19 64
    0x138440c0000303042c02940003040c0e03c0c0c9040c00645c190380c1020b0200800d41c000d0018086603001c1081080904400c40c0503880c00a001020b06040c14100302c00300312903c0c1c0e400e01194501000a6000700e0941d0015001d01008802501a05d44000001d684c201040d50560a1005201001002052520465004032440280d01854044101c06039410030300210f145955410249116010b0100404441d48101d400003581c259501500c2e0082d90703000c03c1e940050b9500c0d4511200c2c050100402c170b414072641820b41205103015400281a40b0a06c5264030030061200c81c0c1303885100030414094002c0e4911035065494907126503282c81c0a4010300020755a8101d0030000190845a0f4400c5603241402082210a45c045201040d0007942c407242c401c03810402c040200c41110700a05a0714009188100e0b4012080b000c6001850300d0081c0d8020703601d0344d400c0341c0c1d40c10004126807081030042e80c64044c1c0c0c00c0b6941000000d20070300200708507030005244000c00101403140f1a80221104018a1242caa00b203558 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 754465296 1250 754464046 754464059
    0x308070f0906050912010e06010f03140601120f0c03080c01230702030403120e130e0d030b0f040b120a080301060f0201060803041a16060209040b030606031203040314040f0f 76
    0x601e0340344100400300ea8108505005410000000c1d200b0352031420001c0345c829041940140b030080240d010101940c40d0103c18000c00c1030b1004030404c0a0002001040e895041c0b0480b15250f00807103000070200030410482c20f04000710b20303800100441d00003100c41c0e21003002402c100d018207012070700141045000d03c14016050204c52040d8014601c507801541000d056994008100d00c2c1c44000e5828061004044c0c2165910f140005c001c81d220349001007641610355256502d0b2038100f20520047c18140984650952101c0e4400060405c0490b0049070004010b0040741200125002d51403041c05150784c05014001814021412180c0d60364840ca05000ca00d030049007200c0725070040e01001d1704200002c200c0241d0780350384450307222882801145805080e9020174901d0a401400b240e22907004a01401d0502d45441364100009041d8054600e40c600800066201c42c5406004c03080520040045002c1c180310781642080084048030241d610340e04c035101915030742001e06c10032981260001c00820301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 754466546 1250 754465296 754465307
    0x60a0f0b01080f06090c0d09060903091202331818010315050712020a030f0b0f13020f070b040b1b0703170402150d0518070f03080a0e0d0308070f 64
    0x18403c50b01c814500d5071100010003404940180990400070b1040c4964a9003404501c01c4009481c460207000688154030b140281c0340300c3d0789505c03240d6003142e00c0c03400c44050303183d2044038242c440800c2e550b0781c0100301e2030820808030403101c0321401d1210008204625044490410303089460703422501131560100e00018800c140d8000d010090121403102c2a444155103030b500140d400c16582c2c1070458488004108400407a0400001500040e881e41400362000b0309d41c0c480c2104403a0103681940d2045448000f28040a04070700d5103401d1940e00150070250070384400251040f4030303802801d2074000d0406051003134490ba401d4906d50225044590085418882c035000c4a00165164540d00c40030115400a50f0b55510002c0062b0b0300480780b9408000e182510f00300401d4202820000014241031038840303405108404640131140d688048002e0004043d4030308810200ea50204001780d80384c0d60040112020030000d0085900800c0c10b0000c1c0c0105070b00044040e109440c6651110340c0b030a40910102c90 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 754467796 1250 754466546 754466551
    0x50c0f01020309030a031a12010c140a020304031502090a0b04031a1e07110601180513020a15110a1101030506100906181508190239060a0f0b0108 64
    0xe013a40204500030079070740650449040c1c40b070745001252240d59070300c01080452504c040c00b0ba60513552800060071864200c0001080c072441601e1003801e02c10f8055003e9540c4c41240409030901940d44260100b000071034040f01c44607600070346400c662680d0341000b8274454000d4042200c008010009001703440c4403420307101d40325001040f84110740c1c00116031581706a0718050210000c01c0741c500e5007002a03034020030a090091980070514424001201001c50403540042c01c3c403034513070b41003800c04805a0384031240350044d50070b030707442c2030301c00b12260b200a0300c885545403044c503400e009001c1c0342c806121601101810348002a02c06101c965900d4040000300001c480801002c01c031008024044684104032a40444245030a039190840d160744900700c40d084d4802d1170038002070078401081904048140707003001c0302d800180f09604010b40300c88081c2c1c4443d41d103003141240c0d68000061200300610f6008081c0702c00e5450003601c0482c109041404080c0681c8004011720a050003e420307a0b65110381041071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 754469046 1250 754467796 754467811
    0x903030408070209060409120f14120c16060911011b0f230303090a0c0b0f0904020d020d020d051b040f030b0402040b033c0604030e031c050c0f010203 66
    0x3032030b2441a074208896110302034810394005684411001c005011201c0012500c001526000007070072070703a07070f0040c142c80440c20f03042d11008090210034500c0c035885070341d1600140c5e4984d04540b1900c15504040108080a80140046003021546170500c46469a0440100d5003a038034a424032400001c1442e024002d65401440b014240d030003200822a4a10f404509c03507d2600781b000f004203954030040c43d60b0410b0300d064142e1380100500100304054030a5003c020010781087c41d050401e016000081401103220480c05a0b800250300080080b8550484041035102d001c115121640040041d0040c40d04440103180041c0191400d241000c084003500d0840d4240a1403644943c00c40e62040c0f1002d03030180040f41c110f51110a2402107a5050100083d942181a85801d610801c203070100400c0c0c66482044805200055480500d00804622582d00c617416090001103191170601091034022003000041c05048200006060180c0c840000c00101582c1000c8032391917500481460300701c3c8400e44101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 754470296 1250 754469046 754469063
    0x909110402040b090d05070f0b091002060906011208040306051f2916080c0307050606010c1208040212010606020a0611040b09090c07051b010318050d0c050708010e01021209030304 79
    0x4450701d152141030040050b2280c002e80d220745236251a10402502550803584040c007001c281903c032418090f8024583c41420f00c000e00490a01010a584594041c001d002d6442d581500240a10000c01d045500540d4400d00411551600e00d614200c88a450b038034046104810240024203609000201e000b210030202c2600166945a01e0304049907021241c40c1c6007a2101e0844000402e10b00700181c84071040c0d25024680d44c1d6000e18103035041ca640244014103010700351710500b011034185600c45814060a04090407a500e81e0300000d03216a440c00300d01c40440d03003480408103080754042224406a40720b10f03414404050300d504d0406460143c0d000e407081c501000e02034000e42d0328005051070f811501880045140c0b661035194070341000c03c00c13aa82c0700c90407948050030300036503498440e02c0ca0303045000640c501c41c038003559a03d075103500712408450f0400210440c00b9041c040107100c4a4014481217000b002080549013402d030107500402805400201b0040001c0c840c0100070045a103d80c0d40b16030031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 754471546 1250 754470296 754470307
    0x4030f08060909060c0a09090c0507031202120a0203093a02120f090d150203070e062a010609090c05030d1704020607081603030617030f1209160909110402040b 70
    0x5da50441d0010140c45081084200d00080c1550487c4110382c6089903658440b81e454074103050103850144034500c0795190502c10441c0c400c0342c401c140c0d042070300300c000e018015035662902942c4601e000d902c3c40c103503403030009001c141900c002003414218a603966081d00c0c3c6400e040300800d059840e10821801c400c0f040c0410804031030003083c080000e1045c140001c2004030a485680c07240201c0300b80341c0c440d07442c030560f0010134089015042152154418800c03035681c5c1c0703071580221852590812615034602440a43c240041259a00703420200140803080001c105200c403030704140e186883c462140030700a00642060060041c8118540c103041a05070b00c2d8889a910707281c2c02d02141c1e6020b02001da42e81407042c8500d00c81c2d096203541032072409003e5035005c40d00784c2c00e00007002c0c42ca000198440b44180c0c010441030021840f110123071102d0940c24424800655a800409070a001c65041c40348040b41c0e240a021031159004c0d4020007070b05000c1c500340e00d078191305101400220311aa00806880500a000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 754472796 1250 754471546 754471561
    0x1c111504020109030f050c040b040902220e030a2106030201021513060204062105060f04110f0f0d0b010305040816170307110f150610030e0604030f0806090906 70
    0x64164125106161401e00e5950325100c0c4000006049021110364100c0c580d07068440c5824016040180c1e807c231010030508140f540007a040104006401c0c01079000c18a07100b0075107800d64032105900c010304003901d503581c441100052108250422840c2c106280b00c241002a0010748589404d0704d5042c0c0007011003606d289104458018020030080c00d107001402290001050380c00a000140606e8071185007000e08020a40602c2c00c1c41a4881e41c1c0f40d01d04000c010503582c0f500060446e0690a6500140d4016052403c111a11450141c1089645c0000c0c05c1d048102c8544024090040500000c000b00c840d0000114196407041c2c0d00a040118140300e01c0c802044110950300b0032600c6050003c01004441710070310010380088420b080414001207103040841d00607c040c90680845002918100c40d0030800303c411901e0142020b03008050b15044201014040e80c00300c001050000101c51881c5450704e40207054904442c4444002031511000c02c1080c20102290b40c0900b0500e07001c0c01c03c590b41c402 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 754474046 1250 754472796 754472833
    0x4060b090a1214030a0305010e090f10020705212a1f2c3f1204210c1502030604091a041b0f0303030908070b091c11 51
    0x80c015651183e610340010402401007000740b0b464202030b2808191507141c08003c010411005020b50710fa50041c2c0c3c407000995034046101e2403c2244440e0050b102c004506107141b0344003050b002410946155185103150b2810700d0050082ba40e00071004110306110032041440744480f18010104a50005c1c031650005a4030300701265801c2c11500700040d0720240030001c2036600d0b0040c1b540e0440d010003107580010140060112201001c00a503a0701e14508014041d02020108480300c01035040c43c562240c02040c031715008503052502d18a6070030050341450304000303000040540b17603e60b040c0a4071854032541c500688900c0d0301a034000300d10000c000c4801c015003000e035000800f003e40c0b055a4100750307400030320b0b114a0310340004c803400102c0c1c4051406282510900310f5542c00c02c04072400381d520410407008016100030603207a05240200320995641340c002c0315400358031001802c06080c4001c000c0c0d0201f00203480080000c46030940c6000328544002a58251249908400ca82c3c000400e580700d01d05901 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 754475296 1250 754474046 754474079
    0x10e1e0703054501060f1e080d0e0109060e06070b0a0204050639030403030c0c090c0f030b0103050c2d131a0405100f0c050f010b04060b090a 62
    0x20700300d040415a00000d607804a90440b4030090744201552028000d8081410039840580f00c4030004c1000900b040894064203150307201304003000444402000d02101c078510114002c00c180400c072081c01c1301c2220081c010030074a0310a20300065809200280c007501c65582d2480c0d81c100a44654a03080140d04d440300c84140c0100b60b500283e070204800112902d07405d004004016111600010640c0c607010074000b0140410303c0301208c4d006000400015000100865040301d900d0304010107021031528000d86001c8090b0f100520030fa02d006801d00380c49030485403210f98800301c4c3d6010040b0380c0544005500321401a5400b0161500900142e40e0a9000c4a070203c4040c108004111101250316024449070384260308003c03100541c07010030851510381c02510b1300d80400e800010342c242424040401d010440f503540540400c1200c1d698403022a0145000490712074000e81078840081490145601030045a01014000c500d800030004118280d9019a441c100000307200c1c40246103071044031601014030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 754476546 1250 754475296 754475311
    0xb0f070e060706060e07170108030c03160501150e180f120f04080703060209030d0c030206071d190617010510030c020709150e010603050402131802090f010e1e070305 73
    0x803411302003042c144444102d0b10880349980e45880710302100010a10700c1e001030b0f21000c1250310502c001d4008d54404801c3e95000303001002c03803070440c9055080540c05803116541010744214015400b00b8202c190040003480745581c141c56040401c0050b41e816521449075255035600c0c3c001c030f9011300d5554940c20080462a00364490b290400352500d5206061094980c0200c9969900059002c0281001d11141032181c040342411440803245880c00f03502c6800082c102d038101703c4c01450307084107030690581c414022503015015095401c0901c034401d81c0500727540a400007090301c840415000500c00c0c850a816100041d09030919065175400035006850000c10303400035401031041c0403800044a20504402c28440d00c0030420305403a040c0761200b10a0181c21010405080c1001c10000d62110040303994505c02c000000900c4440c22401030f02c18584410009510000c0c0350140b0103c092350070b6003641178401000300d8008603100c129581075030b402891752403600d24080b200080c83c43e5000c1d0b40300d03030f910042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 754477796 1250 754476546 754476551
    0x60403050a0201021209160f030f0209180d0c0b06100c02041d0a0c0603051605120402062104060b100c03030506040213030f0c0608060a03020d11060c07030b0f070e060706 75
    0xd2044848181d40d2003190342c0740d0710f640f0112400c080c47c16a540114002c2001c1c0b06249035090460702c0303c40c42d48811031030280c041c0c40c42c0c00125008151052400070740c03468080c107440354400d10600c020040300e1030602c1613810720302d94004100c03640781040c0c0c241d4111050342c54500c0008401e60900c405000410050f00000440801080348000c05200c41e0342d030148210b03000b0400c0303424140d0240464102a18201102e900c500142030740a402038200c8804089100481c400c0f41c0d2a440001c2d528405c6c3c100c82c0521102e0600030b09403407250102c0d1140654424002445840c5038801402111010401c003240050120354040c0d02282c001d81c07021340c0029000c0c001611701b40031181c0e85941070840c1d900c00c5544004041041080c0308608251002030259450a050300307003840400036242852070701010f841880c40c0c00007801081401002c0301000c0740c014000c19103482d0326210302038071000c0d20710040d81d02c5003510380041e680c2da4840d0050741c410f031950b481c0c5c044819828001d0001d207405c440801c50f65140e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 754479046 1250 754477796 754477807
    0x8031519210b010e07090608010b0406030e0f010c030603050c06070209070815030303011205060603010e0d0e0402070b040c170c0d0611120c090f03030c150601120c1d030a0302060403050a020102 85
    0x358544040b80c0a003040140442c0c00d0b04118030020f100074203591042c401c1145c83d80042c40340c1c4054500b100c040b51038514000c10f09a84a0608904080418030b00c14010340ca8105401c04603074041e0419070481c1e011b203054410028140041c0311241c401e5403402581712a141000440ba103000e0000f19821610f01c00a01c10301981442c0840e146a00a0704410400600d1b40c200c9030030031004108465100000350004e000b6141c4400241c0e0340e41160811704020710140240600c2c0686a641c1a40d1445810440081d03003400d142c1844034004540b1b000381d0320304070042441401113032000245800e04480162607210404580d0310340c0f03001043d051841d4500f0010800c940036120144c070162501a04003090303503d680340e8101c070801002c03200c41c2e00198003035001407101101490f00410400c900071064015034410b5a10880103c45801c40c0c035000d04941440c0450f20020203500c040091004c0007c41d1401d4640b0710140c00b01651004200341c000c005900440000e40000d106101a00350160580005070404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 754480296 1250 754479046 754479053
    0x80f01121506060302090916090302120115170708030a14030403090801290a0302060d0b0f060a05090a06080613110c01060314071706070f0e0406030803151921 70
    0x86040d43d00c14000039401040c2c1e0a00c501d0906074941c0c00503401c12064407007110418010340300c07100c01c0c40080e11608406d04000812102900011200c1c415102ea4000d4281c490480082075026001411100c0c8108980412008070000450f903000c1d0075a2220b050040d4080103080c096400248218108806000f0004590f9400d0184810005400c0210360a804883c100c1110704121000c4d100c1c824083d1480130005030b1203d8084a5a1011800010502c410303c2c1e004184000d1814070700c1038011000081c03e613441c80d4800c1c0549581d02080750380002050b507680044a0260703040e500b00d9804910003c04502c1c4101c2c2c0d600030101c400c204040d55052070460305050342190200e03401901c0c190440180c0c010058014802d50f00170388000c1d0303c1344a0b25905070307900c02d0b541c0d4070091069017440400b1070501c5105018003079002c20540000d200b8020340b030b103919101229400035200144251030074900c0ca01c80307141110306c0e00a8004000c8000541c0c51803c0e800109404020248900e000940306405011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 754481546 1250 754480296 754480301
    0x6240314040809101d01080919150e062205100f0921081b0c0105010b0a110708251205010207050d030b010801171606180501080f011215 60
    0x280d02510380b160300c0d00d02d21010f00070b2410f02d4540900411403640000381c1025155034542d10a00400e06c4e0410701a55810121490000406407030b52951130088a01020004c00c5052400d02c4001d09400707111084484416640e00c0e40181c60040100e0020144a404d072542c46890425483c000d20881c1c58078402105c52004641e05420608490b680324071141040c007408521001e440c5c011130300711180d081e0300f0520041000c4000780001551b4a810300c0c4c0c0315103c51014058905020070100204a1543c4d80c02480f10507510010b15000404c654003200082e1038004600201240c3d00c3c01c0141810700c40070070a0303508a0724034000d61103800e00c24480c007190030781c040d00420f820039100d140010390b25101810102e1414401c44802000c060a2100d1003400c4d90f070010001c0c2c115206181100769008043c0062818488126100c0141420312080000c1a60740102c400c1001258290076100142d103401c0110b41c00402100c25451020300c160040201181528005d26801d0090190106001c0c2d40c9000b10203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 754482796 1250 754481546 754481551
    0x50405031611010e09100306090213230105010e090a0b01110f0c0a05061305150712020109033c030207020306090a031707020a1101020106091104030b01060306240314 73
    0x402d555101d60309407055070441c54089041c00304566544040c41c20000380d0359030030f40a0200804041d1140707600c00454484510781c0c0c0120600d042c06200044075a10741100d483c10034003070b440708074541400026081d400390340e4640558134090702e500826500c10301c02601400b8650703c428100049400c0840c8c41d04010300c41d103820151500098504000c070b240400c2000341c0182c0020b0722405040090503010344a0740d240d48c0840c0c1c010b980103110460340c011080c50724041c4000c05005441e4042c540412240e041d03000e081d03450b100fa11400d00c60b400c45544000441d00d5524110310b040321110300d0000c200c0700b902499124504601d0b000d490481c0ea58080307400c0c52030648050120303511940489080680043d0b4000700e020020200c40010b240110000750fa034074840c203001d0b254800c82c240640c0141d100b900108050310345e180701441044100044034201d5800343c481502c24480140000c40c085100380204802c507045412000540c1c141901c00c100c0d10800d9180303100c14940d8990303c1c4075503c1c2d03d5008039403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 754484046 1250 754482796 754482803
    0x11202010f030c02071a03180708030d0c1b06140c13050118050a060f0207060309080306130e032b0c02060402100c150603050d1107120516030f021c02010509040504050316 75
    0x80c0c60b0b041c454042040310350030350456440e50b00440327400e000040b80002900c4240c44849004140d0a42000f001d4410803014400c4400c2010700503030036402e0181681283c0541050cc031180301d9156a0080d48800c14003400e111025540403400c3c04000643c81500b5220b01c0080700003110617440d54440014103c6262644808045208a280d113036403a0b405102c940c000b01450304051002d800b00341e5071031002d880001c0865106010680030080d0100031588104019880b8104880e503540c42079540d85000304a190301d00a101c00c04003038202c00c01c0064001da007074094080e0018015a1119420001c0d80c20322000f00314200604a181c040229540241c281480d650184d0300040c6107007182003040c00c0107144020391003408a9180090400300b00041c10808440321002c040c1e900c0c0c0042e00c0d110303080c8907250709002c44049015001106010005402e038801034804c56a115402d103c0d0f1816001400300b0000c0030b80032036018410100d142c00c0503004144d22900c241c05407031030407a0a01c2c020051003803007813058 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 754485296 1250 754484046 754484099
    0x409020906040801021305120a0c03230a0308010f1d070509010c0614010314010219050d18050d030b0a1a13030b04050601030204150e0103170702060d050f011202010f030c0207 77
    0x10445400c2c0000382046101102000d40b143c3c89e0503454a0802000c0c51000401d20321017509003086080032018620007c100b41f1007034903e2a015424000d00400c401c4c01440b00e9034000400c001040003100c03204130780c556808011011140e80f01c26040d030741034100405680c103018021108000003055841984c0704041225155030503541141403145050400c440074000c16131041000b4620003006464a481602007440e040b503444013140e11249c094034102c20103800c2c018000c0c8a460401401083c040d00b2109195802c118828045041280141103840340c1d1484050b5803942000d1018000c1c000d02e444416041cde00031030144d603543e40c810824000c0b1402d460036041200103100710300e828020400b40300079003200807a20354104042c0e01c1400070184070003002c0012240400d101d8100150964a105800410032500c03603526000a030041c02d411102448003512190011401c40d203100748100107282c06035924480e004802c003080d07008061b0074406005502c28080c0003e40702c04032000460b14060360b900c18 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 754486546 1250 754485296 754485299
    0x3080406020c0402030705090424181107021315050a090f14090c270907080c010c080a08060d0c120201030e0105070804080f13060905091b04090209060408010213 71
    0x282400750002c40c040c412401001480900b65205003500c400e5103003107c1c00141e80b010f0402d4140e0f580d20405074503c081d0090718001400c0c890441004100b0034440d1410320003a0740a014404640c070810000035844000740300c142c42c1c0c2c5030156010140d00604111100391050711400019550400756101c0405142c807005c032090b000e03034540200014203000c10301c0340c1d0b81e03814440c82c1a5215a04441054068185900000d003503102c0805c01030b030301c003001580002c894241020542d44541503805580b095214003052007200f540316840725403d040c2c00000c51030074080c0304403044400040c0940788070341c09400303255402c0115200300f400d40d0040103003c0d1400508182440094155507200c210803103ea45088100b103442c40d00300c80d41ca5800b0740e0004805585d8a0001005440360241194109a02c071a004020070255082107520702a80c508a804005554908060780400c6031800c1c440031117920188130400c62811250003408600500522450610b52036480c0103089801c044410880c00c1d003400c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 754487796 1250 754486546 754486559
    0x5040603150f090b2802040815090d020c010503150406091e05060901090c09080106080309090a0b010e060a0e0d0f170304031707090521190203151f030804 68
    0x7480b0600801182e0500c0703c1451074031180f00d500340041111141280d90020004c4044c401a1703480d843c0740320000c00f1900c0fa80c032581e11941d10988024440590110100072848802c0c0004030810124a10b40c000d149003001000115140e41000d07000c50200c8102e581150310b00d54031401040b01500441c40001907806542400189203010001050340c818a403600344a200e4481e0000181034801945000c80e502ca00b1a600322820f49950b4041e4159502e41070f40840d01100100041c1000c1c0011a020003564480c10303001000c5a40c1c0404a0380440c410b104840039605040300070700a004c0301030411403404044000854099114280c04545e0756249042c52020050421074851840750800c10381401c52074650f40290004500440e04403180c010f0f24001017400380b0410710040500005856504030304003611030841880860b41a1540078099235160304050601d01440d0301c0c03000e400800820128281080d00008294050140185e6590031490410f11a1003011407000451265600503601e915040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 754489046 1250 754487796 754487801
    0x9070603271b05220209060919090c030c2f1608070f0503190516060e1e0d060e01021317010606020a03081f030501150e0f0403050301060503100504060315 68
    0x400007071003200416000000074858616130b00031a0320340c810040c3e0740e003012000030b0210f0007510b402d1344c3d0245080c40c8003080c554059032400c00702c9289150a10074003001201c160180c50580005d03200284150145d42c078403030007054002d58031074504039000d803c3c0350a10390b0380340c204000020845030410750610708005810042284600501c4c024048080d02400e02d000682c90384a20741d00301004c2641600303a00e080c48000c1c03001003803900e02d0054180d41540c2d6481c015242d04807014220b80b007a6008440369640700c101c2404421501401080d0750308a0341031f50381d842d008004422a08001799401e00c000d00b1004055a90036010340000072180240400c800803250a49591b90454401c5400c944103000009402c0003003e80c00250800943d00700c040850048400000c00d540301034455806d059880301142c0c80003070341805484442060000558071880900c035806800d0b20001c1c0005c0080004008040c8a24080c41e00705217207018030846140d440d00060706442d001c0d0030580c0e8805081509003100407207031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 754490296 1250 754489046 754489049
    0x1020a020c18070806060a140307080402040506180a110c06150901060906020c0d020112050a02180904050303130302072c0702010b030c190e0411041409070603271b 72
    0x211180c0c8a854800001400103002400711030158030082001f4502c14040d0072200700b5203031104101a00c91501e0800101120425031302a80110326020200d07180741860030f48181c002d800c090400c10b203604c8140d0410001c1c40700e444a00000c0c101840009200c000c14000d049c010152000c405a0b10041002000204030044c1e102a06021004800b048401d0f000b2401520b1210304a4084648014034001a80c48030030001100214918003400c11066041540c090038620740c84074410704151111105111480c80140c1d006401e640c010310010300c84105074104027444500c28410b0300c070300542da1000140c91407016503100d200c0e40340c1c0301e130022103140041a000343d018400d440248024074680340400c1d2940203501030140540240200d1801043c600660300c00100090140c00500d482d1a0030481c0303490310100c1c00248a40c0c1045609441c0d40c500e0000b803406400c07584041d01c00d01d8a05001600140701402c0006502c1d100200c014104c50071150181d510355000f80515082c03100521641c200603100c0b03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 754491546 1250 754490296 754490329
    0x3060f0108040c0e040f12032007020d14010204080307140c3129041401380a110f030a0f0806040603060207030c03020105060a181d01020a020c 63
    0x94401c200103d444564088112640801000c80320703259805c0001c5824210507000c2c051402d40000c00110700e9043d40008120078818040c030b80d068020f414031f030303071180b06130768010394402811126032000c00c0d0710085106141140307000061401e82e9404241d800c2d070708801d00580b82860790f184480c0e510307901407000f80c1c4002c400b01c41e0514461031a10143c86080f0010a44d4040c0806103440b1204005480c0e110004503080c5d414101200c40e881d10114881800c0800f0881c011030820280040d55000c0e4076105040c1e0307454088400c070480f00740d00342298070040200204c6c02e403808820300f0100e0340a038074010b100e00d800d29980c0500d0340042c5106030386080b4a10245002a61081040380d0405d50300c00341c08500341314586010320003500c0f10030015026254541014085610001e000010144c1194014000d00d10a40003031141782e65070010004942c00600c2880c201c0210071383d1600c1c500701264004101d04403075013201c0b10710b501003581031822a0845140e44001d40c1c841d0001c64482e00e40601520010500c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 754492796 1250 754491546 754491557
    0x1303030e070e01060c030201090203190314090d02010f020712110f01020c1e010905151b1908030601051c020405040e011503060e0307050109080a110114060618030f0303060f01 77
    0xb0700389424840c1001407064900b00308181e11a801098402e42020304600e400404441101d82031b042030400b1410340c050224003041c0240e00140ba5074003810141c81001d24014000c02200d140b580054070200c0d5040520001c5016040012031040030307840c1a00c07111402034180c84c0e04040e00c401445140c11203000e5041c103552049100b6282690ba1442c1328690740340e000ae1a050004080b001a0b914007074a40056034405050148036000860110207001ca00701125000107100c20071080007900d6101240c00c41001602840401c804549100011138101c04189055840c0c05071508080c00072680750280304014a800184c10480d61034940070b191441c900c91402007288100440c07420b00a14454840101156100c1d007100c1d0b0407035014815500c1843d041030080c00200070a207064100ca42c8001c05150214071070810980c01032505104064150089140b0f0f200da6403590000c0019941080000d074078400114030502855403024050303c040700b0440401507440f41032034820811031600401d8110304021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 754494046 1250 754492796 754492799
    0xc120f07121b02062101080f01060515120714070f050105010501030c21020f07050109021e010c11030309182e090e151e01080708030a1d091303030e07 66
    0x80742c0703082800503a0407522183e440c50701840c190050701caa0001d24450407120b4000049100000c5001a1440e10000003040318944400810100f440c1c64001e044204c1401e00c010780099001109998214245003030490311340030608940c4105500119046071480c88400a4000300300f024019140544003d0805012168420900508007404122110701009414140c5151225150b0485010361040007000d66140780a0800901070078079607608a0284403401102c4081241c00721580c0f4407840140c1d84c98400c3c441c1c546072100042030041405a050004200d903d0b41a60f64005600300200040e08900c030a1038210300c0781c0d40c800d04585440d11400640c000014040c007848110f201035503100c040004030005505991407034104800c0720301d00c484004509010700c90070740b0680300705006200005000300d41e03220711001e6224100d521a81026034001e012581c62140151400e2008003005203e0003039816034140010510b01d0207031600394480344040c500100341a41400307040b0080c00114001d00c9c007503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 754495296 1250 754494046 754494077
    0x14010803090409110301050f01030b06030a020f0108041a190e0102130612240e09010902062502031014070c0503040312030e1c030c030e070302060c120f0712 69
    0x28840c4151a9204a41e954030383c0c2c041205034040301102280141c001c00880c40c1002c0030f42c859150a0109a66245070308000607606d190014403003204a5000d000c03c6c10398070f00c032401918546d00252040300d84503240014490011106240c0902c00d162003140800e40160390f5140c0c00c1100c4202c0540d0209034010081c3c0003008413034000c41812101d25160200000e10b004a0030b8004000b103400041030704001c0c0c140b1a1661000000e01403c0d01d4150140b00880e469421016089030400413000390009000d000400030054615011400321000641040d000c0d880c5500213030400700c00c0b0240800c0940d0f10b03011101c0e80302c241580c565102c03049040050100015458580d60f0340a01d1100a00340c403a0141d00f201441d201c0c0c0c0102950302c0000e01198007101c101c8524030329061998450000003494241c0342103026109005040103114030f000036240351030075038003407051940c0560910001403040e0758200c050f00071100c004142c00c44030644800c0d1140414a00845941824003030002008407200d1401c815 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 754496402 1106 754495296 754495303
    0x3120c0a120b010c1401060308120f1806160306050409030915030b060d0c14030f0603070f24021905061515040e060402070c03050a0303140108 63
    0x115031200d400305045807202d6164a0025a810040d4004170346821078105041d40e00f400080b810646a0322000f285900c0641000420040744080094000c80b8000c00c6800c0791404401801c5245030500a40d9207840182c400341048643c881520f4a450080e4406002008003a10502c080e982c1401c002c0d01002c200c1c410010504003003039120482501c42e108281c40100014005820460500d41200c011b2520180c01e0042c42841810003007019505000b8600c941c5c0300d030000c0502440d20300c0905081c240e469210200040d510003007804104d0600075025000b0580c10104c01080d85c12000482c60440c202e00090045807456502a00380880800c103541300c0c000380310707002030421001014840141c05840da8090791000500c01440f1102c61203e156411500041025003044150784510348446116401100c4070750103094070348201a01809460701441d0700491000c020342c03601e541c40c0d84 = true := by decide +kernel

theorem cover : BRFrame.Cov 754316546 754496402 := by
  have h0 := BRFrame.cov_init 754316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 754316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 754316546 ≤ n) (h2 : n < 754496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
