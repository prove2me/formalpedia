-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0954
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:28:34.51695+00:00
-- url     : https://prove2.me/submissions/8ecad529-d081-45e7-9a41-216bf0958726

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 171402877 ≤ n < 171582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 171404127 1250 171402877 171402911
    0x8090c090705030915270f100603031101050708010905070c0212070303030c090614161415060a0b070213020f03130203061b0901030c050d06030807020a1205060c0309010f 75
    0x40704080140070340310110b428690300c10005070103040d54060310504140d01c844400c090081c005001d200c10b10513847d003c08014001d0103030700c0341d551001c0c40000302d207407a41c2009800c0d012075110b680000c0c0d141c00108032680e0717001120b460540d105450001340d00d9981f0542500c8948803104040c0d070081101382c00c01c4018900054805c181e138802da17810301100b1204007043e2208d4101703000d65000300d0b031400f90546990b0128005048100b400102c0390807807050a880e001c540300d03081c615045c080d4010300805041030407180000354200100f5548141910b10b0040c021902d4020b11000a01c2061144145c80342c1c041e598050341c944031904000981d4074103009014540e00d00c1c0403a4201d0080c02128001030060350102442c0da540b286030040349160500c480011801070510380b0800c1c0a000c420b100d60b0412a40d00d1090001451013a8031070703036440344640100800030441da80072480d07030b030010482c00c000550b01041c041e40112450040340d07102e88581302c90034058076401402060403850943c40d00c0d040700c445 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 171405377 1250 171404127 171404131
    0x2120708041703030105060d09021f1115090d030b0a052722060b0d060e0709051005011b06180605040303050603012702010c0506010e0603070806060a0608090c09070503 74
    0x9400442c5500700c6048076a5102d000c2441480d0344454284003607081c4e4142c98001541142c030017800d48203418000c3e01100f841c00240146000002c2c0ca8220320400c07a0410460800800800280841189850000196103015001c510000c1544030741120380c50f40c81d1a80003130003410004014242410414400781d8055140e09100b40e50040d040c401720744880341a0a4000342c3d51807600c0580c0c50002291508001342c803041c5803a58110710086800f0000c41e07609e01c9041020990701028005107403402048078203982c0c02038542441c000c910801007020f40e811a40783c05141501c00841030507403026051400040c2030803130882c620703510402c0600c400c0055070350200d40700d0362098500300314940b80d100c181804ca415502104403004400100c00b1030008070104240c04aa20501d0b0181c24080e0317a654a50900b0000c0e13110312054035003001801010300d4103009000107410748500620701c51500000084620b42e05110308401d01543c54045181c80c4d0b404c0c0034160611501410f40c503041d04054030010025801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 171406627 1250 171405377 171405389
    0x151401080a06050108041101020307020d051c080c07030e0102030408030c060105130203062d130b10050a020304090209040e03070302060402190302010806120a05070602030307020d09050102060411010212070804 92
    0x610400100700022a1151900b500c0060703642c0e00e199038032a0384504403042042c48807415480705006640050ba076a00780740c1c0a09204501820407038201d80d000c1c03090243c003408100280092101000380f102940701c01d95480b1394141c03030084056a44c20740140e05511494002a1060100003112840d0381400100b0f1412580301340c5042103600455810081240402e461042c0c0c4500803508030210600b10301c6034045c0700041101554002d100c0d000000c2c1120101480309a07100d40c840c1c111807010715020900e01c0c00540759007031180c940b451041000352207204601030002c0807980030501c038005881350f0340006500314008084a036034800700d04001c0c1d03403000102c800b00e11640d00d4010240e1620354401d40841200d9068491038041e4503a038007004240d459441565025101d0348000d1000300b0410040e00d40103158a402a56503802d14480c02410070301181501810720015840400103a680001c0940d4000d0304289243c288100c01c400403803e100008008038010038003c00c0c001c0034440418010411079203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 171407877 1250 171406627 171406637
    0x22051e0c1c020408210d0212060a0602030a0807030e030f030a0506091f030f020409020402042402060106080609091606020d02100c0804080c01021204240e120a03151401 74
    0xe03403045a2001d0303220380d019503605600a0b030400c205c00302030800c201c180084140f031000d042c00210301494003280c001104440707000224500b4001282040c4103018003500d240e101440c80c0081c0e04101030000740f4060950420503548062010f4440300502c150791417180c8841c00540d40e8140b0003000c402030304c01070b29100c1c4144450350100e00000b18404102c4000010107a86132440761460301d50050150b0b000d64103903003040e101c1000c407005a07618070050003d44448103906c00940400c100080341d00c00360002c514107652010b0f005110a503005076450740d00c104100c4100e04690b40e140d8000341041c040b21082c000031588184041601900400da01c01a450141c0c2107528181101d81e8007800e84502c61a204082900580480c0104251500070f100c40c0076850005842d011224450682e00101101d007521480a100411003400025041d42c206448c10030358140071714845041c4043d1603031030b0418139551282000071452481c3d4080d401210b0b200e981484501c481b43d65886400c0305003843c1460140c009a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 171409127 1250 171407877 171407917
    0xd14041e02010f0e030f010e0601060906030e030304200405070809160b16050316050a03030f0b100503090f0f030a08090d0903110a05030a0309030b010522051e0c 71
    0x38104401211545405a4484001e81094030007a6400140001540d400d8040d1420034981030b07500740075a440005644c0300603c000d40c904040100701031095044081014101540000050000820f0f07a802c40c3d00200600802c0070b074021038a0180080305003154000b802e20040110140e00308840902ca09800400d68078000d4281404810940312401106500e034008d0143e0800050641040002d040c40340b41100d00d014a1400b000c13070908009a022542075000741713005820554140110110000c050509200c0300421000003070310f02c1e411071030600800c40080009200000e04102c180d071404410801c1c2c40c0e1612500340b039941c0b03a03401000540041901c2c0800b0030280303e4000b07801640c081c543c3e690503e00d0307400e66075004a0f42c0b01c2002800e42c0030041080c0850b4030b035401d01c1060907181c8070340c0381c11a2040c610700c0e050540100591003a0f1180a200a000d0002c9640b4101c0d1900c00c46c0b250750005d40c40d5502c000c170b0705211940c801c001116098560810400c541e0301c0740203254030740d80385100d500c2e52 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 171410377 1250 171409127 171409163
    0x408180a050d0f11030c060717040305060c04050f10020c0910090903050409150806070809011401150207090c02030405060304050106090c0203130e0103020a05091b0d0902150a140c030d1404 83
    0x15111a0299903001f0a04201d404042800c00035000d2040303400f11006840c06650340c8410746000e1003070710390558950300040c042004d440d08002b42d080e0120b0035503030341104025402020391544803200744680501041c3c030000c0c402000e400b455002411902e40100050700ca81e0800070f2140d0132074000c00a4003460001100543c60f0006c105208840c020001015999030300541103c0c400006440030301c0c65034940d01c40c03820142d0b600412902819803c030b410203180d000a05d000707207445925849480014501080041000d0b40401101c007170710000e651480c0d580c5c5032464928010300641c1e01c107505451815204404d003580c04801412420913020a080f4801c1e00c80c3c1003070058100c2071200a5100701e131440708010504094140d0750b40000440b0b4900c40e01d8054042420080d480824000c5102c0da07038004000462500c80c20a69260004000303090401d0b0341d108000e09080029089404c044401003206502c20f1020402c0380c82d14030444070244085070582030741a1041c1030a4030112001c907903449048600c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 171411627 1250 171410377 171410383
    0x90e090606221d0706121a060a020115060816081005010f1101060e04230a0b04020301090b090303090f12090f030307060204060315060507031215030f0f0b070203030408180a050d0f1103 81
    0x20514030102c0040d001d0f000341d400c000c41c270f6114030350200540d52901c1c205c1d001001388200d66801041e40c3d884e00882807525156840d072001c40345002c48244000c4005000080c243e155904050b0f403020708010080007100e5506540c040e113102d54600ad80d40c00c04001042100642c02079074040c40c40f5406611494001030100f8001c0314481d000030391180d0020036134902044c3c10503001a00240007034000120117083c0c1c0c44040d03002c1c20860b42c2c482c41d54000800c0c019440c00800c201d1441c0c581c0b1502504030650142e4580d001c51280b003e45038401d1107040c0102500e540d080c8200c1d140e941d4041d50031940c561780c07010098042c213400340310b41ca440400c6180c0012400c0c080d20031a107a46900d60b6400e0030110301c0c1c041c1c2100900031b900c003401c0c54081041000c80000c0e000c17480007401600550510780300464515006801c4407000303050300110b4006006000000d0100e01c180c0e5028401c01c000b24040c82043d0700412040e11140c0c0c043ca074040141d10743c84042c409a590340381031160280c4402048440040305242e6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 171412877 1250 171411627 171411641
    0xd0e0f0d021c081308030907080607021902090c0408030301080d09050604060516080c0f0a120c0f0f03022a01020601140a0902130803030403090e090606221d070612 72
    0x440310009629607003082e0310035120603922041101481160003115125120550400c4031030f8a402d50041d0b40070700505408004030f541c80803003840100000e0180064200303001e03200140080c0110a0300d4085004801008292009402481d0481c0d446c1d40e51850100c1da200c0c841c1070000301140154001240c6424890300700c8080d10403c2d1126842c00c0401d003031400100d081c22405603a0584148400e84200109020480012260030700400e40840a41800440b400106070f260303040c04184174800c000200c0514014040c1a0001000d0680d580760742801c3e41080181d40200303a903590805266800c9080075031412056000a81c221030080c0e80b5402205508028421520b611441e070260802c500099a0001c0401c04a15509512a155034560032440d54000391070803400b0030406001031003014282e0381800d074444054030080a9134180440490307500e580c101c101c014008200041056608139941200c21030710b00c3c0c00c101d4590245440111a121440d074007071800064405007080300d5600701802000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 171414127 1250 171412877 171412903
    0xf110405013002060d0c030605060a0e060d020c0d08011e050105030a02090406090f0203061305040b160c0f030f09060503040203191502040e07171003170d0e0f0d02 72
    0x1541510030b040c078000c00d5007040542080704040c0c0c00105001a140c880c040d041000341c1c2d01c2c01261540f510301c009000e0700c072560005c90041605000c00b210381944094080a500d50517502e040c0d484540e0344d1130030017a1044aa144101d413145000101c1010350240c005412200c07070f80b038882c05811920000810b86151841001e0000320188040343c00c90f4090b40c001c0600c02c10042001a0041c0e880810070180c03244202d10310704c91580072040140070f007408a03101d4010f20b07921008011034036103640e9603610b092018100e51081004800c407041a00d010f11946412240c0121203c150307a650703817500a15009242490b100000c2c9a6000020954002c1041d2030040d94010050040480842e440f0714240d01010000d41e1402d43e1800b1aa61460081c4000c0000c0c015003145050300e0319024002412002000368500758a42d04401040f0b00e4220b816166000c0d00c3d84541c11040c2c48001402c01c8180f4001c3c24002c000f401e05e002d10340c00d00d0f0b400c0014080150504a81a1100da81038444140d0b1a40c516805007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 171415377 1250 171414127 171414149
    0xf021603031202040e0a05060418030206040f020406051e030c01090b07021e10030603050c06181002011d070503010b06030f040303050705040f030503070b0c18060906090301090f11040501 82
    0x50000901a604510b0b500d210001d00600b016615a0000d003001c4044e07030142402956581030001e981060700895100d0b000501c00c80000c01403c2e81c00a588100044c4050454081c081964045580c1c9800c840c0080100030702c01094403860000d41030000f00c08000d040c2c820b1040e00c031035000c0c650184040700c0c1202e0000c0c00311400e08000d40c0074000445038040303c0e91407054440081010a660380fa81600c40b4180d155000540c2c2400c42c5082884c14000c0d0b1561032080a043c0a919200795040f039034000090b406990710180c92286080c243e02403d0700d00c1600b07118640c11030400100d1a0005400e000b120000c6000380441d000e054207110b040d2100fa0703000344442d49030070700250119000c4d40005420241504d001850b0954410000400800c250400c50b282c2d04001091814000c0c030701c008542000e411a00146851480611401c075600d64410441c020400429103410315030758501030702c82014015009201c0006280380c4501030040c0b0340012a5501c08022802109080910070715068801903007031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 171416627 1250 171415377 171415379
    0x1110c0105071e0506010e011a040b030c0a0e151201090b010e010f0905090a09030e030c0307060309170c0d020d110712110d0510060603090507060c0c0f150f0216 71
    0x2081c0c01c020031015400b01c450191034203c400034508002c428000c14042406100a504003004c4400c0b001c00d616002603035481c103020030b202000c1100c040f2030b00400300342c00313060b03950107a01d109480c68020150200d9010030303081a01c40c0081490790060001004147c0d0017005c9a0b00c4030000d004403500c0171041c90006042c8054114994000d00d00101001410b0074042640c941d41c5002845459080303d91003a40c0351245030290400d81c01c21403000c00d0500c01c5019280e80b258000101340c2c0c4200d54401c450400d6260540c020134410192044101d100c101c0031580d5807030300d646c55101d94880c1c00001e5000144110742c7d140320540c0c410141c145803204c025000d02205031401000c24441c1c3c400034010380d035928120808404503503403100b11172061803248000d0b00e01d80600803200c40490b807480e40030000749410040780600050002c250841901e0050401410880e5a0b041c9450080303065040f4120500b5a8480030581501c0100b002d42c40901c04e58804e000da91100c04e0485e1140d142c10b9403c0d1298500100c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 171417877 1250 171416627 171416633
    0x40c080f01060305041e050a140a02031002030a0b0402070515090328030608030a0e0909210310030507170c060405100e011202040f210506070c0f0b0c0901110c010507 73
    0x40759030040c0c01b5811b8001c4d10820400295a600700d080001c0358150f215106160411003141d11075150186550302400c084c08187d000702c1d403158215010140c01c2c90340000000e106c0c007a41c1e400049100009442103407030700743c14030304996505040c0c00c21082c412111000074600c403000100707c400c18541c0d40940d60345d0801c413020620303200d00036820b0035007850b840d4040807420b1b500802c0580107a40440c3e48150201d03c0150274001c2c9040040c084204541007807140f00d5250000101408400100c039004695990342d2500741c0c2c0408260780c000500c107004200c0001a0a00040c029814410700344090700c851403400c208000c1d83d84a0384c401c240d0007a24440c1952807560249011507d4940c040c1001c00c8200075240c080802ca900603001440c100e84144810b001301191101800444a01e000a40381079030525119140c1c2c8039001040d000400c134148100c9000c100540241c010520fa00203107403203290070100014129900000001400100e00081c4a11020800248a9850481a1200c91038124191 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 171419127 1250 171417877 171417881
    0xa05010810020f0d021c0b090112031101110408100b0301181113050123060f040e180d0f110d0e040902060903030f040314060f13060f1505040c080f010603 68
    0x8900a030340c0c3c500500c48858140e00a0008282c103c821450302048004120080b9080b83c1906440d10b0090345d0781c0f00140100f1080a040d00c000540505203031303003000e59021190380942500c0700d070349080b0600410001195030000030032800c150745010040c01284a03c0d02032600300c4100e038008000c4071450305150350116140c035188c03400407040984092100009441d40b0000c2c0d96080c2e0150200390441c840c040051441e008242c15803500c00c40b14175240c14091020384d0700b0350085000301c030644880341001c070300c402a0800502e0421000300c0151105012101d00c0500202c040d003602c01c0c0421440c2c0a800003840e004640c03100c1050807520380300040b000341c0c1c00388001024404e2040f60400c004101c44541075504201401c0c031400500000d503522820752a1403660038001d000c15440d150711903410700044113202c0d60803e03449140d81c102481c5812007030a001c3c0241010102d203842e9540b0300070243d0310804c0710f43c110005540c0d0955081c440112450000c031404182202d8102c2011040300041c04010f100e5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 171420377 1250 171419127 171419137
    0xc0604062007150906020106050603041106190903030f050309071e0506040f150c050d080a02070213090c060f0e040c0504150906030b040e0a120207150210050a0501081002 75
    0x181840752111861a00c05803801495400070310020021003d80c0559640c0200c400010304846e20090108603d00f01c041030280c040039100411403040450040300700d0b100d40c01901ca072200317100c0303454454240d01c440281c69100340b40000c1e000105200c034020b44044c02141203171301400040000345a02c0346009004108801d941c0c0c4507803c0320600c0480000d0b50350352440a80b0140c00c58500c0416007510b402003000404178024a40c00038400000c1c100340209102240f001d218005904281e2503a6032a40060002807140300740095200900820003000c051441c1d11400c04070303100b044e08010b103e40b47c03a4103495496840140c0e0000a0510300104003506050300544003001c01030400f42d00345910382701c195941151104101d80050920581006510361600550a0b20b24050700c0802050b000c2c0c450041e21201d8403d4098400d40300014610100340c42001000c0080c1000000120107411007100203407201c410b614880c400310b007840040340c1290058400e42c0d049170003241c000c103021285401c02a010b5080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 171421627 1250 171420377 171420407
    0xa150e16030e0708030d05090601080a1704030b0115030e0309030d030b240307030605100c02211e0f06070806090a0e06010b031f0807140307051201021b0c060406 71
    0x2644004012039a081100a000c4c008080c040e54071030b641031110b0801c80c1e0000301104500c1d84244010400e004000c07031841025030300a03402441c5240c8040303a0343c400348a42c1c0d2008106110507c00083c0b0301980310080340f551041540d050200008001125549029107195260f054002584c88c200e01c0340264843c03131281c0c002a01c00c48015862030240c18840d542c401c0e040b404c07804000100300341c00b82d042c420b180142c8012941801c0c8010504001003440456100090107841a05000c14030304003a142003285145030344044038040071180c0c00211014a0802110499200d02c8400d0390500b038011405910030401035480040980e14802040b24400d0064990303040555200b2086c844c9840a100d014044d0005005c0242e803401d000721004040003022000d09a0382c01a024140080c410204007030007103039400c4408010810040c00000d0814120f0f600607580040c491545540022041d000b50550302e000b81708648003502c10144071900d442649440b150b0004041106100a60003007030148a1404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 171422877 1250 171421627 171421631
    0xc181707050306090102090909030705030a0503070c02040e07061205010e0c091503010603050115170a0b0604080a06050a0e0601060e10030b2806090e060d0819080a150e1603 76
    0x680c0d14082403d00000f40c4100d5180c0e500001e560980f401c2078600b13141c0250144000307500d4401c550311001d440340201041001005000000b00300014403904c04110207640040041000c480300c112140d95804091052a000c40d070007001d8403186140e184241412541c0c00d400008035651045560b030140c4d0311480b04190704c030120050300d030104c0301c046020f540a040c8545000800754109401728500e80a554291030800c8a050343c4440729582c03004505400080402c00030501149440c0018038a00490f00114414071440000c08207008143e0840c501030b40d28440c04000d0100c285e10306541360002401044041612425100001d08140740030009401a628001580e940e030400003402040140071316100f441d100030804a200302c80b202030b0200030b241038103280b107030b4524000601d5120040144014030406544500e9004d000382c4c0d40c112400d000030245040382c0342c540600d0180070440242e90882c021842d180e007400e0131200502d20301c000d079107050392540346076541c04000303408401d40c0d000c44e1f1082503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 171424127 1250 171422877 171422879
    0x308070606230102120306010f08060f030d0302130f030206041211060301121119050d08041707091404082706040b070201030f270503120c0703030c181707 68
    0xb0103185011041200c00e24800c406030242500081c94034420100c060880b500c1001800803907a003050390141c880e049800d0500b003550f5103c000a441011506070150540200302d145050554158000d0000b028002000090b403621940303e010107255034080250408003c2105008900c24100d000b1100c0d8440e26440c2010f55000c0040394040e0800e078480f40c1e050004114172001c000800b43d800d16114419a041058400c41e051901d039001c0c42841003034010040440c0d65000d1210041c01c4801a2001c058902e14003c0700d0500301c0d9480110b031081c400c0b028540f0580c20740c0456040c45450050350801c0d4200c1c208403200010800301159103003091805c0650355400540303034559501400090070321500e0b40d81c44550300d00016045d03d00f1001c84041b03091030705500640700b05409a0449482c0f404070075150880c0c0da0752030300314598410504c044991101110401201da043d00005048651103603034144102408044262403107014064041440d076500320f01800f842240c0e10012000d4640041120407071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 171425377 1250 171424127 171424139
    0xc0e0a09050d05030712090b010b090102030d090b07020f0102130b2503031e02120714070b01031b09020c07031511040b030103050609070605091c051014070504030c0308070606 77
    0x10b01c0e405402804518044204030b00981c0041018031071500000b018001c10b0f06070760750007954800500407443c0f42d0101045159041c0d10800c19100110500c2c10100003183d0182000c0d042104103c50000051203030f000c0d01640c540301030094442415186a42d1100d0605100c078564454121200000341401d00d100c10180ca03986905241783c4240c06520300042c3d5000912864440e007400b0056050307098010407a803000080503281e4994802c1c0300d4601017244203044c44200c030700761040500180c03c0c203071424008014402c0e40d2000158009000015802d0700d50303500e2480041c1e0260021840c042d130000c0301d0420109400da1100700718003641420001c0d003640d426282401603085034200858a80d800300049c820400d08000a80c0c0180085008000882c981000188284141d00b01680540069403072002c2480100001000c00c5070321030709550b00301f500d21804400901e032080c40c2c10702c03080700840441e41543c0100308031802c3e030790464000d0f2103050541e10750a0640e840710200300c0c0c1c41c966610b400038035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 171426627 1250 171425377 171425383
    0x31305060a0e010e01050c16090509010207020102030d050703090f03050a0f0c0b130503041509050a090209030304030f0204060302060c0f06060916081009090309090e0303060a26030d0b01020601120c0e0a0905 91
    0x10010302d148e500b601c0d0300b403400345c0e01141c100421844a50384100841c0d00580c0c1c0000a540e02c0e020919008101e0b40d480181c11000350149403001040b403400e0321314410416400c03030301410010255a403045040035900d8011034181c4500c100162013070a85501042d640d40b44482c150100c20302600031203180a6170340d1520001403401034503210000f902d50780c1c00c0c001c0d80340c111803983c02071003400425030801401e0706c0000d03103034440ca1000403c00e0581300600c00031900d40760000380c000c54000703025079202c1c2d0358403012a49854480c0c0c0b617120203000710000214a4900b009055001d40344001314a10b410349201e20640340500301401c515200042824001006005401020314151081d0742e8420050b162105000540d4150803800740160001d104218841c1c4034001041c00721040154010384501007003541c0084210031a0510b850340c000061010820100390f0002020740400380d0803070340326070fa98040c1d890410401000c02030101d007900004112070400d03d54103d030019440c1c440061041654ad5425107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 171427877 1250 171426627 171426643
    0x218011202031207110111010b03010519140c0a180f0611280f0204150605040513060302030319090b03040b07080703090f0b0c0d050405031305060a0e010e01050c 71
    0x945208a0305000e01181401d0004440e8600a92102414030640f42e9640144642c1c03040703445e04010450030440300e6184250000090000f018000b00440c2c02c12100d101d0200c1140340300803156a04100c1511001040b0115040c400c00098429504100081404031160302200c03440074038900000d400030031072504a074001c3c40144001c0d180d11500c000c50103c0070342410440c808c260a001c0206420180c00c51a5244407a542c586c00a415130400c41c02e1b20001d8000c0090300145180c071201c00c41701090403a08800188250b5100b1154103101c405081d40c10301c103658103400000d400d40c10074004c1c07150b00aa030342c19603402c185490424042141d2a02020101c0303030801c403020f0780c03003010340b5040c000c0b1683c100044a030091003e00e01484110150380754450b440d84000b000070084952440042c0060700c6030ba0685440218882c1c0520082c00c041c1021560b0350881e001282480500300000102450400112500328800d606c903c50080c046400544521120540103410300200f000195100070003403000340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 171429127 1250 171427877 171427889
    0x70509060327030a0e131b0305040201090b13090908040305030a0302030708160203030f09070f0306140907031703090319030f111e0306060c030c0601230604050d021801 74
    0x2846a020280302c46260710403020280c410b03030f00100b00403410190302013540e0311181425103098030800d02e10f05900c00202203002030003d2103c070700c24041803042c2c0d240c1c00c4180103a0007644e03910795150300c80d41c2901a034403030f40c9c02800c21202402030130003881d12a500700d841c816000e1b031000380c14965284c50380d5045034012050074002948c0041006041500004615000381c10030b81403c0307580c908003001039038a10010701042c1c0030b80c4e28400000c0d0150401c0150102400c1070150320302c2d04035034034a40710010b0846c035124044104416000603054941c0050000110b82d006003021460303141c2510b1440c2698000361104401c3d0004000c07040d0083e0380000941008003980d41c00203910865944003208542c5100300d544c06120381045240c84954541c5c4800a02c40110b1040039541d0300c1d6000010f50500c154001e10300389001c04224843d801030007081403070484001400390000a40c1900307003036030901d000595981d84134005210501c81e60400e6403d0f0340700c80344050202160a6282c01c0c85000c100e030241c0c000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 171430377 1250 171429127 171429151
    0x312010803070317061507050c040c020703061a010c030c050f0d080109140108030a030b0102070e01030f170a05070803152e020613030c02031002040f06030e03090a030303050705090603 81
    0x2001090340c00b0003407400444c588002a03529041201c005420481c100d00240c401d6100403443c01d09010044c0a000038502005204102c4e00800001c0030b9140c0490744402c2c5c0f400c5162504540c0e400703042021600342d804050750365240716a840e66094421440924041d6040d03c5603a40034144510200100345006240351140520780d0314001c84402603031002d11401e0544c0401030010024181d002040e02c2084602e41008591115191f004034640302450f8000da18005401c0000030a108407440417901d021300507541d034030a845060f0f102e40b0591142c1441d410005008001c02c1d40400c040c1300207140c002e00c400b07410710012152140090011858240c000d0301c1c03c42d050b482800007070074092405034640d00740d001030030b07892074044651a4891045000174042c40f085c0d540d007508564061140b01c039025082c200c00c41d1990346032048104110030500030304000c685020446001d50390300205a03405000018802c500e140d0840c1d50803405440064003010501c8800e200009143e5500005148900c0c020645 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 171431627 1250 171430377 171430387
    0xa14031903050402131509021608041d0601110705010507080904021903050a1415010e211e06190f060b070203010f0902101d040504050c0f03010c0e010309050312010803 74
    0x100040c0c00c1882e45a80d44661503c40c51100006c072a0013500d0495240401c01611a00129100102c14003000002014201d000902049124650702213002c1306847c0c0c440040303d40d40ba4001560907141c040d041c07445560107028200030a610500c010400310b4410340280c0d06141202010a00b41e1b00034540000c1e0240d00340e031036141c2555241c07140320b41c000d101d150140030404044281c6d0b000c00c01c0c05460910028159603840031135034000c0c0c1a801c04101d015101c008241c0f12143c1480d4285100c9071a10124043c0441e510448105050a03854001054000d000340b070b2241c40750f51004884240c07200b01041d84604442e07905d440540b04c0c040040c00c100e00d030300e541c40700d55104250845150410350107141d807818060f0409a22007a080303440c5814141424036030050661040c0740b0385495040175a0b8820304240800040100206000200e09170540b00010039401c000205401d9030100150300740050704070700400110b503102e9080140020f010b48180c0785000c07290b0002d15900302e006d80210740a40e1000031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 171432877 1250 171431627 171431629
    0xa0f0f060e06090703020a05090d020f030601121407050f01050702040905030c0307031e09050607060204050a03111c030806011b0c14030d050f042d030507090b010e030a14031903050402 81
    0xd0f605502400c50310b002c514100b03d070345000d00b26004503804640140c0c003041c0b0070021900ca00b008003801c17840040c21104150781d104d0080c506840e00000c1151619000844106030150010340308003540c0d4020f15070800308590308011101500f01920590384136841f131203404c0c0854001d1006061000e1424091a41c401490074042d00c80c84404048174000b548500038003402c82e80c4102c01000b59041100d21a03529182420200085e0059400050744600860000810440c0c00d603041040c0420a484002c2e16541800380c0c18800fa51a40d4080c021510400005545602c2400705030306004081092046200440c1c840d218049126040b407400d0071442d030600d1855150030002405088814500640340c940c00040302a00c602841c4a084800205805031004078503101d883c0703541c40300c1032000290071140c1d6414501d946851610909103094507200e80703a0b0b21944500200c003603041c0040c000f4a00c0d08016514031a00e4540c0030503201303945c0000c0c058042d11854503a80e40c00507a80310f40d4017064030304140c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 171434127 1250 171432877 171432889
    0x1090b01170c030601080c090403270f090203040c09110409140106020c030712061107050a0b06010305010b161e08071b06030e100c02121615140a0f0f060e06 69
    0x9070341d1a101e0303131040c03004104500c0006000180548251100c012503200c80c5410750750020002840712a5481030105414003080c00c421860840e010a4000200103940b50b9851080b44416a03002d0040f4101031424441444280c1104443c0110b80c8070b01403a00359107612120031901c017443c10044501842004000840d410012105440e2084000d0521186810100d040c448a00d00700101207a8a5103000306000e04403000351070210390403c0603178041050345d181405598400b242c02c0b070f01203454034002158694010041d19091190200054820003072900d40d424040c0304540d0101c0a500b242c0403000c0082e0111001c0c00b14148603a104a0085911a4041d40c00b185141c122500f05442d1111005200400003558002850031401c000f5005400e040202d003001500300805000110000304207084010301034000307c0c41402070300d09584a261200d03000c420f0b510f8035070028140046c50340c0490800786d0940e000b0a0321200e1600d0009000f41d410803000c040c4d42c80d5522010b018071000c010403000e42404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 171435377 1250 171434127 171434143
    0x52505040f0b030a3201020703110708100e03130e010312050a08012304050c091306150f0e030106030b0603010f0902090c07020a0801051003120804080a03050901090b0117 75
    0x215034144079012410b00403d65a00040f9805881003810000300c5c451000c48004000013048640440098802039001c0103011354007401080300020184600206065400b00b045000e5883c80c41c040c3c1501414010454040d0005440080c1c01d40400c1004840c2c15464a03420700042200400411780c940c074500742001002201c4000400340641084491041c644c414034142c103507044e091a40b82960340b44029038006881050301d194006140c0418444954070180180880010413140300f518000120340583c01c0d100207204080c00426846101802d19000703854810310300c0110710b80fa00490310309200203420b4521a0f402901d9002e80c60040c424941002e0281488902c62200c041c0300c07800003540420401000141200c916580c04184c0b00300710756400e21640c008002c1c4800074841420100007400180780c0700d12086031400202d03018209294042c0c1b465900c900e42180c1602d0601603042e4064014180050040d141075586050a100050299a0b2103018003112000c4c842042c400c640043d00e00b40a0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 171436627 1250 171435377 171435401
    0x302041e05030d02030a05030c0304030203070203010921020a150c02030d110306011715061b2505100e1912110103050105030307080d0902031501030f150e03090d05250504 75
    0x400c0000d1b09500350050f0890750880222030009aa903a1035040890450044042c001c0d455401e20320260240072800c540607840030030913400414030010f4440242c0c1d444002540050501801400590071040e0a0b4040d00c60100d10f0300540b40341c403038000490800c50381d2590722078407642c1c0f011007840345d01c3d41d0000030300b2402c0500e4500c2c1030317403030424038540c000c0601421001441504001141005406103001c8881c072a001031084403e1818078442c407044428140c3d0240c04a9080c4120004482c50320385001100480380b07031545842d44034924141300b034001c803605d100c1000d061710f100300040c440f1408090817201d40c0951003941007544d182c070006090b00c3c01a80724500c01e0703000380500808113600c0001c4492406001c2800a0000c0c094808a070806c03880c2d80501d5104074501c0000001c1c01200c288050708144208801480001c20018880403205800c25400c041d074418803040340c00d4103181112922007401082228034100714102e1084820070502c0020040004211303017040356080034000c504000130 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 171437877 1250 171436627 171436633
    0x702150a020708011a0102210d020403080301031406061f02030f04031a06060901020c042a090e1608040b0711030a03091716033b0909010c080a09030302041e05030d02 73
    0x240170b0700004e60380c0c440700d100c02c0700c400782c0c14848a1816000d60111410b0114003007007551941e540381069190fa80091000792074a0803800451f5035286030115a052003500010403443c2081c1c285861440c0c1d41d520041c880055210400580b81c0d8540414064002984207084603083e44501310408400d042002d80894040c80040c014800707541c0c1c0106d43c031440c0000c01c0d40c0000b5154540030410400110b4600c1c1880e0045c140e030610700c11145c0c0710071420207845c42040b40b8081d613100c07034441c010f1b9075011018000000b010304c000f050000c2c0c0400541d0780c1003605485e0045541240424180c115407240c2050404265200c803240304100d140345500c10381c5040c02e0156424900e03146010b0101420510b00142005010b000100480340b209082d0f08c0026000a201440401c140c221a01030b9410381f100d05108840483c00190341002c14011003850f1040c0d44e80c0e003159600c44524610250400010480c01e040d0240404a00c1103485a014000b900452022980c0189464181801c04107031010002c1150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 171439127 1250 171437877 171437921
    0x2f0414010810020c0304030f060905060c040f05010f030e07080615030f070512070f0305060f180d050a020a14030d150f061b12031d07080606060702150a02070801 71
    0x801040310440070200c0d02e000350703662000041880c114822a0002080f40c0070059212003800b4041d4085944030b0300c211308842e00364868034441c0740703039004a10909a070044003078418031803548141b40480c00703000c841c180402c00001e07501c40a420513116402444080c3d01180c00c00440c002c56044c0094280c20a401030903803a080542200c0e10342169000703003409003400032003124400c0300421030700c001000d00017070350b84d4100d0b245c0c5130181e01c801040e201020310404036408540c82c8c642140300d002c0800c2c030f544024480204980ea055070aa003045020000791701848404a012841c103400603031000340804013455941c5415060101166521412000c1051030700d00c0c07d100d01c2d0356130406c2c507043d11501c0c2404d013402c000348520403a81094040b801030001007540c40d050350850f0950803880520340c03030016150002040007000c81c4d84a001b4072a500c000e500000100c1c0b89400c010009003200b40c0007400c91055540107100e1180c0340e81c0140d000b0030069004038020043c00070300784a4a54891122000c0890308 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 171440377 1250 171439127 171439139
    0x20a091a150c15101203120f1107020907090510031b030204120b041b180e06070c0209060d06020406050304060501120b0103080a0306080708030a080c030f040b042f041401 75
    0xc0d094140710344a14541da8008903200b4003821034608020071080c01e07220303041700592500412107a000212481d4046c20115501e00f190500e0241150381100941443c3c1004842c1d0200300401030041c08041c244044844c0101d00c40c4c0321403074014074095541d00c0104201c0d4100c41e054840d075206020080c00c02d4410310050184018417080140200d82120b07000c60356448a05005400781c401c0d0b80074086032540702400080701d604030500c106080700041300402a112007003905a4444100719424000198095881c00c01890b1080c94203410840242003400221300715640e05049074082d402071008102e001c810081045a44c0c09024050100380176016095001030380d52046415041c0070060441d0300200d92004a54030940c0803400a0110b1070440f00e0b199501c400c890b480364001d2502c42c00248401d40052480d880150413a405003800c2c405940150340c5d03644401700e0f40080903000300c500d80301c0314142013081c03c0a402004004421030030186070f00d00ca0713074040000312840c101040091404220040100c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 171441627 1250 171440377 171440383
    0x30909010b03150d06020c070e070e0907080a0f0f060605040e01090b030a110d0b100609090b030c010e060d060b120f040b040303050612030d02030106020607020a050c0d020a091a150c 80
    0x20003c02955286885200d40c44e1140103405254005149032040c6880090108404021b15000e60669200c1c1c2610980c070405000d03130a03008a9000011480071030203d180c1203169804580d002e0072030200001d02c41d410a54190594155a11000004101040c01d0001c1c003043c111030b5004220050301006807580d40c5000c01e4455a003150082c4c50000b016030040704a0305d8900c00010302e942e002e404d010703151519045010303041c070b0340303008901c0011450303c0f01260f11090341c8104c3d06400001030041554034040d00044030351000e10102503411802c140002084401d090055801904c0301c42d405d26144c214420390a03940b07800c0100072054204420f42400041900000e680740c0003074046c5000b1074150303a84004a1105c501c41e003500d85981c40001250020020142c1c0914181c034080d0382030b81c0460315140c100301da803015440000b4049810070805c8100c0c1c1c0c9070003d8249002ca20180c0b0700c210881c0e840d1210003c8528441c1c0201b041c00ea04401140580b41c00e9003051522035400e01e42030b0a00035260b0031070b55 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 171442877 1250 171441627 171441661
    0x3040f0b040e181507050408010c091707061d062a011505010507110406120f0c05030601030305030c071b0303020109050d03110d020c15180601140d0318090c02030909010b03 76
    0x180b105400c13400325295a1081d0308440141c0078501c002c2c040ea81030148001d0111160348200039200b080055180307114400498406c046071450341d54000400d80d0030020034254038030035030724070b91058041100c18a00303420000e04004056581c0d0720aa0301c03c12a890442c02c0d80c81c40d00c2074847c407899895003880144c0e00038050b03c41c510f8002c0d1286180c0307808540800c004103410b4210809418041d4214020014200301c4c80c1a024400c0e01d00000700781d0744400740365584100b03010040210303c2c00e10000b5900441a009800030078021104003a008050f000307035880c061419003059006035128400c410511008210300901600b1f240b6041016a41e4000010914054001008000ea40018210880400821110000780190303102880203080c1160718600303100395410303218800d0250500025034001200c45081422034003501c1601c41100fa0790341202d41017405442190740c4202d061300130610717810074803407240a0002500103503540d050700c0d0204094154164422200b42d1780030002c0002040e24a801c4070b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 171444127 1250 171442877 171442903
    0x6040b01060309050c030106150e0916050c010b0a0f030b090c0901050f0d0b070e10080c0703030e0114070206180610060f0c0b10060e0301050609070e0303040f0b040e18 74
    0x7641d01054508641040c40c0089416410f43c08c03c0c2000c1000b042c0b425003e801c207003040e1250158504120248035403400111000101e2809241c510b074074060042c00207242c5007400e00000202145a0070000321141003d401844845c0112078003842001408000c054102d03a2041c028944000001c2c001404110b05001d240d00900d0f0f1003581c7c80c0e070744c1c58441c84050381c00c2e44039036140300700e143c0b04500502450060302124410849181110100c034040e078801806104280a11403030180d4548040d006840c010712500481e6585014036810910036040c5640914981c0e40604064244101d89803e990580702e024011034120703105028000b10b0a0784540202c0b41581404003412201310b4007620241c480c0d5002401c031402c0c8104115a1201e4442c99400380e410a480c2c04808a0800d81030600300c80d41103c102e03404c851240003141c0c986011f078070150132850005044171b15091f150201500b400c5840d0740200b4004101040a020049106400503070008400c84015801c08083c104250346942080c151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 171445377 1250 171444127 171444131
    0x6010302010e0102210306010201061a22030501090b04140c0105030123100e0418020f04051b0d090209011703180a270f060503100b030309030a03020a031106040b010603 74
    0x21607a134024085250340d800f00b807552407400300b448034001c220342d441281c0003030045d40381c44004240c002102292513400710a400403c1e04002203c1480075501c9a403090001c0070040510002000400c240075a00e4a6031094200d0001e605191405000c40070329200208400c1d041808405020703640103080d241115110070464101400d0306041c0030b1151160090141c224054040d1016081e41050344415840c005807003c0001d050030f041c40008146580b00001d501c03c8000505005524007500001d401c400764205042d0340e403d6000a40c0410340c00032103122949600e40c0034030341c1546095602580107210f2040c0700c1000c040511603403512481440d0000044030140d00c40c0c040c1c191148019603025100c00892200c0207105070081042c03007220361a00034402c60610740d43c020071510b10302614049903000341c02046000120b04661000e024195405a0507210511451000b690304025061105001e60054145140c090070010070740c02501500c40096804801800001143d00e2401c41c1160081c4ca00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 171446627 1250 171445377 171445397
    0x11030903120a29120f0601081501120305071a0112050610030506220b010603050a1a0a05061e07060204050a0603050606090103090206070c0311030d0306030206030f1906030308180109050601030201 86
    0x1401c000701038420558103104171014520201300c0051814181d030340d2002241c90240c411010240008000d004030400210b0503681c070030000c0d000304060058680f0500d0303100d10609181016082ca07802c2603118401c50855600700000b40881485021f800101160401540c20308688600e9a120406880b036641407800b05585640e40301000660301a01d079200c020300e80d4559450000401402080d00c1c2c85c0c5496281110910030500d441041d081d07900c0c070140c20400001c1c07030141006859080301c0959240810307040c034505581042c4500909003a441900700685407030a0000380484000781d81c110f00185440c0806210813552880d05940e0810424079000c1008034061010034854000d40000030060011550080100986840030b680b202d00103130115030012040d01802c07403e5590b1840040e41001d41000402c04034222403d090b40d1107401840347c801101c0691404800321080f41c0d00a400040c81c01050000c0b80c10140e4040074500e01c03501c000d0015070302681f95140c40e0035042c44001d043c0622041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 171447877 1250 171446627 171446629
    0x1331d0c0f0a020c0a061803140f0f030403171e0d020705100605040b0f0d110301061809150618091e0309050a08030307020706050a0311030903120a29 66
    0x4581d40c0c24402460a9160214160041c1d981c900710911240300d10407410001c210381c1c1c171402d07407010424001180341c18101d1840d01c8503020445241e01ca0f00301c0d40200204011581001c010010300d000d40440115600e03807940c20626000d40780340701c1c0c541c2201010003061241c1c05c0d54107015400c0f9802d00b0402c82e070756541c00c0020b1000f071240c14401403440c040c1d42c0507080095160f40c401000c95009407818805a02008100700d4603822030b0214503408218581403c001c02d40c1151301d4120802e02500001300680c650300950452217100f10207040450b1259800790170080c5424003c03101d4101e904080c42068140b233002c001d00c66627014000e05141c2c1c0c40003258140402500d0764650005030740341130b02c081d50ba1404c00412615823405100d01520405e540042c0010000048134424400355018108190401c2c0c0b00321442d41c004800441050788810001c041c1d145803400941c0180481001155591481940b9004c560303c000d1254035400d140c28405040040390800b60060b50010708000208205410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 171449127 1250 171447877 171447901
    0x6150405010804060e0a1a0a0e010209030a030e0301060509011e0b09060d020702010c020402030a0917070c1214070b0a020c010212030c2b05040b0c130506070201020f01331d 76
    0x40068050300180c7c04610411514074071650151070b040380140142e4042c401028240d01c070b1b01003030708d4040c0d02244e003442c0400e1107040720f2030803100001d00100d403844e6540300080d24070030300307800a5a0070003880751360301c120940b0750016034014400c00c0c000f2801c12024100140081c0103607045612050b0300003985a0442e031080ea41e907403c1e00c1d8010030441d1a41040c180c003800405400c00116011224981c0749041c0309005030541d09070301c0e0b0050383c1889142c1880c06051080260302002c40f0506440c0000e080b44117824003418010f011891946d0f500d607072940c4002890101301e41e00c0750303040d0740088051420b0202100c08407944103081456160b5a10030240c611071001480412048001c440d00c10742076603140440e0001ea01542c011040001c0d2500c581c201c1d00000d1140700007030348140c2404001006603081c1031026260b07150050041d51000314032520103e095810100075110708454901c114002c9082d142c045001141d1469070140d45142000c003118040506e41300010507884942000680c08102c0d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 171450377 1250 171449127 171449143
    0x6010e04110a030503131215090305190c03030b1c0303021308010e01050108010506180a2705070609060306030305090909070314031312120e13110306150405010804060e 74
    0x1d0407070000c2c1c41d66030424588940101d5421140c20340c904000003032041141103004400c940240311340d0000c100820601c001000002e60803414040240b01c0056400c120301001d045000ca191280340300b1901314500103003100c0759256800c0c8603607514509400c82c0c015822640c4040e43e41801e0059843d10003105035124418030f503200c440c0700c0d820452161812003040d001541258041030090126440384000c208401500400358200c0c01078040001e81650103640140c4080c0c2c14038040b0507100d06d030b0b0030021326004122002c10343d080e0344503420070003420b540106100005c1882c3c0c40c0400a290079581c00910038410121414411340707d4401044d9540001e108542c01150302403002c40301014000d46881c0c40780c10610b0b60003000082c202e00041c00c80c100344070306410035038001440d00310303c881c220040e503603c508011150340201d01b85c0944883c0030344603c00c0c40e00000000040342d449282220410107a064500c002c007401010501040101f43d0b045002190499804040800d20b445500c0c9024609151 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 171451627 1250 171450377 171450379
    0x60c180902040306050c0901020312070c0803130309060206060f0906030f031308010c031107030c060b120c040e0d200a12090305010b0d02031e070e0a052706010e0411 73
    0x20055000400c0140c0e54002c01c2202e218541c20301c01a0ba0320f4060b008203000c0e80300d220740580c000b00a0000000003440c0d9180e40095541040c04204056850f6444c1c030740c00c216041414402d060702c1110a240e00b01481800402107803004040c549003c501103405201c180c814180181001000724146035400d0280b078140e02080400c0700e0315082441301451501c616845120300d07a52a021030710501e2072003130055003003040010340c00900d403110b80d50b000c5821154510058690590300c569104440d070700c0c204007460032140d4100814a00c002c0004100c1202e007800c0026455078407060240c4030f2190003031000c44800040d0071600009889084c4281c3c140442744030020000d064010642c0c1c0d00395000140a403da81c0980020003040907a40b0a20403180c103070000113176051f4004404244882002115201c080c0030314000e4403006a40c0b50441c0d4800036040d41c00f800190307240e01c2002030751052551480c0c169410013000c912050042d41e4030603100d00060141070180010380340000c050102107a001291210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 171452877 1250 171451627 171451667
    0x9010210020a02150c031b0d0f110d0609050103051504050a050304120308330a0e011202270a050a1803090519060203030a02130b030c09040f06030f060c 67
    0x1001c02c4000352100c9514001e0400c2c8a29a004540d00b00303102810703648035541c0c95000d804c2520120724095200d0300300112501c100c03900d0301c000351101c0455000700341d1000003502c0c1c490f48070040e010154003582c03400c2d040b0110b030320b25001c010000302d00001a600c0c440d01c0300101503c40c980b50743c00c0c19814180d010102170200d1000080020716948124619109180290340d42819a101e0354800c11448080074a482c4a03600303e045040f0030881a0603240d804900c0051640800381e641e8515403802300300983c0100f1081407081446011750800c20035078810100c40401c843e40b410605241d03001003d90203890b40368525174510001d03e20b2442a48102542d0307803418107540c2140907074071300140610160b0040724010b1011009201c138007010070412405031000768000d141995107175130300d00e4001d42040d9156038040684003000500c0030300e0000118020505071404564400b850010300041d100c40a20f201d2481d868440100003103010003100c5500d00d41e2281010170480c80c48601102c07418020302100c01e44507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 171454127 1250 171452877 171452887
    0x10b06031602010c1d040e1c32180409060212060f03010c020c0d08071b17070302010e010c0f23100902060a0f1404060e030c0301060b040b0901021002 66
    0x100840420910030207080d40240b009603a601411201ea84041780c021200100c49404a0110320f01500100d0074200d4060446650b00c200ca03881d0344080c4013290160300451410740e583c0e121207203402144d240300d141801c0c2c460700988007010350f0007a9200d0382d446038045031100312802046503030b950842084590015010340d225000000d00c141200f8041d240306202d0182d41c00c09010f1805c060113810f001b240b00781c001c4d19043c00004188a480c441c640700881e0300c3c010401100c00001e0803040e40704400310b083d105210196003040e4960060340791070000302c9078076440001c0c1040140e0740400c0c00000b200b400c2c07825070301659662803c4544190314400c02880322070802025660404003609490750b006102c001c94241d034003001ca80e58203d6030028400f941003101003180c00701c1d1a01680100400b1b082e5450400c82c0880e940982c0c2116820940111002035211075082e038881c9810001003900c51400c80013040305038608442088030b40300e01d1081c9041d4003004254036407035030f000780b0121101810b13401d000c0d560f030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 171455377 1250 171454127 171454141
    0x708031e040b0d0f200306060708070b0a1b0206010312030e100e0c0f04050c04050d1e0c09060b09010c12032415020303070203030601180503031605010515010507080a02010b0603 78
    0x1d0b04116074099240e901e00340031119403d046072003005e0400804168140740da19010144685c07580070350401c0c0c40c0340804011030000070b0283c1200d90720590501800003071001351429181d08800b0410202401c40d4040001480412445c401000c1600e000e4100083c0b1000d003c2c0b07031030f8140030a000400e44e50300c0c0741c034155200707401001c203060310904002c0b294102c0e400700c0343c0c0400c0210b50003540c4180d40c10b2000d0000f070102c0d0400c10107202c03040c2c0c001c42d0410b0004014039107486141c219044116410f25896000f00100320702405913001600c810350352030381000c1d407420000342001a500d101070700000e069000096080d00a6002064101c5128003112400c20042c0d03d80038004070501c0340c8904001c02d02c2410240f144040b056030700500380e5601540c038680b503031001140d0182c024a40d41603500c0c0713035103400925a5070420061030a200410700d00440c2c4062401c085084401c0100015a0802018500d080682e404002c48010541c48580c0c540c580c411824120300500c19071400c0364016000000b0301400c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 171456627 1250 171455377 171455381
    0x17060913120e2b020f040902060c030d0b0607022808070b09100203090a1707090903020105070e01110705131b090305070b040e160c17070c080708031e040b0d 69
    0x82084195030b00034044050610038500c52011000007007400c443c0b0011000189040030925240c000c00901c0400c1034804d82e0001516540681840007080d03000040a82c40c402003402210010f04040341c5036070500303003150045250203143c417014101c10141b0410341c2000b14444441c030000381c41c0080c105c43c42c1a847e1980c000b0141c3c809646180304a4114480c0c84203980b0001c11201c03030540103810450020b10b0300d00c2d041c1c2803048102210403140140000400c218006108240c643c078004d03800491203040440001c6c102c444e844588604200c54a02041607500c000118002191801c0c2c4003003404000100021000b40709030380288000900a501c6290115072000042050301c1c043d1066545555075541e0488051044d445200034004880b00024030b0540c40401c000000c182500f44841540c190b03641e0202910150007001e5889100401d586050220b003001d4600540b903031030002c0c00c4e05402c100b81103a883c02024407101e076a01440c910502c421810000b600c00400a00e680d9548501c007076428000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 171457877 1250 171456627 171456647
    0x140306040b3012070c050909150f010905060a0e011203020307061a090108070e0109020a0c060c180506121302192603091509031908030106020d1706091312 68
    0x2940700700603c0304039a0302c80b102111001944070000641061400d1b06100d0700c04e2009103250080e0280e0800d1000044500922502c655103201799200c45604080030711f4201c840283c102802078841aa00340000110f8003440750641c0e00720010711041408038501245035102e2840010407041c01c2000740d0021900c4622001d00d00041114003004507a02e44c801c00fa601c070b28602c1480007500c0100700400410403581d0090801c00b0440c0b401c4c1060030001c0e100c02c42921150b039242400a503541c0c0c24070f580c46402602e48400f500e03085030913520b0176035215041010f040e00038006500c0d035202a0784100c2103682d9010503240d03a036000900030f140717030707a80764024040d0b1000c1c1200d980c3d0414074000c004000c483c002c81215440f48005040e00d400408600181d072440d0850b00f1079035058801c01500e4480b0303040c86005001d00c948144600c0ba66581060343c001d050503030340c02e10102072103500020601aa0018225654001030a0f544043c481d034825042010070307001d2040161503059501241845154800c0b9401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 171459127 1250 171457877 171457969
    0x130611070605130b0c0304061d100b042906071509050d080903070b15030f0a050c030102040506070b0703060e0c0a0908070f06050c0a0203031306020d140306040b 71
    0x402d994031000c001c030214181e908010032a4954100040204003000080c0d60414098100003848006554040c00945080d0751142000d901550312200060700c11f00504409079016070782480f1844080845560800c1c00080640b0040c0c40c05a1254035030b1503400c06c0d100b22640084c3c00303c50301d078a881c030f01e44001c0c2560901611140600480ca200c41405402c003580038903421801540f50003855140d1881105001e402c06c5112145081500d02c190b400b009174070000c40c07565001d4117401e1590300d0880e1401015101ca02c3c041d0f40140010003550f41d17484180c40c22a5003002c40301c1190354231882d0840003001643c00c1408180d08080034000564a41c0010381410712187d150140060388a2130042d079905010710800f000b50509030000d101c0b447c460702c06441501258000c803480c0700500d9000900b560060050383c07107003c990310400c02130a98100302d1074000c400039040c103203440b00c90740c00349969601c00240158000c5440d400910916282d140700c003103503000764607005074070844404100c00307482103000c0c040c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 171460377 1250 171459127 171459131
    0x1080a0216121409010e040b040f2c0705150a02010906020406031a01080c18040b090117060a0204061b03180b090a0806090c102706090920031306110706 67
    0x605400c3c0d614112202484161904500c203103013541080050185850395a0308141c80d0b00b6008440071140c00380b00014422806118800780c80b0701603a0b0703182903245440998071303480400100800e88a05a20244031001090887d6842c90900c400342c0c05002c20342d0009000500c0014006606a41907001d800c008100c1c0c0da50080581c803003001100c102c00283c52a040c035141c10032039540d01c1c1224102c000c401840c050000708001d54120000703540f81b9000d03401002c03800c40801c1c50800e50581400515400202c00e8011410182400d1005041c5101c81419052481041d41c8000a1500030f5242d6040441800701c9405403603150845c40b0407540144a5190090390000400704d2a1003000c90042d00c24010400141120018842000318075440740c225003050100c00c180034000b5a1071101c0303290815021396002c12150345004d0300200207017141e0348a440598905114611b610050b04144401101443c02d000d4aa841c1c0003401510740034007180080505203484020b40c5503e5200025190483c051482 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 171461627 1250 171460377 171460397
    0x10f0609050d0209010509090f01061508060a14010f0306090c03060302030d0203072f0d060501081507080403140903070f38030c0d09060b1011030901080a021612 71
    0x511500c510102c100951059240303005002c076081080300e540d8003c0564040703604100a419006007111079582002c800710380050420700c3c078540c0180035a42c016405564806040e4500018009a5698840d60504001d64066418402c0d4440d8210001808542c0400c0200b440030801c0a8020440ca01c4100d00030701400301d0b640549030011048d1100385400040391840201c200041b03400201e8215407089a042c0c0c140d5500e034690b110400c0039801e203882120700140079410800850300e821842d48145900c3d10044042120117035014142a0b0050362600b0801201d9880001000040c01200a0320740c00d40305020700001c007441e107102c3c035804940c18034006205c0c1180a414404504800c0d1821540702026180d000c0c1c2c01a81c05001583d026005032500c600302a5000c4420003943e50b1400140c400c15107400641543c1e00c0c00344041a0707c590282445002d0394080c90600c0c0d16409540080d5040c0407074000024841c150f581c0445170030031500d02c641107894095241c05c07444001d102c40f00b07070000b84007004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 171462877 1250 171461627 171461629
    0x905010e06031005071b080f0f070605060901060507061805061003060f09083c0c010b10080a0903020f030f03070f09080a020607030e19051e090c0306010c0b010f060905 74
    0xc5082c0c020704031741e90349099003100305040340131005c10759000300c071710311820850301011940c0003000e40701445035401031a035030f0005814448103803040600745034411011100104a1280c01c5411a0b035466805800460f00c6000d03003640010120b0404c0d4050818081c070010403040240040e54042035903c601000c00c1300a5461000e94229090840002c0080000b0000e1842102038102201c0c0d65100ca4030b45203081c005209404000d001203d84103040e00c0c6400304801802c414203004420b2400c600380d03003100d05591200f100514801028041e0940c0036510300003c01854401d0203041100703d5404d00316540d9070043d1085040a0f401200c91100151003400b2112744148289011400c031580b000040c03070b941c1400e80800082c1e5018200840a1161400c00c012043d158450003845a0801c8002003200d545841c05101c011004410ba414000500909001595039069040e60700b02d805c5042c425225618100169003181244c2d50141400f0b001d03400008524909140850035101c003a07403040c602e666564 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 171464127 1250 171462877 171462881
    0x1b020703020a09110d020705030a080106030c0909050a0204030b0c0c0705030604050d0f0c02100305040b010b130e090f0a1410140601120f0204061205062e090905010e060310 76
    0x102009511100d000000c1007a4103080e0040b68680c1810020940b50a0000c3d005d0000c82c5d1210404440c41d4002052010079035402940c0640100810308040c06840c0070b02800034407107151b501465059a50381d00105d150105076906840c0038681c840d0058241d400c182c00750100640040d4043c20304e51103100c3d001f0030f607801c01003003680c004d03603000c802005ca00b0071041c0140c6215812405000400000081c0034000d81d640c440d40310724040c46074400103443e00b482c0c00c204007081c805810051042d6020010002c040c0408081c560803220312410f20741e021f0701c40c4080c2a0a0250085410351070f072049988060038080a02043c2600b035400c0c0d000c03940c4507803c0c3c42e84102920a9a455407640701004000a015035018651041c100c4110100004907503030b07401c4008040ba0400c0d003005000403112040c6a6074012180f24080c0c00040484807003882c0d042c1c3c00041c002c454522441c078402c41501c0701c10720350552b0048213070360050711014106100035078680c0c003400100c140884a407442881444010b40e0003c0e07040c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 171465377 1250 171464127 171464129
    0x10603060e0c030604140f1503010b010207060e030321090c040b061602010210050a020a2703081e040311011b020109051c1709030706320702040504061b0207 69
    0x500201d10341a5101094001c441c2c000034413454100d42c445171115101284030f24114440c919800440042d410000001d080003104c1e48480d46c0240e00d4013220b60300710380e0000b520208903483c914092401d8038031880424150301401c1c02001e403100503035070001c4d007034032030041c0703851240009104440440c15240300304415a51241001c54114804000d014058801c10404416940c01801140c58074a01032800000315801150036800050b401704d55400340302e501560301c1c800b242941600940c030501440c085c0d40840694070000300240300c00100f801c1c01070080c04400410711414942c16480d84e550341003003101314003c01036860029034414080d802c0311803e402024015501070b51104d04c60303400d14050044071214108a4010410021125000158440d1202c2074810042000710f40313a103010000e2514102403a04a4400c0c00900b1140000000d00b61440c0401212000c03a03c4620503480c3c081c204d441d209003000a504a0300382402c120920400da04070b042c6d080819071500004d98001c00e012078a4400d6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 171466627 1250 171465377 171465389
    0x6090601050612061c03030b120f03040e070c0c0e07030c080f1501020a081317070605090f12030c06040c0f030c0e0606121602120301050310090519061401060306 71
    0x20501c5101e6003c00c2940b41903030310400140c81d40d44421400f9100c6940c00c88040c40841c0020f40307408110f903807401c21903801008800303070b0300041074a100b0404499449004901411624041440004070740500c07801c43d45104940020040c2c4039161100c1000c01600011190040444d042c5414041503500c544460f9106000c00305000c0c1d40e80c4c4440c144034003c0340b500911181184030780406440030a2990004160044030101102011761410380e4176070888841000302c0c03003250001d401c2040120342280448142c032200300d660a03180070300140000e43c3c800f0101181441484040781103400c40c9400240540281c0c05507811614003660740140d981004006e000003031506202080401c06220306890381c5030030202c014011401d02c0400c0300c035040c0d440e070100c64a41828200410801c4442d40502540100b44051501640313150f05102c007081e07641084014019040e6501d9030000280302c0c0500c0080c44014009000d40342107030043c20302030058440c12101c40c01e4007110394000070f2414068429801102e00f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 171467877 1250 171466627 171466639
    0x50c030901031a210d0201050f040605091e03030f160e09180a03021b09100501180e0109060305070e040b0402061303020d060c0f2307050f0a050f0609060105 69
    0x3840000450242031100d0016198601030492204aaa01c000a80d0070307003088880109802015020441e241100401c0d81005692514080c413003410280061542c3c41074104102003001d450700d00300d8620f0540303002c5c52128035201c0412200c0b0311000202c0118083c40d4900c07080c2d080c0c0c0d16600780c0780100c07034034941d01d04000c520311850800307543c10030003100d0b03500803a18070b142d2041d00000c0b420f0506050b2501400ca006030400540c1d142d02c540900c411000c401030030364000e4160f24003815501403030002c5004140c10f0050040450502c4c886801c60040034000200c50010a541d45500c840d002c0c0c15180401c68541c040c4d81008500c14400070034039440340341c00c1542c815031a183c540a00605e940314150011002034540004005a220548110441881001e0004c1c1e50801100000c1c0312103c005200030411500310500382191080c5000980311111a0542c16660040c80c5001450700e020303000300c1c1c84036000e00000306c424050041820001c04640009a0b0201e95540c40034584425090144c0c5900c51 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 171469127 1250 171467877 171467887
    0x507050f0601050a0918020604060201020a021e06151207081b06270a03060603030e12030a020706050904060e040f062d020904090204050f06030c0406030312020c0106050d03090312050c03 82
    0x1c40c15000318041c502c4400c56102405221f0300401c2031940150802400f41c1c0d00000c40a103003039410001c1e0011001660086607040c002460b1503503ca5402070034001058089015240456a50f4043c640f50040483c04450300740303903280041e64440c002404440a92000380e03030b0884240c140300c0102e03000c201c0102c602608900350040c0301c0303d100c190311408540100045a0210018210f4498103000d1406030305c500480c000d5040400c84600810b1101c00d946030824401d04a4107038000480200340c0b034007428102c1c0c6030210034012070000d0855911140a0103008000c4c0814408494135190481e0300814091103106040200300f18103d6102406e043c1160035502c0b4034a1490076503016003c0c0c140010004180700c81180c0025080d9a4162528200400742c0001c3c000103103010032203000741d0842920f0500c2729a00d181c4000c0c1880014452100029800041071990300d04294003800181400030441c030980c0ca16814000e01243d000c0c0800c5a04003034500716034054038014016242500000d0008603e40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 171470377 1250 171469127 171469139
    0x210a0e01110c191b06020114060105070203060a09020609030a03030f0b060c071215050c0901020c1e09090304080102040308030708070201060b030c0c1c260609040b09030702030a030507050f0601050a 87
    0x2e14010f07003080e03403000004c03c0151400e095041d00e0000410f002d6002062180c2d07160b213600100764000e8151814010100503400058070082a016030005c00007400091094190003c1000b62107041440c9a145c01200c81000404d40c140c2c0c05400602d24000342040010a540306011451090100f04c42c01a840003000f0003040c1d61052000c241207110720350410b0413044403c1c45070180c0c0c0040c2c9d25484400004950340320303e540d04100d0440109400c0352602d014010705045244200d500b03c0c4500e000380000800a070310080c040003160014550013000319030300c541d80c0c103051032503810580300e12000554460208205e507105015000640d21620b1207140342d91241e4903c080103501885d6a42814011801c240e50510114044c00e0010078442e11003042e2100c0e00c08100d103003080000d4810701340c4008481845404d8454005103a4000c3d80240505116201c0000b00c4e490341c000c82c98029030512a000d003200c200f660207006864180c1c070420482e560030300c13641c1c0c1ca107407507107824000c00b038100d52503007010001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 171471627 1250 171470377 171470413
    0x311060301052202070606030b1504060f1505070c031a1003050613050a0b0108060601091a090103150312051306020d0c0803100308031f050604080d05210a0e01110c 72
    0x14100f600d000501d080307010351369041075503280d80c41524a441100c0401c20b42d400a280303007000c04201214104207141c01c00f00012000e04c80740c00396044804040302c1c3d505040740100204e4501035045070400d018140c0d640390042c685403038211200b5401d06c2d410007241c01d1501300c15644050f0790307100006d403d4650790880b02c1075034012841c40075600c43c80386490503800301c1c04404400d4007078900c80000c2c02240ca80034001610400342d5901c84000c503100710983d01000307024a801d82e603072060301340b1700400c0311000ca1a0551082201d80c0019000341464407500b240550000f00a04606440002d40c85140d9903403c4180d0b1a416100c0d0301d24003042e040881500002e20b8280190384c1b03d011440c4a082070b6803aa140d29500d904100ca024107406000101d803000c0d00c40d10420800103010494045141c00e080071304c3c0540381c0d1400e214410500c0700101340c08642011107072000a5002400d08034861a150680404028101841070a8415403a1025880131300c0c0e0f51404071804018584000e25000d0508000703044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 171472877 1250 171471627 171471679
    0x71d04060c1b0c05040b01020c0a050d02010c12020c0301060e0705070609061509050a0b030d050a050d0b040903032313020f0a0506030702070314060112110301150807031106030105 79
    0x100055001d000c640114a10b5418949500541111040500700014001100c1c0462101810755015241003840390380c0d05400d03a420344100b42c584200c0303040796100513512001e03501801818000e6010012009580c0059880d812480441c02402500c0d51840c100040070f005445001c00285c04104c00f0000c45c0c90364003c03201752403284c080010700d482550752905020b100c81c0c1001c200280c558003030240801d942e01a5a89220084014000072248014080c040d0310404200c0d1050000100300c8121322060740c3d00440c1c0c99500680305020303c40d981d1400030010b1184010550307041004905a0b210301c454040111b00c80d442e0003075918000700c00364080041d080840f01c0030540c0040c0b40000030401703880311f10165018030100d40080c1002030852a001840181c0360344404801d03403041d40100840340c800360464030314540000036001e000b000700c00800d0241a1001c00480d035010010303000965001d00060410031a0702803015401540d40e61010090302d440284240d5500a0030000012807104840703820103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 171474127 1250 171472877 171472901
    0x3090b070311010606020705010306090608030403020936010c0305091f02040306090b1012030219032f0c0102011802010e0a03060f050105100c0c060f050706060b0408071d0406 77
    0x45203000d11201e159003134800303d401c0380005801800040019503010302a01024060b180000c0c0846401c0c00c2c04107650b03025a210180c85502d240c8049456002c1c40f10000034498960012a42e0403403030300d50215100222040f0039901c03513180410344000940b280c45002c1c011700061b40a05220360741030001881c2032403004c400400c401d0342044000009400c1e4480d80c100203124203195401b070301e031912540514204a034485c045060901000c4d0700040d901007481401c5199101c0d050b8504401414200c864665403900103400da08940c50b590306c101e007007996901c1c074000c01c10200c0b28100c074100012800d85400480b229a001c0d8a814072030015070150100c401c07030140c040c1141e4030250b80d94490809640d1309407a5541259503403001417045003040901002003d096040100c686007095072009004071651180000b00410180503440061080c4100d80e40150400303400d1001688070201c81c0c1e02d135405849041c240d07100312607000580b80b004034000c1c9400305248440d00e4050340e40c0e0b10b50801510440d0301003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 171475377 1250 171474127 171474137
    0x7021806010818160f081630140f06060103060602060604050c0909040c031506120b040c0512030306030d09051503091f0509150c0403080f0d0920010c03090b0703 71
    0x615003110b0600d000c00001d02040c60021702c0c581c60440010b05140100849014040e000801840354486030034640c4000b000e111000d130202c2ea140c01e0404402512190020501210038200c03c2214500083c5040b1a450a600351003280c0c80c0c0c01c006400310b5006200c1e0001580000c1d000507101e2410b94051030f0b00440c042542450104141d00051441204503002c80c2e441c1001d03002407003406090b511081d11008a807004000d21410900b480d482c00c0007042e0000c02150a0302e0008041201c00318440004110151880148406500315a1b880350411504140030f07208022040c45064070070110b860031114050804d07441902d8190030103c5951000b09410b06030702c16210b00c1da290507803010b204a441e680012000809003005005a030404044011009540058005100c0e04d42801d4084800700c0b80c0c040f030484d6407003c01c00809000c2d40110b102d16901c0c1072800001c5401e01040444100f030950b814080302da01d8856a50054555000e1a400900054440d010034044c1080784001084500d00038104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 171476627 1250 171475377 171475393
    0x20a050a0b041a030c16060b0405100e15060306100201090b04030c06202203140a020117070504030b04080c0d05090a12080d05061804060207021806010818 68
    0xc624082100e0740035032516400090100681448a64198260300103503203242e1950504040d54001801040040d030850850181c3c00c10411440340c0c004018910098810712617894000f82c001895503c0f4800c010400420390001080c0b141c181b00c2e010034181006080c01e085844038420b100350b4203140c450300c0040d590394244076004280c149005c140300740d100e5968542c1d10401440c2800c103450320b100c0f10004203020700043c0303543e0030404400c2c0d5842400c51135901c00c40c88044400c441c0b0904240d4805000c0b0b1448020402c01e2040109a182619000383c0720396039049c2c04100d4881304a20101d030f0080001d0004c0c0414000214808229500203002d903444a040c0203a56001d641855548102040030404c001012411405e0086003d0003c000542851400c0162030302d5580e01c1d0f21441e12000703c0c640c0da8038005400341c1c0d07036113210344005580c02152144501d01480c0c461b0080d440074006910444d8661158a6105003460030248138200c1a92160101e440e04140d00224880c041c1c10b4000900071591 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 171477877 1250 171476627 171476629
    0x3030a0c1707240e0a15020d0504050d030e030412080723010e060c070201020703110a120c08011109030d080c0d020a020604020a0807150507020310021c050603011503030c020a05 78
    0x15090060040020028241d5a04090100c034044a810f051503d8201215000c5041d404500c840ca00398000e14a440f03096522035995000f03200c0c50a078140218a44002d00081c800e0001c2c840f610300d0060346041065881d0750600b41e56900641c41000d001445418002d0005400f0b60301811080e440303510f007101d01103419804040e0100c0d0003070300d15500d82e40d21160840070340760030414260420741842d00585420b4260300000d413151404d000291600601002003040790b203a4584030002413124030030921812880d468000190240c81c800d0702299801c1115000480c0308400c00c68920031002002045c104260708015942e00c0c00080590040c104244185440520f003800180000c0c0c5050303018041c246001d104110701c0b11056000b403c0e003940149814008000010185041500c5038145651500354030b100003407030210031001c441c20003800442e0115810300d0184100c40b085086100038803d90341d540c0d06040c204d50102103001d54110003d501000400e00a017801c2e01c055001030655400340783c90f24 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 171479127 1250 171477877 171477923
    0x5042405040b0d0506040501060806010c02010c21110c03030a050403110f060c0f0708060c041e050d03030b01030b030c1302070606090e06090f030a020a021005130906080f0c03030a0c 80
    0x104012070f1844d240c408000643c64507119a501405150800701c5403820210002400c0d80b0101c2002814095140c401c50248420000c6044802400d08a4000006101e1354000d202103e014000e04041c0b06482c07244501c1c4c03a01000380d40035510640e81d854149851078440405640d201240b0b50b40003500002404001d85585000f08500c2d40800000c0c0156030f8480b03c01032508801303901c04070f0380e5006181400000c0e0005401c98040302c546031103441c6036840d403040100e00d1207559441107510c2841e03418040101501034102d4007000c1400d03281008881d11002c01d06450320100c00d01c0d958807030011027400c2c4042109030b000d005c606006079400503016403600344000440362001d41c1c800b001c0e0f2081c820040c01307035400c2041c1c550710b0740000d01960038410076104c043d54131105414001d01c81c1030700d46132000c10349101c1c80590b001410558609603610303680310ba043c5c00034a154094110300b070040c9006480c074520000390b4841d0030000174000758a480d9101c80c01b00d4591101017022500d84200140311407600048c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 171480377 1250 171479127 171479137
    0x1050411270a0c0e240a090905130611070c0303031a03030d061406120403030b060c06070f0e040618050705071b051311030f0a150f030203070605042405040b 69
    0x160b0001521400c0c0f08010b08108400043c1a1044031100c001102000e500c06180710031500c0d005a0940340c0c0700460302921100c2c415003000e0300706441d0104002c81c41c0701110481d02c241d40514410842240c0b600071285807031052503406400c2084035101040040d100382e0000b150564014a108002190040060b06587c04070070350b0500540c90341d4090050940308055180e507141d0480d01c0c50b14001e07821a8280d4a43c01c002d00c0503003499520748030350780d260f220481200e40d42c555045c2580c6662910210181101840c1e480c0340000032481042080d403800c0034031a410940c0c5040c0e65140e64007036001c50380000f8000050110301044014404c000002d103224816010b1885203030b6980040e641414140708003514080d0303402e95014200650f07007110300748407000c60390803021829541440e50303034140d200009006038100c00e13803640460000000d410f14181420f0f6041d60300c203c00359501e40d581c0c0d8804960900403030107286501c00034448540122034103d1640030700c5517040e080c01800d265881071090599041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 171481627 1250 171480377 171480391
    0xa0203030405070602012a05090d081c0b01091202060d0c080906070201060609150c020a230a033210020d0f050411150c01090318080105041127 63
    0x800300500c0100a82403104001400981c03008110048030b40c070741c0050480c00032618038482112104c82c0d00010b8411011113201c800d000d080d0036660b0f000341c500051260301c003651024443d04400c0098910039802c0c003403c4004a0140d50f0380c25054144852620507440245089030f0008042210641c11042030003a207541c1c3c0c01540740c5207072920f8811106810100020409011a45024024408240c028820744103403400050502200329012506444100c00300f18007940c0310060310000502100204031402c03980d000001a41c04017805501031280400700b902000300001402e02801c2e40707400c00c00c80301181c0c002c1502e50100d40c1800001d4032509101900120780c41c41500091440d080400b180203090302d2000c941400c1115127042d0311204000c0e000b603402244242410307012590b4482d001030680c2c0c1640c5018008011142c69840c01a040405031441d003941c110030154005034810043c070501d88070f150400803081c191840402004030300c0e40e90040031007030005120711501b1030050504c603c5100e990 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 171482877 1250 171481627 171481633
    0x4030209040c210302070e0a2c0d08090a06020c0a060f14160909020318010212180d0c030c030504150c0201021e03040b07020a030b04030c02040609020906070b0601030e030a02 77
    0x10621a2030000300310341080d2203010300600003c0100203580000c44800b00c600a5030660006c0e114244684098050700420012005044030080428210b030b11944031a40c13039540c100c40e44c6500d034180640b03000401701c509503401d4010401400100301c16400030141112290143d03203100c0384a98500c000c0300c41010841c5401551000500340c1643c46144907608011038040c40c9401e109248002809084030780650040284c01202140586000071007401100c90000002d540701e0141d02d5080300204401c0700c00844180d8401662070541e4404107980820034141c0d991083c13002c0e1300b5102034070100b202c501c0440801004000000d4040e9000c40c014420140681e500420010107000092030550f60400c034a6810013480c21b00041d003640001110200c540c4400f0050b1078000ca4000104034009680c40a0281c0c80304208210401d94007151103201603208603810050244c654104004a00a2010b000d4020303200300000390100e8002021154000700501d070205284401c081c015055801c03464034000542c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 171484127 1250 171482877 171482879
    0xc0e070e2101050c0f031302120f0c0a09060e01060309080d050703090b0a0204060906080c0c060910060b0909180106050307180f180f0512130503010e060c0904020c0304030209040c 79
    0x12080c00b421390004a410705050410b01d1070700351112a440094030b19400141c2813090b102c01c648981c50a08402078003a0290b0700551506240907840b201c2ea802194440c0b0041300010801250a02c43c15051b105114141a603681c01c000d4160000c080200003030f2040501031150094a1000b8040c1502ca1070465401040c03082091811040700340015000c03074202401880280605030f8000e198070f0484440e40341c030320419200c0d54985c01c4e45202d0b01c2401d95503805081c040056a60001540d030118201801041140d6076480b001c82c140750250003441030340031072910701051002c1c4104003102c2d00449483d000040030303a0b81e00700103403030b102c00c2e540b1428110460101345030b0301c2c0310a84a02c00050707900304802d1250500900100309421600380c0001c0840758040f440c20b00f407140421420390700009a611207603582c442c009e00050a40c85031308c0381034860360a00c1d00c10010442c3c0031896900403e10b00c440d50341045041c6007000041d40011110000c01c0c4000d102c0000907a4920700d546029a0048a40d4868a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 171485377 1250 171484127 171484189
    0x809030607031a060a05130906060f08040308010b0901020c0310060906090b090703090c12051f1a1e0d060e190807020603060a180510080a0c0e070e 65
    0xc540010302040c00d240c90025601812036001910541401085501e140d50f02c64001058810340210368900b40940441407010402c1c0c8504d50045068076601d8a9204921003040384c115501201120024000340a52004010885242015013901041401991044000071000c03a2405100012001e0100e89400b405c1109140b2403203a07101031300000c941030051984480200762000e002030041d1080543d950108028800601a5000907114800a5103466800c5050440ea04d0805030b011a0848509000f031465501c020320034903440341c40e0344610017106400e03901084603408104151901c50880b1500c000c20715902c1c041c031803d51520a00e00010207410318402140f078954603a801c6006124070340c2d1500007060741041035425007a4111a49692586c0e90340c0410441000e40d8080381c1308112491014100c0c1c0100d80081c2d110713070f01002507540d00c2d60751071548036590009000c000e000401c4499080c442c46181308c3c15154841c21500700840607007800350204003130402c9031024042d0b0046e04050300e00741e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 171486627 1250 171485377 171485383
    0x106050907050702030304230303030103060903030c031b231b0d080403021906150303110c0f0d0303021803030703050703080a020a051614011521053403080903 70
    0x101e540781807420301202e903022070341d41d02c90750280d0110b90340c00113030b10403040c00310400b0090000400b40681e074582d6540e151500282490507803c4001ca81005480102d19200b4480c03035030700e881502100c0c18003008204041d107290711030240001c80914a15440c030354019044d0000d00710354010f010403003034000b0f003032100c10304290141903400101709a12080c03001180c0d00041171080118103440f010610384c180d00d07010000304642e110301c1e900381e0f008003400011300d41c006010079040030303040c005d0f603110700150003c101c00821074101c502d81c01b040d0703950b10f5404079119074041c00914406050742c02401d14848002842d581125500714009240040c495003050340c000c480b41e40040307426900b54140003041c08054240d0040c070004103585c000c148681c405205020584030b4100d00c90100030449100c0840303440c0300840f003601610017001c800c0300050601c5103100c07501c4040c25412030058090300f0500e5800b1202c0c1224401d03207048250800302483c09019200051000662041c1d54181c1e03510000e00c00d00d41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 171487877 1250 171486627 171486631
    0xf090415051807120528060615080f090303071b06090f031202030603030904180b0708010821030a0b1f0306090605030109050a030e03030d02070809040506060c03040e0601140c01060509 81
    0xa0038132145030710700091800103541c24404540042035020180d044544a82c004c0450405040725040900014204107243e070005076550041d0790740b12559441e024a8102c07440165000d11050b8400c1000400c0e45105a02c00c203000100320740014071021041c1c655101b03943d0821002d440c1d13a600b1400c59401c068001303411040300c000c580d200350300707610303000001940700c1c0a001c2d190340c0103476280c0080e403500101242c0c1c0312065a40c4801e071043c480c10500c100821403a02400359454610540075101096000c80c0c8a42e030086648120580c51a640d100005c006450010080c5400c240000080780d802c1e1129410315421001ca0707a80019000d00e00480300058400a50200c0c0c0242d14100c6820302003040420341e09201238140c106040c4c92405480442d1840c841d2805801166102181003410011600300901d122001114244115100c20701045500d21a5a80b041c000d50b0040000300f001321203080910340d100005050082d0301d14a41c901d020841c1d480400492026555810180800d20380211415 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 171489127 1250 171487877 171487889
    0x24060d170a0215010602190c1706040201030b0402040305070b0c03040b0f12010e040206070201030c050c010207080c06010e01120f0204020912030a030c0f0f180f06110c06090f090415051807 83
    0x3c0d585515040029454040c09044030100120700c0394000107002c0c1400020009040c42c0024640200f42441e85c2a107803181914100e0010742003861b14581d514003070082d14103807a00400034106003842c003117591009600501e0343d08101d010620001800701e84100103003032843d0080d500c1d1a5200129454111360322016003050092044403010f0001580b1194242d91100d85d0a080024640c0203456003601c8600400801e06195800011880d007040701c800041c00c00c400030b102c1210810b0341c840514682074502409103000c3c1843c010701c0d0b140400d2007200a0340034103001410043c0340500740d10201e0864002c20340013002d6940001840a05213a0511881030002d00c03034034007000050034900c8000d003c071040d0085841040300042010b8480e5070f0580b1080002c11071340303102e005075a5550001808211440446400f035020b0b86030302d036010303081c139000301e0311015401032000945104010420101010140003560a80f0400c4a040b00d0b960301442440e02070b0484810315480d40034a08405850700718560401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 171490377 1250 171489127 171489163
    0x3051f120605090105100b0702032b0306080d050a0507061b0309020f030c03030f1803060702060708070903051908070609140f0a08040e06031c0f090824060d170a02 72
    0x401d030384240c2d007a10340c1500c4440c7c00181c1e8420b09800042d141c86040a40c1c49078010a52010320b4a91031118070f00f503c85116520306008046d0b544003031035129490b590b00500400c1e0b04000aa800600c110000c0214034411a4000340d0383d8920b60003003a2600000c048180460341d00c00070346d025480d0401012443d1141180240840804034011036124042d0142000242002141000c2c042000c001c05483c40c5001800b120210316008500070354610040e50841e012811400c0071038240d6204203402c0d000d80360801d00810491404000f03180300420301c1e2505503111b07030043c001e050009000740510b804850241f00008a44904c00307585070b042ca501c0900030f400b141d0149a4000c001171404064508a8044440c400307100e80d55080881c0c2400c0c4c40340010040703528007240e83d01e0041d0300048120718050f0300d40d5600e00e00359207a00701c050f544e90415100d082968a10400302000090502c846a4004405030000c401511142e8607100100280c6891070b1606401003000102c5030750410810660402d4803900c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 171491627 1250 171490377 171490381
    0x306080115090513051225080a050307030b060c07051507110402030604110c0102030a0c0c02130b0105040906090e010c03051312211a0306100603051f120605090105 72
    0x107903151120301d407041054640e100c0340082c003880083e541d84103c4541000c01e40b844100003030f440c6c440913800343d040403c400c0e05900c04601d6501c820705840c00b51540c4081c4103407500c1c031021015961b50708028412000c00d074840041c0ca41c0c0e80c0303812000e480c0e50003d00b002800181e04180400c00c0c400555103401090071003d004030070105407001002e02d1048025140142c0d0703512040b021901a081024042940e0170700090302420041c0d05600540c41540704030f000b0410080064000c0741e00d110010300c00780d4030254083c1c8403551901e4540c084c011024050405901c1e2641c0c6030031910070303a8201c1d803003564420364503510070302000b1080c010060b110f03910380b03030030800c1d46404142c501d43d11210103409008184418259502140100303126443c1c00c070031031005015004020501405056640c030b01e81c0241c51880d82107042c1d414001426405a4540f2511003d840d003810002c4009103c010003044002c1081240c030440181e204a10350040c00007600902d8148901b82010002d58401809110140e0701d0801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 171492877 1250 171491627 171491651
    0x3050a020a050d0209031504030917010c08040204151e1e050d17040b0f0c100908030a0c26100b13090507030e011b0f021902060c07030501020a030c03060801 69
    0x80f2a99155602c0005071a8040072000c2890210b6255040180e1a41c0c6410310050681000a141c11504518441c03291075407250540343c00c2ea19602d181902007061040406c0040c0fa2680141007440107090420520591b90340050040071042e8007101902810010103110844125040364400122030904482c200d251201040050000540140020b4802010000d007134240c00111001072903101349254880b10405454000b590004100f4600d5205000c04081d1032035950044115003504125a1801d650360f68104801400594440c1810041c00d8425449451941644652034507141c40c01040c41e464159104403620300642c004015200062050040c540100c46190b01510300501c40840c43c0e0f190801c1c150003911440c43c02c2c145039401e05080441285681c101d0010540c81c40e0b071080c20b000d95400d0f0070b0340c440303401d120b1040c5540e05080120300503080c803200034000348100b60221b90007603581c0e484042c00c82c0c100e0401300000a840740002521964540141400340c500d5500070494031302800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 171494127 1250 171492877 171492887
    0x605160801030c030b07110d050904061e090b010215041103060618040303201204020312070809040e0f0a0606050901052e020c18010306060e0601080703110412030c0303050a020a 78
    0x312005107103004490001d00840d101c0d5124031544103842d401c940c5903c2309018080c0254002182540c040ca01d41a00025000500103102603a50750724a0013262440c02c100d4120080c0010024190561041d02c142c0001c0b644880e4001c1e2043d405502c1c5210f1184c60503003014203148010300400e10800f003c5018101c03a072007624006811a034182800600041d090700076101d038081c04210b5031179500c0c000c14100718100c142c25141e071040344200d081e42c4c3d10240e05031600b20580542d000c081c00c0488180100c84103401c15030f000241d101801022030301a2560841c1941c03400840100c101c58540d00c2d00404c00146c10a4244c00e0f02404086800c2d0000140c0100e07030b030080054100d2407800108107030b000242c42500030300104d11302030000b0b8101d0305241c0c2086400c40440c402840121044e610f045000110b101d40c080000d130007400141c2d140002603c461400314041c100f100112110410100800203800c2ca45189601906100b0b80790300c00060714078200981220301c000c0602405500410100d05095401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 171495377 1250 171494127 171494129
    0x240e01062f010b0607050a050705090c040b1809100f05030a02010e0108150916020c0409050307030807090e040c03020906100e060c0106030b09012c03070b09030904090605160801030c 80
    0x15014201d01825015400760000458041e0400310004004040c8070300403620021460040080390768aa94480c00d0148214044502034040c00d004d11050200c807090000034440c211208100d043c800ca40207000072003540c400e0340d1019802001207020042254400311050090008070003902d40d4200980000c0c01c4110412215810050748074000f429040124145075a082c8014042c030b0381034074080840e44012040c5e03289a001610a001d180e094525207802a2108180c0c02005103061140998082c0e4a802014091800b0b00c08216070108258034101c020a01c0f4a00070219191031070f00d50300520240d000302410146c0614013800c0b01c4e920300ca030400c0c41032280c940e0981d4401e42d01c0c0300403000c0314018003103500010820041d40e4103014108105400510b859203070030140e620301d60400301d40c100036a0050302500806400a01c00000401c02c0d90301c090754001464802d59241010b030b64000307000c8030b440c1c02c022500c0c0d503560f03c148007142c960f03000c4524044d4103a0070400307800e50654940017012081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 171496627 1250 171495377 171495437
    0xa020a050409031e0201020d1103010b12070917060103030f03090b06060313060609090212030a080f06010314041209120506060603060a081e011407050a0c030201240e0106 75
    0x21410b18600301407150000080100b501160500201100311009010350b01c510a070f426414100210b140c81d040d00c000c100d074100c44040c6001480d00c02017141a0074403001c000c140b00140044600002230100c1401003010001618402401d05503040d4038001c2d0903210015200c82c0ac06142410b214002040144115000740013110815120b590f41c050b0080f02c0011100300a11490601d4000108800e003034210160044c4210f50243e02c3c00184031a090b964003d0300e074604005a5100003003204086442546a00018180741c0170520034800182d00032160400c1d07030304850032841000c0c45a40603920400d00c0f00a445005200883c24002c2d8403110350b43d1002030601c41c4034110000202e6016511207610304018030109040ea031400c03201c42c402c0701c0c810560030304405c484e5003482ca01042c0f40d00909509445207010761503150810420b580100c070144070088044056650f140507050244080c0300034a00b841e044080200c4200c3c0c14241520507600040c1d200c1d0040c40300311903d004841c82401d26050701540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 171497877 1250 171496627 171496631
    0x12050d060b0301181e14010806070309080a110703080f09090615040b03060402040f15030e0c0901060f02012a110303010302030706080405070b0a20210d0b040c020c120a020a0504 78
    0x1d81d03c034480305004421702240407a181c0248040c29001c1c40d0140390480315488186c46066030740e1a801d80503201d4400c402428000d0030030101c1710f424014031a00350b025006504941d817882e100c0e0b462461f10f5200d1000041000d5010a5600e114034005105680c40300040d46c2540312020030850b5200d0501890040342071250022000460f10f84450b0b050340d009102c900609a04071780d40f041140e007680e001c0e00e040c1000a041c8030400c0c1080100207651242030b039018062076050781c40d08000325a0044240a180110b540381c02c01c0c658100760090305409141e151460740031b107034020110b000e07007800300b201002e81d0f16800500040000da036001c589042111580d06101c0b40036a100d02d001c83c02c00c40d0035000b1000c1c28001080d0203905990100c07154494984c081c02000503a02018078456444507080025000698101041c2d10b031101c103400a4a00c520b00e404022801500e29000101a0340610342e140c001a0b1240322040501c0c541812204001c0c626803016226461003030700490300e484141c3c091140201d03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 171499127 1250 171497877 171497891
    0x4051b030711031c02090a0f1d040f02090108061911030615040305070305101a0a06030c0c020306040b06030d080c250206030a050f0912090f01090312050d060b030118 73
    0x4040c812165508800105139401c2403040b2403400084d044845081c0c001c7c05a82c03c08140700e8104040e55007900c50a161148540c1c2c5200082c0d985948010001c64140910b81d0380440141c0302c0320a154083c0c0305540250045140812240251484444603c001c140c20115110781000e4218104c94221b9000c3e11601000860710001c01024495648000c2c1144640b4500000748100421001c00c4082d110b0410b1010f00d1102008882080b0003440141c1d02120b5410200320041c00303548041c019883c142452250b40d201c0703400290070680115000e9417042920810400940b60030f00c15006000090305055200f030503d07551884284c02024000c14144004559184201c40290505544c4590041680d5668a0042500800b41034191680b5603001d41080200e820003201246400a0081c0c0f00c1d1107030701f0309483c502007201c2010340129045c14000d880b0400f00c04100300d09085505030320750713495569403046c1c0a14041c3c2220002d510401070503000740014400b00d80c100200180c900701703000300803c6035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 171500377 1250 171499127 171499157
    0x904060903050906130e0a0204030b130c0f06030212060301090c12020d060c03020901021b01050901050304020604030c0b071518020909011401080a0309080c0109031202031e03010504051b0307 84
    0x2d882036202c42ca522030000300f0814513004940c0c00100a465030310701645c04540780c001c1e00c1e00c181d000340c0c00001c0c83c00e01c11200140b0341640580341e5100e144e0182c0c040c10b44a40d41c0e2002c924103d09203400820009400040503a0840d00c0b024200380c006d2000e0f4020095148241c45501401c1510b00501c0b2244604140030310030f541d00c0b8089052007a800c034404205400c80b03404041d00942c000414503000d8058210110030a1107416009012080181c40e8a458019200011560395000800480e072041c0e05000200c00b155002a45002a1400313084080e034442c22400d10f20b445014240e03842000e68201550b020a551542c1080d841c42a4140c418600380d0f00c0f14001940502521081e405e1040c07400c0700001000400052a5543c440c003d854062400f81c85c1c5803e1a104d80d0b00441041c0480c07054001007000551741c6040312264122441a2402c090321144000d00036285107283e4003480c000400148524900743c428542c112050b207010703d04525100e0b1008026020041603001030041c0030700c044c941f07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 171501627 1250 171500377 171500387
    0xa200909060a03121112120f0711190303201c060302100305040201020a020316060f0206060a0303050906040308072607020d0201030e01060e0c03010303080609070e090613020c0607030e03090904060903 88
    0x42d135034a4050031607c44c400e0300c4001e00ea151080741d904051260480205500600910840c035140c440359024000c902c2400000440504400c1030031020541e4500c000c0101c0c05007207403601c1010f40801700d880e40c1e03401007413843c1d801ca03e8241041007215252074010401a0307204800002e01269906020036240c1e25800142d040c4848014069003500603c40300a40407001c401c40d03a4140d405c581c4804a484100340400c03651103000700d401640115085000781f01007401107001d02000b03800207019514181e2070780d07101307111500441d03c00c9a0076481001e50110640350809600c2001c02207030034040c1081d1407500042e20910003e807020b4107042ea00c0e80450545102900804090803042c070061105041c4801a2007458bc024807081d40052480f101141c81c0b0320f0051074440c055415036940c1d02880010f4010840e040e940a40b00302da000280450100110f0280c2c005024a0800341000d00110320300160013400381c8411a82041040e001003180449582e1461195a0482e40150303000038590754910381a15 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 171502877 1250 171501627 171501643
    0x9010c0609081201030b130b060616080406230a020a3206090c0121050a0213090e010b1909020304050f0f0708160b120a200909060a031211 61
    0x42c0030340004440c10b01d06003e072400c6040728031949a075051a550502801801321540d02c0043c4840030b00c41c040361175480d040c0046c140c403030b6040b400080742000359a980a01980309904c02d00100c0e80d0b0f078544200011080e000d200e04040020031591900340d40075002034944c0ca080c140100980c480c035003427103214209400b007104a8914040c030029001c4454550541d600b001322200b00b0b081c0304111032403072294072554072403c0310ba001000f0b54070960780c000141c00203000000c0c50b41c2c00c0190b00740005034241da00311030104000c00c100000050680760b5440824255600120164062400c1c80344584160000d050400c2c105c90b140d000068507500c582c60558108440a00c50103010301c10318841200000000c2800011150781d402158410101200c00c40b19201d0a8400d40103426418001032040042d00328105a10000312080052a0300e850048812006d1004c0c0e400c0d0544200454807200c0c5080c84154240c111400300c03200c1074000c1c51940c81009181c900e41c0d00d4002c00003049100306903d0801c0107641 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 171504127 1250 171502877 171502883
    0x903050f0c0f0708010212060307140d030e0d0305030601020f060106050a0c050f070b0c1c0e01030b010e0904060501061103160204091a04060207020109140306010311030f030c0115050109060509010c0609 89
    0xb8000351381c0c1e5000b06010307400c001d802c3c00c00b85000001003000d605d400200c90040f58200300b40c5d20034141c2d03041d04102a10840c0c00040e070a0000d500d1004800c2d0b40e51070194101d180c420744401d41c076820000c000a140c103804c0700109203641d100f88018040990410192103201000d0716000d20081001c0c68200d0616031900208a40c80c070031001c0215403100400003a0000034080005c0310010b10006280300c00c6811140c031080086000b4400c4200e40b07503c2a04060103183c1c06040c07002d0880400c4c8003080c0384000454040d0f80c119519001070000c103038410034480340b0072008801103081000f40f40404a03600102c240c003c3c8150744c4c0710300100c00c02a041c0c330840c1c3c0f156103a80d030050b801e01c1d1038200b400c0a9804480b00301d000840182020503400f01080598041001c09801007289a00b9561980000c1c0c10b06c04c031444c1d05214000340c514400c0000c1004107007628109001051f101c640521085007004203401450500100c0c5c0d00611940d9070041c240d070403010091810514100c010704100c1c0003000003107000303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 171505377 1250 171504127 171504133
    0x10c0b0703020c070b181c030c141e010e070f090903140310090609020f03160228050f0c0904080306010513120b0106080903040303030504021306270903050f0c0f 71
    0x80c5e40c4c2c8020b0060000c11031060440444285642c0401109110440e4010314003c0310070301260109201d8426004110b02c200c1403040070119843c0c1d2940f6110000ca00e002061f6044200006050401e016030010007591000070490903040c074441740d450399650702074030010a5070b4102d00000e151140703200d041280c1c07020742080d680342440c1d10018141c4c81140141d0322190704040c00000c4140b020700c00c030b410440c8003c0c02d0360b00359280c5d18000d9074268000442d807411485a02900425828aa20244240c01800003410038000e51850700718281ba100210440040e0488420001c02c1d84401d12055171003076004038421b5481d9900801071302c0b540941d001d034a1920b001220082884028051090007150041c8200c40c00d60303907074440031a26080212039168a541041c0800c000086c0641c0203250030610080089012411160842d412200150b2100c5640709101801c1402e4505005101c910200840010b11074404c0c1e81d100034000c0d104601103080a510300040c2000d200d0710034811428549410b03c2a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 171506627 1250 171505377 171505379
    0x30106090e03030405160b0d0b03070302060d0b1302190f02070807030b0702010e070b041517150a0b0a0504031e050d030606030c1e0804150203070c0b0601020c010c0b0703020c07 78
    0x80c07a40d25003049904458900c17814103040038540c0c0b207480800072141011748462074440340880d1000a81440100941c00d44680c080202c016520000501a41c0406101c0001e00441400801c100d14600c44528504144104081c0d0501d880480152005880c85e0400801c071988900c0c00301e02d400c4503070740820101c0c00f401d40040208203844603024000c0c0007c2e03000340a5252502000c9448100a101d4451201410001007044000e0f40b604105000124100950f90202803021300c4c03500300007102c58400d40c05a02c803a821070782c50261800d5010f407540c2100c041c20b14185220180451286000c09021012506a444540c0c0501d15410100e60391100c140c82c0311000503500540507241c0b034018000440c1c2440d103184030040c0725000b20050194600d8a561030138030850400e4550031000390041d509130500600c0c0d0501700302e44c4e0001b14001d125982e11032041180c90b041245079541b0240c200c42c11504011041c0445a0344210100300303c9405c01c801c0440e64035440800e80c02407240000b009103078000c045e8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 171507877 1250 171506627 171506651
    0x6020307080403120506030d080a020405030a080901020f070e011a070614040303060b07021f180e040209061c02100e10090503060a0e030d1a040906151703070206030603010609 77
    0x6564082d80c070070348a22010100c80c2da04001035600c2203d907150103a21019645014500c11643c09402290030b0030010720382510750300403900300340c1040000d8a00440016002c0000d590420001c2e0040f1014005400080d06084030b400d24104103100e115240e40130780008851914441c011541c0c1c842d40138408001e0741141000350b102d20b481c00c94081c1e002ca45031460005180e20341c0e02c1202c03900f070390082c002244d82c1c07600400d4119020032501600100a03680c00e48a2031140d840340c0c000082d0201120180851070326204000803860010400b60241268034002420b021004250140d000d50480c0d04140d103501c141401c4030040c0540413001c0c1d1041070080d00c881403d0304031410000755907061301500c00c1c1d656034581d090103840d605031807511568020000121080140d51142c500211800c00201c0c504100c18001025542080810780b501651a29240b0341c3c000c0f000141c100602e0b121607004840d442110803aa2a402541400f80c01504c002001440c240e81c20345c4400050f152100d0f0420602a1070b11b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 171509127 1250 171507877 171507887
    0x5031015050a0e0609010e060d060203130b041a010506040605040302010f0215010b0d05010b0c06010e07090b030c090102160308030a0b13050c09010f030204050a150507143007020d02060706020307 86
    0x345a050107205c001c400030032500100500c803071090501505003202c00407555201030007580001c10903203004034084034640c00200301c544000d0107940950040c0703000c0b45c1e40c41c1551042d00c40c181c1c0064851a020401006403942060940741142c0e02403d00c150310ad140002e0503401c008262444a480d00c880f00300115012111201a001400e0000c0040150340e032115018043d9105250703440700c4a40c845801085103214805400707a0040040c58120202540d0f4a5008269001615036041030100420012055641000701560581d042100f650205d85103864a0046210261100300c0503500c0b28910020354486600141d06081e10100421041c40c00c0c0780a035481e03800c42107040c1d000690808003162403500c03034001d030350070b903100200f04406081c41c280409004c09040081401800001c1c003880c1c4c0400c010441c000c00d0400d001000d45611440754200f480251055000c1c0720502d0007102c00c0468030b001050585000c6035041c2d400000c69041c500025201d4003800400800d41400001082444c42d400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 171510377 1250 171509127 171509131
    0x105180d0c090f02070206040b0309071d15010f080f0603030c0a0506040c170601090b040b090906011e031e060e0303043008130602040503010c021c02030405031015050a0e 75
    0x702d001000000b41c103100007803c1c0e1180e400c010b940050140002d01444088400a50300702000f4070458640981e54491038100e1b680340d40d00400f15981a00c20030800f503030f0011540000000928286c1c000030902036026295440107400c89001244800024295440030002c480c00108008212208c480e807900d0260360f1803008540031034038012980c00020301454440345c07a00c80e540142019004503802c01110310024004402c0e01c0354010f07222a8207014940f1030642c01070086140901070441581800381c10848140e00c60252a000d040c80042080843c429108401d50030400701a040922007441c03d20002900401d07101c084940000011701c03040006208000d075940110072010358119505091090550044400e0300b00440c0302000002c90b14107035600130007100342c4120001814151240b0120b0b00311654290300d100964000180c030018084280500c950203030040c401075162900f0100842d858161030b00a4403000d0b501d442d29441015400098100584405840d0341c000d542d03074403c03259035140c1c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 171511627 1250 171510377 171510389
    0x10b0a03051e0c0d030305070309020a090c09050108061014090306070f08090a0b060405070c05030c07030303050901090215070804030618030f020f06130221030c16050307050105180d0c 81
    0xb40c1c801850580d0404030720303108160740007000d440e414001c90700c0c150007a090040c803010802da0b9500c3c03a800140e44407014080617200e24200011705000038800540780342c00540005050181400401800355555900c106c0e242c3e48600e441c0078000d24001c0300e61254040c0c0c0d81e40f0340e418001e040800440316401244034608880d1523603120b1050b242d4182a0f81c441c62100b03005007121105600194160a1039000035030800014909210440c0d0283c513014195002810752000702d80040100b0014542d16004441c2c02512040003080f609030542d000542d47c0322007402c2444094004103c8070140100e10342510300560700201c0502c803e08582c051102c1c1180303510400c81c04a01c5071264210828800205028180c4101d0002c10554552581800c01c01d401510126031141100d44c2caa204498140c2c0310321519040500103644814400c03942600780754112848402088102c042002903a400240a40c1107032002e00f42213555040da00e090301d041d2028000016003000070b641c403d00400c50185012000c0b104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 171512877 1250 171511627 171511663
    0x903030b19052d03120a0906030e03070f0f0b01030c0501090e0906070e1302040b070c0b07030504050d0c12050c090a180206090105070c06170711100e010b0a0305 71
    0x842a0141c4903075118902540c0c3d0040303905604070564410305101000c1c122110405680a101e210b400030340343c99001c003402c0604560126521709002e412103122409403101d402c05000c0e02c01904107681d541d00130483c0250025000618003404d0200568198a0554106036032500c1e96840e401c0801d2400410b102d02400110138000004191008580c410b000703000007000740c0900c0d103c88504840a84040020940c411080b41245d1b9100300b451005200030580303030304500d4882c00d140c18034403a8600140e005100500c0100f0554000035400360488003a601c04480c0d101103040345003004038000d080c58000c42d409489020303490f402d01c0400201550003420440f44449140d640d07100e1b400580d900c52280c503500d4030403221404018074005010708422036040c5425402c1088079145d030008003005522000100c2d20740718014066183e050040d60b4860a1824242200d003114050507544075008031101f000d50344d40c0c0c142c5407071301c0c0e100b03401503000d03504002c0514100903124240aa00c0b01b1140242d00d8580d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 171514127 1250 171512877 171512899
    0x1507021306081b06120402060d020c0f011b080109020d14150325060503090f010216060b0105040302060405041802040c030f1503020307050613091b020d0314131103010903030b 77
    0x11180055100c0c4a102c041c04c4281456460f030b402c0481e01c1c402030000c90b1b103d10103010508001a0a20150500c0e19040004020b48406440085e013120040642044541c5440c20003842003030b0408079103030442e01c441030010ba0703c51224142600a02100882c4401c0d01c05107400c0c00070303444c0d8030205105a15003c0b819581c1710071060743c100b1040b81c0240700040103001d602e0310400c0114020307005194428285415602031100021095089a00440c82920300c0102007625a003800400d1042a2004400382069440c1c40d00b1078002489900070f600c10144506e407281c00000c041e030f183c8001d0801450740508103100030b1030050320103070142205c03000010b042490112503080000c9001b4a40c0222600903014140d50741c201000c0c441103030b001121510182c00f51000002c0e0340303d450f00c031311100329080d005a81c81c45100294001d040c0310070042c1150415003410f8000c1d001188005040d0342102400b01c140c1800f01d05480c020f080140c140e01580d5142d4a85040c940602d0b405410100e072200084400b9039001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 171515377 1250 171514127 171514153
    0x15180a150b120a1b051e0a08101205030306041a03160501030b0306061c03260a291215010b0306040b0a0b0909060d05030705010c02190f02150702130608 67
    0x300e00b41141c038642e8404c0c50700d100080900410041504030580c0d00c901004201558000e00e1640c4016100350002d5560780c100203824030840c81010140540c02043c1f14821b80e01e0700c0d129500d01000d480c403440790340d641d206070b200c0e00980c40304070300300380000b030300799101584004003180d003410003803246074003203130500c03416082c1440c001c40c226108040080c4034600b81c98024038850552a4500300072814840e95000706106180e0308404c1030711043c82122804824a880700c43c031000e84004805090840e84d080c8103c001c1d9178401150510f000c01305480c81071002c203096241070314002d014804960751152601c004242140141d00561199800b901d052104403614000d001d402031840c400d40760001001c2c40100c0140c035008601941041c001050032500c02269201e10b801c582c0100c004035030705d030b40da03020100355035805000803500c08403081c929211700021a02e0320310131044141402071141c0d0b403440c6440703007519030b9805031034070180c01400300d0f4f02c00b0400c100c5507070042c00c4a000300031041c41804c542d4511 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 171516627 1250 171515377 171515381
    0x2d091c0f02190e15030d030b06030411120303131203140f0a060f0e01090c0f14030603160b030a06060207050105090d050f0303010b1b010204030c030b0a0603080d06090515180a150b120a 81
    0x8ca1341e0f02605241c0385a850303444405c0d0503004641d40d2176002c01120100b200466080029600409803a4045207980e0858604404c1c5100c40100845c285418072101109081408080507070281614100100d55900c0c811003100414140d040484902d81200e40459815180200c0f0741c1641c60300b500400c00c8041054080d140601d4403410600012601d2500505580c5507402440d0130100c06421201d04040c0c4951284a050654004420076203001c02003016506140c0550002080180081c0140c0703400d01c0f00080052241d2503000d030080f8030300e151400801104111070391803203035203005881d12543c480300c02081c036520180290301d0129884500c009050018401c45040743d83c803204440c507a61651f5a501d1b40d03040000d02c541103495442d04e000000c00c0882008200d4441014400544d203802d103040903040b15809444901004c400c003030703001c01d141c49041c1301450b010410b2030800c11030782d200600000a44840c0c6204080c0418541000618114001c007070009491204505075840e541e40e0341581c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 171517877 1250 171516627 171516641
    0xa03021e070b0c0a0501050a091b08070b0f130b040527011403100906233d030803010311060306010f03022d091c0f02190e15030d03 58
    0x11660030040042240b035910310b0080c100402228244c034003075489500c916085540c01c44070003100d55151040c107010054400341404560302c0d00b03805018400d051410480e0b0301d181500a03c07134030240010340c6448140d003040684048611011742181002c3c0c0740ea145807141d400910403240640304814108481c10281c11142c02c0d1242106408081c0b0ba10b0004e00b000d01400000c1c1e41501401807090000320f07103190b40641108580200c0000c01c01950030710318141b4941800c9582080200b4035000e01001070000350b111000301940c00304507103d01031121980c0d4090554403950181d2529402c80c0041007000c51405541203a001e0316600342403a0070141845070520048a425001983c2e4510700c829150090b40941650a84840b80c080c106051001003440c2e000c100c249900c2c1504041410a8149000c6104e17a00c3e0311801200d10001c50302a640d200c00018010400a1158000c00383f050740b01c2400788140c200600b0340f03411985683c101640c28100c3c08100036a103902034040d08400716a064028000e2503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 171519127 1250 171517877 171517933
    0x20601030515040c08030a0c030207061b06150b03070c0302010b1f080408040f03030908010e01150e0c090d0b040605060102030a09170f01020406090905061c021003110a020a0302 78
    0x8801d07040751190040703070b0400030030454512010102c00301c0d0921041018200917003040d160056606110b04002e490400181d104404100c5d40070b5101d00101a410001e41140f544481e0108a420128094201580450b000a14504008010800c1c11940030b40d9030134071907009030001c21200d070402c2c0500c03a8140c0340407002c180d07403040c1c82000000c8030702c600c01a651150007129114202078940b0741256841c0c0507a0b000343d000614440d0140701020080c480c02c021561420300030003c090003075050741c41000840c0b02d480355a281c0040004c880343c1c80c1808a400898004203034042c9640c80385050748280c1001c0c3d80540701540380400040055000004440e8107410f0f9840b00c2c1000ea2600e28403403440000d00c0e0b846170190040202d00b0352181405d0000d040948070381c0c6c407411030460902c4d01c05801c4580003000c1901c0341d21020052490035160184400300070350180c910b2a20071604c040242c1c0a001c2d011543c41c07103500d00081c0b0511069003c119054041d10a90030f83c0e40c00403040da000700305503008401c02 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 171520377 1250 171519127 171519133
    0x14030105010e090717091e0d092102040603080304053d0617071502030f070605060301180602180103020c0304050d020d05060106020d0e040207050a021912051b010206010305 76
    0x81c1d199490840116940081c21385452410b0f12800481e41d40814020f41d41e8104a50001000c01f0074181868800585509032070002e01e6803000d5440c0c0245420720902c40c58080700d01c1c11840c2c02421050404c0700c03003140d801a00038000d00d0741d00d00e4807070b45e0360740103c40c00c0e03c59001d0520b8229011441030500c0d040c010400001104018410000c12a00d50b41c0a0711420095a601d0780041c40840d280e0841485000782005810340900c0c220000d9026003030014840119001003140c0c01c001070300c0c00251110f47e81c000030001600e0b62014082030040482c0f02080080d55003d420000421025400809a003990b201054040c2c1404800540990281c81c0b149521038100b030100703011604002211003000d900003440c074103403003004e0f4031040d04001003a007004005800c138420288a00350000038160701c9000503202103103040229100c050b156220340200a02c0303840c8901c00c01100c131075501d10702006001d40700404e010071000e910303001d130307890741c50860044200c0700000400503550300204809040307039005009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 171521627 1250 171520377 171520397
    0x3130c1e0303050c1614030c0307080601090915090c050111010204050a031415070c020a060f0f0f0203041a0310091404060207080f04060305090606040516140c120a1403010501 77
    0x10f8826401c00b042c10109441507030820004201c2c0303143c81100900c02c402072103400c440031005240c1045195400c941c000c0e40404d5042201280c0022401d04583d442c00000074024924a000d540c0440c01500c101c40803403c0ca4500b00174010340c1a81c000845030f0980f2207402d05454200d0319402d03805184101a441842d4901c1000400d01070700c8042d4040c0404001d88160390588200307010141415604000000d498100136821420400b5010020b480f007404c20341c5a400342d95000400003030100300142d00b00f01031003d09080c01c60081080c2c074003809860000e5502c0c801310122100745070b042100d25420495440c4000910402039200d080c20101680554098540d1141c5941020f036001d04411030307503000e04000740e0342081042c1004e000074040d03e0703a0110381820461392030b520300807014024921440c0b03014203100c3c0c0c1d1022600c02c82004d0f0f6007428510f40d03915000c60104c17144d005900c0004810b00401c0025004022050300401000c5000d40b82d11083c101094140f10840c0001d02a560200e0741e5500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 171522877 1250 171521627 171521633
    0x206010906050f0f0406090c09030b010911070f0201031d03070b06090c0a0809120409090b150306130804030605250c020609150d0e030901020d1b081b010203130c1e03 73
    0x16526002c000060300220706c499543d0540070840e10107003042c00003c1c1d40c501c018010024508030041c010080040700740940c0320801d085c158588140031005144c47c501c440103800f1a4000c1c1c0101090280e80c0114010180c041c04029440c2e600c0420215541030700e00c2c0002d141450040c1c0c01600132900e50400c6c2d81030a1140c0d600f51803030345001d8600e500905c5003d000191a201510080000d400ca00c140031400311009c0c50702d9100400d028000040c43e188090590410340c50005885a000b030707006054a64428403814610b2580c800d0b43c0024004a0400c0100001902c1c0c2050f00d501c00948161a18a240030b0703000200d50040346e04500960204040000640e1481c116000a05503842003020a180c00803000790303e400c540c1515a0081560008610f0382c5156030107004407a840358042c14070218900d44200c2c5900c0c901502c610080000c24080b40c2880f900d00604030fa4000c2c600c1480085640c1d040000703003d45000d4004004580e031050b0481c0204d2a0701400c6c2c100d189100580b101d16101a0640d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 171524127 1250 171522877 171522889
    0x51606090b16140106090209010f05030601140901110f06090f0607210b13060302130b03030d09080708040608190e0607110c06040e010302040f090206031b13150206010906050f 77
    0x36005031140c2d800541c080f51400c2080c85810000e1603c000c00507945c814620001d00520400c0903075000b0b02c40d0900800ca81660084110f14070701e080c0c0c00e42c207a17075415110016100140f5513560108039110b08a404aa0a800000d600740503e452004a400a00c40342c0d0320b4542e0752104075007110000710805421001e541190404c0f01084c2a941c5c2c000c100151403c020071740711060804040e42c4c454941c036042040d400c008181c80142c4000d01400d05c0500000300109a80b846040c0003000030035622040c040610605100303a50710b49912150250b0361b550f40e40c100500b080011317201a000046640003011084110348144069020803a002c0c2c8005e0b41c40d000c0650b0065080b5188104a000e82c8804c800342e075440350b00400160095000d000499415070042c04100c401040510f60424508803441000d41d0b42e50342625844141d0520490241c2241e03040f00b0414041c030846d900200056090100c2c0038140c041e003254110909500f115050703a684c501d506c0030f0b101188111504000c2d14400b02c86941401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 171525377 1250 171524127 171524167
    0xb07050a11150c030307120203010f030813030f080301090b0d0c060c031101060b0a0305060607080301030f1703040b040605060d02012f06070906110601050915030f0a051606090b 78
    0x4080080a2401004039030072680881001c4030f56400000030002101d800501c2e400a0310790a900460031507050003501d000110650001070007007035001c81c2c4401d41110060b40c14001e1980024058a246400e140011080e0000e00803081ea003802e003e00401d040c10083e2800260ba9000740703e0304881841d0290507202c5490700f074000c0d4200898650459280300c000d01454004026256005070b07181c44000c00141100c1c000740029115220030452800460324078801e40e415a900040c4482001c03001c1e141500b0804a80c000d900c06440000c020030040c4800349040b2841140201014443e81d9a100c0c01c10050310403582c1b0007404102c019921503031040c070310700800c0d07066282030f5400d9203c445c4500c002807070680100d131984005612200d05100c0c0c00e6100d0340700344a0010301c1c00242030703d5061000103400d0850007080041290000c2c907480541c1ea404012110f5450110404d48034016018285248c46541c4000c4905450300041000250a4820710111040312011512a410030003003d64503a60059a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 171526627 1250 171525377 171525379
    0x30f03030f0507020f0f0606030307060e240417161203110705010e0c0303030108191e03080a0614090c0c0c100503011508010605071704090204120209010b07050a11 72
    0x756000152844020340309090240d401e580040c000d004100340b0722032a2a401e02016580f50300900180a1603407070010942d055644d020700e02003164600880520314003146892040d480310a0baa49007207101d144000c14600aa0043d03014807050268071036405a02c0c032403000750030742a0b2803d5651801090b0460605400c0c50300314076011030f01c1c14110b20102075a8116800c01d44031a55510140341003a00d08100a80321800140c02460541d1302d025046c9440344414510b02011404112075182044420043c4086444c01c510a030602103d260034001e0007000200c0e6154041468501c0c0030038007002803442c03154003040040032018a9540d0000d880303d20f801c100180e032030380c0c82585240240c030354a1031480780803080156202600c80d8074010f042d04841d4900104c000033300c07440d6001800225840411a03075480d800035203544140d120700101d001c0b144907030ba00c002d42c150f00c08100822200c6624820b00c010500032140c440b0681d03202e4013482d0461003110401440344e0300011982000880081401002c010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 171527877 1250 171526627 171526631
    0x1101030b0a08030c07060305040305040e061903050c0406080705030705010c0240051e180607031536020c01061805100308090d110402040902190c0c030f0303 69
    0x8100c8003041444a4a411004007900003142e01001c110b000c0040d40020300d0a86010701c0f441c1407a4501410511035030050302008400e00c0700141d543d446010701210002c500b60940d203101036990802c0790302d45054140c0d1510079820400002020100000d030a020b46800a001d1f0400c14a00001520950900c0c00c040380c10051408041410540c208180c0003981c04801d8107022410264000e003210a44030540e444800e03240101340076503000f58504a4010b0107040111004e50345900c40c901c0004003034045108075521403d401c001c50030b0381c10340103c1c40d0240025400c640b0143c488407000c03031005400c114003018030540001000505100064882507241c214401864004224081820740d81260051403012141c4001134042d0712003407049580c4255100d0700e103440e032401c41d51001c81d07038410300e04c61030701c030f00e07914240b10081c000082d45980625900500855550355101c46c1c04010350464050714a0900e2070300400b000303680c011b00034035200c00d0340b085450a041d41941c1c0e4814102143d0301003981096 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 171529127 1250 171527877 171527891
    0x150d051213050a030807170403120813050a1410020f0d0903110312011a0c0601030b070e1e0306070504180f020708160b010f060e040f090b0106080f0f040807110103 72
    0xd02d83e490008060740c080d9403225621000d80c103103024111a040c19200c44510f00b0007040010402c441c400e0081c0a001c4c1c40c1c01925520b544a680c0859060742d140038049000f125109401c00c010a00c0c44400c040310203064400100d0108641c00c101c0c003179443c911001002c20041035019809541c80075480300d10a040c01400c20000c1a505455a04071400c0c600c9246209001441400c3c00450001e13481e009a5503520310307292003850b8143d02d484040c40300404002d1070380013007103469004403640c5a03201006401e450460001c10090700344c02c00007c840c0c80c00b9004d12004a85128410300840f000e440d00301607a1181c96024100040c004c009600f280e0444550a100715400100c0b450000c000291a02d001c0800e10031183c01c0c8596030b800c041c0e029011410f01c0e0b400400c80503801c90f00b0107800103000c41e030001d00c1c6d50100306040054880c0400c000e01c43c1c80a40300100f000d0350403890300d6005416140d040219907451484001001106482c0503107614003d000d14000a08000e050001d1941c041c94042010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 171530377 1250 171529127 171529129
    0x71b0803030109050106030b0f01050a12020405060a0206150102070501170402030a0602030c0901020d08010f0b0d0902090c27130203100e090a02030114071710051008150d05121305 79
    0x41d0401e811000040e922400100046513060180d40c030b17020000c81e211855104036038000380040c891400461305100001c80610540d00705541654000c101c080c10250b40c44e50b2070400251181400c0f80c04107464036071280c003003115504c00100402600c03030684444044081c008a455850705000f04104d0b814803d24265800081c2c3d0b50001e507000c0d08440d0100d80d210b8460000281c20100f24400300402c1141c004010001c80442c1d41e54601141c5802c400706980f90419210b2801500c00140040e4220035020140540148075400a00d9070f03107524480c0c501d83c0d85c6411f21030180140e00c0402d266011003584c13000a0188035a500840d0020801c000032403809507201c040300d008503c21110300c000350f040380d03010b501503040c04c1c02000c4840049400d0903109180a400190170b41c44107241504003602d080740003035411001c003444180130b00802403810312513000300c1c0f030000c04880c030851355040005030b2640701d6040390a2a8400c4003070654040042c104c800b40751250103201e5080204ad9801d00741c0d070002e00040c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 171531627 1250 171530377 171530383
    0x705030403081606020d0b10140a1b080f0403230303010302010809011b0203090310060807060509030a051510120302060a0f14010801020304031403220305040306051905090c06071b08 80
    0x3d000c0c1c1090007c24074038490010040c1e402c10303100c50319042c440c03101e50f110300303498041c0b08488000c1c11509000760116920b505554400100b04001400031100081300d81448083c44040e1044901c204c0c0030300d00f0908003098049144182c000d1003003040e4401d1005100541c000d641c1e05600494000000500e8015190000500e4460590700000b40c0c1000a030101c050605200504e040c000000040c0101c86c03424408907a02c10240c0310342020020086001140360b80c0074400030710031079088012548207120b805a181c00700281070b03907481a5003410710000243d21a81413051502c103071b01a00a0030503595564000d8010b00040200030555075980d6500840801c401c0741c6d83d50285c90381c1c0c0f00058692405140103010007512035030150400070b0510802c026009407800b501b5081c070b0b0020509416000c1c600d01a207290041e9003000740b81178144420845d03000c0303510103104d541024044061003191104800e080d00d802c4982d80c410740101d810030444000c00c401e26016020000545e01c004240c40c0d4550306903003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 171532877 1250 171531627 171531637
    0x904020d0501050118080712030201020c060709050a050108280b030d0e04060e1012030e04180201081609090b060c0a080a020c06030705030703050a0906020a0c020a0b070503040308160602 82
    0x8905607a50010302003540c3c40064414040c00f90100003412a0400c40701da40c3d0307844940f048032982c0c1c80a0b002041094800c0d015101c0d403440d40401c4a25604108601a000800c90302815005800e11140014250b22544032580203091018002d0383c5044003c40ca2004001c051180031b040940700c4400e50b42e2610208451a006a96a51000054100c0b103003008140c846a41c026030903070301a2024000295190710584003100c2600b0700c0b035640c0301003a190130780710311300e140d41e200e40e20514180105280165803010729101c0e034800d0741e42c4685640c600001c040007455012044002501e0187c1c1402205000c1d800000880d00080c107007070500312410002071411160040880703400c60081680004c15404001840c507106040301c0c07503429450850390003485400004d000030201500c6101041d10300700c09071b000c2001d96070001c5055648018810010b02102401c4500301d0180518140c001011189042520045c99001c4041c40c41c0501c0d640b5000c3e4140c01030486200c912402e0000c410018000e40300401c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 171534127 1250 171532877 171532897
    0x3130309030821060a0509061201090f0b040201120515060a0201060801020d020c06010e0c03040b0a1803050301060e0418020d05070b0408010605010e03030c0d1107080322080a03051608090402 84
    0x100ca10707101c0116880d61203d000d003900c0c2c09400a10003e01803541c2d80b1030210791010042d102144504601c005460140940013400741441c00c0207c0084207101c43c2d01c500f503200318000e89800300900f40404204080f140111141c021840600e80048894640003008042e103c0442c40085501e039120203001c0d0883c0c0c8050240d140d41c5500040180c80404140b05203070061920605051442c580382045100b244030040004240d001e80400050000781541e1026030b8007400c6d40d52254422442d0318014003158401c0c010800070540c8129407102c05d1a0078001d1041040301980382c140106404e03424442e03010003098048415014a10011844500000240004114a0b4004641c07035151000240040d1460107499010703030400c2080c0c10f43e102000035640041e024901d4889a034841100b00182054175503003110815001c0007580c2e54144201c40d000d00d0b1088460b20407843c007159200e40d019034686c404880140418410f009030b00b02c0c1d400026040100c0340c020101c20b494003030001c0024080368001c1100c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 171535377 1250 171534127 171534157
    0x12151212020f060402130204030b1f140a050603090327090604060b0910090b0c1005010608071d2704120503190209060c0105090a26031303090308 64
    0x41061012480399205045628005000600001c010b22901c0b030200801c003038001c800d020742d070340c4105010b641110700441e080440e80880307082100b00c1d59948003003517204020011690402042c03601f0b044406014003c0001c0c034004140b0301c1c110520409800080c80c100b00d5010610690075402200340581425034403100000100706420300401c015440050001800380d880d1030814484041c100b021500c1104040ba800340712420304103c04c6640460716080750070040750220b82074001800004005014007078a11040c0650307038880c6c1c030441d4049800c541540c000740c40340140d410003aa907000c54145015010340444075517810b100c050003140e02080c06036000c0c5e50505c41040140050110042281481032900600e5400c1806902c0f0f001400621305240351580011814090f5580d04d045814515240c00203002078a8268603158442c60142e1082d0f4070074448035901140ea400680685410046040072207041d5100c100c00c072200d6031b180c03c9046081c0a04000040081810900544501c880213454 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 171536627 1250 171535377 171535409
    0xc050c0a060c05010507030b0d02040f09060f02040e0901110f030a11130e061e040e0123060102100c1b2a15030204030803010506090a09050a0c08090313061215 70
    0x41400c44100030700d04c900701423070000c6109095071403000820000350120390201d200c295001c10b890003014102e2000b8461840c0c0045954017584a0300500111024691010f000f582c1c0c070041c0900b40c40182944504401c803c1009450418a200203940c0086010f030000802448124403240564041004040d0101c801d60040050b96a440d80241d84180e040d10242c200700c1d1088003224040022141c19031240d41c0301c80460480d24001d501041e401d01c034070100307403e4a2010348064442c02030f09848260040c080e114028030504402d00587da80c000e800d580f410121140b280038594010000c50b03080f01c040c01c062060070860301420380303400300f003013540c4004428040c0f814612160502c2112a5101414014001040031401401c2079074111803040e00d125a0300d142100000c0c0c80700085030841d802d03a61808c0c06111080e0392943c0000456a12178503404030f1500c13107185141c0d50780201842d0038801c078644041405018440c2d6412500070071180c10108003d0000c030341c81c085101382d82d0000f004050103445 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 171537877 1250 171536627 171536633
    0xc06100501020c0907030c02101a041107030e150714070501030c0e0d120c02030706020105070201050106030b03370b040c060c0b010b0f071509060b0a150c050c0a060c 73
    0x41a0801000240000e1032499010004101820380042c0b0050902d6512248410f401c0d00921440304010900003040040380b000652540d42c0d507202400321805245072171011802220340c0700440d00e13160340648070f014001c0c50580410042e02d07030078a92040e21300c2c0700b40184e100242d500d0440c0da000d10a01d4000c2c2010b18286000103084034103030070b2142d007041821030084d2003585404c1100c10b50305d42c1107007406041c100c100c5020baa603406440d00094141c410500c0010f551617043d07100c2d9010303101c1c55000744403d0b40c0c0c1d0f950850035106509040380d41074204000210b03d02501d45032000d0400e2020304407a8501c020f030304104003000011082500c69030486010003003040f640c00c1030040640094285a105a4540d403180003051005004200e404000042d0041c1c2500401054a0441d54800c11620342c51040e401c1e924041c00003840301300c90807802c1c80c89040c3c8034a09040c160094500b4005240d081012480048402545518003a1101c0c040c075180b80c155502c0341030480001d4021511b90402c02d00a81c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 171539127 1250 171537877 171537901
    0x30615050d030e0f01021b0108060a0302120a0618030e010f2001020c07090507020a030c030210090818010e03030a030c0504030606060906020f0312011715010602011d0708210705030c06 81
    0xc000d4174119002070794468042e2285040d14a450b85007843c00000556844001c60228282074202a41c03151240038100c451000020341c1111081c4540018040300c3c4403910100494180b00d0b000030041000744031030407283e502c0740c1c4022454502a1503d0020110402585061040c4500d29480c1594000800300001c034003c10054004003000c481c00c001900d04003034029203900c0303003210003000c02154440c80c2007030610800c003462144203002e404002211481c905440e06a00440c0b82c022000c1c021a942c801a41c0a11640079000308098099032402c020141c0850041c142d074040b1605000c82070002002051451103003030042e08844d101c1c2c1c1c0e1191704101c1e0280c0303408528044040154030411840314a001200564ad04441400f445c500074925150380a40c101044c2004042c80041064000640c941d81500403060602c6410b40c04465140c2911800313071646031900404000341d00102c620107040b00159495142e403010b00c82d180e810421a80d0703450b400d681c458100030269500040030300464403101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 171540377 1250 171539127 171539149
    0x50d050c0904140c16020d050f01050103030e03150705092b03020111160303020703030f020304050a0c0b0a09180b0d121d01120905010f0c080109060b13030615050d030e 74
    0x125007030490762a00f540c1c0b0310114445e4491900760310407400040c00071522503602d0311444541c081c040c1c9400b90424000e980c0240f40910060713002510f884000c50700c0c0c1c2004120340c04d00d0940200c815009556189041d281e991043e20b001e90130031002c04464454002031001c060a010a000240304440030500f402800e5031103028075402043c404104410b22003001080e101c0a60b64141405a181e1400342030560061030007249102a03140000100410010085207402d4542e10500c040c082441e101c0c48190300074040d811102d008100104000d200004001d00c640d034440020b0300340410300400290104d10940740c2c07a0350071501c5402e50300704400c003171340c03c00c070410441142040070040226003480000c02040488210350351141ea1012181e0500900f900060054045440c041c003c8214584000b803080c0802d10a10b440145000e90101d08484404116000440d00905001ca80341c00c540301c4400030300044060215000307242a0010701a00d8070088010200d0107a00d030f00000080000034084c5030122 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 171541627 1250 171540377 171540401
    0x603120720012d030f1410060201050903090d1103010603140d050a0e0d14070f031b05010f2001050c0406020c040510140604080a060209012606090403050d050c0904 72
    0x61900c5002c00201c450900400e02c540142002078042c580960030f500600f2520440a0100d041640f210000401c01b00380900030062210a000d6103580e8800480c22644161501d2900350000c00c4604044d02c1d0891508420741d000d0800400c444114030002400c540595208881c1e080704424071130400401402501a071000b0390415903e480400c681c0241107800401400c2d11503503424a00000340000c40c03030951407240c00e010032074910070b03181d14400c0420040d910040f0390429194000d02d80070301a501c40c020031544103858040c020107a074038050342c0400c203060603041110440c418070018032009000320350091001d5004541e50780e0a114000341051011211540540d00305030610401104511540084680400441e060541160b000072032601c036a1f4008205485109804002c2c000c041e401480f17020400d890358500c0c42030200c3c076000e12600c2000302c2160141c2010010700c460030101c1c443c0d079200d4840d00d0010b00d400500142c0504642c8140c0e000d03a000c000108036103000d410a03119402d46540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 171542877 1250 171541627 171541637
    0xa030221010e0f010305100e160b0d32091203040606171b0f03030403050a062708070204020d0209040903181e05100306050303040306050a0606050c0a0b060312072001 73
    0x3065451b1155076440600032a43d61554400d140c2c0348405d4103010040204910080200c2c3c06940c850303850748c843e0088203181600302e241481207180c1078030604807081c441e00d00c5c2e10000d4008800c0300000313124903c01464007045004602c00c038083d04400d40300940c0301d1441120000303002c44c00d280b05200e6824160003400129400103c11450050b039140d00c1240a44c0220303802d00c0400010070101b4114020760748002c046d4800e05040c4c1d0100803054011040c400c90040906451441100c41c02a0304850140040c003420403c11a02015040036002812449520342c1d000d031030500074002140465204680079400546668420340d484ca01002000c40105881c07050000f040c4004100121a42500d2180b5407044458405903400f0500a411001c0200b20044c1525240c0d980d03428001e0250800702c1e9411141460701a000c502140140d0980d280044001c0040c01a20200d0f40e03101110000a414141d01d0700c1482010f41d0091403a800030801d940c8500303529071110707050720345079080240f9440d40c1d241841 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 171544127 1250 171542877 171542879
    0xb0105070f153b19060e16060f080c09090106080601020f0c01020c06031e1f0905010f090f0b090a0c090f0501020a080a0509030304030f05060907030b0c0a030221010e0f01 75
    0x2114081c01007030604400c05005400c3d0381142814540052040e10b80c400200710035401041c44419402110030400030015502c80e2801c41c0700380149410350b4001d901c0410080780c1c0ca01c8074288101603160b44402111826803404050b5000140c040d4001d0b13001e240040c4500081145a580c103004001007011181c2c028414441000000303034841c2a101880d034043e200c003100041c001a0840c0111203120341240c070a5030141046000300d91101001c840000100c0103800001840201e1071107200d04a0347e0920317080c6005810004010060614201340318103031516075800302c0c4255030b0b500d1524003658440000042025403c8000b6100c050a54040d56018000348000c100d544d8000c038500c00c0050b4801071107641c500c0d1032001a20b86010340308540f80c151001041c0881004910010533580700c0c01401211040d0f030340e201c01c1c144d41d08c82d18000141001c1c50040400d06c20300b6600040c0245d038810782030140c18410218251810150b03046c080b104a01c2d0494010040c8840741d4500c190003400c0d120030b000e025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 171545377 1250 171544127 171544181
    0x4050f2811132c1302030a02060a080f010608071202031305010501140f1f0f020a050703030c0c0b0c0d050903070e0f0402040b031b06090409050d02070602061003150b0105070f15 78
    0x82d80000c0c00c9400921340c5a9200045507024003851159680c010300300c0d5140c3c40c029400030881d500c100e4000034403c00340320010401c3c502580da80e034860740c015600ca4408088408994002c2d41003d0300c43c1400240c01c6000400083c0280078050203001c03247d0380c2038244440042003000307105060400c030380207036035500105030a01c10050b030040784180c0c94103000300140079000f4128170b094410240a8002d003c0c1c0b40c0301004040e1321020307210126000b8030881036441e840300701c08003040c070911003552220ba000107490100b0324001c1c0050072000000405031000c540c1c0d5806c6030100980120f039100880c810b050100000c518080c8550721141d0015001015101742404002052400e11020f09100c0c040215103280f995456422150b005640402902c2545614417130280d582c510a0040c1d5016001e460001484215240020421a030b007040d110f00d040020104640014803c08101604000003048505c02090780350f020b40621038429075140f01408980380c08902199098180140756141d2160300c0714a0f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 171546627 1250 171545377 171545459
    0x6051509060a120b06060702030a0305090306060a140121060e010302030d030204051509041104031406070e030307150f020a090609060201050106050d0b010e10090504050f281113 78
    0x1140c1c40070004c1c0707207030b282d041c00030341c0034000d05078025031520a100c0428201544107000d401807a00940071165140c440303c081102048041c001c54401040341d85c4843e200d0343c400c0c109040003800109a100c004155a0b45480588010340c00980005007240c0c010811410100000075030a42c1502e404c42c140303403c00e000104001500c114002d0f083c400031074064455507480c1c0c0104e0084210703030700344c950300d81da6450180303905030b5401030804041c003a0400041ca4139004000c60725200000030301861800000d0380e941540e40204a40085600366076100c1500c00e88160301c014202041c0c152286c0da0f0a80c0361000c0100802d41c02e4019100b103905140041004907001070503901c501091000100ba4801070380012aa00140c01480540c4620f2905524110f29080060503003902c2098800f0300003a551403440902840c030548162140383c650400782c0a40500311030b114200d42801002c0401c0c104601d41403516182c001d24000e403501e8062480802c45184d4107120403e42005038018031a113090091030040b9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 171547877 1250 171546627 171546659
    0x3090801021911030409020a081504090209070516230601062f01020c060709090e0105040b07110f060f0a06050f180910050a0c0f0813120c06051509060a 67
    0x420310004541c20840c040044c400d807005800950001c544840d505034000300000340942d071101e02000c0362018400941894000da260080e000f9120700c9072922400c90448465002c1c0c0c4510960034585604280051020000d02c412a080d103680c01c110747d20809041d604003035041e8030800501144840f04201c04062441100f07401c2103a003803490707215154840c0180640f0618040002500a10341007100694000003040155015201c04100700c07000003503011308030b440588000e4042e05440e000501414400e11020a5001e080400d9611041c00284001c1c600481034034000c1c0039041b000100190302425110b10801400c003107500311059001d22000c59544000346148000c10600000015200c100070401c2e60300c10308141504000d5072a12841c28001420303030060140c0040c049901b00d01d2494030810070140a41b01000040161400c03503903070500c9014010080f00140084c581980003c6021441168410460300341c1c03c50381118030f00100b0203100001000503103d80d074001d4007403211001d60301001c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 171549127 1250 171547877 171547927
    0x60f0d051207020a030803072d0206010b0306030a0c030605071b02011b06150602010902040b1005030a050a090807050307050f0f0a030806280609060915030c110f01090309080102 78
    0xa40c2c501060000c1510f901c02504041c042241c004140000d4650000c1103980940c00261500b000d0b502c03411001401820003000c00300142d00860052002e002030b5001940c211800034111400c0001a0383c0744040c4889592082d11920b0b92001040110741e00080d441890b03c10520146030311071880c0d800a0515500c0021410300605030310700e41e01c02c0241a6014851054141c1c5850304059135441d40280030b0801c16508a0055007007940d81c403142d0401ca4503c0158402d242c80c0c841c02c0d41e8481c2511002081e004202d00c40c2d903903c80880700040341e0300300010041180541c3c041e41d03580803c0d0400074079011440390f08032202d41c80b072180d81203895000302e04240b02907414541002142c640200060440c06040e00f103200c2910f1002080101d1082d4074500400c54045031203152480e681c1d040c050703403624003a00c501c001e00c849003406a02e50510130303171141d2940c2c2458180305900850140e40075107452161a22850a0780d03480721041c050640041e900e42c001c0202c40020352502c0180752a2282c03c02c1c0048200c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 171550377 1250 171549127 171549163
    0x302030601020c040501151103031314190309090b01020a0302250e1015020c0a1202041d030a02120c0c0111070305120a1b0b0105090a02130905060f0d05 67
    0x8a440ca078400c1c403e4481e4124000d005000958460080742000200c6016000205400d2035115540c68004000d8a11850300480b00040443c401d0b180d0104000303810800c41e05a00030700700d030f203040101c0340306107071602a001e6654156a10708052070842150390303041c40c0f281554030100c0d0507400240e000400c400da1001124241034403d90700781c08581c0c0c1e80081d82006d1103031031418081200802a1002c910308540e07450070040c03104a1103040590701d070915512030b281c00c4500300205204184c61481000344007440900f0024070b079006880014600c04c40440b8400c019000041c002400583c10000705040324138032403006241c610f000c0a400e0307480c0c11801712203051050000000c25540c10510500c00116001030941d0300c0e081c1d414020182c154804c2501da0042a0302d82d440c0800040d40c2c0f00c0c07000c85c00d54010071001039a401c00c8100b03c0700380c01c001c03d0421119001c00002c640014030b800444002e1480c0a404542c40c1032882c20001705801004401c0d00814400b000140410780c001510fa48981900d140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 171551627 1250 171550377 171550381
    0x118090c0501110a0203030408010f050105100c0204050711030307020c090c1305130219030b0405010605030105030a031d120a0209011d0a0c020a0b0114090708070e090a0e060108030d0615090303030203 88
    0x44a410020032084c00303940741c000410001086801034000c113081e0800c40c001000340f6038a603810081c18005001e82000010100f880d11001418182d001d0394101055003040d640d100750304c1c0780e2186540e10480784000103810038510740c1c00b2030802c0d80d0450f8118100540060801980712119095002d007440358a1194944032510401c0360b05a0b8102c8024501084000c000c0e5942004060003601c0ca4044c80342c040c07231818000155141c802c000780d905856008001c0c2a8213801c42d02d08840c080c2803122000b00c00b00342504d078422250b8030307400112180701e100d401a001c0384681e070040142111050340060301d0700124149110891100d2441254480e4080b075001401c8041040300300c1c94900014002081100c20000218403000319189002c0060070803150840141d071890021107241d04140c1d10000411101c08005200c1d2410811459200707612010000d5000b810105603842c22400ba4450310300c5400010f56032528a010303018200240c841c10300a0410a8008a4028500f00a0f448040c04055001c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 171552877 1250 171551627 171551657
    0x90b0721110d180b01030c030b15010e19050919110f070f0c030b390d110d09121103130506031e07050d0f0504020d030e0604090f050118090c0501 64
    0x4003041d20035070441031a40445d81c5a05e482544014140810343d5015203401c0003406c06140136140710000312061752002c3c0c003d440c01e810320600d500051a403240e59110402c01040c03c0c1c48401c0c145110b503c50381c504198024482d84a80201c07140034028810706201003002510401080741100c002d1a8841e1650212078994146000d6a035550380006000384028002d00005041d10080b80020101400482c000d41c181d41c1440007483c42001c540c05410b100600884104611580c00303101011583c00c9803130f20b0909052410021508081800c070b0b84440d0403007004035610340c00080e0b804030b1181e1900940c5041032840300c14428203030f148101481401c0c008001083c50b0b45540250f12520501c1e5080c0384682400d61026005070048160407405502c4c2198814800030140034880c012a0080d14001d0144e5083d1000c0b80c6400309249850f0b0040803c0000040c003220a00c43c3c80c40c45007400c50006029414a24481c00b9484092101c803e0b140c102071656020650004008048840909103240c4813440b0702 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 171554127 1250 171552877 171552911
    0x1404080a180b0a0210050106020606221d010c091d0f0709050301090c0302010305060d0c1208070c0e070e01050c060a05060310060b0904110406081801090b0721110d 72
    0x82c00c03010405202081e42d440440c0c000550444854800d03400703004076030b00e07042c0032039440c8002c030b0714950f1000000241c00c09803456085455070400c450180400c04201e11000303031301d03081c1141ca229050340e956540c40070305a07540b0818003000340003020481e0140c0407108200d2814241701505c04916001c01501040d4964000e01610000b07000143c0240315120301401c004a55516a120070781c0880d0609000400c6454001800c10086a00c100c40b12100703418800048480c62440d60101c603080c08c208003481c0400c44400d0864010084600615200d240035803000740340400300300d0018103104040c004400c0c0440d01042c40b0b644a0f0180000040d00d60399140020300c0d017032401080505035880c00001086a140000062000308001d91b0180b102881e98207030740041e4400c52103103c0002d0141c501084407284800c1811001600b441d001169000c1e0688414420741001c0d191180861084140010384d0f14190340c0d01006103060800c10040c6e1001440c0c4007283c1e200b9060300300400e03a590720740d46409503414 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 171555377 1250 171554127 171554129
    0x1020c0a030605040b0109060b22050913060c0305040b0708060a0302040f2f0712051c020408061e16050418060503120703210207241404080a18 63
    0x1018003010369030300d04005004142c29501a22102480f00c00410080801e014080c00c0310b503619191031030603501c0c5090f210001143c0c05081c0b404600c0c80c20010709555600e40c00da02a0b500c0c4041d17211407001d94a4020f0460740d0307101c48a002d01d42400200004a000007400740d43c44040ca06115403039a40e14000962001c2c420b4000a50103403401c1c802461900b42907100c03618011082c000b90709056041604070100700c0706040d03040c00110f4104034000003e94142c07045e100e21034203814140e050003c54810345030940750241140200650228007006910420002c160300302d244001d40c07081c1d00e506007c038401d503848000e000007120080c40e00720b020210f1280e0304035002090304018800d4801a0029000041c2c080791198034820710610340000344c140001411a0561941502c03400f0080c603912041c0c0343c08403055452500c55590038001d820106131609032034900010326119440e031000006903c80c048034510554091000d04e088200400031b6202c5c011200007048604040d2455403070761048140800603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 171556627 1250 171555377 171555379
    0x6030a11120405030301060e030a0c1a130305101d07270207050105011502030a210e010516091e0e27030309120309060a0f0b15071203050f1501020c 65
    0x2142080005203c0e0200145050714003650b03070a0743c4400090205a500c07a1590406003d01c002400704210240b00c6400d0500e07820b0580c0002030400d64642c050041c01200c50b40292000e400561503d50700359070920411081140f10348401841c162140381003a0743c1d03aa43e0140c840c50707130494510701d441030845803030601c01c00d03a44080640d030394407152134034601902081c0700300040c5013080304140c01000d0002c070644038411410f40d01d210300100400e4045403401011130300c4071220750765030995048426080c007400340309411065140b4800c1940300d00060044240d03520030410304201c10b40d00720b8003105a42060007254403104c0e0490250f02c4036442c510040e00c2122110714034142501d0340280042c4041301031889103941409540c03011105142046562004982e007031240c0d004440041d0240c2940d901c840742030800c904000850b06041008a1703c49020001c03148042000170034017030204501100c0e04816403400d468140210f050852100000c02400703007500b0001c2d15203400220a69108201c18003003144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 171557877 1250 171556627 171556657
    0x10b0a0509041e02041e05010806010c060b150a030b0f12070302060f1201060c050f010216120909020c010b0a080304030c05060c03120103030e03010c170c0f0904092f06030a11 77
    0xc0c5e5004200031b945e50701c0720754000c0602c08620000740380d8058020540301c1d00040e128103160118a41e01c200080c280e031120140c0c0449134100e14903810644d08058081c44000b51000034408222400f08502c1443c6484254424240c9640d507000b09180030400c44103da42c15503100341c4503170741401c4417440c5001d01c003401030100d10303454000202e4035032003404a1541800342d4151650000100c0030b0754243d1080c0c0004041030052000c49100003031960006185841080c078200803040e1316012070400766880845401c080703039111a074250700e615001003144020404a00254501844e6507a102c110841e00e00c22a40309440225829990720003d0045625240d140d031044c4120b580c5919025000c62401e1034500d0081d81ba280e007180036207009169825a41200b0190f10400ba61800c181011551261400b00d518003000d002d070441c3c40e2558003421411030f01c55021010f000350040803d0440b208102c0080d02600f0806103c40c42da13460781d1048a8002001150100761010340403001d418074480c411641800300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 171559127 1250 171557877 171557879
    0xc0603061c060207061107023d030e0d0503070f050c030304150f05160908010509060705091f120e0d0e090603030408060405030306030d08010b09010509040905100b0405101a031b0d14010b0a0509041e0204 89
    0x75600100640c400e842c50344541c482d5148100e8115940d0080f11240d000c103500800101c0c010a41d00c40110503800320504012030403000b08045803050704d00c16194035038426000034404559d1908404004040c0034041c008005604c3c04120b015580c20000d0241c5c02408400605020907481c4e40400082c01c0e00c001c0040c50f900f040444000b8055002c90002c0080070303152451350109200b02160f5042e100303a030b07030740e407a4034440c4c0c03d078200b080c100805070071550b041c0700800001840d840c00340304880c400c80c0604003031030b26480d0210916003801d6010180c4c90070004080014400c0b8107005040e40c1010b0342c00e00c3d00341d881d040d60102040003400d80201c05450781c490f4000c0b810100045030444066104240c0e0184a25214002e03c0800c810b0716001f410064a0041003600032010000041c40c0e015440c0328140003105d56030800580705a1040c46c4d5114284c2e1520b011a0500f141542d145006020004849150038038440c0028800d000381c8510318425074640400104803821070b40c08800c903841d100c904543e25 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 171560377 1250 171559127 171559153
    0xb010914150c06010612060b0d2c0606090618070c061e0902040b010e10080a02070b010b0a171012050f0f030c0c0603061c060207061107023d030e 64
    0x60f420034440d08000462560714400512a54007802c0121002000140c0c1400100d001c441c001d445003080e40080501c548001c400750746244507941071700e036618030007425940c00e141c41806401400204170384d0041c00c03803405c0c2c0b607400e07200315207140c2d40804545001b001203507651400502a004e481981c100400e1940310001c2106469031221480324030172903080150f51032403401580c0b841c2500ca0080c0e80411440e18800001c0d00a030b04056102041650042c41c201c196940c41c0d20114003a003000c0310300c46010510a06203031b00040f90511401502c00e46c0011864044414294002c03103000303440ea04207608a02a080100400c510300c40c3c504541c080da5018a07100c0da81640d80d800c03184003511244100c0340c0d4008142004800c0302c1c090304000d0f00c0e0315244003000d0400001e007005000111552a820000c1e8008900c40d8407a5a207444400b50009540e8102c60040200c0010540310400b103006200a00d00e180760070b070010301500003600300070042000c1a0020198001e0016180340400da0050361400849 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 171561627 1250 171560377 171560383
    0x1803081302190518160c0206040b030112030912080405060a050c01060608071713061d010c0c0c05031f050714040b0c300f1c0b03060a0b010914150c 65
    0x95500c15111080d000c280c48013041c03000e8806642d000c805400a4002081451080d03842401c0c40f4000352401e072801ea6a10301000c0c03170390700980c8544c241c206151404020194403010450051040d85110382034501d03075440d0041140300f03500c03416200703a2000503c1442c5a010302c0070340d5000f582c41d200070455150f80d1100a40003120407919040054010591000610b0141e9282c034014500010040098091965504000c1200306056900c5002c281400c1340b01003424040c00004409a0340c0f281c0d170501d054034241703a0964403500710512036008101e0240c0801c200108206241569880110f0180c451003c140c0d0744034440140c0740150390f0001408503036142e90314010300c0c004013018105c54010004000401620410611b2103a01c1c1005201614194580201400324007800c2c0c3e61291401d00104071581546810200ba00f21058489022007180d00d001e01103280d2105110750103119a22018000800400c1a40034004549202c1400700b11240c540c02608d10002d003062820564503580c801c10307595 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 171562877 1250 171561627 171561629
    0x100503011404060c09030b061003060b0a0f030f092a050303070605061e0102030703121416020f010209010e0d0c05030d12110403020d0305160602040f060909180308130219 75
    0xc0035030401440302e020303602c03540c580c170304403a00030180081e00e8aa160030490700403441103c0e2802c0548032200450081c03a4240242103089141c1c5417022401ea038840081c0aa8003a00d030f01c1141c0d60315044002c804124030034811a80d0b1a00c84101c078603d5003040014240c1030034541c00c1030345c0611000c1078210401607280d100e107008680c101c1d0494046100540c0c40250340c00b40030101030041c1c1080c046180080d0180e100c48010482914000c17950310380844800f0150780f030448420b20407244400070001d0240d01400315110000400c4003d5240440d0080040c101c088401c400178080d40015821409002130640b0035030103803d00505807054a900d00074000e1403100388011a000031480c0aa00580c50404801150122540a483d4002c08101c903241500d07250411000506079042d00f09003640041c003a44000c0c80581605140341012a0500070001d104640c1078212144c0c00e0710f0603000d405000309103a8031114550745803400c1e04069a49045404690f0040d150080d004500e44184d0f6a80303d005200400c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 171564127 1250 171562877 171562883
    0xe030f0f07180c021f090204090b04060509010b0f1003060f030b1015020c0904020f21010f06080307110105120c09041103042f031212010b0403110603100503011404 72
    0x10b612042c40010449210110030f00140c1d2049112404440f031841444010b64030040c400606c01170141c000c00c0541d00401c0c4101c6081d0880b40400007040035611840b0782108809000308001d50b42440840d410800849029104551010300c00c41003034404e4020001a00c000b00900046503030304c0c035040c00842800e903412409130401e0113021450010740480ca901c4c0c0303109540108890869242481203107200070304103070b8101d044c0f03e0805400b43c03582c03440312444056030304182d4010100340c110142190f80341880301070060f0800c074041004000c0082555a02d5411a40340074020743c0c40702c0180d84d40d00c101a83d000f014204507040041040c032a9003d80039680c401e81e01446094a200142280e501c0708403402403800c2a0030300c0405001c81701da80d012400c0d1000501c4070805c1c082010001b0302d0890380114400303d17040f0015052544e41c0e809002540101503002c2110300341800d5955054002d08411001c500594001c0b0010340c10501d083e036210010000038008104c45015502800f621410484041e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 171565377 1250 171564127 171564149
    0x1b0706090b030f0112140d080f061c02120312130501051003020105180604050402070620030f181606030917031005040b040f1506080702030414010e030f0f07 69
    0x41d28200074000c480c41540011100545603081040400416030006001c0c0d44d08503568806200c8a2001c03c0400c103440d0040d140d940031803402030812610010700910407409030001901c2010082284d030603d07046140c2c111000111091440c00d59861405444045100c0d00140010b205805084108521485000384003c1c45240d0b100115180c80558a11000f40024020800301c5c0000501d24551080d11300c00a01c12403074141d640000900740d802c414815502190707075044020740900d0004480150306507065806007146004410030aa4280c000c1844041000c9180c543e00c0012702070000100c280781c400c5101039002c0c0c503181e000700208000e8504a0700700701d0b030013441d1050710026800d07244190f8580f01150200c0742040e060102804106201c80d13007082d06d81d103140340c0b4040c29016050070001c15040d6a0a145e140081c003e0a40b0741c00781c000c2c410744d0010401480244a403400e030180a03d401e08000090071900f80c0800c2c6001c040000703d200c5170080400280d040071300032a5450444034042c00e8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 171566627 1250 171565377 171565379
    0x150c051207030c0c02060901120c12060504050103050c01200a0b0406143c0109231909030e0a060f0906021605040b0a1d0a180b010612021b070609 64
    0x3a022a0a030b00c43c51000b10f10550b60f000e00620b811402403500c3c480c10724000407402d07811104201034500403607a110105445440e0f41c2e400040a20500c4014101281c0c00e10043d495516140d4840d401d8500b42810048400c60500350403408078003202084207020202c4e02d030ba51850412071544a07043d03404079070060900d85409034800c141d441d158068050b4a04482883d08041030840f440e100b030094103920001440d846410364465165010b0003001031600108003403e0080c070504c0d0114840e4288a8003500040034080c2640c28103ea103d0408903000b00050102150304058482d0240800c0e1940d00040c100d501080703040d848940200c04012980b5001c1d1801d40b0707548203980f0b500b80f00d4651882c44150706000c00042c50035070460030900320040d15801000c0d8445503070003404040e003140100b0840300071050100803001449525401c0710500c5025100007110f03607468191840c184079810402641400f00350344104980c1c1110a00c010b44110400200903e03180e20340c84114500c107100101e0030090b8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 171567877 1250 171566627 171566641
    0xa231903030f060602150601050a11070308091516080d060e0702010b040c1106151c0f0b0105090103021c030e03030a1119170304030309060c05131401050f07150c0512 73
    0x20311b02550a43c20b42c0c5000700c60366918011100f60300005aa10208040200c500d40e034041d081c03240c2c80146009841403a41c0e01021024841100c60b0960030101409040051004003420450518800c9612269856949020810740303005480203800255000c004042840940c540550244a9084090782c00b44907004a20005541d0001120079803170f122340200300080d0480c05001c90419001c040140240e010480216103c650584803a604455640a441000041c01a040c6241c2d0050204580041d284c1d03040d54046900c0b01900104240b0341c0340102c240f0000c0500400100c06803103c0074040300e4807200c40d410000c040c0c0380300c100315200e0783c01140d180400143c1000d620202c0280c1101c2d1020fa00007000001c5100d65200030310a40816640740d000c00000b620500820340352110b243e0f00c80c0d40703d403c15140440300039003035444030714450388843d882000303070741c05c0b0050312003070640ca090181e200d00d141d0030042c82100300020700c050454a03041c00350112a070040702902d0343d440e001c2c41507091917440b08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 171569127 1250 171567877 171567883
    0x40c031b031a06130816140301180303090f1e030905040c052a0303070e03010e010915090201120e030304052503021002030c0106080705120a231903030f060602 70
    0x10010b4003078000d0040d003034541030a05400030a030000b1001d07004822540e0700e95030b060030488032004999424254000400a901c13601c610365480c50003c900070003c003041c514000e4003800d60480c00074141900c5201c0b28080c0102c0840032030085404c06169003200b03503000e10749004a040f418040b00450030284d07020a583c101031160140c0603a1940b81c10703141050f2084c13481d030b0310003110280080380c448865841c48031070380520186015104548800d0f150311a040c4c1094250380c802020b400260b03140054101c040b4010000710039000900c1003001843c4007044c00100c40401c1c2c0c4041100030030f418407500000d03090001000f14451802441a07450b009a00301d140c20448054405400c03110005003420f101514000c030132004440d00b00d0044078a41045050310a0a603240b0307600c03218403500088010402800c004000073b13506c0b5407c0d00a403c040c00c06e9500c2038000c01001c5c0e41031103038214a04249210104c00c006000c03210070200d1561240300c9a03407038001d01030003120703050039011424801c2c0090400c0c000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 171570377 1250 171569127 171569141
    0xe0102030112020f1c050606100503040c090b04021e03041b0308040603020a0e030d020f1c051206030a020d150f020a1d1f02100e060105030601150e040c031b03 70
    0x3079030b80445903202d0340c0070400c000d5116107050703031300480554601d06142c0910140c0e20010b0701c0b80c8090b04c12031400104000b4000d201009030740a004041041100055a010000064035462000054803140f500c2c00b007802401100b40000c1036541c00b00c4403860944054001e1845a4400c030b810011050390954582c64010315440f0082c10184244000d000180c003e0300a8021580c03c1c3c94140e035022801000130385004800304661000da00315000103412201e0a02c0303003a60005002c41035010a40e03040c00f0007805d6100c0d0b10840318080100301d01081043c0d4003032040703081c8160010070071401094035080200701d00001c480105215850100350300361144850003607c24201e1643c0351604504030007001c4006480d04118140ea002c081d034088448000903040c84495214140d500800f009034013900d8441c219007082180b00030540c0410300401044c0da0000c2c1983c15540024a41e00b090f8501c14402d40e0901d903c2058654018205000200d00c2c1d540b6a1046a10211040b1908c40740daa5282c01075003140e501c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 171571627 1250 171570377 171570389
    0x1150303020a1401090f060902150f0c01050703020c03040e040807020a080d030506040b0901210213020702012a030f09030b01140f010801141c0807030503040c06080f07120e070b0903010e01020301 86
    0x29910030000481c6181d440311138230070700140c88030650380358000803154698041d035041c0071301c580c02003582c050015003482035942c00b0075541030031032600020513002c90faa40118800d026400c061800083c0420640d0002e9945055002c1c2c04091103980351440c0b1070b00c58551180d480c00191501002440c10b1429001d4008410800381c903040b5581d080190440c120a201001000040c0c4091607010068a58400400600c8403088005889400c14400180821071101107004110b201102a50f01c220b811045180c290390705007002c40172805002c60545000000f40e2010300344082c00000014010080d244141101001303c0b00481d00d080c91400541f0201c10038015040342a03e441002c0c801403d1003d003e0b51243c0c41d148080040003142c0d9620b051580c40708070203d0001350b02005110401c0400382112020304428207001030246803c1240c1d0411441c0100f800301000b246480782540b0803078541c06102440b44036825175121645818401c1000d500074072819010b0361034001094031014041c401d6a0513540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 171572877 1250 171571627 171571643
    0x3150c0212091807050c100b01120b0303040605070215070f0c080d090614070206070614011203080408030a0608060f040308090706140903010204050d060912050a2001150303020a140109 81
    0x9a400000c0c1c0c0f410000500d1601400400c10080744c4e403900030008420380181e0900003140750029180014080c20f1600705400040d41052682c03415907802005071402d403071045c640b198403804180000781900d03900000044010f4800100c0b602071207500b8040c9000d050003082e02c01040c9950b00790855440c100c402d418000541c8110042c0b10980c4180110454400480401d03030401010350000340c0c250340030301000c4504590300e0550314054030198450714010031401d4102031040415807030142044100078002800c602d4000001184032004d80d10400c0a006050215a41440c0540d41400e101900392400d40c045103c143c00902080130010302c0005491580d0b0360304166685603800c16100e900945199135065400307020104080d00c40300740c60b00082e4002d00000c03802c680181401d1a100500d4141c40301045000c0040d60345268115003e0484006014080c520210b03424a02c58010305100b43d041d103041c400c1d45000000d140c2d0024090b528107000b980341103500540020f00a00300c07a88c9403402044c860f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 171574127 1250 171572877 171572899
    0x30c010e060714031308030309060112020a061b0b0406020c10020a0215040614090d0f0906050a1101060b1812011a0d0302030f0418150e010b090a03150c021209 70
    0x18243c1074128026101070002c880c1071482d02d21240303415240c01d0308010850b60010081020001040020034018220503000c1c14440407140c0205860000301d01800b000d2040f0101108552030b203c84443e40403039040001e010160500c1e16000001e0352043c40b0001740c51060349001c50041d0130901c201c41081101303400a016601030641c6400754120014402d9944a59648003220b418190390099031143c11a28003400f020381d544500034000784086480d280030003003a4007042c00b01e01d0700042240c004804a007451191000ea05080301d000d420690000c01aa40001c01c2e201d4440010b060105542c81d400c80382240e002940920250885a04c6884e851410600030628403007400c081403501900742c0a441580d00e13006270710122004562160713001e1144003450b5040608500c44921515001400c050442c40040745400341141d000324041c01034402c1c1e078034001108411565404001e4005641c1b00850a4201d000507200034010700160741907001500403071490118404a0f20100c0f40f008030010300d220007030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 171575377 1250 171574127 171574133
    0x3160503070614090306151f05040603050c0c070303020c0f0603040b06010309030504210b0a0e060403030f02070606260307051513080c06090d0914040203130b04060b030c010e0607 79
    0x610035603240c207202020f04200c204420b88003801610304c07400000080640002d18032050100a15400079407179030300180312501c81000c41d4000122001c40b000742c41e0224454075071b180c0020071442140ea44502c54880c403d4004209500807540c0c01002074102d0301d200c034030840e0809214440c8408c0ba4002c20300040c40c0001101d660081d80090440d900914081c0e0500e500c8205590801684150700034020360400e0001042040c0348034125404449448140000070401900950311760f40500001d050584a0b0340b5044540c3c6140c1c142d032200ca4200f44144541c0d6070b01c0c40ca070300c0260502c600b8510008210849403100080000469840a6200001382549552603841c1414601c024091298503600102c81d01d000c20440d0000d00008031009000d4005030800d0702a40b49021400c2e403050080c40307030f95807080007a0b00d03450b00341e0106100d095a0150392660b580001440507502d0400040c00341541009102c103008081e400740a05440980c1100d00000c5200015210302c0710406610f41c2c0481d04000030700c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 171576627 1250 171575377 171575387
    0x90902040b070f030e03030408010219050c0c0f040e10020403150603050a060b0310020c0c010306140102070902211f0503061b070c03022706060406090b03090309030304060e031605030706 82
    0xb20034000e1400c0205817481d540040c0c10f60b8001d6000030096900070460440f41588210308085d054124103100b850030403a46101034403103540458540c42a00200c910480b1602d0b103070040401d498a5000f030391090710310a0104d40007900280400d5030000e15042201c103804100307120780c0d425a43c0000c020300000303640350354140180032880480e58141c01030101425004c0e1a03030001e06a840c03580400382400151f130390b00050483e2440c2c3c2c0b15004009004610001c07903600440c1007802d40300052070160b070700d03505010607102c0704940c3d00d40b0f194001070702030820000b42c200d542410400740d10b0b481d80c1251140e58500b05566500c060311401c610802c2404503020080c5220010444d480c802c0004801c00c55403500040d550701c102c80a01446d0022004002003130481001c011a4890307000c5549500f0281441401080748515008900b0f803c180040410488032003001511030307900b0001d0440c0e41c0c41d0b8440b40e00400107840034038014042d11580350403a0181000d11070305001e40300d025008004041c5407201c1111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 171577877 1250 171576627 171576653
    0x6170c040506070302030f03010f03021e010e0d020a080a080c06010902030903160201020a0b010b0d060501030204231522050301020901020c01081b041e05060703080a09111f090902040b07 82
    0x4c154402040031101c1481c465010354003d24a85c24540e40461440c01403204170ba410996220742e141c2c29200c585a541e130445a010b44190f020f0703a41c42c01402161010408882564101174824401d600f8440700b000030f0170000b89680c2c095041503070782590303807524010164041540c440d212504140180109407003580581140c5074014412100d0900150b103842007203641c00c0e00042068800050210444805805060000d25003881c003103145c140b4100558610400300e004500e0901c540503009603040c2c1e61802c2280303800700ba8081c020765401c14420080380a4003030b0101100e299083c0d5100064900e8184250740b562441a0083c0000038904401100c1003c0000c00041c0144941c2803602030200d40c00e800360000d8503000c40368081c546944401c1c902207030059071100d4854902003180900190740240481d801c20b2903020081105441882e003500401c40d0342c0d0000d074002120b046540d80d40701c400d000015011109407984001c0c1034842580300b003a031040b406500e80c80d40c1c0c00c115a0000a8225440c15 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 171579127 1250 171577877 171577883
    0x191208070c0e070804020114090a0308030a1b08040b1003030f110127060f0504031e02070314100510052d0402040320180705030a0f06080706170c04050607 68
    0x420031507110910105002c00589816000910082c108021540c101a1025846174055860b0742080c50220000b204d0038694000201503840100c04141d0480f6030b6000704648281c1448003000ea100540c400030702c8520115019100c0d4550900451001c5464540c48030603a50141c0c1d410b903441d81000c00659040908280c0801341c1c1d03584e2042d8041186042110350403403070036291403162100c40d5040c902d0555001c140784041a914000600c000280c10400000d44000c0c03d0503003c0603005050f600b0b034102002944040d094a10700075440f4048103010603604d280c12640c000400003a00d5400c0044841e0400d40140381d00300502c0c0740703107a0110440316034440b000c50072034891003000c801c1c01000c00c0981c0c00a5100b140d0082c25040540c09006042c5050075504e0019101c00004211302c1c01c05100841010f402071041c44130000c0403e402c0107158008034021100321105100e07041c1d80d40501590f46003248a860300080d8a501320a08401000b99401d0050444075001e134245400d010420581e40d10041c7c0031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 171580377 1250 171579127 171579143
    0x91003090c0e090a0b0906060603041202030405090c030103050d2a050109050a120912020604030204050c120103050d020d110303010303030506032b11010b031507230301030219120807 80
    0x350780441e80580b5442007a024015020079403840c90814000c010140000c09203400090800002e40c0302c1001303480d031040e000400c3c40200c840ca404281d0035442260070950b001200c1c44100007215401000944c1201c1c071070001c4070001030400404560800f003d0944210114504400c15003805004014500755401078000203401411590362078a0a048410100c48540e01d411003a01c0c00e0f071300051158000d01c2030480441c4404066400213905200d40d0100034411952000800c81d80d46c00101900c0300461000d143d410107503100c2c2485952044250111001072041c1c40c0702128051182c0c1d000120440c220000f941582d0071607070250060407005000d41d41621030041c00308610403412811888404850103503c40e13000c100c1c04000e001c2e160110714210144e040141d4810141c41c001014004003208404a00c0c003074480c00000c030345000528441c0003c8492910341c2c88022481103000f941200d20031580000604e050504c4010340c80c1c0d451040e09299140d4a0030708012071101001021070500c91940 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 171581627 1250 171580377 171580379
    0x516020f06041130070e040c03030c0311010207030c0203072108030403020a050d09060201050708160806040608010f0f14090307060911040903081f0f050111010e0105070c1106091003090c 82
    0x10911142c82c00b404020b14400c03542011300804101444010082d10621003a03222900d0f00b40c4079200d01d001c40344401810080c4030b41c000800c2c1880f42160b403c52180580080d9903a00c61800d00030104410b500059100b40140b9000040307085040030300f0070440860b1411800194280d0704e807941c1c2c40d00010026800c0d4080c40400200041081c40b0104c80301c14241c40304612241080b2000f42100d000524800c2448180c40512601c8a60321820000c4041185800c0c1d60640c2c1f99000304000c1c09003a0b011a1256080c000288901501034001052140d0000c0e020050f101d03000d00134001020050322148255001040b40c0008034105070007800700c2c2030080d00c0c840c2401c102c1501050455105c0c0d00b0940006004a01b402918401d600e502215038100000c030b0403401d41009800040c6081c540303d914180031402c1b0304040184c5080d002506085504002080186803560018050b1030361a8401c9a16484560100351a882d00c1c034241d41105071701070700041c0d414000b010103800038505030006644041c00d00d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 171582733 1106 171581627 171581659
    0x10506010512040c1a04031e030c080d0212012c060109150905060a02150a0606050a08070c0c081c050304050a030c080d02030a0516020f060411 63
    0x40070401c43d803690b141c81501c0c00081d5200da400450240000102c0417540c0000c0d104807402860f413003250b5000001c6080c0e180098400042c041103d100c804004104d000d0b01a0440100b8224014a0580f0340b0805c0c6882203402da01c190313090040c004c40103900c2400d4910f0b07000d10b408807076030b07682c01410210700203030896140d40600210000f0400c04401c00c1c6109481540003000041c2c0640c5e80d99825903002501d41460f42c1d031000e6209402d001144c0c180405114070011611983d8506091204090085541810103041c0300c00304401c00c1b4048001c41c440c070200100a0080c0e0b80180000c0d441e5030024011451000055414803809108210115401180301c001c85507052904018200c410300c1c011680303005001c6c03280d02c1c0c1880801004a048559407095009400040d5091007200c0d0007601240d139200c460086000e59046a400324000468a01980c40c5c501c20040c050021401814 = true := by decide +kernel

theorem cover : BRFrame.Cov 171402877 171582733 := by
  have h0 := BRFrame.cov_init 171402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 171402877 ≤ n) (h2 : n < 171582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
