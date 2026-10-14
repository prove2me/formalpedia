-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1309
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:17:59.271858+00:00
-- url     : https://prove2.me/submissions/8ce7574c-7f19-4e9f-b37b-5a82fc753233

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 235251798 ≤ n < 235431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 235253048 1250 235251798 235251811
    0x18150c0c081305180f092a0a0504020c013602040b030f060114030c0a030c05040e15090a0b06060a090308132303281509050a060906110702010503 64
    0x4550b50000214000c0c1c0640e00e80c0c001c02c2c0d1080407028041048046013032442e00c10710320b000142c912a103414010326074403024160b0806072406146000142000c1d12440241c0d001000b030032802507070b03071130b040010f05a81000e01c1218890b03654a03007513611584079a5421440d480103450103018058103012000c044021040043d014a44a924404d0079880800c005055004c0784826186c40b541c5030029010346070215181e0700c1c407900c03c0d040c1001007480c2c4581958100c1e580304442034030045c03400061001070030901c1580910f9000c0e00390b800b000e2020707910002d407142280e000609544030356480c010480b200c002e41f8440c01a141031000c1aa0300742c00c2500841030300e0b00104034588401c000c0301640f0315100d1303640007031402280c4880b80e44140381d000308004e40c44510031010f840c01440824400345071605080038104035910403003107000101e01224000d8076140c08880001c604e020098442c40d14208500078100d81c01d540d1004001c050040500c1017400e00e04c0300d00c03c01864044a0b8000074107600019000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 235254298 1250 235253048 235253063
    0x504120908070e0c12040f0203010c050901170403090b0c0607021908090d020604120f11061e0309070f0b09041401060e0108090c0429030c060d090c050418150c0c 71
    0x22030804c2d032141059911803180362001312100d16251408a880c803188141c01c82c0070350b0910300d00424441c050300a9a0800006030341c0c02d501000007918000754070f180500150240b000c1044081a2031403c68010010a10320300024203043c02c103020001c2ca8034040700c0701c0258040360500b0650006040d081240c0040c0822509444030034a40c0c000514188215401200103c40100c1074400304810000d08070700c450701a01c0c10809581040341408120301c92414840703289408003865a9000e80104c01458200e160035003102c0c001901c40c20002c50700c6105030040c0d17401c4003021030308948034907090003032a12143c00e40d10011440d51503c00c000d800d0748003000b4498140310150002944d005401c010206000800400901013044072920400103445003a140381c0d002d400003032440c80e1b1800d0024106800d00e8001d81480d05c0c01a40c00402d0006081c0e4040840700650100c40005050703585000b501c08424100c00d03401810f640354949140c6003000000400c0d01c0c81d013000c0400e00b1194024149004040d0481c58 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 235255548 1250 235254298 235254301
    0x12010f051f090503031909050a0308040b07080c032b060803160501090c030308040311031204020609031e030d0c02011503020f0303070602270913060b010908100504120908070e 77
    0x82d9074100719504160b42510011850494001c1218015115662141c503110101c41d1603000780030624031140005007041c0d1003080208a2011014014010f1502590a5501300a40142054215446004410000080103070350105421028801e0502e60705914010800c0500c0d00076002c0d02e074080c40d91208009a5041d00c1c100074040b0a4006421190707011781c840f24103545900d8007801c0c4007801d0342c0c00e60019042510380c42600a002084032200703007c2e2036001c5c50a5880d6420003045600031800311360580201881015005e00d204078008920792804080c42c1c03100d004030300d440100c4003090010400c46e0f0426025980c0c3c1d5102c00340c81028ac90f010340304e40f000b904003a004245940f08015005000385e10000c3c8071529070004420b15003898031624510400d001d000010020001c0059071121000308005d84c500700012074a500108100f1010f040100d0050342d2221100d00300703e400122030030304544902c20041009a00b003c101c400d500c01b0b080001100c1d04203908640d85400ca03002d40c4000c8502d040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 235256798 1250 235255548 235255609
    0x103020103050c09031e06010b04030507030807030908010f0c03110901081f0e240d0b060415080106090902090601090806040b041a070201020712030204050f1c0609030512010f05 78
    0xb0441c4d081c0c5101500702c1c0d5400c4103040c084800140d4404c0700b071030a800b4000001c10004007501c12142140c0d0060024104981140c60f008200da104d0b0604605215010b203000035882020302840380e40e420101d01c0000c1039410040f001c0c0030381d007403400340c24103c000c00c00114295a810038aa1500695080d950308404005040c00d00403041d419023190852000b043c0070400c0030b40409540089280780254003e0201d4040001d014184010460040c0360310112030001d05241031a5100304580045003544455441d6184070150840d9003035048034000c90f445804140950a15030030342d6808c01406e107444900c1c98a0b01c4012912450080e000420802000000c1000d00c0448003519142c1c0202c1c1045622508144c003019000b503000241c1195490014014644243d0007442a502100d50207000180001c1e1058100f1082d80d00d0080d2015000c0403000e061070100e01c1a03c121010544207858244d56030003032001c3c0c0c2040540c16400364104051101c414005900c078143c007500c00c80c1090301602480301d240c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 235258048 1250 235256798 235256821
    0x31608010f03030c021804241401060f030f060f0911090105031609081506030f0105100504020702060c01060603140c0a0c080307021e01060f0b0306150a051308010b0103050c070b010302010305 84
    0x1b00d40d89014104560140001d10581005180100c12014544010001420a1b031010b54001804542c500c50118004200321030044c2c58403241c04010740f80004400035030102e10f5040b43d690350400d4510016480e41408010a14491513440c4c0c80141c03030341410300745d003280020414403000b44028000d070081103003c500d841c0a090a4005003200f10203550350b407100c00c840c07120071031812280d840c800d1180d6031030022000d90600c9181d000c1c0d210034135141d101905000900001e507128071812a0818401c10191243c90710a105001c05001e5558022522000340000107181140c050994503e0030401c00c407009015800000240d003603076001080c0c0e901d82d82d81c40400d030b0408102c0c1d180f02280b02c0e400c20221090010643c419000d8130b04d103540740406540c50b081190060b0104980c00c940001410028104981c420006812a011035280451400d140715a0354100380f811980b248800d40c2d1140300e81901c640e014043d00f90b009400c0c00c0318030b050006607240d00c07014082c10300c4064141552032000c0307030001c46607 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 235259298 1250 235258048 235258069
    0x1090503030d020f0c030c1c03050f041121010903030b270c040503010c020a060c03111e13060c0303180b0a0f021b07030b0106050307050703030c0504090c0203031608010f03030c02 79
    0xe4170030340f0b4440481440083d110210031440e030713110400c03c19a100c1e0321400380c032456004001c0e4000c44070590343c50790384a40e6040e54100800703a0244400d00800180c0000301e10054681c1a40700011640d110549406400d035800300f000c0c1c07071041d410304090518400141d001400001c0d908006080980c494454071030070b034880e5811054241d4200403140c00f010781c0000d941c40c0e0f007601c5188100200c216a413021070850345203591034118003d04010450260130140030b952036411070740c80c010385001c1d1440801503010401d17034032040c0443d07803070344060050507018458543c0035050103490a1240400d81e403503000d0301a008100c118015030302ca4042000c1c484950559280120780d5921420502c5454941a9500700381d20048424191150011a000340708105581c010390254954900704000342e5002d03005400380c003d0042c01c002041c4070004444ea45d40c05401c0c0b801a458001d90b54904203a02c08400980c42c05006c0418440d00b41d0040105864428040d030440e601880c080c8250006031000070680c000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 235260548 1250 235259298 235259317
    0x11060c040317091c0516230613050d0b090d030507050d02180a060903020306060a0e071d0d0f0b09070303050d0b03010f110405011106090a020409031803060501090b01090503030d020f 80
    0x40448804e00304580060100920b50108250b005c506545112410b0500c1c65030041c8200546000101c00c036078289000a0240b4640d0300c3e410303d519685440218801c06071620040d1200c07044501072191038241805600180b1443c0e04d011310a6151001c0301030a184124044602030f04e42c00200203040c1100a1000c602400000b844001500c1d91038100400f03000d248c0c0801d91003401103001081883c0703450b400c5807080b10100352000d84203540d1040306988400b05210540300d1440c4084c088841c6a0380d0940b0240c0c032911449040810080342d0502185030103000f012043c0300ea2100100b440400e40250645900c0c44100c000840d2203000940801e016003103a1707442203012030030501348407210000400500262103003a6141005040080d504550b030f08000da8500019412910100c1c02604060304001c20385400382c00c0100192404030b0624041d0303c42580140e890598503030042c810f00240d4081c1c004907131000d2030701c0d4144500b481e002031340f244120030010150307940c009024104480001d017600d240c0304 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 235261798 1250 235260548 235260589
    0x1020a120206012105060103060b03031606053123060a090201032d05280e01050112050709021305060f0301030c0b190305220311060c04031709 63
    0x4032540302039500c200a0050601120070320b00300460341d40c9055116074880c0e07005801403119900e1078035100b00503d0003011070381d0140400c011540b1502c800b68805013a080c03080c64002214541180d2810403080b5410b503148420070f040180c46100100b1151802c440740d008450280d8a5914080b200c80902d180c41e00039070309005010030040864555030180040038000e032814001070714011041480d003005441a02940c1c418440c8501503110b4036401264000f22181c034242c21880c0e40b145102d0421041030784115015111006040d001000303000e0705004004528003a503401e582692004e0f01d0b003159000300e150f032660108158000c140384903038910040402a100668889641d0f940510640c824002500c013038003103140000340d074a508403c440000071011200305641c00d50007003c601810000c5c281c0131641100c01c4115003418444c0152502c850306c0307600e440d86e010000810076400c180c0300170520514140140001c101155404000a030b0000020920550714200900010b9811008801c00c01070310 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 235263048 1250 235261798 235261823
    0x9010f090522050a020310140303160b06150f2d040806040b0601090f0509040f02060d020408070803090108010e0403090b0a0801081608191109091c0504060207050f01020a 75
    0x440300c40d0003a15403802d54280300700e030b44502041d0f0907448180d0705103601a0001604124054844a0070110000b00a003603a18010341110100312101c011f1030103413441d60103201030080c47d00e40220850365110b0203680060420042e025500c8040c000c0c075148264007551040b5400070018078045100000036071044d03030b07a01c407034454079101da4660081f203048564290210103c0e060f90301843d1201d0403128a508005103a0f403c01e8284412500090f1081b910004601803807001692008050071090140d000016121885c0070a4646005416400002c5540007041030036090b0b60b004400340c3c1901e2161100b50b2860700e540c1f0b03045407002c03c0c0d036100503845a03010440740c072100e511000743ca040b00d652908580350001c043e611000440c840d40b01c2c2222a9000320241e01104504260040c00c0c58001c2c9103141d0380b0008007003c81e2503c907085607400401d0b001582000075840400d2803908a541d2645016420a0305108000c0c0d9694168040c461207081c8120703803000c142c0e2082061061301035003e00c981004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 235264298 1250 235263048 235263079
    0x4080604050d110c09040f0816080a02070e13060e030c030d060905070219060515040e01090314030c0904020d11070609032003090f030321040209010e06030309010f0905 74
    0x120707204150410b00141e000a560141107100203085030400e88020312070b1600782c640b6500d4480403042113204407403a000900051000c658403103c07006400e8062203050760b4811141c031009080014035040400500ca861080c0f08442103103c4800300c0061340810001280260080414650300801c550300da01d0384000102d10f44501c18a4215078212154040140619102c1c64002d076120400d5400300904031b49148411404034a503608100d0300000e9030001c0102d03244032072010800f51082e00390424120f0391104200020103500030b00c0031010407c06c2d41c00c43d066042007d0090598450f08002510440c3c02040d4424000502e030301c80101071086200303081c2d40c3c022500c0d040c0c4c00380449c42c60a03004100f08810010b8400c00c1c01007074a00c40a240c10240d071034849008104100c0403c812000d1340c06100900c111540b110740d40740c03800303a00a60005141111314042c810010302e0001600149401d4179003106011054500000340c41100b2400d0030210342e00c02000808540058160b8083c952004c40041c0d400c2c1e4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 235265548 1250 235264298 235264303
    0x301021e040504050106111b040e071205060a0501061b11040e0a020306010509060f041d0d050c0708150703020a03090803070c020102010f05070c02061605010f0204050f011d060f0408060405 83
    0x21910300f500e007400355030303a1842d064600000130000c003032840d0040f84802c1180c0c03203035640404400500500009550120307a25070341c41c01c031041d002810000d2100300810140041004080e0384250103100a2045606240c0020318152056201e04c2e00286101c82c04410000020080745072100003500811120040d0020250354000710041640130b40600300000c249820030240007442194060810300340302e0200d409110060481081541d2405100111141402d4080c01824500c08190b076825444504042c581c0e8100001507202c0503041e88040000b0031020380c4681020303401034031b5040041e10384c000a0401d1b80541503600c0c00506c1808000108568140c1140c5c1c035041b0b984c000c0e8000c00c0460790721502e600807250169034020201e94001925001841c107040245821003840c00000600c280d150ba8150949200191042a050300813809120030300340f040d841e00741528240f03070280c2850001c1101c118004807144c40c09018480c00688610b10000b1030003110000c01010f4111442494141003054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 235266798 1250 235265548 235265557
    0x20708030f27060f0a0e0301090308012d06030527030406090b040b09060903100606020604020f030105100e0a0b06030f0403091203081f09090f030801090c1d0301021e 73
    0x81c86500003102c440141e6021001c03510690300d01070a8945885140c220320b00164200c1441c4408100500d0f100c400d090310207005082402d4400e864568440d41003100a4400e09460301001e0041040000303440060201080e4000440c0c3c41800c0020b403d444c0c1c01c00d2112180054021031807001e0104280c561441c0d0000700400484e02d641e540d0000890300c2d0b580240c05032107140b2480f08010f20512450b05c031860250b008000749000101103038284901354010b407099804551007800540c21080402042d410051000d0182d408100d0081110f85000c0c010b00d0384050050044004032107000c00042c480c00c06a07803104020342e1005107030f980c480c540000382c880075420845045000801000001a0261003032a400748280e5040c0c03a452039995400000b119860389030038907040200b104210006000540d44500c50131a40108500010391241e810080c05024040e801041603924084414152a500c0031420240c031051240c2c1c0c550f0740d40c030000001e001e4001c0050040c3c0c000000c081d8829070102902c01030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 235268048 1250 235266798 235266817
    0x31e160212090a0302060d180507060f0f020d0806010e030718111903090606270b060301150c05030d05010b0414030105040f02040b0307030b070201021b010e0c060a020708030f 77
    0x200c01c1807070070300d58425460040d40300c1d01d5085035039840244010720b810b030080c04204040010004e9081602c010480154004d403000380d81540003040c1c14000d0300c0e070111241c0014009420180c3c0640700201c002591240360340c00480801c15124046561680b0844103818002001400c840406850341c0034400d04600480ca00c45105140c0608449080c0c01d100c20b807460003038045000d0f20029200769003079025241e2040d003100d030a43e607124041030007c035216024403c081081076a085000720a40ea2000302d40e81c041100d885403070b05100422005400b5140110302d404580ba11fa03400402070710f000e43c55070268283c8030100340e04100011600c484020064030031a18a40b0301c00c04c1d0804141c0c145400c0703540030345028004ea0f450419900c0903090903000f07480008000341c1201c044580d0b0f5161007000c0341c020b0705e5440040c1d40006030022424070446140c080083c0000080000425050300300c0e903102c2d419103000c3d0250b500410b030a41c400e4000c0c04460014841e82d0180d07555a909980322000070f0348000327900c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 235269298 1250 235268048 235268053
    0x1324020115050603041b0801020f030609100812090102160e09060112030207060f0c051b13060b030a0504020a091a0907170a0e0a0f0b04050609060c070305031e1602 72
    0x100008009101d101c001c449028140034555122034840c0741c880112900c054a04180542000444480c24030042c401c030040464101d859080c09400c000d99a5805070460281e000c9040c03041c00b0441000c640080b81d02c8010940300e0384c0b01c04440040c0d08001d842e080c041e41c10f000c168000a07054410500c1e0350311030b4804605a41040ea01d5801e544c00030000c412000e00107030b00160050160341e004064101201c800f5080003550f035800750395150302d0480b200411140c100302ca003503e43c5085c00c0001c812034101803110001d20455060120000d01c0b404000e2010806580341c00215040d91103c6d803402001e4115603009000d800c603074820138a0490000945240117021100000742003a02c241c070005441c80001803030740001d07100c451190f405044140b02182c114003c40300b0000005940c0e50420302401e03c100d0104e40e461074107051050604000802c002d00c240c0184c820014a038000c00110390350b8581c18100603840792a210424210540400c0c0100d038800031202c240680001400800d00c03011046508 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 235270548 1250 235269298 235269311
    0xb0402190305090a1226040c0f150c06020a030b03060103050f1b011b1401020a02010b1f050406050c0a1a060a060e010e131107030f0e101413240201 65
    0x240d5079510130035800080c0c40b0144d512029500f06101d180301003241c80d09038600c0401074890100c00350100c1401d503402c40f09520401d500700980020312240c41d0080005440444212043e0329000d80341c9810020000c1c9416400503107259220300a500c100e00c0264040c0c00c1303031081c2d80c480c070302103030b5801c00003059038003034800c402503031880100440007a1030070302c4183c2d603c805001c00d01c03011070b140c803490344c0088803a03280c10754070000341003000d02c081e1620840075800071a02c2403620040c007201111007a042c4400d244070050400500350843c00b2181214000d15141c1d41d9911030300501828495001030003442c50345180c0e05424403000c0e98400b14002c140841d006910a076440e04191031182c0c1c4540d046004c64640c2e21010707440d00c2c0070010408100784442020580b24180b02c0382014a070300044040740451a0383c440d240c411a444250802580700542c0c0300d169440c0c8891000c0d106045288480d84900d100088500c074080a141074000248841082491000110550165041166012080158601003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 235271798 1250 235270548 235270561
    0x3060b07020a051e030118020a08010501030519060213030f140a02090a0b010c0c0b0c06161e180e06040c020601030f110d0c0602030717030403120509010b0402190305 73
    0x8121603185030300a00c24000546488240407050404540200241c0c465190f450304548081c00344c0111500e03010b45140034046240f0400520100b190004c2100360714090041c40041d100003009048c0011001d10145280c104d49007180180c030a8600c006181000c0e8a00001001510111070403070503c0707401e21500402c07a201c3c9550780e07940300c00c81c0a944028094003046102d51180e005004824040c034040392001640d440308a80320045a01510848200040d84c0c3d030804018000550802c2401c1e90f070030910000c142006043c60108140714080c3c0c40c48126218565000b001a01c200e000111200000c59540b0395150340f03800c20071507000b80030f242800d42c0801c0c1d01d0f101080290583c6d91103000501442c1003034413905180340c106a07001d40c000c2c81b4480f2100c00b007510054018020034455005598609903460220030020043c8200758401006005101c0040d40220580b030030001c40d0070b030000d05039803800c1940340540051071409421902c009080e40a4000c400e0710807108100300c0c0c0f001d00c025152034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 235273048 1250 235271798 235271819
    0x601030e0d0206010501030f14150126060105090406030b13140a02060315040905030409050a0c091412031e0903010506061c09020102010b0402190e0114040902030c07050a0f030306 79
    0x10001d410042c0c00100041c00258060f134061409041001740018810380d50b110051004002598042c0b849507502803900925130f400303c001c0e503c3d02c0320031001c0c0c1000c04012013014803040c07000d40380505220000c130f940c9005840d1a40820300440d00b04c0c00c40c40c03850500320b0360b010b00d000c00c80c0000d0b6a0030040300300d001100d220010302d5201744e6038041c00480c5540d6a000c106445c0340e001d154030903440b1f0340304d00c99540400d0081000d000640500700c0001202e00b0880782c041c08a500b440d400d5000c0c491229420010303440b14203441d10006105460341418400300618481c2035200c0c640c1c01c1f03034a98481c443c40081030a00712014160030a002e80081083c1d48421040202c14040d054840046151801c0095034a60300764020450341d17032041c0004229010084005030998110207e103158010307005110046007603104a904001001c01e0030549911f000c50f078030704452032003540a14200b4980000c0403660001800088031910350304001a500002100d203424125010a43c500707400290400f4008a07403040714 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 235274298 1250 235273048 235273063
    0xd0207080304060804050307020402070302062e05060d0912050a021510181b05180a0302060d18020a0b0301080d08062214010b0903070b030c070f1403070b0601030e 72
    0x80310000d41c01c003854060200d880303100042040f511400240020300060b11140081c2c0940da1090b000740032189403a511031585500340e6200c01601c411803801c004c090301c112640301e80c1665420b403019681c40100e42180c0d00a00306035180140851540c40324218042d5126018005403e0f41c0d80c2500d01b4902e600601d91114281614000c961382c00c00301e4100042c0018040510610340c40540100d0945c0c0c0d80e00701c00c11800300a0007002c000c110001180780c2c1026201596810090044850340052030550300466428014900355524199071000d034800e40080c810040d64074142c3c01020302481e1922030b815240d02d078000380f10b180340c071380310b03001d40c14110b68090900c0c0b900c5510050183d940056018407501c01016100480e07038141551092542d40001c0ca802046010f0b0050361003880d030b100c10300ca081c1442c0c11b5096006044a000500901c6503e0010b1030031a50040c0d044001d41c840d01101d41800740a4a4003003400000310310002805108002031048150700c94403090702c3c00c0010141a500460b00c82c5a0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 235275548 1250 235274298 235274309
    0xc12020309060c07030207030803010602071503021c021b01060b190c05030a0f030b040507031a01090e010e04020301020c0d09080114041505100807030b04120903080d05130606090e0d0207 82
    0xb140000301d02a42180103400340c1c0e030107441182d50040e941d440d1450343d9442030300a000160441002807140c00403100320340d10f10000919045243c80040038120200340c0312a2400c1c4079807900020b101d6a62105495024912040000208022561610442e15961241c1d040c82e1210004c1100401c2c95400b81d0000c1030603c2e0003002a52406030907040442c0c5000700c901c1c481090554959800d07072661030381c0c41101c1c410201078800055144220780410802030fa0400b509040004079a0240b003000080c8a40038111140904031040d1034807948002406400780c010710103646c2c0704068840e40410751102c81c010031940c0c0c03103000704500510581c200220604c101c8000d040b0f0042e80680e0100450f42c0c1d803002e81d1104111040c50807180c0c86600090a141079980181e03201d5140703c0a200a021820000001c1043c250400307198941c60340da00c0221500502c0c0d5903200b02e81d40c40c4c0c00034012100048001c02441d81c410402c100648d21074005800a1251000141ca2031142c100c200f1000d40c000200c842c244c0e80b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 235276798 1250 235275548 235275553
    0xb030604061d15130603110102070803031506180d081201050102030901051801030b120a0b3103020102040f32130e0705030102130501020d0302090d1211100c12020309 73
    0x240d800c0031264044100408031034002c14024212444544a8405d0501a500c68406940c2d469428800280340c0411500000d4180d001001401301030104212031498140068403440d46420700c44003c00e055030a500c1c880c3d40c10402c50201802000390300001072405680c0303200003c2082c2d8898004a9a901030110f88c0fa012500c10404094182c0910241d40190344051401040300b210314400301d03404610010b0039070f40c268086640b480c1000217110040e0b900a4040400705079091220010001d140c0140080034201a81a4020002c0c5403003034040b82c01070212071070b400c0e00710750b914584a5042c41c40707064802c05840503c0303e0104c00009141d240c40044500608660170700d4185241d000052104455001c0107100c0c03042c00040c1c0c0c9c0c8003030026000380d0000828240d41c291a0000183c1001d180380c0d184420035204100442c400d03500c4410018070107800c105140307000c4011101c180c5105049071180c0e200c43c85581511601d212003508503042c441c20384d80d83c090080715943c2d0303400160700081c0c2e182041ea4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 235278048 1250 235276798 235276801
    0xe0d140a0c02030c040905010c17040c03020405190510050906040c0c1704030f0b010806010f0303020d030b011b150b06040305071a120109150e0103051c0212040b030604061d 76
    0x2a44148051032000740000e044e1070407120200f0000c2c0c1103d000003000c075450394456962741c00c401d4000c5500c0311005418102c015007480c0544d00e0248a80c0e050000a124641d00c40c082404200071a1a400a04000ca00300b0001c0c0c1c102800f039038140420b00c0c85110b101c1c80a110000c2c81d5420180941c1c40c0f600d1080c0c440a08102c025640c040c3c06420349881860015070a000c008089101000c032004154001c500e01e8166504042c8280d0030144140c028040d0311810179020400241e00047c2c07081e501c620303454005a00425400101c0d4040394991002020340540c0001c070060111500da00354011030310f08401c02c400d0400c0410301240703004038031001d4060b421118041000303511183c54082e040111451140c6042e4810100c03070074801c4207030083d0f04015907406c0c2040c0009000012400a0f113058200802d840d03145582d010396504541a400b0710003c08151841101e50082081840105003100060744913501e42e40140d290780c2084031210b100380d050031400181c000f00d0120b0044805201841000203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 235279298 1250 235278048 235278067
    0x71e05060c0f07201504030507080106061d010201110c060a0b0103051014060f130801060605030c090f030c03010c02010c02010b0607030e0123030f010608060a0e01060c02031608010e0d14 82
    0x13107500038580b50082d10000c0200280e80e0400b102110811001440342c9450a604046103068003036041804582c2c5000000d004558003c485c03280716000742002c280b502005400101c1c0500359504001c0350281010810b03a00700394011812511070a00200b0401c9028400d030300440c00d031402511000c02c4085156018008a02e91561903101e982d4050070307151800d0045151802c2c1341c0c3c0401d44a52440444090601c2615000c0c0a05002070107a0710300242103040c030001d04030b12031242c81e405500c04c05d603814030300c111a2030078401d80c5007200004008000c031410701ca42c003a01034080082c40304015460440503100c03a103010300540701101e40680ea0058a1603c82e401510b00390000d8000a110418502e8102401201000118800d000e4050003481c3d95142490181c010070000d840d4070710840c202c40040c0205002d17a02400e04544075480d107100c0c101c0e101d0000c40d0400c14070b419802006500113001140e2203105401105600d1a40d404440c0341c00310240b400c0b1a1002c00000120102d101080707007104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 235280548 1250 235279298 235279313
    0x50a0f0f05041514030c070c0602070f0e0414060f06010e030601151b0c120209010914040b0a1401080703031107060203033c1801020903071703071e05060c0f07 70
    0x802d90802e0070038020501d0402c4801955810446d00c0710b015200008000041012804841c1c00030000750004082040c140b03682842018030a000c1c603590314008000050038040401c140a0060707120343c05680490904010106542500321207540c0850513096a40075a410f00042e007034100c60121981d47c010100c6c04504070f58240039082d070800d0340b100e1041c0d040003207004921428014056001d2406040890303105000c10300e10141d020382d002c68034081d0066000002c2010b041e0b889544800c655109960b81c44600c00180480240300d4010488900049010ba0001410ba07059034041d4840c240400c07043c042c596520f888600070000141c0040c0085039240407010151601031028480c8441040c415a040b4420128029000640c0041000900280d91a001c03125085884104025450019500c1c003080d5505d0284c41101200640c02003409040390060003a614000e43c400b800d20502c10810703031402698031b2800000e4486000d12408284038003200c408591022100d06146030404160340c80742c41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 235281798 1250 235280548 235280579
    0x803070c080c06040b0c04141002070f0305031b061e04050a0210080f090705031506060f0f0c0c0316060c0302011407020a05010f0c050906130902030403050a0f0f0504 73
    0x509200602152030005042100641042901d00009040920309400e04e440100c10281c20701401040401003406580201003a0741d0741c6220a45001c80d26869450301240703002c0040d0701c080641c920740312003c000c00c00044014000e4510100e80710226512091b50113459081c26500c1000c1016001c0c0007400503941d224080364010f0142d01655480142c2c0e0b004074615102c01090100041c1002d8100034811100031000d07500048480b004080b85401c1c1000b1036680e00a850083c40103401d5500018070340d658410440756072100c450255503e401c903d0480000700c0c1c10050340390480b40100d502c0c5c41102d00f40000d02e000c40b0b80040b888100c43e1481c00c2c0f000c2d00c00a46e00c11042d000c40d500e45800c2d440e00010400441e008103880d40c010007008d203d0381070080c01c50b40c178501b01c0d001072402c0c40b40358100d46605c102500d051220440f01541e81d40d000f40341c110001d041caa400300b02a40e0011042105050700b00018000c1c4001c3d64840c400150a4104102e82c80c10080c12406c001c20400c0c441405121100040d14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 235283048 1250 235281798 235281811
    0x7170c070803070f110601030b07111c02070f061404090b011b050d02100e0d0818010903030f050f1003140304091d070803040e0a0c0c0803150a0f030f0803 68
    0x1540303490034640707840e450380c2e00854040b008038a050640240f00d40e840b0f4103805180b5081d1002d04503079410340e40d03141007503103019000d00704101c1c44c9120403400300d1043c0040c10550f040c0e01507400c003005404402a4881c24548240f0280640301140091180e00915605170288828001c080c0741c1814144004024059a00c60f50304001e084101400c2c43e604840e18403200c280278100501501c5410341000b480c5c58031030b00c030300d03000182000d01d41c81c034500300054040150f00c0d01d828600c000c0c1d074400080000d4142028665921507083c08040c409254060707000303190854960000303000981d06c441c010160848251446407800388108810008164050312001960f6226019285820f540365090002c3c0c0c0d58655000448802d00c1c55002d1a16904002c0a8000d011301c070302440c01d03d40340c0508140e41c40c40042c5101c1d941074580122034142845080c101800c207a106403100c0d2030303040440d010300d20800d0f8550018000c0040b0000811180740c2401a9070849504c490310f150101507a0b601c403840c941014201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 235284298 1250 235283048 235283071
    0x504050d110d210509060301050d02010c0b25051228151d01050102060714130b07030e0609032a03031603030501050a0506070615080f01230717 63
    0x10681e600b01c0801c41d00c500401e580f008824903500190500c02d800700d030716000e005042041d02041e8441c001902e0464a0031510144012401e000585000c101908010034424a103000c0041c0e0640352880502e4480440070310003c10045041d05884602c903c0c01d03031100f0035240e80f000030940c0207000030174592121002c1c0d25041d4001007042081c103461940c2ca0340e4880500e5640103000000c4000d224500e41100c4101d00843c551500001035200c0d1030252001003044529000036000d00116000c440541101c030002c5070b500ca54420301101150017038a0218000740d03100c039140c0c0e00c515011042d6901c5ea00018050900c1121000580d000c0100c0322061088880c0d03843e5001c60140d0b01440540402e40420400c5002c6844e10700d4000c00303e80058105502c10350300740000744255102c25064483c02a4009000501c801d60074000c0004041c0981c4414080d108132012818011340641014003103100340c410500e900344030050b0741c0c0407070b0707030101c8401000601c0c240c1d0110b03c02031042a4103400c06800e045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 235285548 1250 235284298 235284323
    0x1020c18060120030405010305130b06010c060908120403080f09060114011b05060f0c0703121a04050c2a060c1606060e010f0806040201081503070b030103150513030504050d 76
    0x102c1d2540c03062280e0300385081d84c00120f0108400c0d6090b006da02e90215400b5001038101070980d480c850304134006400e45041129817003040c8100301c0181d116011241d00581c1ca60380380c070803003050441400c00840b002c40010380b800300032a802e40c0c84400068025281344c03014141503030034218108400c4090400040c1080714183c16000303022401c10b18010103e0003900606828a4003c0072950f0404000e05107041644007003100b0070100c0d51000140041c041c90b5000412443c0c4034035000e41040d604c01c92400c2d401840c0005104401900313900800800703003c490060f244030100d42e8044503c00d2801c41000403078101c4000120303c9d025000040c00003888009001d10807440ea620b80d10102c44a81d00300c2448c0b920488014440d00303400b000024028012580108400d01d0141e000900181002c1c0c00100e107030851040198081d9000c2c8400d4000e0212003510380d84075179507400c01030100f40c2d0888440300e6452070140030840080700e06601207a80f030b070943c541516140c545024800c0f400c550f8070341610384170017591 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 235286798 1250 235285548 235285577
    0x206030a0203090609031c0506180703090303051005090105090c13060201060914130609020a080d020109140d210b060708070209060405070c060509011103040b1501020c180601 77
    0x91401051000001a1a0b1511031129840d00c0303000303094170410f036000b44902c00c2e107141040d0408286414500340400c19071949008a41e011229200001c9035188081c1040001645070340801c140500940d42806a61580f180f60000b00c0c42501491f47c0110102c00103020358100119241e42214605034441d10b42480c0603c04103d100705600b1002c0141d4461004011020036405043d18010000a241c4864140f02401021104041300020005902d40080c0c005540e10400f030304004040040a44a076604075010083c000d1a000d10100c80004015459000159000900c3c124003c99900d511300515403081d020025421130620b18041c140c0c59284034211501ca56024084e40f520a64880c2d80340c091034030402601d48002010607014030728003400c0010f132a41c0800141011a007003000060507841d0245c24a014040340c1020f08a040c60000c144010800b00301c0030b10b482005841d10010a03d18640012a207529400400302e910040d10211a208004820a10750f0041703014144100c1890034403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 235288048 1250 235286798 235286809
    0xf050609030a0b090601030c0605030c0a08130b01180609050105030613050c0a0311010834030608070303080105100201020f0307120e0d110c010e0d06020319060b07140109200102030702 81
    0x22104c90480c1e411140040003004803038a44034000d005a82016030940c07900b030b0040443c50141140c0c09040000c02c00204081c101c006110303001241c0c0000e1104000d607100ca442500e1034030801c410021071072400c00001030000c41481003a040c0c0d50001c1c09001c10f40c6800d0880c09410a20b40001e54031030003030008151041d81e9945000740190311030403060f0f840c0103a00c0b001400244004103001c2042094010524141d480b42d01200341e009150040c20b00313114030620003200100503035040840644201000807050540014440b4101e0b1400c41c1c48500056600c0c604900340c0c021030400a0040d0020b2010601203400f80b41c003103c1d0924807280000b0300d1402c154006150140001c01740012444000c0d51401e83c180500401e0311031030080c00e14450354040240894003403803c404005d0041035010000c640d22101140104148102c0080700380811512000102c06683c40720008840854034003020604250041c00750074050390f0460700280c00000700e11841401080d04030f02880c114001081000010707605d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 235289298 1250 235288048 235288051
    0x305040b0403060504021206040512031305030408062a0a120e100b0405010909030504030b070513080f0d08010302010e090a2012010807150e041508030c070501090f050609030a0b 78
    0xc1d40c0f011680d13003490f00500800101c00284008550000e00c20040810800650788034142e8420007610380d41d80d60903d10744149115658000c00078040000c3c00598071500044140c00352181c02511501070031540305a0400b42c8003181e008052000502011903d240681d00031084040c0c10713030021440070082c2801c0740c20604000306c1d2421541d61003a031340b025400d01d44039680c090442c00b10100480d4a058a01900c6409140702c0200040002030004d540c044c070803026244002640c1c48020030403902c039066161a01c0c0d1840d01100c841c0300d4401034200280c41a03030300f00e04032901a15512040007030364040c40081440107001c0a0303441e403100074000d44d400100f20801010418401e9803038803030090700207a011070070b03040c0e004070081c0e80600028010350504144240b100001ca04104081c801a040490050200f400c458524102c008030005145440480100312005100098610450301c420042d200407000d40601301c61900401010b0100d07041c86002040070450007000ca504811030b969441454410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 235290548 1250 235289298 235289303
    0x312080604152304331e0305060702070b09100309171308010e150a0b10030f0518030f0903030412051c08040f0204091410060f08030403150203040305040b0403 70
    0x300029801d003001c000302c060b4420040e003210240040100c404079155920340000d40103100780ea20740d0210355411012440b080086c1065280803143c1700f46040001076010711480300341c41034003031080080d0100348042034800c10784180150a07418581c0010500115200301860b10080c10b83d104400000307d03440d1444140c900004841c19a65540f072000650740080c001d0740034580340ea040c1602146e14017008501040040f102c00710101c0c0c6c0ea0f482d134001c240076107070764800c0581000110122521156058000c00b03100c1e03120a0041c41a174640d22070b184030802c504031050f141c5400910121079902d100303200800c114030000301100e0030503440700e030352200c1700004520484a907400421702510264a0b40340040080c82942408651480d0070b480c2c802c0c0e035900900c40284103960b6004244100501310b6010150003102004441c131492101c607561008000601030b9102003815a003001903025000401c0390160399000e000b01e0000300e001c00d4854044c0d0009001203052000c103100c0480ca0288a4001c0c000460 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 235291798 1250 235290548 235290569
    0x30a152009010e030a050304090e10090305070b01050d030905011d0303030a020a0201060e0f01031e12020604051c0c331b03090803182404110307031208060415 70
    0x8500001420941a040c40f41d4001d030046200b0340c0102c3e00100c103403800ca40110038041100020b56800c5400e28800d150400c06440c940200c1c04c0a16078420054004a482013580a5003070742c941c0100181c240816400a0020300240720501155201d414007480b006912250000c00540080020f070654000b00d4201c13400c5da80c00b150a142d055070902500c0014242d86103582c0b460300b0710b111901500b440c1408003030a814a840d19a003085800c40c1550366805802c900c2d2404581942d46000351540d10989003902e081c42284240203109180104402045c45162101102c5080580d290f0007903058500c0a11244078034032102c5401c6010b4441c10702010901d8400004800e100e017000002c01c09081440041014503107046503000504c0c00d800c90340c01c0610200707200100702d982014649020480705080312850484054000844070310f1360410b024a11134069265020700c51405e2554441082c440a070210740400c80d22001035018651030b682111000d0004140c40360060101c0306c4001240d400b003080741 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 235293048 1250 235291798 235291807
    0x3040204060e01060203040312020715120c0f1b06091b060201050c0315090a150801020904050a020703020712030912140c0406050603010b090d0b01080a03140702030a1520 75
    0x628051045002a00040c1510b0460303504003d0000d40d00d004030300000304802c003681c1c03014952500070020080204034040c800c0f010f8038002e000090a02c0d0385070101030740d014100b5042168540c01600e120b02a1131050f92124280b4640240741080303001405819240d02e07950710a80c501042c2c4418500e15406116402a84014a8044000e003168001013007465841818010700a0b900f8204a80ba40c840b80125104c001eaa1030f0800d180e001008a4104001059111130000490b220103401810212900329000c2080b82e40d0300d000d42040e0300c50504002d0058200540600c42c406074802840b01c514000c1c5412011103480340480c550030741c030004003a21340038418030b500c1b803c445c010000078140020584040c00a1031810000c42d03102e02040c05070b4041c444000c00c0d009040c1d00da404844000e1600300e94100411f581d1120080d444819038402a000244c0042c00d0f8071100106034100c0c0c00040c0c0c0500240740c203452a80359001c068217071031410444592a54040d0404075019140000d981d50301c1002c840e510b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 235294298 1250 235293048 235293053
    0x30703022808100e010e040818190501030b090f06061309050910061d040b06060706020f0a030b0105030f010506030a1b0f0e010f02060a02070c0503070311010e0f060a0c050c030a080304 81
    0xf030340d40280c0e05403c005005201603078090140c550403e03403181c1083e4071507001100310b021150070050456007041c09504070303080040c114483e036011a8403e890400074000002d092120b840011034080c010745003035402081c8503060500052100520010021026548800d45d42050354001c5c2d503a6542c80d4041203403524070021502c41c00005003040104050441012156070040d00c40003440903280309139103000606030f038645030121031010b60303c240110354849070f40003c0600b5401c010b500e00002440c0c04c5490b542c5500030070489000300c0310070b0303a494030b20f83c6080f0400c80540c0c001442c001040d901c0d8448000202d003840c3c0c9034181d2003000d4032445807002491000801c98941e20140504100041d040c5030902d94022400a4101c60380d15030240e554071590508401000d0a86c0c0080d42500c6096400024090140a9044d20b00350036070312510110624400c001c1071900845030769500c034400304034003483e076402541c104104a1086040c0d41e0000301c007800080c00c00c440302d6402e0350742d1880042007104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 235295548 1250 235294298 235294321
    0xb0a090203220510270606080601080703051903020703060203010b090f1c1106070c260a1e1a01061205060d051c03090b01060e0102010b0409030203030703022808 71
    0x851409841c114000b03240c9545940c0c920344101a140281d80e803289090f203d8003030490314602c00c0c04505821a684c15890000d0080000b44101c0096010303041c008102c4150101c1c090040725008001400c899040d0b00300e110462005070710071401e44c07091307800000021350340f800910700070101c091040d501d400320402442030b8201300c4d51000c5e124891034800c03188907005d00c0700420303940764200007030b20740707042d401e401240381845a0440940380c0300c0c00510005042c00e11641880c40c0440c2d031b43c40226000780c455600769031440d518000030403010760588a901c94501c0c49442107182c60007038bc3c5081e0300e02e00c03203071a11800e824203030403050020701c8d43c070b020f4920680940145c5401c07600950f01000403c040380c035820f0f1103a0031005403503044805000980b00d07883c400e803c0680000d4000728044684d503941c113000b8143c4242c001140e40507500f040142c00140c03409100d100341d96601034001d545507540d181d004400941c4800c2500c10200940c03040d00c0803c1c0030070100d0310303038100c0c1c540c891203100e0804140c5500d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 235296798 1250 235295548 235295581
    0x1312050c0301111602010e03030f03091203070203071202160b090a05010903150b06070c08061e1e09030d140615030403140f0c010c1e031802130b0a090203 68
    0x600a0703040c8885030490032580012101e2544540410540d559560710040350006405042158140309c04200c40c94110031280056002e40044011620804c844256402c400d0004850440140e0000d01001d00031404490184840980a03c1a140c0010040e4400e034802c0701280c10417540d040380800c5400c46418441c40b40d901826090030007c2180b4a15601c603041c0d1000d448041071200d4803103101c3d1955440300c0f01034440d00c41d231050200d044c50ba2181c010715601c2030121400304c6111191060000103154218000c1c0c0240a0108030040710b018220a4030380c0300101800101c0648003c204980c00a8841d114820000d00c803e4503002d80350500e9001c201d900200c0c41c00204031214104103100000c0c0e0062465004503040000883c3c1351000c59408842c64090140c01e00195428550621007042d44240150891001b544840c80301c1418158102e040b2800d1507030015910f1000310855000d84ee01c80c41caa00030303504012003c11040100800300d6000e4034076600c840b10b401c0d000b005001881c14100c5400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 235298048 1250 235296798 235296823
    0x6040606090608030912150c0c01140705120601090906030506190c0507060b010903020a09020a030507052104080c030a0815040203042012060717010504111905131205 73
    0x2846964200840192680b06848074584204401c00703010700145c80501c5a901c000441901691141ca00044023100a034891801216607510f071440c186400b0411002e1036004000c1e130782e6010301340b4401c07421006031500c0150006040c419001c0c00002c0645080c01072030061071041c4040c0c18541816518421480380070304d48031307090904004003031003a59444001d54140320340240010900412072030058542d201700c1d0b040079402a517101c401058640d2260000c003480b0715a640d08211030760340c045045529000d4034815a003d0541e841003a80c181c0d02c144c604a410501070060507107442018182c180c9198410000705011030581c0080107134400160700c41840036041914254a1450b01da641c5001d40072941190010241682c1c5040c4055203480f02014058002c003030480381e5508106c0009802503011403480c243c3c00d440500007113802d0626000703100010080386c55541c1460f005190242050840700349500030420b040c800f20f50780c4155800400020410014005207200303035801c08904007407842c0140c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 235299298 1250 235298048 235298051
    0xb0604030203060408032a030702100605030c060a0210020a090315060e06060a021005010b040f0902040b0706020307020f16060314060d080c010b03030304062a020a0609031407050604060609 83
    0x40025880110f0a41d50096200d15116540d035640c480d409654190202c2c5807070a02c801c07505030444041404001d502510352902110380c80002d15103140d09883c8180a10382d016080211509007906101d4060040701c2c0725401590b480c80e20301e102c500101d0b0847c10022000544131b5004006114280403915500144000306001590401405c85142c400140c1540c1c0951400074540190501c24003408103803803c5248144aa542e40300b041e08041c1e00702e03010348012940780004c00035084101d0710031101242c1c00c0403801802c1c08002d03280c09009410040c800303415801030fa0034078145218240b1800086086400e1440c0b1054140000182101c4c8519600c1091a0381f90082c80b4090f513842844220056114908a076a540c072441401e0240112103142038040c031000c0144410421541c020840e80817030b4910031a446080c00304429a410010700e01d03440541c00440308900482c509401c41c20740d042c0a8240051012441d000c01d81c01391340150000d0300ca64102d01c050108012003809000010200381340c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 235300548 1250 235299298 235299307
    0x402070f140d0504030f0c030b0411010306090b090604110712030207050c0607110d15020a08011e030201080112020d140a030908010515011d12030a03180c0302040e0705120a02040b06 80
    0xa04144913a00010b4441180034031a0020892900000b0000e958080202c01c0c0e2401d091031b0080001c0380030a00c840c0030070308149012854155078802c038400c6200081c100d0f07510784c4410307040c0401420b0a04070100c0703004e410091780000c529050709007104c20449a0300187d031440982044c0d41480342440348030f80300c0c4004000303400c046061645103041d202001c5483c20851074a5140c81c01041c8070301c1c801d808503a4000301d011400036401180040c100c1d03107040c540304036468800f40e00c0108100c403408000e000c28000b2005000852015401800303840c030291500303101c07401036280d1401e0404010312800c404d51107000e20340c04140d48000d2040c0101480382c02403006e4240380b5901c2c240c441045501c18104880c1c9031580100000d82402c043e43c0c40005030036511220000d0740350a407a82e00ca0004180800d042c040c8400800140105181c450350300481070040030b900f035500b08000b501150074850000d01ca5130350089070f030703a461140220342805224002d00940d1030760b01c107110503a04085040c1c2e104a00600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 235301798 1250 235300548 235300573
    0x12050d020c150f16050105010f08192d020a0311180108060703020a02010902090c040614040f0909140d0306080f0102030105130c090e0901050708010b03191a0402070f14 74
    0xe98100d40c00c503c3c001e42d2683c4031a40d0121004407860000f400d65801c00c000010b0440048507413406072588502070392040803007001c0601c0c1d40d0458103c000e00c030450825015548400d02014146c6445800072150950b482540006407984d60b1500305544140c4200702514a0389050f410355100e06d12640041440c03585080d03211034560100926102c140b40d00010070088991007980318910155004040c0c1d882d0f0306100c1025221070704203000d00008102030400300e4585105000550f800c8440c0c00800c964200c1c201041c20000d4101d40b0022030700e11541c0c06000b20001424007103889000403d40d0300003002458001c04600d4825841000c007030991040005000c3c6840c2c500301e01000c4d013505c120120300c141d5041000c43d01180c20313a00000b090440003041c000e07408410341115000c1c3c80c90366608803180e600c84511422501c010303110310a03c5160001d40a400c3d00b440d0704003162104580c207411070240c204130301150580e031003a0340c1101d0327802c2a41c1e4004100400c03a1070300f1944240c014000c00c403090030b18 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 235303048 1250 235301798 235301839
    0x50d050a080f070b0f01170a050606060f25020406090603050307060b031203040605070e011b061a04180605010b07080f0915120612060601021b040612050d020c 70
    0x2850040e10001c800030304040100c1241048541180e0b12020400091074800550500c40f0028090100c00000d861131046030010001444c400d007580060107000300d0b440d100104801607005a01000b154903050049001410780c80d14005500301e07181c4014001c00c0c00c5407040204540880c1c2090f84201d1038490107001180002054901442d4031180000b00485200d0000b45400c51074203400f50200c500104100070461a42c003c24044d20080d1108510362000c00019a0310100c2070240060590220741c140d00460010307000410030100c108410049468007402141c259141c410300490646030b200d105204002c43d5204031401001003031035042c107052041d9510b900030710031180000c0058001280344a00d0340c0ea41c1e0901011032030502c580704c1d80e44400c20050103200794110b42691107001c1d41090062000000b040040c07003030005030702034906544211101200005500c8905800660b00c00d00401c4181c400b401030303550b1501400041200000c0c01c0300007880c100c001c0d4142c5009142c411461203081021 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 235304298 1250 235303048 235303063
    0x709050a0f06080603161203030e06060913020d0c120302060c09060a050c10090f060f0b06090d1a0a060f08030702010e1302120c030105010311070b01030201030c20070609050d05 78
    0x551503c0c02c100d40b6000f0001e171502c0025402484000c0e0b00c00070015a01060440096043d807203900c0501c802050403c2d00f640301c81080310030303e4201e107003140080c002c0c1c211110b40100c50307440185402ca03040310343d07115284544201d4010201e0b00f896a03e5410030b2503010450140c0c04120f1101c3ca52a020206022032141e004501c10300c410703c0800300d1424901c001c280100d00c00300d180d22504115003c1c03541880125a040c500041d12550b141605441c5000d142d8094034a142078050b041070b240003000c10030700142242191042d40c0d070b00c8004407501844402c0c41d00f094003c84d14200c02080507810941e00d810400401e500404442e4010006000181d8001e40e80c00c100d014111405210300f00200720420180c0300e0508055006541202041051190340c809103058440aa8080107140f4109038a216688241a00034103801100740040005620980002400681c245028401618200e02c5414500b962858118160300703d03490078020660700c1541c21005000071241040a4101d903100d503900c5144 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 235305548 1250 235304298 235304309
    0x8160c06020c012a120207080d0e1309020f060f070602041202010f0207030b01060302071713060e06250501110c07050f06161205040b0a0809010f0912030b0310050a050709050a0f 78
    0x41d10700d44c1d05181b8028010b0100801085054a1200241c55402061070940d4a9083c0c49140204c1141142014034481c0100050b8041c0412800e02e401d441000390329008a9407440700c400c030801c0300400056060020340002d10303001301000000b1074030b8030001d042d42d0311030751803003003150300c10b9800300007040b41075101c9411103400d070034011707034921081c00c150503040125045c00080d4080014000b180055201a00b801c9558a583d00c1d4044041c00c0708200091061107804107008101860440002092030400c1d0a41803040000003040002140007801d10313040040d1042542d0400f0000b0015800c0c280710604882604807941890804500915610b442d20f6001c00340581c4200e00c03050ba4524060021600540080f85610b0f0302c1f1040c034000145850400c40e44501703c2d509100e004c1100c401e29004511450360f1010205070180ba0300e83c0100e0081126100341641403207491202d18440303001d80b1540e80100308010002c5400e00d842607000c0c0040c8090780c0241d0069468820030803030100030311103e13000d488 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 235306798 1250 235305548 235305563
    0x3190806010309060e060402090c0301080d030b0a030605010609080c0103050103021509210313080a0305071b03080d050601110c010503060f0f040c02031914030408160c06020c012a 79
    0x2140c010040300141991007004040c4c0b86400001d00140000103182403045108880c0403c82d5603890705001d026001c28400c14682e640003800400c5070034085e0300042d15521000e06603540e4981d0300e0700d0386025540e0a034401d4021491072101031102481c24807041035040b1081c2414000c03940b440d8080380c0105440035995100e480301040e400307503a03620071109003100200706205030750180c01202140d80b00d500030405101014090307280002c0742d00700416800f0f01550940c443c2400e01c0601c0d1206488400510081020404400c601000082061004c0d044a4550000000c2c20345030810000d824015030248044c44c80e8494030058642d80c3e03212007200e03440001540c0c000303501c00d00500031442c8894140c1c80d484d4040c1c2429101c03c01154000f01401c01561004901c5040c859612000c2d0b404809000301c0311110302c0b0400005010854103002000100c610f00f00c01001d0580540f10625418903d0300042c006802060a2058640e03008030215416000c203680041041032072080410070303410016005280c1e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 235308048 1250 235306798 235306801
    0xe0d03050c1c1805031c06080c04021c0203010603020a09080312010311030309060c21120106050313021f0e06090303070b040503091e010206010e0106020c010309060b040606030f0509031908 83
    0x85203800c04104211083c6548102881d1450126104e03000b00c000c00124500980070001c4040da1030180740c0481c0d0010000d8000d4911034420710000e98011400c2d001b1310300c1c03204810540c2610b00d200550007000079aa0041c0c541c250050010700781d5519500079843c51780141310584464441120682c1100e074041c4018140045071000700e411030142e001e84035488200803402030b1103084045101d00340c1180c2d1382c1f014245d640314048540000c1c011184982c0c540381e5404018494140a880107542014035110010f203a03030600d034005402e019407034a6089400c140075401d440da454004c5e0200600000440701349041581c1980825a2800f603d84c015094105840200d001d00400340210b03440104080c04684203d01c01c905000800e0602c01070590041c03086100000c0d94045044030941a14079990103050f41e204600700440260103a0042aa002d580e1514041d00700e554034411500101100c0d100415151102445401150001081e108281c1c1080042c414141030440340c2144907641401c2102e1203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 235309298 1250 235308048 235308097
    0x504050f1216030318080f0a080307230d0f05071409060d090b010810050601050901271403060a06060c03081003150203060907230d02120a0e0d03050c 66
    0x1855068241124140820a004401d06500502c1d500412440c98107a03480c05e5900d4005564402c0e00174414051500414a1032000410403002140c000c0c8040c900340d05030003031000d8507481414100d1b45440210074002120f15129545000c1c00703180401c28002000b041c41c160901910003185461000c0b0469400981d1449955500b000d44544420030745040144442c1c83c507143c1c0c010f00b800e01801c50903208200c46089011640d0092500c107035030680d1103604200c01c140c01520341c41e555104084603800e41130001c1c0403544085115100616035406101c41e00c070018001d250520a000e0000c03540303a800c0072020b2208541100d160030549074145080c0c00170f540c50350140003042119800c01000507190610103949103820f0340185024142c1145c1c08022600c0d142010340d1143c00001e4880c00da00d071900c9002114503804805082140741c0030740007601d0121a24120003102000700c50700042e0030b5545003451141716040242d03000c410f81c0b0b42000c110908080b940c00b02c20f40120346045400029442003401d9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 235310548 1250 235309298 235309303
    0x10030c020f03180102060906190203180a05010c09050a0308040b03060a0f0305010203190203090705041a0913050c0105131503060b070b0103200d1e02030a150c0504050f12 75
    0x18001c1c110300a81e40c640440c4410b500e90004807242460041c482e800125410b40c00100d260790140c503644c1040340800544d40c6501000c1c4d040140f541000800d00b80074011402d0044c800d0070800c62041c0000a900d500e81c0c071019040000907003016000e412990400e10018921808490039030f0869002c3c41d84a5943c0c1000409451041d00401e44269000ca0000100501500a58001c0380300e0500021079400345401001280400c0300d1040640d4810441081681009e13404051083c2092040d2900340ca5400003144944409495040e080c2c50014011424003106010035242e9003403d20303000d07140c0304041000d0b01103420603018888c09000d1a103061402e541c0254072040c0103060300f0395861707280c19041c2895881c13101d00344402d0300d03c104070000300c2c0300d420079024070050802c0d0028440350071501c0580391055000075005007030509189078406000541d400f0400180c005105146031680005881558401d031141c054010052010520041c8540c0d52201c58a91040100b500c1610506681c0c6a0551 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 235311798 1250 235310548 235310563
    0x110304081602060406030e19050307260f180414161b030f030501062a02121e010f181104090605161403090c060309010f140402040b01020c10030c02 65
    0x254440c2c0001380018203d80c2541000c4040d81248064501540340780008011880250000401d80e0300704010040c0015003840c5071081e200301c1a5242c104c051015a41c542c02c40d840500441c20589000c503d0300805020342420204030340d0280d605200d004401800441c0699014020001003621030440c0d040e2144205007148000c060a030b04070442900a00b400351410040c5404040001e00b080b0021590901a810301040d8103240c850319581c0800313250715840d072980c00000c2260304c100300000c41c184d0300d202000300da100f0502c041250300b00b00e10101902400c484024100d440a1400d0030a24200c104451142440960704101310701030380d40250f00024010312160302e008110798504814400c5502c0f0240c1000301c00100c5072034081026050380c644100344c0c08100c840343c41c035500207401e03804181030203009150801403d1001150310102070040b00c0594241f11518480011280100000c0d0320b040c1c00303482a00c0c00280007a000501c184008201c48102a10701e0b20149500c800c902441c00c0c0c401c00115 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 235313048 1250 235311798 235311803
    0x30c09090708041b05060415030f060e090622081c090302010c0930080c03160c0506070201080718030209010e0f010e0f041203290909011103040816 65
    0x600d4601981c01038104441540e096481074580034036007651040c40c1301c40e102900c00c0181307018203080c0303010b030b8940b1a5511649200e00309521402d2690900015016250152140c1000c0c2c01c0d040c601154281e2074101c0080c6545201c0411890075107105050f03680c07c004040c0c01c0000996125803081c5080c0215000340e00e4181103d1410721190b09065040d4001041500d80340d80d82c0c400340da9600f0840805102c2c1c0300200102d4101c00742e10140c401d4562910001c500e00c90b143c1141007080610000f030035a048890f601880007111b81400003000401c502d40d0010703182c1180e0107400c1011a800081c030385503004120105220b445104803040e85040f84442004550080410043d0340c0c440b0203250444400f42c0b8030f003032510503c40002ca04e068186881324403800704a03a03402d440c0e50366a141c0440f03d01b25400190203155854090b0b044003060104415408192521040c8070f0716004c2c0c050103c441c50007072a01c0c0d501d0740741c554415401d0207184112900a034005240175250400c1d055521501c00065000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 235314298 1250 235313048 235313059
    0x9061b070222140711060609091f0b04150b03061306090e030c120c1c0504090c050c1c020a060e030d06240c0201090b0c0f010501140306130c0b030c09 66
    0x210742d0b542009401400340440b04841d44a219180c3c1503040e1075000d0f110364940d8103034008800140e91410803105042d4072101c1e01c1c040f503090024070092045d9607449508000541520b4440c0c0902c41e040c0740c01100041071000d150b0343c140c40d01d80031070b501440c0030181a1511411074803101b00001c03041c07a0030410240010160030040089003081c080e0303881e8000075002c1200d004041070450804030710340c2901c6944802401a06a01190422551107070441114440500400340000301303004d0214803810440e0742081d11801e58544480f0075240c0b81561700300d10030203007200803c0d0050a0310f83c00318021010f240c0c00070012a100c030341d541d030003403c40c05440b102070599407905100081d0381510017503a2120b5a000612030440c510a55011100500c00100103070210b05465010005010361000803d00800c021043c1c4074000541e10030742e0700b540e00a80c4000d504164a0fa50134409140600c40c1c00e4001079070881b52074138410a680d402d81682f0031842094101c0ea404400107801c4401001200c6650400414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 235315548 1250 235314298 235314349
    0x140c060408030406090b030603190303110d09050f0106080d1b080a05040e18030f0d0207120e0a1e0611030705070306050117190204020a180312020609061b0702 70
    0x40942d60f03402600c03406001900c0d00f08000381040e1400f045030b00400d4050041e10b15036080020f000d5071108580011410513595080300c0301d0749001c49016244102c0d030b0390801300d00a01c090801a18043d0300b104102c8290b45094420400345100041d110815546418000c04008550194092a543c1c5110183c60f1904c0040e001c1c405079404401002a90035a40c02d0f8505529111601503c400310700020b401c85d0ba1040164400084581e03010f840300130744035080945009120383d215a007600b101c485280c045107044480081524020350031101603e1110b4410511580140f480154803d007072152500780b00520850f0b4a5100303052048401d459002000c1b168034588d40c1ca400001020240300f5000501300b031158040c8c43d2400032621713000c8102000350b1700201d440030350200030081d07010a5031207040c803030041c16000314001e100d9038010065020300c03480c1034002241c0d240682084802446480650082e508000b00c1c1180714680c1528070f40f5144243c1d0722800e881c400703c0c9074645245400d03800303000c8448 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 235316798 1250 235315548 235315559
    0x30d050103140613030c06020921010902040f140115140f0405040c0302040b0315030f0a03030e07050102070308040b0d0209040216031101020306012c12071e05010c140c0604 76
    0x141030303070701440c4454200c03401e80d42c0300030b031102462a9900e00200004c041860900108187e500501271441c00100000c600440c10300d001d02d001c0c400c0d07010203c066519a6003400079440c1921400c000c8a141420078005d0790110000403842c00014054001e03201560180d0b06101807040d081c0d11811104000d03c10360324406903181034119042481104c1c8034074140b09070018064800d00035034040710305682e00d0605544840f01d505010003200070100b90184074840304c00f803507410100505201e0346d000f41c5000420242d158141800c110b400d070040750543d44407010800c0007590b0741c0e04540460780c45060703c2c0e0310388040307942d054040c4c4103222100368000d001044c25103100b080310009a02e918440d0b1a080224402a9000740c20b0b400304903031460100d00c038820014520f0201e0609235481200c400e524000d032018010014904030060801d20b6901ea202d41024042601310700c1410010600034144502c840f45000002007955021080003480035141404003507004604000144030f50700b00815480e11661200b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 235318048 1250 235316798 235316813
    0x206070f050d050f04090207030e03030a0507060b0915101205040327290c070b040f0e040b04020d03020c030703030f0e040b06161a0109021c021207030e030d050103 72
    0x164001c0e80c05009070301040c0c2296004004030341ca80f0511040c0c190500e46402d506000030342080e0016400d02a41e0340040280c1d0340c0070300040182d00007a49075107481e03107002d0800c03400701e0f0405100c850284c00c040b03003444242081e00c904100401800c40300c0940f03011411038100c401c1c7c004136072511900c9046c441440101608040c0d034501007140345d209170751b12070520140300140e61094440c40003503010100c584041c08220b00ba0355140030480c42d400c40c1c0380003c449007852424500e548071300754005000c1001d102c00044100c010008000b00c036401ca16034200b6440e0309602c0301d0b001d00300034450000c04800cc000c01d80240309400d6503100007000d54800680d03900b00949054007110200e000203680b01001280c03407405104144d140e0320003410080c2482b020b05c05903e0f80845065040e20000001880801010000b4592a010304047d103001741e21108048140b03a500503a101300780306040c3c01400308200f22921031070b2080c1d000d0800c1c134001c920300c1d40d4010f006045100e04101d01c1d9120b400c00c4004402d02125 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 235319298 1250 235318048 235318073
    0x41a01030c0e070302121803130806040c06080103110d020409021810080f19030201060503030a03020909010b040b0d050c0c01150515090901060f0219031d06160308090a020607 77
    0x90b144911039035038881c0e00071412032180f2400111513080c0703c400300c0c03020844002190380d022850000c40e481c140e89102c0103401880103600030340c50b40e803010040004102848074150020300c80f13400c1c44030103541142d40c2d40184405d01c05509003d49001c440b15000c1d5505c135004050308a0300500f040e00c01000386000050405800c8542c0f90040040741d17000150700c1c074005008101c1002c942c3c00b60401c00396100780c819100c020850700b42c003199202c88020035039903001d00040020360900c0d100103a0325103000d1700b44510040c05030711803000c812003404104a82412101103480211303034100000746a80d44d8800844060003802c00c140203541ca082e141c8121010710400310025503008a9174a406150340440c440c1c0f46120740c2d091707950001044c2d401004101c0c09846021288182401514440007025070188501e5a580200f5000141d4207107191040d20002d40041c42290000c0d42d03c985040718555080001c5218654002c3c10021000c00160402c0d07000c2c41540c2c1595402400301d50303182c105084c0403070300505 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 235320548 1250 235319298 235319309
    0x140315040f02070314180609040e01060815100f0b0714010c0e030106050a05010509130e0d0f110a1e021309051507020a1e08070203060a021b030f030a0203041a01030c 73
    0xc2032080340c04400c0d0001580d21041c807440d41d8001000c0480284001f40e04081803107a0020389079164900668001c0c020100507100c4080144510107907084903410000000d044020645041d02c81400321100301d10b0030344191801060065544d442601d07064040c01c0003d0754032800c030351070702d2582180d03290b0001c1c2c0c50b26240400c80c000d000440d161020400c0712401c3c8e01c00c1038042001000100303154280380048865040d0404400a0400301a03100070f4280400d0b0400743d4001001d800340030702803c7d000f54905c841c102022000f040650716541c0c42c03055110b120a0606505641d0f090142c007103546038a0043c4602e090701c041802641706c1c61401c0e69a1b04117428844004120040c005003041d44001540c0c2c0500d03400c001200500380c105c1e086590314080b036003001d0b51059030800c02030026071410442280a010440401030365841000441295003440010507966034000f004400a4504035000380c0740c001104c2c83c1c00580d81d858500c0c02c00041100b06488085a10700c05c030001051043d5004104110345 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 235321798 1250 235320548 235320557
    0xc0b0a0c030b09090a03030b190b0d180201020703150f0f060806090318060313020603040c05030c0d2109081b090a0204030f061e140421140315040f020703 68
    0x1d2202007200b81c0f0780484039a070142e4040c980e5100441e119801c68660040c000d048012031f198084802913000c00281c0249514410010301944131010b60311030600c410b1100c00010100410f02d9000070344985c158170015100c42c4241c52240b030140b40c95804035003826400c140411134007955484071005802d0900c5402203070302800c0d0000c2e0000c403001c0111021583e66425141070310400c9010486281c0020f0a00c82c1600b013440070745401038803000c00075406030740074001c0805040d150008051520b89012401030242c0301c03031004a40041c1c0400440c00818214115a11081c840c071501110a04901c1e130240d00d0600c1804081c0317148420882c607207813501906a8445625a8a40303034440181e00c07171807000811001c0b982c0c0307440011a185510004e0201019800100c40481a604100c10760b00c3c654854911075140c1400d02082208070041090154200405600e4080800c07070081c00000744d081c50f001e40504000002150024242001502d00000400410609101102ca5002504512000c07401f15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 235323048 1250 235321798 235321811
    0xe030d0c030231090e1002070303020d021b06070201060602190f05070e0a0b03070b09101815031d03040303080c040503030d050a0c14041503060504061203120c1409010c0b0a0c03 78
    0x1c2e803c1c0170340400c40f01544010041d00d0203401e0814001d500444081c2d040650900801c00d6969a500050211100016090701030101c100172250a111001e000c03034066a16102c01004456008211001106008a400c0c280c2d0020b034181140341405500340105903000342c080c0840c010114461f0f040c050b02040c0c80400400400304240756031500940101905c40b001400a1050361800c07160b202176084541c80e103821003070103a207803089002c00940c21800800c410345204d101c60303d905100b840700c03080c0c0d525004504100700400d9940c491085001c05003c000000b000030740b015440320115001400080c08482d51341c656460906c0042c02c0983e1258041d5003000c40610180f4072030300414001d400e4204001e8605441d040c10b003100503130241803003024552603401c0041c1d15600d610031003004054400c0481c0882603646402400400c174444001c450704d28001d40c0c0000d090b880b0005c40002c0c1380701c4d60b52682d1501d030480160b446a4140c60b000741403c101408118640a8503040f0030752401136500e00f8801c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 235324298 1250 235323048 235323059
    0x110601030c0b1b3f1b01021207030209011112040509130807050601141f11072106051003050705090403050f07050c13110f13150e010e040e030d0c030231 67
    0x403040c0d1180080c052840500c400c0d42c5c500042801e001c03a040c00d04000602e130941d5500013840c241022110b5201007079021601c0c007620350300400c03052186403180c00645003030b14a8130f4604006c1e00a90180c0342c01444420700161207900400003008000c1d400003140c0d900e407101c52604c00e41e1690240142e003c9401c26440700d0b009810300c0e4203e007030040d415248080c0f914003c5403049420311002c540c0001d82d40308a0000041d03800061107031128841c0d0081c02c0c028441418140349054802c09001e00b1005562642e081011a03400706482d000d84c2c6040b40c00e44401e407500d041c06c4405010750b0082c8042c01e10700060680401000094000685106a424000000030000d03000700b110010504811071719800c000c2100c500714498018088480100c803480d1220361110340710754504240080d2503011459140201c8011740c5c01c054507049a4004481c24491200220860740d22070191800404007241c8640d070282c1c4aa000b40c054400400d89090200b9448454200c0c8508104642c02d90740b181b40c19480000c110b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 235325548 1250 235324298 235324393
    0x8190606171507021905071406030412110304091416080603100b06040801060612050c04030c03080d14101409100303051b030d06030201110601030c0b1b 67
    0x1a2400c40e10040c10000307940307a01c102d4818100510040450281c15100d000c01030240080d8030005008000604851381040d0002007000a800c0c2c040d0300c41c206c140304110000e4440c1070070001e040018a0a420030040d65007040c0d1460249400c614812405c04920b1450312411b071241c180710300040c0c203240c80c12480d4183d0554036030a0544ac081e40540045e00c0e6148140c4607a0004145100082c000a18003a51210068211400c5401042c000f803070460328552408003d00981da00101000c003041d01c1d061542e581d800592415200003000131101207990805450551320a20449001900e04c070039519040c100344450903e0341c010001c80c44200b2074264180d0a10b2458280709603400f010160311b50341180c90503601a04042c500340b4202c41c1e240c00003402030702d0500c060625035a120801040c810705520024200b4803c0da01804031661101004002091403c0c8541c0220707802d410354030355a5080185802c005c044085c0081c0400d108100140b1400c444040e4550f071b94030760700142a088019980341e0842c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 235326798 1250 235325548 235325579
    0x1e0305040c120804080a0b100f15030c0509120f21030a02071401231f0b0a0c020402041206150b030411010c0203150103171201090c050408190606 64
    0x1405644140824000300e84000ca401190b9805060810b0800d5668a0003521348181070404607111414075042c8800600c142039400081c14010041c40c030b5044c109501c03001c10b003200a1010007010748074005642d945004004030783d003010010b0841006441610000e59483d00205c940030b805d88101d11503400441c03001a905440b0020500d500d520b90f845003007104002c0e420200d0240d03000c0c0f8103d201005800c100b44542c4040504089001000c403250946c24107c40200901d1200d00c1000c002c3d0044042c141300a0b24010b5508500d42c075604c51806000850307090000c82d10081d0400c0c03001a01246540c009455400114812030017800400600c50702e45840c8031042c440c43d0100c010500206c1c00107040420203145901c41031602006440e000c0e0000f07840d00d546c0540b080d101c2000080148180901036801e05c3d142c0015041040c94558449001d29070710b00c05200d50210b0681c0d8180b5098114816402c43d0000c05680044440d540303c4e01c0064400302c91110b4049400300d00d001000515120840d40c0b12 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 235328048 1250 235326798 235326803
    0x50f0903070c0b0c0c09090d0f0305060108070c0512040b040e0a020f2508030c2206020d080a0212010605030a0c0e0d060203090c0402030108010f050a05010510260103031e030504 78
    0x9140882ca064541c8243e50060b120043d614001e41745c21a11544a002c00a44585440802404a4000e00d140500003140315400340c020542090b00b00046a42c100c50415003104461422210403041800c1190600740e8401c885410440c0000b0b0001c0c0c000d08413006042a6581a0704103092601c400360010304900c60f144d071909016006000e904040c000034024001c0310304209601d025004047d81d501c04c001c0d0310440c1c49041890300459021182d41125425040e10304010781ba00a16508020000c0d64034403103000144100841c030400106031103881c0c1c055800c6c1c0030032240e040259585030702001d485500111140103080c0d181840f55200580700f44540b810042c80900030031070b02070701921140080d50000f40144114803e204845080d9103480c40158003d2002400005484100300840350075500082d10b6040c003d42004014031540d92960020340d00300710076003040040702c8001d17410101392051040c00b19480418110002040c1500400c000c0f031039200c0c403a1480c2c0c1001e0300580c00d4003204e005a801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 235329298 1250 235328048 235328063
    0x628081209150721020f070303110d090b0417030f0c07031e030e0f0111060708060a14030c040504021c0f020109060513090b0409080706060f05060414040504020d1401050f090307 78
    0x34203001900841c902640111905c103a030420324a511240c0d1804080d94011000910410f4190101d0701041c010044900c04524280e64020315103010460140101c1c0559546910402c01042e460a010801c0303811b441800500503072107611900c0b910f600d41005100590350303940c0105040308580d521141c0f04400a900da190341592040280074030640c180f5241800303040c00103c81c1582640c540800c1001d1061025035075000d2146441428030900c0d03c11039205005010220b111a90741e5540171811100c10141514009811754490001079880e45824494410f0b0100500c00c12081c0a41102d010329068000e8944011003076a4441c12902171141c0720f260100c4448044080c494a03084d5008101c40003001440880e81d002140c480348242d910010f41181c800303944550400c00c0d0b803041200600105021614941080d14050b0964100c6040d00101840b0302d0b034031000a000c564520001c50445500800c542140910a001490090030251105540c400b04200050a842c5000007100c5486901500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 235330548 1250 235329298 235329323
    0x3092103180a05030a050c13020403020114070303060b030a05040302010c0927110417010c05030603060414070306020705060f06040b01050412051203090304090609020306280812091507 81
    0x706254019000200c03503403241140398001000d69040110301d51841c0550060412090b4080c20044242c181300c001440c00350051108002607030700941031301c040b1080c450250356034211798601180240380603003017036100440100074003c06440315440903208074401c1c0c0003040006901c95042d600c0101600c69540f038504106110500c26100c040440154200d420303020548202e52001020309402c19040458541e03036142821031180b10034001c980da11081420510310354102200401c3c1c46420040029085624040c41e450001d01c0801c0303000015500b004045403689034501d8a00c4d124401900d09000c2101c0355408680d152a1502c100d0340c0d0036005864440c501842c19840019549a034401910325000d40c108080c400d290751401035208d1482c00d00650b54aa04026412046426541111440510610421a943d1107440341e803042101c080c603140d410703601500c0c40c005003600382c5e0b08520600c0c012102d014401c178914001404500034126101148607202000a040d0342c01290f001414070380c1da00d00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 235331798 1250 235330548 235330567
    0x160311060313030c11061b0c040501080715020f01060b04030b06030c0a060c11100801031415060120100e0705030f061303092c07030e120c100e03092103 67
    0x604c5410300510510351080c1c102c650400040f00b90708180a5208103024490072000440400c1c40307108003005d0100c5003000b483d410148956618000d90046068494030550721809081c0200640e505100948000f4441541c849040b2119900039200844003580c01d40c1c0894400e2501182c00b400d0480d004d056100c100745480401c44004103004001e13548680812003d01c503640b0343c1264622030b14220340760345180e545140f4123400100c1d54840f161640f6080840450708015001e20b4003034009400341380181030b1024034980c1010920780000590700707a100710b2130103150009640d0402c1039004210000e490b04117071f4480134141c0f508100700c1e4a100b15044000090f0100810411076074000e4020b1412010751707511606400710403484401804955000030084100d480d00d01d007803072503100d80149420701540a242d8641a030b1558080c0104002e2100441c0912140b0030400c0342c0c1c00c0030b110885007846035004801150f80c0780e40c07102060714014500c5080710100c462000c0d800100e0f54150200441c5050100f4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 235333048 1250 235331798 235331807
    0x804030e0105040305060907030209060a1401050a050d0515030708010c0903150e1b130e1903120603110f03010c1b051e010c021605010906031107020316031106031303 73
    0x600d41c14800d06200c040003184041103070510503003030b01004004450450040140d841030003440c9500c00c4585030f0b410301403044e021482e4280502c081c00c1940c0c4881c0b01e050305440c01e0050240c521009440c020030850b0410508558540d0283c1c00d800340c0d0400c90f25003061600765125502420b002c00c00666080001a005031684040f50380940c0001848032801d0080c2030900000340c4502d0041007841404034030903d40980110840c070002c44040200c10419035800303444e0030b0421000c002580c0c07007803402402d06000d0844501c40f4141803000708401c03030300c85c501701d0f45002c8901c000c0c038002c5100305018225130405104140e07440d0340c02d84a4041407100e2011064800032101030441e083d005000c1240c0c2a1400f0142c00ca5400c204d040000c14841e1030700301c000307103044170ba50310781301407000e050504105036600100140d040d60400d10b004104e002203c0d660251078400c2c900000d41600c22440c4440442800020010a90b44107116545070341d80c1350001c102d41030006603111003141d140b0310781050020f03008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 235334298 1250 235333048 235333067
    0x5150118170307020d051509030711011209050601121a09070b0a140a0c0203010c030614010309050106080f0303010612090218061c06060914040b0a0b060d020a0906090b070201080403 80
    0x700c0084070710344200d59010174283c080d0380204803115400307100c5d00003000918404140c2c0c4452000020750a000d442c0c0c44a501c0034102e0300c0c4041c1030021001c04280025940e4114540ea40c3e0088111001035941e0000e08100440d110750a98240350f40c4c2c0001c928541c1c43c480954080d0301402c0c000c1034000e0070200b000b40c040d44030704031043c2030148400882100025042c0a000118000e445241c5051058014035082d036038540130b00703801c0524042080c0401c05040c41c074090078010a10340060b07100114940280100615002100305100d6110075104060000001f1816248aa03650350202e40c4c0c035800100984007170a00c002d510900c122200d1b14140d503034a092035400000188100ea404480c1c0a001440900d110800d64189131100c100348001c40d524006d400c3c14078401d8203800000d00e01a1586409114090074000300c0d6034840044030300c5d9603184c40550f65114401c2c4070466491103803d20280014100d486944085100c0105c0011503500110540344001d806845096803640c40380e4048814800c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 235335548 1250 235334298 235334339
    0x918060315010608071403060a030b0c041a0c0706020f06130804090c02010c03050601020d0e0402090a030b07031b09030b0f071808010221010f0303050904090209040605150118 77
    0x2014070752078459601c40051070003800103884000716401e0142c802801660780c41d40000340120f0410a10031181c4858203401c044a030040c1d51080aa00c46030600085441079501500740501e507414440c411118000c0140110248034085982242d65000242e842e821984400d54860700300c80005440c04204041400c000345c401d443d90392616440c0c201e000c080b01c0001c540000140e65802c42110410380510842d81c110340c003400109000048850f009242c150410301d07050041c0d4001c00c042c01c45880b901c628201a6030f100100411138505040000e0040845145103c2c1341c8002130b00f032204081c0250001000e8982000b260039682d59583c0e410007d0b0340e000b400c1c03d02041a41003580720000081d9107441d0103403107200c002603644e41a982100313801c2c415609105a500c100d440c010807100342c10284810449902d030902c0340d02d648068000500921603d20040c1d0015009e10400c001c020075944482e212301c4568000120594007240112584121407005406d2000742c19014031812503c22040c2c0410746 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 235336798 1250 235335548 235335553
    0xe0c040308071a0903211003030323070c0501050703050606090d050a0c0801150515041703070b010e0a1811040b0619180909020105070b0a0e0109050319020309180603 73
    0x80d10714043e1104400d0445804003650000708143c41c103c00c0226002d07420b2185007000c80e0b0141400d80d2040e015982a21004081c10b960700c4030030401e50084030240d08860b081286100345450090405040c03800451012559940f030302c1c00042000d802403003070074024103010703041e54100907070641070044200f5103500a0f2120b118402d141000a29040c0600000d04a40400419600303c080004130a24451360062481040f50400c1e00c4102c00303045d400d0b54100e03000d1002d039101071090585001d040d445100030245c80381645c6000407c00a101840d014040e54108504120005450302e0001008518110040011120b600c00d50198501b03030700305c070700100f9005100628100d900c481c1c0140f0146424000030100b08031080e500c0a1900910b00f1400400709020144082c80155000800d175100340f4800804075600340c03000c80c1c0a0701c000d0340f240281d40340042c020081100d0b00e080c120fa803a002a03411410310000001000c100901c0031084e5072880d41c005c0c04121a9400000070303002d0345400106041d8251 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 235338048 1250 235336798 235336823
    0x1e1504021c0204050c3a02071a0a0b130c09030b06040f1e050108060108061603060512070906091a0603040623011e0602100905070506130905010e0c04030807 69
    0x583d034920030035001c1c1240e84d00341a0b0300c0c100d881c3c0048040760488500081c1d0510220084c03c22400a9100c0d000761401d19401a515001441e003082140080242030820f01901e00c10050710364100d612000614001301c903c0a000094001101e0a555007015640b00041e05044204009111404040d400000041010911085140540c0704981e000141010190341c4002c08425107080c80c802e440c090014540a49925810002d40a5943d00e02402e490400c07000c6030303184175406101f5841321003c3c0500401070754a100115400f160b4451150058003010b515003100062040303180e00c00c010144501e031917080400b024031420000b2a40000300142e540b140c0b210f0388020034240c500d461142001050300b4a2072103505001102002c0c10b1301e81001d07840e45040e020107020b800d800048100004002d44008070300400540381c443d0415003035030320081d000704021410b400b010b811800e0002c29184042030400c0b9aa07a12150701c2d0000c602584c000031034000800081c004120342500500101303002e514080020b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 235339298 1250 235338048 235338053
    0xd030c0512070602070b0906060904030f020a0b0915090d0c0602090a05040e06070f1704140c03160e060a06050403260a08010501020c03070e0c09011101020a021e1504021c 75
    0x6582c02404110780c4103600180c000208403840304100d4026010100402c11894040d01003441d04d40080c00203418000680c00c007a110a1003000b040ca00c0d141d00050314002c60500c00301066403410103222680c4000340200000350459000102034144103032554a0389288c0019445042c020342c0310110b41608009100310101d001e84840c000d400b040043c0400800841c07a120300d00600030803c1144000400a0240e401c8804162160015070440d41200d410403220901400c01850a416101c1c031030382501400c80030082c58004113030389508861454100407501c1e5034031000c00020300710a0140d0b00110360244401c0c80420060804c03484108a104081c02100c5103040c81024542c10514451000819120040c003844d41e06028245070007105400130101a800c000d005030100b40b0040c1848049a0003242c03500941c0e01c6540800d0f0074000280c0211740e40e40c000c0000a445800b0b070f058000d0925001e044040c10076a0000d2a82d0b8540003000701505240c0382c613820424544101814110880402c1c0181c101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 235340548 1250 235339298 235339333
    0x80405030a111c0b0a021804050f010801060501141801092106061212030b030c040513050d080903120c0702100c230303040605090a1a040c0f050d030c05 67
    0xa4540540c81d030b10030035034041c800c00c4114250408440001000c40d612000004c80e808903445e0080021030026071074800a6540c02a0348010025455020f0f01309000e10400011041d1054140c1e41050028000141c48170010756244264500c40071312100e040140079456109a15058070100b4149441501650780d80c1010020200e0318521640740c501d44994001084a24844c0398010416100c081102d000291199460009200710080505884040748141d983d0705001401560000030800c114504041c0b20300c0007001c1050070304072030b544509207501c52001d001d00505449521100300652400c00b1f0400d000060300c4003d4090107a00c1401c0c0840d071300584da20002d1000311103180c3c0d82c042001196050810000c261603280ca0f4440c294510391000d00207011044941c4190800c1d0049442d4071540038041c0703030036071602014003060300c2c5005042c03105500d014000d011341d028118400c2c000b0f40724844c51420201521440e503000d0964440740c40080e0080c01d03040c00d030f103008c0c609859003404590403650 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 235341798 1250 235340548 235340563
    0x5061e2503050307120e0a06110409021602040b19031103100204060f0201060b0c0c09060a05150309010e0105101202011808030a11070506091311190e040902010e0d08040503 76
    0x4002c20408410000b0241c5d101c0e01d540468000c01c20248100302012410715154100d1100c050a041d444805004070040008229002006088811981c480d00f134800070400d421844001c030f02c550700303000592000e860480502c6420b040340e900174410061075a640d280040c1065000c07036403d400b540308003407080c20072440580000c1926440b001903550030806c000b42180c0b00c64121010724103052160324040c100018070492440401c0e18099007680301c6c03900041c241e0000c1e45c0001d40c4140200400345659451402850103403c520009000300080c0c4456942a1001100d40076145411034408200081d84800000301c1c0c10b0041c107002014105102f5890310105081c0c00142c3d4035400042c0c000101c075888108589222454805400c007141020001842ca1061408140c481d440000000c1c10882d00c0e94040d500c1214a030708481d170b8030900c01e05001c04c030300646034284c0c000c85c010b043e204c91181083d00501c02400c0e8165190180200748504000800c1030459040d10440c1081c0004105070300c040114a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 235343048 1250 235341798 235341803
    0x705060325030f0221073b150c16030512090d0b0103030e0a0905010311060a090b0a0e12030c0601051c0b01030c08010c050a0903020f04021207030504060605061e25 72
    0x34203082c0d9152100b2000041c040c05a40c2044500c47c91582001d4500940403103071032010300f400b203426843d48640c60b800b1888489503540420082c0042169605000040c05000c5418050b1040741c1542580790382605614400509290020300c99a002c4002460060280c1d440007000c00030345080640303c2d6a1540400d03007044002ca11444111380b280d1a011a03200000c00c0c0510003070003198195500c403500144200000d9020b140e000c1461082640615072004c05030040910280d00c842922400400c0300c1701c1240c0c3c19000d40c0d80280b00d1031209401204a649007405200240501e03464030044c024054503003c400c3c10401400e0075060300240225120a000f0b601a950300b40c1c0c460b040c030320307500d08403010900710f4414001d0030001c2030210394008125004480d01101d031000c0703d04040b00498007900c01c0c040e0281c659101002046003254040e40414082d500511003049560307200c0741402940d1040c40701e1069034031202e44808524004000c018050203445070640d882c0d0b4401c4084402d080322551408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 235344298 1250 235343048 235343077
    0x207152a06020c2b120c0215040b0f06010504030b15060915030f15030a0323030a0207030f02070b0417010b030f03070303050709060504150905060d0e0705060325030f02 74
    0x183e64285032046111030301c80e28001c444d940340c0480c400c0007500c41040c2401240c40c8541710705103200d841d4024400941d00108852500c41c02c4e14146c981a8a0910b040f984003054608036800704400d94860403d58003500d6210321503c0c269114002045680c004140c0341540c0102c0400c181403c58a4458045044c200c225400c1030322410080f001c02d04091004195080074890500000c585590001d414411640c0608148941ca58804101c401c015005594425041000070030f012821041d54018140a4080c0d40c44849544030f081b0100c2c0c68095512410080300028442406040a81d03c3c2603102641a0b90000420121000c00309042030744080101e02d258102081a0341410b81602074598009181d01e0b000f07030007a0900801806038041d40c00386140d40d14107820151011030003a140c50014282c018001c50b11403060141940260038001c0e9080b002e07002d071440010b11410240c00f41c0b8010f03010018598031384800c4105a084558a0181c05020161210319621314201d1510052130140c440720344 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 235345548 1250 235344298 235344313
    0x3060219030b060906030c2215121a0f01090905040602040302130c1205090a060618060902040503120c1903030506150c0606060a030902130501060207152a06020c 71
    0x5800c46184419680c041c680c10406040c5595440080300d6020061020300c03030301d448c0382c0c1034800d8039110803d192441d00b84100102150502c0c8010b07203008a03607000d0380c40c42602c0c6000d49442c4103036a00c4040710340d001c00d959a6901d4241c0340c115000495240c0625100c0b82031a078030b14903c0181c420a032000c5e103015034001002d20641c10014210100545902e01c140080902c103d40240070740c1000d0b8030040c4465941c1d000c24001c036800d000241a040c1c2040090222641321078000c10000642c2007400d0040b0b203410b00c00a500c020600035038003203400050180c202400583c003030a2180d4030070080c1c1c032000d000c0c01c1c2e440740c1e24184c80803c4c40d080901a0b5800541461b00c003042c81009208110002002441403040c40100c04002800302d074041001d5490715100c1c456038800740c003d445002e00081d484030b2469102145210707160710084c101c84260f8210b59002e0307981c0450804011071048400005040d4203480c1701d401040740c0c401403104511000c211000711881d108c0c0e030100d1b00b0000e091040c5801a00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 235346798 1250 235345548 235345597
    0x12040f0e01050117010e1003051e061005210102040806010e071b0b0a0e12040603020c060f0609040b07021c0c02040f0203070509040b180702030712050403080a0810030602 75
    0x195039a01401082c00d00340000030400340c01d0491030a051290200e800611800a0140c141c01e0320503800441c0e000b000c460704c601d600340700380400c016003889a124501c00c00c0d00107908601c8103081d0b801115005001c486071281121045a0f43c00b41411003040159000c002c0084c03405001c00499000f41509912101142002000108400c10b0003d540080300f04082103080810a0303050380d10341003000c0902c0003600b880e0402031141081e00c0008030090100020030001541038054000300a52100700050310f00c6603803010307139100d240c00c01600d241e80c010310054005130000b40c200c1d0038603412000034011030301554a011030740c107603400c1144000000036444200840440c145400b4200050101c034805608514010798010401e0280d20b031403074411030311440c6864058460504501100c004c1340ca140305145029400a582e0b40c0c0641d001700c7e601b444490380c031107000d403282c6c0544041c2c2c2d0380503051915040d07084008440d00b60001d8038110354150420800000901c442c801060000e030a2000c611002e034086 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 235348048 1250 235346798 235346819
    0x203010c0504051c140631080906130b0a02071d040302060c0708090406120204050f0114040902041b08100602031603030509011826030402030304030611130f0510030b09041412040f 79
    0x75184040c1547c500b5180000241084095445010003501c580b43c40e00d210802b410b44003400c0d503101002c10035000a20400180d4040750400070303100300034142c2003414180c0c06020b0050b0801c0303078042c00503040100410b000d201c220000700446130080b5400790600160f64005021140b42c1e42c400c0008420b0b400203002141024020568881c400204040d015850f10251000b500a0140b503244030b00c1ea54840b880846d82d1705d90144079406441801403003603000d50700028243e51400c3e55039001000c06414002822440007084624004020752400100015540c0a501a04001d40403140b25502d841d04411600d42078454000b05501800c00e00a500d90003801070340e031201c01b805288502000403c104400350320008200c40031240e00c4440095600580100a40a170086d504030b0010f0102c103400c0018200352140f41c901c00d0b5801255000e4a400c84400f0650403100a2030506400c004100c0c0000c002c46d10b880c1041080d101103000740d9804e8100c50074400420342c061341080d041070700d000e0010b0003801e610 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 235349298 1250 235348048 235348111
    0xd0305091603030503060d0c180608030f041406071208060f0f090613020c070807030c050103020a0e10030f020c1614150a0201090f060203040203010c0504051c1406 72
    0x1150060400c140710700520011015040c0006800e0060000100d035954596101c2808075a8102003001312407501d4983d040b44801201c0410656113081000c040780961000c011140b210241d8008a4a0689428044601c28038106440e59000c0c805100301c1c0c0210f84000803190a4100799503c2c00b900d0b14002d001c01240408038a00c00d405071405c000c42007040c1d101c00d58040d0300b1a0040faa0401401148448000070384122160138440d8010f80500280d021b01c0040d0007001d90340b1400500e00e080b034498004500328080c41c000000041c01c104000c1d03a441c20704108105c00300300c2e6803070046007002c200e8144001340e0384013482c0010507074040c1c0000c0c4807000318442404083c1001d50141800521755900042c000301d01060a0180d0b20350000d1030f0501c1030f0003588811402540800080c44200301402c25800941045030280d0095081c04490740c2064814000c4a0a9500c014041e8000304032071403000e5004403001500325100c0c14035644d00780544000300710540c40381c5650045004448105414104880c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 235350548 1250 235349298 235349311
    0x609020912010b061b0705121c020d091502010621140a030c08030a1401060302040617160f0210050429040f0228061101062c0601120c020d0305 63
    0x1400005060f99560b1404591100070360081280855101404035800c00c00c240e404907900003202000f141d00310002042c022101200704020644640c00002d041e6100c0e03100909040c0054400041800041d03c1b00c00c1e48400032001c1c7c80001080d80c0c5440360440680071070307189a003e9080e81e03c100010014a214480c8034100340070050b000f104090381e00a00080d5036090000c09007000400001d0714107040713900c9208004044050f02082e17581d2860080c00951060240c4000100e041300e02400712014a04510700030162281c40e4090140401400c8442a40b400c503458118040d6900c0900540880d001e16801140a20005046400030600604014840c240070400d0b10310081c0810006c5590302080c1e01040383c042c4c0300300c0d561810203002040f40303030402c500e00411502d01040100f4510752142d0407401d07074501c0500030401d054503850160300688120114140a5801441e80350f02d544108074010303080304060400c410b4482d4601106000c0c1e407031411408005030b00034009202203582c18040e00e5080391 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 235351798 1250 235350548 235350551
    0x6030902060904050c0706020406050904140402010e270415060f0303080a0903140706060f080c0904060b010e060409050a050a05010305030901080405100c0c0b07141603030609060902091201 83
    0x20603980403601d24090b00314a0792183c0c2c0e80e440000c0301c14080d2400c40b5032141e40988115500c3e61548070192a680260098030700a500d0100880003a403504080c0030f029030b80507121115203410704000c12142c4240a0355075241d0030030364100b07107401e80400c24500380218410784001e01d1441c0100b2941d030499646a02c1001d00d81c1402d103040000c203402c403c80b2078000954020203c0d07403031001d080030349142e0544944c01210300f42c0001d100041c448590310480541c0c9024150421942d038070b0b143c3ca940c0350f101104d1300e9881001000403d0000b01660300800b43c0f240c040c1044c821488090b40040c11581182c1e20850003541c0b02d01c1003046042a600c6960b9005504a40810055040d0b8958503560302404905606100c030740000310f01031060800c100c805801a05a050001100a01c0300030001c4e400020112000071155010440c0140101c0c0c41490704045110007030700380484c60f44034012090403070070141d003850fa07200e42c0800d03202910300445018040102c009a40c800840c41801021081c4c90150440ba9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 235353048 1250 235351798 235351811
    0xe090106060801140d0b130b060f1c0c0b031003063c06090f020702011d0102031e0708070b0f18070515040e010608060310020405012010050702010509070603 69
    0x40e4105120034152451301c2c00c1603100f108050b021809410010f4405044000d407a001c1120741100444042840743c4141d0345e02c1955107070380e028008100894001994040454014101039103441d61590352242e000303988101400f43d4407203030000e47c0e078001d0b51816a1080b50050602c140f020a008410707901d20352004800c114594805000d03c05101d500001202d40200049541c0705505500036001502004804008910348401614000c0d8000c12080780400c6031001c001e40c0845104001c1c5920640603005946042a1130750b045d680f000c071408500140840074003a00b808200007502401010b071003400044403900741a0205040a08001c1480c0207001c4940c0d0250000c120104a05045030320035078070189840d108a0703021110380502d80004484901e40c4000084685c4d100603240d00600c019010340e252034101ca80004143d06c12801680d000c26403075081021900320b07903035041e2000301c281419180c41d080c0c8001000705440080e200313a00140c0d1103405010402e0303410f1000d03a00501542c103040042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 235354298 1250 235353048 235353059
    0xf080108070303031d07170c0a05060f0a090308181e10030e121204030311030c0909040201270f05010f02060604180c030302011a0a1809020301150f0e090106 69
    0x1100e105000003810140c44018103000e070350800200c02e05a00003441a251010340301c0299420500c48460384500e14801c8d000c030480741c7d04084192500343d64001e000f980c54810154201c02d0250300404207081003188005c0000f020420700400742c24080c3c00d5014000004130b0000410039505041402c0303040310b100620b0700f4509030395507400c0b1500b0b010140c10302181c2d84400c40f0640d0b04000390448280b00070100015080f00a084c00c8102c507100340d109403410008250b000d16070081d035020407558600b4640c410420094645002c00c40546c0c0310b8030515181d000551480c2048094044418a21010b4071207042c061141c094218800400f60000b803030518204004541e000b0350354000506994010f540c0e030400d045040c0144100b43c05000d4024540c05c51155503458024024402c200c0251515031020440078400c0c500880c0348800c8a00a814400100b11122210030080c0b00310042268950f40c0c03070307900c0820507024081c1000140f8202d940d640506281c11200f110041008100441d9a454100c040c0322 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 235355548 1250 235354298 235354303
    0x8060a050105180a110403030c170c25051503071205090d08090a020415061107230a09061202011103070f0f17030f041101030608030417070e090606010f080108 70
    0x400340c155030440d078180e11130508850042003491400c0200c00030006001c014142c01c1056840082c0c4078030b1300c501010000e411928182c0c0181c40007010260010b564040c00940c0e001d014075090742141c600c050896036603000142d40050b03030102c007202520002c070400c90303941d030001040003500b415820240024603156800701d88414030380100c41c00f440461b001160041c00c0800c0340c1c0041c280c0c00381c4100b02c1c5013181032200700903d400e44240d200084181d803814080032804170b8000111400117041d12034010141c12078000e11305141c0c0e03000342c02091200700040c00c00c1c42409040014044011982d144400740c0c000180704407101c4102d0702d45507008210700720000740c1d0600410b441c960011807421480e0711038a4101ca000030b070025905070015010040c8950070341c2d40c0c81b03454029803040c0414965519180c005405980c15845800c94030740042c801004180c0d02e042802858050f80400e45103515150b00c44454000800c0e10200c01d00d1b8850380c2000f28958000140c0d55800b580c60400d05460761405c0303103c65 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 235356798 1250 235355548 235355569
    0xa030906150f0909060f09080301050909031c0203060f0a0f06020d0503040b01030212031308060114040912080703020c061f1a070609080705011a0a0b040b04090209060c060a0608060a050105 83
    0x2591596141c0f91213050140d150720000c49599503042c00e2045805500345038141c0c1d002801064440c2d01e000e004140300342c0d00001150f00766070b14107101d000c0d0000d2a0541c40000d4000400321904030114214000d15035540312441c1000c1c000c2c00840c00565420250001d1511000ca912541030080c04c1040c0030104200011003411a581198401c16040d08000e6060030341c003c04580c00b0701448089004103140c0c0000c5010313816200301021611501150a0401060b268040405400c2800c05810260301038454840d0075840030050a026140c031509640951921808959038503005515100425a04540401d82001801705000800041c0b03a100c0d4a600301d8031510710010641941c07960f1800030011644203507121150428020003400e280000c05010450200751aa80710720760142001ca10080c19400340c1e8290790491032101c2c03d090500684500942c0030007415540148140000d41ca030300c40402040d40b141c01c0181d400b0030b419181040e51440d1400150010400e5030800e0300511481e1280445071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 235358048 1250 235356798 235356809
    0xf0803070b0402010504030b0a021801031a2b150606031407050a170708060f060c07170102040f0b0c0f1920280f03050a0f14030a030906150f 62
    0x102542d1601c0c07005980030b11859100a02001d4004108140c0300f140741d0140c600b4038803c2c0584000c50602200450441c5d0307441d852030041d81c103440340f91541800d000b0100c4210859100c0f21111500903842600b102d10721020080712444000c40d200300407403215018803002814181414842d9100ca5040c080310311000407e1142006804501c05000d144584400818149141850810303800c2a01c0d005000ba40205e601c580154003600b140d0785541810700c1141c4601100b00044e0903e01c0c10300074a4100650000141d0744503640030700c00440e43c0e0000380d000c00000c00450064a6a6486020320282402d00360b444401c1c52f43c03c50860910841d00113044040708541c81085007030707004548140c0101c00f802c20410560085803040040341140786080301d00c1580c00c9031050201500360344240400c181c0916000050903608909209000540225907134800e1a01c07a089908140160304881071031600003a1000c000a03850381d0280041c42585c1c454030881c65420900107110751308000400032560002c2c802e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 235359298 1250 235358048 235358063
    0x80d061d040812090304030206040b030702061005030601140102150a05040b09010507171314160509090c0607050703120210050106050a020a031b08031e0c0a0c060902150a0c0b010f080307 82
    0xa003100c4001c5c02210003841c0c1c000c00700c50b100ca03142c490340b030141d81045500170098800c0030049488244640305d80b104807403000b001843e07240c1c20f09400c0e0385034148052003e030540c070070310940b0103007031400c40b450314494008420001142d1919040c444140800075010b0045a403505d02800740c070541c400343c0400002c200003e8a4040e445c0c0c060000518030500710090b00b003c03044265964134810110303041d107006504a480311881c544034800c025403e41c0c1a6080b440a62112001c004d59081020140200034082c1c4d0076900e000d030341c4e0703229001c030325100016403801608244440e124650044c8511405403140b458890305050142002955500c200c40002c0c060205001a41c1d040c05660840c0420269106071081c3c7c40f0305003c0c440407000940c501c9104442c02d0244000b0700319030f6403842559410132240e80c1300c0d50341c252075840e48401000c20503000d07030700100940328015030848504020141458195540b02d00503016040c0a9000001a00400c0d03c1240203001080304080c0001a1922107400000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 235360548 1250 235359298 235359301
    0x15010309150c11010f020a090302090a0603080403060f050703021801140c150411090f180312010b0a0207150203041e0906031a01050901260109080d061d040812 70
    0x800c1607412010340346049910382000c0440e1002584110f101d450005014000d1081c0d1700120000c000343d0040c2c0c4804c400054104100300b025140078425a50040c80c0d404001075165129202d0712034540c4160815600300303860301c2d0051303020280c80c1301c2d403540b00245180841c01c0c410809074080c0e813110a40d200d10704021021f0480300d1424805001c40300d42c641c0b41000c0780c000320805241c0605c2e503442210b003904c0380600c00030700c4141c6e81400b00e041841408120603031006640c54103510491203901007245500c61000b8480c045080ba2440300c900d0281c00c1317103096030740c03210b02c2d07000300030701d40643c0e074100c0c02018442c2041c2c0d00800350000103807019120304025448868045400401500c4aa9803001560b9070400000005000007545201c188000402c1c020515a80303071021302401c01c20a1044000801440541c07040ca91803040c002401a0f410400210310500c103a160411590881804480c0380f80e66403004012501d43d10a1150a00d07070100030014440c80c01d0744801846d800746504207552014102d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 235361798 1250 235360548 235360553
    0xb0616110105090d031d1f080a0203010f150c080f070b0907030b0114040f0c090810020306030a0609020102030702132c060f0702120d0515030f0c19050a09051e15010309 74
    0x503c0c0340c0c80d20300141200324020035242d4525a22404503c0c441f02041111b808920b00760113074001c803030689003904400d03032525140c030061030403038200b0803d184200300e00a51111b0008a0060080c050600c0c28450292030304440e080ca00100f000203425402c1c0da5005040c10400905290f040c20f04544200f228800040324181c080b501034000521440186d91808000c400170305e070080c205a01b0340340c4c043c04070383c0408121b1200d40d00300c1c882522006c2c1e2661000c4800c2d80094855004a41e0141c41031041d241840c0080d8003050b4580d150406003031901d80c0300e81005114041c44020601207060b0484100c400c444090000c58407000d01406c40491940c1440000f0300442c002c101414400200341d070040c1d51004403001c0c000c002d02098801d070021342c2c0176901c041e10600c0c0000d075641c042d882100142c50441034039810414648400c02c01d00e88442c01c214800140d43d500c0c030114200a000003840132900d8504080d90300e44107004400c14046281e00a81800213007000f80c106040100002c0c02c002440e64800e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 235363048 1250 235361798 235361837
    0x121401060509120f06090105100303081605040306020a0305090d020d05070206210112060b010c021f0306081608160b0f0d061a0c01050c0a0f050d0b0616110105090d03 73
    0xf01c200403040c4145800c41141c100c000602c20304c02c92404008224980303960f0b0480c401403250f880080c001662900200b02000c0342d50002522000c00c0342000c5162079980e03603840e41030340c0090000e81c0110f6500c904100085001b4410019400c040b44060084404140e00240c124060090040d00403180841c0d8900e0850903102101018004a05201e103030703686d51000801840b406410032580c060810481407965401003a200041d00d900800d640540142c00f282150002c043c0c040190825454003400901b182007400707d48114102c1a18140e0742d5820260854608101d1301103618500c580e00c0001c0103030803e02e505989001c050380500c1980d4132241481d0001501140c2c11880082c69880703100f054124180b00144609004000284800d81c2c43c0300143c990b5005003000d41c00450413450320000c599114000400050114100014803898000007003042e0741c0080c4542000c00700101e5206052280d1411201c100c08400d10741075140c9040440414500c00c07585400070140645c40041a0b01d85114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 235364298 1250 235363048 235363069
    0x2030309030a080a0e0a0f0b030403030b0405090a050111030601080103021c0204060b0702090901060308030604020714070b1c0509100b03010207200f18060907050c030d020307121401060509 83
    0x900b100c10b4a030050a05940716400741d1003820220705160520032090828614a0048441e07141d0a546481d140c1a5a95900c1c1d0004004504059031044d10f054603607118840d10340110309030300c010801c260841c0b90403803c668054103880e00b80082441080450b83c0d201044a05680d41900c014161700007034180c07020885c0040302c000358498240400032880c042008060940c05000716403141c2c0b50341320351218500700c822074000508400b00401c000340e0982132035001070584611924883c20f0031148070580e10709280d41504607149184002900316006c1321642606110604050304c01c1029003045841190741c0d843c0c54801c91030640d203954210011341d60a50556203490740143c100c8440040d012400c6a02ca80c4505069100780d1000b400081c00c2c2c1016034000034103031000c800b50200740d1201400c00070f5045005141c5410003804000002402406202030041101c0d1400050707200d007459900500703800800d9001c501d08507d4a0200200303480140646811103407107040040c1c1c2c0700001004a0458080b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 235365548 1250 235364298 235364317
    0x91412030d060b09040c0f020a02150c070806070807091206150e162303010306020c071509030201021b090a0e030408030403151d03030c0d02070b16020d030e0d050304020303 76
    0xd0404009210700f02c44000306030070ba41c2110100000d2901000c295030520186000e1801070317010b2902c540060618801081c1c4903008000383c02d081000480c80c40d85041e809400010407504203c0600c07018a400c001c0072904817809040c180503040c18070700580075105200c2009000c40e61144188081a0085c6043c0001b0703005404c810810791070410f40d030615600d01010404001100c2629100092403040c107009010180d2960080c0b4603481d43c0c07101c20184d0413168000c40d65024501e07000854186440824080141a0f141d41003c107203540006805c00b00c40540070032040d100d9090402302a52171801c101e51210b0282400250101c2908644e8958004c1e9000340005200004010007440384070b070400791501c41d20590500a04940e111440020011140e040389554001d00120303980743c4101029210015034204014180300217500e404040c0e000944074500f03291502034804800703550520001c2c050740c000c0e04090114005221314a07903640c808680740b108124000c4003080c11960144110b030010f01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 235366798 1250 235365548 235365551
    0x4120302040e04110109060315260706080114061e03100b040612050a0b010f050a0c0213021801020a030206060d030c02151b0705030c0409060e010c0801090b01091412030d 75
    0x24051501280441d07516804c2c5000c500c101c4000180310b842805031864400545217100f00241c0751943d08011002d510468003510300c1040001030541074108140e600902095445129075490f1412942c2010101c180041c003442c0100203482240c03122100206071110426001662541c8418405900e48840d81015103441400100080c950341d01c640c00d4994101c5101c07040255407143e03214481104d01840203580424074080240000d00d004101418042465003401802d01c0c0785135000900d81203069054102c480d46c0450503d4031020f28400480e12000b080c0020110324009445c0a5510700c3d00611580c0300d515246507441c2003601c200c10040c070346035020b01440389411901c0c4140e4000d4200c0040e0300480305130406002da100784000b030044210780c009009000c80000390b80c2400060300711000d080ea12151240307604e0003243c1c801d100d241c00580c1141e94405085d4108401d2505030781081c090541081008201400140c0320180b0007580280c00301c078180220310750f05d100305055008509036078000340d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 235368048 1250 235366798 235366801
    0x106050903010e010605210f0109031701080606010c111201050a0c17040305030109050601051b0105060f2e020a020d0c0515030405100509071e0e0105120604120302040e 74
    0x154201000d400040c00450082c4034040700008000c1c02c981e003e00c070351070b80048643d40880c203002895200200c5101d28009407045031490500341d600352508840c045000a4070003001c01d4000742d00d498070b14017508940000d0300c01400c03d000020a40135421101400d107480d2041200101d96070540500c070721030b2107000203004078501031600b01e00412100c940307103012034102c0414100641d0400c5c4114412941516061f00756424420307500020000188a9414402c080058581d0304250741088a4003021031000030403589011400d00010003c45643c80d80a1080d4404003400c0d10700702084008000f90350040302107103030700d42c0c40c08914103d50000301940200018140740107004800f2003402c10764900b40c8155880c2c041d0300c0c003194058803048401401981101c40400824021504819003142c03007482141c2d6219119903c040c10100c0c6110f0b0303d00014070f100020071451180c084010b004040850304801400b030f40c0c1c0c1e0703c19250340d0020001040102c0300c104025000c0d0113170b4141c5004e040001c00c943d40b203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 235369298 1250 235368048 235368059
    0x12030903120c060a0c08040f030e1c110102030307020a0f02190e090c0907080103060902030f010c0216050f030a080f0708161505090d0c050304030b0f041e0809091e01 73
    0x42c1d0151240c0041c6000703101c00128100c0072406000f010142030381e01c1ca0641d546549400019605c508403c40030402d80f00100a45a0b0310b200c01401c4000c1100e0321120004c000d440d000c2d1071049520701c101d05642040c42001501d90f000303d4036541480c0c000301c141d4840078407440020509c1d207880006d1308032500302510201ea03002c030048080d07101e11070460480d01c441b00c2d00b000300185080111400303030011344030b1001440068110b400246600d8809400c8a95a150482c81c0e542512803001e482d0f001640803424410308104405058802484291003c3c0c400d0b00c11400803d032a09510a07014108410010340041c42e118104101d802c9290000e410750386411203070000c1a4502402d00080c0c40b14400f131002118000301900c0b88a000d080e2003401058650b11820080d280281004401e5690340800d204c000041500c2c0c5400703174170403c2180c60712040c500c1c0625110030047c2460320411141e410204003400003440d020111041f041007129510768940e2042c138400100201e0090800e1410400e8000242 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 235370548 1250 235369298 235369333
    0x613021b0127110f1809060601180f0b3f0c03060a05041d100501050139020f04020c06070801051c061104030c0e3312030903 55
    0x302c5000041c441099820b103080c001c60340d0100550040d00146180c4100d00280c07800001e21051101d004c0d001020103d4090038210150f5000c82d00c400464100031b08000310b40d0ba02070811007406014400712402d107030420741400e0600305103010b601c07031000e400150981e0240e00b044c1440c09404520344000550010303480303008500744562001e42074004e0920086030990043c0300540c0d101d51030162490101c94980001c020240c1010000003504114076481e2a142d0b020a12038462510300b10034020403e545000001407140c148500c40a010b02400c80d01612018110044080b2a1252520b103c0d444100c1d07000090782d06202078032043e80310348005400c0120a0000c600c180c8255255100c090303042ea40c1c1c1080c003c004014a50b440c10b4810304104e01d400180c01980300c000c0030351100b07812a003015265551a020190300c0d0b00f0980c0c14000c01e10401114040c51a0b2103038034003c1c00d0345040400120160808900803546020314800d01501300c092b041c461040040d41c4404200401b160054560340300c02c50b5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 235371798 1250 235370548 235370561
    0x80a060c02070b0319050604020d1104140102030a2312091b1909180c0b270a03030e0316090b0102010b0301060303080705030411150a08070f0203030613021b01 70
    0xc000d4001c10300005000010001940c1c402c408900d00040d0800305200008028003006103159802a030074480e900040762148944203c40d60300c00303041c640d0f56050801102c4008005859070b4112342c010000100e80587c4001100310031025000e08004003258041420702e03c0c020302c0c04210007401e00c00104000144001518030482d00701c01d0940c5420103011041c0861010003821b08401d8a81d060010410000594070081c180400c10302d07041c0640c00c06d60389070041c001469010070034805001c20504c001e03850503008034049080c94640c10707000000e0b280100360840810b20001e81404058000c4d007843d0744007400035080ba0303422540075021081d03d500101c0d004005055609005603e02110b4040d41e040500c00d0106a80d09074595061580d11450225200c2c0d00003030007191000d90518400000d034841c0182400039614910b0481d4440d80401c80c000c1200800074544003c001d090081c005607a6000b10840e03410440940324016213889207501000039110702c00e1307506666810b1401c4000d18000650010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 235373048 1250 235371798 235371821
    0x80a0c050f01111c0207120305040305070b090d0f11090a1d0105090303060f0105040803030c0703030e010207110405090a0209040f03020111281205041a010b0406050f0c07080a06 78
    0x94048164240045961640040e81141103074000030b1201c0484543c3e03513144040d50810700c101c50340c1c00e448100c0f420418481203402c5007c6030700803c050003002410b00000300903203100c2c03c20381e00740740c1d8032070001300b80070a202e0014250800ba101490140800c884846004400140821045080c445488001062446402c004c1400040c6c1042403600c0103010707490051078040c0c000c60641d19000304002040103417074103007818031008001c005101d04d0306102840c810307100400744030707114002814064280c0d0003c1d11105140d900c10401400050861007042c2d07082002500d00007505d035680c031782161810340c81d50f1001e0361106030350080204021203261007001c8076100768001d1100014410511066010b246c500c581c403a0214550f1030a1124246408000100e0b40d10b00200d030f0703481460607002114800c1e00d05076803114540c500300303040501010b8124014201040d1441c6000d00e81903000340607016482800501c18000140090301c40010041c0700040c0ca258001c4d1413418030b49d4a0326100074249030550 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 235374298 1250 235373048 235373059
    0x3a0b15030d0302070506010509060f09041a070e0306040b0703020c0a0b04050c0102060f04080d06090f2f040b0d09050708060a06060903080403080c0106080f0f071509051009080a0c05 80
    0x1260300c42c0c0320340240c440040c0d001c8000c01c0c06900301820804030060003010a50070410b040e401c1103280d40c0307103150320380075074000d14051104000d4101606003505000344040140800d614840c05d007500d00003071840c1d105030400500c5896843c0e4540c200c0103403117828111441c61017851b40030300912000c050407a000701d1290742150b0489140200598a03840704803440400000b034800060082040040103040a4000f410006250b40e11122420101c40650f00402c0c80c4584d100c280c0303480842d2012045125291080900101c581d903003042400c148101c3c040c45940210126800310085e00581042405650100965454644864030207030340c0c0008590390300003503082c01c00008545000d64245000e90f604014561f182600315181c4c511a40d210320601095596a0f05000030010010f10a10811200003800303000c400c007141c100103141840c07503001f4601000d40745102241103034105090008a440c03d40ba04a100c0b03099070700540d20f81d04580d0203141c650040e0b50301841007042400d08042034030030031140e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 235375548 1250 235374298 235374313
    0x210030e0601140d1214030a1d1c0f02031c05060a090501030c030b04031112040501020106080601051003090302151509130f110f03030f0c0105063a0b1503 68
    0x140040d582c001c10501070b8000440800203c00704500388a0245c03034080300d042c00c2e8014901c0c2e22040034298400c6580204581e6182903040d2400c4e0400005040081c2d420010007100f0350780c0e2140d051303110030016010300740944040107403d424028002d440c01d00c480320341252040340214600c036000e40001c03225a03106100f611004560030f00548507050680b90010003c64400c2c1c2140c3da500038050700544290280443c280404c86a0380d01006110f903214408015140c803245058006400c2d504180c003c100c4a8100358018002521401e0003c529040d851901056419250400382c0c20300105400c02d107900c0e0807240401c841240c070f1056260307a070b01d003d6900c0507a41c1d41d201c85c14020b500c0140402441140780a11400101e0850f8408110b807240081a0a00e11542080040c2c40e41d40441410320030b6034004140300b03c16100038818558040740596009a400807050302c1183c400d22490320100c40031504800b00b60903c41d01240c88900d00364000100d2244d420300f989280007040041c01c0c000d11a205c0c051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 235376798 1250 235375548 235375559
    0xd1803080d0b09010512030304060b010e0301020d091101032703050403082209020304080304030c0204020c030403060510050103110f13090c11010f11070f050c030a121b080a110a0210030e0601 84
    0xb101d103101b191400303000c1e43c10f42d12690307500d0f005483c1e00306215041003107100070700c64035039401c0c8024880c0c101c45400018140c13480e4a440c8249035078041c28a81030520305400c3e512a1102c000c519045420317000c450700c100440310325080c0c80b1030003607030009040d03a40d000c01c08002d40140901030240e02100c4001c440d0010fa500d83c880401e070700c42114002e00781c070003e00200d40041d0080d6003190030284002c00150412080319090362440e00541d0040e21030945078402c2c06900d40c4103000c1200030b400c1c2841e0900c50365440a0b04d211103403094900c1c4c2808440e00140d00840303007480640c0c0d400035046141c014032000c10f1082e80240f0764200d03000441c00d90351a24030b01400408462146010340d00c01d004071142000c0c020f4503104224045032505540d00d000c2c80501c0d4183d940c05000070003400c0d00c103003e210700040100307500410101ea40400301854480740c480807404200c0c01000c1e912080d44604e8000c905400707602c481070810070490780080d0481f440f480340803189038064102d01c1c00310103a60100d034039030381c0c0c2ca0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 235378048 1250 235376798 235376809
    0xf030c0503030f0f0c10050901020a03110f030105190905040b01151107060e0a0306020a18060e0105030c0702010c15050a0f021606020c07030c03060501060801080109050d1803080d0b090105 83
    0x10b00104040030802c200e031484c0240308602400405240d070081d601c0014086103103c050b1001110f005520743d50025030951010b816101c0d100200710340f41085820241001007502c00791006000d0b09104e032602540d1802582d108030202400340102c5e0106214608040c41c00300c103845002c0c0103d825200c021400301c1d0000d8426141c1d42409850130000304440c501c2c100303003900c10280e01740322603401400c030301000b00116a05000034003012010f41d0310625225068040004500c0003504054200b0100b0303c0303000400d07a4003070196500121918065591000300d880162070031201010018506618000c0d4201d544d01d0039406144030382c0309a80e0600004156003504002c80c40703242c2c80460070742540c5446c0c4010078000d078080c0c041c0400782070844032a10349a0b12901c0c0d9440403948202da034141c44d14014010340c0c0c1d10890032401410800001d00c642c00d074907610a03031104000c1100000b00001c05001c26003206402c0c8564009603041103200d5561044034002102400c1450340c414000c4400d68000906030408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 235379298 1250 235378048 235378057
    0x50604150209030c060f0408060108070303030c090b03071b0b0718090e12030915180c090403051903021903020306090601090609060806030102091c1505060d1412040f030c050303 78
    0x34050004e10003100c00b001010380241440007803e810501010510900170040d882c080c158010080c02c8980c46d40c903005090396074100e010810018110402c1081d42e01c00400d60303804c40303d9401c282464102c2d0600f00310f040a450039018001e05500c0081c0a10a600100306624280702222800002c5440d00e03d40000c0ea40710503c3c40049900900782c41d01100b0540d0091a00580355206550700313007081c1415807030000d00941c1d41c0003444031035182c40a0a900d00704502210794105981e1503a10385456200900507014005942c9111000e03c080c04540038882e50441d00600c40d0601c0a100960300c408009000f5001290107070b00035000000170a2441d0300a107900402c03110b03582e5400b9280360400a00316840301014015503059902400580442e03070b550101a2003001d82c0c1c1c146180700900e20304080c6141c90013a440b50b0407551a103001e0020381d449610030641c0ca60b420120348183e031086540d81c50300d094440500c60080030700201d804118500d078155804216402010000031143e180e02c1010f071240f04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 235380548 1250 235379298 235379317
    0xb0a1502070e041b062c0603011211031e1912050a0207031703090607090302060a030216200a1e0323060106020304090c03090b060405041e0506041502 66
    0x401e520801c010784110408a52140c4665580c0c040ca203540c0c0040900840181c00c51000320b0444c00d41d41022100d17000348100d0404074100c0070b60b00e00140c0b4000c51102d02c01805100c2211381c991b46c2c1c410620080d84000422210003030300300c9500025004158001c074288400e8180035004420320719244403085c6001d00101500034250384407508402c40e081e1050ba0141c1c400c8070a6000b80140000407615040c940080c1c0d84208487d82da1f00e11380120300c5c13402d12030010064824040d0140052000d030301c1d9001900c1358011941001a82c82c04030400100d0b01008102008201d8868601c10f0303e4207040ba1354160000380030a4442a4050752160b02080c80c04000d240c490040c294140e00401c08a205041010500010040c0300c0c140c942c40402100d00301f0809802103009640700041c20010048070380b159142e100b800745010045c0108a650302e090025010309014403039611000428140305506101c141024401c801001101c1664504140c48000450342a81c07208e85071141014440700600843d0b01205 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 235381798 1250 235380548 235380553
    0x100b06030112020d05011416180e0c0c0105090307140a0305120402061c0c08060307050a141219020108060103050c07030f0e0a09150b0a05041401031e0b0a1502 70
    0x7030034000042d28203600c095080c0e07840344c4c1400c080c101059082c42041d0f0440c211801c540c0040c0b401c003c02000b40003810340c44204018501d40d0112840e03c141d0440f5060f01c0c1441c0103030942d926900380c0003c0078021000c02c05000e51814040c0500030a001000300140361069840c084001e1043c14856207400c020040580400c0c07081100900780d01c101d10459030310510042c021401e201c1d2100a14003806070104841084a6442021007407540e0402c0d41281d100004800801c10541068003260034202e140c800c031b0b419800c0802d850241991560316a000c0407030200101ca127000011741c1241c0406071840c0050740031508840100306554800c2c014188521410b940d0540f03032280942d4100c5031400081e4001c000c201008c2000a205c1c0e444020910084c0a00782000c5840b02c46240302c0d160005096005800e41c0e5001c000700b03009903030085d0545080b42c012086590304914440c0042c0c01810400044110100400c2040c0001c00041d6016020ba03c0c001d0310404c10349034030f0b40890b42d00d00c00300b074460342e000d86d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 235383048 1250 235381798 235381801
    0x80a05100e070e060418050402030f190305090f0d0305071b0f0b0310051e1309050d14040504050f01080615062b1506080903070b0c0706240602100b0603 67
    0xb5400785000004400029103040d16046d61029000500d001c113001030b0801c00d48a00034003066140800c01c118590220102a24901c100d07900800c001e01c0e0204402010720801082d100d0711940c0390812a60400b80103072042807071000901d0000d01d16809440101e0f19040d51038142c98483d00304c01c682c0320a403544d00032115180f50415a00940a410083c00c0d01200c1e083c02e100400c4c5911541d59444c01c0350340d000102904c0c09140402c01201d11940280442102d24041701003000c240c000541221414043c185500070303001c80c0c0b4003000d0900c910340015402178103100900c05211264680141241c1800b0150ba80507160482d02e000b00b0003868144942c0440c00340300f030745092068111318802400355103912200385a108507096007624040c04800703160001003802041801d070800c0500358801482c3d0091803801c4090b80e6003440c40c2c4000780071000c00c2500031070a80f081141c1ea602089490b1455000c03c02600c1c0381d00040c04200d034035406011b0040c002d88120303000b428064003e000b81082d0040c02035056 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 235384298 1250 235383048 235383061
    0xf290925050c19080d180803010b070309080a050327010c12050409060b03011a0c030d110906070c0501020f01090312090501110f03040b0f010308030402010315080d080a05100e 77
    0x1590001d1065407820b000704921a81c0d407031000401c4100d103902c9140110f0b1a42d03990104201250340c0d2545007091006c0d40410356000a69800480f8151041001c016031070707213400d00f002c44d02100d168020586074840c00d0703001014400000050030541e141c0000480e2109500c0030000203580100020502040c841036074080005c0c410000c07250b1125407468500d04007965084594141c0340c950740300302c1c40e00c2800801800300c040425210038500c3c0d05d2104052030480c480da801d903030b28840c00c1da820f040e04c2c0d56640655100b40800f0121001c0f03c00040c100c07900d480381030410ba02c090170544541400b40c402d005440c460484103000d80050b103601605e581004801c00308841c4013501890800b200c1d107540c4c41d500b080009103401c0152840c0c05805000320740324030301f624101d810548050b08054243d8000c1c4010400100706074100c0380d0090703081c640071606021840e0003a4806486401036032040c090011388910721a4080006841402c2c4404280440d803500d05003401c2d81d004c42e010348902c48032034000003101c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 235385548 1250 235384298 235384307
    0x602090a050609010f20150907080718020702010c0819091527090c200304050607060218040f0906050a0c0206010302060a02070b030c07050c03150a0f290925 69
    0x1100680000444106c0068200c12404d19041e0b090001403648110140450403030200044405014002c008022850404182e0345660350341c0000c000085030000307540802c40e40b04603601d40c0c850307611002141d114004030304030305200f02d01600008001011400e0005032140e0b09145000b40c0b5199495401c10303c8000811f041668a09280d0010191611600000c001e001482202c08000c865075840030f11403000d000c807482031000005607141c1c5038014081840f25030359540c205c03120b407070f40082c00595407040b0b01d0000c0c4504000ca29810392051604001c03080340d01c0a60490b100640c800e0700700700141d60b240c07458401200c41402742d0030300692103a0010300040c18030400501c26500140111141543d5440f1440f1860b80300321030102203108003050304020841c0420055114000480c040e094241039030300d411542d0000101074201143d221890443c1021043e480503e80420907900e0240301007035034110602d07445000d0387e080e0043da001c000041140c0b0011513034001c6a01d940c07440740780c145500c010458 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 235386798 1250 235385548 235385567
    0x5040c02060c1b010209060c070314070305071521020408070e0103080406050307051209151e0c0901050408060a090c0b030403080606070309050405180f0712140c030a0602090a050609010f 82
    0x5116650806c400d00803030b82d8400103422903881040c0145201411858038803510301c0016007443c0d051380500c03014800288041150f40a031a020755040c17100100001045a50f071103030314550800802c1c012030a600b00041030300203005035415101101c070340540e01e051855011000740300281034201c0a0200b07103e918840e0000f16013041c02c44c9440c90600f0341d900360020b5951415101640181e0000b0810850194400190381d40302d84142c0c0701c0d9900e10035080c1007001c1c5680c01850403140c2400064511600e038054810354020340b4103002154003d1615814220080c0066202522180101031000560904010842e48179540c566035642c0740c1d80303441d404d1007a5031704900b1040301803014401c0089250f854030311130f1905c0f40203003a80900407002c00f50401c40c1424103003600391401e03400040052005070955240790b0001507020001400049210056034240310030000d00d075516028404ca48810300040d0380151100e0702c0c0807541808440c0c0e1740c900700b100c00c1c811700c010140415108552185441d00804201 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 235388048 1250 235386798 235386847
    0x60f080c15131a18100507020405042609030615061c0908280e1806060d050c070c1203210b100f0e0307050d1b050a090605040c02060c 59
    0x102d07075036071942c15200c1000c5014200140500010030f1070300d140c1c008a06040d542e00021303101c500301e048000070020705178440c041000c0c5c0590b460790301250800440e1074000120201c5228000ca50303a0221807420755903841019124803a00c5000c0110f008040304018240101000601d260703c1c0c42c40910108000307240410207081c09c10b540d4a15034000c5017007100244410703003031b50b559000d00958050803001821202e68001d02000140074000c101c03038850454100c614040c4c440ca01075070703a46010002d007180c4540c8069583c000e080000b1700408860b0070020300b842620440b00c1075170103510b980c600d980502e0b4010300900021310400c0291b00484110b440f106280b102001c02180c1507503110702142d5164007884242d00040c1c1c1d0b2200c0484000d81c054400d400e80c83e4201c001d40825450500040c0030104034a902a1424200c900030b05015000c40f04410001d10024190408040c0d40b000705900600e039601c19103011b01d00b40f102c0e6000043c4041032191040d0710941d4082c1c107268440880303406a1107008030a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 235389298 1250 235388048 235388077
    0x17031b0102090618030d170105040b03010905010c180902030c1603020f15060111031201060302130911040302150c0604170d060f091d06040305210a060f080c15 70
    0xc08103a03210300300104184c1813808001d408012064003030501c0c006041042c181003040c1449003c054094001074141100e07011540400c0014860b000640188810ba00c010019841c1c038500d60b40058000740c155484800301800c9100c20380d0b8605a0034180e00c01250303d001400c10070041300740e09550303030000c3d000070078041d1046412442c01451034034540266100705550400426081201d075607804028620184124000795080c41440b0354072000001c418000c02040c503401040300000090700d456504010204140300b404061510074100c07903d5070007030100342c4c0100040c0c6044940444401e0480f03d080750040010110369070b4030b482e1001c1590001c40500c4007101d0420400d42072080d64007500c0e001e45800b286848800c3d1604d20f2031800c650b800e40303440c0100300100d8200030744031340041403040c4d0064041c18001c0e0345400007044020403c80b0f091042c000602450103001e5003071190340c407020503510403911990b8440d44132100c255481d0541c404555006000703084200300440810050328005805040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 235390548 1250 235389298 235389307
    0x80403050f0319060504020403080706020a0c02090a0501032d11010207090c0305011d06030a03030908070c080a030e040501054903080708040f060b24070b0117031b0102 74
    0xa411500d5000703540c82000f10811007140351091180348074400040200b15001c40ca0246155104403480c003424001034000750b800b06a410100e4000e048801c51203074028044031062501d01c1c50200180701c03c2c0016a000f24107001680410320000301e0a00f107050707090090300303102050765171000f0754400918212411801041d0000030b1901391401440c3d521086030f28086595814080100c0c402c1c80f0000f80b05420035414000d03c074840d100414460041e0b5054500420428002d040c034121034801c070400280070021382100021031080100b042d000003446076482c82e98050038081040142d480a000307036030381b10714081054080d02c076218802040d01a8040f6001d1004140b06448808820300d034840b0f4004034820410020415602800c442d038007000b107081141083c201929801204640c441d03004000303643d142e0341c08010756642d440e010031038401000c018606528220701c414064004e15022100c8107949800801c0b8280303c1c0641c145000205001141000740c0c00d5140c8003903809054045030715550810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 235391798 1250 235390548 235390567
    0x901090f09050105011d0637081f0f06060206131505041a0108060903031332010b03150a05100b0309030316020a0312020a05091e0111150708040305 65
    0x30f064000c1204402070414010303154050072000b04000d02680c0316101192000d01c3c56041c001e0224034030030030302c50701812303514500118000c00e5081307400241c0c480c0b2071444425030b42a03021520180d101e8030f1000c10302c03408110b44071410555085000e0900960840d00020300401a02c2c110250b00c280240004c1440003510000c4c0011540c090b2000d03201c000341481c00c5401c4c6520042d50500621000c0000c11481c98503a401d103880c0e00016140610202180d180300702403011059110710446054820035000c881001850b50100d001c0f901404595400c2a41810301c07481d011480c080320b010350402920a45e030b6101d02200c004c040081c0185803d200c81e64003c1303134145102c80070f54442c040e000029652802c181200515541c182a0300c03a04550041400303400299020700507810010380d110300941c035030681100aa5290040105e5190001c214113003200c42c103030751800341b0420b0560030388551b5141c20321402080c0c0c4a8015024449821391402c01240286104142c10b44e8424041e01c0c3c002d08001290 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 235393048 1250 235391798 235391801
    0x190b0901090c030908041706091c0804080d050a050a15140d06021c02030a1a0f090a020c0d0314070504030b01030f020303210402030c060405030709050a1d0d1d0901090f090501 77
    0x580080707541c44481f0606880c0602e041100c03a030091802401410300c2401c2940c0740d1640c5085151a508001d03e00e03001c5410400000c05071000ba1405c13820a001a1a01002240c000c0c00c0c01c8501c00400c07400c01c01d8201404881c401ca010954405102012078000410b0a2100061102a0413141c00e070f42000081a8100580c8404602c0e40e40d188000d81d4038104050f900050303442540c1c01c0780d8a400d03946010754032591002c0005118510036a500e0790140d80f0b0845000c020301512103a08414000d143d80110050b034594044602d034410100041a5030316440710444d014042c80c00010301c502c2c0c08000520200b80d900c104498031510050440b4900842c0903100701058840e602c8043c61840c0040c184400c41c80c0601c007071040720b07c00340c84d99070034180703054000b0707a0b20303096880340d542c41135658400b06440e41c03010380081803c030300101c491f280c05100800c4146c0c0d0b1461030284000014442505035511003404450740f155070b1600130564413a0381d0078408400010130300c007404005010754480300000026004e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 235394298 1250 235393048 235393057
    0x16081b0406080406050606030105060a030e0f160317090a061b150203043c0c030f0506010e0c0313060c02160305071403030309100c0c08070506190b0901090c030908 72
    0x12551601d20504007844c00000361007018143c24480d1800b440140040c0c0c540307070296a599501442c010500300e0241100e6802c1c001418040142d902952883c0c2842c2c510000c001b070101c074442c0b10000000c2c1d03544040d06419018400c104caa103c0d2606404100341481005030001c18140c1007a00400010345a0743c0c00180740c200da40072001aa0044208418084405c260388840100160844040d124081c642c0c60040c0900d5090807100e0040780818050240504885000d1684090181c1c99000c1c40d0030040d03581ca500344151841e544102c40040c0201d1495420f4138000c425130f1210000040440da41c4801070201110444114800c9803049a10070940c401c0c800010360041000e84042da04200c0301500c12880c420001e402270b0700420900028150014042c16400d540030300c0020101046281100c080d40760b0720020b03002c075a0125041060242c08128640110a41c68842c0741001c0300414010a5669800c01160f0160090004020b007051035000701e20b880b682e41c03800041c960402ea0728044e0b180c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 235395548 1250 235394298 235394309
    0xb0103170f0a0e0406090b101407201c050c0603070e0913021e0607020f010507080c0102040618050d030e1f02060f33041506020f100516081b04 63
    0x200c540140b5041c0c1410300c0f0f060080c050040c0c0901908118038041440030340f00c208e2000400c2078901e4100e10351404001521000d9600c0041246194094401c10840d0324a107200284034401000d440810214031101180a0962002c003822400008208010750f41c0c1000b0061001c2c42104c100c2600c80d80e50b0344142d0b6103e410944405424070b0344600511444003c45610880c0c20b176000c412480b0700d0750310f280548100d0b9604542c480582401000101c41c903014244004280010100345444917001c19006402582c0c0b256841440d070100504115801055034451140c101a0500c00360000c80c0c4558a400440e01c1e01804035040003e001c0300503903680c0e801c0b5800ca00160820428002c2c50081813031500d402c4044004940e0101c250300c880d541070301000180e03c25010035180324147c0240c440341c100002c916649042c0030006c2c1c1e0f403104060741750a198035041859001e450542e01c501c101c0c3c0d22482d4020701000380440d1400380d202c1411340303130b600000d000c481d40201e4600c0f2068000c82c00800a001501d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 235396798 1250 235395548 235395557
    0x2f0d08071803051e03090604050f190e011701110d05061801060513080a1a0714030a020a081b0301060c030e040f020c06070201110d0b12070306020c0c0405040b0103170f0a 75
    0xa00c00081c00c0320403550404c8a64030380c100f040072220755580c00081e81c00341c81044803032008a100c040e0000f0810342d048245080000c00680c00000c44c0c046400c0c0c014102c948200e5600460040f40030018200c41c510f5a10700704000d001e0203141207410507a8409a80280d015003005520780c1508082e440c000000d90020000a400064078100c0c0c0c501c030600c010050070880000c0c00801455510160008101d0603005400e04141c0c00051113544103442c40c0c080000d11040a559a00340000e003030002c0d5004004800c0415040b1002c00c514201e26120542813001c40c0907114203503401c04004580c8526400d0301902003000440c00d01695544500c50813900c02910180103030b0394840108190b0400000070030702415640751001d00c5d659078624008440204007140390015204040300d0000b00100e44000e0200b40750710a403c008400c00229600900601d605442124018804802000141c0b001118002c1c0038404040041002030031107505205d102500401c001d0504081c1c3ca100e201507006405410b0014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 235398048 1250 235396798 235396813
    0x609030709050a181211070906140f010e1f0c060219140406091a0403060e060708011e0e0c0910020d0801060305040b0f0a0e07062f0d0807180305 64
    0x81c40113102d040410fa54101c181400038295440d8440540d500c9403a680500c030300c0c05d62000d0101c60602485e0082c1c05510010020242c03140e040d14000c44412000034050b540d5a81480300c0f0b58003843ca103c00e0503100910741c50003541420303501605586035401e02810f1108134500b450014441c1d002404080942c0341c256401c41e5a5980c1c01400c080403c00700c40d00c1190200018401e40758488081c109881000d2108500c10075074042da0060f51140da0701c0500b105242c480b8094a1040100300c0c54061007031035442c01e1840c1d0b20340c4024038100006102c00314100c00c80c0c01080001040e03003c03a042c1c0c07007106280014204584103020030240f81ea1018981e0058202414403090180c0000d103190140500b40303810081c515013541c43d40320b651805003070810805121000500c0c50085a00401c100040a0301038801c401d568080c080c20a042a42102454400c5400c03040c03a640c0d0000003140006845400528605802e088141ca4120b00a000b000030441c80042d190200d40d210301212005510507002444030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 235399298 1250 235398048 235398061
    0x9150f0f0b090402060d090c0506040303020d030e16031104060b0309280f02040b030c0a1d010b0a08070f05090907050d0f150b0a0314070f0f0507020105120402060903070905 76
    0x2115450356919100b22000c00501015032030350300941300080444000000d41803080d007040300a0040e84d034400d603031041c4001008010940d01046001c20004e59440c14007064900100d100d481e007502203100c05a000c0218002c0000c0b0304881141c3d1310340940030740005001a15100426451703481220604070541c440070301e1070a8802d80b408001da010741c1e0115889410a80c42ea00d019a80c01503290181c45aa101c044086c1c082d50306120030184100c00410140009540c0e0001000f000d60705041403812480f25400000c40c8480c56003107504201c15030303031020b0f101d03600c00304150ba4401c0c0a105c420104030051005d9000c5884084840380903079116210750713884000043e003001c195548001010126170500d00446016201c045106081d144a0005c4640751072098030304800901684456903c06e02e094014409450b8010702c2c4201c86115036039070b40184a044140c02d440c0c9114148000f40002d004008050110444906081d000342c40105024507044103040020b10b4030510350068032034640e90304180190b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 235400548 1250 235399298 235399301
    0x302040608070509060d0b3106170a060c11030f0304020f010e0a0e09011503140c01180603020706020d0207050706230304080304111e040f051909150f0f 67
    0x601c09040d1034004e15200340440400c0c0c850240203481d400d09034440c10114215511710503170101042214070300f61203c1f2085421100c404c10205031006142c2d260030f401140c004501c04401c0000103a5500404d854a0a6a1541c001b040b08544000400c10f03a01140300c500d9030140010b20505c6010700000c4d480303041c40d00402071800f0f10f6000b06410300861041003c1c45e61581840d80c82110b40e00e080e40c10309507940300c1d43c480c05484000f841f504002e4251101000700301001243caa2510400c104840b0307114a0748006544014102c2e280d0304442200d80020000c0f207120750001c041d01c40c07081d900903007003a494580000990300301c0702084515401c0f001083c04590340c0312099140c400807040d640d000e0020041340711181d03484050000f178000310001000a080c0400780c403d000541c0d07005444100d0410340721022180f0f84c1012094688585d0070f00940341403030b448500440b4010082c640d040c2090b4440181d034103005003845076040381d140c0034981c4001c20340f500600c02c01c008001c6102e004109510114030560 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 235401798 1250 235400548 235400551
    0x20304060f0b031005221506050103050907170a0804080c1306050612041e051c020114071b170a09050301020301080712080903010504080703081014010507170a0302040608 75
    0x62540b41592250751694005020f0107021301d01d4100080d20b488a8441100c0c0801c10742d440c0f1000c01a14240074200048001c3d11502544000c4003084010744803401102030322816100d4240650105100344011065111949880310f40c0b54211605c1072050b0365050034981041e440411107030400b50a5000f5814405085070500b80c04042c20022503041100180807030050407103071354180d00c60b40001002c110380c080c40101d400141d00d10300c61070f02d581460000d540700c085030101801c0d1380090203141c035000d0050140000c95400103840b08001e56500004542600f0561101c1140d50325000107034000c1030f1600506901d00d01c001c0b440950303c5001301c40c050004410380c0c1c00f0034040c0e0700c100010001d00313001280d5002039400504218056124070304054100340202d84010b40c3c5540703440e007800104200a00144480c500c41c1d2110440c50f41c5881400081e04090301c2003c5000c00c80d00d00740d6001c1d41c4a8001451014442c41a00600d08822914001540c00c00710003000480c3c3e00040520101c0d400c5840c0c207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 235403048 1250 235401798 235401821
    0x412030e03010506090f07050906040f080105040201020d030b0d022701030506090d110d11030712080f010512070302060d180b011a19050f0906070605161d0607020a0503060403020102030406 83
    0x44189007007020320305c46d0864006101c0300030000042401c42c503a5440100311001460341101d803d0308981c0300c41105000740819031701203015105072280340c01d501e4017a0183d0303840484020211100030020f6020b110320215041202540b28640d505c00303406814000b0b41d100d0103140200020301d400d1626902051520700701c2c4a01c8410301c0212200316201c0c4000155854080e0b0480c6840c01c00581803030100303441c42c010750800428851012a1744415560300078002407042d228800d1650045e6038800610005250000c5003404582000d078062000d0705101e0000d20320201000303c00100750042041c00c0064845070b1744110f0fa100550030041140400101021116000a8a070b035890b200074002c802900100000401c0e0605c000400c0d0070008103208070596184500180000380e070780e2414a0004003c000440b2868007411500303141c008402c3c401c152454042c0c10500040b80798030400005c100302c1c3e0700883c804a900447c21800070a41ea10140003040c081c6109030000760322800d051410405484080c1482c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 235404298 1250 235403048 235403059
    0x6091b0306010909031106010801020a09050a0501050307180503070620060f0114010512130312180609080c01061502010b011716030b060301080a0204140f011a0412030e03010506 78
    0x5001a5903000309071541140c00c0c580300000c0a00c458030741a03842400345032000c60076024240c000030350a40190010a10f00505a544020083d1140f041041508003800340170f0000e44280009412980261005805880c1c07a80f030184043d590b410000345454095008240014140d000e0042d4114000481d140b800c40b90101034503503864036907d210f400901c14440c0303542c3d20800540112890740640111007010741402e46000d69031400f1a908298800e0401003100000d8040141100d10680c51007240740001c000ca50307907403941060f03890744c6015081101041c2c4103841d0804c440e68428000b482410000c060810b94a03042010804000e030842e10b2140b01d41e070500481e90b9204103180c019400d6550b1250111104110214412004500900d09268441e41058001001154880c3c0001c0e1030b10100740300700e03014483e51403030304100c0b03255142c1580c002c003403c0c40b40c1c001888411546440c8459000241000c0c1d4201550340d00d01c00851001c4000942c0400e4212115009074113085c080d50f94822002e440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 235405548 1250 235404298 235404343
    0x5040503070905150d03030e1525020c040f2405120601080c0607080c011103180102040b0d0c18090f1103040b060103020921010204150219020103050a0204030605090609 74
    0x31880c0d00b500900604510172410422150b04150290f4448824119442c04945500d0070b1850000429201035402c1d64942804480c0581014203540b20103200300e540e5409813480b0a88101400041c081641c0754400b25900e9845800302c031303c1000c2100100c0000b108990900c18640824007240300100d46034074400d908000010b001c0f030b032000641091400c00544100f9a2001c2c1401e08485c54061400204040e508000d280b2402001c91070285000c0c15840e0550030141c41700868540c200c1c490380c443c00b86d110340c060164920b448040d9100d1214804e82c0e01308004240500500300c070b1004e00940100c90310300d40c1c84030350041d9140984940a80700d0a200302c2e080c40c6003845d48990152010007006503040540000d160400750315686401c0310400e1038194454029040c51401c28041d40050141b1442d07590030303139030101016100042c20038081c1400481b200a01c03006400440140030300400c044034041d000c10000001452030300c81c0c648288860b00141c0a14241582d0103814205c0740d01c82000c07440500c80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 235406798 1250 235405548 235405561
    0xc020411032d04081303120903141930031b03060501020c090606090d032a080a110312010314070501081009020310080a0803040c0f0609030602090f030d05040503070905 74
    0x203a4043c1c10070303000704129443d00c0d81d0804044200800f504001c2104040f42c5d40300c104650020980700683e40714507950081005004507403507460403105d240d008011490040301c6d000c42d03100f00318011031a07850440e80c1d40c4451424400c1c43d160b900101c90100090303548403100e034046096440540c0c04402c501e020b01000d0f04d4100002e6940800c0240709100749800804500181e64520441d9140380d000381000d28040341c0382c100581031400741c2a400d0703c0d0b0704d00d0901c7d421000c204400004407060380581002e0401011290441d000301a000c401c01d000c0c07000b00120b81c41641c000c50303154021842194051811031800d4a940d060814a600032414050b000080c440d04854118a060a41740000307070051f260340d44c0388a04140f050941e880283c0500604041d0b20620040a000b50700c80c1d801414400a0301c0e50f110740d10181044648296000244000c0c018400100c9075002003018000003400d45114506400004c1c7c24a90401181070200303030001010420350800703014043c01401846010881860040d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 235408048 1250 235406798 235406881
    0xd0e030d090e060d0210030f05060a03020d0314121015090b0a0c0804051924080f07020a170a120912050a020312010b070c120203070302100c02041103 66
    0xc1c080c2c040c0c015448000100c1c262110811503a4443d00102260f1075903070922800307001030440300c410b070316001e080100186071802c1034140403048a0307001c0c1c0024600c180c291030031070300110071f250408a8850100540d00070541c005170007038040c210420300361010342d01e050041441d00480040c20f00c14421924810006070394908243c0700500c5140c2040f4120007080c0c60800c0303482c815a04072550110b0001a04004103003004460002d4400044c29a05441d03404030b8404c801d0540045250001405840041c00d298610150745030040410700445034402c0c00c0da5540700e02c42000c8908003080c00d2002c9004503c440c2d20120342e000300c00d201002000180181d44510030010001840c1e40240200050315038000340c42001195104680c101000d04503507100d10a0444d00e1340886e07000d9a009500700340115920541c0c04044201da81d0041c010b220051669082c0b110503e40010607000380020703815002c002d61034900510740a11040145d20350760b032902030410b0709414000c1c15095088070450915080c200e604 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 235409298 1250 235408048 235408067
    0x51804020d14210306181513090602031302131104031b05030607091e0605030a1e11070c0b0a140d02070606080d14031005040b0f04020c0d0e030d 64
    0x100a91150b603090401195203449101e108100101c03031410710410160b009500030b036010318800c80c0c010007043c1118624183c0306100340c403510112034403070303900d0800b82c58400c41e21130a41c0d0000b41c0200c1e0a4010741c40d080100e0308100e4146902c02e100e0a01e900c1140740142000001031510141002000c1c0c1180045c0d1140c052030000509401c113241003c1202000c945024000340002011512145007500c0700030010305c003038440c01c011000c030013000c484a018803403108016541d490359520704507526005042e014103510741d00d031592004d01000e6110964560300a10102c1440245080d5a4103614640340e914011168444104040700380101001594818407034204102d00c00b0380540c44502d4004060020b105082005156915240001038102c4011500800d0300382c207503c510650071007a003c103107000d1004444481ca2010920340c180b00b14034103544900503003d006480c0030021560200400c1c100e80c880e10300b0851a500120200c0c40181d130120702d05040380025000343c0741c141031921026000102 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 235410548 1250 235409298 235409303
    0x1709070320040507050d05012301030b0f060a21110a050705240a1505030c0d0c051201020c0708010c201504060b030c04060b03060d080d02070c051804020d 68
    0x1c071003030081c03640c444445040c001d580d0000c0c800c2256040080b4090310700e44c030842403290f8441c106400010900d90009038403483c42d03040141c001034641301400450040852014443d4041803550203040d45448032405803801c07200c1912104140b25091090b00c01c0d5482d1810340d07240b01e504102402d01941c18500640b0348941e41350600c0741e1036200e1441c00c1410b154041501034400d000041190300c1c0540f110145600032255914100496131020342559601000e82c0103254055001c00c1c41c0c40114108a481d01000a010302031403420340c1e440308001034a0703e41c0014524101e0b0b40105603401c641341e0600564001f86080e10080181503203041c1d02401640520400451125520640402d803800c00d2010000121510020300041d141c20300e0020010801c1c0101280a0321601a0402c240d0806120341c1c41941c2c01c0000746800c6540d004104007003082e521204032580602404043d03008241c50001d0031685110381803442c0f40c1800c0c102800005513040e810701241d0407004042c440540c4904440c0d0406c9074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 235411798 1250 235410548 235410563
    0x31106010b090118290f160309060c022101060506071202010c0206010f05100c06050a1a010509060301180219021b060f19030e07060e0f0301050405031206010e060c010c17090703 78
    0x101d092003164900418006c048040d10003c0d0180f0503030724a0b92038440c17052080c0c403820b60560301ca0000303c4040139014002500700303d844e2504841c0a0b02011800d044000c01e100204000342c4031030104845820100040b00c49081650725024555020301591501203d544014a155072401000740c1130f1030b00c0c5200d8540100b2031005039084031481011040c40954001d801403005041a20720359008090f1290480c0714040101c20310151580b2601c110380303103854004d00d4142036900b406034072903000b00e009444103402c50f820410301e941c10a140e40500d501d4101c580242402c01c0541254601d0401440482481400304101403241d001e0140c0039103004407001d9103803001c841c0000300300768003c12801c10324407080e1107050000a0040c1e07008038034404441065940b01d032007918880615090b03840903100140650414401000841c24584210f60b100005250903c1000c4485000c2000356000102d55002d50f5110a001e407145508440702420489000300100d603d440c107024803035100c0c0d0680c0801080c51 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 235413048 1250 235411798 235411859
    0xe0319020c130b010903060501060804050d0e030d030506190e180c0a0b0a1719140408090907091a030a0e07060806040908040f0b03071404030b070804031106010b090118 74
    0x140d2141017214041d50744040108003650310740b9406004260102c0b400c036203a00c11601a000458490120720004201c00b9004210302c0e400c8640070b4018190040105800400c10130707404419420620200c0000d168600060001c1c0c2051819403038907426101240d04994000d00003912151030707503550001140c0d028080c040d00e442400c04202c56880c0c034a00c0d51906900b420040c04408811760300b4846907152044800c000c1142d03c4810314000d40c0d012500a46002024410b803013490806000c2c1d19440003da262518903252280d80c40e110708100640342c0030302840088100602d007500b030b01c034550290f441c0c1d4004000c40c40c03801c40001d2480d07100400103030040e40c40e2080c010400c40c543d801d4402815411400b01d40585d260016290150401c441e08000182407031609014000804c00710760941341c100003a06e000d40c0c0c079608260783c10900a4000c50070407621001c0c81401103003d02c0120301800d19003041b00d50310641c0c07000042c07110101c031240361030500c070071041048018480790139811683c20b10b54441955 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 235414298 1250 235413048 235413071
    0x31507050a0305220606170a020a120201110604030206040308090624041104180b01080108030a051803010e010c021002120117070b0a02030a0305011203050702040b12010e0319020c13 80
    0x4d40c400c500080070500450303e0102d00f086241d4000e4400c0c0c5528600003207039a001c8000301035407484180e401940101d40d0385010700c0f50880d02a40a4842801030401e410180c00004a0700d251050894081d40103070010000d0100b05640300c06801d0f003001301c8a0080c111800c05000520301d208003800460742e00c801e90100314601c0c1c1c031583c211428148030707070b05903a0302d503030396040c1d4010071180c00d1025501840c90454202d04660140310490f051b24103100085042c00048081030314181c4c00584500c1c41e10401d0a5210403030740d424011046009031a41c000328440030703604000f80c41c04085215113070809005200040400f0006400d030340c116001458040e0820065100302401d0841580100b41100382c0041c9080702c180d000030081c10340101a07501000545e0340d560315241c0a07014458028005481044000c0140c5010340000e48142c0b80140091180c0070407034205402c45420400880386130b000072683caa609047e1407203052034403109001402c02c594a60300004c001842003c8403c2040396102005540b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 235415548 1250 235414298 235414321
    0xc0b070c0c12060630030c030210061e0602010203070e090c04030f1a0705070f0308040201090801051005040b09060d0f211e032d1407030b031507050a0305 68
    0x1044008242880702d220307802d00402612090090500a00c480e010b5441c004050b0044120108402408040080c100b0b903002c03129040c400301c0a4045100700103122812040b28030580004244d501c400c0e4203054114a50b402503400300398000f07020359105000300305e0503982103c0040c8440004944c18203240da51091400c0a9010319040600302072452800c0000700814030f4040c080c4004141c2000c802c0e0740c0c1e0714108442620a040004003241d51441240340007a005419044d08603105040000380c00740c540c0101404c40d031003100d034502c1c801c05802d800c01c5141031a01c40c0c000e034030406440c171810078945980401d2001c01c40c0e18000f0180c800c0080400f080c011608601d41e460300e040c40088031940b000090051605004480700e0344420042d81c10300d11a131380284100442c60052500b14031081d80089030107000521003042054605071100c801840d40403804404610440b03054400190b0071440b6420700d40707800390320054107620300c084409201c020398020b0240c99520b4201c0c98007040350347c0e680c46030a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 235416798 1250 235415548 235415573
    0x2070f2106050c07051605010c0320010f050a110705030a0509060f030f01061101140f060118030503031b0a090e070912051e01020a05160507031a160c0b070c 69
    0x1018989042c0070320039103550920007041c066024800300c80c0020702c25103602034181810720540d40411320f00b82e108000680103000d00442401e411100c94640344078102000c0c02d5a01c0040d880341c102d90341d441000f1100b95640701d5110f07e05840c003c014101750007541d03101d82e03038403c40d4100703014450003255510b455a24a800c4be029003142a803401e45a05100c590b62007400b80078003451010900c03484e022000c071001441840252100191985600d8484030b1540382d020b0809003c20381002078401100903403982540190000b0f51142c0000c5959281c1002180f40c803030924001d150480b001000a02d582c01e034070010b55410380301625800c2c5030ba0f861f98941995444d000f030f80702903080714804080005000c80803400240010303c41c803000c0002504290700728200e200e40d075000300c0441e0061207512400d128a10011001500c900c0271208400d40300d444041d59080110120680384a86c48100310302c0a40c2e05405c80103020060034403c45e00c40c11941c8076450468020100001c00000c0c00010040c81643c85011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 235418048 1250 235416798 235416803
    0x1407200411070602040317070807061d030703092c040b0a1d0a031206050a0e0603070305070e041407140409021f111504050a03050c150114090702070f21 67
    0x75607a22001d24142029411510003650501e84000a1048040707413941240d40d019031000c0400d2406005559820003400003500c541007800e060403011030411410001001201c1c0640c1b41c41076080c1c508000c0390703c95003915580d01042d038030480c04106081505115581c01c603a10a40f028401e5403a511200000c202a6208120030a140303402e142d5126004227034040c0160003965141c000030352064400041c2c480134071810360000260b4004000340c0c041c41544a402417001410760340c080e581c030b440395850502c0c80e40000d840c04200406200030000c0348500134500207204000b40148510304151200d01c0c01c2000107184c09952944000c0c0115070f5004421010100113040c480b0703160441d82001445201e0001210400c2e00c200407007081d50140c8152003030312aa612500400c0381c002a5541100c6607040400840c10500c501440f50944184004c000c50107004584491076001c28160208151010702510b5001550413014040c0191000020f0001c10b84d2450860107020545401100400c0381411101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 235419298 1250 235418048 235418081
    0x2060106110c22141603090f05060405060106090f0807170c031c1101060b1905070b091005011721090d0f020301110c2d0303070201090314072004 64
    0x2491030302043c0101c40c02c00220b1034204000d510003481c0e405216034410354015006141c0d82411420080c4a9040324040303620542d00b500c0d0700c01480d59001d142030800c0c1d07000c032490380001d001802540d0384029034400500245040c54182444e01111584640c01401070602001c0c1d400008680840c0400c000100d801e405000c1344c42c02c449850b880109001548484400542200f00c8419004014003030a0280c1d240d80f840c0c1c034981146d6049180444490803218001e210090184402091802c001580308010200c007418451446091503004c483d8140c0200c4c03400003d00320b07860b860507800100100135004680401c0c00780d00300c40c0c21400c254041c10311203942c0f01c0010502c800422012070701c0d805880d44241d000b0301134600440070a10642c002d41a18000b20307407240e00607038141180b0b00130445003603049120b00d5141c2e41c542544581158021a00107016030344902c079a00415602c2200822a0030012030134909080c41e6540d00c074010001e01c00d820540741c000c003001642c40c0c0e807203910401c410040d8026 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 235420548 1250 235419298 235419319
    0xc06201207030606051201051315090212070906020d0806040e0f0a0203010f090506070315030c0e06010801140d1b090e160605030606030c0d0b04050709080c0607020102060106110c 79
    0x48148020088401c41e000034101540014018012404c0c0c43c1115004180d505080c0c2c28101880010aa28011803501c82d486180c0c2c410040c00300950b1002614481c0030142c2e8032500c50504078141740e4098600e07010072502aa041041c954007040300b40400c1d00c50300e8135902548600c1c00060103070000c2c4841003850b0003840d032402d44418000421090251080c1c1c003d000101c0d09240200441d58a0a0301510301e400500014881c1407081e40100c41c0441c10001e104080e80e1a5281c000011710950090f40c500350000040c06225038011841c20f00400c840c1000040310030b4002c01280480304d6081004040240408040e1801c5040230a03100250902c650304020625010b03a845d40c0c1c03100d0a5100703100b29030081c18040f03019441582128840e4030041c00c150f1458440d840090aa507000c0d035586054155202c02c42ca07615611800380c28001d62155480c030031681d08000159003400401c1e00c0c0248200c504000400041c0d8020134054111200fa08044070800d6a1b60b0084d400c0c9005410000e600000240c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 235421798 1250 235420548 235420567
    0x90b120d0c031e14070510020a08070e09040503091003020c01050405030304120806090c09030c0406090f0605030a11040510080313030b01050102030c0a080c03070c03080309010b0d030c0620 83
    0x3109040740d60182d0740700b15051040d0000f042441501e035003041e001401c3c202002140600d010010082184214206d0346030140040c280c50032600909500000540c100c0188a406a4070001c0003604200480d0304c1d210b6814555100d0b40d0340e100d0900118000c9041c42d1f207004003c2d0007541941e00c01404070000b449545010f240c1187c50b50f20441e400c0362410004031107819054030654505228401c00341001030103441d170041c0d0741e40b20b13008061100d50501c14100581d840ea2224000c1000a0111000c00701c0c540c561000c1c2841500e03013030342140e4043d03440a005c401c081503602d18200a80b9506980001d5545c40d0241c0600200004da0400d4000784000140710260001040c00c000071a03020341d440801c0360742c0f2903004a031244030f950001c43d1503902c50b1040e43c010410140041032215610340889152080325900c0c00c0c0c0e130380d031203a01c20f030b400d0000841080f402e0b01c82030184120400c01200c4080e8041141e44c0d000c1c2072000000005445156184200d103030050881001c040d4004413003c042e5240d03404207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 235423048 1250 235421798 235421807
    0x21c08040b0c0f0a1208190c020c010f23090415030b04021903030206061e12010204081006030206040e090109060f05070e01020c061e091012060e01050901090b120d 72
    0x600d80a1481c0c402e03000348403448000800e5255650b58001017413030300c10b240d1060840e04200090029190b007004810520062803241c800c0c00c43c4520160007904201442d10005066840c01d21052000e00440d540d400002d400820041502034800b034a88944402e07a000100380148040030710254200c404600c080148656548400e109038422a902036480c950780000d02c080100c80c1c8001005a88000041440c518240358480744914200103003030500011480010300c0e0600410296405950016040c04042000c3c002214040c03518001803148510b154041415481503109007241d800c0360b0804122491007e421154070707540c204605002181c1c1040812004040a81d014000705401c0010300b25994000300700b8004030180184182c1c14080750000110700c07844420618072203000200980d2081c1d035201c14044074640141da896090280c00c80000c0c004032009030b04401d80d9940800010006a9100b6030418107444040fa03021440ba00d03004d002c130307030b10f01041241d4845a000b000300754075115078003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 235424298 1250 235423048 235423057
    0x5010b040e0c070308060f1912170a051b010f0501030602031504090b0604020a0306031502130f05030d0e0316030602090102210405010813050109111318021c08040b 72
    0x5589441d09989941c504280d091158030030040116180000103103e505d0050401ea900280151280d18400d00d00e115070360040103543c120006540e1001006d80611003465030803c15002051310203881c0400303600018285016070b10b41c0b070503840c030f0011542001e41d10a402645903540030380014006035849241000103034000301c941035075901c0441044801880d141c014059503070780048444190b9120741c82440301950002420b0814151903c50010000343d01d241101c6003051146001602c40300320503498549000304c0d038011819480e05140508c0380f40e40c0030880314002a024149400c4080044010034101541450482c0d04041c1d0903c0000901007140c00800c040c55090703090fa10201c48016007407559401f1590103000d20001448140141d5004045140c4c21184d003031056141d6900a0b82c1d41130959041d00401c48500c0040d000c3e030074050500e201c9102d90400130000074480c00550100d1209001045840603108104414807803104084102080062035007024105507150f440e002d81c003d00360b02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 235425548 1250 235424298 235424309
    0x3090a0803071e030c09090f06170a0b01080d0909020307030e0a11190f050607020f030a06060f1202010f0f0e042906090907051c14150102010509100510050405010b04 73
    0x1254919075001c5100e841a5070300078115480f18051b440c102018840180ba000303149041d03c41d956140410b40903d0150f104004411403002030811158501d801d007414841a88021456403141e051401d8154200c00420152003140100603229a0344440890241c0304c0240d00c42c003140100602401484100031072440c4c0041c0a4aa071542000c0044c201c1c10426068170841100e1540b1001c02c0c026860304000521950340024047c9903c45c40d2400064200303030300c0506c00c4a03002c1d5140410800803c40344d41c844010541c184083d00441c485070006883c10351441e82010030410b014410b8034045020f0401c2224100d40508100007041640e03641141400003818220881440703807503054a10315022044075100e81c00074040500a88500d00299015000904000c658070301281a842c8c0c8405140b15046912032024801212400c00b1101c80301081d41c0608018116410001000942c40300041d510304007108043c0d0008080d580c0f0000d402e03811585410455001d41004000148402d181c8081c0c800d452 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 235426798 1250 235425548 235425587
    0x10050f042001020a0602300405010f0606201501120b0903090d02190e0a09060f090206090f0604030212161202030703020409060f0c03051b0c06010b03090a080307 71
    0x260440e40222120041d02080d40143d20415a000004845402a2104614240301310000d520004065a9158160903003030184107090b200704000d2060034051080740c00c6007058100072403070403e41c0051031000a10840b0780032081a402c0304004060401244040000204e801c80c501e5843e080740c0c0300380d01d121032002c1e152029451301040040790080121081640003e000041e407038401c0e424000c000311110043c00008072078800002d626044041d00f81d102c3e80c461031001440081c03070718002c01180e01008190140f00c1c940040200103894031310860751650000c0700e544555440b005c00003038442c07240b500001d4001168800784402c4d04400284050500041505c4980d86a00c1d140001090300784198080d6165020700e02c1080135081c19407011284601410740803841c106c0b611420000e075a49403205070002580c850030071101d40a028055100d001204040c2458a5010b072600c0d40c0d18001801388005030100000405c0c16a10100400c0024541c8404140c2e02d915000c080030303000d42401d480720b0340600e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 235428048 1250 235426798 235426823
    0x1511030c012a0311040501080702070e04050d031b0801030206030a0209041b091a030109020f16050705010207140d140a050a1a06040c05160c08070b04170601030b160210050f04 77
    0x4034064002c0d0410704a80d44c0d00c2608080ca1700340115141c01010306420154000c400011811405086106100b00c1c042c400a018124103e03000908031042404154000120651500034440d48030361424116501100d9480d04c9459500c0b4200091148046e01c0d50700c2071174030342e1070048140d250001541d0020a038407070030415075a940c0203140d0107012407810411004100f0041c400d00c6443c0c2e010308100541500c4040c01d01074420210540701494000a980030b60110f00c00700910742e41041082c000c0d0100300300d50b0b00c0d0444804086101c0c20b209040061501801a42000100504200000a0a4214080b00c494401ca81002c0040c0440001c003204400300d84400500c0500b814010041d50340807655509240442c1c40b411100305803550281101c08061401c800aa841c0341004900b0142c03580c1e0030360540d1140707044c299082c4180040d071039801c650403800041010480000265a100441040d4094502c0c06a4012410071481e070689804061911042c0702c0f41115a844280c45244686400b0200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 235429298 1250 235428048 235428131
    0x9140105090105130b1f08011e0204060f05070f08160b0105040b0120071a04140a0302030705240708120f091f021b030915041511030c01 60
    0x81c0c0f20102c4241002074a541c59840c0094070802160740d029107103201341212103c004100181040481c0c2c05004d6982d10358106225440c0710619181300071400308402c51800346440030207051039049219071028400003065000900810345072215050b64000040c995980c4e20045044903420498004d4407091072400c00850542443d12807110388075016118003101d061150103c00344190300c03d2a503100e602800c04000742e819100003080550709040005140c4035420880601440407c009006121318111801000541c60200d030301c1e02a10401d0702c01c0c2100c51400741d014801a00f9540d440c917030007600040e600040c888600c1c0070b401c40d01404131a400d86034842c0302e24001030328800e848462980d0030082441e51000902649540307002015071026040100b40040f00d00350018038102c00401b41c000042009040c0740c4845080949064280c840b402c0ca400c085c024845059500d412005110710074040d034004030420070940e90b101c1039070700090150982c440307034900c005000e403043d0004100005440226 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 235430548 1250 235429298 235429301
    0x90f060f080a053105100506030c0603100311012c272701230f0c090910050301090c0f050307080a0609030c05060c0703021506010804030c0510091401050901 69
    0x32040b0001c0304c40350500b00b43c8080a22075800004a919541c400c2003000014028484511101d6000c4400261450114245030814100c3d01409205a008008001000d1600d000c040f003901d400c1a00ed401d040d0030030b0300584064070740d9001c1150705140e502d541101c800d440052071544003000d89052602d100801c0d03046440361880d0301c03034a0390411038171b00060829002034032408100c1002c05040310075025904000f403c40310150041e000590840c10f8a00100e04511480e80d01709580c200c1c0b10000e8039106503a036003140505c0124a108c0d4a0784d901184407036102246001c0608401802001070301254a040e040d01d2065204a00d00320b420202d0000fa1032030003240403011200070202400c0b00c0324440d5613841c02000c1113a011424003003008001000b050082010900c6a146262215a240c800f424044c4c40d006803a00000c445e9054442000341d0350b41d0080c50240c000b580341c28000814102480d009050081416901800500e0558203906010840c440c0c502ca20910a00030440e684481010a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 235431654 1106 235430548 235430551
    0x6040e01051c0b010314070312020d030e0319120f050403022b200a12030c0e090c030103081602040507080906100305120a090f060f080a05 61
    0x114608284464082454440e400310b107031541039568200842d01d05000c01000e1546501031464040c3c4200300c02000f071030f03010485a281c0201c9260096441000d00300e200000b904141081030343c0c89021045407280d02c940e40c0c0b40b0841e01c60306002a070708810024114841580c0d5040e40d4000c0200ca132080c035008521990103001100070480d80501703201f1000307215a0711903000141c240d40890b0081c2c0004440300080d5114003448c9241d4010a00342003100d803018007040c44081408003020f074135a1004024a615854000e1012a0311013440721410080350140401c280820052010900200107480220100126482c00d66074940c00b0034155901991010042030386002401003000091095981c0f04410800b1052001d20b5510b03400e59500c002d86040584840000b080347d800d034414820b85001c1c0c000002c10f812000e41d00d11006181848c002a0710000841e480042070380010300d4044c05 = true := by decide +kernel

theorem cover : BRFrame.Cov 235251798 235431654 := by
  have h0 := BRFrame.cov_init 235251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 235251798 ≤ n) (h2 : n < 235431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
