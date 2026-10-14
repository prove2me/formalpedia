-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0465
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:57:13.154097+00:00
-- url     : https://prove2.me/submissions/8b76ed87-2cc0-43d5-b9cc-b42dabf10705

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 83453238 ≤ n < 83633094 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 83454488 1250 83453238 83453267
    0xb15030612012003061003060f030303020c031308150108010b150318030c06010603050708070c060506031c0c020103050a20030414010207030c03020f07080c040b0f03010207030801171b060307 84
    0x1510040560100035425404c202c501c50302840d441d0b10505420b84c804e100b01c1e401c0c3e070b02010315080d0300c50854508400940086101c0d07445803000304180355196000c00d000c0001000075800800441140f66000120b9110607400381c85180c4c100008501e99540d17024403140810740c40c43c0d20a0300c0b591600c2090314081041d4100c1580d5020000300d50300c2074200032405d10705980c000d0300c0501803600d40c8001118059001c4034203038009520030344a1030018100e0741100b42c000c3c8000701265454040e65007050001250720341c640000c110240504021941c250003034a90052600d8401c00410815174003482100701865040c261100002001038208500d1040c90a10516440021500e0301d035503141c06401e107403400800740c0140c0315404082c5c03105440010402c0680351440c016020022918091001910b544d039480d690100100c006907030300751005d10161061501036a2191495450100440b45100300031000b0b13a69074028942c6c440066070900e0409480b01c80c04da880c0c0e942c039552201c04030340403139091b03915 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 83455738 1250 83454488 83454521
    0x706051303120e100206160c05150c0310060504121106121003110f0a0e0903040806040c140d050307031206090f050412050a02060417070506100305010b1503061201 72
    0x2e0521164424450b00a020342034540801d98940640c0581e07803070b03804036001c0903007401c014044107129100c0c0100d40051403096040381d5941410740c0200c80400000c072803e81c4540340100400c0b10300200101441c0c02400c0381d050062425007001c40c1d400000b00704000150000000140e07442c415203403030b0125505103041e40042c4003542010765400b04410014441130354a00c0000c2040c44240c603180a020b903c6e00341c024500c0560300c0c9002c0795207072081d4004080882600081c8070004010718107200b650b04c203600c40d0101d15040f900304811201070001d100318190161030300e44030060010b0b0740081243d000c0c40d050709002d9402041c55607007101400c00742d00142c8081d4200441c0b400044130b00c2c1c0100340103503c11940c0c02c6280e4008041100c240c041e2000c0403006030321100c0480c02041010f030785100300701c511500701403a042d05500d0342d40c40c0c18010303242603c1c040106902041409000e101e00c013481030003202c581d04443c000e032442c2074850101400040c0300d000805990402e0207805d51128980a408000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 83456988 1250 83455738 83455763
    0x70e0a0f03020310060b0d0e0f010e06040b01080312010603050c0d0f090510050c0409020f13032003120901030507020a0c060315120305120405241e0105030706051303 73
    0x1400303160008511040f4024072800c00e1031142c0203024041c00050703681e1000d2442c03d10400004103030142c0031a103243d034260b0180f1030400c44180d03401e0003240d4403040403000031300c420309007440e1a8034001ca050741b040e0080c0e0000e002000000090041040c1154214640455292100310245000e4030426942199644c81c1200c40c808000d42501700c5107806020744269008200e1003503002d000e07509d0444a020109404020900c58844181c0c0544039500070070100c02d0812454480148100915400a480c082e0040f013401c2c00d400709802441907100d1017600904041c035448a016035060044d035442a041c503482e8000540018400c00c8904103241d0400440c2514541e280f00280c014485400e60841c04820703030802054001114483c2c240c0c0703a81c90380d1110b2a2455001a00f850b00740c018004072802c2c022a50740d005100c10b03c0d4a20091602c848600000c00c4c1040301d05603058204250216540c0d10003400100210740d8045220000c94901307040260b5649010001d1284003440c1d50401003850303000a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 83458238 1250 83456988 83456999
    0x40311011116060b030606061606090204140907140a0e040206131404060501020309130203100b0406082d0402270a020a0201060b0c030403031d030d03090c15080402040203070e0a 78
    0x4892031000380607103c00c01c8424034000c10f042d121a422500690009020418a03000300600138a2821060040c48002150b03d450f80c000390070713246112800c14a003040501031110292040c070202c4003d007031401445a00750101d80100e003882c0c00ca4840c41c040c030300c0e50300001025034480ca0110b80c583e60580444c48140e6072119000800c071507011070301c0e0380a20300d081da020450707500000480d50071003c018aa076149a0907112480042d600083c0100c187e1035a01000080441840c000352014080584030035a10780f8003034110055105d96650740030702078507500007a81120a07400410540281e01920903d000c007103107000b6030026a01b03508050284a041c901000701000e401e80c0a000c590609500921041d41d603090030505038042c02e41d841031103800400080000a02840901640c00700014401241e0709800000a041152400380f04000c81d803a4045070040140280004000c1d003001c444015041c100748200500300ca41c0100300a00031a40080030811660158210500c031030b00c0141018a5541c894 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 83459488 1250 83458238 83458267
    0x5040509092b0c080306040605130f0c052a010b030307050109110409051c030f050f1b040b0412060608070303091802041a1305040213051906080403110111 68
    0x1d034140b100d041c101002806844480011990125402c1d6200c0401c212152203000746540044c007516482541d4150000d91525116000d0980417150b880010742580449208403d6840c4000410104a000c2124150703204011f001c210703211103584403207120703004c00359119030040400c8039100754944400b06800c410854150403207901244240c8122110340320030810702060b40c0d200440108282c02c001a0800e400d0141e540c4e0800c21000c2e441c01103080880544210110350041e50f80c81111a10b4074108841c2c0d01d01705202c02e0a11002414a030f15143c5040f24a6800d030286000c0d06842c1c407000120f001c184100c0d40c0054015101a9060700d540355a01c1ca0080c1004081b03101d003040c1080c5d030394049101882a80300352001c0744c0c106004026035101340b800c41c280c107900c030544000c10140b46034030100d0140c403148041c0c048005c0a040e10751140342002d0801c040fa9103028a02012905042c80a0060590005510b0b030495898200308a003042c1104209002d0013140300c000110003001300304048090b820 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 83460738 1250 83459488 83459503
    0xd02031e01180e06070f0c030203070204110306010e0a0b0a210e030408060a0c020c01080612060106200102070f0f051c020606040e160e07030e010f060303091512020a0504050909 78
    0x80c00800c078000101c0c455a03201c0c802100d03504085540c410813182c6c054040c000441c200740c0301e441501d2502c00c0c01d0380040c0854551607060500003c02104016a0b0b58000040000e00641140c0d09a242e61400319402d601d442140c039001c08200f40705200882c00341c1031350100f08062000410600205e00340340138181d41d0b900300b441000214441e910100341404084c0c0f0490081c0c810765405403616540500040d40e8140c0e02500250300a261640c29060000b010310070140030301113030b6a07068a80407a019011140c05016082440d07141d204010480001e6500c1003111125030340444a051554940d0410301d040c031030400a102c0c01e001e10900702c044126404030340e03980309010403a410032510398015215a540c241c64050b506079108400c60030700c07410000c1d84810394040800d140c003103808407020150509517441c5c61801c900c1c2c00c1d100d4105004168200c035044000c0c1180c00108104201c540100400205084200c081060383c00a08142e01c288200202d601511016251040a04002c180345968019 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 83461988 1250 83460738 83460779
    0xf03010e010c1404030c090207020d080d0c02120c0303011703040515040e0c070b070c08160f020901060e090103060c03060509070816030c140903150103080d0606030c050d02031e01 79
    0x95003e292403c507400d041901c090b00c1c6c028a0810016062030b04120095001c040b0036170780701c10900080000281c0941c020400e1541803107002c40d10a41c207003006403503c016035004152240c3d09100f44141c2100001c140e070b04541c84002d00007502401a0769890852003a0380001390455076441030b40d00c1c04a140703801441101c800d00b0208403141d49064200c2d14034040c141006149416240114aa1078440e070210310f00107000c0c0080a1510030391042052159200d27903402c40784843c0c0003800b1030540c60840092401071001c0d050103403540001c540001c1c0c001c82c0c140401484c4039681c0510514591003030f4001c40c050300300604070108030b09103d103001e04940380880f43c0c400d0034981266030215282c8603006e0701010041d0343d1190b04188959010320019030b00440740c400d41501c2240c00c10451040301940c002d00860141114555604403500300310151f624030781004c0e003418103000c1038000b0039500a04a44c0d041c420fa0b0001612078507408401501ca403010054907260158a10010811003101c0100d02c80540c2c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 83463238 1250 83461988 83461997
    0xd0c0e24011205071403010906091b020a0f0c031b090c020c060319090803010e06030d0806011209030e0411091e09060402030711061509090c03060a0b0f03010e010c 72
    0x42501280940d281000c60300340c00948414401070010840b90401c40c0c111200d030511091544292241d031070103820980c0400031032a02c0362400c04c03100b00340b403150345400e820703400002004050380a130180da0f81603515401070000c4400e0b040d00003131200b603800180c091944404a00c4203502005206143c281480c052044d0031031401800001c280d00004004005d1007010300311034115a9103a5522680c00861304a00a9103521580008001003074840298040c05029078032150034202403003854503000c0c524105600780301c180d60031b004050fa00030441c00c0d42081c003604040b4a8241520701101c002108081407030b0028100030303540417100e284001900c502081918001d040c060030303c0c8244000c446030030403250090070401c0410003a061640085902651504041514415100c000d6141c148100c412410844000082c4070440c030708480740d603401c0606000100201c03048940000d031200e20152201d038042e0b5a40b81c0e0300c0c0558880b00206555140024002c0210012102405019080ca181aa00081c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 83464488 1250 83463238 83463271
    0x2070c15020a1203020309010e062d0103241b020d08100b0306120c0a0902030613020304120c03020f0d05041403060c071704030206040b090406090c05180d0c0e 70
    0x688006424100160060440180c0b1a500b101c00c4d4020750020301402c000b0354903103048007000842007160902840b40040400b07001429a401245d8030707403002c482582000001c60041002c141000c9206031140800b8807108030b601c0310012680010b0032017000210b11024880c0300c90321070710b401050a0003078030120340702e41000d82e03200c048101071480d89025049448400744003050881c28429001301c5500c13140c030b0071200c03040ea101000586408850344089590b41c0c00004210444c2040600c00100c540c1b01c95055003141019502c2034074a81c402804c120801052106072000e0510800a0006100940040d10742040f100d02e0020300681c0640a404180616a5801c03800b500700040e442e072040c07200b07522040c100780c3d00755a109641840d88071800080c21050102001694401c4000d100800403800b00d0780d559101002804151070f842d600c0085601c0c6090642801140c0040442c0c88210480c40000d20749604034002407545807803120050040c6180030710201e420510703402460b01500301e0b00c0044102e03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 83465738 1250 83464488 83464529
    0xc0a030b270c0a20030409050907031103190f050106090c022b0203070312020c010f02070317040c120804090509010227031002090d021002010c09050d021c0201050c0102070c 76
    0x144100160000040d18050700c4e240c0010400c510801c040394000b040d40e01c0c150f5a49416002d41c1c00030740709107401d508403400c10010070903002c60244c9519001d0340a040d10054040c40c09002600003800030300581180303100c440400800b0f502c0100500084034040000d42c0811030001d40e2201d42c4407030054030000fa0060b400d000b4003031001300944240e0030350003949002d0340d07964100c460490300304050325040e409100f0040120f00c20b000b1031a21060912005841d03013010b060060681c142c8608003044840c80c1000e000105208a003460295122403a426988044a240524180c8078a80c81004031603e82001d00c0034506040d0002c007440103561600b1441c2d10881c401d49001401600c03030480d4554801001c4040d4554141c018000030100103020407054000e60b0003091145081030011070050359034241250559411006035405000140e0b20000640001c1c0d0200c0c1c440c000ca43e445001010041c000041168440d000f2598072600f100300954440100e854682030106203402142201100c440ea001d08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 83466988 1250 83465738 83465761
    0x60f150302060702040b0604090501030812180604030f0507170702030c0105030705030f040f150f110901020a0b06240705060a0203070c0605150a080705031006030203060c0a030b27 79
    0xe4030340050a06140400a03800c000040690707030b40c1540c00000603c00050002c110340304a600131030203810314543c1e42d4807140000540b080018600319240302c00d00c134000035030880041d01d1035100b03030305040c0302e005004141e4042e181c50080520003804406107807a00c48101c01004040c09c0c441c0e1080d03084800070000301d00191902c0c001124034400090341030000684c00211602c1580d042030046440158045840c2c176000031544d4024101054070b0f032070b844111841900ca04c5941c856840001d030075030400c200301000035111501081d003e4510281c00000c1103055a40000c0b500d0303c0503e01c51001c50010009010100355080800c0548140c0a54000113140035028000c49105100039540c4120180059031540010000034003000959030b400080c148032501c803655540041d0985000500e80b80385850109031500940c01d0072001868100013003000107032000104541c1085080c54801d07214003924900b10018045981700c180c2c004620340301e506500000745100d81070505500b8540505a0380c6040901 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 83468238 1250 83466988 83467031
    0x150a1e030e060a09020f040204031a0a150b0706020f03040309032d0f031e030b09010f120b0718060807020d09030c06110a050f01050108150118020906090409060f 71
    0x5050350040400203426002a91290004d10b01c0248500c0d811404640030400720782060f002100c510450304c1c0d108440c42181c4503290f0740032098880c1401044032600d0b40c0c021030b1290384640500c05001017200410410740b901902c01c01107850000d203440b0f14041c140100f640c0342900c410f80b0340e10000301007048940380071220504000200a00110900799560b11042403040800c000e50811545000320703909209250811499406150360100c2c40c00270305400c02c50403c0c0181d00c00d01608100103000c01c41100480d0300c444446804c0904212103980c0d100050320114030702174514030840c02281c00400c1481c0c00218440c00f84486070b0880303001114a41007130b5040b025502014004d100d902c802002514428030480400f01e00080c19240d60381c646071b03070f19840e06070310000840042c0d450320018810b1700c40400105000784004949580740e5490441c00032290028040c0082a05800050540c000c0e10340000320b4a5140014100700300060742810800001c1550284009049041c000d5038200d0504640b8100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 83469488 1250 83468238 83468261
    0x20315070915050906070302010e0d090515031915080a061514030703061509060b04030303111305010e06070203060a0e1b0f04021b0a06090201020606041404030806150a1e03 76
    0x1c1340313844061030400c8225000200103e045648900092a555000b80140030307615029403662041d450520040009420100c1d000708000c60040c020007483c8904a0400703501c0c244c2c29040000e4a1881a9210110340c0840d04041c0d440c0c450303c00260200b1001c0c1c1e1217803134004c02d00f01001c40840c1d00d40101030002480000a10b52690004a00344081480d6600c4180e0f0400c003041c5613410180c0c1c0b58000d006840482d032003140c400e030010504201749074150190300d1040549204003894003850502026000c82c907401918100b214412000407640c4910048852040d0000c2c1100c01500c1c01c0c09014000d41031000c0040854000c6580a604000345000c0d40503070040010100480e021b100d0080c08020b403c80c1014820039164150402099403060000b00e8825000b0340003c213440403980000b9140c0000500494000c52400c0300d002d03181d0700162541c0350810781c0743c5801001622a10002070a00c807100075030300d92040300000d0361540c0e01d811080841ca100745460760750070f405a41041c21707022034000d511074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 83470738 1250 83469488 83469497
    0x1a240105030a0f020904060305030c0c0f0a031101030609090609050d0f050a081306020a020601080c0105040e0609060310060807060834030f0504080306011b02010912020607020315070915 82
    0xc1a11001250807455206000103c01410242020006019104168400e48254100040035144046c00744203c2200a80c1966501d4070301c134140b008559000744c2c501c001340c07009800030b1011304107a101e07070441401460412820300c507543c15401c0c82801856685400c0321940308958400070325500420340c0e649a010640c40b02420849030305410346940c80014044001c02142d1418a40004d103680301600c01c4294640c0104a19814003444501e8505480350003411f000050004104e41c1c0702440d82c0a6201000b95070304140c2e07031071302c0021078079100c1c500081664035418050702003040480011804116520355403101302944034285a210070424510040200201482c40c4040601d500011308110181500d00020f60022081e098000c665042e1012640544000140070351981d2240d11010a0b401d040840707051098a0790000c0c000c0c0c001ca100e041844401980800103554a903400c4c1c440441d000fa0590b0381485a00a1051810708115052804244070400c0441c516000c10100e03000c4100c0c9454 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 83471988 1250 83470738 83470741
    0x6040b0303190e0604030308010f06020604050325150b0f04090f020111030d0c0f0906050c0c1012050c070203190321060305010c0c050c03150a09020604031a24010503 73
    0x1011012000920b00e18052103480e01d0180ca4589600c3c000304019406030b81c07000142e50401d008c00040d120254444800c40d4414018000414400f20803180100c044011030711b416062698001001c1c0c403240c201608143c0514801040d1301c1598002482240040360070070503c03014001000b007141c441d45c2d4050140c02030b21103014019405140c0c004140040d0008880c101502448098181e0f21aa2071103800118039644011803e5044442a00942010300749075081c000080b54055880d24070007401751141d00d40300c00f801c90650050b50301ea64100140714091000745084645200142c1c047c007001c074000d01c149240e030428020200041211960305649034030180c0c2e0070310000f6503486094400d51220750f46e12680000000c809225a2012400745d80703560031400f243d410003605280300382c0c400e24040d400069440750003c6850103640ea001d00400c100003103a40355030012901a0046800080c980b000c0080341240d00c104420880d440303006d1f0f0f1000540c0d02c201c020b0144401c880e44d2141103020406c01d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 83473238 1250 83471988 83472007
    0x50d080d0f060b1305014104050301020f0306030c010512130302011401090902010915051c0b18100b07020d0b0405010b032409010204050306040212010902030109060f0506040b0303 79
    0x20444150310079846404100c0b9600c41441c0f003034070f900c01300344846000c0d4010f204200700d5800c0040c1400411442142c00301c0c221010b02c07206504601d00402c1c440300d0320700801c454503001c5400d044d0750203000090b00071516407650145030045540300343c0d501c51117485041000b2160358411000c40e60a60700388900590b1070740311f1400c202089405444110300303654071840c0405010300110b0303445009298412000c940c0b4109030001408125080e080000c2c400f200d00304815601e41c00004440000c1c1060060441d41000e00c0b0001d0020411000900d0344000c0b52082c45040240c070344502c41c02006001c000e01c4031942d4585040e407062241c0c9000942044001d402c4c807004c101c52020303441c0e100c2d01480022504081c00d13030000703007007402c0038041d0f808841d02d6840541100320240c0c0c0c642d03400050040210b14090400002030750fa0704000300003e2040e50700c180d504059000a402411344c0c2607020b8002d01c40303003c849c0f40c8403026000700c60100c98200e25100c0029424900b501902000b4203010f0040c520f00b60805 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 83474488 1250 83473238 83473241
    0x1c1b0927030f170c0405041802100c020d1209170705130203061c2d0f08070804090c0903061107020109060305060609060f0c1c0912031106040615050d080d 68
    0xc0303402d102030140e2090300d480c0c1c0541c041800d40c45940803080c025652420300341044101c03a030120b0185010940c0350030960050319040702e50310304002d09080a01c4004010720002d4118180030f04010301000084000c0701480307822800074000d4680509201010180e188545540c2d26600c0c800c072070380b080c81d0007001d09107510300c0c1e801180c00c40c9002e45518050441c0d0592610400841c240c11507115403410003115115024000c81400705042036010103101c8502d4950f141410140003010f882000f001958804103d04001240c0003050303400303410701c4102003081c0040c106d41114403080e500203003000303c070f41c60104000046a0509905845000840f4180f1504500600d0020800c42d04140100020030540d0340d0000038001041d00d45014540d0340141050090418101c110580d03079111104100703c000325008034011054442450300045003955a040c22500004501000c80d4140a10801e000612100d84c01040ca0880c00d450341a816554940902810a00401002e840d0550a200141c01c1c60041d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 83475738 1250 83474488 83474507
    0x70f06050a0f0c0f030c1b06020c010209120c0906120d0c020a0807030b0105192301030221090609030c0706050d020c01020f0c01110301030305091c1b092703 69
    0x54030000340342c110403a615030860300c210090401040902c8116205542e05004048aa82c6240b0381212602e004140c59001415051001032800303402184000d80702c0025415107200400050039442c072a41d080300155215801d016915001d00504030029440381000c114080c106641040201407400b0b40a00880e9511062001264401505031000032006030400a00d405140200e030620f9881d40740004101c0030f5125201e400030394250465081180208152100e60380c18586030048104002d01001200244a1400c130038901a4030122404080d480141e1140c0c46488000c040b55030b1038841114469aa0040120b82c42143d4002903040c80480d2190f0090010203043d4500903081038900404035003a600300c16080c1910001c041440306414509029402807032800c0400c503865941562401001489012043c034001c40420004003540c1c0b159882c1928919004140d031401140540009802c0715410f210748845e0030b0600518543d00d0b0925038a00590032150f142c501056101d03a40c0c00d5076803060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 83476988 1250 83475738 83475751
    0x8040e040c050307080c01020c0301060503031c02130603051602070509070f050c010c0203130b030405060a020c0a060603201c29010602070e0c0304020901053601030611070f0605 78
    0x8603400002c403030b203040080f0000303000540b01030300f0b10002c0d82c800289080844120b2905c03d13810403204011075200842107540c500d0485522002c40c4c1c8d16418607101a11501207039141d0300080010000ba4503515a00041c0500d85c0421500d10300d80c8090b000700c1e620f1100f03000d003d0340201c40801150f06a801a0400c0c65180b0840c11714070708001e08543c80501f11a0400704100c0541c0000503550b042c40301400c3c88c1c1c40500409001541503050540b9107968690f0001c1c0906005070380000d041c0350b00341c401c002100c81c07203a00ca1000d00c411501d9142020122010718024003807408100c002402c549000c04801d520034036514a0006a17003801d884240c000f84203907021040c843c40740102a40e03500b40840310349019191640003404200d141c445040203440c402082402281402c1c01842f005a0718001c0c8035044840440c0d94055200c6540d0003203400e035996590f014140640d44240b001c0c070031601d0200314100c0340120300405c03202144800943d01880740038030091240d03401c2e80ca103400044066129941144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 83478238 1250 83476988 83477003
    0x131101030506131a0f09010303090509060a03050109031d0609011d06120c19110303070e1f0e0307050301060803191803030518060a020709090206120c04080106090908040e04 76
    0x1012600845807000b80040030008407401d01d42c11810301c105c610181907000d5a80001030762454400a024041074040c80c3e03c609040c501203010b603511a0000780c040c641000080041c2c0511b458040c1200091101c40702c0c52045981e00e0720383d00e1418a0550b480c2d00300603150a4221b406e0b5801c40d42910342980c0d8582c0d402a0700f44a0488500428442da034414801004107036919034480781c40424030a40820503104000c82061000408400801a00c0e00038201c0d092603c0b10144040000317543c13820f8610203e4150000300b4594407030581c0603040c000200425801d4907502600c58041c182642c220740911480e03079000b005081824002d44031024139405051600d41c141c03d0600c0030011500c4215031041d40058400b1030400c1d00075240703151041c0041030403a461490312180c944041c1d21410f041c4540090341d5691450f40056407510301c11198045100e10311040d05242122500016400034011801d81d58a0711a0104101005108101c42540c116180300d081c58a05121a41c00c0e0030b00400c21603010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 83479488 1250 83478238 83478259
    0xd09050f011803170301030510150302060a020a05010e1b03011b0513050d03080411040b0307060c030311030a0603030212040302010507060b040e010f0606030c05040f0e0612030c0312131101030506 86
    0x603865031201d52042c000c04c004503940b5455400c1c55881c00040c010008801880d2248030301c501004440c6900c110303913040c0d400340e0300c85940c40e000f60f04000400c00d0203403055082c07106d03680030340c41c01040704070b460b60341000c100c408280000e0138035089179400f90b000e4503240102c5003050002400b8201a00c2105640300d4200300341500e58001c945442c586e510201c01040618051100704103440b07210712440350058404002e00c1604000099070703142075108107410300c40c080041c0002d05104e0307040148040c1c81005a141c9d28140305500b01c000340214401076005026403170040080700e10345002c40701200c0d0160760705030804403039441d608001c00803400b650340d0140d95040200d00c21780342030054401005e19800002842440e021014003601d00500c400c0d402c0000030803003030042e11a140300603419561505903003600e030350f01c42e07011800d590048190208644400305c2d48250791000000184070300b0008214142d001e80315100740c0c0401200c4079100401e201d80003110110b00d035209920240d4044030051210950 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 83480738 1250 83479488 83479493
    0x50f0a110f0106090b271519080604030f090b0f091f0306080f030702011b0f02030a0503070c0b0702010f0f090519090b01170106110705060406020d020d09050f011803 73
    0x84a0b5507070b200000241e1500c40b5015030f0301c1c20205003001b00c2d00040b0315464580c9644030000361254002c014100c92040395004031459121503080007054035007c10640070140d114800c4940d904c0b401c441c1200016001c80d092111103200704402d44c1200e8003854060304240030550b5039446ca8001c402030f16002080100405804003050030004494106620000740c40f504003080941844401c440b0900c00e640700b00b14001c010f0340d0081d1844900c0300503502c450b04554a070f20703001900d90140c22010f503052041051100031300c080807009105075031080c072050b8441640d43e0008007050040002c0a404900840d080f2140780d40a481070028000245c0f82c41c2491640350000161000784c02c00130340c1406444c21714240152250781c0704035090404242030a4494034900c04010500792014080c400401c08068001c2014150401221010346401403000303441d1034907020000d42d03410040c1403443c0180b18128240000c1e50107049904d05842000e0500c0110310328030401960b1400865403060100390108400001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 83481988 1250 83480738 83480741
    0x271202100f050a06050a140d02060c0307080a111504060519060906060201050901021206060c1f0506030618060a021b030703020102121509040f05010905060a050105030d050f0a110f01 80
    0x141101c00006480e0501e26071800843d10160800b501550014009225540c40c80d00900b2090004660200e002d08151004c035109001e200d02001080c03102103490320401079401e018100e2000c5030395949031030040383d410f12a40c500c070402c104080c8040a401250105050380c1049074401011004020300100b020300e080225409a401605070039919501440695828065960007000ca20025410f01154121060564602400310341c0b048200081c4181c0043c2c050090755007068070820f45e581c4480d2080c0c140d0011300b00c12903241e8464090080000c9402c80e2501074491404540c40c0201150346e12048444001c1d8808019120b61312503814102c19410706c00c00042801d40d119a00142c0c0318039001034500040140507201000900704412200300300e468001186034041c3d007044810490203143c0c10100d0041c100590050b003240200420855507400580001d03040701e0080d0102d43c0e40c1134910340201d4070b500510004c1031280c502040947c0c05584217003070080700140c401042d80c190031b803000d42860 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 83483238 1250 83481988 83482001
    0x3051602010e03071e0609150e13090309050909010207050616091715090303130b07050405060310080d020f07260318210c0112020f0a0801080127120210 67
    0x9001407200c0e00d09503518200c05418100808040c00c00a45040c00e0400c10023142c0c0c00c028400c002c0008101000000b40d44180c0e5103d842d02e18030b0400c1190340f400f4100100568001c0c0110b601072042040491441c200500c2121041500403002d0a182d440f000d001c950300c4200301d10074404004040b0b402043c4000d0301600d408030014408010700c03001c1100c50940340c600174010100a4140c0081c010030070b4505c40004245070090f884031041c00b50b95588081079800f07000d0790f0091904a200031041183c0700c0c0384418034100f40c5140c0b1049801c40d40c0e0180040369101d0141c50104c403150032180c0200460b00c904404007030103d00f00508501c1c100c00c51101180396802c10002050285660006040c2504040340250011140810342a840603d1100341d59940c00101e605607040190003c203094a00142d54191071200c00519100c40ea51519180c0003811104280036a1045510301a402d00801c001504207002280080c1103100081040c0c2d1504103844c20070132a10700030340c0030784400c600a4422520419 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 83484488 1250 83483238 83483249
    0x4020310060603090b010509040c061101060b07052113180b1c0c05060a08010b0a0306031209030203070e040c0e0a02070602042303070303050315060706050103050307021503010303051602010e0307 86
    0x9503001343d0303041001040d401070344560700407000c450500020800e1600d011301036842c02e092001948001c5100b080c010a103d0348000c2d224800850030204001020505d603442200d482e90414038042038a0048a0511501e840c8214544001000300241d0524a4800c0e0449030545000650704500b14049020940f0520350010b07500440d4020004005850710307150003402042e00c91508113264100c1c0600020018003a28891040105000c0c031458840e03040040a9030303000f0b81480d1054010b0b01d01900407402404124030038000c1e08808100c1070361b00b01100344607175004041d04080ca0b16101d14200e42d840084e1040000c1a0204281c0d4080b0703400e40010001001100782e1255510701c0c01c036280c030009400040711880ba420482040000c40e602001742da40010011120050701300f00d04000400b00d01ca2400e00419007400d1800000c140200800542140c90007550600031076a05550340c040d840c8824040240442c1d42403200d170440041c0260350345903081c0306051086945076900c0c002450500d256028 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 83485738 1250 83484488 83484491
    0xb09060a060609090f110414090c0307021504051e030408070902070f02010e19030b010302100503040f02040c0e03060408030108060c07050a0312291c03140d0204030c08010207030f0e06030f04020310060603 90
    0x148400d050262700b1503400748244c4016411418010380007910b5221002100c0c2c00036003190085000d000060082d4900400b04001d1500343c2c1c514480703955141e4000d482207038000d025a0713500040030b4950740210391507241d2250084045071059401995410060413081d604840454035040c03411400a000101440c05890058101e40c074502c104240d1984002205040103003c2c82403200080811107020351081d0304540100e2483c46040d000c07100c0b03030a0128459414810041444207000c59140154160380d10001600c0059440d020300702c48030301c28240700614540c0b0020322140480d01c101d00440b0001d005543c0402d94a40c0710442000c4883d95911204144030390365103003109464004c110300341040542001c041c5205041d00c004d0480284403c0c0c0e450316000014034a10780907242da0403600519404118840103644400410b4002d40080758100d0100704042d40c4101d505004440301459100c00400c1b90346160b444155010641401620407a010710503a03202d81d10071081401041d000d40300c540d90 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 83486988 1250 83485738 83485769
    0xe0d08180d060b1c0305160203010b040f020414010806180601020109150f060906050d110d020603090f0c01080f07050703020a080412060b040203060d0206180d0b09060a060609090f1104 81
    0x8000c4c140303c0c43c25500c001c66407020010710009401c10142c545d00611035086500d00389540c00821301405130300c100756070311500d40a90000c1c15095580a04140d4800348055004107640c0c60042d82d0038501aa00c00d6844120704005240c0000d40380c0689510003810300c001f00b115040303599100f0f80d81803841020320704203441725038510100c5410305c00c0380f006041000e0180103d80c0743c18085400303034030310100c054040182141031540c9901c8043c0340c0000554050640e50303a9203480c100240e21600290000380081c0a2130050a000c0d602c0359031082c0c06145102c154901c40e4a0b03159041c2c41c19444501d00302d0030f602440c485034000c80c9551b00a400101411380c952005000c00e803070203c08039404480414403a03481401407107495200c2c191100c1c590342e81900d80b00d42c0d0700d01d030007a001454480543c2c10782d0700c114408c80f0103080140c00d6070b40c24007400c80e00040f1006511080800d0b07040e00d002e409103500003420100c0820003885603400541551000803400641c45010b12050710b0241d10507040050340c0481c00d032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 83488238 1250 83486988 83487011
    0xb0403050703111b01031a060301090204050a06031406040c0c02030709050703200306011b0501060810050708040b0402090705070c0e04110307030506061504210c05010e0d08180d06 79
    0x50700091a80d0500d01418015021403060600180f00403001170426a4442510b542d06050300c90341c19075414003d1070951250307502d1580101942c0240221800386100c0f038000625103000b07004000007030301110980d42040c0e40b00300a010081900e818402d042020007201003025880174001c1c400070340035403440030840303190503140602500c07014580c0c55000c0002e180d0113041202c0110aa90304020240380540d030604d008a0804490100307014041d0182d40f178a18006282d02000031881101113a02e101403000740d8030b04100380e5103030f00300b102c0240540407079900103030041c60b21200341e613404602800c0190130701007152582c40e00c0050507003003299a4496a024001400582020000b41d82000c500030b102050950361150340300c1e20084c050900400003444800300300d140d42c0c42600c02414501c1c4103200f03010000211020103151000702503504440070140481d02e5480384030001c8020b94060a0058058015a2095904d034049201408448003800c407400c0703140e076605130190045010f010041030411000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 83489488 1250 83488238 83488247
    0x607021009052803140115090204050f090610030b060d0609090c0b03010f09020304020406030f05030306040b060a090e10030209070f020111040510030f090b10080705060a0806090901090b0403050703 87
    0x83d80000041d41021442aa14090300c01006aa900c0f9a29030034240a10403401c0c0901189040f141a80040201c08540000e5943c041c2c42100c3c000c880462829445500303100f0200d00035a606500410111060f0f04018001c0e000003034083e002501711440d00400140c0e102c11120700c1e0700440080354980d00800309111001603100d015043c040d05240c515454080342031400c000c4c3c0d21030010b0300b60300031000605664855010400030340c0c0200f900c2c1411172291505546035841100d1b1a80300b64074001607408142401d9050380d48207890b81d01ea40031720381d08004121407086001083c42140c5900d042002c070050b116015103500490301910381d0000155410030190a403484130a80102e40a000d00c4100019950448124000c0c4224100002c52030030240f00f100250410300340107450f0714420130601c0145140d540843c6c003210b0300c8100365078040361900200405882040c110b24001402100402c1c2145001000150800e0108000080f00c48041e503404582c0081100e0942c040b0304081761740c40905820 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 83490738 1250 83489488 83489509
    0x10e010f0e1c1a0c03040b04110a03080406030c02010b0a0b070c180e060a02030f0103020f040e120406090e0103020a0e13050a0809090109150b031b041e0602120d0b060702100905 78
    0x241d00e03908400d880d00b130021003094080100060b00c5018200042002d018502c61303d080c0042000d0030141041c0e0b141e0a107400350b94403612480d4002840d0800d45010300e4410703c5003464180c401032502c41c0c85c51078000710f80a95001145c0036500035014100001e0085034515403050600040b07032003c2200980a0f000d02d090400050400310501d00400c1040800a40c2c0c00c61075042da0750440d034a06201c0030380c01c0440e0003040c02104c80001403141480381c4000c007d5080241040360343c15a2110700003034403083c1800d40d084003880001c1d005811007071706000300490503c031964444960500401c02c920940c031000d142c081c12a1094442d5000010580700d281050700c5420b015013007070501481703180980c210390704c0048000c1c85191048013000c00442d07801c1544030705ca840188071b403007403039601c1d5500d43d194000769602217100c0d00e8071280390420014980d800840c1d03419204000c1030f045400c0403401491000541840e60300b49510200c10406180144d0340c001440700c200b9102d541d04004a4140b43c140a0200c08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 83491988 1250 83490738 83490773
    0x50a06050403050d03050a090515061c0b01050f04020f030703090b0609010608071404120311100615050702030a0803070c060501050108131104090203030304050a050c01050306010e010f0e1c 83
    0x801c000600116030b00144001164502d454005125961241460010301039050020620700481980c03203003074200c0c0718050340256070444d07600c68407295404026400c00440f1000600c010181401000076280888000b4075503040604058900a0001850050b9610403200d01011a40e605645001d101b98650351075401881501e1004040d41000c0d8050726403280244540100503c900520700034114882c02d07500100b1101156541c00303025442c000c1e048181440700206a440354881c40d0b40c0e110214081c4000b2a0030040301c9803002c4440a008440303e90000400b40d0f018811104502c1c0041e0b9910000d42c820403250359a00d00c2003145203400d0090350b9042c1e0240f810422840e040c0408006040c5203640c98a03803001c01f0940c583c0d00000854081d2502c1007000c1d5050101100700414054040b4143d00b29510074403e6898010703140d401503d01d400300340c031624002000e5204850300c65006880c41604100301d2b0070042d0713681e2002c0700080e1840c0b041c3c0c4001d158540c00c0007950020800720358540ca80081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 83493238 1250 83491988 83491997
    0x206070305070f0512040c0806270703350f0301080d0f0206060105071a0109020a110a080904051909110a0501050f030f060a0305010c030614030c0a03061a0402070606050a06 76
    0xf29841001000e50040707825000c5035517005404a42040811141d26000700100416111a031400c400340c108002c01440a0340058401d91104851261020450805070b903031161b500300c1211403501010350300c8518203d20108800c1645802100e40c41c03140090aa00907002041659a40c180002da03401c201000c60048180030320b2000c10700038140c01164980d4044001e280c481c0e11249141844c0d5401612100c00281008104001258103506500101988001c075203443d0150315401c3c1e003d955880c4a100064000181032010b4250761400c0e400c95900301d003c00e098041a41210704c02d0808a58400b201200c903503c4200500d5520b06103200424010842404d00c94100b060505c21010030f44801006241040403150000b0100d40d140081800510707041002002248a11a400350080c0b0441c06007107101c2d0301140000702c00b481d0005924104a90207003000c0c14552071651604003412a950040003298200c4084510300d131154400350000c0b130300410f00400c00520301028881c8000e00c68000c1e60802 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 83494488 1250 83493238 83493257
    0xb1201090c1802130b0307020a1a011a04030503090d03030e1501090e0c030c0f0613061101050105060703020c010f210f141b07030203120a0209030c2b020a0e0106020607030507 77
    0x201440c130200c000311000006071980d2940d4011089003803403007102008000e02d20004403041001d0304140524103072451602c4074841d403209008448030a0040e4400108aa40b081080c10140e06100060b03c1b4000e00c42d05020801c102c2c80da141604091014980d160300b43ca54900410280c9018000d46580e09040009800d625034003101017a2169404034455002d0040034001c40d0840e210701003200d108025041e842042d281c0c0b2140014030501c130600a658135582084000700701e51600c901215000f50341a001007069110001c019220a1020b0303100070144040c014241a0035800c1d00c0646143c0d581c11840046c014034441589811160244040b44080c1007120070061031003101032520000d41c5007940f0090b00c3e00d50340d1800701d10f90321810300d134104c84210103014000b1805040d0050503a0316001c4066941d460164400d0218034410355010381c904000a10b02100000d07041d11319034900500283c0044242500c609655050a00a034002801070348042c0400c016158180300d071035007050340c7c3c1c542080070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 83495738 1250 83494488 83494507
    0xf0b01051305060304051002220f0506030403111e01021c0c020a08030c040503010924050709150504030516060206090601060f0e0102010e15100b1303060b1201090c1802 74
    0x8106550280b180100c03000004101844804c110014455000700801e5550300144424501041c0c200701d0300c002c0f0040400400300d2500d544883c44029500090891400c1d680c0c2c5031011141d00c1a203121030301041c01001c0300b08a005011050580e8000010340015940700c810248501e401b8040030380900319180380c1b0500c0e40a8903408036142c400a500a64001c0d100c1d1100c0d01c02098500c52030b406179601d507207000104405c11001800961038540f44000d000c4104062528040c140d80f012590f020020703102103030501c460700820000d02c1401c044c0c1e150607810319071a950399510b001140030b402250309000d40e00400c64564100030f99540700d101103010301895450402c2c082c058140344041c0100307001d0031900d1b030203069100f50b002c0d184819030b04040350410030040c4c0087c141254191445000301f40d002c0f102064001c101d030119a0b14510303115079000d69a103076480da00010142604140c0d03009920001d03103141c150703003406000742c0d16000e4070360200c40c2e0307207801cbc0004640890f0007041d045490050002144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 83496988 1250 83495738 83495767
    0x609380a02030606210a1109010909020d0608060408030f010b0f070201030b010e13060602060105030c130b030109170a0921110303090d1a010602030c030d110403150f0b0105 76
    0x40000ca403040240e160386800e00000d2050088103048000404410b140600282c40750200d0f600504482500700920713030840a04015074442c5140b114049028904200400c050603401003510350340130100090450f40b034410341c904141082e035050383d1612010043c082280c00c00607000340101800b481c428900402c140b010400c6000d40600a0b040c145e0341c0000108a9005190700b00d107001005040c043d4001004640ba0000c1600740201001441003100218003420f00090360aa0201c0082c0241950b44242d2581800382c810103001c3d5415548500310f40000a07003141d4884118260006107644440711103200504403010b561210815040808401400400034045440369a4105100d100d5049100000c207146102b011003180d0485030046e140824010070310341d044087e00f240107035440c4590361080c040741d0304e008000101409070000c10501182298650000c010110a0800b09003050754948644113511420029480010b440706084c07a00c41000d4490501c4141c000d0810070b081c403800202081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 83498238 1250 83496988 83496991
    0x1050402040f18170d11071211101508030c030406021002030f040206070c030b0a0f060506030105061b0709020d020d0b04050c0313030e0907020703050d02010504110d020d060938 78
    0x140401e41d844d91072411048000101c80d01c1c1e100168081c42482d92001c60b411559112410030b40d20001100c1207039166502c601d00001c8200d00143c0201041d45000000b00020128481001c80c00b030030100d80003400c0740007030000c1c0c880440d0b45405541c565191030340103801c2c440001e07c0080d58500c10800c103c110300f0701000b01c0b500907405a42082d11411740d0b103000000c42135a0b400260016292408015280390950000c01041c03115282c18400940e448040c00b445000a004080c2d005105010070001c5042000102c05c1e00381c60181100c500c07903941c1001000700da1201d841980141c1c4c00281e013061801442c01842403865090300e0400039460141085001c900020780074021089510701d5a409041c8214506883c0644c010000041d40c1000d20000e5520700d8680b004031114010101031290541c010311410b482190409800d09500c44800200001c3c8030b800070080380c1c45800d4a210101080d1076201c0c5680310391013201034540d011865070b55500b0401c80a00c030035224241c140740c124294615406800e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 83499488 1250 83498238 83498243
    0xd08100806241c0b06030c011b0809030a08030702030304060b01050915092d030c1203070b041a070206100506040f030204110f07111009060e090a06080d0201050402040f18 75
    0xd4211698a00010b201080075030381c000400f180302d52400003031101c60240c00340905021400c0f00c5104000c20010745081c2c804440c00c600008130111810080744e903500060007011002001e507043c01c01180e407400401d40080c1e8448005070b1004c070410042080a00c0f500c5403207802421b1660404c0410303000100810105048080b440d13201045050b01d5440b00301c0011b196443c2281c080c6a00e5043c0401100e040c2510a6040d101e8814007032484c40364203110146009041c00400036524180345606e420204e5031018008440104a0610318014001001c040ca40035060ba640981258101003289002d03104150f044944030307a00802c42041078000c55038224045990642d0301103003801d80a40f0440301030055900c0316404481c00281c51080060092199450300e03000c4420500040e034505003201d4510f4603014100c08140080010342062a000c4001c55000e07452520106580d40c4552041c0d0400b01410b40d9500035039129424001145803600420350308185044041000c074400483c0b81008080c0741001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 83500738 1250 83499488 83499541
    0x3050309040c12060303020f06060603220203150a051e0603030a1404050301091511090a05010804060e010204120b0108030c060f0403020a0203070b030a0b1503160c02030d08100806 79
    0x1c06a0b800e00a140e42c42d20f0701465002040401d54074180030791902c040102c82c204901840000903414648407007035034010300552402e400054190036508003881441803081c3c6c2d140c802c2c0102403000d1928103018510a1079554400300707540c2004c085006600503500701e60780b040308201c1c0820000c2d440000a55216162a15002c0034100d24001072001511568120075015402d0a201c4001d202c050215804c4403840c44804101d0308510340103100480c054200751691090103e8010016913110391507103600035008030000241110700c1e418541c01caa02c580c0c03220401e00c42c00f098a5041c40b510404840c01440c8100c060b5240092080b40d40341c44501c010305000184020b0800b1600b854800c11040c02e69a40c090200c4002e5510341d180c412141d04101d4a4921090901551030200c1c100174210034900446410380d03500756100c40180d99011401ca40c40ba6040007000040d40008d44d404104a801142a0703450301003080c201860000048000c0d900411040e0348040144155460080310002c0c01502c0f004a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 83501988 1250 83500738 83500751
    0x11010c030c0503060f010c14030a080a0905340f06020f010209062a1b040e01090f03050f090603010f090513030f05071401050702011b0c08120402040603051e070f0305030904 76
    0x140d4480b031070070001030042c8c40300c0d41e00030b515064000028418020192103e000eaa07031007807000300a44003100b10080c82500021084e10b500803070380108102503d105d28a00c01c034007115540c00140c8201c550700c102030304600302e0410011241c042c85000d210b19140d100952800c51490f000c108148950000c041013001c4c1030f40016036101101005d08041d0b076180c0161110440c0c08095005030384622500d0501ca0b0346001034020043d03d05208405e5040c0d4003860741910080c4039241525550051003452042c0c3d0f2080110b001650f4802c2c000314003a0990410480400f0304140c0d941049940040a0956075030b4201407040209400a400c56000101450810381c2c0b0031b01480e01407619170381c00075807550075802c0c1000d21000030303011741048030714002d041c1201181c01c05c200c02c00c590807212658082c11240c02000041003480c3d2200c8840c2c0c0c01800503001090a950301d503100c51400b06255004034500600c02400764000c001800880300801d000415100c20700d0440d2141070701c1c0d1190401c81441a0354903403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 83503238 1250 83501988 83502019
    0x1180b04060b0607081201060801030f0b1807030f05010c0903020310020c0c0406060c170a0f0509060f07030c0c1e0e10030b07050409150f1a13030311010c030c050306 73
    0x100100a100c401509480d2101c11500d031a05e52070b0030034003d282451455900118149119410060489801c0103c4421200c7d035600d510002030405004641c44c4034070b603407681c0c0f018202081081c005501c034102c3c0a51070080b90402900311405000c070b881c1044002802080941d130001986075602c140b0950050391101c00d005158507003070481040307640241c00c0000000d03540340c0040b407102c41c0700e01a41440d035403040c20840d2801c1911507240c2e0040030480304d4a2000f003103407244000d0302c40140b01402c4540741c12011416012f1a030019103040340025445580c3c01c00700984090000014103a13019610103840c9400040d8052600e98000d01550108175400030b10440307600500343c0010740d00903090b14054148090300030195403050040d00b15060516040c4500c0680d0350741a84102c80b08000801c54160400030850600700910b030015a1058091200001f142100031f0340c2ca000b10310079103828500c1000c0034440303801d54900440b4003040c14035288107580a25003001c1200c0d4801811500f150300030001c0d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 83504488 1250 83503238 83503241
    0x309100f05090405041101120e030a030b0f040905010b011d010f0e18040b0105010e010503042a0305030a09090e0604020f01110f06090c010908060103050c090a020d0203090c040e01180b0406 83
    0x1609043e489800e080030700c0203011520030010008002a81d0b40b02008a002d0300c0b08043d241c884c030305148554000c20810448038030235800b582007108028012a0250b00b60ac0004040c0d4480038419540e5940d18131b01c5200715030300101c0d034000b40b03440e00e940c1042d000e08030000a4001d12005800030305110b0780c10102d900641d541c1c400d004e0414140d85ca1100300d8145070070300b100700850034010b69010650704e04c0940c0c82d030b45c00341003604e00c00c03a4801a01e051031241c00c40070b00180e45a0b98450040d0365034807440400000c5041c0041d003402c3d502940d85403880303803070400d002c003d44400000303500441d0004d5040c0801340e281c902e031404200d102030911558400c404441540703031400c000c030380d50b1140c0100c800380409010007081d403006060090780c1e0003410036103440010307459140a10000300190301c01e4090b03850341e00b004041c042e07026141c84401801c0c411104110000d036802101c07811801e8109062072071032441e00d13109a48110f54020300070860364164502c2c07101c030390021030303030103070400c54254005006c00015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 83505738 1250 83504488 83504497
    0xa03050109060516030209090408071b06020d080a1e090c050303040e270304090903030b04060b03040219052b02060f041401030b01050306011209050d020f0c030309100f05 75
    0x11800800c00d01003142001d4004200c25120750143c42100030b80c03820094801e000359200c00320020040300d4680c0ba42c2d0744050441e44076510444040c040a0091818110000385180c014841a0003600c2032031002c1c0001080c02400800748040701d4a00000c9400030400c10200085102d22104000f410400340e0900255003615540425494400028040b4a5441c406240c0f0f018074181c84c20203a03007900e00e2440030b00030300b41201414459441400200700c50007407602f003201940e00138140050a03d2420001c2411ba0741641c0044440e044000241300c01c40c1881c4042000f20300c941c0c45440320450401c00000c2e000c5d410403840101d01c9154070a006502018400e00f040344c181d0040c41260703070701c0014031046241c4e0130074807039104405c0d40840080c140c1d5001c3c2c001d55101000580d1550701d0365451100540e2126024024050803030313650549800003450030000707181c3d008920380040c401d082c04124110301c0c02044d1522540a6001840340302c07503980302da8144044a800c02d003000900c05a0841045405018 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 83506988 1250 83505738 83505743
    0xc0608130b0a060515090f0d08040302040609141305060115050d0c03050610030b09010e0405010b10050c070504090203210f04061e030c0903021002070302060f0315010903050d0e0a03 80
    0x103161050100c40d200640c070190844000303849030150318400384005e40d450300800e03405580200043c03a0003070507498400241250144608013441c106620f0f600814103c0700300b60041c2d02802d540b0484272817001d540214855010a00d1180504071800030f9503400d03158101803041c1c8000b0103a072010380c4913240c001c5e01030320501e41d40460100005040114001c0151900380c441a011705010b480001c0a10711a00a49074910000382200070b59901c0c4c03440340c40c1e01c0300d40240245d407039558070b043d00000c0d0768a0044080c0d410f90030303655883c0c840703107101c2245d41010720350b80c41544142d1900044200589021030014540d0324455003841070b200e942004102644624042c01c1c6c0c10490010b030118005421004c0008510a06554041c0140240c1816003c40703400c220048040f900141003000140b0740180001c40781d41d40c9205a5840b87d0352030703004c1031146d0003184c20418418004010030040d810308000f20f01c007002d400d1a180109a1964459603280c11002038203204001d0f5000b045c00541d02e0b4600d98100559 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 83508238 1250 83506988 83507003
    0xf0303030a1407050a020601051c0b0a0903111603060522050d0201050c03012702040503150604050a090b19061503051801050108070b031b03040c1a070c060813 70
    0x24111038844000d060001009041002c1500800d00300c07445002951054107054005054031303403c0104201110f0143c051400780140b0305140310f400207410000c11405035002180c080303000e50152070048e2a54072182c523888280c1d4822a19424140040001c2100301d941110300041c40380c0b280c03400e60403200c003084040d40b0420020040d440800800041d910708145d8113074000c1000382c98100ca24841c500c801e104a0f4116204191040350200301100e020005010110f8010302e425900c1c1c0210b8203010110815500f440e03d10301c20404641000d010b460b80c0200348401c100f110070190394544040080140c000c010001000031505605441944240044c103070300c0d8400c90342e0f184090f00c010040c00c00bc40300741c6094501e11214002c400720502416044c0c440300030103849840c0c144880821560401085c841e120b502610f4599041c4420f840198011405004414892806e06102310206039801c815941c41101c1040031700045000c40c6e03009c1c0103aa0041c60011102d441d1548445946a0801000b0744101e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 83509488 1250 83508238 83508241
    0x250503040b030a0f021326071502190209040b130501050414012415050f040b07140a0c0e0c07140c011103030c0a0806030f01110301051c110105090f030303 68
    0x801c14405580b02e16862602403102107200d11460040e801110703c0080c000503000024004118400002e80615101d126140c0d103021001030f40ca440c0401c59480414800300d107101e03004440c1da0601003103c510000d40d01e038241e04030180d40800e507000d1000740040d140b410b8810129003903d241101d40c5c105681c0000c020b0016040c281455105001046480e070559031034605813404000020190800d881218844120494580300e0600c400714542c1d4040c004020042040d244500780d201e0180014003a90740c442c0b5103812140c500524251803414110880d0f522149000c0002001411142c1c261050070001a64503110395500b803da40c0034510005040c080182c91200c05000c00090396034410304241d8402149007181c001e0a52284404c0da0303002c0d0700000400000600c1c1d070041c5400c5800075009000c0380e0b65211091102c13400c550045040c400c03a40d000000400c000d180144440c49543c184801d20070710309007190f0311510380d5500440e6160501001107003030520b40e41c0710b02c03809036035070b501405a954a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 83510738 1250 83509488 83509499
    0x312210f05070e1008010621090807020a081506060702041b0c0203010c030e0c060307020f15040302010b011407060e1e0102030f011401020601092f0306030607031125050304 76
    0x207044100c1da108001400021400c02d14a400480042c00d0822621007021590811038111a084038950241c0c80c44030182c141590840c54611070179800f28010701032180c407019140b040041800d01a030008010764082c04d5960041d5000c0401c6036040300d012180580c0d14601d034804030700500003071100c02c0b00c0355100d0503400d940150450b00d0210030320301c00ca008100c030307190222080d0201c40a00300301b854960b008013401d040d80c0c00c08072b008640080c824011141e4800114050a02c0d200e200c154400019255400380030405409000300f40c12650b09080034000d02c42414014000b03030042d104003600c0162210108142c045c001d2100c040c11030240515244a007111010f490302030340c400d6840f114a04601e60000810003a1401845007050059018203010b9203800c00721405000b4045100b800504a40d00c004034442c15048a40340038044031610580328904a02014102000103110100385420b2500b150031b2200004200d4140000103c58200c0c0c2c465490076014542c12586401889480b000402040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 83511988 1250 83510738 83510741
    0x10806040204060608010605090402070809060307050c0105090604020d0f061b0504030201090905010506090d0309150903060c02161701060b070c08101a040c051c0b0f0102070312210f 80
    0x32880c001d641c2405015a40e030b004440015091050b040050024040e141c0c46281c16002001c1840c05242081d0801c47e1078000150141e0003a034840300801c4000a022003045000c1c00790540c0551031030041d01d4145401e03008615102c5104200401401203509120b0800400da0b0022141c8003103ca0704039888220b00034090066440350000b07078045001d581001602d2582800341758180c1d1006403005041100c0e030301c24480a2941c1000840c1031000c03c240c00708107024203400e15001c0b03105540d0f4401c00f43c2d2550820720f0032030f07180c89500d008540101c01d075900c26401c003941040c2110305400d404c40001c50609081401800c203504402c42d00ca41c006011030034045848110070544e00101c050703c1c030700c02c5980e0b691000c0f01e541c075518240788420800d48100c00e16195004000b4059642005480c0007052982101031480c280c4504036025603620b40c0d4030035810300a01009450b00280020900036044d0b4441d4911031000b480802d042201624200c150001c050015400c801081c0f60103100750f06000c0070010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 83513238 1250 83511988 83511991
    0xd0f0912020f010e0c0105090a09050406021c090b0606090f060d0c02250608130209040b0f090102090a290703020303010503100b01050d051b1c0b01030b031b010314010806 75
    0x3001407088250107041e0b4201032041c40c40840e02540100400b00c0b4520040d03850f604030f522203d03840390400301d00240f6541c0368094944580e10442005a4034502c0110760400c840c03409404001481c5020000c0c00041c1c00b8032049900820211a014cc448442e040021501c69141680717030340006002c80c040400f42800c2c3c01080041d007880c5c013174501d4407511700500707411120280c103e070f043c00740010801c1012600408650b0342040c201c03040101151000c0d0049000c03c0415030717003103403c0303844002007180703d00302030076196080340441e802540740103e4540014000700c8240200602e0481310382444a42116161011094a0800b02c0e900d444885904000e0b40340d4000b44180f5009000345103e807a00035a440c03045110003c01610b83d5030425420084400040c03500818101140540c2415843d01480400152081010b03081c25258a281a0003901c419074903054855814541450182c40c429580840c520000d07155802d210022008184012405403003061050030408900c0000401d40c4040402c145 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 83514488 1250 83513238 83513273
    0x90c0810090c050108070c0b09010b060a120506011d09180607050309070510080c0c0c03100e1002070b010501050703051c05090d0c08221a030105091008070303050d0f09 74
    0x12807400f540c4100540740c2c1d5500300c800c200003806c940506d10009101c1c1607082e17002a030100c00010348810200c003017407080d803200303486501081c4001c280380e16046040c041e07150310150a10300541c24400c80200c01272805c1050340c0313442c03003a04550005001450408004c14003544000e0480340c15040034000035100d40e0080c2c644484901440c6404105401d040e40c03289105801503403090125038444402d0001c0e50807107504104140540540c0003e266010003180710030303030344500001521658080000745000b41c00609080658014007440000c11040c1e0003040c110340742801c140350313141240d2400b22041c2c880c19003074410b00b1420100780e008008040d03004cc0d110b85c0070041141d4541181081c2580c4401c0c2c0b841000f40980e204010b175011001c0030518912089141c07102405403a41c9460740040c032280085041c244071800400108803d140001e0b825230803195540300b51446500702001951181c41c940809410300c02c0014010001c81040d501001c0480c01900040003461614640104d2400050001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 83515738 1250 83514488 83514503
    0x8031302100302030c07060c02010b09090706120515121e01020415080f011403070506030406050f07180b0306060d181704050d0b0a02070812010602071d0a090c081009 73
    0xc007840980203200b140d0140c41a44540790031300005a90760f40260510380f6414045540b24505600c0680310b022010340075000090140000609120740100202941a41001c40509040600c072818501341c03502400c0c507105480c001200100700d00c10b6071900313051800b5188100030320f41449807103190640c0600145c0b1040030740040007041d0400120744200040e01c00c01880780700e2100400c1034140490681d508402d000c2e05030b4105668440c0010748130380049606a07003a030785030010415800041480164407044d2418101c00507901c100366006d000c038030b030b010b40712250b00000040765281d40c5e084180c0c3c0c10301205840500000b5880c034030041070a03642483c00c4903005070140c1c0124001a07848240c60070703200c0140c0807070750f0400c00e0f440300d040840780a8080da0710ba07a803c10803030011400080080080c0a0042c08250b680d5161241c000e2038020300f0b5000e89254494001d500f4000d00c02c121034150081203000f80030400220702d04201c81c1030050343c0c6c40415103100318640201902400d070400c03c00140030340035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 83516988 1250 83515738 83515759
    0x901031104180b06040e12070807230303160909110c0105010e0606070602070213090b090706020d09060804060b03010606020a020f0d0b13060207020d080301150f020709020c030708031302 82
    0x10382d1485124828000b0301c800318200015003d4209540080c00e8000c0ca030301201c054403249103c009080d032081e00c06480401340025440184240c6040c880049002601040c00380906050f440391207000223004442011443d0409101c1c151080c150500500710011041140701070041e00d40d5141d0b400420159815401c040000440c800341c003203414482d00010700140d2514201e983e400009500646040741d001c107402415050160252150492044c4554902c4500d42050829185002c00d5640514219070045600c10f545c01d44c804285000c582150900d0030079a240d0f407902d40c0180034986030a540541c030380140007640b20350020700c451106000351541010fa190300402c3c0045024481006030064660501088841403014411107545018030340042c10880c181d800245900101c62080ea83c100010005102459203840c200d20014000d06144501860000d0003944820341c03445100c1703151743c0c00324455180820a00131246d0032075101e80394941d84e24003c0c05100151201e8001030b40900000c50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 83518238 1250 83516988 83517011
    0x180b12070e0f060d0b03031e0405030601090203103012030617210c010c0503011404140106080c0f19030b0a06020307020d1e03170601030b0603010b0d0b0901031104 72
    0x41c100031820b1400340055260407079100d0304001814904035500c0e051300c410020315040c0340038848a03500f60801941c01c0380d41c41d460700080500d4500d040c2c00c061203491040040c04400318240c0c0c01d400407128040b04404008400c10700b080d038444100f00251600241c0f200712901040b52000c4c0846c011309003030301d080114603290f50103403508006025201a04d64000010500c072580c410300c8040f0541851480185410340d06000749007520407004501001c144048010310114419108a1403082d0060742c040111608141c0d040e12101c4d410700c0351000340300a80700810708849810040b2034455102c0d49c0c000c1e658100d000d8400c0803c0010643c00000245010446074441c507040c0b03882000c070703030150340210f00b8495035408000b00b0640d15407048806092842140c0e410460890342e040b4541c0c029120703140d001960980005e24a03038001e0282c0c0c10946484c050b040503135124010349040d19120441c0c3c58a400101c1d8110008000c02d0082079406880400008104000841d140401c0e00341a0790a0040c100c052 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 83519488 1250 83518238 83518249
    0x703030210020c12040b04090b01140a08060325241e0507020a092306100c0602040504110301030302070e0f0c0c07051306050f06040b030403180b12070e 67
    0x5000050050300540c5105000d8200303a006082d00340d10180030340348005001380036444140d1066010842c003d001080410280660340319080384c210003803c004081c114052000342040c8245650300c000d00c6100d00214525403410401c8000484044a22102600c4c3c9a1803a002c041c89520030182607071103086c034030003405401c0c0003001400150381e1a5407460001e0a00c8130803500400c980d9103000c001e400d1101d0b4025130750391a9144010201355000040311112071500c4a45c1c09503802409235030308a000280311449e101c0040805080c0301510306903041011600d01040640319075403120360310600f8000c07290501344240300194101c9203e60200c45078207a9030102c00c01c1d00c01c01161024440790002c000070f030741c1c0d401c0a001032814031188019106d009441d900001c42ca4100c00120074101b03503a962017480b0b281803189020b06030740001c650231810700e4500044900300e0b00c00200000c0810100d01c43c0700d2600c4031034558400c0030f40880d110341503e132003403840312155101046844100080d926044d814082c1080d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 83520738 1250 83519488 83519503
    0x103050720070e0a0e06060108040f0614070806030a081c090c090209030613050d0e03011b05040f090b0a03030e03030706050c0d180308072f01090501050c0f0904050c04080607030c030e 81
    0x170300081d1502c0d03070741c600054480c44001441500c159204213080c10008000b03100d00d40f1218065445000301d4100010300814044000b001c1c50300a5003d801040049081c4206450202c40780c546e403140300f19201d00e00b0301c000c0d2014402c0101a450705180120fa0095180c0142c140b0540a40071601c0f03680c0c0b0010f4204120281c10806082900003c9010858a1003040201d02e0010090008555400c0e03941c855020144c02e03444600014101107824099a1900c0070326900034200e080003800681803120026114042c1480024248041090a49619103082c000d0f40c0e18031380c028400b00040c5c5803000d080200c1754460744001311614a009907890104901c0300c8480c0b100b90b05070703541540c1656801c3c03080e0303480840c0d101034803484418200c03110307000c4c103072407051403d00c2109000101b8582c8151a100c3e00f5100c0c0a401440940d4041c040c1c010b09281e014161014141300300da000c9015100d940c940c60080c81030780c00200720b6000e40010410425016044070b000f0941d16981008611030f08107d80fa11000c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 83521988 1250 83520738 83520761
    0xf04080607090e040b06060f190809010212060603060d080706050103030801090501032001021e0a1a13030f0509060706020306031b06070201030203040c2115020301030c050103050720070e0a 83
    0x481004c90013107221040c82c16400180070b41000e2801c012801240240d4000c0c15600c035030030120030001502981d20a5080c0d800000140082d1b0600030b901c0504030003083c000340702038000c5074003000040c0c059460360b030104000d42c3c210202d00d582c0c4070507041c01d501502c0c0902064011481d58000010001d10320310520b4102d03900039845100031028008132840d81450b11a05604500c9154000f5a0003000952102e100b41c050780010401d00c81c0500c0c09181016080c1101c101d0011503008001c0381c0035200d8040c07544990b052403e000940080e80041e101130054505460700b00c0340c0490804100103095004501400b0700714101c40d514404001c0403609100012210380d0041c009000500065000384c0140d5005885084100251503c2e0944003140585d082d04174801c1c0e01641e02444140050f080e01070015420740c0c0800d6242d9030468980d903036109502c1c13203424105543c40303000070600b501c11062a074200d075000700c00300300c00f03004440c146030784550750301900007a12209c2e80420000d5000b88a41110ba00c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 83523238 1250 83521988 83522009
    0xd0f0f0806090403110d0201020d11070210051c060e04150b03030f090406050301360201020c0d0302031209011b020102090a0302121005040b0a05010509100905090307080f0408060709 80
    0x9441005005200b140078000b10240203030124800c60604050210310026006035000503101c207050f09200080c3c50b5281c85018440c0c00c200f20404c0943c4038100c4402ca20141401c00c555908026104906028407910340b414499103408008540c1c0d00080410b14041c41c003e6501c1c0201c4507140c1c0c2c0c0201143d40128405900d98401c103c110780c40340360340010b04011100204000f07400d03942c03a00401d080d00c15820300301911001c0c1c0b17002104c074103c040c103d200c0d40b140070144001b1185a1030380042d684038850a6590700ca001c02009803400c140c0708000300c0d281001a8290b8960074180f801c4018080e11309600040c2500d9100640400114070510a490315180014400820241381d80c0900c15500401c400c8140a802600701c039003904c1240b0301906028920503903500c50140b4001d1410b00440b83d040c0c1000d8410041017081c8401c0240e0010795405903605900006140e8550304c104502d540b00c0c0040c0104103000102d200c1440d520b4042c0a80111030b4a541512165a03400500710741904080c003501e413550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 83524488 1250 83523238 83523241
    0x100603020315040b0120030306011107120204020702040b12070305060a0b130c050c06040c031a0906060415080d0909060e060a150207090e012c0a020d050a0209010303020d0f0f08 78
    0x18940798016028489040c1040803d000319041b1400c00003841c011081d6140d0300000a022013960300c0048a00c0c6e04661401410b0307000c0c14540386121500c05100060706c00c50300400d10308155a11a4841031010100074103400c0c0844a00d0340042c1c4410140c03206582c030740101c5000520407400380c050450320f054020003641c8000391640c5002e00405100a81d4030400c001441928850301040000c94005d60080c002d00149501d1071038185010442c040201301407040d01828030817010b000155058000c9001c58001c43c6c601a240e0b0003c41c5d0140303c1d40300020501c908442c90390a5604010340c002a10b008031403e021880d154401c11140e107030241c1c0e2254010381c0c040000c006040780c3c51081600e548040c4192000b40741d4075140001640d410004202e940e9640c1c0f040100c05015001d00400c4039050702c0c07109007408108466090702c903441c503440640a60761030003501080040621044121036802082001e0701e50b1282802580c1c0d0080d11250408a01100710440300940564910180c0d19201d0f070300e0080c01e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 83525738 1250 83524488 83524531
    0x41b0e10110a170706020a1101060b040b04060c1704090c030605030f19060b03010c20011a060702010e030307030f02060c03060321090d080a0e040207020901052e03051006030203 78
    0x1801840c8190180000f010b20030040011014002060148440e540d9103828400c00041142125590b52110030400ca08000401c100d02c014425503044954608060161543c40c1c00c001c40441da0000c10030074208400500850003d680b640005240c80c0075a4007081000d443d0320031b0542e2101c00740810070195004465100b20b0340c0d1460400d16006108084c0418002c08000c042402d484800707010a000c0381c5407911050760b60b40c188a0400ca45c0451400a01810450303414a8031042d403020708003406620300240060540e40668611521004041d040f01c0c3c0c1c410300d608004104a201c6d500040043c09102e001c035040f00d40ea10280d03405140010090f22951005201d801d000700d002219276108500141711042581d070701d0300324580c1e201d0f019000b201d41d500500c5a008103028140600740f44128810b000b90300140c2c4500003650306494055841c2d5015070300207080302e9030710440e555515070080f852921018a2a0381600183e0055241000502c621921818244c090780011078103a040210070790320b91101c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 83526988 1250 83525738 83525753
    0x60f0f080a12021e06040212010203060112150e0a05180319050d0b0315150a081f060e1018110306040b062a060a060b040311041b0e10110a 61
    0x11804003a00444a2102104c001c242d008050303c2401d68031504008100015810104a400d417000ba020000b1865442c0520018201034510301e948002141d840c49401030040928100c14003030030580c01d49110741d151810030b0202807c81110100d014107801c83c95104032a100105680110102d07200c3d00c06080109107048580d504200d03084100143c40b5000381d4110b40701442141c03021b00c13240f080e0441c0d07441c018140d2408100410344640c0108103802080000380713800300f00301c01d541000440110703e8103c0d50502d80c001e4040c640210b107901c00300d6003c2c000050701c0c5a682000310355102041e8040c03c5a00c0442c002210280c40c07014070781d410204001644c5103050351148030312a0f03000f4032550400c1103401c00b04c00206070540b400008262206078a156650b003c000380d9a0100c00520f0502419082000340900c4c1d001e076100080c43c12201451030030a9079075503000300301c00a8810140b04000b0080c604000c158100741c404d242d001c0c0c0055220464002d11806003107005050329001802003c1b82039441c0e04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 83528238 1250 83526988 83527013
    0x13e07030302070804030f0302100e1207030825120516050f030901110307030605030712020a0303080903040902280314070e010302310603060f0e0405030904050a060f0f080a 76
    0x12402c0c0000c001c003100140d600e42c0105100c43c082d174014014841b40050610480d2610bea08500c00d031320015103642d42c421420b00300d842c100c1d81490010703401d4941940302000364904d05912040e400c0501d00511080d0b60100c01240c1071812401c0034085500c0e60a25005c520000101d00d034001182000305040c1840048011138011075150700006d100385868500f03043c941c101391106800a502c40d00c041009260800111005e0010250620309400761341e40040c14a848911004007480640750001c1d100340d000340103480c01400d4110742555510310b401c05007042d0641c100c0d041c104251080480b6064944240708a0300c0c0b00080c0d030300a540b107449100080e258184100b650504044d02000428180b2000b07416034440606800981c28694602c0f403101c07442c00342c8680041c410980741c0001005403009800c00c0c00c00300e41142c0d003005e24507192800c049007540704d00c80c02c1e00d80041c01e010501c5a0341e1f20380d40c0001c0c2103405543d900c036406501c41d40381c0e01260030305110300c0d44554040903040000c14299110706 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 83529488 1250 83528238 83528243
    0x307030e0d05060f0901060f081c090806040302160602010b0a140a030c030b01030308070c0302151504091a0603010e030d0b010306050a06020c0102010545013e0703030207 75
    0x49044800315520b803880c00400b242c4041c101e032084814480840c0c001d000d68030280c402114410340040c101a501c6544004540c0100d03405100310b9071501141740504001d50250281d0401c5d2040e40c581407e02079070b58001841d600009040d0710034000740c0544184129010703084014414544545000d600780503000810460a03031101d10010000002100384c1ca08a0065104081268856156080c003a201c6c100060031807003449100800440025804107412022000e115034524094490800000c0d032900030b03565480d00103281401610070f12050002450303a92501724040314107660381e54140760994204d4101d60700140d00600c141d220b21b050300e03040880b4055043c900069080d07500d40000c0c203000c17160361107880035070000c22401c01c40b96828041d013544030054118100403070516042c0c90a61b0001050300d507002c441e800b281102e030007243c4481e000c4000b09180c002d011003810b00c802c481c0112034000e03010f0f00c003114000b522280424807016426040d180e2880d401c1c00c120854400f900a503200d04801c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 83530738 1250 83529488 83529499
    0xd050d0f020f01020c100501060528020c04141005060f040b0315030a03090603061e0b031306020310081606050f0307020313090c2d030b03010e010606111e0307030e 72
    0x20b0551102440940fa401c062440109056244144480b04a91040e0411b0003000020803030b85080400c0340c5110f100c13046207032498a07118981c140c800c078104010210380e43da01c00c3c105400010700741e90509216000320095070001e8240e0741d42d50b081004a06c01d882c1e0341c450307054041c8010080d82211070040d69020020700c400d810340b420701c1c90001e410212034020440108208400500859a161145001400907002c3e400c07000e00b41c0e018095007240007403040c0140c080c80000001c009941104003148042c0c2d02140c107644a040c50a4540b4064125016134032107803007200d02200340040402141c004441c1241c68082c500300114004d80c0e896800180000c0c2984420040050201c40074800d0340d00400d070410000407089518031005154424030b003c001c42174041c1069048080100810000625146040004440301d030729000c24050103546044d274105518025001448503080f08a00111010020548102043c000d494842e18480306042c450141c2c0280700d60340000780143c00d0040310002c000d08 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 83531988 1250 83530738 83530753
    0x627051f020c0306010303020d1101060f0b0315130606030b220b031c0f030f1a0603060f060304060207060b061602010f03060e090703050c010309020f062101030f020f0d050d0f02 78
    0x860b141c10806e900460042c0e00c8540304060540d40320060309040d6281d10b0003448017906e4096001c603101e9440c040c14503682000004959100c80c11000c2ca5035002002d46400480141084c2c540001c11880c814036000c00d00305070f084a070707a00d010a000d0765408200f10064114240318610503008100342088980c041c46126082480b1891001d040c2e101c5000b195280385040e141707204000c1c00d46065010500046042840300354500e9410368003003a5214040d104181c0784c0ea04c0c18000394072080c29001c550740081c0e001044c401400016002048007038091107040c00102074001c144044c40c860900032a1440340e40030503141c0198401e0303204081100c0f4924020402d00d8948004417034803602500e5928161b40b104d88200100041808554410442400d04000c0c4000c0d07a00802e1445148525582c41007100107554868181c00e01c0034200c030500000f2401e4895a102d191900e1282250401030b840f525400003100f00a241c40002c0b80c40c4070ba403000281c06400a0740c0800c1e0b85503081c8240711400d6000b11403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 83533238 1250 83531988 83532013
    0x1b05031209010c0306051203030a11190903060c080c0a0806010c020a08160b0f0d05060a0e04030c15020a0507020409030207081b0a0801020903030703050705160627051f02 75
    0x1900e034040d14000000203030030801c0340000360480c0c2030360f8071142c080d1030412412074900d10040f081d2a0b100000c10b601044048032522280154492462900b00500c54004070b41e070304943c05080700e0141d030310603201008a0742a00d501500c840200b165142c121510820030140140d00c662800c5412080604000d100200e881c2d002541e801c1064200034410752001004604a14a07030700f4900050400721072031031500b1505509005c1c00d100c3c40168039042e0342c90380d0208459889048500000b0102071a01c6030341803c1626000740f20344c4503124256240300c280d850440307030403481c0c3c0300300c50ba0b181003922543c1c9086500d5003804050000d0b030300e050307055004105000414080901442500340d680c41041140c0710600010481200c042e03402802040e841440500702c1ca4800004071884107415050940e101e0b1000d00c2e004d4940106140d40e6031074620700110014902e90480310091b294241c0301d0b01800810300031214404c86c00c01a2140329441170001d901200c0701204082044c082215500c1506c2a0f100000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 83534488 1250 83533238 83533267
    0x6020a051501210512040315140708060d020a03050609160609060e100c060603050f10050906040b0414031201050f03060403080106110c09040f051c051207121a010912031b0503 77
    0x680c408c0d110341c0642c00380f22460340710b14851504960284500310407207007041907005144841c001c14480c00351179070100c04010b40d42c55091120003107078041e04507481803130540315003919182d1014540261010106020130200e0041e003500c401da0ba680c0ea44c2c0d80c0a28004000c1120400007420300f502400f040c0c0c0c02e0440421400e0049001450140300102002e616001c0764914000c00303001ca80c22050b1500b81480550f0202240e40d68010b030300100761a0880d141c90920f8858001c90091035801840005100103480c0004004a41201c500b01e82c01001507501c3c0c802d0646641044a0050001c1d03101300061041c14015540401d04510141c202c0b800304d04e0600218806020903076081c2c850b00d0780346866404100e02085002452a94105142610402c3d4100031300325000740c100070000b03c00340c1c1001911462096100c0080300303140250178080a07000d403050460381d451010906000550442000c29a01c6041000c500e03000d51650703501548008503610044280700082c8102c41e50b010800c4620000c0c20381 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 83535738 1250 83534488 83534497
    0x12140705070806060d0c1701270506100312030509011116060b03010606053705070203010e060114130213060819090201120b04090b0106020a051501210512 68
    0x540c008184160600380c26074036184005010380d1140c2c1401482c4000608000001d101300d440c85002402e424a0014101c0c0c09840d82c81c0302000c020b039400c1c0d449200c1550303d400311000d4900860540e80c4a444040c41400c10050790300010b44040e0f10400352070300c03081c4030750320280d8071070b4a65000145001f00c8100c80e2241e9444070300303101c04c45482c0351414800d0008038820481c011004030000c00c1160302d40719001d0968043c0b0107082c000008020b9161145545c030b03942400310680784030b01d402c800d082c0280020303029400c4940709a0107980707804010b40c149100050624103891000817460005015101000000d40c50000c1c031101280d000c1c0100c4080028240c0c80c0350142031640c4840d01940f4242c10700705c00b0300a503404251501824461440d0141c0d030490000384481c622307410701141c21200c00700490090600c050b4010403681c1c1d03582c00000c0c1c1c290f000c1000d111461044045d140a07006c0c2c05503d1902007828006d0f0341114241c03020903007030205c060968000444c4243c0982c0c0e120154151500105c1e040f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 83536988 1250 83535738 83535743
    0x80720031201090e1f0908030a09120c030207120f0506070503040201020d09120206030915070203090a06030b03060c03091513020f06070f02040b24071103030a020a121407 75
    0x81004000091200745280c00351002003001c00c04040c82c010441ea4418459151640c0d503000039a003503600c02001e030041e6080a80203600a5074034100f141c00100208a101810b407001024001843e214a10403070001d42ca03260141c0c010401c2c2820710a5a44882d150780c14200c815240308122035000803824081d42e4401c2440f611950b40300d240070300029082440a005020401c040f2010034000501d80d0710103190005c0c1c058500c50303203a0303543c4c1302840c1c900070190f40b611014034103400400070031540c00001080c1a0909070746a50ba01c6664500c02e405944d8480603d81d4144c0200b40015000e000c3e80000e954494480801c0f80e0800310660449201e03800e0a40e848008216914050419804c1604d143c1814044c1500c885103014002c1c0c03280516506060002440343d0380721032400134555658140e45284681d00300342c0c101e040c1900c500c034400c43c0e80010000c407042e6505039001c0b6602e1501000307403014140d460300640002c440e06d54a8080e0340b640882082c1c10711881c03440c2c038178010030844040c0519a2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 83538238 1250 83536988 83536993
    0x6040e0a0c031a010608131e0b0103200307050d02040204030f030203120f012105070906060305060907020102040503122b0203070905030105010b2d0c0d0905100807080720 75
    0x40c00c0d801c0000f0416004a1410484492580104481d0f030b48951503640c030080700441c2c1c0040c0c00d014908400e2442c0c01039000b14103a445050081e01788102307024210b040b64464841c0003080754004140404855000c01e0f041c0e415007100d00100311a051110407400c940d48004e100603d05612980d4840101120020540050f480458804082844486003d41240c42240003038010f42c034000311241c030070000440c00659520714660103800c01070208a10005004500d00501c96184c403034500400070041228101c0c4902c0403d00072030034160062003240d043d218090302801210194000b042c17402c7d40002c01c08900c22800280c52440c9115005022009002c080d5000da903070b0030071100041c48a125a00f20500ca645083c3c010007011690200702c0380343c08080310300c100448440091005480411384603844800380002007822440c8004200b0700140030b45512251002c40d201c500f070190046810000300045203041c0c1c00306070140d02500d41c6950059a52400b0700c50100248482003074044015803c10056 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 83539488 1250 83538238 83538263
    0x17090603010f08190f02010c0201021507050d06050607030801050105030c09062106030105060604150908030a0903030807020a0c21020409050616021507080c130e060a090e070e06040e0a 81
    0x1007506101881130059600303500304040c0d00c0740e01c03414420202c0a0009050100c41c00100c000c690003403058940701480c5520000d0189400380000c1d00c1940046179800a80d80341c60700201351f0380740a030300b03462200750199100c8005a0030800150340f42c0e4000361014250000502a8010b150f039240002c191611a00040c040d0300c0082c0b207901c03607541c00080e00c298403d0341001d0400010341c4880701030740e0440702c201c40000c50984140300141c0300701035a030b000b07031000c0c3c040041c80d42650313504402641c0032680300703684c2c65a0755034a41504a0301e500c14000c00030721040e0050700030003092030311841102d8000e250341190f82c0e10703403480d0340058101d0f9030a00007224180c2000041103007912010207202c0c41140a030014050b0000e21801150f04404020203903000e000030000030400004242044c1c400000003a951440c6040d00ca00200304480c0c411a400e51280e0712552020981c201c00e0300803100d010707000d14000d007603890411145241c22500107112a4000c0d83d2045007a00341c060401c40f01c1d002e2406450b015504 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 83540738 1250 83539488 83539499
    0x1e070b15010306050301090314030a020403060e0303061017010501030903210905120901020c090907050303030709030501050705090d030c2f10030b0a060f02030702090103060c11011817090603010f 86
    0x54540136070282d4880d91509581d6004260001e4182c90024290810241e50350340d8003804900034010f0381c002803d210714200200c207508070000b0046000c0c4400712000c00724144d02c003800700c40001101ca4a1075220041100401c1654000c0c0c0142e0400d5100f420080e4070001c4124400000ac004507040c44110f507250005802488014890030654002140c0c10614010805002035981d842802e001801502c642c00010081c00c400d200520192400030181e95403803d000c400103011001c5030006a80030351030b1401165049010700100c40317011001400c00301d694a1941c038283c07100004c01d4020794202e02d02d90100d24510350480340f112000c2441880350100d8206010500ca148040c886540b41894680000c0000aa8030303030f13214000321051450f11500e03112810504034114010300000035001014000040200001c40c0c110b1410715440d60745040c4c0100b01c0100d194283c0d03503e40c030141d4a01e2200c1e440e500202f2020860000004c1280e03a102d85088000030102d012640700343c1c01000c203105000b006104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 83541988 1250 83540738 83540741
    0xf0c020309010e03010b24190807020c0a050f10020705060406030618061a030705090d080a0314061509120f0a0201080f1009050a09060c021f111e070b150103 69
    0x510303804d070000c0010600c0a030126412003250701001d081701513504c032a50301010300142210075400c0b0454500b00810240358000e8000b07107083d24410054021030b600c1c940503003004070648081f03a100074000c0b449030a03598180551044c0300c801c4041140a80354000c07459480e418000e000901480e03400142280c0f8044000d02070940341d103030031031186003040010000c14006440002030003a03032150b80e036a05d8031084400d407840d10801c12515003102540c3c01c01c2060110b400c01610150745291000e00140090f00d80a8058940031255158400d0503220000d030417003c01e60180c00d42e010040e04148010b0300d0701310031510782a81450f82946d02d90041101c64119640005000d8005030010034591032410983c00c15a0b48259074014020502c2d40ca00000e800c0342d0700c5400075229550400f500b0000d103000e10100030b460f00034a110149082c01e215480804806052203008806040c04281505021040141d13481c42d02d40c3c1240b031003810800b884488082003d0a900c5402108a80411400d46109100150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 83543238 1250 83541988 83542007
    0x3110d050c06010302010e011e03050406050105041b0503150a0312030c08040510020307050706020c0610150503150321090f041103060904020112140118060503150405010f0c02030901 80
    0x90811005001082120354001009410f41e9030900340440000081d80048030200f0007421004909218142c2d07200134039030590300050285010324002d200d0750b0b898101380802c0c0c03040c620b010100c0f510902c1c098080c462151010b0340d08000001015001c1003001d6000030040d0009400c203551054003140c11100680d094440d0301c0c284007150408209514180e11486d880d003c181206442041c0c00000044d0040d200b03004a40340c3c282d000304215124615855000d0352090704581c4040c44051080700071980161000c00d0741c052076415505c15285070b40b080700800d03900000903c00b5800d4400c01c2c17400610950210000884a0004802251260710100c10041a40b5040d51950300942c0382403502d0101c07040c10704c201c940c4035405a406001715180c034801296418406201610850702e03000c0d01c844049007034072529049507460900340c0703006179020301d1800840304c942c40f51940c1540020198004180c1080659074018010000050682d00310480c41040d9071891950000503080010150301070360b0820f0051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 83544488 1250 83543238 83543263
    0x1201060801020c0c0906060a030f0f0e0a110406050d060b0a051512061f030c0c0219030b010e060a150c020603040b010503061003050303150a17010902120105090d08060607020d0311 79
    0x9040e18202580420690300c161200e54080680b180c60301e8080c50038179041070001c04800282005215461400715488007503a90007140d1650304ec684100d59444c0c10f000340000d540c0010029615600c0d5952030b10024a05c40800035007000c40c28100240035520000420140001c03c072180d07a403841c02003c0a240007600400d124032800340b1001c400c1c1b080480c0745840401040724100020120304189055074181c9108100075400034655040100e403ca1350301d521401c8038412400002d00da601c2c2c50541844080031550590400e046000402140300c070304102043c0b0b104c071800d010b0708168036500403540651084801744c4200004100400c0035003820024240c1c040d02810000e0030440c103681d10140c41c1c1c0306c040c20500304170030184214292642d40d42e480d0307801032060b550f420f400107290241082c041d10103000e05034440d0491801c641041c02060007150b02c02d5082d040500a8007030291000d680400014003507640091051040800503240c030203100e40000c3c0203407541001951501c040074680000d0b4181c0303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 83545738 1250 83544488 83544499
    0x10090302032b05160201030504050c09011818051b0612010b070c0e040c0303030c0504050409050f012f0703090b0c010f05070c020312030a0e0615030d0c0519021201060801020c0c 78
    0x901d039a040c13a003031118100d6130918010403541c807241002460724054955981e4480c0c40b08000140034050b01d03444010b800540d080c03d202070011034201c0803aa000070500034009803c0142142825803005200d9402c06c1c00c020005820203c800e08100d51383c40098001c0c0302e000e4400280c020502c03c03d0080080100801c4609103814946540c44845000c003500c0020180b40c1c9491550350268058804d5402178880600104046002424082c0c6d5401c0e40d807046070b029500e0800070144041c0250000c08410364662070200e070100340c40d098bc4010364800715081d0100085444007203102d002d540000d080c4001c2c40000403441c200e40e2901c850407140d018125005100e1000425001030303c0220703009215014003080380d07480e0f41d1196003110240582058a02140c001c13102041103141188044840c0c1e400280c1c1140c049120022040d101c802c11888080c000c1ea0041c0d40d601e041490a403500380480c1d1000c1c0c014801e010b04800e102d800c0d1040c0340c02c03412a0365008200881c502604000444052004450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 83546988 1250 83545738 83545747
    0xd05060f01120b1f120e190b0a020702060a0804030305060105041206020903010e06010303020d02071d06100e0303030a0c121404030c0311070e0105181510090302032b05 74
    0x20384860105030b00708070304640f6820807110a540c0c0040f446080b000f00403000240303401e41c11008014440c1452648021440c0c400c070050800340002c1d40020030f4214040041c0190307515120a80e07039440040c6080107194003000b1b9800141c41f5000a008413014540718041d15090601c0d018041e6440100100d0410105200802608440b015a041c0082c0c00c0200141d1300c01000021a014103100f4924044610510380000704041d400584c03828810220b9003a0780400b43c8920f02c03480840e03204c0c5880c001a1060742c020600d00d281c0042190007251a40c10b00004680340b100209055800c110350700014281d80340741108400360000412035003034180200c10810309011201d01185444041c2001d8104440c204444007018091140c1c11540b00c50103080740c502ca03580e07050300081340809000d03450155090b84006030203600d1200c080340c0034102c4204203029041c2050b06000000085100940801824a000001503281484540d0315881106080811010703007a0000610311000e034003080400c0300812 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 83548238 1250 83546988 83547019
    0x30815040510050411070c080a020a0e06030309090c0d090c050f0f06070803040318080604020f180601110304170d030b0108040b04030315090f0507020d0c082a03040b0d0506 76
    0x2c040006485080f5400207015034280308000003801412001032210200303400109490000244480c00103100b10b4a0380001521100c05e49807452040e500b1a0b00341e403040c032900e0f880c5e01e07001e003940340d0110400d850542840401107200040c1c90008009407415842ea48043c8003a0400d0000c500080b0815120344d03021091180200c1c6540c45200401383c038140c4040007103800c241c4981c0c040b4401001400004240986440d616500d65400781c0b01244900041d210075080c2e401c0240003030b0072080c8100511584d503560000150b4020400c100e002034140001c0102154030448041200038441403c0c0c01003090184158018044640748038145041c402143c0c01c010008480744503140d030051307152030081010040c110300d50044464a810071009681802540181001107520062103104c450b0b080b07410034000c0301c5040e10041d144060103130105104000c1c4504406c3d48903c010403207100d4410a204034a18086103500f150000c0e007042102031000165407911a44030b004403504880704a40c0c2c01281c41034031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 83549488 1250 83548238 83548261
    0xe030f040b0307200f011a091504021303030c050d03090c1e03060504030305041a0106020703030305040206090306041b09020901120c0210060902120c0a0c26070308150405 75
    0x1d00c20041c1500c1d00000085025214014a00000c04610ba1140407001007503c0c0c3da441d0060600304c118598030700014200c0c0ca801c0829960310310f0401411100c607640700e450b55040c400d841c40602c203401603000c00c480c0c604100501441d40c001c50296a070f01d110904145002e41c00d05550846c0041098200418503012a5021402c4011140b8081c6004400054a1402c411401a40d4400b6120514190401041c15056001103100b64801d04250142c0c42c3c00601c0d00782041001c0c09031030010380c000401840024000d60010341c0082c002010710303042c1041800060b2402c401214102e41001e0b503031500f001e40ca00e40b011280050034216070198244501c0c000000d00518001b5442054251100d8040e2a81d6000340301e800b0007108445002d01410307071201c06940c0a5030001020340c1d0f048d08850002808210141d0907a04031801d250342c1c044220504da21007a075048021101218030900200d0030307100d0f020010000340009071185d00e8058503458a80c102c00f06a4202e12300480c06a8242810400e454100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 83550738 1250 83549488 83549497
    0x1111204150f1a0307080d030b040b100c150c0c020d03170f010501020d090b16170a080f1f092408010f0506100804120309020301150602010e030f 64
    0x85141810059039241055881c20407401d000040341440e007a580d9a03402c18035009000034414415140c04924044014140e40705160710814501e6000410019141c91098019500010300180b000c90011480b000103031044a005103040701003140840c031078042100d162002c076a9048006000c21850080e0320000e03201d0280100c0c0280b09941483c0c0c85801c0500402540d05c207115071900c42c11451429100c810b041e0340c020f014050151003981403003070456101da038000c0180ea1641c001c0f00d04118203118444e6211003000030890381c80503045c04400119040e08003400486034a55110758250404001000300740c03c01402464400020442e0b08070070f400d02500354001c4510719480019080610600041c019034004142407103007a4119000a80c0030301500020007052000304200301c6501c80c9000c002c1c0c2035044056000c0072460840000b004251000305a0303120050606010a02100e1a400a801c4031000d001c40c00300c4500051040c8603040d42480f030f491641d0400001180f0b80b009420384d0900b50b00a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 83551988 1250 83550738 83550757
    0x605040e0609060409320706050d020703031103090703260a0c030e19030506090f060a0207050304030f0b04110a12020d0611041205010b0609010504060f09030813090b030111 76
    0x81407008a0056102c0745c1c8071800c1546c202c4807403803801c480c1c007546114074460b0340c00c6500303095008030700e41c055854040b50010450302d0544819217860302d07a800c4078000c2d4005100640605980e00794185101500781c0003944500c0c00c500103081202e0661034480d81038403020756038030b1804003401044899203000b00129502c1900b2802c00902ea02020300d806c0301c900021885081d00151001d18200c088680002a2015170b44120251406641c4204025990313070000301400407a584500c000c241200b000341e00405040b8001d034107030780c40c0c5612a201e0107092221110202c540c45012420841800220800c1e0034452600301c401c1c90b113007884d2146d0b030082003101c0d00c0040d11401a451102c02004950790001c0c048030b03030f241280b9407900c0c1d440b4143c01a4140341c3d48c081c1e0307565084c26210005883e06204491f44940140c5401c1e08003810010b0448404d030040140105008041304d006c400300f8500b9010303140701a1040304121005003007000b92816902e030010424046d80c10725020307044004003d01034500040b03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 83553238 1250 83551988 83551999
    0x2100608030406121a04060902070201020c060a0206040201052d0910020a02010806120703020d05150703060308040605030702010e0109080a02070e01030b01050f010c1713060c030c150204030c0b090a0605040e06 92
    0x49185e468001d1120188031294018940180007034a248160090144503000341c0a4602010380c0b502800264440d001d003a00c0140c011000050066000c5c20140c145807207280960640f5140500c401c048006121101c8011030a0204810203d03150030791110000711500d202070140103540340c0c00a05000c0c80501031a10442d9090450703d20080c04001002c01541c006010040c2040c4a0a0480d00c4000c10700742c4c40d0065404034009884940070b80524411650320640712842c0600e000f40c202c8580d040903004000719501d0304901d0640074004d01401706104d004501c100c0e03030350342074101c041d19014103640301000c45025040104003085c0e01e25609411918180c503a40bc992004000490316190b60f000700600d102041c0e11a803900e003580002400b030035a1185a484e01c40c9483c0e490986580c03c000c20020000b44904806a0003e680c41d20100514048490007608290f2281c5d2960508420380d0800d2400c070001003900324861800d1002c2100804841c00c1031481d10f030a00c50000d4207514018427040c0141d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 83554488 1250 83553238 83553251
    0x1090506030a0512040303180b0403110d06090309090516080c0702010201180c080d0c02030a0224040306050f07030501060f080907050d150501050616061d030a0210060803040612 78
    0xd0310103000042d80c0d40d91040a4505080719111041d405803c00e00098000075402c1c40d134a181d200301240d400080d519024020390a041c61a901c020320502004405500000d110b520b440c006495801103030074031482902d402d040c03542170015000031218014501c2e184240c07110071001007541c0069440f500301110032030150b0b81d103001e0b00040c2e01416207211607003a10807000c80788500f070003170403090300d400c0e0351441041da2403030310320a0b40489180012100c080d50540001d00a00010301d041203c02a045031807a02408040b18030340b000002d25046a88251034007603d0350700b001404c100608165500c515641010842c070b504088005004c03182c180403103001c0c0410302c4041405050204001d50080070010710345041c4100e036184c200c0d00c40c62a01880010a030500740085a80d01c1d190083c0d8a0058412030a404580340320b4407028090103000d030042607054403800049481c4e00090005002c0606076400800308003180f440c503c4111941681b0069070340d00240070a115480e4070114403002c1c040c5d40c00c40802e10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 83555738 1250 83554488 83554501
    0x506010e0d050312070503011802040b1804090501021c06050301200f0d051005030c09040b1b07060507020f06010b030103080a2a0b070e01050c06010504110f030109090b1e010905 78
    0x3c52040b4000250f444440ca42005941c0b5031050055058074607030101e2203550001c2c0207684c4203a00480c019049840c00c02d001d21101d03c400d204c40c01043d524000c00c0414440303c0c9440c2c07242241d01080810f000c2d0000c81c404051100c58038040c6000810003940204000441c010403251030040180078600c00d8640001c19504d1a0a20000e81d000d40403054410031032800c02c2d89214010004503c60240240280c5a02000c903240030180f09200c0c64014480411660702d40d121036003103101755100648550010b100e40d41c041102403150a1044e1440d1b0000c1810307010b000065032030000c0c164052482d4031010001400000c2ca85415213a2000003030420040202440040040d41780a0040300034a4816401d64903044c80004016680248800c0d101c148840d4003e01c011107281c42588080020355000100400650809034400300013030360031900d00d6042c900724405200484d0b01c01e03803003014407175220001e80f000e100103036250680001d08045140b41c004100041820100c0341442000400c0d65248001100e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 83556988 1250 83555738 83555743
    0x3070f060b210309040501080102031603110d0f0204050306012c06180a090b060102120403020d020301021b0a0c0501030902010e150d061d090106080304030609030c1403090f040506010e0d05 83
    0x5003103510015102d0860300d500d0143c0c0d075084900041e208500b49000040d19140601c03c990042102801d02c41d0740b0343c98800242c010708801012900c3e070f444d04002c403d10007600380c8620f06d00201103440140e5214949405c00d8900074068222051590007808081e00030132902001510150b02501c1c05030092751403400058191070241c070320316224a480020444013201ca6407010b01c2052182c40c4014280c1c840500481e90703204900c9010800001c10002803001d03107481c460011041e8030003400540b80007901ca8000c481d20b00c0ca00c0c02186141c0c01903201e0b10401c40c2c0280404040e0a0a20301040452020740000b0300d100c4a80003e14007e807083d60312022100d40001c22100c3c0d96841f10310601005a94682c1c68081e140706a41111550100402085d0780d41c030107002d524201e90000e030040d0306050840d147d100040282001c1201401074514241000419801c44460811498005540c403200284280301101003803807040340c130603482c0104100b101ea81102c5d851140b6001602c01c00c50b001784502c0d040d0f1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 83558238 1250 83556988 83557009
    0x90b030c090411210a03181202090903040801020a0c030f0201050609040807030e040e0705150a020a03050a1e09080606010e030d030b0d1506050a090204030305270406030615050303070f060b 83
    0x101c2c130254a0512401ca080000d014060758480c2d0344810180c3d100309480941c10704180681d800d4070203010050b0000d403402c5412140c2154a4500303413850b00e030b90390003800d0882e8000704041001c5400a040c020a05400a42004941100340002e0103d8600080014020b6800030001002c01c080072448205141c85480b1000240e007011f04100194980300009a6480955201d01403141074100d03001d01040d03002000740e03510b140140d001002d4007403032a50190351a41161a0304410003103a0090303640702c80510030f840d80340580142c6806501c1d5040a4102e41060001003201341404040722803e500741e20000707410111050030f441c002504c4081e01d00003c5043d0314144025240d2001820342080e04c40e0282d105100700c44040b00d049110a0740d8442d200141d006034030000c7c01044d002e110000301481603551440c0600f01d07800070300003034118800019007129200c0c0c000303542c20381e5101e800102100002c41104003500c011401981001c0660380d0b00c0043c0d01c03181c5c1e0b00412030740d20707a141980c00d5203810031b044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 83559488 1250 83558238 83558269
    0x609040f0b0a090b1309081b1c05040905071805010513050402121e04150c05040509040c08011104051311040f0e04060b0609180714040f090b030c090411 67
    0x4400700ea6440c0c00b4040a01350400c9518411301c200d05810600100610880c203180e0340c021307142d034244011490100316507904584509a41d008840300707419000d6019020a140d044181c031100d443c0ca0a088140044070001810802440603440e001001998134120040403142c0911748580d807540320304107074031600d8410b910640e00b150022904054141140803000d1160504602303c0c501d056240c45d01000481c801e581c06070820f9002c40c040d85082d20203420449a8801600f044d038036040d40c0314081000014215000d0314000d600240500400c0002c0c05415001c602524400703003440d0801c00001e191480040721804566902d058040b01140c2d00001d550041c104107280441c256501c4c0c41c900c070800030448007260101d2400c0d02a405a03e004000d603040460050680d4502c944070456a40c48040c002d0001d04c2807080d0310070711482d0590040c0051018014046d0800c02c0980382c00c1c074103416607a00b0640c4900c0f03a04000c3c6090b003e62121818180d215411005da8104241e007040451480415072a00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 83560738 1250 83559488 83559499
    0x1009050316050f030304030201140c28030e06030601120b0301060b0c03030f0c1207050c0f0106080c01020f060106021f150303051c0605010806010f020106080f0c090108010b0609040f0b 81
    0x7070501d403029840c08804a80040d01c0c0100307080f900000b090345a101701c1c00001e000c501c00c10215540050700001a00501d1040e000329050b40611204600298414081160b0f01008592001c820554443d400300d00c04501540d13504e0850a00000203000c8070faa961040f00c500c0d42d5982c1548680c0e4094210000a004503000c0994407422603800507285d038002c6030401d60007100440420469680710040301e10300000c00903d25010b0700c840c43c1c00c07202e552108641ca2204d100b81d850b4481c274500d00781300e101c0c01000c0d0240200582c4219000190501b0160805403103aa005540100720080c1c020a05243c0894440304014a00382103004c40801030642300080b6403880c0202c10040700b05508500200b4851030160707400c0e03001d9080e001c0108190b400b240126070002e07c01c18041000c0b54020000c00d1110841d500000c1892900c80c90500d1400c0c40d098104503250b80308501c030100904211095a02506820009102c0c080d101c0e03010030050301c10007441e10302580e503404ca0684902e600d40d20048070444000c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 83561988 1250 83560738 83560753
    0x3030a0507170c250303020705040f0f0e030a02070b0c06011a07060203040b1902070c030b0c22060822150608060702010504030201110705070902030a090c060314011401020c10090503 80
    0x4540d0307400041208040d42e00405a010b8404d820b12141400f00c1e5416402000207500301001e0202500b40224038880d003540320141062591842e0081030b009280c0704c1c4c006c503103c25140d6802403415000f070307020140e804410004072440c10000300d0141d0554400c020802c450a28040d000d12a6200300f07000500014404401d1004002800c269540100345c4c020455104001a0300380408070b02c1980f40003000a2a1420304100244d45880c0b2140e2200c40c1501007410240201c40404024450351034014920700e204c0024802c1c2074100001c02d0b0842c2862444410100145c01a406c40c00740030327540a4480700c1c40c828a12080646500010003502c00b100c140e950b103040820b0007070302802d400d860072005542461484250103c0e40400d075500150828010402e040c070740355070200203500c05400e1842d1103072102082c2001c80c00319000d0750003c108039500014911910700c40d04901101c1a04103150942d0b4200c0c1d03440b8103071380c0020181d452080c120740d6841141c010f2401547c5510403a44860307058090b0780c0d0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 83563238 1250 83561988 83562007
    0xa120305070206060a0806150609030d030b09071e110309060417060f071d040e010603030c060e03070b010e0a060801150501090e0f190b04020708030411090603030a050717 75
    0x8020500441d501d40890b1110f480da03030204441c901c0140944851941310100152030440e801e21014203260014020914150700d10001c00d0806c0318594103600480c0e00d03010443c45a00300790500c2c45c0c0c03094441c600321001600c180b5078003503124000d134500002c0049048032401001c8040c02101d8841ea002484161b0310781d542c0c440c002200f103468000240d103009220004907242c8801901e18862001940d50081c4609800800321101d203402c4001c50f001a500c10741c042c00c0e00d0b000d110f41405107002c0e0312200311401e801d14060083c1e41805030588026002840841d0025034881d104905440ca03081c1070380850fa40303031042d00700140540d0703021382c0c01582410801c5486107545000a42591002e030303a000d94180c0ca60701101140f12064440c0240200804006192120450100000f04010000114403242c0010014050341c010300c40503103100100100744800c2020400107107280070402e8510003242c0c13401d03a0010740c41c1e025200b0140140302c6c00013281410001000c0030440c504204030142a103904411 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 83564488 1250 83563238 83563241
    0x2805060f0a11031c051801050c0a0f020c030604140f0a030c030c0f05060a021b01060e070f0203070c0f050a090e070308031f120b060a0b0d200d0b0f0d03050f09030a1203 74
    0x581e40c211906d1190309032032002c0314041c00b07036612170308504030301d94a270401e84201251900d99105040c0308500800003818a195014000140079602480e807a154030014031801e0740c1058107070012125107a11826210002a13000300d4001d21458241c140820203505070704048008144c2544001c10707a0160300100201034a069006d440b801900c0050300c03d1050751803000078200c1c0d495003d1900215426070001e03825501c2a05070707051081c60341c0705881c2803811541d01d17980222059000050a802203a40c04d000134100402d9640c01414000c000f4402c100c44c141c40c80d5111a420b001c05400b0140000000b180388c000c1c0d2840303c240100b482184c60049640300300e910095540d460046031a51140c0780171a0720380c5065002c00c404d0b2032140002c113180c02d19401d21030000340900a081c1c003149050085c00c002c3c5e8096500502020701090101142c2212a40100460103c08240b4988212031301204000840d40c800142d60354450201c1120781e9800201e00000c1c50105401c4005080c00e881c1001380040d039526 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 83565738 1250 83564488 83564491
    0x160f0302061f081f0e0a0605010509070f050a030903180906030b130b07030b01030b09070c0b0c130303320c060a05160f030b2805060f0a11031c05 64
    0x810b80e540c00c0104040d0301802c42c0c45075500c9250300ca5400340c0340241c030080c01c1025610644241800c0002c00c50000100343e41000d01d581401d0782d000355668010440c81c144001e0b07456001c402d5103004544800100005440d900482102d4020955205d80280401d03001e0134104100f02500074070b510b584c6680e040d024014107103d000c2120510034a0780450f81d2040f110381c048085540c050a802032655400d001100100440c0c11a54105a01c89a8090240e103aa0413800e010f0382403640c031810030364000d0a1260000c0e4010f020106031010030019902403131041000e440035243d2501e48268054003041d80301d10031444c001034000c0c001c40003000401120880f00c008041d492541c1056a130310f641c4004090007101c80403210f581c2c00118907256210b0040c030424411074401000c0c103000409085210201d1080d12081420f081301818180032603c0b030001100c034481c0240022030391503180c50b644240c8512140205e03a069400e01908032010301c40c9580a01c1950340045400c0843d00e10700900c032881c2c4024020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 83566988 1250 83565738 83565751
    0x4061412010e070303140d140603060f010f061103040902040e040c0b09030304030f020612070315090e0d08040c0902070303020706110717030a0905030304050601050a120314160f030206 81
    0x210340c03040ca004000e040c01001e01c0b0100c10b1002c0d03e01c092a640b410758482105076101d12000c2c80410400562a07114801c1b401c10001c2c440c8001010f20f060300c01d241c0b506101810b00c900e402001e4004008180083c2d031680141c800300e180130624500c08a042c503240d8000c942240004500108000c04d1421100000901c941c1c01a503200700c03015900e15542c0d00501c0fa40c040c1a8040d08208418008908904407a000b050b03c098010f9103403804059181d8a070013401d42d200b40c0001d8582003110380c4403000c8540754000d04150001003017011440e00070707903036107030400c03102003080c49001400541880818041c00c8000e050810301990b940150386001402035100d030100b21040c3e1321b071100e200071034600c0b1300c00c2c2ea030700c180e02080351340d810141d0507802c414542005068001c0c182d00c40c0380d0100043d074180061401548900010f00c02941801c00700b00c6a0307c1c040c1c002e42c5070424190010001300707a200c8a992101d1100018080d5951107010004404c1d0815a401914030900f0040310750030980d000800d28032541 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 83568238 1250 83566988 83566999
    0x91a09070b030702070608060d060207030f030b0f0303090409060b030f0601030204060609180e330f040215070201020a210306080105010b0f0f040e010f0e07080c0a081302040614 78
    0xd8903000c0388200380c00b0545040380180e00801e4180720141c014214075030450401400036143c03094580d01c4500b030fa8171540080340001c1507100b40740e0030240c040c000c0b10304400040310125060422900400c0c0d8a00503c030b04d4610854907440703401c1c14088180e1080030703080c102800765480c0c0707402d0395441d5507038040a00c000c0307020303030314060f00050340a10611190b410355407540c2c00001c0f0b5a2203120140040c20100c040c400301da0082601900d4a0310002403400d00c0244820419100d00c1c103202031b540d150800013408a07032510208002c000c0140c0c1c5422007411940038100e102911a091800101c0c41c1c1018440c00506201103815208d403020031500141c00c0e02c6c4800d40d411300c8041d071101401801d0368401c0c842c40802030014000140803041c5007014041e0039504900003802c0c183e42da4114070001602b1781c400e101488004009000494205000d158048400e062020f15030420458450944c4115041c4900300302448000c240b101149401c4e0700c002c5600200144090341d01da02101c054080034003132803840741 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 83569488 1250 83568238 83568253
    0x60f060215011a070c08011d0c090606030721050112110103090b0703091103010203010902070c0602010c050d0f0902040e070f120512030603030c0703080717090a090f091a09 76
    0x1080d031110041c1a181c40c08180328210002215240b1a504410412182c0e64030117034001c14011824401c1015100410081c07105290980e4440d50920724442c0204e4051080d81c800c1040580f240e20417280c004200f0300d002c025002c400070340c120040801c040c84035070300f81c01c000c00010441f02e1170b101e40301c41702d01800403a02c41a400e100190300301c4583d2480207118054440019101d18001d07032001082501030081554054000c80001c1c2c22a80300342c0003074120350f03030200e02c05040c04100d50f041d901814460008000300710304070b00041c00c180100800c8002840d1200d0282581c080c041c0c010303000c1140c4c06817041c09080c99415000303494031413500516081450348080010340e02c52508009811a800202400312040f82e02054111548002d00350782d0148420014030010034002c00410000303500800099884c3e000360700d00200d92554080c0f21181c1881c0c1400103400960316031906004940e61290300140704074101c0083d2000d003801c818040e1220418001e00c803c8155180c144a106080d864240c8840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 83570738 1250 83569488 83569513
    0x7031509030e0402090a0e10060212040810020904020f030a0603050f010c0e040c020a02060d090c0e160309051002040b03090d0203030907031103070504020a0e011d0102100915060f0602 81
    0xc6481110000e4006120000712401c0780c02c0c01c2d4010091520040d00310070800e625100b01c0e418907042524092400145000d08000a5505000d00c180c21b0b50b8544406107054588507c9540c1c500101b44801c144560024036106140d41d140d048409084080c226591249881070617280209110f100c19509405a05c41c035040001d810702c94059085100c0d00c03107880c03c0c1800014440208002c0c00048154410844408003580c2d40c803002d0a0218031030316002c980074507140380003080e4001c039034800c0e88005540b00030b21010b504000d40f0001d000d012403900040303462403824540c1c94074142807000d941c0c00c1c0c0300140100340c455a0380001c52040c0b40203400c81e20442000c2c40100d0f500e210480354041e00303410101041c0009000e000c0500d080a0000b411100c009403500002822a4403030b10600c404076842c4814002a560001815480c0d450140500f00795001c00100117510b50843c6440c205019644201302c204001820720040000701c600c00c0c04114442e215640d482d01401103006401c0540314207000e5400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 83571988 1250 83570738 83570741
    0x3040e071808070f2606091b010309031403100b220803040f1503060b030f0402040e0607021c05190314100f0b070302030714071805010803180303040e0405070315 71
    0x2c440040c0c25044d802844c017018080d41010040303a10031000e4072854000301201c8100022806620484043c142c1d12450003202c2c0b4140d20b5a5164030306043c113081747d071004a80c114000410152000b02e8080d5030380e48204107022866080d400c0400191b2000c9850410085070b040c40303a1300f560030014011074040d01c510003550f03a03004030711405081002d5040c003070010b01c81d241c410b2494141c40b8240071944c00c1e01d40d00100301c13541040b104100da2804000030801540741900400c20f0240703001018209078201800003d4581205040c1108001e41540c6003000c80c501c1602181d0000000c080038182e00004480010060b000c04614654815000004035684142d00c9080008480b10b1200c01100c2c40e02d0417485075140d0700801c01c00d80039804248a6a03000c20010441e04080000000146c1142420401d58428881d50000100d0900e482e080c014450040000110343c00301d2006641030341d1901804001034518070594010740d0f500406c6000348400c0050000746c85050381e2003005800c0e4602045080f100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 83573238 1250 83571988 83572003
    0x5090414010b030a110c1207060f0c021002031803031f06020601080a030c08090603040b100801110d0b030a3302090f0906060f0a02031c150e0903040e071808 69
    0x64100030008a01540ba482d0b201c1110a81c00301102030805032003650403402c11f504041903011410700003d07070800f001360a202d2462031141d15070301084010b04601000303503580e80d0603050404007a07000002c603252001c000b481e12500082001140d03903a1520901300d807000140302c0b000c0c98000000d0080070480c47d0000c11564166513108004001c1e00ca00c07910115a1070800c00b13400d075203201081084c01816103d120082d842075001e400921103a042c520000900341c00150b00c00c0b03000f40d2500000c0b45100c800f281c00c44042a0410f24081907a404d4040000d003040c2e102c40009140c015100002c040001c801c0b94603020004031984001c106aa0640c051010380c4680d00c012503100c0d54000d0003060324038009102c2600101c02401e1581400e0034841590340c16440240f2060250380040340c1c1c16054186003004000d07110032000244400c140f0001501d80030151800748081210b0301000091120350204103440040000750710a0700c290a28110180c50040ba408844d00c0c01d0101e07503400300e50450b0005013407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 83574488 1250 83573238 83573249
    0xc060105100c0803070e040608030702011706010c060e0c040203041209060905060d0f1b1d0a050906060a0203160c05100f0f0f020102090a06030519060302090103080313050601060509041401 83
    0x14400100d056480b4120344c0d00040a9106120105000d17150545a51060320003400c811001903503280114000501075540d000c44203c03143c0045410410186d80c0061200c00c0341c0c3e40220003090b01e4164030b40042c02c1101c012000d80e00244080200414003040041b0a020700f44141c07116407205445050885050341c07580034858200000300a81103010409900036041c1c010544400500c19004c0014840d56812858414000605580d5409103850941c9076001c0d4230481254801691403401b0f01107002008001c00107841000d000c190944036900a00484034500303034402c429801301c0180c0c9485e5100f04140e01a5a000710000503841039014080c000c100205465a00d5044400361100000c40d160100c0c0d805080840d5024410001c0302d4550010a0300038207020740740400c0780d282804005003e42e1580e8800303a101c504080003040545c40d0001003a0650342c01014441d925a1002d0740380244d5809000e00030554440d44000054859114000d03101d155021181400990b0100c110076003004000e0007032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 83575738 1250 83574488 83574497
    0x305130f0b031602010b120f0f01050603070608040f15090308241c0b010f05040507051806030a0608060f0f070507020a0509060d120f030f05040b040201120b030703080c06010510 78
    0x1081003809001c3d0802004040c40c80007180090420303001c917071612000c102d40242c0ea4801540308d00d02010521920850305c102e0380c0204580c1c03402000181e40c4403814402c8a081c81903500c08074042c400c00100c0341c03881c0d54002c408402100ca9800d0810b00809004000768006134407400496048040300310705d83c44c1040c80200100c81550360740d00308800004558400864444003544a80010710710301e84042c024001a0000c144003841e21042c0010382d40010511410000d0404c0103030440c4050011100142e4001e84040351241d69801502c40208100e4201c025981b00719003c1201404071200081e1084001c0784100303929440c0c1d610141c400c0d02036200006e61201030301c4003d0140307060865490380c1c00f40000b0700004038920503454132284442450398000000d5000c0800c2c02407950903006041d00c0c04d40c8030700c0c20031691419403140c2c6069000500020b04020700e010b107100e00350509400295240c100101914003165880c64035045650208505543c00c0c01035400020b01858500b9924860f0385190b02c0c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 83576988 1250 83575738 83575741
    0x2090105030610120f020706051602060114041d01090c0504110a030509010f18110303070b06040b030c04110901080a06030f030507060228020f06010b0d0902040e06040305130f0b03 79
    0x2c0140003c1081d00c0d1100300204001043c0032103215025203503c01c0c0d10800e0050b5111540c2c1071010544900034007410416244000403892103900249141c111140c0140000003540c40c0c2c1c0c00a40548034017601003840e00940819040180010b512410702d0606c592464000c0e19030745c9040c0020360369082c0a580e108141844151034880c0030b42c00ca00d80c8200c0080001845443d4601c140e401c84040c00c000064406070f1000b1041040240c3e009011081d80c01c40040d030504c0810b42d65025641001485e0303500858540b50035840c207450420400924400c002c0c400e001d0041081c0c8044066002039215500196038400400d030468818840c0344107a0742c01810030300000705107840548640d800202c00721a41c550030041d07844440c0300f50341d41104040c070b00503000000b95051500280b90000c0e0403a1310802d50444030041182c15a8081211000071152202080702c03001800002c0c014400040c0042c031600461081008041e403200061520301011040048404d0b140e00b0404e900800c240150410f2460810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 83578238 1250 83576988 83577001
    0x711090708091c0e01030b0d0f06051905090d0f0203070507180b040b0a0317040f0906060305060105190f05040801060902091206090d03021303020d030206062d12011104060203040603050a0209010503 87
    0x407c106540320b4040c0c40114005c8180ea121400310201e4075054502c40c1d03599080c00724402c070b91490160070b00f030141010300050070f1170b0040b86d40740d070380c10132482041c0500d5080308403c0300d000b07209a178034003a00038040c1d904032560341316410f0962a08420707200d0b80d24541202c8081e1440e003441200b4134404050141a262411030b61501c0b8170500075004a40e00d104107010008034884130150600c090030490b2404142146460030190541e640502201d05108040c040d503881614180c0d141c40030f2600c1c521300310400b825040c0040e1201e100b5600304a21650074481d0209000902d60014480c0c15806d64204880e420003646040e101c0c80b003940e043c00d141c0c2200c150402d030303d44aa000380000c0004402129a80359403940090030610022808401603007040040011038076001083c4010708501c0700c0d20041c1c03990a2054845012010318103603100d034010301c4110302c41000075404038120004031321190782d5441e00d91002a40d030307412511070900001e0504001901c84074150080ea158120103031282c0d1f0540e00d411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 83579488 1250 83578238 83578241
    0x206090a050a1203021b030901021e06040201120f090f050706052104110a030f1502091302030c0d15080d09050609040b1801090207110f01080c0711090708091c0e0103 73
    0x480e420f0825801b841142400044000c91255020b004070003103603249880000039080c030701034690729500032050103c8101d40f14404210039500c1542481c0500c0d070729128807a144002c05940d03d441c0e40040c0b03020041000c0060003034403810440c0c01a000c54106907036800044607188210324608406401500c8143e14401d0010101c940041c422421066011013820101e000400f80c0d03070007500c4140001035041c003400710300c8500e0191000c52140c10f503d8581002e0119031007440600d01240d000c3d60003c0040e03000e112030800e480c0005440c610034441c0c02c06071580008094424041c0461a0088400c1c0103800c5d400f82c00d40408480d00a4030f030a0420001b64100002007004401044d04400f81e0041c2c5004640940c4415000c0c2061007401621010541001c0d800b148111001a00600912840f0021030307810070801680500c0300f0101a0b03032076460b849c001003001031200c40a42c00007506010f0041c641d80002412f489401e840040b0390324191320628600740000401c105c03502051521034441c1e8154443d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 83580738 1250 83579488 83579513
    0xe1506030304421e0801050d02010c050604060b091e040f080d0507030e0d020703080405060c0a080f0702040c02060708070f031104080d08010816050d03090b03090604030206090a050a 80
    0x5100e00c2c505a031105003102d000710f14800028a40020200d070051070302c40e00062420003103113044188440d04e012401d0301526445041c015503124284a4240b1b5003160301c6214192241c1c1e5204098800c03900380303032500001400d14051322030f02c5117010a000606c808040c26000c4407000708400c1c1c102d51501c0d00e803649040c03900e44000568100c10704000e42da00380ca0242c0655802040d0f19a400110001d0040405007041d06102d594411504029001c0010407054800d443c141c5504503102951859400b40140ca004001d0800030402c2d440840d62106225600d4041d043c214001e480910090220700c80c200d03141c41048030900c002c2040d04010488a900c9041281d1405030f8600300000e80c06450480b40341d158215600c0f121080d40241000001079900890745030041441ca070042c918904058070880510f540d07406814001d085080c0d0b42d0007818030034211840205141914642d5a08110190540b0742400b100c066002d88505c20125842d45c00005150503002e0b0444003a0031400c265a543c030440512 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 83581988 1250 83580738 83580779
    0xe090705090c0f071101080604020a0504090203070519090f050d2028092007031d040204141f21061d010e0106021603080304150f0e1506030304 63
    0x50002c202d41583c480c008240da0340c05004860741022240000406c10b8800824081c06140188281480140c02905072415070307032000300240c0c80e0b0380c0d9580c1c100c509015440301c0000c17100c80300b0409181c0c160000041026610b030424100c50203500d403014008100503540d0014000d50380607801e03c01004100c90300348540c40b8000e0900917205044001100030766800d800340700c0000e9a002d001c0121003210b100380358902003288030042c0940da010007400440d0003241030190602c0020010019940341d060200340c0c4e07000008104540340c80c0c54030001d05003640c041c00030500038120381444444691113804a00006001a91000c5015100c0c24104039140e10500510301c289440301004a01103141c001c01c02c01c894062802d20304550715106608103210b0041e44050155040581304003c540f0150052900342c07600550759131390b80e4070707030345801c2101d071403e05101800c141c60243c1740005107007070f40c100c81c1320310600c1e1045403040d40365044454401c1c102965215403680c4100410019010045040b20800b00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 83583238 1250 83581988 83582011
    0x16140a060f03180206040f0e0a06060806120109060f05090c03010912030b0a0302100c0308070e0105030c0c0c0a08100b031504062a030204050114090d080903011e150e09070509 77
    0x3d10a6010481a4005030000e0019062100c01805110200301c980750707004040301003d0007024503207940070b0a40700c000742805000b02800003084012241c250400c50035540d00140402c6506038000748580100700aa50700c10642c060107004248616050180420742c80d00400302c10032601d40050706600500682c412550441c01141c0300001581e2003420044901401c0d4480407003c0241e490018213004005000e401409800110a002d9982c8581560740c807140d11140300d60386044c16550b0900d40802c00130816841b500c01c120100e501800030807041800701030142c06102c2261500101515034a222018800207448000040c0110720281c000141d124220507558200b40300741084004c94601e40e0314804042070b00081c080007a541d1020940c18100014584542003591110003d01c450840c0e0030058005000880c1c40400303590290b010850081a03040d4481012100044090242c068205c0121003070719501000240300c0e0301010014442c52180c0084d20400b8184400c001882c680601038840340c0c2c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 83584488 1250 83583238 83583281
    0x9010608120d050c040b040603020307030608011a13060509060d020a05060d0b09060907051204020f0a08010504060f0207051905150c070b01081c0c02030c0316140a060f03 75
    0x105041c40301e45000d0760850266507030741845845030000e03150301a1407245030705020481003091000000c140e6040d20700e60710300965a0303219070404070040c140740c1d004115075520b0100b201c0c0070061503200e0010b070107009644d111500c6420f18101000c407801d600c24150411890000561785141c21a41100c12502c018030745603941380c83c3d40104803180c201074001e46a050780c8111548852a041407003550240040f5203807640362030f1042d0001c00d0340c000c445c0c1c0840071103001008034003195122915028080405445510000c1d940d038100b6010f06002c0d102074480350710f444220300c0d10800b103000f00c03012076400400030144001d60340064895041e540380241e51070300070043d194a11040700d5071104d00800c4401340c8241c81d2005802c016102d980c069010405942c002008140c10909040c034001000b1903d0900908400090000c00d040c0050124000d900d40075008042c2d600d11040900035090b240c1003c8414140042e407c1070008109a43c055940450001414600c02e00e02c07076044240111a42071484609 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 83585738 1250 83584488 83584499
    0xa0207050f130213140303040513020d0b06030a02070605010801090206030c0703020708010f0c032904020702030c040c0c0311030f03220c03030302030613021c020f16050109020a090e070e090106 85
    0x2241c004a1013841307080040e070010400124074410040325920100e014510f01890080081c0b00c0c00007104100303d500340c000c145119900b815a03c611007442d005081c02d8ac4c0e1b85401d038110300003580240000c54001385050000314480c42c0511404008650182c10a861504c450b01561002e40104104a0451251a9020591200a00a5050465440601041c60700c0c82403409010b4500c9601444c952442c0f03030346680b140e404141124245500240d400503a01c1010380082406c10400c402c0e0384e0b40182c1054002c140a81e4170181d01020740f40280e0302c21249412040c0160785a00c00c07440c1c1040c030300c00b00b072001c50fa95500d442101c0c02c102c0780000340058414016900d11030740d00441e510580100c5e03404001c00c0394500701001c0315004800030b0101180340c004000106200c12700c00c481d0500001e54041030fa80004a00c082c03c480a0048801600c4800000303480c0c040e010f4444c3d142d00302c2c00b80320f0400000030502c04038000c1c1c3d40c0d5004100c0c050030641e4100011100b004d5001085062075641700c00300002c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 83586988 1250 83585738 83585741
    0x290f0f0714030d0e01020a0c020f0609041401080d02030711010e0a17010c030b030a0203071509050a150914130903140705070f060e01050a030506062a10020a0207050f13 74
    0x81d003180c0c0d00003543d1204410703031024085940310303c0510060390041007081112580324007a01d42041e41160604c0041425001144480c001e6003170b02d982151602c05410082421743d44098100c412a10031100c1c2550b003008201c0e224041d55070003c201c900c0c0d6008a00441d03014980d007031040a005072507000d030965584c0c101840a41d12441d1201c090755500004540641e00d40181101441d00381c0042003c3c0c0020307404179644140c144240c0503044030100e01210402d00c62059003000386001094190025200c002085003071044205e4003000c980000000159400e030300c007030480c41420007441c59941141c43c0360701c6405019412011410003201c554800d92a1405001401c071300ca014000410030315060007541c888441d104e8100006103d48002c0e40106680d1080807103a007401140350100702034442c0f0010503640d0042d0040c44600a80e41c864a030b40da8600c907824405444045c0003150030903451030141c43c003207110710000000180c21100c03081c005410000544105191b015240180c5503024495200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 83588238 1250 83586988 83587013
    0xa020a03031b200102070e070903060906140405030d05010905070c020409020d05010c090e09190311070503030703050702010e01110c040b0d050102030f01031505090c013501290f0f07 80
    0x11411100c002c59000c156810003c2c0300c0913008009151040b408c0050307015003004010721000340b0468686029a04000281d00040d007040515440c80032241410b1038000d880c2d40244002c010101d02c0c00c0d00005038020b00340103460190080d070b211802141259002c0c0000741007a8402a40c1001d118481c501c0091401d210781c0345c500c40b040d0b4500380601d04003814000c4c00b11020b44807a209610115031100101d4180304c4420b8070a60505054450700400c1d114a0708082030355001583c1400041030280a1507000350080208500c00d9031082c0040c501e20005440c031200064141d065030303011030204c1500d41815401401d14000c028205030700310f0b105070350b417500f0390340100d0322110000c00d20001041001500300e00c000e03003601c1d044000e204624151842c290f07121000601d080c100800d080a043d0100e4444c0d4861030403801107480c2504400c42c02200c880780f11020700c510111311910544443d06416400e00a031544414030145030319201800d030003011a03030400030350b540898200f0405d0750000742c1d101c081325 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 83589488 1250 83588238 83588273
    0x103060501090c080108330c07030e0904030e0f04180c060e03030f0d05100b18010801060f05030610171005040b0f091b1323030a020a03031b 62
    0x2061640c10030903100180d607402d240f520248069031005100f40700002c90388403000360842c10100001d4091082075038148205990319040710080c4030a05c41c080010000502119010b0380b82c4803011481d10301400920386040314058005040a034220f4840d242a205542e0130141c02800030400503002641101c2c4d422400c5e10854541c103060504100098000e124800310081c12009036061007881d1040710092303c80c1032030200ca45a500c1000480100c0c05440000180c0485030801d0385901032243c0c11600c001c0d441c10b03a47e0109541c0000021070302d01c62076005481c2c0581380d40c3c160441d05d40c1070a101b041880240300300c050220107902c004480c0040380065201e819844a02158a40b6250511044590b96403c141c001c1d074031088480456114401e00c076421241a6480c21020800c41b00b0483c410700030070304d801c3c0c984d200c5544000f500c024940850303001c203901c110010150090040415039146510034000750007240350141080440d0165044070329041d60281001d421011507500c0d41e20103803288228 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 83590738 1250 83589488 83589491
    0xb0a09080f12030a090503070f1217010605040902090d02060a0f030f05060d0b06010c0203030c010605130203090c01050304050a050106060504061701061407020303090a03030923011d18010306 84
    0x10000c003041000910421031210028180455408120040d80c0c44000e0110a190307071a02051800c0040c108116865140c2000700c0130960503103443c00559130702d040050307040001d80700701c8504481c0952020160403500c594480500c0d140c5031804007000380d0006821551310031010052400503864110044c211024280e40740c6425004000c0302404503075942c1403045c0504c1c50001040b074141c9035043d50100e00c5402c40c1003021190b443c140106da040004401c000d41500002c10b03000c50400701500400140c4600720b41c04c0d01c41c00c170200c0b004402c90000301c500c080140d0003600c1b0941194004c1c8001c1d40c009001d60700344d840c184913903102d290a440d440c2c1e22000000700005010085107502544099000703885102c03845540d49030960041c0b1503500000c00000308000001c9141c119134082045442205016050550f00b070307524200500410424480c01011008180c40000d10140e4020700d0040e016050f10f8152080c0105e01003c0d038102d070b40c1c038006904060200424042040035a1846000b580300d401d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 83591988 1250 83590738 83590757
    0x30405010c0207090903090e06190902180f0306040b0c070506010605090405011e03020108060f030f0d11070303020607180306020c010902010f020106032d08040e06040b0a030503120a060b0a 83
    0x74a420119131240144a15044809000a50042c6081c0894580d190416075989031040003030042c41c61003245a2030940a02000140903103103130064104a510224204400c4032180244138044100403000c5134144c00210000d80041c00c48a00590040464400c481c104021580d1361860540281c0054007c0b07600820904840e24184c0240782c09440a020f44419000003d80507242c81070b10b60100a040c0f18a602c00a130854850b00c0203e034000074000d0440b2002e100b070603541500c1d40410441c01c0c0024111803031103580b00a00003000000c0b2507140d4020320b01661003001c202c030717562146044c0380307001c0d05402c4c0c00001090b168005000d428044200000d200d210300d00c0003402c01e4084c0c0c00c0072401e59060400420215180a0b050042d80c1e945400c040d03010f0030200c0f0070001100f0800c02c0103101c3c074004240400d40c810619906440b948050b40d00b0400d000454080091114480c4030040c9590700401c11036036800b10707075100250001c02c040b80104040307848420810003604502d0244001401e03040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 83593238 1250 83591988 83592011
    0x5030d03090b1503060403030b040213030f02090f0c0d02090105190201050717091513020603040507090506060f04060315230102062a0705070810020306120f0303071d0603040501 78
    0x44010781c10070581c20030440a040143c000c281c0311400104080c05040c0d03210a000c1ba1903e42c0c1e011201070259903501c4460742501da107444881c50082010a9029510000002d140043c01400ca580128420b01e401707820030585000c1c240196111440712410484244075030070007412402a43d80400555130000f042501e009039008041400000362284244d04542c00c1c421800d0010a55031920742c0d55815041c000c1c2c0da1004014801c501c01030700290480b000200304400d01c440810f141094400d030341c4040c41540c4424003086a01e01816862804a071410442040000c0c00b07540800a441c443c5040d82004d00d5079105480399003600031030030312810340300c407072500a896078144034165001001d904803103203600714848602e014071510900401190000030710307a02808001c100480080c1001011540c03402c0910441202a400030355415004950752101e030411004049144030701c11032440300541c15561003c0c070403a44001240310107000b0300c000488840c01603d4100086200340d001e1030011a04020300e6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 83594488 1250 83593238 83593253
    0x315090b0123031203010911041205030307020d03020a08280f050105040c050304050705010e0d05070602070303090806060108150a09091a0106080910090c0b130e0108150f040c05030d0309 82
    0x14003150711a130810f804907240120f40c1c509036419034094040028079500c40c00384d081440d10581c2c001d030080d5103030031040d802008030010045110307801c0c2c0d40c01d45d05013001c107040a0b41a401900244008a0007420025060891040d41480800e4203200c19450010b40410400102e47e150300c0e4040740350344c40300014004c0d420f003401002e00740301003031420754514941601c0361511400103009450400840c07006c42c12450351a010007000a039005825201443d5407550082e42da18001d10048001c20014070300040c194402107490382c41000182c45050142d44c83c400f801901305810504507038000185480811010040e02c0b5800e803481c41009a01d88500055008250491301640a0701c10080944100100d0300d02c04070b0f001d542486c2c40c4a012800070814540400129051b030403d8074600b0000c02c080d001003001c003402d00101c0d008521030104c0769072030303900840d1514816030300b07200ca0500c0b44000c106101074040d420303548103004203000303000c040e1210002424031031002207410009480742c00d08800e00010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 83595738 1250 83594488 83594549
    0xf0605010e0d020a09110f030106020d09050111060a110408010e0a20010c0b0402040209040513061409030f0c0307050a0317010b07020d0201081008030408010f0e03070203070315090b01 81
    0x1c035a100c07004102c0740d0014041400c0781c05010300e140e03299a00360680c44420410f039011110030300f80c101c0d201d40c0c640400a580310f01d0380c10001c0020303420980024503540a00030500c5074803484406411a070343e4400484014290461107840094410000041c121500b8031601c00c4001c98040544905119401c1c4024810b10a1005544213011940018126a008006030220f50b9105200e6031581e6107600004000380501d010701d44d0041c0c207001c1048070344c2038440e212808892080100300202d00c43c0c0180004145030464078114a50700c03c0001d84c1114004902034004e696000c01183d1600c00356070382c1c150500310081d504030301050081b40c039030040040180700140907002c100d100a04000300ac0d0005401e2400519000c1d06000400000c20110b50701c000c0c02c00003815601040ba0b50341c0343d88100f558000d00e003511540c81d6281c0382c00c1850000304808811904c142d50000c008010803400c54072000083d50702c6010340318a2940d21054140083d081456050007032481120b10192490810452400c1102 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 83596988 1250 83595738 83595767
    0xf0d03021314010516030903081603020f011a06090d15020712050901050d0203150d03180807050d02060a1803030903110303120103060203100b19030e0313061409040f060501 76
    0x41e0b070460007982c0d81c060306656101001941e0315540350014107050722010308540015201d0180045c01c2503180c045000c854020754802d5003101e91410601e0380711070032200300310726840c0440c0403000c0300d21542c45e0000241050a000030942010080903946000e104d642064602c2149500802c0d130340e0074045607003c0d500209015003005840c0038010320000308548500303003141c4c40a507030200206400c000070030711880c040c40c4040c04007208920b060034050b20003074603407505c400314242104010400e444d01195100c100c510142035007140c82c5032503082200d590003000321241003005090810043c061380850500081d4065103c1480321411420f00400311a0751911050080e4000c01c1801d030340301c4c4100140c604490b0484001604c9403900480788103007150540c0804490000850101ca10000000d4983c0d00c50b101601c04109000803c00d44540324081e1000c0d460610798580c60822505018081d000c00858031407180a05c4c00282d10001001c41d10400c00a40750746950321800d01840d42c0141d81070342c50b5034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 83598238 1250 83596988 83597009
    0x4030207050303131503230406231918080702031203090a0609080f0409050f0a0e0a080903120406030c0807050c0a1103070504092607020d02120f0d030213 68
    0x212081c40740c0520018821030b0351764822005990040c0744a580702d0003a000c00c20b0300c094511640500004e540180036901540c50300e20b800040010742880601c1600f01c080703216000c0d06680da0340f001c8481401072070742380540c0141c2c03298106004c00c141d401012034624824200c00343c8a40382c50040c10b140c0b02100840c02c00b82e0500b041401812040040e4103070445501c040d020070000d401d07180c005507d000f501c0700b07460514000b00d0042035010705034100b54410800542c146407a540c034500800c0c143e8070b10b0b044803030598010000074804140c01d1402803071302180c050121048480032010b1402c090f44682d110750006980c40031100f003c250300ca150590040b05c82d03d012802c02c02c103071500d184c46001c5010300400c0381c505900060115141480381a00518005104109040c01070400186613081a4011090641d808242c2c003810031002c010f0340c030342c41d4019120111941d0164280701d844c803101c0070b02c03a041d031142c68664416544104200141418071b07035805030b00c6076129030342c0c1c450000e013a411410990 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 83599488 1250 83598238 83598247
    0x18010309110d080d11030f15030f0706050904150509060105031302090a0f0b1509060c01060e0c09090f101809060905070503210f0a120204030302010c090e060906100e04021204030207050303 83
    0x1507451100d941e0020f80e18010748807080d10300000649051090302e10754006d80510314001529a3708a0060700c40d217981510240240f8051071410503107559240100c2c2e41c07003810710000c0789595200340d004c0d590020880300146070000c81c0b0303000241c00c0da400b29140c01c60380e07807240000050b981d107178001c0d00c003460070a4130144080b440380614000031f0b009804083d4040c0b40d0104913400c0700b85094000d100207190840038882c1ca81840c00c01841544d118911071401500f115000c5180702c01c0302d02c80c4c40d11425111800c16502401d108441102c0740070301001c02080c0c0d4582d81c603440070070014840da200172741c4503c00a005042c40c0c14141400d04101004d40070441c1c005400c6d001800780010f080f180381c0d0300e1190b84c0642d00c03042402d00381e640c0b040c80c80e603807040c0620205001c400c05405520840344881161120303c0a80e0740c0c0c0d03510411416048a0325900402644003007942c5040c45040d00ca20150242885060030308514041000c0f0303041040c00c1242500d945050105050301401804041c11003a806540390 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 83600738 1250 83599488 83599501
    0x303090b071101210509030c0706020d1b020607020306130c1220120d0c1e0203150c040b16060b010c0308180a060222080318010309110d080d1103 64
    0x800d2501c80e4141310090511048480c07070102d18007102c9545a500b0041030130301d0049141d59412202910a0b540700c1c8800200d4401e0000405040c4207610395105002c907880b420740804142c0d0b4941080b80c000400344940307001640e0a100892054a0801e01000445818149522203c4041e400460034102e4244071101152060307065459801e4174465924443c1c49603000b0a2044180d01c40004030380c040d40c0e5040500039800900e40c00310758000d25050070455a0010030007072111860b0350080d8036901c1441d456510340e81c1c10b41d0302944070703807026407080c00c281da0b410b09211580d105842101d480125851100200000d502c140b440082082ca454403424806a0b4064030f07501c80a0032004643c1c00a217000c07002c50348200180c2d51721030b500a2065403101d0441c0d030039019224407404120911205141d011500200000c180c0b60100000010540e01180004c015001420f009005543c01817242190040c184c403003800d5810214851040320ba900d03514042081c084400110300d015a0704070030000d1050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 83601988 1250 83600738 83600753
    0x9120a0e0d050a05060106080702010c08061c030e061c14010303090e0405030408011107020405060d150c14040b040e01090516030c031b0306080c06030c0315010903060e070303090b07 80
    0x210240d940703040911003818154900282c03010020810f01c502000415802d0f8400030300780c05002da540003400340151801050704c00c08c01c2141c0c52134020382000d001052001e203a1002880c0300340a070418032060007140f40410030031f0740b1240c90014500300d04808108540c0d803e20640c0a00004c94200007140d506503500181031031820710641000900c3c00001c6001d2200034400c94000309540c0000f003018000b2078258500e9034000040c20f07071040d03151100244050074620602d00c540d03a440345c1c4104007503505d194484000c0550342c0e807240400410800c001002c4150800600181c016624000d858915111061101020503081440250f08000602c40a00e424004984060520b400d020905a10b14003048004140a01c0211082c0400b207040081c2c031780d01a4804000c0e11805c4003074070b054011071414032185210030341d01d2202180d41000019000d8a0f0302c100a1030118052410822450352074880c01c040e03c1c00360000c0c0156800503242081015042150308008080e115441414450192a5201f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 83603238 1250 83601988 83602007
    0x18070b07030e060d0606080a0b04050f04140a150905010e0706051c09080712080604090201051206010c0b010b030906060d030f0c02040b030a03050403020f010801080703032303070809120a 82
    0x141405880301411410381c2d20b4800355041300080483c1008003595030f1000411820042d03071041021032034071903400f007581001c0c0138086c4200312003104409251200e60356844040e14640d0510240e00803440080001046d181c90111800f00302c1e035011a0059640c28210b0846d6a04010110640c1c82020100206e942005c10346d90010084100900b03440844421040501825100200a5440000c1c0361007004044805420110300d0b90351004100c1d07841c0b80601c01280e202c0031f00640450300900c0300c00c000a01b01c45040c1d500001c18507003203c2d01c5113140d41e0021441404c4c1c00103868a20080300300096034000b01724490307001004440d54000c1c030749180c801510100500c0e402504009c141d660b80010754440d03070001400703c980941250f126a40d07508000300303d071b007060004a00c00c0381d4211100c465903105d03042c101d05076001c4c1005080d080340740d9134007510300000040005444c0210798841607454107103600614441c60441d1100022403800f00740560078152203050000b940f00c001d100484941d9800300001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 83604488 1250 83603238 83603243
    0x90f020c190308130503040510020a03140f120402030a0203030c2a063702070504060b12070813050105040f020108090a03050406030c110303090a020a1202030c06030703090b0f18070b07 81
    0x221a0b44c0c80c581481811b40c4030301c6d0410364104420322038102c0820360001d0301c002c2546c00f0781d0360452900c0c604001c0100314814041300d20b078008020b00071004214072503816950028402012641c260046074082811500300c9103019404d60000300440c2050303889007410000807039418480200c090714000014056005d4a41e0b44180b80c1580101c2401e00200441d01c411800d1001200d0f8408070039141c0002c0d6145035a0191074062428043d002402c00289003d0300e114240103940b0002d5903450540132108803e00a0000007420031882c04034003c180c0070300c10140900d02680c114503031011180000342201c58083e00c000001d52052144101280e404010307101907903961701d40815030341014001259a031021981d82c008a000c00014843c16a00000c1d286080c04d109a4005a038503039581d1600e81942d010110181d0541c0000b0340c84042450100c0c02198803a18500b0f000031108030759140c69800e464111103202c42c040d0784805000d0180e0411542c0d942882624004190f41e03030400d03140107454050400300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 83605738 1250 83604488 83604511
    0x2030304080c01090f05031308030301030c063c0e120a0b0606070204021314101e120c020601030303050c180603060103110c03040f0b07020303031f090f020c190308 72
    0xc12039180400e400c154a13090300000052038400d01401d01c281c41c0e900c444190040d2420080001803c1a004800d40b03040b245c2140b0070b00c048a251940542c3d0040c6401c1001c4803990103071a81c4203490609880d00003800c140301650507480d8011040181c030321840003014038480c03061702084404151000070414075a5500142e1144c00d030300e500000c40d0050044d080000d40c054004580c0d13020030205868005d00303c505070161403500925100c24132544520301003800c00007480c0c0380036080c4020240d800c424098841450914000b0602206120231154031008401c01030b0083c030010018184d15014482d00403d2103400145846a0070417603100d05415400c0043c0900008000030300d10368000c1d4400c03100c0030308440580d5901c000c4002119144c0e400350148042c001107a10b00450071800c604261020701c1d40c003500542c0f540d150051140c000000c010070040940c1c0344080007003913401c03040c0a400c8003464070050250b151001c0c000041e04010201a124851f14a40307501c500200340d00101094112902d01c22 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 83606988 1250 83605738 83605747
    0x1140d030318030c0209011e1e03300305010b04090905250e0906040c0b18040608010c031b050301061206080d0509090a140a020c0106090c0509180402010203030408 72
    0x14280c014141c1d0200b4061441d003402026410b05400c60703860403116100700d4840303095a0321624001c9100794544512080280c03810400e011a4891114084803082e1410442120680d20307a0f0780f50300300c941d2810222141c803012900a8a1011107411905002c40600b0144240c2d03040503a01000c900a0b40f04121200d03403650421300a1000c103001b540c08000340020310b4400c07400c244e085801c1070141c0307200e03481003404c100c00050303030380c01d00802d080340140d91082c1c0c002001850662129100e4002c41240e00d124808c4261600c1c031643d4034400c00e0001d140b410000304440b03c045001800301e070b540c510804900d240e100c0708200c2c120f41c8841103a065500a09000016003017510000d00100b049401c1a0498810301c1c0d01550302907040809880c1c010b500f200c1c40001c03941d81c2d5944000b503c448000c1d0690783e113101404107026004031740103015034a050000021314140d64151074004d13910081c6210002c130300d002900c0f184905050710f10703004150119050015509055000035500c1c0f00007000030740000300c00314 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 83608238 1250 83606988 83606993
    0x5010311060d020906030108010e0d080702060708090c0d050d0207050102010e10111606060302041b0f0807050c0619060e040b060409020f031c090501020705030307021002010b0d05010b01021501140d 87
    0x20f0507aa20090007030f0840d81c880d80c480308100e0003000032104a50442c401c8418128156118a2550740f08100319800307403900b130325140780580c1d01c040042c0c450b21a0b030180301e070902406d40701c0e4031146000381d000c0c10040a144c0c50000029040901c1c5030442811a41001b050000e40400080e681e03640348602c200009140c0820007400c100303400381c0c81900c4a0000742c2c2e0845400c0c00b246030006800e40703000701e4041220b040070f4034980803105c07540c1110402003504c01c0d0140324014001c440e4203a101c030311420040c0c68524448681404c0180840d6038484022107504942000c0e1928410000030b40751082c3d0403042400e00c0d80380d81c0b240b160001d29403823095480388495030841d00d41503011000a04043c0c00c9800140d1031015078403076010842c0b00000050050080014a98030015000f812200c1c00f80103585440440c0d000d000c1100056036548084d0341d200d0070580ca55031a001c1c0d00c2000c1c2c5004000008400c51000c0009041800340c480510421b48040014845211040c0c46041284822180b81c40d0b80545071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 83609488 1250 83608238 83608241
    0x2a090812160c0b070204050105091311150d05010f08010510120302011415040b06131424030412020102031504090302010e0123090106081207240c0e0405010311060d 72
    0x81d4000700408802a400580f004000003d0040d0502c2105c0600032683c880003070000a1104a5a03440c80c900650300b4903010400101d040840d507800504011100030302e40c08020041c0d07120785080c584156a44004216922401d104c20010b442c18500038015420030a8070041282d81601513244415410812201054000d40c03091603080c28903071801c2c41c0c41c81c1c15284c801d0320703d40c84c0b810140128180185c06185140c02c90403103215110340b2024600c03842c1010704980303040fa03c07030405541020003000b40520608948071040c100494201a80303a491900d45400c10b014100091103005585c0180207005500d048944540e641441c1130b034002800b0b00d06401d089015000c6447e0340c60145d440c01400c0d000d0003180c0c4070514100e840b180c40c207010f2030b12171030181422104a846112050707000303403000107401e644101c0201001c1d4003c101c9400d400c005900d00f5411404d43c5019440c0c0903544030340b0408242c2d00030001d04202d10085900f001075600d50340711408942e51602da1140f0440c0001080d050b6032045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 83610738 1250 83609488 83609527
    0x2010c0b0c04091a040c090807060f140f03010303022401030809012001050603010e071505070c03060e060a0f09020f1504090510030201030b06040b0708030c0d2a090812 74
    0x1603001405054003002107030103021303100c1c0105401141801100510140a00003120032184207070000c11100d0301c0e1402c115a448820412141013262103680e03080f105000e40c0c050700c50420405211940c0b5403461401924110301822780020250307803c07400900c8c0c0c00b110602d00d411a40c1082400d40d55040b000012188007442d0b0032031590a500d41c5499440c030341c0055002a1050800340c00030002c0030000240b50fa901d030400e1054025606006070960400f5100314050f0400c2e0b0310542c43c0c4034510b0740b40da50780015103008007580850340d0710980800c45611168000c40a9440490004018801d00782d00401d01c0c501080041e1401112181c40c010000c1c4403003001c450003044014000c000500704400d00396901d883d00c0c801a170009041c02d4889449152032030032103086480303917002d2500d00700b010340d03030102c031a00000c0c25543c10060600601410518900034400c6054444000355803041c103241c007020991000754255410840c0443c01401120030000d40b01c040070b13980709000c948990380351500d16001c448 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 83611988 1250 83610738 83610749
    0x617040b04140a06060e10030b060f03010b06030903070b01050a0b09040504030e10090302030f0303100603090609080a0c0606080c0d030c05010605100c0b0705130b03191107020307090902010c0b0c04 87
    0x241c842d0f0b1100f406205da0050064500d009041c009503141c007075017102020b440c0d000c0a08800702d0b030300c0031410714a440844510b00010140020400f00b10441c0001e03510342003150080881d4000140440410446220300c5000d07042c1101ca0a11084c14102d403440d80f030040e25011801a903a030804074050501458a42e46c601c2002004004024501c2c0e000400d060360138481207000388150000100500c80c0481601d200c1e010080013185072501e040300440180440b0321007680d010741d0b980035450200c2e81090003412200c80c2c540340d0540c0c8210070314202003120348903407003032003c0d4101c2c04950a03541c0c0e60f103414144241e05441c05010041440c2000c0c0d004220b01c3d406a54041c1800e0010041290002c201e0144140035004156856607043c00c152158031800d44403144494041505000d0704080402654220304d840000240054610320814119510030714950b0113a440464940d08510302000b0403130181100020a005c01d10f00f0368006000140c200b03600074125440c400000c0d28000185041c0e800415 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 83613238 1250 83611988 83611993
    0x5070303201303051009020f0d031101020406030603120e0109090906020904050f180a020a151209060b040c05040b0d0203191109011e0819090206070c0509010617040b0414 75
    0x1c0d0710b218107503418154801210ba0b40901004110301075124454240e505d60040d1082003c10610010002c8460b42d140040b801d00601d030540110800c403d1019001400c03450700c00080c414114280450700140320f182c49001c0009121858095036404001081115400200807603210703110314192010303010f01e81c085d41d0424500300c104204241e02d10341c0c0c240162007544d4404c030050f840703406480d200d1030140c2010b50000624103007005035804c1b400e40c10700b031402c0d545000190045e0442c400b0302958040c0c0304c00e42e0680e845a42603443c52505100312118210241000341c0340514001c5900100d01605d250010700c298084002800c031004030007501c00c4402c003140200800b881e140e00c005200d4001c400941e00003441040300d101414009108122452104d48030722881c0c2d40d0395034001030140716041c034881403240c0342c0c40581d00503165000900003c03807248005031041c900b404140007074010141c3c03040d41000780c00421714907081c60360280c1c039070020340001e000b0305280e40d6030800303212a41d1018107017416403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 83614488 1250 83613238 83613247
    0x2030705060a1a03030307090509100503190203071706010512010e240c03041104150f06020703050f1906050c1303120f0305150904020f040c05040807050307060507030320 75
    0x100503a80201031142c10780c0da0702c103071100e4400f0038583d0701d0100300e5114021907455002072001c0d2400078502ca40c06484102c2603112a0345410119082103951075200b04100c9040104004500d01481820007500005596a4849038003203529503440394180304003401004060f1012000c03540a40201a8140850088640580c100d59004a40d6408a01e04030000304051020135000c0c0444003c40340a10f0f0420b488058061a500402c401000301e015844018032010100248041d0445e49900081c0516005080001d00e1420680d007010300c0d090803039150342c10043c55054005238245401ca140f2383c11000001c6c580c1e480403800c00360f074400d0030300e5241c8075040c510002042108810314880c07030608643d940c070844450490240c090b2001903900c0419500c2202c7d110342c0a0904484099201d030000b0640801401e03a83c4c0440c04a601a00d240800150f0004040c4084e0300d08100c01d600900301600101522460014014228010f10750000c042603250341121010080c50010305400103903001c5003030b665 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 83615738 1250 83614488 83614501
    0x90a181407050a0908070308030601050d0e1c0e0a080303130302030c10061e03021c020402041203030905120309060c09040b030d09090b040209060703080603120a080402090603010c0f030c0203070506 87
    0x103a40004540380d00050a8a01c0480c5c0d151000c00c00004a0340e02c050b006007581c45010066413143c00c107000b2142c015903920f01441d5550b10403c081d202110b440b520700c4107071081c6035400070700c81c4541a030210b000348000da0041004000c00011681d0041c0040c3c000400358810389001ca0071845400342d240854410041c418003000c00070350200c4220390160190540c802104c222111061a261001070341c89030650701d940160300074201d0a0412944010001450304d5180c003e00c482100600000f0340000341c0e241d4031b840400c182089102d120400c110345050842c540078551030303500c1d0802403526000741404a03041107a62641d4100c601e080800030b040d40c4200c828060001c0c001d80300d6118401116046c86100ca5450909200310380402d00003922880c41e03c0c9160720165401c45000d00415098454800d54041c2e80640300040c0040c0d40c001c0e5101000381c186070041211604001d4481d51103a454a0f41841074903800040c90f4075099864180031414560380f00090f4114080c0001c0034040c5d00440040014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 83616988 1250 83615738 83615747
    0x703180e010f061d0d0809012124140105070f05060405010f06090b1809030702090a0f06090b010e090405100207030305190b180408160323090a181407 66
    0x1501c07526a516040d04c3c120b0003400c2240440300e551180c120180181003004034100c030000342a00c01c07040c10b02ea01045100406a202c840003810440c0540c3c1e40c800c0c109c00b1490701d41c2081801424001c40110703149090040600c403c642c80880e150610400242800400000141c0702c140f9541040581c0c1f264507203400c02030b01070003004201e00d500360b240c24400300390022203110b148030310000a440e00390030b120789416007e288040580280e0181c481070081a00607910054400c1c480c00d014680881e0a44507250700e4070035601681c02c0003240311b0800d00c121440c1c0c0d91144505d20003450890303061846031200d08016091081200d08004041d000003188d2040c0742d05604690b019540d17841441d0380d0044d24003000c4003118811910030783c3c80501c0003001c28140004040c41508a400748202914082c4144041d4007404a004011404903c84150f8081d000007081c0e0303899600350340c0c0c0c40e68520b40f00300100002c10416060003900e40e0101c1901418003060104e522120001c2000096045c17581800b040c00b90 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 83618238 1250 83616988 83617019
    0x3100b03011512030905010f0203040504050a060509040f030e0108041509140102031e18070e07050c010212010e1302090109020a02031c090209070201060317030c09100e18040203030703180e01 84
    0x14080b0320645e50000349075200d1702984006402c1c80e409142894140010080508006000e40e50a60345819022509540da03e5030140940d1144811a0f8010300900e005828848030b41c105d5810f0181c5101000045a00a0000000c0c0040e80c0d1002410002a2800e045101d1307108104043c558030201c20003101d011044803801108c5010f0402400716500d01d451030a540040c0e40202c603240d000180c00700a270010f8904c1003074016a0f2418000c0c14114100301c1103007280c122010444440062a00401c4034014005c02107402203000703400c0c080c803001140c01240c0411810720594110a07400205205018401d00a85644220008150000034a00306580028250041c810792154a55001058505005104500450764020140352500c41090032440c51500010300c20740e05c022007041121404e58030300308141c0031309529494586195030354400b0301280100c00202c00780c1c011566802d210251303500000792500140d140c50251011905203840b02c129003c5984262000003040001044580b101d80d031b1403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 83619488 1250 83618238 83618243
    0x709020d060e040503090402130b03070c060b01020a11010807030b0d060903080c0c25050907110f071805130503031e0a14070c02060408030a0c050d020c03100b03011512 74
    0x6111040d120951490007101c01e0750f00409590040040c12043d0a098001c0c003204801a4041c0c0318050f910880c0310640e03842119510300040f40341401c5801c00002e0711515070404001c0c030040c40840925911050388c4400702c2c03540782c10701500700d00294440740719070402128600c02a046000e40f40340c43c0b0b842c0c4094504894210081808940003814030880d00090f180f2019908004108000f00a08601c0d2600208842c03950004405e803804652a11906241e501804082d81e80342902500c2c625194108586401300c031505400c250f800308074102c00d94000340c0e01422071810024854a803440844400d100b0000c0c01841c600003c01004080819401d00c101d0111001580e19519a90b2084450440305d5032030451700240c14101c041612613216400000c21248090a03161809031190715051541d0070940c0960000b82149010fa4200881407040700d4405c5680d000806142000f0070009440d11122054100850741e62030700c201c06680c00350803100e000b88c810f90706880090785440d0f0045588000007000e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 83620738 1250 83619488 83619491
    0x60807080d02060606040308030603070b120a0605030d05040e0a0204091103161e110a0203010203100f0515040b07060f0507050909090a020109170109140d08010f080616110709020d 79
    0x35164000d0003c1401d40c440d84008091600d01411a580d5140c3c40c2c2005e00110b800d80709490000c1011141100180030405440c00c0440061400c40003200c155038480c3c000b240260400e00c106204150050203440a903846a01d001c0d0803561504e00700c178000e014650082422500f0300381c0041090010000550003880a885070b5400301c40000815210300340003c180840b0041020039030400c90344500a800b50103251078066172450707800ca4001a09a8106913080c04406403011020818800074641c2070300100015030f04a030035a60106181ca4241c0518411010790700c0b00024000104a4103038001790801036039503420402414508001087c0750410861039004e8414540030503d118400500b401384503a05030b5450380c246060041c40c030300b03c00e5820300001d119034840c05480000b031011198128090007081c01400c203040a8103000b440140c2c184e21401004800400a011544001c5102c5900812040c15052101d0f04800c7c00c4034204042d2901242a003e100c0b0042040001c0d50018020061140390 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 83621988 1250 83620738 83620753
    0xa0903030906030b01020a080a020a0f050d02010c020c0904060504031103070803150d150b0a09050f0601020606010503091902011e080a0e01061214010b12030702040513050307200406080708 83
    0x800d074104d13007032212031300e0250380914520700c000b50001d8006c000401c2c0318415225040d125a031481340c90118040121035541001d0340c103140c1294244100c40e541d003410720040c051410340401003011584050300203468079444200090030306000e154110160304841d01101da0b00c8415090400498106450107000407481c001001e5161411170000e105a80c2c200140c200045105440b100c01800b21001c203581206680301c1c002185a82e620543c1c1c03083e00004000c62461a10000080c10f112005202034107220b814800c0c44600180003842c10440900440b60118640e050300050312940070394042d11207100d91705601d40d01c0c038983c00f00000d07004c0c4280100621140003401083d5003030390800d005404004030000c4100c07011481408a41d03001076500400091010781c0d6202107510030b0700d00d4220750016440000c14004508045c803c1a501c0b11101c0b00705504991075566482e264494080050301e035140021000c42c83c1c0b00000d06803820000020010004c141d80d0305905d0391513044a00c903120700c1e4011041d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 83623238 1250 83621988 83621999
    0x307030b070503060f150d050709050a03030201020c0c1f2714031507050d050a0e03070506041106090a03030323071101060b03070f0c05030909040f14071809050c03030a09030309 78
    0xc0500200501170301c0428203021044647c4801840014000010000d48150015003902c8542c00e900145000742e00150340c40740301e07003840c9280215211010b030181041c041c10514841e1003454060510b000da2800c5031807000b2007007030041da10004046000550040346000110400100c1444075015020340030b80303c0030007040d500d110a4520841d42480072134020490a0110125984a00e6000da185c0c4c0c4001400e1102124503882c43d0000002241c8580c855000d000c18400900d0100d10b4058085a030549440c0502c40459103070652840010141071301d400d00304048000100c5150000720306c4614051681c54000c4006003081c1020041000782d51074001c2c0422101c2c101070840f44074141a849000c00c007091040100d070300c0703510040103807a94042413084561656071078504038003070b50103129107142444643c103045009000103801998154000b1703070204889012843d080c0d890168000b0002400d440d60b040a81c1081d007507040b1551b0500001a1000321035401903181c0090300d0180d9106090b440c0c41e0f9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 83624488 1250 83623238 83623249
    0xb0a030b040617061b0d0e100603030819090804060c020f090c19090e060906060d0c0302040f05030a0c1412190b01060c0f0807110310061818110307030b070503060f 72
    0x445c0c07007008a207030420000407a10344a0304000030301284c942c03c660702180c028505104075000354004400095140e018000501c6050102c0c0303100780300300c0c4020005e03420140d4820949204600c11101840b524846c02420342d50f9500c4c840880010190901402d45410781da4040680d01c410b413a20143e40d650344809419510900c07280080d2901c46940d10340e240c513400b0400c032031480000d100300c0d03201008000d400d441100ae809a9829482c5c203880168880d41040ca22540d1089150041c03801b0390300880962002c02c0c0800d07aa02c0884000020400d800c902a001080d03000c01c55403443d4030544920071100c1020070800241402180c020b0000036003130798842d442154814000040540605819018000482e00c404010042d142c032461380d26a249416002003404c2c549190506418555140170400c44c1010b042a04182c00200810800501121240807102c04004000c080e01601c8503841450403a1410011140955003101c08155a1f160000740140140c0c003c07030b03141c0d014001101440305070381400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 83625738 1250 83624488 83624521
    0x504090c08190b0303040504020c0307020a0303020106470f130f0801090305030414030904060e0a05090106050102031806090904080304110f09040605041a1305060112020a0b0a030b04061706 83
    0x6010b186000d07d03000c10840a034000e2048c2c41e00343d01040015000603914160313464002c0d44241c00200d8668600007800c256a010180c030711448109514020401000c014151025244203031803460180f642c00d4150042030082180074801c40800050701e5400703c1003550380340221880081b05a48940d2a60542030a8039000b65000740445e60a0001c03c000403900f034042203441d09520200c90511050400190542e2003680c000e4800d5903080c03042c0301c4880440c0c003507203900440c40f800074400d070b030319280000b03544c0d20481940203105203060760401410364804003250180311009108a034a800c00b410810082c1d0b0040e9022106103800b03a03402405424030550b0003841800040151183c1d1b5074688920000e030100800840741c141f41c04629950030a0a9401c00d801800c240d0150740c1600c056241841c545030041c0c001c04a0b17500c0180040f00182d50f8010100700352015001041d40350710101d4815809051005206507000d400c02201003018040007614416441c4040220b401586074420340f040186107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 83626988 1250 83625738 83625761
    0x1061701020414060703030b03030a0806040f060f15050c0601080706270e0c0c071e0602073b1306061d010302100207080102030c031e07090303030b010504090c0819 72
    0x240403140441d1450074801521191b4001c4c103000c980380c032800c00001d0555002081c0000441c40f168240240782c103284c070031030030447c41800c0200039041c00d00d078945010017a20300c100c440c010800b104c510046071049040d100701682c00c0040314580d507150f4040e1603c41c0024024140007640740000f007032404060400b4200c0940380380d654603003802e041c0314100100c0c5000400c11000350504200072000c2400800c1000000d0095a50f520307810150000031140418543e806181158041d0303105009a9650000300003030b108076041141e035443d240342c02c0340c520318541207100b00030f500d419001c02c10103554a45108406a12524040103c151154181800c40c3d52210080080652003001480141004003020302c0c134100390700441d2891503032001154260ba0046454030015080801401004184101803040300360881c00204a2450803041c003c2a0b20b403180b0003e010180ca804927000903034043d0b4100e60241000340f00900c01240d01100140c00c4d264141c0e80403d510140d0104d031601c0848a01c0b41c01c09900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 83628238 1250 83626988 83627009
    0x50601081e060409030e1903110307030506060603090f0604080a02010c050a02031c0b1e1c020315100e04120801050102010b0a0e060307090501180516080604051306050108010617010204 81
    0x4840c4070511004201d052803c0b014010380440c1580c00350b82c2c0080220b010442c140c089515a4190b00d015101c00844010240c080cbc2d0280d1170500005401150265000c1e0083c0d40180e203d1b070768568800d240c9042803407602c0082c0610030600c420300808200900440c08150028404206906421241807080001c0e500060b001809a20506040c0c0c10002d25012880c030004100b450b00c29001541600404032101400c200c85107040f041814846144045011080300304092403a1903008a83c54610403191600d504400b400011080030005228402070904000c1d154030a141c1488d2a00d0484001d400300c20200302e101000140755031050017424040d24000e081180c0b164a8a55500140b0b0300140581c0c0e4940500c01021400500c54806c0034001c00e6000f000d001991485c1c0c649404403600034210501010107a45400c0f1503a81201c0900c0d04a1015240000c59136100040300b00d56646840000302002d09181c00001d08030015080001a2102100365106c0c141504001c1030803445544114200d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 83629488 1250 83628238 83628241
    0x6020105090d080f060a150e03070504021207260a0c030e0f07061d060a18090c080103110103020909070801060225090e191203050c0909060f0102010b04050a050601081e 74
    0x3008041c0c1417608014060a50324882da2150100351609001c071240900060f0501c00003401d5240402010300180b50545c4d0862602c8480011081c214074010418400c1c420640341000c59807400281d81005240d002d40702c0b0800303042a503c607070090910001406d002030300300400300000400206944540d030107502d000f443d00918005007560841e80c81503280c11040301d0881144001c1c1c5030710006040c000500d9a440511500070441d10383d00304076680248014518181c00840c1c210b4001005034150b0707810140003080c100d08100124040d10640c5032441e040f070304440078840900d40150300103041e1416034003514160155601921840301c0480c5c114038890803811001c0110310000c4d400001d00d03002140070350b1000d401001c000301040184d2402109d5000e240e0b0400340c4040e6051003071130f40000300e0494007032804003000001103c401c000743c0800c2c0b0401c2e24610441d8140e000b580aa650030b000a44188650f10f01a02140c0040c0400c032041ca000c209039100003141c200400a00e0400d400c1e000c0110f40d580d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 83630738 1250 83629488 83629501
    0x20c0a0212030c070321091a07060e0a0605040b2d0403090806090609070f060f11101104050306010e0c1e0717030a060f120204020919060906020105090d08 68
    0x10107454034622005030108116000d21604280105405103004110806280e2000450324483c3d02544645104010f101c10782440b80400c0b0320680c941031980d10403820f85482140c01c01f43c0c014010328035030400078031509101d0810070078250800e5100da401803611172010b9440701c0e011611850a036190b01d4070302c5005003154403a18a1a204039401c80c0c02481c01086013600d60601c0b07480c04c0402d66144d0402c0c0e11017001c1100c12a810031900c07000d040c80e442800e00d01c43c41e010018103180d981044003024001c3c030040306040d6180420506007145503049080c488881c0e049180c0000340d106c0d002d0030380640250340011654022a20710140203003c01d40c1061f1070007203c403a110b0b802d10680300d45524084010042000800c851031190804500000b20641d03407418110545402ca61703880d440700300c680d089607808106515840c021200c800d07405407805a60b0b1009100050740c120000f403c0642c408600180201d80305500c0038500041e298103400800c40380d1680d0f00c50710350b90725204003c50000380800001548 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 83631988 1250 83630738 83630749
    0xc010801180e01110301170105100b0301060f0e040204120b0c0f0405060c0c030a060e010b09010e1906050a090501030b0a0e060a2705010c0e01030614060a1101020c0601090f020c0a02 80
    0x2c01045140c000205083c04c14181c0d60141d000b1b034440800465440c04400c1150004c0c402c07140c11080791209400e034103192100c0c0d000d40703000505c03440c42444030f912103103031a00b401440c40418241d4020011940c9036110f9182d440000310200d4203880c1c0c2c490303603400501c41a2020084400200070300c501c150034145032074100002940480060101800b5507131101415450400014841c103108800110b90500d584903020300b191040340c80c182c480e05101d4010821076a00c0c0341159000350104000210507004c1c0d28002c030107803645610080d0031485001d0005121829039000034103aa22401c0c0200c46901c3d550080005e44491000305500d54010790046104040180d01c80c82c0c4c5203007400c040101680161030302c03080c110005d10b03041d1201e9446805126440c0e078808040c09510000b4281000400e00700584e0045281e00e401e405406580c000659198450041c42c45007102105800295519844c0c19280b9440d41c000f840341f449040d0a10030f200003078007841d0084c5c600c3c0d041da440c02010400019001c000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 83633094 1106 83631988 83632001
    0x512060d020f040c02011404050a0320030405041505090406090314160605040f0b1501080c0a020c0f0109090f0e0f061006050703030f0c110c01080118 66
    0x50050b07030780748428015540180e900240501c8100700c1640140020884405401c0d011002c10003006400981032502c1d1b4402c0d9240020070303217064040100ea0807964040106070308144024080390400d5804003441c40040800300c66100e60b41c5d404680d44410030380e000e940d615180c030001428142c004110b25500680e8291a0740fa01c031408241c0b130900c0e04021001482a921100030800b842213444071b10a900390081040d441d94101002d02715411040091180e0102d0704000c0003505d5100300388280c84266a06401a105c100521020825070a41c41014035040c031483c040e000c80c400b2502d100381e81c058007080350009403042e0f0398001207141a88550f0b0600065001008125130034025110080403149035082207074403901140f0b01a005003214801c0f40f9003240c0703804031080e5041e0780164018006002141aa01910340c01c100440c1c030b5402c03d001d81c000001d070a06410103c0d420903407108 = true := by decide +kernel

theorem cover : BRFrame.Cov 83453238 83633094 := by
  have h0 := BRFrame.cov_init 83453238
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83453238 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 83453238 ≤ n) (h2 : n < 83633094) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
