-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5105
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:45:43.803282+00:00
-- url     : https://prove2.me/submissions/e73458f6-2ec9-4a08-b3d7-9d411c7a5dff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 917985611 ≤ n < 918165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 917986861 1250 917985611 917985619
    0x60403050a170606090d020a0b0720030c090412020712050d0207151202090411070b010302131e0c091a040f0b090d02130e0a0807050d08040f11011e0e 66
    0x65000000c042406056024003c0207054a043c02044010001c26200d2101c0880c0e000e0403030000001e14120040103801120301602201d8558110940b0a05442a514544600c80d400641e0764440ca5030f1014400341d00070340c02c100461000e00030380806901c3c000c030a42109518625082d00310080290008850407100856426074207080d59030107805281c82d040e072000b5404506001504e0305d02c201c2980c09815119001030003c41c140c00c01e0010020302d0b511803441600d00d0700540b401841036041170016025100c809400030410400341b00141c601c80c2e02c5d0480390501c01c94854443c102450b00c030302c0d121700140c0440a080c000070001982e00c43c2c0c0903402071242e0409480c540400207580d01c03002c41a2045007001612010140c0c400d5400c0248440300300c24440c1c0f1490751070b0607805a8200c00c0142510540c4180c42c0e035507485030340341030a61500d05503014490401910001700702c0000d1000b00404a0668401d01c40e941800c0c11400603903541040c030005010918070f00b105a5280c5510a02d100001d2109035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 917988111 1250 917986861 917986877
    0x21504081608010c0818032701020606030607091226030901060803040609060305062d1e0a050d050a06050f1e01061d0d0c03030201020a120515120f060403050a 70
    0x40441e50903101070709504e10210300810001031000c5011500e180c0811282070a591501c0164005140f55000e842c003801e81e40f400b0b01c1c460070f05550301001900d82140040b4010315041c80e003105c001301f0101560080041010034a0031032070800003621440d0040c0c00d800300445c0701c000c002c4940007205401c05c480c958a15030030040c000600c900080211401d541d083d41c0c032808a20300b0844194090900075000580102c003180e05450301c0e4041d500c8c03400081b420840c00178503aa060a0130070020448001e0807502c0410141c10300c48490f90350040040445800707503500ea0000150f400c125080041d015000b80c031590402c030400c2112881e000c0d610f48541040c42800b201040c0590512080000900816010451131109848103240300d201200341c800b401040742c0b12100841c1d03501034015080d40e0007200503030b4020900c0f48425802c00002c0020490100d410081c1c0d287c40307100799490541080e4400c0c00b0701c0500c03d480c018800c00b48035070021800a442264107030b003040e140c0280183e0200701e86400003002c00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 917989361 1250 917988111 917988119
    0x315030703060603060b0310060e0a02251b1a0409090512070c050901090507200c150a0e01020307051009110909070905070924032a140f03130215040816 67
    0x2500c100429100000e0032b00030303031340d0301c042d80b4030300960210395442510307410010142140e121110600101a20030740c40d00d901e0304e0b101c045103000600741c3e420000010000c40203646003800203006039000c54078078120210303880e05103040c0503041c6040361241ca5090b440024802c02031004a41c09041204d5064821000c0d41ea80c40242c00708442c1c0079150000001c0162842c8035030032440040074512a5000804d5134442403a210020300b40f40540101c06a5242c13000c9034620849401c01e00d000c044140a0014620340510f6075a516260400182850301080d980c0c0c07001c8090054100e0941070405014000b041c1d141001c15074240c0ea1035161003001032850902d00000e03c1240301d103442d031040b50504100684039411984010f420150130704486005c01d03680300381c07407207142d18080b230344c0d04040307005400da4504020241001031007204040220075600c2d80401c036000c5034001c0282180c0d4030031096900c2220f240c0b5640b00080841d41034280f050120a404200454104004201803507a00381c41800300070300c2caa031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 917990611 1250 917989361 917989393
    0x120901020c01140d0902010905130f05090303040b04061104050418060f0e030f31170111030a0911031609050105150306150d060e27030315030703060603060b03 70
    0x50303c010198820144500e403503460710b0713400c0680d41a205040c8058419254404220064051400340040c9070300c4156054506400b0300c0754581201d40740d4065072962420f611290800b500c042c00040c1f8003651013407036000225070081038401501004000f44405c0b89200700702d81c119844a0002d90b079051a14038a1026040360388545410b2a0054024500305804541000410b4004066010311000340036104110024508029001e06a21a00e80c404071400d00e0450101441c441010501e05da24100c0348901043e8030105407a4403458140c0d01081e19100c618140c1040000c011401e6050311801128000700441548a901942e0203007000b000706c0c0e80e0b02c07810081318110046802c0c01002041011444c0e50a1603840305446000782000e41e4a4860300e03441d5041111660b1303004049905214003404040024480f4074542c1001001000d03030075006c0441c00070703140e00c0041c0640c014590b10f403a80d00455102881a40d00440d04a00104407281c0e4a0505c0c43c06080e50702926882130092640910319102 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 917991861 1250 917990611 917990627
    0x2090c0307020609210d3308030a09091a0315090c01021b0402070812100611030702180a0609061502010b090f0606091c12180608040b1008120901020c01 67
    0x1100e0b210034400070601d03901009583d21034811a0006516007c00720388011168480408040441c0c291046810005049901d031082940049060750001c002c10740001b07501c660030707006446100a00007101e48a009100d02e0017040405099014060414440b000e8154200c911313118161900a403541007558400490b01c0303000c5034881d1b01c84641c0c1214a440303d030a207940540b01180c440d0355007a10388441001143d2603494200e034000c295140700c01e414040e89500c42c41801c0800c1d403041c019400c1146540c0091095080c107010b886455504400007100524580c20203401001e280b241042000d481d10701d0100540202c1c200b13000950708041c0f02980900b4000e80c41c41c882c45085081a1850325440c1c1040b110b90320118540d98800c014680d02c0c0f94411248000c0000c0034402c40b04c9040744450010040c5c007000e0100e104a0f460400718204010f6144c12240d43c5502581c4117001000ca0b1340d1b9a0383c124049103c81e0801486403051580500151013104010300003640f098007150b400015000046844003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 917993111 1250 917991861 917991883
    0x70917010506090c0702060f031003230d080105090604110d060602070302210325020a0b090f062508041e030c24030e0721110319120c02090c0307020609 67
    0x90402c0042184901d9235801071a01b003108082c000e032840d42d81e501c1c1c1c18203002030703849601c20081e03080f01447d410300820880902c05801a050800c640e40c0343c80c0002d004c410b8010500c40c0640d40b100070312400364000104850889000240030014a501d900b8025640c030100d0000328004c0141114103040c2802020641500388007440045142c840340a00d034045c4c01d000210f0344240851035514003401695621605030180401488903511000440c003009009c1c0388007030019000e0501005482c2000c60529a0000d04962129040c00100c80502c1c00c80c0306880385510a5010803040003070006031b4003e200100d400c4034040c0c00c0c2c26900c1502c0b4114500a0f1004020340c071584003d061516941c10300a030070090508180c1420340c0d800540e11044454072200410f0300410007084110840c0c10415100300c02c14080105078010300341c11100706052800d800c11101c01402d100e030075034118003800d4030810651146a6020341410312074144a540c402d003d400564103140540203440c0011075840001400355146 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 917994361 1250 917993111 917993119
    0x307020115090c02011a1f0210090602190f1d12060f04021905011d03150c03160329060d02040b1b0616030e0102120103050a02030d0c0308010e070917010506090c0702 73
    0x410441d44604180841f00c03290f0410b40c090600c1c0160049440c2c400c4000c02401038101590f20380300c0c10000c0014003800310044050014000b0912066940010050110040c500000c209041e00c81c00180074000307440c000803d00d101c8d8904122001311605200c6d4080c40c070070740c0d10000e804001c4002121810283c00b690740081d401001c034114103580a4813040b00020003030103441034001f5401286c2c55890381110103904950b400000d022400e11150807070754004403589001c0103804d0022f005401155040d40003401c4d02c400e041504c402c81e80d607502c11245191100001103681e20b03034880300a010f82d04580d0312840004080c0131001c1c00b241d40820118841c00b070078a000031b403109851a0030f90087c20300c0260301080d50760910481e805203a803158201c0c003941c080c50047c25030181f2481010b20b0058404555020800c105139098000398001c26400d064608c00e03280148aa43c030058200c40280e40350303201c01d078249011441c0704910035041d40302c40e0160505960340342039580c4010000b0441e10030f1010003900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 917995611 1250 917994361 917994379
    0x80703030b0103090203030a08010e060a0b03010b030a0b06032412100e03090d0c180b0108070507020d0807060504060510050f0d050708030a1101050f1302060307020115090c02011a 79
    0xd100354840d40c038031030301410002401e000039004245036401420785030011500503070060210040301071640c0c0d031000c000c076900800c20382040e0640e2442e010620804031207000100c040340700c2c0c00303c6400004080070003400c020b03103030300d4110101d041542800f04030389501da00b11016042c00d03040507540081c512050030000e1041e903407038240741030050900c0f01200790140800d010406181e642c4209200c525802a25002420b608040c03142e9810148410a01c9101e483c04102c91183c0c0d800c4010180e201c2c03524140f0300d0300c0b2900f60011400c3c054444078014050040004c12030b0810442d6030125000380e004640070132442d42c0d8502c041e1001e5941f40201a0701055880f100d4106162100c01d07054124494825a000749541c2e0003e1855a000250480041a80f5608038040c200091080c9980000a40c010140900b07080445a2100c4800c0c00042d0141c40c0010000d043c040c005d4110b44000c1c80d42e5000c0c0341c14035585220500003001d25070760f40b0b0019402c0c020a650070310a042c0303c0b2039140c0001132000390 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 917996861 1250 917995611 917995613
    0x40b0301060e12030c07080615100f120501060c11010c033c050702131406010c082803060504050402060d0b1309050601030212030a082e080a1703040807 67
    0xb034550704640c5129480007004052414a84041c0050090316903140010655182045201400c0441c001d2034812024030304030403100d65a49a04021001003c141000c8a016516580456103200d00c074804031745080c00d20b40009617082e44070b42c0340c0e0f07007803409039043c4a00066403000440c1d002d00c10b0000a000030741c00c602ca804821882c01c1c440c01c4402612005514003801c1e2400b00640c0c108690b1400011500c0444c4c03142c150b0038003604a032001e1001d036070208981e4000c041c3d91604400d01408443c1000507e1911000b001051822210503100700b50a50311032007007800d0036201c002c502242150020341842c0300040c25082900032140039507030040241d8100141c14a48100500c003200703a02e0f50000c1e00901780d071900e04051140c00e2410707000394094049907042d801800850ac007140e4120340d907a4000c001c40e52400c4c2d80b0520043e04180e03101016030300c000300c4007030141e10f685200606454030311040c20000381c220340016090075540d00c12581c006020740c005841801710301040790003800d040c0040003408 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 917998111 1250 917996861 917996867
    0x6040c0e07050d2c0a0b070c020609041b0906050a0801090c0c0b04080702090f0420030c1302120a020a020d050f1201080a030e1906030e03071b1505040b030106 70
    0xa5004005250540c00c0c500103005540c1500d0003481d601007154200d40c040144413241071079071210004d42000404c00d2924070341d2001e540590040c0340404200415808000715580c08040340d92120b0024821b2094587c0b2000000059081d83e0394030000c10080340300000e18030701a405507101211141c032102041d0307207403803207000c05012509041d0342080194880310780041c1039090003d00450048180d1030f1625a244188141c09102a2402504014400030400015200c0c114040c1061b0035075084800d01e0702d4400480d2030074406002c0d490744030f451243c103060283c039160702810f559105500f601c403868544200c1e582c12440380c04803900050f00311180c414402d41c015001090650101040980790a6030440d40e0089002c1c282c1000f01250419161041072540c4031010114980c400c9038403081d100030196061401c5d060a20440003810340303e26418880d4002070041e00c101075040025440d000b5000c3c40102c65040560195801c0d03e03080051700244d1380e12880940b07040d00c00540c14140f859007841015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 917999361 1250 917998111 917998139
    0x91203120e030f04092304060902040617010209010e040509120a091a0403050c040506130f0603050d091a121506130e01060e040b0f100216120b01060206040c 69
    0x1003198035125a000740886008000410081c1c0405184548a5080449800a4420b03006040e403545400c22070307010b400a160086941c10a41c00f0350001601c0300c4510214000c1c00260f03100118110444650031042d82c01900102881c140980c0c0310440060a08100070841d00113440b040110792144c1103020100c440e410052004041d45c0c10030b2007544c0d42c0e03a19609540351400030707042c0307880c42e000c90100300b000740c20080f003420050110b03414031083ca41200800c10070f81400c9106100703580c50301d80402600c20305a00c4a405540c111007030790310303401076541c0c050249001c0d44a481c0b16000701c3c482150b590742c0107409840f61030584e201c4800c01e548034140e4201c0c1030840c0401407a480541000340b0380b80c80c001091143c000780509010344429614101029003818100180365000b641008452025542e6900c50b801c1500011a0302c0040020b0181e012480e0000d80c080500501b001d8001c0450042c1a41507084125482034100e24080d07030320781e02d040340c41b1907090700c0081001ca01c842e820310150001c6000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 918000611 1250 917999361 917999387
    0xc120604110427050a06051602101104030804032603040f0807031e120e07050105220e0a021306030e03090d05030f0f030a0c02011b0806060906040e070e01091203 71
    0xb000603184035000701030100c201c0058101c4641d1701c5603421004000032805540e9001c442d80001d00d0810054a4000e501c0c1c1698800348040503a0782d600556003000745001f0f03100a1500700340600c2d01da54680c50450001d41414456441005507584540c0b1000c1038082201c0c0309035030000348100f200354541d58840d190303040810210b041c0f00004606080c0b8084c91003c0e5046c0440c640c0d1118804403448142c0012102c4582c01d40700203810502040c1b0542c2d0700320013101c4425500800d50714508520161070003000c00300c2d0704010344170754140d010302250006a401400c11464603100814107a40c0e558070644c2265840704044404d83c100f840b46030300600c0c060164084680c000c00c181e92400c000c0d000080c0c020340c419035841001083c04000d100c98100280701d086d815000030b00080111450f928549210392120605036000c000c00740300016602c0e03d40780c040d12800c4501078541e60311151140581000d49a04541c5a0000780701080c07005540c0d031240500c04c0480e09080e2109031444a03517101103ca510b000b6407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 918001861 1250 918000611 918000641
    0x5060630040f02040e19150e0601030309090f0b1c02010c06021606110c06011e030618030210110f0c0c0607030c02090109090803012105010606020c1206041104 70
    0x15210000c8003a03244040c496482020402d040e203200384100804c803001030b00e1909040d88000303172000120400081040d42c003600008a4030500c580c0111050240401c00c420341a50302401c0000410503070400b118000b40d40d41c01c001442241000d07a645401c8400555016038000f00225410751440d14035000d4401203070040c502010090103c0d02c4581c05da1303010304426000d6540528100e01070142d03900c100420f0160011060745000050008070b40c1d92807042c003901100b00c0c2088640c0d00c040c841c800a02d0015175000c0414403540e181c20307001c20668100c0740380c2900940902d40c401d0300d00e0071051046800c0300959080f9107003070002039500030322143c10080150406224800c0b000700107545047c060000c66200790303980003140f100b51040c40302e40401030b030040079251b04000000b0005214902a641075035050305900300c800442d50080e847c406d41c5448007402e654a0728002059496002c5510600d40c10240d0315920140403d1414a0f81c5000c07c45000e81048080841c001507840c00e504500c0034030344082 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 918003111 1250 918001861 918001927
    0x201030e160f09060e070e03073b071e141303140a0b06040b0a052106060121020304030311040f03030806040b031c050415030b13050606 60
    0x48291070100d40100e00039449841d0001049105040c00d80700c005800303441e1050101c0c41c80c1185680948001611401c00c2c0155001008115102081503900400b0100d81c881502e50200e00c4a0b1a120a4211241135207901c090300310080d8946c41d001d090040303040e96950301e5160a5040758500c0d00d045603140700200401c3c04940014a00f000c1f0181071008400741550441d5459490702d26020600b014406200d078225900c101d001c91040d201340c40d48000d09035004180092207000190078440981c00090b408004000c9010406416081094a6001c40d03030882d50030b030f2660741c0159040a00100e400485101954102100003520313009103800910905022680c2d00075905105503d8115070841c2c80b100c40c943c501081895440a0031135003200301903404004143d40300d00800d489000d5200c00d1030b501d01640c070888818a00c00d100b107800a020751301e040381c4402c0c1c2c008001405014280c00700d80c07150b007000041101c0f202d154030070345000b030340014480d40ca880c1c504042100083c101d800c594640841305 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 918004361 1250 918003111 918003131
    0x71706040b1f09080307082709010b0310030218040605280e01020409140a05010e150f010212030129132606041218030b07050c0f0a03020f0f06070806010c020103 71
    0x30001b03003101d1480360340ea407a10307030100031019480020060404045500b045c54039000c01e072950f00c030700c60540c1e05030900965260781da24044031001800ea4002034020200600b855a01c01d1070402403130042d40320f4030b01446607444451159400d00d002c070400c0480c2c1c04292083e9940d00400d40c1c0540c2003010100c0001d824140c0d2017140c901200e140320100c6e0b400786203040400144a0030340c46040e01415415a4820050030410404404450341507082070286210080507035450b03000300440740c00d587c0000d403150354942e1a1910303d0413006010700886000e40701000f180782030050344001e68203410340b04001141101d10305a100c101a0180c80c0481c014820000c07103035003902000f40026480380340a034071a0101d810b60503030b008141d643c094180e82042140d5050a0000407050010b007a00401d06252250321600351400302e500b0400c540187c1c10203441441c030031508040e00440c1c9a0241c40751441520100d030b000c40d03c1251900b01c1100c2810010740030034000f0b4a19030140e1000c2103081e00601d03000440f0002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 918005611 1250 918004361 918004363
    0xe120d020d0b090709290d050921040f05180f040f0c0806190b0a090f020d0f0e0f0f0604081c0c0e15071a04020303090603071706040b1f0908 62
    0x10a813500c0c03000460f0510240148020702082e00003c000c0c002003460880c021903481d110b5400b0702c0e000100310684490201b0281031040000d521000e480041d0f42781c0f1700c0c4120710704441940c810301c5000190200d0a400192900c0c00e081c00031850384401c0400180c40c1d6481660003c1c00074010b100b12510314004003003801280b1418004070240800900030705c164100750001107050100b805051440344e007440c07040001a11107004090880c0c03010b58000c90144040031840c00a4041c801844046501d41407950705007003015004450301074100707130540380c41401032207403691035102e00040000e076648039401043c00940382030300908407441031401e00e04042ca112440c040070340740384416880010341d40f00030300241403030410b4900c0e0301a0001007803503250a036595510b0940402214511102048a100240c00d5440600403241c110038018003a55491429020140a0300c88410b60210004411340015685082900c1501d40c40400140102d1a43c002c00743e06401c20b1040740340e80010002002c00001d403100d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 918006861 1250 918005611 918005629
    0x703050a0309030b22030f050d1a090a090203060c1c14090601080303091902030c040203040807061a06030a0504020a0306060f0303110303011217040b0406080a0e120d020d0b 76
    0xc03180e980d104219145042c40d040301003010307002c000d021041710081204004014800010f850b4141800031504002901c2500d10b4050380c10f083ca202410480100440fa14121540900c0942108c8903001d94503134030610021542000350080d05a4010000b113140900032a0241540d00d041c02c18003d804610007020b8070550340c2c203030b0f45841c07004613172030a103d01040c0034408036002d042c0b858015401c61521800341030391541807200f050052105030a4503015500d091042c4040808050030566aa0920345805082c43c0c1c0008410343c2d2251801c0403a8503640c3e0700440c40007581c14010016801d58480c81c001031300901c005442240e02a0b00e401000000aa050080c0c2c00280305400f5001446440e5040150070030003240d41d0300380350350410001404a0703090304010002c15900310001d20030216640701410307a03a1166410900c031084002c40c0c0000c2540e40408217602c14541d07140c05010581e202000c9582d20928001c000c000c00000344012502d420b182d40c017603c14003011844c0420781842e00070215003815 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 918008111 1250 918006861 918006863
    0x11809110a0e01031119091a0a02160f030b0601030207050618010c1b17070b1006031b08220807050a0c06020615062a100c18090507020703050a 63
    0xc0c10124480300c031550407240424a045081c04c0610500100720f0800c4a54800d001c2507100340151540031040c001d200700710b1003000e40139504900c0500741c6a00070b050a2904640010300051040023540c5041c02e1007007045d003084030790801c0f5100c000c5045960702c0c0e000500c0204800d04041c0c2c2808458041041080300d140208004003401249a803d801d5403400c2d00d800c440100d003448880c0350385803d50940014425042034001d0485a201c0b401d1012000300f52040c000050b005400070018010449103d418400c111845505c0802c0b170a0584030003442112175021946010841c1500001c2000301100001010b0850303020702071546071515a00c3e880135800041060303c003580041c07110400c121170421588094100d0b80001c15181c0f91694200c1c28a80346108110300420000c140b02441058840c500030f450000100024200b2144020203076031070b0313004554400d04504140040c8000340c0980c03007881d015415161f0148d405400d0400c00780140202800040c1107124400e03001012900511500c3c1502d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 918009361 1250 918008111 918008141
    0xe07290c10050601030b1e09090a0f0303152c0402040b0406060206040b091504030e0d0209040510150b0d0b060c011e0605040c08040f03111c0809010509030405011809 73
    0xe403c0c00000101100d15601900d4000c0d21520504075007030442c0b01031001d5142088410303504c196900f90190381008030101008045060b070070541e804054058124003075546281e828000c103141d984404460480b20b0003100071078003c2880300c940b140c91104801d0303070b8450f0014001007010542d1401003030880e4510352103400180c10501c00d1004000d440040150001c81050003410705055101502d00700010141c40107040c00340500d00704040b612066106051150010130144051800d0304246449041d2103c5480f0350501c0c0281c2d4182101080d550b0b841600c840c0740ba44c03800c0c03000c41b90540000780350703042c2600e91003041030003200361170282401941c80760016001070342c8808a2041c0c2c0c0009482c510b412130f40c42242080707034042909a104281580c042d400c50301c0303c40c0003001400c00362801c2100c0700c0700c3d5520b40500c4c81c020703e661007641001100300d80903551b81d0040c0e50343d000c005801c030342d81a201e11800307401c1044104110761081602a410f4030080704000390a075036030304003c02200c1d1015010840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 918010611 1250 918009361 918009371
    0xd0c05190f141f020c090a0905010c0512090604030e100203254b12021e060609060d03050c10060302090a14041203060504050a0204090e07290c10 64
    0x2403403d10140030111508511000d1240d00507521000c1d448585130b0031020300411000001400216107500182c100300d4100c00200f0000308002c0300100070303610441149801100c2003000c1010040c000861500c290341681e14070300400b2408040020345034041c0041000c601c014020300103454140383c120520000e00b0210090b802d542498114100c80350103940d2182c1001c8451107207010101f5144960058809908038a00d03082c40d2440120101400c0c000034101214558200701c00b00d40000c2e141c2074084002c80103285104100b41c00990341c040885031680c211011a000c0f460f10f00b0301c07180f14040c1130711a0415504041d040d08400786000394070440201059181da41c00c10031b6040192031030b600107242c08000e220704c00035080d110102c41c0c0f016100034a02d51000600d1408a48254800005060000e0040c4090308004042c14003a40050150b0021140b9000c060840b40d00300107080e80c200d0700441600341c44011720034613200c500d8408a80c0c090070310300c0810402030703102000e0180140d1200284070000d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 918011861 1250 918010611 918010649
    0x70302030606060a0e060d02070b0907050a0f0f1509120c05271f0513151502060c0d1107030201050709060e2b0803040812060d0c05190f 60
    0x403030980d01800081c001e140400180d130106a00041148801e442610443da4401c81a807066001380310761040580b04001e103d0500042840110f080002ca890403174101c210345840f26207881459525200b44501c941c107607501004280c0c070380340300041c18811505121000641da040019044403060074110389500c05581d0601140c50a2042d002007030583c1c10450903180f0040205218412001d021403c184c2c00d0703030344c80d002003011003000f10019007805040c0301a08041c2c034201c04040c045001035100140008000854108011011441010071507030040c01c503904c880c1410b00700d50703012941180c1d186881d0242101400e00d030800a0568a12950001880c0e103014040142004e41c40e422000812194401101003683d40e00b00c1500600d0801481071148000300300c00d04d10070003144000601100e800f200308030138041c02501915543c0750500e03000203950785500400c01c1405104070001c1c80c400c12080e090006040007a80c0203951048a1506800c0c0764480500c0c41c0030320b00b42c0e400030408240c8050b16035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 918013111 1250 918011861 918011863
    0x90d02010507020105010e040b090a0c1719030e06160804061d0f10200105012405030714030903091801170304032a180605010906110c1c1407030203 65
    0x1a0780800b032407008010a5040408140302c5000260014241800d5500414048038061101c20340f0349070f0108040c0842c6540c1d0650007078a95803104200014003a170303200d181c0d8a42e040031088043c0c0358144d031100406041c400411180790451004050000204403405001030035001c0204058030301e0384c0700c00d03410300961640729140d051100f920700c0c048d40805800b84181e40b10101010500806810b00015002d05070855002280001c40c3c40007056003003000005842000644200751450160880c0d070100804220541c0c131840103440b500c000170155001d41c3c0300e041c00140956044200401030700e24205402c400030f42a1001e4801400d280008500100000f170948000841100e510401842c101443c0d515410284000ea03104104038102a4141a02000d58200c4020107043e200e03056100724010120800014201401628086299000041141400b402c071844030b031949240200700c40d409450502840e40d0703d62406030280144880b81c0c100090040b048a4010180c14005252544c5140105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 918014361 1250 918013111 918013121
    0x50c0405060f0321070b040c03140d050a0c0807060218040e120d02071403030c041a0f070f2916050901021507140d0c090602070b090d0f0605090d0201 66
    0x410b104a0000c1c0014802d61400b01d411511240c0c045010f0301c01d405144004c040074403c0c514004c28103070541c002c10041107107803030100040d20301840c104100950403030310080d61000303049050000300c5d1040c06076240700c506c2804000ca5091081d48030604081c01c07a9218000d07038114012400101802142da4007039400e16200f2409269040c50040c005120a107105080511880c1c2c800f94031107400050203024010143d90344044d044440b0110780d134900d0411056507036038219010b400f0703050451a4055511107140010740d15603030141c40b0391a00c2c01c01c0d070f9902d84202c01c0418100b2600d0741d108203444050b07854074095043d03210a0908004400307260449000c091003080c0c0e5220001d10805200380b10050b64000361412580c5c03640c04182d08151204a000d4580340342c41d41d04004c4021000641c1d484402da0b580000103103070002c1e182c2d2144241c8920050303884940c079024800c2030740004e0003c0d146900e030402c80e0f10940b900030850070440a81a0b1250401e95804035000f440725440b1031052016954244a2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 918015611 1250 918014361 918014371
    0x306020414121b043207020c010306030804050d1b0807060801080304121b030b04080a0e031515011101090503090a1212030e10150f120b0f041b03050c0405 68
    0x2403c440c05041080c000041d542c12070280c004daa65a42c10000320350921849414003030a4092541c4900c03603035a40c80c1c5e40348400c840c03a10040c028407004d400154080e0107104142c07076012010f1401e150400003400550b2030340f80f00599550014400b800d004440b2103503041d0240001d00003820b1800d040c00c0300a00343c00d0040e48003400c5544100810043c04541c0c5000c00e241c0c2e98802c3c03601da40c40c00c8404072a50a003900d42c00c06008403200390203101c100090240104010f007915150a07680c40200f00030903403111100007004143d1589000000c040c4038407038081040c1c46130141840c4403568011201e45084a0b21101c0440e002d60000401c03a910345482d51441005044040b03032240034442e940c6d1440588062024a401851703103035003000b0100001408108400101c04508001c5a00d001042f01c80c040b0b8035105100920b1407015010600200b4081d0b12124141c01880301e40c0d04c0d881c0c100e0203010003000100300352102d80303800103290b5044031002400c1e0000c42c0900d00a002101400041008136040075003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 918016861 1250 918015611 918015613
    0x80901090b0c0d03021b0d050403020a05011b061805061608010e100303051e030a050103020a06030b060910021f020d1d0a12050f070501230f15030304030602041412 72
    0xb00c11032441100055450840c24145400340c5c449040c00038a0340b445034100c2503c0c41034040d080c005d219044e482001b0b401102d00803148621203d03681c000550304154a03c0f840020500800711a01c0400d00d542c00c94a40819000c0b48500f8414560b242c00e400c040301a1740040d08021000b015400190f4410300e80703805800c03803810130240d07418401c40104e4138400602c0020280b01e80451282e500c404401c900441258013580100d690703207006100940107010074002207115144012011845501ca4070429040d441c016000303520b01051503040020b00309103110754404610a101c140c00c0c102410507020202030814000c0561549100d002650503141c01945511503c80c200c04401c0b01c8290001b01e01d207040e50401c00b11070108602000444661040f1140b951445070b0000d40b003000c004c0c055003c2408804105000380110350004800c401d040c8003a10840c042d00c2030b0002041c2800e80369403c1c55843d01006007100e01c2c0c10750340d0792400c1c10381c0c215074410300000383d14440f0036045040441551001824140c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 918018111 1250 918016861 918016867
    0xb03060a091b0807020c150d1104050f0409062301090e150a200c030409110702220b1f180b030c0d020c01060b0a1103070804050d0303020d0504080901090b 68
    0x9000700c20301c010b900c2c407400c0c00c000441003c01d034102c4c000e11140e082084090901c296208050903c0c0745164402e00b000100240713025038262925801605031002d036480102943e10bd01c00300400c1202400c0024000d561403030f6611144000b00c2070003603d01450140384e10409072290f1601e2030840403204482c1004600d608140c1c8000c9180d270290001d26440884c1c031200141648151030004140e207604142c00324583da0000b44c6100b0080004003410865515520502800c8119400b468a80c02180d1009400c06640050207100000203040749441c000043d100150341e0b051200020703140041c2d00c5228545081100039190a658003d5044104800c01c614030a9024605003642145100041030344c180d0143c08200029060307142d8040796a030751000c100034000141c4850400303405034880102c4001043c4007071012100c01c00d0104c1070391070b1290840b03505414103180c1024017a8085072010708804060b400c0280209141092190342d008900400f2480e4481802400240c2807440c150401002c0107024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 918019361 1250 918018111 918018131
    0x1a120a0b1203030c0702120a14010614010203211905130201030b01110601051e1305070e2403061203070c15030b0a0b0a05041a0c011104050102060426040b03060a09 72
    0x50445c0e100301c0c0d041e0703440205004007c80540c14981100f5000340703616130030f00020a140b2015002001503410702030b07c0380c03000c60504c001a41c0c6c0e03108480008880c50810300040d249401140302c0c01d83d0008200c400080740b80b45800c05001240c0301182c03c0e0007502803003501c0e001996407612030700c02800c0d000c0c00c01c0e08001c0300000da03860341c481c414481c161149071141200000e0310750b8203500315000b4a018068880f11411500c03100301400c02140c0002c0040c0445014011600e0705402c0c410f0b2108815802941940109207840200d84c00200507582000d0300280592558a04200410100f801540a0581c1c0da007010003000c10704803038001000800d03042a400d0301342556421500d0007140e107103014250750317070080010603101405a980009044000da0a0410048010320000d1800c0c541101c001c000e001103031024080a0701650144c103005920100c0010001141102400c4c0b803054030302c401070300e0301100e00c90090403a40903811106a100740801800304504018007408040c0118003014403131390500d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 918020611 1250 918019361 918019381
    0x2607121109040201030f0e071e0b070312021917060105030907060c110306010f0617040b070e1302030a0b040b0328080c06040804051906091a120a0b120303 68
    0x1248003618490303881c5101180031a80a9481031089503071034501442890740c4039214903102c600c0341c0704030b1400000c0400a07001201c01401031005440e0a02c001c41c1c03d0600a0300d0442d0f2103110411001001070b401c1201c900c0490852145003011004c5544014414009108482280401409180c14807a050040c840c43e1740340801c2120994a451906004071303505070400120410010380a1034040c040d100000c1445c80c240702c0c0300b02c140c0d09a038540b0040000da0481c05807258200319409410381c4010804a601d0078482d90030b080b482100108155415000c5c103c298089a00039a40410410303a40c2c0303102e0f01141060300903038030104000c9000c3c080181c1c11205692071088241801d1424031a00c201540800c00000c0c107807031900710f07035000720b581510b45450444807940c050b00405100e00c05c07100c0f10344d401c00d140c004c1c10030903a1465a00c02d0810780c540444209021484011a01c2c00402400303c12650008aa5031500c5960000f03c00314a580c20f080074002c09820300040c140d801d420401c108810781003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 918021861 1250 918020611 918020633
    0x1031b031106071703270c031b180711120705210409020d06090f0911120a05011107030e0618060904020705030309060f0105030d08010b0f04260712 65
    0x700558045507038080b6440d2001c29042c1d0400500c003c41c00100070f000d44041a070840c0030610316a84100840b80d9102510a41d841c0200140b0340c1d031641c82940200e41e4007213480b4400710158009444100c11300c1c4169060070000c842101c10f200010381300402107100c4070041014612400042c4242454490700c0d44406884041410320240c1a0044a00c3c10a8000e03038401204c0090420301c004549036001e01c804040604164815000101c0c01c008014100c0005485080003055109040f001d010503104240074a565001100c24078500a203540c00d00805c4081c001c1016004074038280a607070700c07054580074081d1828146c16030f0040000780a25245404000d40d11549090126809038460744181c001501a2003090801441400044280100c101c00004d1345401031402a801d03160581e21201819681c04440c100e680010700355800402500050781c0050200611143c071244c500f548800b501621240d50070240b00d064501c24000350002c2e00705100c05030203848010400e828801d5151070700c2078005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 918023111 1250 918021861 918021893
    0x60c210702012c060c0a03020c06120703050402010e030d0c0525061107090903020a060b04020306130b0a0312020f0d0201021c0e1513050705091e10030f060501031b03 73
    0x400004101c20f04510042203081c0d107400010301d100e0707580003054035083d1296203100d8103d0145c8580250a0301502d81007080d20150601048810010399a03980c045024040c09041030741444410151440c20351030910a01440401f01e858201d03900882d0310348689043d42c0b0000300f000000a034880400442a1141d911040340d1880c9800c41d103100741120750742d003410890f41c41241c0e5a8a0844d8040802d03802042c0901ca0a014503002c114040c4d5540078031060b03100440740141d0201c1e2191980c0341ca240303d075100454603000640b160140c1c80e125517030402c01518510841c00035034004aa9031074405130801a00030700314150300c000d41c100070752a80701040c10741408140c0d0310100d448210f02c0300e959400f04582d117110045004001c406003451421402c103200c04110550f0a80602d03000400c50341002d200080c01640c02c600041d669100703010507810110001ba1054100d4540740200001181c8105a80c0002600444001416503d03501d060f07480503000754050548041b418104201244443c1c003030b002030b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 918024361 1250 918023111 918023147
    0x20a051c120212040611010b04060b04050d11031e0f19110301090c060504050f0312070b0907080a1104060e04020d0602030a0b0402270a030c091109060c21070201 71
    0x8050107410390415402038569052a01c001c81c002a550382d2010541108180c2000200100000c0f41e05000075107050307004050220908200400c03507820100a4520320900540c11000c40c1416000001e0802407084006140c85501c0150b141402506120410b14031107982c00800600c0807001d041c202880e50050042c03d00d100e5080b803030f4696107080d00400c2d480c0d544810400c410a494000c05085a009401041e006a080344500d03100c41c00e0016081c50240540d40d501e50a0001540c0d6042046030000c000018501502d1400150300c10100704c0059210300c5440103440c846507400500040380e02d40e501002400c03503203a0034003002d46c8501c0c000035441c50f04800c0160740c0e41c0d680069840a0004412036036040382c4000f8480d44242100c4d4812106400800300180c5440d8911080003941c40ca03500014181c40e801800c00c101201007907200031405129107904038200100d08000a100c0e41155440f524039410084040d0724007100308401c40c503c402c24090590a013642600000c112001c0f810042c504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 918025611 1250 918024361 918024383
    0x3030504080d0f0e0d2c030304051206190b0913061503030203030610090b030c0d093002071a0706090212030a08010602030901121a0418020a051c 64
    0x5201d82a41198820402c1000500c00841d10b09283c1004000c0c1c0040c410507401540e500f190074921920700c030058588410070951903c03c0203a1011150012422010b5042c80108000101c0b0384601c8203c1503180c4003100a40360318a000505039010b8140e4030b000140280c81d28110616998070b280c081e54002c0300d0011084c5018003586000301c000c20444501d07006050300356000004040e4000010b40c0300c2c00041d200e803a940c0d0803421041d180503099004150a002061000510401448028100900c11501c011030140840e03111020306000b844c0807180c1d0072000b00041c03840420010f1140310010b02a100800c041c500e410051100190700c89c1c2040d40e041000990141800255000a401b054000304000e55100a48602e90343c1c9034042c0b0070b050042840071000154281c0003009903245108103840384103a400c001c025880040c19071b4251000401440c09a01d4469141c0c0e02c90320484522515200a0220403401040300301002944001e100302d1045042840d11100d1850f40780c0102e51124078030340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 918026861 1250 918025611 918025613
    0xe0d050a180b030c28020a12140a05040501030b03070b031306020c0d02030a02070608190915050c0a02010b0f060f25030f140705070b0a02030f0f040501090518010303030504 76
    0x3800c20003507409034035202d002205002080d0840c000030701107110501181140c12550904074405c2106440d00800582c00810684001c81e400409080c2c0080251a00a10309000500107000b40e0b0003a0004d8000610b010800380541d50f0544210610448120010b210341454040121040e10006120003c403100303514000040058503015a200300141a00740d03990b031049648025900d410a144600052203900400129540190b00d0726004171070380c440c00d03480030f1074611600340603081800341202d01d4410b213103645090040510503e8002c01d90b052584d6a070713900010303009080d100000300d26442500314a5090125035607003c201c030001019000300d2a225109600300300c031000540c1c00d07241c08108600202d1020140c0c07084206080001c25140c0481c0c400310b14480038064021000020500e6102c03034400d12402400201410b00314000f84102c1c1e103000b10b00c051410907a00300d410032240a0034003050a2045603040121400905010344001c101d0b00d0702080070000b0110f041c880602810303503800c0400c3c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 918028111 1250 918026861 918026897
    0x8012418050405150a0e04030519050d050f040b1807050d0206120f060406060923030f03040303030e011a0d03030c020c1c05072403150801050c030a0e0d050a 69
    0x30704000384100002d00c3c0c8000000300c0400031985492040e01070400100f8540000002c1c2d50090b5050740c0c0352400c1110319480c01d1507501120001c1001e200c001d00098401006c4c1740206445a4068a500300d000e0600c6c0c5000c55200101409500021000068980d91510b000442e80301b160400c40ba51044444a8000700d051841206109923207508544200032128002c1d40c2c141c0c0c000c60095070108025a1f0b201411103e600050062242d42d4403200c9071110f91500008203513041d00c000400b91444d003004030341e40030f1070340e070159000300d0110752070713044100c03030041c0038070070242c400255140f4000500400c000160b0300d024400401404e05554040150100b4420480114404405018881c0900d460900c100304100c1c407010807101441540004201c10380700750b05070082444901400340440c96100c0003600030300f500954461000c0502c00c0300240541007400f0f040d0242c40e6417030306659603007010354507103044d00c0500c00208c08951042d880c0b0489940c0c04800c0b50001059860107490340740c0402000c4c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 918029361 1250 918028111 918028157
    0x30b011d0d06021306020c03011406010c11030706180e010302010e12010b03060106050405030615011d0f031920011d0402070f050327060f1b0303070807080124 70
    0x1425192011841d804104412403101085d1081303030b02118600b900000c1054242c0340607000024460345034002040c1c2c0c40d4000c2c0c24050300c2c00d1080030001081104500800e03c0d10070651f01002c0050039280a03e10000320390402c600151425902c0701c0038543c10b40c5c00281c007201500e941180101000ca40d41c1071110750070340c010b50340c03450000c0a42d132955130f4441009003150058010315209000f080b02007061188601c130700c0c005001068407006000041e64488034201d011151002e41c1200214060503550340d801d0194141501c0016003405100d03040d1f003010351240000072680c1408035890010300c800360f07810030400309080c00c0d080341034141c1102c007001240203400b0300781c0010652410200502c08201c03010000d8504020074036620702c2d10041c0c084074800500a12660503810a601b00150004c000209000b04500504200c1042003448907038841d07851644115044800500c4ca0000d1042d01540210400d0062992086000c880c0074003445030060042071110500603c414060240980380034200c01c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 918030611 1250 918029361 918029363
    0x902030903030105220c1806020c030714030f012a02031c18210e0a030201090b0304030c0f0b090c0405070e0d030908070b120610140904061a070210030b011d0d 70
    0x10910a402140c54040c01700d050104501001e81f08a24000c140c50388002031440c0c0c8050b00400500900d40740c400b0f00f04603690342e240d40701d405005490129043d00024090403100039250034061442c08074030707070025200d2101500d81e0b10031504100104410000820894003034162820000611400d09600b00b08540310030324001000411b141420b4402c05030b9500e100c03481c910079910745051094a000400c54030507100c3c0130080c080b07084d180c81070000d074428602442d840b52087c10080c00c0621652108140d011542000300c1c3e40a200d80c04201e40300301d007400f010403640816101400207080180d00500030034100191580140c105000c50300905100d141207400420590b8240c4bc2401c5d02c0d0042c21100b9403103002d5400e81c0710400c00c085083c5042408100c034151a2a13504c0d4204030440fa412114030350301042d0115401901c8034004500c607941d1080a480c1c43c016505c246a68459900c14489103040d00030b41c0000381032034042e10b00c400d030346c221505a5603039155440d10f006145100c070000f281226900d038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 918031861 1250 918030611 918030679
    0x20108071d0d03020a05280305030a0e0106030c140307060507081e030a09230604170c150f0f010e0610030f05070c0318060906030c0e09090c01090902030903030105 72
    0x58000b007071580120382e0095450294054030600d003401005640c031040520751070b4803450030554051010030302c2140516009100031a01140d640644000b04e0b00b074038000c0c2c1054490305c43c000700c00c021541b4112601c03400d040094018040c12884d010010f4120f000e0840064012000045c031040d412108040180341d00c03c60300c0302640c80e4280305410702d0080410901c11203582101306012030304912000c5150450359400e8005083c01d5a030f42c2d441d8520340e01101200d01c0c07039074000c2c00807001901040c040c0c03203402c02d081301101d003040ca01003113074841e6a00090b140030303201c040983c01030003056070b07506000d40e104070140d071707035915010b0f0b00801240200621030301c0f030640d07500e490248550254015085141d050207a07031118500c841e07416540301c05030035501c80c420101d280b4140401510340030344c12500b8100c8141c2844002e0081e540c0101e2079003801118110400d03040600200960360308080944040d03c1d10340d400314214501406040c1d5280700c18019203116941015102c0754915088100184500400c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 918033111 1250 918031861 918031879
    0xa1113031407060207030f1b03080a02061501030902010e09061302030910060506160b1302090403080708010b040f030f0f0c060507030e0d0b0f06151b01140103020108071d 75
    0x100301860424a5207540410502948900140300340c40081ca10742545d81209030b400061503156500083c002d10036905589452025070000041803406018004088454018100d2854690750001c0d07101001d282890500d45405c1001c0d0142c1d9006c0b10202e5114000c3d16032504a4803501c0006600c1001c01c002d03c4446800042000b00840004c07840001e01f0650070420712116481d1010080280500c030002442014404480030202e50031098041d04140381c80355a944c00030f095004030b290340d0000c075000d4001c41c00034801e00071f81641c8455410f00420341c4403120b504260410a40c9000d014044c84050561810003c4c0030090250b14002c025080d640980b540140c03580d100d20241c2260030008043d000300d100c4400d00551030406100302a081c544c0080641c0c0917a840424241020b44050041c03900500744031111008010560001d1030100d00000c001c0701000401280907087d2070075540c8906000385054010030061360040e1542c3d42202550800c0c15900c0c41940f50410485141600658415402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 918034361 1250 918033111 918033113
    0xe090108060430020f070504050415090f080d05160527060f0415170f04030c170c0717030a080c0307030b0310090b1003080d09020117090c091005090a111303 69
    0xc0c074640795840c00400c6c0d4070381c81e9444081000702d86003150044c252280c0c2c0d02c1e0803d602c0c1065405030001d42d12494586080e1032107612a4411604400c2000c0c0800d50b07540140f1210340b0116003070080c0d041740e41c0303001840e000309842c06411845034030729941c46140201859101d1a500c44d015070b050100f10282e066204c51f5151a00800307a0905ea8100c0007144268001c2c00101c00b403d4202445070341c02d1340310b50b58561034503601111101d410300010344400510421003e000c0650b07800422160f100b0070028418141400c5d188003080f4007103000300003594000c10030911200d0300582d402d035201d085c017062140c507542e5280d000c3c5d02601134040900e51501030b000d05003e101c2c0032030303001000c0540036000c4a001c55964215408002207240400703001c4400600c01188604100e1708106034440c4185800440c060301e0746000c0783d04c2041550181e889400010b090103050500f906103680c808a840841d500d03031850040824402c043c041c11100d00e6503103804a46210031070401c100c902170741c03004030424101c5940e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 918035611 1250 918034361 918034363
    0x602250509072309101d04140612010506130e0f0f010f0e030a120f0609021306021513031223041b03020906040221070f0e09010806043002 61
    0x341c00d05150f01d403481c001c50242c0c81c04048082d56151800a000c00480009110741640d035a64440e501035411740c1d40ca005c00d00152280d0056000c1a264503c801a4500f00107080210b40d00d82525440500e0b8908002c10100e079a4404090040d00c40740940004c0c0e40039081012802e0440c01108004d0a12451020503100d0f20150310250142c8101102084410b002100c0c2640340e00c0740d000f40d0000a03510840500c22199144c0c40080014000324002600c1030380c4081d10b4050385c05c4110f0035410306030090010400c00c0d805105010301c441c0c200602c500f4920342100100050103c90320042c04001c0800c0b10418032016940c02600303121a0b03004501448488018018414a0300321011500001c10650380b510300001684410300f901e030300811800e880e41da90401c2c800290400800c4203912850b407030b880744040031081342d01d9014180f259500e03480e820481c00050b0104441080300ba000c4c1c083d410040100f00c4001c100c85803c1640050034041040802c00902030307510610703409642c0181100200040c05030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 918036861 1250 918035611 918035627
    0x1d10050a1503080f16083a0b0a05130915021315140c06040c081209010c0602040b040626040c090b010207081b12011107031b08040902070b10060225050907 68
    0x404c0035280002000d1f4102d016205c200d01208441a88041550005003401d4119540017070001e040c1c018004c0e502c031300213602050b01701c0e01000e00556941905083c80401031a144c44024948002e500e445184c9480f800580c0192103600c80149003103e010107010301c241d8500a0300307440750500c152968000c02d80d881d10790034255030485443e840e0200019004002250314010108000a034034240244003005503024480c400741107600035420000820304100101c0600044c0800d5610400d4000305800d00001c0712070580740203901c02d0500800c101c00070b054100e00105580c407813140841c2c100f2880006078580403081e00055420b004800031f1000d580c0c0c000c40001c4c041c500480d007001e0303114100200d250803910000d500c0b42e0424010450100400e00480d030307880c2110807541c0302000a2070907840c1c90702c554016811540059400181a07002d2007041c1d0407c6400a408103180d4299a1a11101a40d90140c003501c40d24403110010046c000c090314982204001d020141c00d84520f40307082c01c0018200741d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 918038111 1250 918036861 918036877
    0x4060204051201110318030412111e030a060f140703050702010b120a020121020a02060406060803130e0a0207020a0905060420030a09061d10050a1503080f1608 70
    0x450581c1075081421014007550301c0084c01e01c8180307482c545aa03d141000900855490a00c0d03210800c40052081c10b92030040e942c03980514034055080c4c00c058104140d100000800c0384559810702604030740c0d90340126506c09140c0c2c2c401c800183d0240050744103000703004648100407400041e6010411034640641006101d0803950b4000c00c190440c900c2001260010403801c501ca84d840005580e0065024101c0f122405421801c1c0300c8020200c070380035105a0f40007004402c01a000442803000b003111900603100036005540196041055551040c000e0fa542c0e84556203a254582c400314418402070350448840a0300903145048594071043c15002510094403118003c0b842c08000b12a0b084c03e100c4142190005120024590f46500c40000041d00903500140c42640e50344503030701c51040319204c11101914140f03000d00405520311500f030f0104c0d90010704401e0640d06207000503c2c0030030000580010b80f68000c144c1030f2110203803030400c1c0440c0210a682c0d45850310850420003070007501c1004e0301c650 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 918039361 1250 918038111 918038119
    0x2010c030c1d040f0b091f050a03260d060e1807051305060f040e0a12080601021002072909100b0d110409080d0c0e190303260406020405 60
    0x101c000d2080481c1c5004002d50908201c5821850050072840c1c5074102580c6022425000b01c0c000481c0302c001004c4000558001003113001d203802c0d0a80031403185200c400101001c450f140d03031507880c64454a1200804000c0e410001ca405040e00006000601c10b681e0003200602d0b04100b12a26800d0508181000f40d5074035400909460900750702000002e100015038401030b040c122908001d450043c050305000d4081a4044180c1a004000751681c2c8145582281103500801d032a4400d401c064003030041c2010705404001d545420010181d800281082c0312113a0507000680e01c840a00700b04181054100c41d41c44224010310004100350700100c0703140e000e50f01503070990380d5000d21182c00104442d000d13245643c0140c181d0f0b1460000c0745010301e60208010b4050004101607130581e8807600c0c2035110034108840a50344050080c1c80c55072105c3c01021240c0142c509144407120081010500081e503c0010100011568800010701854580d5000b880a0016181003801c292402001075000343c01100c2c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 918040611 1250 918039361 918039371
    0x90b180f0f1506060c0c0d030e10030603110405101703070b01060903290601050c010e101509090203030702061c0606120b3a20030d080403051c0f0c02010c03 69
    0x81451305008840344103142c1d50040405804203030501c01581141e4905605118844466003082e0f1200040072000030304641c1c0004142c2e0952403d40680038141d6069802140303070008000d201500c0c01950030958119400c2c080c1050071584032140313544540c02d00140094286000001c1c00e5400c1720448094034410303220206200600d02401e2020814480300c150051030080201c0c2265000380c009040c181303140e0001040b0b40c21295034075494000e410180b240169030303400301c3d0704000100f00e1006014180d15001444082996000a980c83c002e120029100300c00c0014040050100b580000350344119494080c4030290380c070580a01003919242031400c60038180040e845040c0b51660000060213140191100e5040911101d5450700c5903250091300c480800348007102c08100880c610300c030b0400d103052007100c0d058400f03011701d030070481034548004c14041e20205100c0081c0c0c02c0303010303218151403400315207010b80c80e00ca1140e80500f22050509500c3c1d45890b90781c0b00f800364190044c51802b9460388040c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 918041861 1250 918040611 918040621
    0x5060403260106030f02040e040f022404180204150e01230a032f1b0304231c0b040606050603070f030504051e07030c09090b180f0f15 59
    0x100740d40c80d46010300441c01d450310040c07108500981c8100040790495400604081c2c071001c0c08140c1440540301a5131948030f01a044046150030301c5060310700c454070a20300c10f01c42d02410502c00c147c0160f02a00013100c000c2450340c440134800794140c3d8001d204030004180c2c4031401c0b5101a1401c08000c11550025000c0d1501e642659000700241541003054071844d440c5c2010007404500070a01202d840d02e0344400030191002134000030325140c08254072031280035541d1907039811100e01c80107800744203c480e4200344420404100031074004c100d01036144c0301181d00a41c0243c0096600d0100aa441818918041001c01030000140340140701e2407103150100991034070703241040301e40d01040303c641c40011a5296000c603030b01e10036080b041e000f6100382e00b11586081f01c1080203517041c40c01c00e0700180a50000384108280800148000018003d00d4400c106150007034540e20904500200449005001600d00080c40c1100700b02c20b0400c81d0024050b11903070225005a29120030801c2e400c180c400c00145c020403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 918043111 1250 918041861 918041897
    0x22503170c070b040f020102070f06030b010207080c030303060603100b0d0b040f05010f17010617030a0215010513020703020a050a06020d0c2c0a09020a05040906060e10030e030c0a05060403 83
    0x55805600202c90085a40e250f59964080302207081c03041f030460140440010310800442148000340c1300540f004170f0080f03d081c00081c68200181c0c0702c51640d52004048101c1da450102c00c9a401c00c4040d00e400b9a01e42c0d0b1000d00c0390301403078260301a40c02d001000509440300c0c1c030300e030f802079054450403201032007003101c559640c005480080c0034826500700b1100302000718440008003c0074940414001082c0155201d1070000308141603507000d0095040007a000c03100c5039040c890401c00c002c000b400d0203543e50514000c9140c000300c03030340d44484280e800101001032500810005041c81d500c002181c0d5508118038001c03010750031030804d07000c00b42d04010031a1035090007900c274200341064491140c01030039001a4190a41c02c496500c043d003054401c9404511041c0c1d40c0000c020078607998803070654803403030000c04804403a1607070720020400120450350f5180d0b40c0c0c1c0141d0b06840403854940800d0710300b25114124118400d543d2001d030540f040300300e200f0800401144052080c0c2c0280c950054628180c040c0c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 918044361 1250 918043111 918043117
    0x1403120108010c1403090a0c0e060907110a021507020306070306090b15030f060d0b010e010806010b041511030d02040e10050306040c03260301061e05040f09022503170c 74
    0xf00071a146029030542e030074849002d5030748465400101d88a0b01050348840f286180e25400a03081c940c0040d040021508001440300d42200c0170745001090083c40c021311544651006600034410101e4200d25992002c0721010764125640040a07a030560401c0c0c00090010310007446004e41c41400d060f081c0c1200c0c40d211040c0d17840300c0c0380056081d02e5903450304030508601100070007841d44007014040c00f038085524040d1141c06031641c1c0282c0b02d007d5040c5144c0b5440e00c401640a448918000c00003400a03040d0954583c81d21102c9003880c030001e04203003103403078214040c0349010319480c1d10102c0d0001e002c0900c680114012100140104401c40c1c1390b50616071100c200311400750407048020003c100081101240617084007043c00c0d60001d54a103118058100d83c003e0348610005890715442030041c520b03420f0040884c400d1030034500c4c941850001000d4544206101d00c02840c1c4d40400d011181110013031000c02e94125424903204e60111510f030191100000c428640c1c024148580041d81d840010000c17 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 918045611 1250 918044361 918044381
    0x3020d11030d0b0409050f06090106140f040213051c1106040b0f070f05061501110a0b0a0c0c06092103051b07050f1c0e01020303160305040807140312010801 69
    0x5140703082040b8081d030010708801d00c001504140d540d41c590004c41d5081c041c107001030340701c2c8001d805903060400446003275419540001c0d807010349140d4085030b01c0c0d540a49010110b01e00f605d0143c2c98810989041410b8a0309602c41500701540caa240c0341c5846059010030300c0c00d0b1040301c04449034101d02c0b0030310000d03020342e02540d0100c07901041854101124440079110061158242445001d441c0d070b18203081941c103440e07ca481da401010503d14560700100088103c904410080640e151075403a0751a40360f00240c11001c4460b82c0701c0780401c8084c8910340c800f0724281c009106000280c031034503010f403011840303400e0a00d03020b0150501c0e01c8020300c01e000319400f4080044007121400310040d2401c00301e50098500711001d2042d403101c0c110042040c015404658041401e40d000ea0030801c0d405005401c406900a0454200b0400c10202110b44080d03000080c1e9903140c001550351755860a85064480d1480140c00c2005000420f9503008002008002d00703440d02050208070b9a0350003560307003a501c107411 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 918046861 1250 918045611 918045613
    0x18120c0d18030320010c030b0405011212181d090d050f180105070f051c030c09121403030f0702011506020d0807050d111b07150f052503020d11 63
    0x181c1040800e21030321800540c081c2490103a40720303114079503000d42152016841e150119131908a02c1d00c8520305441500c1c0144020b10290f281c25480740d8443c91004483c1725500e00740310754036038507484000b050490400500941b084060300c0300c0382c508000c100c20030111502601ea11500d201c2012007071048040d07881a80c26810128200710040e28104a003607240c0d211141040824000ca00110b15440c13280103209001e100540300e104480b040c0c0f4503911403a402050180b5007040400c03144194814121002c48420000115101700c841c40c04842c060841c3e0641c601b148004000d00c1211820f10401070302a810a4000300868400360402c0301000800e8411103015820150500301c07018000c1c0d20035988030300c0a1411604d02110084107004803585103500841c0303450080340180302044046105980a08846c008003c150310700009111030700c1c1c0610070741c400c00c0025240842480d0062082e10840b09100c00c1001c0f00100c56034840c10100b4400200390010700c40c0030300070304030140182c500c0c82586d101c440c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 918048111 1250 918046861 918046907
    0x2040e071d070302190309021201110d0e0703080f0409050105190b0c0a021201020d050f1303110309040204030f0b060d0c050f0d0501050915010e1e18120c0d 69
    0x11954451040c000c0c982c00505408101a0009001c0500c1c6202d40e03801d50f0702c1c0050b5400d10b80c0144050b801c449890001c06a00d40030f11500d05c812910240c0364020340150020569024070440d00c3d0034450b4540c0001c080c02d002140e004454160b80016200b40d8020800c00c201c1030f0381e203100b00000104e03e00d142d0861018a003074280303e1480c48070000c0ca07500354400101c460b80d0400783d000c1142c0403800d50105011303075804150b040d030042036405440d8000c00c0070300700d0103103a00b44154000010300700e04d03000038103000d261091081880e00034000e4404000c0024001c645480d40d909004e01404c0300f1030b0f03040390b081e0300242c00514a480c140075182c2d50303140c2108200c0c46142c24102882402c40b9031b062800d81c07086014000c000003802c01d0081030303c0358240c0000b81182d41c0c020f5030010301c2d200381038012031115003d80080291080c2100208401418103906281d450344601c000c0344002d4140d05810741c0e45000e1510b8440031700024800400080210718100c07156145041d070201c43d15100d600c0c80c0042c0c2d44c068 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 918049361 1250 918048111 918048149
    0xb1302130216200307091508012901092c130f140708060a0c020610061706041b0c200306060d1410050412080106170901020405030703050102030402040e07 68
    0x4260306085442e440f50255141c0c0900704000303480c0c130748182e111a070355544403000080b00f40d450030704540007094804020310030021100008800d1041160351010000104100c5082e50380c0b2072500c5400810001c00e03103007030941c040c40c40d1040402040d00b890a41001460100390700208a80000c0c40f02a0062524140401640d40f064000c985000111310140708444021444002c1070002030300414811000148042034848080e060000041c420b140000e45030104020302a0003510004c002e900c03003000d1015030f0f65620b00203001014081495210071f03038400c104040d8240c002948039640b6008011020034038141d40003440070388041111642e05a080640492070071708111b190140d05500c07404240ca0410002c41c4410314081c40082a403051036150028401405802481c0400c40001481d01104941c10708a000c0c25680340c0c0d04604842c00200c600080c18114298107071406808002c4c113440d4015074a04110340070390010364040c2e100c6c91a00003556084000081d1000440d211b500c1ca2600c58051 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 918050611 1250 918049361 918049373
    0x303080a0b0402041a07060b0a06082a0f0c07170c1e0303070b070e2407030c080324030313050d1a070507140f25030b1302130216 57
    0x440c0c07620703500550240404a0304240702102c0000d071a50a400940c2c840155083c0001075501d00800315000b0881da000520003140d0090420340e2110200301c0001e020740284515100507254407160550404010170704450b8840e44c0ca000f00030790700c1d0326130495011644500403540b504552540381c4655038000001080503080800e0300076003c1039406150005800c841012900755805100115007034501041001841d1760068105a4820300550780003004c12608100003117403124009880102c0038020508004142c82400c0006001c0e40c08903802e44c03070b800c05d1030744070203119112687d00895103030b08003840702d4070709000007550884c840c0446a4181c00b45001c00f4030800100d1503100341c44824503050502e2001b2084503581e40a80070070f0b42c0e090355801d09070a250124030703ca54226120b0b078214058210851038001445445004a103040080360845420b4240305410b0715800107240e84030000411110008118698054900a8031100301a030904a850403c903c0303010f00c42c8540c0a10f6280040201d64 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 918051861 1250 918050611 918050621
    0x3011e061b0501060b0c0a0b010b0a022d0706020106051c0c0b090d0c08060613181707051c110601080703060f0225030e011803020402032a0a02160303080a 68
    0x10042c0c000080060f180d40c04100c0a078854440c101e0303240c1c8103055010800c650f42c520300380100001d460a07410681881c1c0025240c2a0700d0314849042403844481c50198810b58043e080c00b5030340c1d401201e1400f40d45c1c100180c007905040c0720301c510441e013600107406109070f4551200031055000040c0658142000c2c00f054080e048210003a411100a50050000034000088080500551802829149411410011500382c661100f404050901d40d10340c0c1141d0030740c0d5500f41c04951080c0d09080500c83d0114440180c040c950300645140f213684401740e00c1e00109003c260f01d2020903603507100758085280405d80d4480083c0301e400080d42c407008042010401e00c0c0d01842a65103128000352418012050008410407448240035542d007030782080b00c0402d504400021002c420030f081090f070030081d01814401030360040c84041c3c01503400000092a10510001800c001c0b802030b1001848208080781c0d860b013980010310b03844054415506170a001840200520301101c3e031540e2480020743d02e0421802c040d00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 918053111 1250 918051861 918051863
    0x3230312070e031207110a031221060906080601060c050303070309060204030f032606031e1501030302070608280c0309020303030a0e01060b0c0c01110c0a0b03011e061b 74
    0x3502c070301c0741d0001d41e070300780f151083d141e006901003902d03a0302604251203c50822101c1c40c0c801e2003441400c1001441580019140c0802d60500d401450380480122040e06241102c02002c64a40703440810040256840541559450780840d24941c2e00c5101c107441440c0c4029016256510600c00150706074442e030481c449079442000c0143c2400d40d260307a05a8840313294801200810181100202803040c44980030310720035401000c01d0a03a081080100384c0b1050902e00a018030740a40441d4000f040b8208880300400807440d4101e101580c1d6418025207810141c052a00081c0c40400407032442d440c40c900103814490300c1d0440d95014030030200c100c1c00510340e580350031041c10340750851b050161341c0a002a510403070b5541000315030794841020240c212980b40e00902e1114606101004000000080d40b00da20082800d084090300c001051291401c04890b542c69400898000d000c1000c80c900000707941260311050200c5491160b84000d503040c0d1041d030240a0008000801d101c20b0440482c46e460501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 918054361 1250 918053111 918053117
    0x90c0f0326070b091015051903030e010318120503010e0a0c021209190b0904060801050103080a0c0203100504110a0e13081b160302100224100e100323031207 69
    0x17500c815046203007501d0f0320713a48840001010080400090514249144140c070712601707070140031400d5a8002c1e003400c0c1084030003410580c0c1e80f100300c4185d41c09048004092500440507016450140000401a40c0300b4060024610804004210303800300900900070205601e80286c1040b0407411003040300c54100781445030384104010940b85280e08000c0044001d05402da00d816541d48800007800140d9205510000032070303147c10010000b15613403100b0703900d018000d80341105d401c0c0042d000203854030120480c07201c9010f141c10309100c1000303200c03000d10440e100146ca264075600d540b080395000c00a02202c0c03a8440d21480c600d80c4000039251401860030b10011244c81900306003103c1541d00d003c00908005c0019281e03032000341f056142980320300d40884001d200400c00c046801486180c82c8401c0a0f22884014203079011441d00e041e00c06111014060042c1402c07610301e4022098a01400144829910240d455140341d21181c41c10081e00c8074119000d00862a0080e1513030310b4080346a00906440030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 918055611 1250 918054361 918054373
    0x61707080712050a05060910240504080d020105040308061804022e020f070f050d0f050307080f0d0606020607020a0b090f0d080a0f02161401090c0f0326070b09 70
    0x181181c0d01c0360360b0040d404c211001900340b138148103000240402900700d0140035074030709042108500c040a030b000030400003042d10072000ca403c00c041c0d800307000c1d5810580d40c500032001810215581548200d00c40c81c02503803858115101c00c2c05002c102a003110010744c80203190400500035081aa902c8860314000080c3d6041203124150203e40c442c00520b65800142c0102100e00340ca544d003000b00101a1480c1250408c0041ca00000100e070442c802000400b841d00764045441071020074001d4036600382c0c0048809940b01c095071407a0900764000540c448030703d850403401090701840094503500c90002a00108a07145107a203030f280d11040c0c005c5c1094502d00c10364480e42900c400902c0b40c4020090540c9540489041ca09080c10a0790080d0000301072052042c0701c114005054081070106003504480c25100842e0b855544a0151852403c040c210a401c4180001e0a42000d8107000841e40991840c1b840001107201003d90b14044080c0c4c041032000901106000c641ca02c400f00c6d070444800c10883c1c01d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 918056861 1250 918055611 918055637
    0x70201050904180519110307060e01140705010501091d010605090106030b040f02190801060c0f020d080c0604230309180c12160e01081308090a0302130b01090617070807 74
    0x840c000000c00b501a180c2d0029254004000146c03801035200c0904401405403107041c6080202803044050303407a810401683c030305540c440505001c43c4d0249400c10024000c641c0c640c070a150241040700003d8000c030500f040c60b20700010043c4105000d89030700500c1c02300c40e41d00c1c081044021b001c1410106500659909c0519100c0303c6a1005081b0303401040e6105800900c904e8025204110580c8401c06001c900e109a40004029504040c15030390304507640e074454180c80c28285410301400b00303201c4a610a4000b8041841003c148003a14910000720401007041d10805060701c0c3c1c0910b40c1d01c10340081d0258444a85aa00d03949415032060909130914100f50300c003524680f41d0f80060b0380050454001004284980d680706603070750440c12082c04d1603005400c1c541c2c0854032032807491401921111002c141d03411075586440000b001190000e01000701d00e1507120070340c1e000346000e2061a01141c0b900e0300000d40300740900100441810042d5441c0242e60b503000082c1e42c20f02c00200706400304104904196 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 918058111 1250 918056861 918056863
    0x6120c040f060303031b1e0c1e02031e03090d0302011806020306090c030906070305101d010e070201110a0e0a03020604080607120e101a1f03060b0702010509041805 72
    0xd070300701c40c02101054181c80d50601070100e41c1144920305180d20641e811100b074a4101c560440e0080381c04124441045a02d0320407a008001c4050040154a010080c010900c22201c5070392401802203094a600c203c001c2c5007540041088550f0386c40640051108242d0741c030701014620950b5000b03000220f0000c00d42424071a4900301c0a50031152540d01209101c054204100c50725404528004218650305101d2080c82d62500000d0000381010b40b00d000294002400d6400c1f44001c0441c0311a01c2c0550115078440300d0071030030900503010300b08040740004520358414010b040986070350306495850700039202c00840e028915025815000b03280e0342d40000c0184c480f00018002405041c0142c000c0d805c0c510310040008070841d814800660518070106211080410b42d44401c25035001c000410f02408007046640245648501c1da0144010300500340782c0340a442c84031541c803040d80e410400544c484c0300b9101c1c6402001006070000e0001c0c0100e428a08040d845801640520030118160124179a982 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 918059361 1250 918058111 918058121
    0x70b150310050112030513272016060f330b092116060216061209060b06120601080c03011d06030a0c03081309110d0504150e0c15070b06120c04 63
    0x700c0442942c0e000d040d0f0303010f403a114010122406c002c403611400d14100302062782c0e001b01010708845503000301c0071200b0003000364001c1c100700781034034424800c02160541030040c84000040c413030080001002d2840303010512076112004c3d03070303580903200d424040400240030311403400840300075070750007400041d012082c410041144100c040307400c034410180c10620001c0c02c1090507201c8601415025406100040c1c000120031b041034000715001030b00d2000c030f003004005400590b600329008180003520215401d822040180705a80a8944481603100c03101034180310310091041c05009a44c400d0b603914240c2e800310380740c1d40108005040f1001d010b10350316810f9911046900072101d0f08000a41085401c11b00c09500e030040c01c00e00000c00c11505030841d0301c03240e0310482030105d0083e0380c2d4030002403c2010364030352148a6400041c08001241c1900c10700c50b503404440411600c00d05410b030540b502c03003680030202c658443e804108040552941814409102483c0400d201d681c051500044100d032901c1c810b13 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 918060611 1250 918059361 918059399
    0x306060403082115040f0209130e011424010c08030a052e060e010507050a0f02030115080601060206010e0c0a08070504171501080f030403030f05070b150310050112030513 75
    0x3503044d580a0b0720042200300c6822102800221340140b00d400f42d256200c4001c1e49074160980d0002c44c0310404000180e004212030203d0320010041c08050050124070300f034208241800c20800381c1c07002c804220040d10000d40c04103000b4542c400420001d0303010700c1190441e5402c0007042c15014003070541055410015054148145800461b500c010030071141d0100419605001c00e082061415105482c5d4a4880309291030280220070640c6d015021920f00754481102240440d5104d40360a0b21580d2107500c9000c00e10402c0c0061051b10300100c2d898514074150741c019084030807150300d000190740b01a5a50a0b00600080600805201c0050310382c002071101c0e05c0841d6888003812000060712100300389080103800016199000140c56190f41c84000101d40a40381c040c03e0800b2900c4992004980c51b1191100040007401c0c004c051110203241038201c80070744c88048081d034901000401c003407000c55001744a100400b00f1000c0d034000201740690000d000c98070080d1180740c0130f46e45480014000c0c4070f40d424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 918061861 1250 918060611 918060631
    0x121e06051801140118021804050103050d030b030d080402101e030b1e03030703050d0e01060b091e0a0603090206090d031709070b030c0a0201140420030303060604030821 74
    0x4021a480e5070280b081802c43d03c00003505155a50600b4410140c52000407110044d07554005480480050210480c0e00030100041080c0525a124030b0925141d90b044038082e00400c1c10600c0c07000151401040024404400f583c80310400d60b103d8007000b4201902443c16400e1003600b10309004640002030f582e4020301e00a44020901c0c504240a001c0d403095101404810051075480d03011240e40c000c400c0b2102c00e1b81500d020740c0c4510402017941d0080000b036601044070f43c0790000018420031440058442984111202040309541d0408a82c0c400000500b165025055502c280b003d40d0280d070001110a0000d404141800382540101d4260b09170391109402040500000a030002450100152322248bc05d01610b800c078030340113207000c8030b00000c0c000903145003001c0b800801c954030075130200e604c8440005203008035042500700841d00140d1084c118000700003511036440c1d2307400d0010803079015410203401a40340070b10703580f501c2c0e4168028031140700007000141d00040110b0b100d4850503000f03520141c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 918063111 1250 918061861 918061891
    0x3060a0b0123041a090d03050a1e0306030c060206060f040c0c1502040f0b0c031204031101240b04030c0b030705190806130504021008060103020c3301121e0605 70
    0x16104d2071500191010242103020400f004050711854141002c41c2e605081c90341e02c40c1d203519002e0328685103000f008504a045510104d90090741764104104172401041460841620307400e0898031904106d0f901030b0005000c80740e110180c101540302a509000034506079484032050382e1003c010443d06001141c40c41d4000c42d0a10606002c160f82100800201e010b540c03802d44100d020a03168012241500240d019560002d000e241c0078078a103c8050b00d01c80000c01245031003080d45e008040050214805442110034080b800c000d2080c11a0180c80d01302c065209124a0008044616030000f0481400c220301807041e110201c1c9101c1250404a0250300c60b081c19140540620401049520100c2c00c051304040612015894004112081003840d140c500459175584005138060301c546a03c218840c840c8544400e940d40d04610b15142c440710703420001082407984a0100e02c000c2007030040e082036558081c4842d001513008500340d849400006542140d46d4556158070086582c11214421804505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 918064361 1250 918063111 918063119
    0x1020d1b080601080103060207060b0d0305030915061809030d140a0b0901030f030c022101061403030403170d110a0c0b0a060308090f01030204090c0e12010b03060a0b012304 76
    0x36105003404401d1604001c80d1500c1e00009000140602c0040c000ca540050880c00b1f200d4160046c0c445980c014003a1528041c1500d0000c20070b520031a0306440c80d00680d1640900c414140e40703100e009000007010118041d06c40415850f9160b0080c01204480c03104110401c102940b6004001d00341300c6640411030546403050008056500703899006c0d101d18020401400051142c14400310707240c2c3c05141c1890082c00900c0402e60007074032101100804003403103d8408144105411113019140d503035a00804440c14030040c59624050350100038400b03008000112400b00e00b85d00500341305007500202181d20700b940100890385d6070000400c140014050500300d420710800da8416500481c400b40c0800505107180c9441e045805040c4029114040501600d4500e030302c41d8064070040c0081c4901000700604000020b803239024403920305030007240c4c009012889100180300d035282d004c2c0040c01038492130b607415175508024a0004801414810003c210501500140c41041e0f100d10304c0089407581c403030030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 918065611 1250 918064361 918064391
    0xf050a1e110d03020307351936051006081c0e030601060e0103020417060f0f010303170a0221060a0504021602090612030703260f0708090f01020d 64
    0x1642d080805140c010001d0000395a844414a041001c15122000550a03d0b6801200100701c400c1619038114000e0240f01c01011040c0003004007040c0b07850200018461000074924901d8104c40382c0400c0101c214901505810700403800c07141c24403480c240d410340c0003012210011551540c011800303651004001c425880c05402c03201c4807007c4d0030f0a02281e000c20000c000380e030707601c030500440e070030054080618419a4042e4041d1406011910480c1d40c1d16a83d442105682d0b01088401c92032000d80ba002103050b645e003040100f0b05031394050360740d80c0b00781c0c4104600251440010346954281c1e98200729014602040038441108022031002414680c1000c1c802c02000d446641c021038441d40c410822000e80302d00007543c0000c403940c10f50f08400036940300000107094283c46040b52043d404000703001030030142d02444503001a000c641144284030055000410100c100b240d000e071980c1c500c2c40115000314000e401c0140d01c900c0c40412106441c0d11300ea001826030308030300c202d0700c4000d80310f05400e90f034500c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 918066861 1250 918065611 918065623
    0x307060e0c011403042418020315060d111503093004051302040f0b0d05090109020109030303021c0c0f1103090916230301081b010f050a1e11 62
    0x202480c08900e02240320000c0c0f2094070020b800181450201d03090b00300745840c0040c409520290315442003007503040340b00d011815a4068881207200740a181c07100c0c46a101000e02040c002c0b04041e1040034407055541d0742d42d03d0038010401e45580aa0000c501c40030843da07400c002c2d4410101d5102030060400810f124001c1560490740103401ca0742e010701400342d441807910665045a6048659072420713840322482070020b01c580e40201041800c44800400c455901000900d0511420755042107640c1c0c824076114201c0320300c542c0c0240090511101000803912a4000d0403040d100040c1a088002e5060400c5c011075032014018000301d60402d040700e10458211028038405003020b03001e1494101c4880c00030701061001001c00c45101a1440801101351050740c16143c03640c90780c1360781c00701e4850030010b1380b02d20741003403190410600c15400380c0c0f20361101d04269001100d0040e1100c50680c0d14a070010790340c903002a00f4080c00c0146000c00000d50602c654803c1c405050191242d0b40941e0190703140c035007050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 918068111 1250 918066861 918066883
    0x90304051f110109020f0d020d0b010e0f011a070f2a0602012405060307090306050759030303010306050406051303051e09040227030a0b040f140307060e 67
    0x645407213008805600c8002078840252403c031042c4240c0000c520004010300100d010142c203019005001140030642e502e1000d0007400c0941d40300403245c2c0e07260003949141c40340074031514610b6000d0014600080c03007240c000e810644a1200c82c0c41d81844010b001c0c072400351174020b01840612101c8200125602813246000294221024800c010240d08a014940a140c810a4040d0740b000001442c0d42d032184042c0406968802800d102c1803c100c2c40c0146100c2e03451903414040cfc0441601c203102c0058501c080c205020308020112001e61804074200071071a42d01000203c0548950351408045da0140000c0d4046c6208001c005250f04145c14440100c460040181c1402070902e9401d0001c03a40010503141d50040400e540304c003421400d40c02107114003442c0115504070340042000843c1c4a0444008041000c4000d174041041e11a40100b55440412600c041d143c0039440c008580072408003801c0c00032980c01220544420202803000500d980d000702016250160303203007150440880b0074002d850404e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 918069361 1250 918068111 918068113
    0x20d0c0e01141201050f0118080a0506060a060e010c02031603030c17030103030819020d050c1e1603030e010e0304031416300827090408070b090304051f11 68
    0x450401004007214041c050941b180782e40007141c4280f42c4c418207881d04c50a582c06984c036140c0f070f5100c0c20a5503503044d07801b00b04e5031402154005115030410209a10442c0d03003d03030310312200300d5000d0011341d032002c02c4e844c0c240d801d800751010114202151040b01c4000314800d5444803180310581c10a0002a04000c44003142044100010000300f548001c1458008030490f107260180f03a0020107490080c0304d0740112141c050300b081c0421070030388000c401900e09070001460002c02d887c44a0318049081c480e4550b80240b000705d1042000101c1d20aa0050848076414000003620a02d5100350516540140e031048640b036501d440c0040c42000c0c1800580140070b50029038060490805c440e46443c54080019100600d818102d0020015507603000170314815040101070341ea900704e900400888900d540700124170b01c081c0700d00f4605d0350b003046800907110f1500301174101d0a007130041c2c0c1c42c017065880151601d11148030900c008960340d0382c1c00c042501110340103502d020030060103840141181204848643c11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 918070611 1250 918069361 918069367
    0xa080a0b0901032312030402010201180519140717070801020c0d0809032a0705181321090306050c07020f04020a03020f030f0a0617070303030f020d0c0e0114 69
    0x2036900d0302989603040d00da2103840190100c503148003c0391404c200241e590020312400e003200701d500004400550066000ba4000e100640e5900b042d60500040031a00800e02c0e0700030b201000c8180c24015040021901c00d60b4400030b08542d1225052500901e0f42100e40101c1c01e540e500d1001c180d003009080020141035000323500300720b0703481c5104d5189d5580e40c8000060246038000140980707018011103803400368415440e03c103e0010b0801d140c82c9040380c2e80d0340c406403180000100f89480c02507494207021080d0700c0041c82030303a1000d95001e680e0344903220448040c2e82c0000c0500001208982601c1c0122895542140c0e0340c9ca141460010f40340f010300340180c24941040307190096100d08140c440c0c0c008080d00c0142c7d4601e450b400482c004d20562072101c100b1000442401120f5105031122030148003040030500400b9240d02c800c2d20800454000341d10700d0b910940702000028025004000c8001c6028001800e041da500f80d40c03801d40c2c1c0901015030001c1d0482000a00c2903811800254030708c9002c0b410f080c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 918071861 1250 918070611 918070631
    0x111b03030d053105191104020a020607090f0e0c1602030d080405150c071106040510030f0c03061508090c180f0f1302010503060303042103110d0c1e0b07050a080a 71
    0x5c0c44412801828881e1242004101c003030080c1c3c03600003045820083d0003155940341650b0002e444d000140c3e024000118007203000114503240d140501700b130301c043c101e100010785c6614011070309070307440309042007004106000d100e00966001c0c01004004555a1600c00c05482c2516249017480000500c40d1003000400060001004885081e50250390340704140c0c181c0d0390a1500010281d0107554452607019441c020254002c03941a00040c005030818202030100e00d8004200390203a03541070150b90f0326515000000050640309059041e0800340e07100c1650a658502001b10f1702d0354030110101d8151041c80c4003030000c804003403036005d640204800041c881900f0102602940c215000c0c601030b040203008004905251360600407100180310f800c2c00400400c0800b048907070540c007080415408940c0c40c0e0189008513001050160b2040c13510380d40c0c0010b100d810b5640c064555000303080e900b018202c002416000030b88048489000e00d03081d488a42c2c40306da05a000a2103264014242c140a5082030041c82c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 918073111 1250 918071861 918071863
    0x301060e0109061b05161e090c0e1e10050c06060108071b1e0507050117060603040f060216030e0a120203281208060907111b03030d053105 61
    0x40c2022014226114800c030344d400d1082c030300500c207031000003026000e0380c00041e0401c24000d09030000550b211004000782e07a03071010004540c201e000050101d14400703108010382c5044e002d0445485000c8031031038004101e0f100802d85100c002c12003030000c00e1000a80c003c64007810007081e548200e00346040040b6141c6000020140900300040b8400041481034800802c81c0c0d03a0405040c5204200c0341d000c1403c040d08015680d01224460280030803010035200d6000102703428050b1080304080c094a1554650342c0c2c2e409803001c001441075644c680d081c0701c0d0980070491074070b1728070125010b6651418502c5000c410400302031202d40c889540e5000c40300503040180c4002c640d42c00b460521034440c405640e050101c1403a48070215000801c408444d51607140c1140d08070103568000d10041c0c494403050b56a4034002d551b03241c10040c00340c0c41a0710a191052041c40030140101041b20003405032814940d003084400280e52003940c04455a50f8110703005004918051072040b18210404007407604101192103103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 918074361 1250 918073111 918073127
    0x2030c071b05010306090b03071535100f0302011404031505190204121e081902060610050d0b01090b0d0905060c070309090507090b03010306020306040615020309010503180703080301060e010906 85
    0x400c144209078000f2b10b8410f8020101c100c1e92010715401500d8a00c6064054501264450b1f600c0e400103940c000480d0242040d0815030f41511008103010003860708603001920740a44024030015007a0f010030002c40010008920709110040780700001c915800c202d07451885000402020706060383c0b041c003040280361039102048480b540c001060000c2000311510a980b40700c04050082d01c0100e000405031182010002d0021400e401ea500f81d070315585a41d02084410103090350303000006201484081d0707030551a41d10540311800141801200d041ea00d4000d03900a2b0840e440715400c880e0780f0b201c200c00703004013030090643c80301c40c980c181c0e880c00415a030080d010711060300843c1c50b841e031b0384c0b00000c40c0c40d0701458402024250707150301141c8969680ca4928043e40c030882d280c43c021810300c80c002402c80b200e8985d80c2c189000340e401131403c114120004582603003004202d00a8904100481d42c8200c0c4244803040180d4040d255040c0e880d810007501506280910710f401d0304022a031001000216881041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 918075611 1250 918074361 918074369
    0x20c031f390f0926060108030705060105090103020a0605030a0b0a091e02070c030b040507030501091415040206032a0c300406030203090f06090d0e06120a02030c071b05010306090b0307 81
    0x35509502c2c1d00030309141070204d52021012507119840001c20005000805801e20740d20600488225a0f00c1c1c06c00c1c4040c0540030311000750440500b407014003802e4090f40103594404000340c0009618460580004d51803040c0d5070001e04401d58928810301620076440740c0b001d43c032220a4040d80341244a030355440f0040c0c0944401740c0300c030305071f00003107001c00800b0b1201c00d009541080081c4110310351824980820049166160b44911460190751146210031041601c150340043c010360035540c45c230f9400051005994050f41141d01c010910b00d203451080e1000d000d03080d100d00000d0292210014614450310164403100c1d454003400c100c4080c0c6044c265084600340d50b2189005622501c42d03100719407918041010101143c01100200480040d00142034071034069941c1c1c0d50b44400740c50720240050752060401070301e0240011000a64a0225a0020358100668000e83c0d0300d00491903d8440c00e0514190304c3d9070402e18941820030180d80e0500032000640221801000071083c0000000e80d152102e100d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 918076861 1250 918075611 918075629
    0x30309060603110a141e062110080c0d0b150306040f1704031203092f01030b0d1109090703021f030506040218090421031b020c031f390f09 61
    0xc1020200d485010903100383c0d822180900d0080c0c5188c0070100f00d80d8608540380fa121101d5803400161182c000544095030b040040d0120408070900d0300c51200404004160301e40800785119091026202005840e10450080c00703003200e5081b540c5810000b02c2e080014074031300d104c414403040c004a074442c130401d00624441e0034002203031180c910300200b0700c1540c0d048068880c6100c002c114626040c0c64102009202c0903601003110850ba4420084010599031380030300020880c181c1408981807540c5c2180d04503441c0c508903074003070b6580c0e4002292000d0a42c1e150104108890000303407200d82502410740c100004807070550800e0710110508000b41e131000300662266846801103014000040110100c0e8079402000041e8994403e80180240210000c0301c01c84101502c03146449500c04100740b41c40d000d008010b421001080c002c40c001e6000c10402c1c2e039001c02e5179190f55180280d40c194441c0d0a60b840c404201e540c10080c0d1107030395800c1703031280b80d0001480451040c159070b982d8084001015204100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 918078111 1250 918076861 918076909
    0x309011d12130906090f110f04090b210a0c0b030f190b04150303080105240d0b0607030c1406010e01064d030903030306010804030309060603110a14 65
    0xd80302d602c1c0d001d160b1000064a2134403202003012243d40c0c01071075070035110900500c03000040000d181c00700e02c64030390501400f18050005000e0140190850701112034000c2c50403242c50103440055030348441125882101f80d100281003c20005041101c00080c5078688480c3c1c00c40c60000a070380d081d01e00061410300c50582441c81101c070310040751304c6401e030428090700402c0314504007407481c0070000041c0000e0300440c14400c000105880d100d418211094943c40c8104194400d1184942160b000104190303501611000e8034400c40d2980b2026043c542d000381d4a8007481901400c003150300f05001c110881140d0040d070014411342a95507290313411152140f4000c0d00c190001c90381d90f005140d01a44040350384590b10061195402001c0c100d555084110703107108140000005203d0703483c45034074040b0b41c16070428000111190301a1840302e0f4040d0103801c1c041140c001b1541d50808444c050f406c1140c8901001c81c84a900382800143d500240440940312828680c003400003514010055041c620350b04051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 918079361 1250 918078111 918078127
    0xe01050c0a0c03030f1709120f041a192613060501080705040c0f090b3f070c0b0411190605030406150501051c0e0d02030309011d12 58
    0x4104010348190045540ca0242c0d40340d1a0042a2143d0140480c00050410000044035942980c2490040c000c0b400100650340002c4408c00d620340203c00c2c5080300764824440055014032502c058018152005102995400b10038095980c0d004000200c10030020781c01c50052440e441c8080c2946401108145030540b550341424840b0440400240205818180000095040d40c000b4020098500455082c8030881070f42604461450103b150400007890340c800420840c1035410080c00b40f41412100c20101007013030301c3c0c05804180300c1d00c180038105402d080c180c08000c01c0000c0b1643c0250703103031900c80400038203a204c00740f075014007401c00750071020780801b00c241c16500c0c400d1800d2600390060a41c0f2000e0794681000d486900308444c15100c0c40c0c20420b0004e0215052107002c0e0545405854007800d0803040c900811582092007006101a035541c0361220070240304101c0e03038000c5a0564020340c2d4a2900010150a40e821030f8030200c2104200d614041c07070090702280d1040d650701488003043e110811 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 918080611 1250 918079361 918079363
    0xc1d041a0a02091e12030703021b040f06180b0618011b0b1f08150f04030e040204140a0e070203070308130c0e04030206181e0a0b0c03010f06020a02010e01050c 70
    0x200c415a80e0711a1310b003091070522011100d45440400c1d42220201d030361310710b141201600c0703100b00c0c80c000f40140c00c149500d01030344040c042e00c46030303003030028000040c0c03441244120b108483c00da8104001d240006800904060254040d00a00c0d20041d54594100700c00f0424800c0440403400101d4148000403240d0308036880c429000c8010b168100a502405041c04000010480c00c0d680c004500490342c1500494841c030b00050b0211421048200c1d074015549607005500c002c580500202c040020140300201c45030b03510300240014010450140c002c29120100700014010b6170340c4003100c04d4501d00708000301540c010050300e10b2680c2506206c101a600c40c082d4400c00c2e20400c0303006007400b20b200030125654107410312481c40349129800310b47d81a00c804280d0000070f6580030000103998058140c443c0310003207940141800c0d1000400311150107650380d4800c5410752040380c491034803403c0440100040222094124001d1845001424407442c90743c00007028030350221049030500000048509072450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 918081861 1250 918080611 918080617
    0xa03020a05091c051009120c11030f060106030b010309120302090d08030c2502030717031b0c100c0503030705070c030f05010e010b0a05130c1701030c1d041a0a02 71
    0x80c0040c4040d00c1811094500410083c9503403043d079880c400c0c507001d294510340c9480340300382c480d4000d00210207070f100b03a07202140e5030607540c4011194840f01000a84a84e00c00300f0103554806017400240c4034560402d0001021501400002410903080040d07210100b012020b02c04e916154034580135035515020f00100e4003030360320b0350ba0003010300c1000001c01405c588102d002c1c10030b800e10030701880300030f0a4018010040e0014284080c1d803603000f03040c0401c124408840c8680000340e11400342d034200941d50f8800000c51b5101c2c04500895003103040c840540f032900110b0300c105102c83c2e00704429031003101d444e580d949000051a84041c4070700021000709100e00c0c220444021a4404c50b0031981c1807451030000d001c0d200701c0003100f150b9800d1200320842443c125101005071072001c0e103900881044181c05401903c1d608101406016072440302092811418004902850103800303030744002c0740340540070000f40907003c401d080001540028000010b202c21380a140e00380907654604020f4544114900c0244 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 918083111 1250 918081861 918081877
    0x302011a15030c1308060106020d05040521010e01020a031e060e0f07140304050109150e0a0b06060d0c050406140a0c470105060403050a02060724020c0d0908030a03020a05 75
    0x13400e119400107180e400010198103854140d0700341c40e106529004255454040c0c1d009140e0b1050300c4e24000c442402c40d2295034400544032030004035100150b40b0480d422684013904050001ba2a030100d00310702410310b0102d004204105104010307603442d003030380c2d9101504041c4c80b480303000341c8080208002a200f01403c40c4461504030509a407824946400f5000f88801c0e002216030314a082103402c0f03c420a881801c894449000151503624041d94504040c01001000268030120510401e0502440e503c40c1150510250301c1c3d840d0703140c2c02c001020f001520300d4098058048400c200c0f101f000381d401031521752520761110303c0c041e060300001000c5000804110030505681542c1d085001c0ea02c039421031000640311501008452a600c1c2d5050140c01d00ca280400f404c07a0340030701085c0d0010f0030500020506c1038050354a1001003141c071042410103891004903030305043e1b00407441840f403000604c01c9a42d452241d007040f17901545001d100a40300e0280800013003d26501045601c2c151340110708031200302c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 918084361 1250 918083111 918083137
    0x21e0f1605120a0b070f111006031713060f230301051002152a0309030901030f0917030a0204050a08100b0108010308042606070306030302011a15030c 66
    0x34408100004a50320100d1058034480c0e60841e5450b080c400002c07a0b841d0070541c016035055020395984070b0903681c070030003181500d041003c030380580c8060140a00c4000720300a0b40e00340101d01e0610b181000c81c44918050951001d07000d003002000c4000c0070b0320f945034040b2001c908200c1e00e20140c1103c141c82d10561030804e2003d034802094006055424437000714141c4100300c511400505c12000b040380d589400b00c4031008070074503c40c08506180030300304030b01c04c1c02c2c56049048500b200410203243d2440e002928000250b9001040da0380d20342da0075020740349a210798014104851070381616100c4001550201c0b0028900000011810b00c3c1c0d410b4040f04c0281001405030b15a10741e0340d801d0340751b82d10115000c01c401c40c0d00e00340c0101e21640c49124a02d048942020900e800e2500b0540681841c400755109181c6100e542d80700310f0303030001c41400507910404507a24001441c0c1d15509019003036030140310201c85081652020303501c041c1d5815211038218540070315215104d544000c1000c00078881c28000b1000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 918085611 1250 918084361 918084373
    0x61507060b151303020a08010c120518031206090a110d0f020c0111030a05010609061d0a0306060902030901110306220b12030714070b0702040e01090c0801020a03140601021e0f 77
    0x5281e9640101004503417003035405803a5150f40b95451403c842c00740300c01d40001075150404070309030b08041e00102d4105e0031807104414840b50341055149590f201e130741e042d825425090708016071850700c00c0109a00414a00003401000300c015501401841591100f156540c0d80300901010080c045e4141d80031a4000d40082000d0350311a090398425800494003180e10600f04000071420500c942900c030704550b056200d505e004c2e80c50b40d020310201403001d0b4800e90811700c040d00c00000300703500340036813001800c50101c010b030ba90a201c2040da0954405404441c2d5a81040050101e141caa42c01501142d20200410a80851b00c908101740945040c20a0980c80440c0303407581c0035a0b0102000400c0d0082c81051010039010031614600c0c0c6400307042c440d8480500c4140603c0015081c039410000f640781c0070303000026281070136640d001d0500311550040c1c01c81da9408035010340d1503509407043c0800891960545001490180e0000b580c502c400318018440c004002482003038100c04001ca903102c1b400e0201a515 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 918086861 1250 918085611 918085627
    0x1a040324050114040e030415050d0f02030a0603050d030b0105040b0c33071805090903091207090c0306050a030f140d1e08040302070314100905010e06061507060b15 72
    0x603200603c800c000d13210324a001710155203144000110b038111b03070803140035107a402586582510716030441004607280c0c0e5103401468071175801c3c074802144144191040050041d003541001d52400c0c00b800d103004189483c0c603c680506a800c001603c0480d54101c0010383c1d01c2071914480d074200b0180418503441000000721646000745442c40a82d2568814000d014007503a5161080761510105200340c62490f40001c41440700e4100820b0050713010080c501200e00e05122480420b0418003004c480310780f82e400592052003404094010310f140760050b880d040c00313401d00f4840010381d074102c0351200901080404019800b00a01d13581c40080a91981e0103551421018030070103001e04004005404000100d001d522007120300581a641c00380303405038001c212050555884c3c40765010030034020300503403007400040c44590803a030080c215030314814000450351002c40604a4030303100b000f500c0c071031090074a05c050800307a00040703060340c242540104002c03c0c0d41400c0b40100d140b10203840c004803110321001582c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 918088111 1250 918086861 918086879
    0x30f1c02010b0310021e03100306023f01081b0f030c1801050307050103110702010e040b030304030c03050106060f020a150f05090a0311010c050d051f0806010f1a0403240501 76
    0x1204d0303800c86c43c1d901002c0c0305002c2d8401c0f032244030071251400c507484524020700100d0200d07800f134800b6030780444600c4066001f454070340c200030b40801e40800d04101c2c01c0b6982c03010324003018407490050540e80e00803c0415400c04100080740340f506c010a00a03800c0b04036900c0155000c001c01e605402c0301806400c1c0114061000811000c0d09000703490081c42a04e2001480794800d205206088a44c4401c0310b08000c81c40d40111103405c0d0604c090780d402074136641188566a42031004100030341c4201f5060241a2075840c0c01425550079070f001105000390018070710001a00440c10200745a80400352941c1c4040c451441c50060045800004203d4600300402c07000c14400181c142c031490013601c1e0403500000b012169821307a080702020500040040c40310107880c1c1202c3c1c1207290800005a01c0c4c1041405089c009400c03006580c2c0400031540c030450040000c803011403082c0317001d4101940d80702408400e954078004c40b0f10452200078400c64407140d0361001000c5662062140050f056002d001d2965203141e14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 918089361 1250 918088111 918088117
    0xb10150c0302010c0c02010503060d060b090a0911030109020a181b050a1b2001030633110d0509190b0a1404150c030507140d0e030f1c02010b031002 65
    0x1240076600e403144c113041c902d01846030700482070741c16900e0610310350b55034041c40881880010110b0340b01d134803681c50400e25510301d5a40391003900560000550141e41e403c0001c440790000c01c0e1035020781d2400e24002c0150311125148015070300800b034080003d500c0c04460308002c0c510815040c2d964030446840c0c00c010b030707031203001041c1c0c00d1615582e68a98445442c0c0145010820840003001208514612181a40c04120781c1c40e42041c141400100780e50b03642c2c68641e0a409403680e00004a031034040740c0e1102c0a120b140c820703140800d460003800000004003e1580c03005004108803e011002c81d030188290348444205100500041c3d00d8000b481c1e6440441200d0342000010902080350b039071185802d034403c2e600792000c962040e20305804400d0130540981e1581c030303155011307002c1043c104000e1000c00d076040b903104400c0391008028a0f0303240f00c080005004000781820103101c2d4001c08000306020400050301c2d01c03007030543ea050801003c0800c00603401811210b0340c140d050b004103504500c3c030112540c09 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 918090611 1250 918089361 918089363
    0xd12050c071b080d08010501140a020a1113110d0518030909130f12020d03200c0a0803010312080f060108070809070f06080f060a0806010612020f0301080d020f0c0d0b10150c 76
    0x6010b081100c1008034440c03070042c072500d078004cc2d1108210304045101814007040300c483c080c02000090b449880305805598240c002008101800102c0050707020b201d201e52075000104651107460070030070741c48254680c4107034480b0034440d08130003000c280c1901031070034842c0400340d000310500c000074082d142c1400c5214900c04284007500540079000031850003400784000340c3c0004428800380ca041c000000c0302e01d8004071102c10462003112281c80000342d240c0f0003140a94050a0500b0031015503010040c000383c0300410080c403140004041c4000d0340d03001704500c0e07008442800e01c0740e520707a02d1000c0646021150b6111159946078403000203006c64100b0306440c0034805500c00340e01d4a64501c024030400045a204140c2c49a1004004000603485204d000401449981c005403800312840c5126085030030030f800c03005940d008506102c1400f501046805118001c080c042c04000e1007010003c0d40c43c010781c000c003034480301c040d00001d144080302c1e100c08400b5000c8480c001c500340c40c040300000e001940002c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 918091861 1250 918090611 918090617
    0xc061c090203150a24080a031d19030b1f2102031905060603030306151c0c170a112a060106020105010806070206091e010f050103050d12050c071b080d08010501 70
    0x3481072805c0140384164001d9a1204009096076401a40c0c00c84100450f15613505170069002a4124640e031882c445d001201c170403049400c0114198104941c0b1800e025294044040001441c0480b440d000f07221b0f13200f01d4001030046026480d9000401c1c2c7e8102e4444002503140c0243d40c84024400202c14a040d00c0501030001c130340456841506050303a038030081d1030540c0c0c41081505e5440d074413465400106094140c0c1003818001040c04071440041c0c503603140508000c10160040e0120440c190b9181035131142c0880c0c0e045c0010582c01306072550030f1144070faa540c01d11003510076020105100441d9000b40b960101d045444541e03507550000e000700400e010302d602c207004520100d030400344000b6201e0300408400c00030708507c5010809a8081c2c040017848200c05540b0340006582c24a40c07849090700a40c0610050011440b4942000304031003075130240328950901e0b100c2071041c204503c0095400156202d040c85003803840400402481c0d0581e0b0b8089040e41c403500011101d11a80100502d049031350a80b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 918093111 1250 918091861 918091901
    0x30906151703041a0702120f1c081302090604110f09011e0806011b08072d08190c080409060303120b031c0504180207050c061c090203150a 61
    0x654055240e11444c4220099080c2071106031124511075401010310303a200801a0fa202071000c000329082405c0d4844d600600d070003800c400406425842050107803e1403070715050b582407500001040752a000f41c2c401078080c100601c0056010f4441c2d5200c2d92800302841c2c0d0254071030f01400f56078400c41c1d118441c2c0c140060600f8a03c00020018141c0760540c0300c030907441d00710f2256030364001100c0e4804501c1c2040d550a01ca43c5a00000c1911071000b4052180a8640c0360400b4072101e100d040a46d04a1b2503281c0b00c840c3d20300480000c2a410401c1c1c405c402850a488001481001c9084802a980321b034050407100300005c000800100369030240302183e00c0381e160030035440405004002110380c907001e9070341c050308607450301c0c0c0083e80b212007003403561503807400e0190030710361515681e049040000140240555002880c1000d00008016202e120f01c0103c803860318298124844000c00308084c00324582640d156030f210811075038184007c0c0146032500c000800c2900c0c0282c4000090007041d000004061460 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 918094361 1250 918093111 918093149
    0x31b07050315010f090c03060b07050d11030c103b060c040e040308130615080f3d150617160f09050a0303021609060f051003090615 58
    0x1040b0090490340040b995010103450613640f18054141200081c0425607252004200601007001400005000b00002c0c200c0100310306002c0d18462107410700b00f2081d8000d0103082512100055200c20f280390010001c03420080d1040641c0120400c003032000c42c11001c660f540c01070390364900000040c40c1c0721102203502e240c40340c1c000700348584500e020341e00003480300b50001070220780a2608182c1240c8000d07401001c40c201a200c5000312031500580901d080c01011040207014820030405840b200000d000d44240302001e1410414145584540c0821004041c071300e03070b48030b02c071018550b404a201480501a02020920190311541e060182030f02003680018030901c8007a9001c0d020341f00d504000e098030034400c4181c10a5a0300d0156240c140100040641c01042c11307100c45c03003004002c40c8070703400818800000754040701c158003e0340c10440031302d4a00341e02008910031700c054910440e50141c0340c02140280303441d000c401401c901030700501101e007000081140c900c510071a1400f12515600c00380010f082c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 918095611 1250 918094361 918094393
    0xe011509020c150903090906182a1603030c0c050a050c1509030607030510120b070807020604030f18030515060a0b360904050309010906090e040f05031b070503 70
    0x1c181e509484c0390b0701c24040310400d03080c031200f40d64010748010402811500200381d44540707028100e0304400400780603a40c480011060007542c00480407400300080c20031507088048090349010701301c00317030805407503000c0b42100500520911400940000543d9000310390350415a0f40c0f274801c40300180c051002c2d11810000d400c041c0c0290b0f000c2a400401038000398460101c2207000d000041d00d180e82e04502100000b03130744070b0307031426140c24188240000f01c80c62822036001f40c13902c0002400c06043d50052010000044c1d80102082031421041c10079049062829413211501c50b0a6000201325118100b0264010303015508080d125000031201c030b140302c0c0d880300110302040c00342e0004803a10f440074450003007a0175192488022200c1ca40c8007880440d04008000900d01c02c82901d041c3c40c141c200107805541d65a10840d1400a4402424149042d03445c006000190000040005d40403d0b0b80700401e00030040c0c24400c403410360414100032407003141849106502e400d038521982e07129110348a9085100a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 918096861 1250 918095611 918095653
    0x411090601121a06070b010518102c010305010e0606061309051302030303041b0b0304020f0105210108070504050a0605030604020607030207051504180912030e011509020c 75
    0x30180d450031000350016400d00040c1001c8618020802d02d42514640140c8550014100743d0340680702104603549000305201f184c0b9070400c0d03401e25400e803081c200005121000008c0c0300f150070002c0780502c00350301e20344900c100300d601a101d0610603118000000a016054026004051002e0161203460b01d8800c01c2011910800903080c0d51046011070800c80c032413003980002d511044036440395a10a03015070010741540e100300d5040b20304410001d03030b000e0001144800341000c1c0a2180083d0f2447c1407076000680e2003c011003203d410010300188004c44030000c0c05444010040c1554441b02070f5840c2d103c22034413115103001e0701d40610300e03100004040c80150302800088800240152003107450b5502404510361118100b81d055102e468000101a00d50005100c0c005040000a90b2602d082010070200c5208901040344c0c8070f42407503118004580500d0f500d0504020341d04001071035024030000c1d6405092010040810f03900b007044005401381054008213880040381007075560b030200081d0342c921411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 918098111 1250 918096861 918096871
    0x30302270108090a1524031208160c080f0d060602010f0b03011a0609030f1504021503070e04052a09090106020d05121b070606060e0406030201053a05041109 69
    0x145c5a44100c811007615400484100890002000034050700e168440307070803440b64001c550201c01080000d010715404203130160802c642d000001ea00c000f0000d0014428480008050f00c1d0270307000a84005100a84000c94030380700f0b03011209000c4540d650001070300a0622750f0084907214101074098000740f406120b1607184110304824105c4c42000e02d000c0c8006500308014061305803040d0102c0e0300d04514204804110018002e441e0b4455242500c1403083d0140c5104410040e40c6080c020700554580100014000140c1030750005026512040b40d080c44881030302d00003410100c40f10030a15500110401450011001d1b5911070341a40d903030404a99803400746d802400003443c10300c01e40040c00309500800d9002120300f410800350489000310a016640502c104581c81075995004214080d0024103800403078a08960410117145140c00203000c1c0e102d00e1004400318602034070307501000200900fa04291000010a03071280d0000e043d042c01c01004142d4040e110a0b41c174080c0e000585c640000d40314031407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 918099361 1250 918098111 918098123
    0x6040f18061a030f1b2b020a090c09290d0911101112090a0902070c081f050609070e0f042403060612050703020607030302270108090a 59
    0x244146440c0c000c0240550b030040140c20300c005641d1071542c1da0400c0360303000040f951000703002c1e001201441e07098a102c0d12280350b40038402c0d1201041c1544000040180020f8000042d513204ca64240300280c0500d01d2a044800218504140c40007003d501409002c140c0c1d5022001c000d0004003030420740190b000261640b0b0b009c0e03400b0001c4140b08041c0e90071070a0007030f12505440b441e07950340000040034920780100d40c10006054040c042131103881004002c034180d402c03c600c14901014100800c039000e403a401001c007803980000744003040007204000c110062802c6006d44600c0c0311241141012a02c12240c05181182440007081e142d280c000f914600070991500c1e88205840c03550180500803948072031030340e03025517107008071800e0815910401c2071004a0340820244070307003540307046c03012940c2c45e40020102111071118000003800004100050b290100c403516211f100502c0c0032400391007101100034012000c9000030201c0302c803081848070b04001c01d0300d910321140d960600311543c5030004c207005040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 918100611 1250 918099361 918099401
    0x13140d02060a140d0c03020702090a0b1c030c0b0c041e06050912160305030c0d0c08040506071b270b220b0d050a03081806040b061c0b06040f 62
    0x2080d0248100f03918152102004500b88004458024101c1352209602c002083c1c00154000861601d50310041c0c0c01110024100850003c0320081040641043c8030041030030700c01301c034400c00c1c58011080e0b000329030b60001a0f10003c7c42c0103196440c158201d0307c130b8200e5884c0140c00140b9410f0707030740300c0302c0c1c0c150b032003550701c0c10f00304a803403400c03c00d1452a00f072013201f65020303400c0d6040c81d0f41c41ca480c89001450150006590700e040d4400c00914000c5e11036802410003007400804800a070b851000c0768100d4000b140c0c45038031080182050740380232607401c02000c200c043c0040000740200c00c640b80c00d03030000e01011904114507a02c210700b0703084d80d4144d007206501c80c9202098101842e0800d0040707950204090300014080807106c040344406900c40e1017910a54002c059140415a008038000e40c00a07411745501da40e54500014160348620141000b070140003c200010210780760810100c2c80c0342e000184400348594070f4102030401c0c2c1010340c0c2c0940504d00300110244d00c2ca40b5805150702c041d14032402550 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 918101861 1250 918100611 918100627
    0x10204141932130911060403020d12030b1c0c0e070507030f12020f03010905091507030506011b0605090d0e06040e090a02310b060a031e0213140d0206 66
    0x201d48500d800a0303903001c00c40b500c100029440d500655034400f6000407000030480c6460402150031000350b14424031442d000c00c03092006880f201900040607078080114a01520080380c1940a401500b0217160010f4102c00d4400010303100d07121510f03070340e07018020b0b01c12140d86910710302041e104212103450104604004400c0041d114541f90907084840345448124000304c4240c0d10141d0340020804542284040f00600c4048501d01c910307034000004800612449529041c040440480242140289503031003000076040e034000c482031034100c1007280c05c9201104e09450305100410050307a40000d14800c0c039070000c20603406103105c00703000180184214213203450100521003d48005010614034010118070701c00507242c1c00c88003044490090414100075a59440200070000720b076091580c40c42c1031441040d0340740c0b1a0002c0324400d9409140104201c0700030446108101061000017000d9440003641041074803404881c1419151084195910340d80b8404c100308800b0000c040183d40030f101088009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 918103111 1250 918101861 918101909
    0x170318060a0309050105090a110901060e0d050307021507030f021f0e070e07020f0d0512160309050604050319020c06030a0c020a05070305150a05150111030c0102041419 74
    0xc8068a01e40c40d021400551955403142542c0e4252a044800e62204c1080410071048615080032648191000303a6250b140c41c00090420007194205d500840d45000b9007401c0c048284111035109030040d02804c2581e4050000011a9200c04002e400180d80740742d0403c40b051010505890400c081034180340c407480d405004500800e514a40c0d00c200307210303440e4005000207000c03980034411f11441e0042c01d00103500c07080c07041c10580101d424100700001003201d1b415a07400515030316007013480b800d542c00327070200141c505400a24258002500d507200701c408010410600200400301c920303c4429900b1003002059059076104c941e441c0e0143c0c00b060500c0060080c01d007a84c0191b03d021894411900d200c1c070652202810f001058100352100d4214001000c102041e00c421150440c40240c1c0030032481c60301000241d040381440326401d04020048061980510040090361b46020021008541d03aa5503000e040d41e46c120795004042c001c1100750817540c02800d0043e10a4115283d450010040c0b4254034144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 918104361 1250 918103111 918103117
    0x50a030807020f0a0c0512060c0d0c0c150b10050708030a181208010603050708090318270603010b03030f041a070c090b0f0307150503150301020a0917031806 69
    0x14100314425880354800d900010419007142501a501701c4110605040c10302c50940c5590f4142002903004200703002622a2190131140c40720741c01480064000450001181c01c0181c3e004040e0110b035540503806107501040c0d1112502c42c0046070038043d503900709030301034403a03028188001c0c01019051000400d6200c180e0001040a5006806a0282c59441d41c0301c003aa00240c001060005171010300500c9116010300c81caa0300b12005046c122824074205102d030b40c1e02d10816000100f2148440061603041d00d03400f2403000d41c901e804286803109a0b506c000315064000459156102c1d600748268580c59040200c1121134140c1d0301d4400c0d074980342c10035100c1e0030341400c03031040a04050010048640403401c2c01900e82c014010103c03000c141424003004000e85100820364143c80398005080400007820b01c00d00d00740404860703040580e265a21481300340340c09006c030801c5a40550000880610403648500741780182d0b844502c1415201d06070b50180c0703540303004415414918203600d040b00c009074640b131805 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 918105611 1250 918104361 918104371
    0xe01030b04051513021303081b0613030f030f02160201090e04020109030b09150a02030601030506031c0f0915050c1011030601050f0720211908120106090303120207050a0308 76
    0x146c81c02054140d03208001c0004d0b030041d9200000030400310302d907510100000c207041956400820960900b9100b0107819401203000805001605100008060194106102140320303032500715102c1d0b0420b6601c9142040e0103030304a00255148001190711004001c20324050394040e5200c0d080c4a00b503544a081c10031340074103210850b00c1103240d895840304210b04490b100300c0c0541805616420f0500024040d20005800a40302c3d40044120095203001e04500c401c044840307140003500c98903000c405079035803207c64200c01c800c40300701d20040ba040f5410200800d03802180c0401c5518050f88481e104049a03014101e1786410071040000c6803544d0700c02c601404031544030100c524582011640d6100c1d19014400d0700b5540c00d2050b10003100140307025600115000400b50001345120382d00344145454807071200f8500400221403142c1c2c0140021082915180820000751100c80e5031652405031050358544400c500056455084900d040074900030381d40065030201c002c1c911704640755000d0724459070081c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 918106861 1250 918105611 918105649
    0x30a0e1002030709092901050a0c0206070b040309050a06140d0f1d0105060f0105191103070c0e071704020f04020d020d0b09061002062d01060e01030b040515 69
    0x25148510600d500c0258040c400544648909a1401001c48203450369013035801a1080395498400108403041c1040a000c0000d1030001e80c0d4940341d5038190f03040c480342c0c1c901a42022001c075562042190501d612070082e40030340c0302c2c00300e002d0f41c400400c01c008000e4000c0d10300143c031803043e0720710080130b0b28043d1014805405020401150010065040b82d00052043c200340d1121036110644400c02c0c4075050308550291800c0c03001d0070390740001138910310580a404802842c0c00710b5168040f4461458464801c512030140c9a55800c2824003001c08041801900707035000c3c00c0c101061105004411140215150807055400c9584507001c0041e4001c0000d0241c1d0450b4003045559102e920501c000c2a021030b07600c3d80011307946041c0050240c0208020072160140e55075085002c00c164001407615800340000841140803404126032100c030780c101d40c03900454180e49000102e203007900820030f0500f840b42a42c00b044500059420002500ca041d10038a1289850745400f07181030038411a89113401242c0c4c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 918108111 1250 918106861 918106873
    0x3020f120702100c09050a0323120310050a05090a0b0a03060c0908060604020304080702100c0609060501210c140319030804031418060306010c050708030408120f030a0e 74
    0x2410a84400408072505401a040f200e405a00c0c0200c500c14000802120310b03010304098200700c00304445000754003000e403041070301c0d134201c40c89200034a0b54400c000a55000b51840100070f440031844a802c10b81f021101c00f80101800b01741030030256a00d4084030002815442c1640384c04031000c00518044899a070402041207000c0003003502401003904103049503881603200c0749094001404c03d080030303045500c200c1c010000d02011508103010384d0300064046403007140001c00c0720800c0e209010b84010003820641032103038101c10b010a660006048400903038040c80707440c4032040f220520400d540001004201c04c90380604c188280c0d02c6000d4030ba824054100c03141902d04042503080c0c0000300c4401c1b8005840f001c100010164488880c0721b00009101c4c5040c282035440d0b018500000002d200340b07018210110001d9526071240000010346504030042e10441c648943ca02074a03136106002d010600d104a16100e4555245a021102c1c0c0704030301d611450a5440c0c4c0c66071600036242c0183c0d407031420f02c504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 918109361 1250 918108111 918108127
    0x8040f06050a0f08040f121e0201020304020f010806030709050a020306090a0c02210c060c03060a32150c07081603240219050408010b06070f02150d0606050d0b04180303020f 76
    0x1591108203001c59480e19003145d00c81065135840045232004040031a4014424400103031600c040c242130209090038201020b5139124003082c5852515030001a02900345010b0140501d1503500840c004c80c0b05485025440d9900c0300403078151150700e0000740050f8450001c2c03407000c6288007030990213210142007030f9107005220001a85800000d580401307001c034000090100524011302000d0081040100d40c0703a0f203191800100c4005d00301c00c03010000300e4111a002502c1d5565017031000818040c443e08a03a128004545019074a03a110b0180c00c176648100d00c0c600044c0700070425044c08903a4001c50358003003441c0c3e58044c9460003401804018502e9024481078524012140c2c0e04400302045540c1c0c152124941400300b03003943c0803060a43d000b071000300280000b02c0d8000c421101901d406540c020001d0103500b648203042c0c41034818445090346814404190241d01c0b40c001c11041c0350030f8000b40705903100c840c100300440302c42c0c0a0301c4614000c00042d80d40060300a40213040d850300324850b46c900780384003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 918110611 1250 918109361 918109373
    0xf0f0601030b0409062f031b0d14060a0609230d300519050c07030606090204090e0d08161707170901271401020708040f06050a0f08040f 60
    0x19189080b905103888140c4586c212000b180100c41003a000803000c80c3c000c44051040743e040c80f02401000f0a80072010504032144490700846001410100d0200a20a45208042e03040d81040d2190b51040225410000d800b41c41071060100380c0c1c5d0a00104e08035103400200b89140744001c021003030341003032031008402e0100d0200e25281d125240412040600e42c036050300380417241e52001e0f81d0700082c0407050001c0d034a1230500c1001d290300c0e4009400c1140c5c3d5200461002403402c0000e48c0000e05071b0b414484041030b80c50058000d04115001c260b020b000e01200d81030520340718880404d0400c0022003400000b141c0c45003440180c1120801030506c4084941d0003460912000e90480350326011400c8070422161104400d00001c2d84800c81600030403650700564a25245031040a00c542640c0c0e001803510300c14805440081502480a94021580c8001c0341c80d00e411260410b2103100100140100e001901c076002e502180d040204558810305402102d820507250998046c0081d28a80310740360340900000c01c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 918111861 1250 918110611 918110621
    0x80c0d1505090307051507050711210318010507080906030c040902130311030a02010f0522170d09030302060712090203011e06060e010e0603072a030f080f0f0601030b04 74
    0x8203000c050f40d0384071168140641b0b0840a14080701ea0241c01c54204041985e10a0580350f440d9404804543c0100001c0c000809a50710714003002030740241421b459480c0c0300004002c10712107455102c141c0e11542200015101400750303090140c0140400c11085010f03180600065501403881114130b41047d440c1c4025004980022465900d20181034106005000703051215868440044006140b0302030a980020908078024011005209012400440c00b101c42c4040c112140081840d0041950344c4544004a0511601502c505400341801442c0c00c14400d0b044507060702d801d030b0000c04a03a1182c8508440410808454031241c4c0d81d20601440140d030203008201c510045a2424046103403143c00f06c60480e00f840c0e02003000c1c0902c0c1c240c403105690300a8500c0b040c4400c1190034545980d10602c0a0780e070b080300140d40c84000c80c03001c204900102c0c0e0303000e06070b0f16550180c0d070b41c1c2c0716450500c1401d0742d45501c2544c2074560303204010001100050301c0084107510600c180740215040c03e1210103c0d0a0394 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 918113111 1250 918111861 918111871
    0xa0c1416051204051305090c360c03130321020304020a050a05030c0118080a080712020d0e0d06110310031b1d040303090203030d0e010e0601080c0d1505 67
    0x2261032000e22040c814108000c1c0420b2007410511494149454001268141100c001c9005d25403204000340c064802480f210302a0000503201c2d070562010010041115130628040700921108408807180c09241c405600d0311036101d22224500c0d5444503820046001d0304031500318200603510540c00402d00641c100f05481e01d05070328025803203041610400004040b5a00014007910403d0f0003000140d80020312a05010803c0c05e004c0d10842c5c1e01c410310020400d0b50781015040c0e10402d4040b90800c4105d0004000031400340c07118029651050741c080340c0740c03100541c241c000550030021030b05051a04015001000c0c0c03241400142c0e681094401d250540c1049604081c0044280310400c203000e1001c1c03807403690407410700341e0b1103039141028881d0500085101e50500b2020002000400f01802640004030054004040760307101c0c3c0c0494800e00181100c42103d000c203500300005040c95140c0082c6040c149c49441c809480f540c03032028203011220038001000d89241010403070061030b582c52071007181d01071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 918114361 1250 918113111 918113137
    0x2061e01271103070e03011509020f0705010903050a12020702010905010f021005190f0b100315090509060403030b040c0806040218040510080f060705090907050d020c012702090a0c14 80
    0x44c1c070703002c80041c1403460080196802641001031130140b464180c02180b06032007038201c0061b100c52040c2c064108502600c0e8008140e58a0030102c842410b8222018000c096403a50700e0040000003c0c0c070070b009900410f8402400300d10140c0091045600404a030702c28041140f044503200c446803494030313069460a95508804902556010fa138408250058041d09041c4503010b101003041c071808580018101c03080c44080560b9540700080c2c0310304000c4480000d1010382c5090045050006069031030b00c2c1c05507400c5000c030786440c50340c80190a050044020003541c6440d05a0107030360795002e00c030203988014a01588003414007008585a981c03441803d00030080c0c8d4200e000024201003c4030700c1c014445105000c1030340a44204400305903c507040300d038140b505440c504069190b2035070a441a0240c9840801014004201c0e6606140c0544c44041c1c10840c0c81141e106082070084030065031144290301a402c54698000201030702c009410540c5483c2440c5007030180d03002e1001640b0380582200d5081212 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 918115611 1250 918114361 918114367
    0x6030302060a02041410020304030c090614041a2b0507030b07110616020a0c0902071a091b0a050306011e0f0f090e1e0d02061e012711 59
    0x6240e4100001a8000280c0d1811441d00e82003121104241c0811803105220380700d00306540c0030803031003402034800540c0d00910324041d558540320302d08050492030046802d04c5c440080031840da803406005a0070a401d080c032500c2411543c060621218000300300c0e4502815492003415000401240b20406001e0b0064000d402428210720304900754500180c41c100c20030070725495020540342d01288180d041510518051516074401ca8140c1c2400001040030307008070803291000592a641e0b4000382420b80c031456280150411442e444c411000301500c11010a03481340031528000034895940c102c65075002020b25003070036a10000a0324000c001d030012007421042140022185407103d0600c0b000c4c10103203d18040c3c803814241c40007000e80c10391207030014081d260860101548000d210b210130100c859442c2c001d000d0a004621944c8241040d02e010040c452800080e00701c4502c41d554034880d00060704a10310b164a81044090700766001c00b204940f1060070291413004000b1807240003080c402d1040c040361 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 918116861 1250 918115611 918115613
    0x220902090a06050a0b030a09060c0906020c01020106260106210201020d0c03020606040519050103121b0206070204020f310501050910030203090a020604180b18060f0619030603 77
    0x6110311020308071085090400600740201c4d03071015442420b850084181584036950b04480801408945002409043c68003035181902c5903c00005426140660200d07400540003030012030032142c892055402c801102c5a201c14000305000c800104081070304000720300d42d07032600401d60103160b51280008a080d1781d20314807421940c050004544c1580c00d41413a01154100e9100691510001450240301c0da03541c0000821801c850030034604008500d407401c025035a100e20f00301000321441c1594001182050403621107403178603548071244855001d0542410144170f50f0070b0001035044000c1030550184148159510050400c09044441070080c180d54002100108039004499207900081c3c10080700f0071207400c00361141003030000c098500d03240040c1d80f0b5664a20032800c040911400950000300090006140d003e0b100380d615031644001d50410175000310300c08110700ca64070316024070101e582c1b010000e8402e103401c40e011410f582010381903074902422101800b00e0304180030b8049000c26603441c0c00784 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 918118111 1250 918116861 918116869
    0x90103060f142e0c05070b040819020a05090f0a0b0a0303051c110c06010906090504020d08030c0717030f0106020c01050d11070203030c0304060f030606120b220902 72
    0x4401030801810140c1d0240c180714000561a858240715401800c07541140848403010300c3c40b25030b10105012003440c3d4070071180d000070b0242004c4541924148103c600100f0046866002c4804035107105008090b40010301540602c8543e04540a80c1d012101300c40010b81d5840300b400d40e910900c60181c40f42c09a02d0f141d0101003c407a18003500038080c0c2c016404c02e00002c1d800008480c007010390080c081e1854001254003d020300741c0c5001c4204984000b0856602009000940c1410703520007280034040d07a51941e00c984102c03417040340d01075800849500c1500101c1c1240d0000c40d048522022a140341254503264070340c0200d440302598002040020410010844025515003d00394500c094030f03c0c9540b1b80e00003031280c09070f04910600e0a90b0b4122079180ca94810080b03401c0c003680034090300e13100d1040c504e800352240c001e4460302d0b01064481400000c8a84a80305100c20340e43d00c3c1e00e40c1c9091a503c1c0b4100e000800c492100250030803500402e100900f20841c1c03448000c409454004503240d103480c4184 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 918119361 1250 918118111 918118121
    0x90717010603020d0201180305032124010f09090c0c1406011a16020d0f17041d07121109030c0f0d0210020a0f03021b0904030e0613030c0902090103 65
    0x605901d0400306100590701c24029004058092800860540045002010f20456079200428500c400244c4401e0120b0804107840048c0216103504815682c2d400b141c95440d214040c10322400c032500102002e250b0040709207000c41201d5241c00b102c000c0e103d42c030a0003100c54401c461004514088074050400c46040d402d030241034141d10290bd02549440c498510340b05040740d07581000000400c001c0c0206001d40ca11545058004080e01181820fa0525100c244140c3e0001c0e1510040400c00b070000c1041c4800f11401c0b200344904640d00c0346080c03088443c0b9100043d08080802c04892003007a103a80c503900414040d000d05001240c0c0d80c980000406150115900543d4042d00045004d00c80319910802024000e507016110940c0131110020128103080300000c0080c91007515400540526038001915007045891100103c0d000000c0c5040010112044500500254480d5100c00540c2400d40140c0003c4c07083c90010710705242c4a6032a0280194240c004104495011070401d90540c0d042c0a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 918120611 1250 918119361 918119399
    0xa051b0607200d080105041e02131e080c0f0d02030307050706090906081e03130905040c1a07060e10060608090105060f0310021305040507031b020d020c0d15050907 72
    0x80c0102051020003a1200340140301b8948515507501c1c42d0340c15080c1c08602c080c43d010070a6011544d40ca8003000d4016590317200c0c012204000803980c01964040940c1818105a5540c0401480300003000000c01c4035008545241c150440c41182c82100162010000f03800c0261150000c0c3c0f034101e0400c4d50050034100700d0b60114030001c0c10900304100400010945280c00d4001205058a048800044034030354860075244000000d00002c001a043d8800d1380302c140601d2142d448030301016580e0b00e255540d10b1150f000c59500300b60811400002884540c8804510f42040050742c034440c203540c4200d000c45e00743c3c1e84900e000c20ba8401c100201d00e5004c2c07042039404001180c2d4580020010008240d8800007010412515030f400940b91a0070b07641b6081420040000810901c00c910340386100502501c0c0b14110018903146414040107801d0011a516005908550041420214450070044041c1c407180d42a00d04100d001500c44101c00b070360288030710454003035000f40038032464012500c00506110390 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 918121861 1250 918120611 918120613
    0x7300305091008011a030903041a0c160f1404060803030c070506060d0309030b0c0c0a03110d170604020a031103010e1b120a1a2805030a02060a051b060720 68
    0x50100545e141545407801c40e915140944a54514140b1403461180e60007003c5518155650f021071207400030300901a1090300402d41c0c0c802c083c072544003078001d85280074200f00300c00303880410700001c4000104001c0e0414010004104965100d010a065610959260a0b54640040c040e02401010402035801c14800d5a0301001c12505031001010015240401440700390707500045440c13400c951003600d4003030a022080c1c40c0584528500075140074815410000700f8060001d403240d03c2400344040344202c00b0341102200e455652501040000d5100c040c85006043d5588040380c82c90385c40b6406980a055407201900a40c105106c112203a0400c1005071150074104200c0400888003100714581c0000305100082000091038480c15040c2c0c102121a81c1c106404405505030703418903086011b882c008404103024140c1c0c0700c1d4140364031b904c03002c500030b90450070403c091030101d44102d0080c03440c0b0243c0c05124450007032040000c1c1c01c1c500c040e140000010714040f0305170502040300301c90030380c0703040860 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 918123111 1250 918121861 918121877
    0x10219080a0e070312030507140a17090a0c031203200301050f0613210213060e060d02030601050f041b02030d0c030b01020616021c031a040b03073003050910 69
    0x745d14800d48880c101500001c25484d200842e003428003441107003080d00040c002c03041e12800c02c000010002220040f4091640010034082000211f000c0b40801071690404c00101d1502d055445607002141d050703601c0420560b0303503052a2030755540c807042298848005001c040d80d9501d45410448000ca5000107140f003111b00300034072100165107032900421030740c12006c1d80e0717004500200c0040c558842d04401a400c080e1041240210002d02d601010640707404200746021900d90506000d290707460301c00002d4265215000600ca580703801d89900c00c100300014804501c103003004100034600b0206144803009a40041084220510107000300000000c5900d0100003e15080d00000e5481901810010b07280104103820141c4c03e10038070101d5030002e0100b079600032841c0b0a600050091441e08011696981110404050381c68070b03000e600c0e910344000300102074060a1000c0c00030305284a020100c00710860480b1410302240307241084800900075250161200000428009121528071109003080940 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 918124361 1250 918123111 918123113
    0x310090c0b0c011508060f1308090414040605010614070611160f0c06030504020d02100c050105151206070f08131208040212061014030312010b03010f14010e01050a02010219080a0e0703 81
    0x780b841f10390151951060150100c25401d00c02180d100e100500ba40150506809070300c1c0d020400c1206024a124042c20000c0d60380c0c821089a40d0721103c589401a40409c000d0078000c00c0302904108000103010048a203020000743c18410040450f240c100d540c1d15411070b17020140400300a00f00300401aa003018400f505d41680011140352080d48000c2c4282c0d640703000e81c0b010521507280d1009c2c80e40e00100820241c200555200100920303c08464403a0900b1442c815050001090780c42c010390321034503012640e202e400400c0e0f544200040050000c101d612032080d0200d0709482032401440c40a8880e07003258105801400b002908001d03020149a00407004e0001c0041084408030455004045da40010104940040c0c258401c1c4c16000c411051100008031b8031107200c2c07000b0b5040303400e090a581050740d5130719080800103050a0700c3c580401c0d400c000489942d402400101101c00c003071710005140038610b90340c1c9941070004030342000000b841d1200300a0111400c2c4101c20440352186c00030031104d072039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 918125611 1250 918124361 918124381
    0xc0f0f0d120b0d0f0312050903090f0118030201030518030301031511091f090902030109020d150e13033b0316051e03060c0a0207050f0310090c0b0c01150806 69
    0x400c0d8008101d1042da984000c02c0c50320842886e004170044007000c0c801410000034042d5640c02801c0320610a00e103c1034000000c0d80552060100c040c1c0c3c901941031070b00e1031900190010301005000100c10020540e0314070b16400305000644c041e61040c4107800c6070090001c00d110803110380000b541490319041000d0f90055445010f1000d00c226142c2d030380c40c2564404002212010010352140c02d20500120002c11f000c4420b4010f48200c080810003088030407200c60b000e09018026224584c118401c01340030641442c54040070f160454007a041c040d0340124031038604014040806800b4141c41071490880f9800c217403140180b401c003113049000b42448a041100c00304d6203042c5100f001d02c1800d030a84881b150140c01051030700c52100040030b560145c603000c000440300381e1002c801c01c0018003805201141c640f504000155452a01400071b182e104415043e04009198a90040d205604098800108c4061640080c26210740c15400410041c0712032404e000b10f030005800421003608180100040011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 918126861 1250 918125611 918125629
    0xf0402031b0301060f0905090c0f130c0309150539090406030c03081309050106410a0809060930070b04050d03110f0c0f0f0d120b 57
    0x2240d4980c10600103000a40142000d0b401700c8540c3c10700e43d10004280c14260300480c41407020344155000c18944000f08420040030602160780103800001551261070f0640c81110003052906000a842c8116143c540358800d40c40c8404030300646031000c2080c846070000000c55040f14a403600100c0c416941c8010780c507444070b4040c6030f080c4140494010411382e503d401c80c1d0029908019400041a1217050040c0994004000010340988446d80051981c6480c41001e0407281656a0100c486026000b03140c4021b02034140001c0507410075452130000c15800b071041007040b8040c0c58065a0351034240c80134061000003800c034440358011404001070500c000c06c81d0b406400c044007402c07030103014502c030035882c24031910300c0f03155001000b046141c01c02080b448007601582c0100e044030f28402001200300c0076a08603c2d12106072140a00140c0b09603080c440c01742604d51060b20990302e201c100000014501400200c0041441d841080410f50703035600b010410184060390303001800310390381000105000038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 918128111 1250 918126861 918126883
    0x12040c170c1c1b0905010501090807241e0504080f07050306040b091507021b04092303040509240a0609060f0302040509040c0303080c0a08010306110f0f040e0f040203 73
    0x9852946001c000720030a043c3c55a102810035414580c1e11607141c0c40052109014487c00300c1d00d03811010580300d000007905400c0780c4410100d520030f01070f11078080c45101100b4000a060029590403441c481648140010028015503186512030349000c410500d030049101e009043c6402c806420320450301c000c901c2e1544030b5080524140d507074075880c02d11b03442e01b110801518440310089003800301d22a40800c0c004030541c5200c80300002c0da0325080410040340d9441400514030480c10b5280b0f189204024110040c004100c010340782810340e1100440c11002c801c448440912109602c00b024412480c24041421001038400204c0f680c240107000d031000700c0a0042c9404d000c0715240c00031013281300b50111005050003810415150502d86810311a41c44107000403808184241c3c009041076469400350b41045005590b20b0000ea4070f1030b241d1100070202000c48a00c00340c0c0c108007028040d00108000c103a105d03501c1100580d254688800c5405403a0042c1003203010b000d104003030202596000030034028107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 918129361 1250 918128111 918128149
    0xd080703090506061c050a030f020d11191e0606030204060f030308012312060603010507020c1c060b040c080f0a06030807060209040b0a06020f0708070617070512040c170c 75
    0xd000084105c1e40710030290780000703081c0c2c481e0000c90420558070070b404243c1c80724a0f4003140d1a00b0b400c4d1030190b070041c405482c4c941c0590301c6500c941d035682819101c00990300d4000d004540e00a018450544c1149005500540b2110344a2600b0804c5090a200706c100500d205c00c04002110306582d0300a002013010b214903080c14012074143e82880e06820700d08085581c000f00215088000d2403602c54548000311000b600c00d5207040d00243c3c405002154003200b01500034180d50265818202620b00d02d9041882503d240c1d564212046080e106c510a400b0324030415218030b9058074004481e1400c02100a11643e20541090020000a84404103071317a07002d0742c040e002603140c0d40203801160041c5403001f551070f0f11444440e00082c0351a00802c50a0030b25640900713542a1a44500000f03036201568480c00000132201c800d030500f42001c54001341c0d0866002c0c68080d25107091880c10309511001074500b501c22540307800c010080c62605a105040b2907a4040c043c1c01320b40b003c0c4e130004a050490b62401c1600d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 918130611 1250 918129361 918129379
    0x21524060406351311090f0411010c0309121b08030c0d09050306040206090607150f060806011d0c0c010c030f1b081612090606171606051309020c0d08070309050606 72
    0x4100881d110076030170280c090454112490200ba690715180d1060314162007011104061900551140c0403800c1e01a806885110310385103400702c80c420161003014107031a0300c1c034841814815448107905a00080082c1c1000b55140d6410450b2a81031042408501003400f0034080c0c1000540c41c0441c1440e40250100c900d140c5400609011808621407034000070880301d500d030700d9000301811030362224010f507040880c208815078580d880e00713a03a50000e005120161600c518503d040c80c5408000a0f03000515008090070281050310440c01d42c0c00000851003c03940b5881034080c504402d1048125120f0010010014042410343c064641c64003e00120004e0810214107251540030300d101c4080204a4a800c1151209508120004101c00d001d4030308003c80b01c040401c44090002485800101e0581008600a1400b01e06807842d82c080300304240307051002c20780000d05201034400340000307581c5c0320081e1140308107044006100032001042035081c03500e01700144010401c00944a54451001e0b907103104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 918131861 1250 918130611 918130613
    0x315070804060e060f07030f0b1804081314090a020301120314090303220e1915120b18070b07060e010216050a05010b010215240604063513 61
    0x142104401000c1ca6101c4d1100b8420060b03036510005104000e143e40420508080e10014001e42e060034280d10f510020f2600400c400ca0807448950390494070480355246401e40301c40c0107003640350603944080d03600f50889880114a04240c180640c0c01401c256085140d581003130300141036070b194401d001d0100107001d400e1000b0642d0440480e021001c7c0241225204d00c1680c00e2082b01191000c42101e40c03015011001a803c1c0c0d5038104a4010240c128414000310502815000105901100405020b071140d0700080c3c544034003c01100c0c11401034550076101d00d0050380c00d04101ea1000300d04009a404a102001031451100640380100e078811400b0450801c1c121295000e40203000d5108981030b07045808000b0402d00013a46494688500001d1181c021040b0059071201012211488451804030020300180035040081400105440000120100420114405410942115020408040c41c034a120185602c061200968a0703030348101c8550101c010510704c01014080e0601d046076964094 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 918133111 1250 918131861 918131873
    0x903080f1306021c11090f090903070c030b06120a112403090106030210032304020409050a03091a040305030703111c0201090b1e06100e03030301080a020109050315070804 75
    0x40505030040e03000c2d5110020130643c1c203003042c10700e6503000c80c2c18a804060b4405800803015100c2c1c05a0080444021844010a101c2d00840080c040007240c001046503400081000056201441c0541c440f44250320f1302034148404905659028000b592090207032a0014601e0005003144410651741c7c607158103002810b451841da8010303041d401c0c00742c02004110a414056200e0320841c2d000300d82104500312030300000e0b4110b540051b01100540344181b898100c41c0c0d00b405690f0740061011b00009811001c58032140c2c104140d07903404900042002004003c0c48801042c0d0200303854211950ba440c1030301e07680d140b6035a445113240060074005401d05040c00340206200180c402d402d42c2c0001000741c900d11130001e00818810f001150070078200800324041c0c5003070040d07200138840ea51301498055121710003081207080045c2c0380c01041200d40d80c2100b109803401e001441c02006440020b100114403880007403c010b50642142c0d01a61010595547c524007990101d0f4000c1c542342030800c040d8a85045c89 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 918134361 1250 918133111 918133141
    0xd151409011703042c0f0f0112030905220516120507021f09120503130b15060403051018080d0c0504091b02060123060f130f090c030903080f 62
    0x3000c2d1000e03542c0d4508680529400d03c01d08101003031400b20010390700c071b81280c100315400742d5001c0341000d9180010301c01d012002907400c2159010b81896001541d0340c900081d841600ca20350250f00c56190b81102e82114580d0140981042c02e401c29949407484004005103100c4200034200141c81d1903a003c00c060a00034080e18080841910240c1d10740d080c401c0e00c0001401314884110381d200304e65030040c00b40601c520107503030003820601c0c4000310007102c0b515102d2811002030002c0700d182404050281e84d56a44400420045100c0c1e406070102c05000c1000c3d40854610200030f0003140706011151002900310381c226020039058070f400082041c01c1500c100e6082c01142c02c5810302c03070316024900550303007920110010128959421100383d6a01c82d00440916022000c50450a56071001b04403450f191100c0034241c207450074160241400d510103006140480e8550181c2c03210b54500c07038180040c0340b0707500400703003e8209800c0900c050b52503541c00030402c140042c02d40036006402c03030124034412034544503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 918135611 1250 918134361 918134369
    0x1509020402030103230d051b07170f07080102030717100308070c030b06152506021201060f0804050d080702340f0b0f031b0d15140901170304 62
    0x421516503840349012a0317003010031410300a80d42d04601a00a040b540003c4014401c10b60360b07502400c0403a900080303250414000310304c06107400380300004900d215028182c01501003010000384568504c00304018140710b003681000d485039004108000d0b9450300a5220005640210141d60362592020703010588030b90307a508003d1078141c000802030b003800581480c51007038a00600f580700c5640c90b0041003040e8480044e01d90300c103045041c881c0b082c11600da55241c461082144254800380c4040342e80d80b03002c0342e01419011034a881050014070801e940110150038031030301814100640e040544940303607281c0c0c120390343c030082165120003e6160342c0700380020340c0000c1001c600810080040610302015802801a5030302c100000100090740054036003030307101120041c514051820303800010358030301940021300c4650401c25035058070503410005001004030051155002880503440e48148441855036846504420141907007003c1942e9010300707090441c1e201810301c000451101d5011402c500490380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 918136861 1250 918135611 918135619
    0x709082a0d0c0b030a0506090f150d0f0c03050601121502090a09020d1b0c02010c11030a0203160504060504061809030e180901111905090d060509030a170c07150902 72
    0xb1001034103120080c05503005041c0c482041c0b055a4881084c419110011107414481c00310003804104854182603034080d081001401d0414002c003151036100c00d03029110011281f0b1196400b0400034043c06201d81c80c09400818120008070f1180e80302c035420002d0400c0c840038100c6e40000c0310b48c050750f1848214001800070740c2d4103540b43c64003ca1041c0081c000003000c0041c034040c040360301000703520900390750003143d9050715140e03604201500d48608106010038180d4140c40352904040c00340ea010414038003000e00d500000c641150418007408143c50952388001c0c0140c0c2050000d00085080d20104aa50241804001265441400e04a40190702e0381c0360313180c01512036600340c882c17809442c006e07a00c60038910009021040f9201da000d00c2c18401d1010000c9207071501c206924a00e0321a80061185e01b00c0200700e1491039000b921100c0c1202d40a590f0303034100e039100050a80304240c02100c003884d0b61115080030f810518000e0a80201445181002800c480d00d8490b0f01d403c2e000254024283c40390042c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 918138111 1250 918136861 918136883
    0xc0a020c0a030501020c0c030304050d0b0907051906031107030816090906060c051b0a06050a11010501141804030f050a11030c2104060c2d0b0709082a0d 67
    0x818514000d44c401c2420040c14058560307d80d4043c1400411034048400c058140d034445012034039154405c04021748030007024002c582000a55a48446040d1001703c11f0010511841d13217800300160480c7c600743c40c1807040780c1040c00040b000c2600482c406600041c43c002d00c003101c9001c40c0c012038034100c00d84c11080c0c2452903e4404242541c7c010010b40915124030121340c0c0c1c40b440000c564249440e02080f6a07840881c10030103105442c45140900842c0005c1c0c2442c00e00151212142400d40b9403d0304070311072084980c440c2803440e1600582001c1103444000701c0b00902d04003910010040c584d4070355400306000c2c000034464103142c80b504030041a40980401d890300c03202c01c026105d8540500e0045841c0c00042c149054600300400000c8030b01b00c414a031111000d035462543c0701d84485920740403541c003005010401c001009448003110b81c0b448c2c4907984040c0a0b01c1c00791406485450b198018810079405052010764585a007640c10718440700740034800410101c0900090b00c10940f41400a00d80a00a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 918139361 1250 918138111 918138113
    0x902030607030f060806010308042705040b160e4509010b030d050706090201120905011b030e070506130b130305210d050c0d180c09050405060c0a020c0a03 68
    0x5901000e400f03882c101e002e000595a502e81c0980e03421080c04042e000ea10200400c10600101050003c01c8407480179085008903840d01307240007141c8044038150341180c110020441e03228240c03a008a00c2d070f200d03404c0078414140c55801246484200c020070748807038400c4680800a0ba800074078020712180718500c01005503107030440b5003003003a00140c59a4400b50300b0f141124100d0b2402040d52524054642d641506015560b120300c4003414102d0402d0b8140130441030009410320030ba004101c64640a03000200329102158030f909014000600507104252402800742c10700c00e004110041190400c440d84e80c0c880005200e25290b400040e84080040ba00004007242e00000c00c8601d4021240030707400b542c100307403a1092074401204da9040c1c5100c840700204440c42003003107140d01c46504101190101c508040c100180541250900f4001c0c04120130044144820411030a1400000e84a00c00043c090740c00d00d6558207a0b1600c01508074000e039200410400000c038803c0081400100006241002840d60b03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 918140611 1250 918139361 918139367
    0xa060512040c0b2107050403030518210a03020610080a0b06180709061806090902210106180807081c122a0305060609010f050d0204030803010806100e06010e01030902030607 76
    0x13615010344920400440014a00e034000c0060300c040301c2d0103440d941e20b400401d404541c00f04030100d820b61307881442d03900703095904401320f2100420615100014240000d9600b00649400d0000f08100d218121610091000040124040484135880401e0a131140c640f0000500c403880401d101003a5007609a0030095500e60000d0144111a042d44607140d6106542d0862a003d421501038003010428024080007551001c3d80140011030140b454088119001400001d1210080c1e000b1030000721301110030028004071040c90401880d03218000d0065500c0c03c010603450f8106518240891020103c203a00224018138022082000c01c1604201e01200e0380300c4007480c60b440ca000380f215200041da0590716503020b40305d51030240300020701013401c10128900445820b1710708000c0c2c10401006114045042c600c0340041c0018512401c4c00a8996041c500b50764a0f0031001400001c8065290300200002c0c810642e22a0308640d080c40d0602440d0714020068010303200c2414029014418101007011141c0c2c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 918141861 1250 918140611 918140647
    0x20c100e06030a0c080a05091506030c030706031a18040303230403020a0303180302060105210105130302120f0901050306060909040f02030c0f03120a030e07120201030501050a060512040c0b 83
    0x5041c5c0c44100c4940ca6078101c100840d00c0c11964122154001010310400880c0003018903800b4500070100e940700c44050022a052030065848200807a444446d8188945518109280402000e45500310031201102005c03100c90406070010b018941c0d01c000310720320034403580c6c00c00240429108007107001c0e08280c40d0082d503da90300c101c1075000a06c1c144c05084900d8840000c4050744c2c1e0943e0040036139034200340070040000031800006101001c841b0380e40d28480c0c1c0c28014a8828a0111080e9440e2030240c100a401d081074a0708810004104000200501c04180140d501c2c0c2102840e00a07281d0303407590041001d40c444d0a546552200d076503400c01c07041100207411550818170070743c16201008911410b010032080c03e00c2100361b058004c118120b8000c0e18090180117992038600d00401c541400801107401c008440e0000c0345d0b8204011110310540d40c00d40503c5005000940e28280c54502d0040d00034103600440d0071a440b2541c10b00701040c02d20401407903041c0a0020600b0b8196100e0014125030b00c800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 918143111 1250 918141861 918141881
    0x7090b0a0518010e150d0b07020c030a03020a1101050a120504020a0f121b060e0d06201e030105090c09040e250504020705060c3f1006020c100e06030a 66
    0x7132036903000596040c1101c1d4521340328540a0072034808100c1343e5940849140e00244600110301c1401c18040c160703a01005541035190198002d000c40d85600d0030080d05022085c05094180042001810482d590001805180d42c10100300025503032580d200148200045038070800c0705031020000422480c0c0c81c0c02125142a104c1e183c00d1030b131048150745865510040e8440c0e0000704010604c2d50002d4108030012000f030512902d0002502060300110004100c0d040280005055010840c4018143c520480c0c0200341c0b1140601401d56140100103400c0b484024603c90f10341e2004110a0159121034010040c00c0c001c54003503543c0001041500402840003880c2481c80050210001440e42404d1007165021900f28014104560340c6170228205640000b09044a842e001d101d851401482d442c5c80c0448005c040340700e12103030747c4585005881039200cc0d25010001101481c100308040c2c00160110158409840c03080c1008500c54080d59180301390551036800850000800030307801a9a0b120201c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 918144361 1250 918143111 918143129
    0x41b031208090c010806130209040c020307030809010515102006060f0607052509180309050102011a040e030d092a12170c0a15110c07090b0a051801 65
    0x640c2c814805035aa000a407080c980451072000c04181c1c0d5050403072101410f80e003090703805481c0030900c1000c0340840e8154607074040160400b00c1c6041c10107a04c200c40d150446c4429000b4401070421803d650050a0152400c40c89070441d00f0381070401c5401609107411242e0000a650954060002130715200c5404464091042500e41082100740c0342100c241c2d08110307000001401122004a903903076000040a1a1055000c24000001400e41640c09031b140188205c000b0f40315100020328002c2c0c602d4400d500014107590410303040d207812004014010401c0641110003080c5101800308031415403083c0781d0000f0f085420160004203110f501140c0710300c0c01503480381090780840e081050b0100c05c580340c002c0c80550200304d0b409a010401204140d807100c0010844039140905018440d40f51000c03c45003102c202e00503541150140490b44074181d0018400c0c442c8d0b0340b03041100440c5076210700240c000c040d0740c695149550305194450604110249c00042c18244011000052992002c1024469140c174 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 918145611 1250 918144361 918144377
    0xc020907090e06150d090c0e0a0605090a05090607360302090702010c0f050a0e060414090105040e030d022101060507052505011d0a150206160e09041b0312 68
    0xa13401c200c880b403062088480b095034106260340c0300000c003402074120156881c5040010119030103601e0422540507520448001905920f40b005022040000502c00140d00d85004100101e074803000c40d259501402c0e0b45080e03940c041324030700102c20400200d0700500d48100c28091051820120a40c1542501d008541d1200c10742e03101201282690110300810340040d41203c050124540104098440100c4604103080c1d01807280c00400c016030000d81c4801c07080700102e0690f41440c1001c03460704d80500410785007440381c281c0385000240c0d0b0344102e042e1070700c507168001500140d11102e0501800000c0d000c1007400500e5a6450005201c0d4110f02406c0c1c405016040b030a800900390380000716150160400c00c07480d2989000c0042d039401c00d000c035081c03192078018002e450301559040c0c0340714040c1ca00c1040010240440e120300030326241006001c3e10090007008241c0f16120f4000c60303105c40840d021070f18900b503907559280001c0d65050010b050341c0750381042d80020003000b428102c6036900c0686565210700f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 918146861 1250 918145611 918145621
    0x816090b0609010912080424030c030614011808010e06040218040f02090c0c0a03121419020a020f120414010e090f07090503070f1a0f0412030c020907090e 68
    0x61280b26811205020440301e0742d04200020540700740440c580d002c2d61006040a54a413007842c060400100e003d103101c424184204141a00351040d107030081410f25081102d2814403680d061300788a001d00c0203042c445e20040700003090348421100c20242a5441c000d01c070311403250030120b555002c1510f04030702c140c442c440152907088141010703174441c2d0b80082d440e9039946565001d014400308050180c0500b4071080204083c0f900781008550345841c8281d640c0ba40390f0706c20040c40070843e0207003140301032840b521600f070018100300084c8180f0340c8481c1650050341c881c00f80704240c4c500b1403004d000c240e0340d020f8001e041c0e04a081c032002403c12580151002500007001000440d185c1d005400d5156100c5402c5001c201ca1003601b0040d9a4448070a0032301e490310f540c44000003843c0445c1d50740322000b101110700d8207205070f000e925a031030106850f100440341401c80e000c125000c180034501844007003400e0113801f4820b040c0710f401c010344540d40280c0300c0040c6040044009003a1184c0380521540c1a0200f00841c1e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 918148111 1250 918146861 918146869
    0x9050708010803071a0403030b031b0111031c0e1c03020c0d141204050c130f0e0703030504030f1a180105070e010c030e0a09141602070e0403050706060816090b 70
    0x40d0a0b035070140b00503915013145c502040004d038001c0c2064003090341c0c580340c9030341545040248603411010b04102b104499410b600041801d10585100e00d083d0300184003140f400c900e000c0038800e500d000300c000840c4069030030041c9850a41070120400d00380b55901002151141c01d540107140707041910003038de41e041e00420010740e040c4485103242e0345106c20800075983c14070030041c0d030950864451415680550540300000300303521015025694042d554004160f00107206201e0b107455803c2c410050862180303545c601804c680514070000e480c40c000c8861400130408000c030000641c0440b03a411a041d81054500024602480300c250f83c440c1d0300e03000208007403e02403417210014800580d10500103598a50b400c5035800e0307003928299088142400c001c07900c010726004a40014840b402003043e180340148401340c0340071014446005640040c0c0050050456002c2d500d50720981504003203944100b503241c8100144a03a80c8180414015904d045011001c20000d03001112480a0140a444403100403c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 918149361 1250 918148111 918148117
    0x1309020906030c07020a030204020d0c090f03020604030f03020c03030d020d0e070e18031c150e1b0c0c13050106090b191b0804151101020a0e210709050708010803 71
    0x107078000810b10010f5503a80c10b030f8004262203440644030020f00c039540d6001c00c0030f0341c0004540100c3c0945035286118825407240d940001004100d44115100d8a503030089007040c030680c00090140800d4070030000606000300404c400070300700a801c481d50b548100b0594002034004200802c405414160750415104c00040e00d001611007510402c5900e44440c2200021380280e01c0b07070461140000e0081255846d00c1481d1416071210b00d00010a581141c81128540d0007c980c21500d43c110000c000e11060407659150701224441c0360405564412681840500e0489194000c83e80305000c001d80c0141003100e508110f04840c810388aa11010b80c0340c44c407440c41c501502c94018489050400000380070380c8a602048842c14690000740c0c13026440b07490701a0254030540058010b007100c031205164142d40941c41d40c010109520086040051917540140442c5c440d40040d4418011340e00391903d174800410702015010640b10803109542c2d501e0710b079100640030448a03030380400d880000000d031959002c421 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 918150611 1250 918149361 918149377
    0xf031e031317100b010c06090b0108060c0f030403080703110c0d032909130227060603060d02040903140403031806090b040902030c040b04030809150a0e0d06140c130902 74
    0x1810f40f580c898040c40008101150001741008400100b68000c50810b10508100c64000c170841c000c150305001020b807074041c0240c00c1d51483c031010004000e04410f09816240c00a91500d446440c03038842d0369085019080c035105802134800000380d2045a2000051084402d00c07050300d0621002c2a1030040b4805080c4801070300704000c4400b0780741c80d2203107400c002165001050075440725103203000d500400c14110040e020300c1e440b11000c05070090900c001d050002c0c1c1c411403c507a200d1a521703100c40441c00c800c8150f48000e0041e919200341c10100760141b0104c0c1c1400d446013084c1901c1e00c0d52800e004092203041c044d1040203a042c82001700f0380921030300940d0181d80d0705604141c0b5061804003140c009502c020060f40300c5000600000c00c182c2a5400104011406011010303122510704042100010b002d58450301d000c00e0030491414400e400203030820301030358200c038268409406410410081d052400000841414007001c22000310300240c040c121a030040103048405540311070b030400072032180e400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 918151861 1250 918150611 918150613
    0x30603060901060f0501050c010e0607050c07270e120d240b1c0b0d06060e101401050f0903072403090305030123040f02181801050f031e031317 63
    0x60174004e0394060f0005100100c90fa00c000140000e070030468908001c801e94510300004e00006400750243c00c104040400780980411240c401c50320144021109030024062055203034490b2b80c9900c0c81c80e000d201c00031080c00c0aa003100d9171542c2a2204000600700d8142180b07800c10860384140c50801d514000070b00351403200d440f9520f000c072110804206041034580302032881e5140d890212030313600d42c5800594168440c4201061060a00704941e6191900030184402400181401c0001e109200c1d038007201000c00b8244141d84040c0c1d20700c0400148103008200380c05124039000000c02513080114a0612033301020b0318181e0125624046081d100d5840b00500025000c1c401801000510701c0108103020583d4814024a01c4450104081d240c030030004010305a800320314035402c1200c41c017840c4482c441c00c82e12807031300d4200c04103030100444045c003819000d48042124010030f0b8404002000c40c03042c07010100c0050010010030303035640341d2042a4880400040c90f1001941040c1250282d540c402014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 918153111 1250 918151861 918151889
    0x60801090812090a0f060203010e010602010b0109060509040906063b060f0a030203010903110606010e03071a1309020a030f05010806040f291b0a0801030303020d0b0a060503060306090106 82
    0x200154041c0440036104103101d0113403d56503c0041c40c0d625004035014402c443c0903880358500101900d44000592110096905296441840380e1740244d14000b5140203080c044d456000d11004240148100e04004040610f40600410f2a01c90086645601580400c40901807116200303048400202c40d09000d500700d07105c80102c3e005141500c4842a01a005090701480f00c2c0d9980009095072061013058000c2040124200e0074070100b8411190f0003102801e00e03089024403000031035036940c001d1240304446d0203c981c600408640150488442d807203030200c0c0310811501d440300e110082d80200311810100e444d00c000d40150500e14020241200c288402030001507490341c446840b02c001c554012900711807840d00c800545c1e003880c0038040561110039000d540901e00050b0b032502d41188031700850851030040c0843d40244e0360100300c0d41d042d07a500d407801503114009840d410b0042d010840000743d100d00e48404c046002130740800518401c581c03c4084401d2911481038030b41c03c81c1c03054000c07551502540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 918154361 1250 918153111 918153127
    0x2f030c0d170d0f0c0c0b010e0108030d0209040b0301021c0b09040f0312090209010626040b011710020d1e050c180a0f061808281e0b0a0608010908 64
    0x403000380c500d0284001c40411200c004100f070004039034418181d0383c042407590010340240140d03048210b0141c03400c0b2088000c42d50400d44a5980c0380544039001103440d8000039910050b8071150408003607174802034000c0d03483d01074941110114201d02d000e004405031402200284c0752405840e11802290007407200c000c0742c41c1d0781c2c40480d00b410151400c240126184c41e800401601d03107485c203d00a01403940e071100f030040d9100141c4400c00809141c04401c03182402440041240f14040c58116980c0aa0b80c0c001c01c043c50f006140ac0c08030038045040c0040c0301144410303079045c01d1340028030501a421910080c0809809242e0103c9400303850089000e0014448a45c1d07030581d1104a08011400070601c1c1c4030984d0761a040c05600141e41c00c4580060710420143c0c05404003e5002d801500708140549903040d25502401880c139046c0302e00442d1035911012207818451040101c84118000503000c40e469055424103155520041e00d00300002841c00e5800201c00030306118800403217500c0b8045a14140203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 918155611 1250 918154361 918154403
    0x12a110607051204080918161404050910090e1605060712030c0c080301081e0a110d06112a0d0e06030907081504230a02010c2f030c0d 59
    0x401001240d00e80c20412111b1003c5c1e480c15070680c03c3c511100301000091405d0311a24211070340e01580030040c0700204001d081e800d015031055a040e0f40f0181c0e11803070b40ba80c1d0851003c0b145002640544007a0b45018030704074805001249501140c903000449100055658050092510131100050000128801d0540460340300c0d40105110740c1d290326054040d1035050700c4490303003030344203034000c05281c1e208060485101e50448004030135040c810000d00307213110040e2038810800d528004603910800b219540b02d4208103207540009152850a0002510341c0b002c0382840505038000749103402a2080503041c14400d10000034403c11004040e5540a030282005007402860380000d030034500d480c060040003040c5440108805031940c00c1410030805c00e030602d41032644152640c4100445111500c104c03081c051440001c3d40700c4426420720b8a0600c10380c650400c017000c4808d40c0b010800c1240c5510320100302c1014240750000103c0100c050f10950b08660b801c000803045010f9000b0701a6a80d10040201000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 918156861 1250 918155611 918155647
    0x6060b041d07030204080118050610030b191137050421081c0513030503040b1302042c031206120f072d26012a11060705 53
    0x103400c3c05030815403206e4201e400e4811201c0c41c581e0401c0c0700300b41102030000400c500b41d000a04542040b03080d03800d50315403981030b120040000c1c80004a07900220422881c507440b1040d00540088ac0715258100c2050100050000c43c032480f541d01da00310702000d84d00091040386411350100c6d07280c0030718007450725194074018402e0007203a01120389600035400c040b40c4020020442c42808441c0b4561141c11528401c080b40d0010b000c03030f4070184004031040006a000800c41c3e8015810805014240c3d480c030744402e59200c040c09000350042d052101c961042e8400c9071300308850010310841c050b80c9400740b0040660340d0103900c442c04e06c10310030b182c0801e1160401406620038842031030151203002c140b015005140041c150300054014104444101141c80f030a000121003000d00c50503004900c0c03500d010642e0070054660300d40b210040f0181c40012100b825400301c1c2c0c816100034240c1130302c583c0c0900b9440c4040701c0304120102189290103000181580403447d948220315a07101e076070829110301c40c0804c0c49a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 918158111 1250 918156861 918156871
    0x1a04051806030c3619060f05060d020c0727092a08060f04060b04150303051b01060b0c07080a0305120a0f0f2f0313020105210406060b041d 61
    0x908180445440daa0040c0301030f0b03540904050004141410300e40c2c0c0009000c020300c0c17200e945280006c140031290401000350101c80080781c0090311150b42ca1600c00080c07151042410b14bd00c00c408001942044001416840103102c21240401194051140007901c0c01c0071b200607c8011501e1200720560070403440f0f403024407074800b21f5858403625401c0041c907007001a14511280380441013048104100c50003121000f01c2e0540701804181840341503500d9102482c0401014400301180004800720903003c0c840b1003000d100020f0010f15a00d01e8401a258000c11020f101d600508001140d59000014100340301641a0b580c2882c0540d00d40e504e04e4045170140c4070069540c1c903200300300c1001030780303004090140c8001c1100290700702240502c0019481c9000c100c2503000600d0f0454908800140c0c1529803000d034003035003005008490301c01201c0b81d07c0fa010305051242c0c1e07051303120b180c0510581440d030b201d5449144204503c94688140c2d601a01452140500900071030384481d8900c00e40d2044940c04c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 918159361 1250 918158111 918158149
    0xb130626160c0803040302061b07080d0c020f010216060506100f03090507050904121e0e120c211203010506070f02012312010f03050a02191a04051806030c 68
    0x30b54a81d0b550141e49030300940d800c1d80141c1c00082805242c800c00d1400f030040700800c0c0030f1103150480319928007906005005010100540d902d00d00c10b601402404a858000141c1d00210340d034040d210002001403181500c282c0e4a140f6000000d180350910035804074500106031250802091244d0b02100a03000c441804c07501c1d800340040004250b159a14000e00440c4030301e41c1c1d4000c42041610050060b1050515100200d40f503600707a5000c50781080440840300c0c002c2d1024000b203865031408c2817420040c102039603040300300c0c46200c441c54000d000d000c010712400b034015281d641c030304003400ca4444d000a0150701d030b200a00304041000511504c60f010000707841814a501c020082078042d01c0600d02d81c1100c3c0030780c1100003030a01300403151144014050425007220b03082c1641181c5500b40d40d010400d1009004000003010081c90400380c05100d03000300540c903101d458650f40c22a140419030003901c1600c0c050b0040450050300d80100d2030300c0340c2c42081c010340200101080f010801c00500e04900c055040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 918160611 1250 918159361 918159377
    0x90105060f1621080714070501020403120e0a0602030405010e011229010e090103050604143d02120f0c210103110a0b19090b13062616 59
    0x807100d8600d41034910140181601d64220703410052045000604202d2a0108601340d002c101c000380d040070f000034013411003202c6140ca0b11150f02d0000e00910441e00042d040c5030004c0e8039400c00540c0308070880902d4805540b501109903454000380e03528081c0e4005e5501180440501e50010752044c012100c10380b84112000c00c0c0300301404410321402d00ca004e101540389050318040310745542c1100e190902c04105642202e41c640c9551201c80e01c40c1000b82008141d11910094062a180c08020031440c004be072101200c080c9000012600c0c1a540008621164510b810600a01501030b8800d40b15214651918800740b41d45912444e405903100404e00041ca550910404440402d0384070700b0202911005001070b11941075040c0010305070b00c407130400e910401c4508014402d4449400a454103411100c02d804000c945180040d50480c056070041000150081000c5049205061400c0200e42803a02d96206806032035004d14001050360701039040009030b040100d104909141e0f00c0421780c0d21117150200e2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 918161861 1250 918160611 918160627
    0x290904051005120a0302030f0708040e0f071e0c020f0102011503240e0d050a0c1a0f100b160c0b0f030f0705070c060827030d050603010b090105060f 65
    0xc403003094801c10500803661100b808182003042d41c400d4144040070041000e4026550000c0d03036842484c10345c4402031000302c0c8031030402c143c80c02a54007500b0b00e10344940c2d031813424202508200e40211845000101c180c1c1c00114a24040032081c102e40115a682040004440c0c09105071840c1e10300d2603030304565960201c6218440d41032440005507118403a00c0300c0100d40100e001c0600090303201b096030b040f468055507a0501300009030b0700300d91100c94109203494070141d241c251100c0980000250085e50b212503108420b040b0601c80358811001c1125101d550f849441c19144004064010081d180004000c6007400d5000d90303926800039441000e40c111265101c1c0c40301c100c4d540168444c400c84500110501014103030700000654001d00c1440d006040c28925218600c24610301c1c4128024402c6800125406102182c07035410088051030490a0280301c0c040341503500d41c00044813a4100785080c003c0b920764607041c0180488502e00902151003a400c100c00c00000e0380c405540300078482c4003008125 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 918163111 1250 918161861 918161869
    0x1015090b030901060501020c0609031e0a0b1602012307120f020a0f0212030613020a0e0d08031f050d060e0f070609030303061e21020a030b0106182909 66
    0x602c1481d440001041e542d01d46000645444020480284204d1040c8110296501c0c005a5171802600401c01c0144001c03900c0141800e001c0720403030180c40c0354003480810078414140d4692030b94403003082c0e00802c28560b64900030040c10000c042c030081000104070126000d20302c96403101200d2130110b907000a8841c16000010100c1e03025445040100d0742041001a0f5190144110403180107806500d6155190440c00100c9a80c105d06100c40b44580c0403c1d5102c01c64401d180c5244141405030911a0100040c00c0001907074104650b81002c455001c5166007051010140c031f0300460324007401401c03001d0f809031b84402c00303030021000d00c03003107441101494280444100301010003040300b625968a41c0e8150b0500400361082a0002c6c441d064100602c4004103050040250031603d500040c602c002c0d03501941c000660a1150020b0760000e55450007105000710341c01c055048071019125110061108085580c86411a1003010140143c9540e180d83d200f040300d05240c1044981030034149070060b40c800007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 918164361 1250 918163111 918163117
    0x1823010501080a02010320040315090b13110a030201020c042a26150103051b0d05150102010c0f0c080d0204180b01020708030a180801140910051015090b 67
    0x24030140d001183d03410641d60148114500705c80b144142c0b00f0703c0100d07a00c2030950fa00c07492000410b907940020348043c00283c2548096100c6612031078140841c200800d02203800e080784507003500c9500707648456a20301d03e807401da5101160707030603005080040201d408120091120800000302d68525803441108491440030580d103200741c6813503611215805004003182054000d41848048400c1011b00030200040608420000000d10b001b20307280d511188078520306941c10b041f00503642e50110700203c5140d03d40c0c228a125841450b02403499400c031034012400d85603411100000f01785001d080351091481000d160001c0c9018410300c919181c8091140390807a4032513803242c01011200c0018071482c0c1194081c1c0b00606409200410b0b05a042c10325664403840f8180313180c0280160b8001401c03008c52482d00160003002408000c0021841100182d0007545c000c954031680350042c03410405100b505407182501400001304018401c81c140b103c444001c4001c0407003d0f0030300c22103040c00900d000102e002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 918165467 1106 918164361 918164369
    0x130f03050625090b0c070e010807030218100308030a02040b0d06060f17010902090103181212060b0a030209060d0e011a0a0b0f1c0c030518011823010501 67
    0x4983c03802c0078a80c00101d41f4803108000141014020840500b240d0003a10440b81082081c441d034820700d0021181c0318000058403c0500c04070b0449405150301c41d810740f80061525468201d1041340d078018040d11003006481d410280720a6a10a0140803a007410b0b003407000c4c50950500022030150780c1406a54601d0342c1c042540800c2e68441e80195080707403031161094803541401e007081c20f01e0f0912080c2c0d91300896010070b69015095190301c1564101c500c4a520541040c0c940c0d03d04030040d61007295019400712040c841c01e245034110b403188a0001c081000002035180400c2ea11071401104908614810503181d0750030002c19540b801280c41c1e401c501030780c10355605203a4004030040720b00b00480070407045c0340c242c070240d02580560046000704914007013502607481ea8107642d070030381d0694110100300300c4080440d640024100c1018501d1101030002695910b0840c031400b070308585090b44 = true := by decide +kernel

theorem cover : BRFrame.Cov 917985611 918165467 := by
  have h0 := BRFrame.cov_init 917985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 917985611 ≤ n) (h2 : n < 918165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
