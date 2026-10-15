-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5040
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:32:44.374582+00:00
-- url     : https://prove2.me/submissions/decd62a7-d0a8-46cd-ac50-a040b78b159c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 906294964 ≤ n < 906474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 906296214 1250 906294964 906295009
    0x610090b120a1208150603060d020117070509041404020a031b18020d06140109051c05060408070201110a0c09051803130513020f0708210c0910050c060f06 68
    0x10244003c0c104441c15400c41581d40b4102c07520740354180d0440f82074205080d80e00407410001302c4c1319860010603045a0f24410306103030320006090210603a41c03540c00c544000120302e00041c03286051070f00b072290201a00ca450821101800e0540110310300d40c0e900d000082c1f042134003044000342115030581c100c005003400f031100e8501c90340e24003103a402394102c203528000e400e0802402103801400301c0d5903110100c9061395042441c074071b880301700601e8000740400f9140541c25800c1900200700c00780001e81c8102c0c0941962552000309100050260340042100d81c1107412020201c0e0010320700705030460481d0300b07594011410b512140006406904481c4e016403d5220004280e0022281305007114100c4c1d400321b4580707900441060000341648101e8103c01c407152003c100c040d001503030860240c43d656802c0130203280302265112036140d05e110165451410080302080044161034200319000c1c062000340341513410300565441a82c6c0d5544013910f1808050000c0f0009a69911092050b07044080340c8800b40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 906297464 1250 906296214 906296233
    0x90804060c0318080d0c150e0304031a040302030a0f0e09130b07020f0c210303130501200a0e030c15040609140a1203140d0204090b030610090b12 64
    0x7a000341068101140460078840f01040d584058510314821180080d000d01420b0446030000c64081c1e85200d800c440000240144500500031481060000c84165005554139806c0d4101520908501e52000d640b940c649420000001c1e03010040d030b1948203403403e00d10f44010941c507080e101454010b0000c0c0c0c02041001c2007000340140d501030803034260300a03111507c1303a4a03201e004a0701c407a4175464401580d807088800f80c0090a00d407207483d0100e80141c9079000c144520780502070456100b5201c880c0c100c402841c502060003002e11034584050f601160f01c81c544402c655007003456008440c03a030808d01500150300080c036241423007802e180e40c10080200141e1080043d00c80303002e4103d40148400603240480200d103859007403102d45040013008141c14581403525200303c0400c6501c0c4411802c01c418144809511956100941510b00d0600c00158486050402100c21220001c1005d4401d9001800380010381c200e801c6917000342c070503401000c54240b19507004030f442e45500005a61040c8581a0031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 906298714 1250 906297464 906297467
    0x20c10270e060406050907050715061205190c0311031623030105040f2a0b0d1b08240306090d0801080f150a0605030307050c0405060a030b0a02070609080406 69
    0x128800e0700d44921400455486003400c0c0000c0310054050340b900082c0c01800704030b00c103000340003803c030f5240f151050b84d118014045920054603603950108000072a4108550b0412409001d400c141180002c44400d03045604d0b25000c0c158061840080c00052000c40300701c110b920280001d0200c0e00102c1456040355645811324040c05102c29444108044052600d80c00c80c5410b0054a004580194885000303002a4942005943c144007400011140030380d21500500c902c011490000c110a40a480e140c03860614070100351669452545040380b020b0381d82424503904801e4040d0050b203001600041c07410000300c0c1c0760314071584a5815a044c881c60003041074181340061003150600c425501c041e40742e44c0c0c80c08000e81c0c2e8100c0100e07201c03440d00402c007024090441c060344103512000e52100441c144e1366075030110303065070301940003074846822050700009141003074059903030000c00690340d841203170349140c8605020740d801500203001c0d00d800081d03440510480e82c000441058221000075565940d0310030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 906299964 1250 906298714 906298787
    0x110c1c0b100f0b120a020a0201020c0f0d03060e090d030c02030f070b090d080103121d060706050417040807090b060d150305060a020708032e0602030d0f0c020c10 71
    0x4005401204401c040f82c4090b400381a07a01140310280c0515407a12148004006904150540c40442d9400c1c010200050010068402c000c421040505110b40d42e02c1c000805907400364014072a00c107010409e001c100f84002a01200d080114130f400204070102d210100d04520949120340d0f070b603503070100d0751000f4408550a03141c0981d40e2601250302610110500703580c40d074004d22001d40704c802e880b0240340c80c25014164403101445102101d1080d640043c000421a4001c07000a46401c0da0f074600700320411050245c00c10041d42c000c0c8102e4140f5107010241503903100715000d0702414544850707410719162900390070346580010001040c0007171061881c940c1c140a0303c13444140c40320b2088001140e680305035031088604107a00042d0461842c3d507510764420104400071107049220640603115611604626030b283e0152070780c0d901560340c60030300e20101d209603003086a0401e083c601c0c00352403034406030b00055490f14003203040d504041c01420102050b64101126132107040342c80c001011508044000c4907 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 906301214 1250 906299964 906299969
    0x9030605190b04150302090c0c100e0c040605060405100318050d14031302060a020c03060a05010f05030c060a0f050f160c0b03150f0301110d1a01110c1c0b10 69
    0x50802180401c40b040009a500100301075550510041d02403000d420b0041125a101402020131307890320490382c920070305e0300005180d03007404c89648180c5034140c40010722400e51003050031074041c07055508100c002240791203107108503441050f02002102ca414007a8100e91502c0a0180b8442c1100c940c50600e035840e0890424083c0008074207090007001c1d03038079000039a070195480d040c3c14407290305650b0a120680d84040c0a46080d07200340c59020250b40d030100403080c030446c134103503000c2095494104201652211608141e00c83d4006c46c02e01c0c0415154001620703180034807480c6c5045041e64101d0155010312804030003030702ca56000a0301c0e06c0702c40d420701c202c240d145200342c05c2030581a644980d020700600054a00348101182a4040200303458900041003980c84020000289644200034a007015031016007441d441c680c9034401000b800e2102550070400540038200410821540107400c2d4441c400540440e2154454081c6068040004489012104c2e4061034040090038100000d200c50405803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 906302464 1250 906301214 906301261
    0x30f050309010221030601031d06041a0a0902010c020613050d05030a020c01052119060e04230709090f0807060e010c1b02130e2d0703170304020109030605 68
    0x85804111480c9501070313040e0b00850008203055440c2c100044001c2d00750400030005800140003404006441481b6150103144980010158500c2202d00c981c2d0959005141c8502d0a203402c0e82c0d0f5026036004607c62601d180d044405c03503038500c1e00d01003800c0b4411040e00301c15040485144410304210000008116451041e000c9505094584004540034421042100e4102440f0030280c4410a002442141c0001802864419006241d1140c800315030407684034035540c840740c0040c08140403948020a108001b00d001d40303414014900c028981e51010361180300030241c2c2da050003501b48044010601d02e80f55010981c9560740c130072820035201a154560015485500c0d04020882081c0103d940c80c206c0180301e00058030444598080140c550000c180b41000781c0c2c0c072035440d2005074a00780425500750800c044040b0105040c0460500c0c0c1c8014140442c1480d404650180082000c2250200c0703900c88401c40c05036660385a00c0121070303802c4581c0c4006c000c2801c000c18401200c0c07001c0941c03000c40000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 906303714 1250 906302464 906302473
    0x60e0f150a21150302060a0201060905100519060824030a030903110d0309170304080d082e120303020d05011401020f030310090504020111100c09050301090209010b090307030f0503090102 82
    0x3001d02c0b0300444100220a004107800710504100500341540039101500ba02c4c00000317840390362482247e0590340b08a400c6005c007281031406001c2854550b00700d00401c1a102506054681042070281c441c81025010b08461121040010003204003c5907402040c1800303402d0395200300c04c6250140c00000d4070301048581d50199445822203040600589160381c1d00f59840c181c125180180d4030018020480883c3c01600040001042c100c104016004202406988075401c9140c03540b1581003614800202070540c030b0b6110208525816079405450a6501c8200806104078141c9000c1d00284504d020300600c407401d03d03000207980c0c026038091503d0440280c083c2c074100300c130002a45403244021031784442ea1600c52102401a00342c140d024030350241c4181000100041c01d540842d2501551507119a480c0e5299080700081030740c4211442c0040c07800341c00034804428103600291a842050043e41110403000c40c01c0d2220799010440e61b0b00458110b901e4101c00030040c1082603c950002e10803034050b21a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 906304964 1250 906303714 906303767
    0x10e010605180f0a05030f150603071208030c07150509010e1f051005030a0507060306211b0504020715140403091202040f020f0c0705010207060e0f150a 67
    0x80c00454000005a10600040300c0000301000b003d405034030300ba681c101403800c20104160300c04104c1007400508030001001e141302091171540550074010704c0b860013500700190070008007100300c8440103415400b00220f81c413560707092003490080c015014003408050200d01e01240441030b5500603401180400c0c000d102110701c603900955640070150340e29004060a00f00300f0701d8100317507a001c150400d80c102c1c806a015661180000e151003903900c42525980c100420030011581c0503c66980207203018110170342c41c0b5060704200c01d107100410301d01030564040c200700c00d05c40103c884004006444010411500c0307045500305444c0d28070482c40c40c0c41940c0d10b48400030400d443c0b500f809a207e1949503031600d080030705084041c44202d2210208903002501c40400104100c2140050560b000800e5081c9031182403001100b460a4201e0f40441c0c1550800c0b030052058903804052811181000e48000c080408060b011825001c002d800c140300400f40420070801a552041c444102d2135914001d01600d0b14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 906306214 1250 906304964 906304967
    0x31509131412040e04260a020f1f0b1f0504030201030518070506071b030f1e1203020903070b0c012906030403030507200c0301060b03160c0c030c0905010e0106 70
    0x44071440b149140003010b100c1002280359421803954054400d50300c59030043c20034540301c0700c000c19851744510b40050100d108804d01d03604104410841d24080010031586180026030b40c00000040140600030b0345070340c0700d01d08503100e101e22080144d01c000114404403502c128002c2a503001400100d000a0901d004180202c1040740325800384214070001d000c5080c030f040c080010991009804450760b01c442002014000d20010b4a00021400f4040c244407840503860f022800381810403020742d00480301942d00c008140703400001c0340c010400b402d0059413003860b080040e00d0025140e01a554901d40019003c000c20019040341c1c0c1580d0405000c102c079044254045010044240c0509800403418000200401d229800054011550b400c000c440c11000e143c4002d61100c42c88000d503034560010102101c14107091103080c0081280790081819401c103441e01c03030300c0d01030131108030420031801504a2050120340c50302a4000c5500043c2c8028190303441803a000680000d05c110442c14007048000640036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 906307464 1250 906306214 906306223
    0x215060d29011a0f19120f0203060f1905150c070305070f0501170c0f0f031501021015031515090615030b0f01031104120308040b07180b0315091314 65
    0xe130544103041e404c0540c0100f06951880c850b028601c1040f03400002400c07601120301c00c01807000020387c0090b03560703e0312409003ca51600c2e0024140034049181380404411108910041500c1044070bd48204e02000c0d4020b4040d400740f502d048200e8003406000104020002a41c0002c440d2501c1101d84c4042c0e4400c01954200268003108400c050a400081c2e152070030b050081c1300303c2c2c940804850070302d1100c10f1031a940360030444041c10820303220a0b0f40240c640e01004031219144044805114a011001182030018450f01c0000c4c805c00740780c14080d05c4400d854010405a03805848a00903103a5240e004202406083c400c0880a61000203c0901c1d1846402400080500a002d2889c0c00c892100110018180100920b00504007484003145c80403041c201030150300e000341c0e15080f00d4102420301805440d8050032480a05c20001002983c07041d11030702500880d841503101640700e80d036030380c20f92103501818160103500400307031010009904603540380036074014010000045c1700303480c512010790364 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 906308714 1250 906307464 906307477
    0x604030302030712050712020f160b07150908030702160e010f23040230011401080903040e040b04031d010e04110d0f05160215060d29011a 61
    0x10b8004000740e42c0070071313009142c01c0d07040040d80c60442e103042c44c141c9400e0100c5102c03880c40d50042e000614405942d4100700b0440618600003007484060038500051a0b00c40e00c5816401000410300c6034a040134250070340c2c02800e2840d00320344403d541c2d00d03292600a4071001207404400180e03607103d002056a880c0c0d240810305135103014200c0900a42000d00070300540c035114000d034400080c00d00204045032951b0010340488070b51612400581c201e80076400c0041c150119144013010402c0c00104031394680c1e0000310400c210203003040c815640b2044040c40c1144504d801c00c2800d1502601400304128131500480d220701d000f996040b0380146a074100c0306000801440e003500003101e000b00070303a00d0701c0c03e5484804040108801030b450011146040070582c2d1442610301c00c040d03a68420808119100703859001e00a40e144090302512042e80c11082c02c0b400f02812030b03400790700004880d1042100715449020388a88152800c81c80160711400d4503140e5200b400b6484420028600c5000580307285000c1d070b083e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 906309964 1250 906308714 906308717
    0x1403060d0311190501021804140f0408190906030b090907171509010e010b0a030506070305040f0f0f230309090a14010b04052412060102030d0f0f050606040303 70
    0x149841545044070040001003108072036000d031045000b0f00042454448000798803e00002d82c542c1002c24044030f44484030f411040c090b5040900d440710748001e1102065001a00340f0b020542c689450820130107a000c0ca1154102c85880f41c10031074500ca400c0228002142d01c2c031399060110300c0e80c020900410100c00c0e00d0700186548148014491440c0e00c00c840c00401640d5000c803001c040042c51061b81c00c02c000e0b14200c5039039560300c1d4085c40d2404280595030201100355006e202807461a920240c0c1c2d00300007001c00081642d12804030381085040f8226608542c1c205840c03001079001d80c00c0c41c0040400000c2c08840c940314a88041041c041d003003009480c018800c0b006581400614024001d106000030580100c45540300d509803144000340f10850b0203400fa81a0749a207441c1400180901703201d5500101c08a01034010b204000c00030381c1000c44050540c011b4454210703446080050b840e40c0207956400640c6802c2c40c40e001c0034040a45c1c8015410b2150310018059915840240401e51040e80001740 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 906311214 1250 906309964 906309979
    0x106140a08030d1a040c18050102030c1911090705030f24060c0f01060b0d0614100302180a060c02130203060108040b10030203030d02071a0705090f040b150a140306 72
    0x80044015800f54903128010030740e03400c04c031144400240441d02140c0000c4003080308403c100c0c40480b206280900503010a000461402a540c204113a031901c0d004000e008008268103000b0812120325026900d40030081c0c40c10f802400c140341c0151464104a5101c01c148050301e0010f02d005020703400c103002003254100030311607007000320b0280f0403c4d034844c880b8280240f0801000010b2454244104401040b105080c0f40e03c5841107208042a1a82984003580000c9526403182e003e5503a6140304000a8240c2801a5101c00100c032225416069203001540040e0340240000e0700c54010510303001c524070844080b01e00c0c100705c141d1031080740402d4444500080941c0000381c005034900c00c000d5003202d46119582921542d03980003174556406240d40c20304850300815000b00300b0400c4080c07551089a204071a01e424a0100c0008280d03014410041c2c3c0b1907651914081c0e16030f1115840480080d40c082c0c011540c42d045582c441046900001c034810000c1c5e5041250344203850b00b2000d0342e024220003000c11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 906312464 1250 906311214 906311227
    0x1090e06040207110a030b01081c09140301090b180d1103030103020d0516032001260c040801020408031e1323030607110601060c1a0c0405030703050106140a0803 71
    0x20009400001c0e046541041e05021944130340d0358030810b0801540b0420030a0740c950f041c44000741c180034085030b9110f420038080941d090042c1e008050310050341c0c80c0e40c02c42004070717a00f6000a809410321410251956541505022940d400001c1d07480135000694202c0e0b580c1c81c0e0301c4004607036154240da00507407130b90018001800186444903079054054082e00407260b20010f01c03030900340c0720070155008030b4000103007203402f094400c907880150b42042d00908210f01084030800144030754034a100ba030900711f01da00400240f0011000f030103440140040c403000f151142c2d01c03800110313681d5001500b2992260300b034900070f2000c0ca0302c94084495850109216012881ca07050082c500c600007000801c1502411031940174041d24100456842000180d54284805190702031007800e20b041038000f8010000b074145144086104045003031411001426120480e90791201c80b18807900454000f1070345070254900000c144070307054220005a40442a0940e00040b10b81d08021a5413420321030749a00d90400d000b030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 906313714 1250 906312464 906312469
    0x1270504150b0a02070501030b060c0a0f2d02040e06011809030212220b0313020f12070611060606211003062313030504050907020a0b0f1501090e06 65
    0xd89904850500c03480c1110b4449100e808603030042d501c224010380c083e460802c0b656a040c011160700000c10f440d440e141c21400007105855002c2041e026102061550f54541000b40011303142d107049070400385040313040c0a185090014299041e006a00c900d00342005903400c05c1c00801d13018100c40400040c00d0301441d4000318031001e400c070700e030003642940100c554146109510b60002d01c00c5070052600030712024162818460758000070341010039030f5501402004036071038a4109201c80b0b01d40450b20016103000c000009081c2c00050344c29443c840c0517051000600e0340e00712901c80e8003110f440c8191039440c2d03140f40070b00c10303e4054007030302903140000b40c0841c0110740303e110b14180e0402824921410065101d40f243c0d01940c01c0080c2d5074880507541c0d00140202240c05072181d80000300030004181c24003017914010a18041ea004642c4a03803240c0010400d0b0b90f008000c600d102907440614400589005000c02202220440d02d44050401d148100c0c021503204540c6d1030140c9003210240481a140c0405 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 906314964 1250 906313714 906313721
    0x330d03080a0906020d0f0f0b0102030406050c2404050d030c050a08070e10020f010c2303071b05070e06030303090a0605130c1206180c03061e021801270504 68
    0x110040580d9641080404215280014034240080c010040345250010341c146c41100ca15480c3c0400080c074022030080180c1c0e01004660444150b442d01a442e9011940c045003071407110b09450803686030a04040b1980c10165840e00e1055003d281601c4800c02d58003015030944030303441041c40028400700645000d60780100503054111180d80741c840584c5020002040000041e80c08500242e0300c007071110002c0a07000d025082110306c4d40d1902d842d82266911480c01c008180c41c0c0e040c1d45016003c000a031165200c0d56600240d1200d002c0d080314203421034144292120418001c109009003840e000800c2410000300303c03401800400700400c4140071703a07110b201c001d10b0083c0c42954080c2c0c1d005000f001245020b0602c80144c01c403145040c1c50403202d494158111000d81000a00b140140f0b1019004190404003000849404c20008030f2060461072512130750710411880800007a2010400c0c03000340c04032052201c0b90b844e0a0b2582c03c842c0f50481204480152640807900700c030103440700240800c1c1000c1c3c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 906316214 1250 906314964 906314971
    0x402030a1b0908070f060203181203040b090312071104090201020c060a0201020415030902010c0f0302010b0402070807120203270d0f0b09101b1d09330d0308 69
    0x400050140640500c008074000c0000c0640000340441c0092000b03000c1408514024840f054001096510b00b4402030345074010300c0d072103041c01c0043c504041c0040d2201c1d494040c9a0500e6016669140e0316a5180d100ea60403210400d03020740f140d69800c801c8044001d0440e202c0d680c026070781050402103042000060030151a00300d0440c042c0441401a40c0c9604016110506284d0005601c80341090781b03840940944401040400d42841d18400260360042248403006030031604c00d4140c0142400d00741d0140c5141c0500b0b58016100044407403d04c2061806810341906ca10b10039007200742081030482c1d590141c0c15050b00c00f01e0088160084801990128007034425014000c4180300740981c4480d41c1d0340200d50800c0e0381c003071154800c12028403410302100c1007040d04880c0030002400c030391030081d141c1d1070031115850074803404c1140d04103010022007040611040040449030b03240703031010503458000960803803102c801208405d044060b0188542d003811000c1e01030001e050300516a2400c0320b00a8028 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 906317464 1250 906316214 906316231
    0x14010603290a1a0904110d1109130b01180906020708040812070c09020309100e100f06031203020f460f03020f0d1802012c040203 57
    0x111000400181d00700500c03104030060315050400c5440048002144060007404000c146207490950303030004070400603880329840c0c151012840c6968924092089001d00b03480e20354801c1a09225004008002d04000e60b1003105642ca80c465841c0c07440c8030314507a000d04100500c0f0864081c014001c820824203000f0340e07001c521501003030500d0161103a0049230f020f144191058a0001410301c010346d4100901700720f081c00f150940d45040101d40364400a01a64004c04510940000c04038120743c03c10414116540030720a01049580e40c81c15a0360f41d52a50600f1942e21a400c0c2810280840864814038040342c0d080810204143c079900f030114021350200604480b501e01c10f2295071030000050102e20b2a80c3c80c01006454442c0e46d90302d44090380d00d4030300c10a84035444009415415150304c8540070b626003c0c0c0303080140c1c884003010400304603400750701580a401850001141001d01c0011102c01006000ba02c0700c80142c03103c40e02c1800b1520216502c0ca0010410441c2c1515601300341d801142d124050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 906318714 1250 906317464 906317471
    0xd0608301201140a05030703030f0518180411030106030c090b06120108061005040209100c05031b070f0501020102091c030e0d12080f06010c0305070f08040e070f080f041401 76
    0x411180128205081c1c0043c1080c20811100c034115003424046000948011401032481601c1c680c0e0003060040b0115400040080c042148c400100c2030b000710032000b0390010840a05041a00c07044501c2103000c03201559006080341c0c9440303281c00c0600c180420750360452100d4039003d092071116405410380316451a0001c60411060f56a25201420540a0f28240d03000e00004d00f09140010111001504050f00c20343c030401809000303030b8a0400741d95031072942d4104030454040c070703003455801c40c020744901440c446500c09508421080c04100c0006958080760520402602d54004a00301c2c0a203a54141e000341400b1280c041c4204201445100360b480781c60038288258101c0c01058200c0b104002c211500700e5508001020150800c5405501c0f10301c034050400c0500d02180002c1061200480150600000150381750a05c05580701010b0280e4000c1c030040c0e5180e65640041d41d00301c2c011510f000004494001a90290344140c17061405100d42c0c0d25580101d403240c0e191911100c8180b51010800d43d030f0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 906319964 1250 906318714 906318727
    0x60915061c05090a050709140432033126070306020306040c0e06030c09010c0c0e01410315070201020a0e090603070b0f070f080d060830 60
    0x1050003694440c0b02800d0181c84004c0041c0342041c82c0101e43d8200e4404203051408458004255004d09540b0981110766602021400e02134500c0071400c142c0c10501d4100341ca0444103004400200034049282e807140c10031070762081a50728242c172400c6600305902d90121481d04121b80c1c0f510807e103140d405085054207003880b462130f12003490700c0ca03654011070303410b0b03004002c1051500e03140c800c05211015070309045c1401149000014054400100516007202c0301081d00b800c0b0341d11450703198566036400b0a003191607644540901c03009642c03d1050308100001ca100700003881d8401e003c1d82a881d81d040c40c2c03181290514401000c03455407105d1000b81c02d0301c02d004001e801c81f0100c6110034040c0403150001a550625000020802810902c41032300030060001407054075140080c10201300c91106200703a4940b580e49a020440344129100946000c1c0e904604006111020300141840300710044100f25031307075980c08101e84440c0d00654000d6900c421100d2211404102410711807040c0d40b58015038501203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 906321214 1250 906319964 906320017
    0x30c17030112060f150303050c240928020411450319020d05060a06060e0a0302090414120a020303010312140a111f05070806091506 58
    0xc00903804101d4140c11a9684001c3c00f61a114210404078013070300a00107000b0034001c0440c005d0b12440000d0401500054480c4050400c2c00243d0781c50942d0f000c64525031043c0460320940400940380b400141c06001900c440d00001048040362400c10f80440c82e4801c0115000c10004040052921300d40500800916202810008104102260803900044032040c5c00c04114000a600071240d420f8550f038842d42080c559001641500c040407007101000c074030b5050701c0401c0c1c000c0c18490f8000d0251003800e007030016100e50381e0440c50507181030307646881c14040420100004801c2620019400002010108000c94140910700039868195001c031101e9a00c08403080f0140d030300003465400140c00100051003007082c0c00707840c030107070440c1c6160004030501c08081d801000e2048500a00600080c000740c1d0303103050801e0040c0d00303240250324803000c00c45040d066400c001c1c1000721990400640760500040340c0b4540f0f07540032030242c41c034206003522204240e405e11640da8403503110b4005041c0b0b080b02807420171 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 906322464 1250 906321214 906321217
    0x3071b03020102130f0506040b0c0c030109080c2112090a2f0301020403030f0c26040314010501141c170405012604030c03270816080a030c17 62
    0x1403099000503901c40e502c13990900200400d4200521040d0100410001a9074101c02d50703040c0d030b03800a4010b5407900c40c0c900700e43c41c0c0540410b2650b015401c054004081c0465440506410b854880c1541c0424030350000c4000c4000004040c2e555044e0240255002c542503c03014a611642c140200d07105407002d07427504448070f400c924070700b1714000a03074100c45001c409072083d08622800903402035041070706543d809007a02065141c03c5080241052110060040e031101ca0010650300c80316041007102c00103402001540180030640e240301414000ca004501d051040504844070380b040844003d007401c040280c298016001520040c1d0b0074502d44004c20301e00e030a0007a00e09a610300050b0f856181400151602d84030381304100c5460501c50741c5c02400c1000d00741d001ea0090b450b10b041000d1500d01c0c07400f0b40c0c000d1a842c06016480c8a00b4200802d0b84104120110036102078a04503030403d08041c80c694102c4240c0d01868681f500000400c50001e4040d462041c1030a10442ca000e8100c0905507107603005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 906323714 1250 906322464 906322517
    0x70f081606020c01110c0d081902210702210a090306110403020f0a03030207050d0218181015030609020a050303030405010f0617060402090a0605040e0a021f080c0307 73
    0x41d9500142e00c510000e0244524a14100b05c00c010506007030030948007a4032981800100300c20b000c5014000381c51218100e070700600e02541d04c1c1086490b042141d01b800418480d414140707011f5540540460b81d940d0001034014080c0c0d104155856813a05498103017601364022140d99018054a00c102000160460007140031041c0c1240855464030300d180101310801d00c400038014024240b00000b0f10101c1d5020070300e90250748081d0f07074000090f102440030030000410400c51071619420a804c1c007100040d40c04058044512040499440401000201080b00d000761600d0480b924140010800140035402c9a85c0e1507000a00010f94580d8880100c2d0450740115001c590513513465000d04840c2d03005101c1e21004e0b0000760200c0129400e0200c149684410140019119020300d0b000150811403a40144014040c050014019240c900e4100f50741c2d02c0d0342400480c4a5550209071080321180d410000310f001080741c4e40c01102d501c500454007019400a401e8004000328552048403200c1c503411400322 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 906324964 1250 906323714 906323723
    0x80c2701020c060a020f060a0e03120c0f0301230303031012080403020406120b1308090915041b020f06060913140105040c140f011e1e0f0f08010b070f0816 68
    0x84151b030340241400c0410040c030605c215441d044414000203000000e03550100c080c45025499900c6400313040e0014081c11102e980d00c1c3e6400030002c515114508240c00740e8500070245038250707219a200f019103c1c001100e203142029448038042000e00c1c1c00845440c5454025227000b840c00b83c480c3c011030f007034030240d4000b201c050076610100c008014046084950101c591400e00030440c810340c0e501e40320382c8506e507085d070306c44d1000101088488024040340480d0380e80c010020030052600750300003011086010305480260050380f00c0501c0024001c14500d00c1640d00521544496548419070762030f8101500044e604180030070b03041703002030703070b00f4810710340524000e00d42184150f16100c1141c14080c0680c40e224090180050115000d0740c00142554158101c4440d218a0030702504003101c80c0c10808102c046900100541c0140c2c0702c2c1c1008003000400319569071080203030f0300d034101a03400d040284940c2003103400c104007034402b0400103180503c20714401c0c0c3c443c2c0e20707114412101c041c22001c03100c0280d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 906326214 1250 906324964 906324973
    0x819140a02010c02160305060609280c0e01030608150912030f04060c05120606030c070203030706050423060109110408061f061d090405010615020303040201080c2701020c060a02 78
    0x1940d010030813030160402070304e0800046030860340ca807512383e00f018081d00e0041c000c903004140b0214459802140e160040422002c0c401080c10f1117901a040700c0740c0c0000810300004000a0552103805007000750364000c401024020300350000e0504009000b0501d0800b40280700329a450f4550b218011130080c200780d0400d1800d8105800c0c508110b40d2079020140c10b0240401c801e9403004201c091040d48a442111619101d644510003000b0b14030a2800003076150000144084c10404550300c010f000e54022100240b50403c00006049a400224820440760f4418401040240c03115000010a40b1220340c241d82403076955110207240c16403d40741c0041c0d6903844030700e00031602501c0400700020080c514064800581510030b540c00d10700005800343c080c03510200040d00b404400d4100100820b01410710340c06c85815010000c1d1aa001528101c1c00a40d130100400da400d20700c8000c3c0c41c0c0043c40715138207404210300784801110803a60106070a0550283c1c0b280000c0079070b00c000181150110725000303031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 906327464 1250 906326214 906326231
    0x60b040e06121f15090c021b0a09090303050f0603010606120f06090608060a050c270411070b0115261003050304080f0606040204060f050c0102040f18050901090819140a0201 76
    0x2c1307002e80d680c100c3d0241c0c2e0320b00074000d491240d00255040301c0106601d8203034400c5168801040c6d03c541030b49c10102600d030400d09800c003003592560020b4490a400d410ba0682c83d1201810182030300d41d43d2051300b00090000c0e02e40d500300c4c907080d4030801c401094600001011a03550f40958107aa8141c0d000c0300c4213030820020018144601cdc0201075020301160481d610344a8824208000c0d21001140a004422911201030b8951903d034003000382010302e800c1c1140c075a0a18646072200c1c203424040c59421307018650502400c41d00072040c00f0410f00d2468910030f1000e08525104040e007000030302050f0704030962000000810010310051010742407030000340c06c0d5180700746c40c00c1d0300d400700c094038190007648100701c20840c140c0e10000d000842895850040d540300e005800990290141e07800100b00c03101c2200d00061010068082e1032506d2403500414031041d5582d910f01401c071900400058480a01040304007805900301600f102044224140460086050981028280c111b03c4040000d03039510000b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 906328714 1250 906327464 906327491
    0xf062a0303090b090105090706110a0510020a2010020c160303110705031902012303100509010e100302090a020f0f07020f060313060507030b040e0c04060b040e06121f 73
    0xc3d0396002210704024440350070000400c940d40c01181c85a0001c00a0400324a190600203205c0c42000c00d4110b02260041d0041d140d48200a5002c0c0c10a00f000c140e800f0b103000e2243d12202d4990144200b401c0250651041501c1240046d610803503414449014403403580190a07411004800514060783e6403a4030800150011460003485422551195024050904003403c0000300c8500b00c581c286052030b0140c181c4d00c0701d80592401e0404040c0340d0100402003141540484521108442044854031107076682c1e81184000248143e5000c100d01c10104000d102500b401101a41c000041020041c501403080071580a1a088404004980e42001075424150b20b80102d200c100700a049a4252450502c40c440451001c10340400405041c0c0315800500081d0180d0300140b10305d4409030040c8005040281c0690700e50005a114500c6140f8045001c18043d41e0401030b01d082d10341101c41d00d241a140c250400c6070524980080081510840205542d5008516144120001500d00100d44411240310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 906329964 1250 906328714 906328733
    0x3080105090c16320a1e0c0b131a030a15050d0b0a2d051b030c070309090e19050a14150604020a08160c0b18060a02040f062a030309 58
    0x925068501c0300041e44040f035000c50605d50f070b85d0307025000c3c030580e040982251030340000d4070f01c2c098400d00d0700080004040740480b005003244c1d400700320050fa082c2e84034000c0318010076a1030b0150717010510a1001031407102c2d1035486108255500780040100d035a42c2c81c000341d95008680710031901c24030241c084c042402018016540c8201012071035161901c14113180000115800b048181038a8940b00403070b8048a480c0c1349d0748000704860785c5e142d55901e0300d03000c00306d603d84c8800011400140109000103060020344200c1c0210302038180540714503110650f4046402503007c00c1a14180501000800011207889904410a5001c4003034403c442c620040d1a41101000780224011340c01085241e2149521014507544100d480024200744280d615003140d42404094000703049844510512841071041c404207081840c0c404c0072201c00d90303105640751040e402603208503080c00d8081c0700c0c148603582c0503004003035003440203060b07943c5002082440030210386203400064000c0780d0703291b80c104203010300c210 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 906331214 1250 906329964 906330023
    0x8070f060615390c0b0703030203061206041e030509030d020c011209022d0904050f0d020c09180a05150618151002031209240403080105090c16 63
    0x2c004600c243d910180380030700c40d403000111030f101c69a1082c50410200388a010003400034406601d0300c030001454003500075402070715000d10030315100c40c400c0580b400015401d03100c1e5a1040c40c4402034019140d5070300070410030b20000c906000c4180719011160720f0070001100710400590040c02c1c4648a0000034141c00400c40c41f0844281c20003d03c0409a201c1600412064000450039000ca81d500c07180f04401294012646612a00d40c0042c40103005002442c203544004480585051415015003641e44c1c080c0403141c95082200c000014a24014041c1c075083c5210b06541a40c503041c1981d41c443e402c050b120100e40c18914181020302c40340e400c11f111070841200f001410820349013000c410f0340348a01030065040744590460300054508604c28400d07034404c9032404c85080f6250625150349916a40c035240050040b00e00e2032603408000d000d07188a1401280c050311782d202564281418804400300043c4078102e140000c02840284040c07e421180ba075a02516506580c490304000030300c0ba40c1c0307820 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 906332464 1250 906331214 906331247
    0x70b0f040b09030f091302040302130b030f030c060a0506030a080a050a032d11210f1e010905040318031b05010320070212060705070506091908070f060615 68
    0x6003c183d054019140865172103810441d10003446004084240c0040e2085401c000d4005035443c03c0d885503003503190040002480b00b1015607244100d5081001e9481c080c4050bc1d82c15580142c0124440c015075600032a001030001d010354002e12402e0b1160001da03488101e8460024400103400500c0740d80c075201d8501e11803000c41b480002c180340d516181b504d414002e50003034a0780e942d560381c1c0004444000304549071840350310641c110502035581212040c02c4211040200c40e110a00040d0410001c031003030101c440040200c2c2840d83c1d0078540141d00402c0300034000c07414480e0558107511840e10110900c8000c1d0712139221029940241c1c0d0150940d07070790030341c040c0c0d043c1800c0c00c0d40d8110000d900040c034890445035003446034440110f80006200c00d03000800000103402138405021003550f110000340721107070051084a1413604da0241d56562482c514401d07100c185042d002540020709020001e041e190700500100f04043e8071034451008032060b99020390003410314420309280b81c54100310040c6025844 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 906333714 1250 906332464 906332467
    0x10306060804060c02070503060a061d01030b1612110703110706080a0f09020d2d080306010503070c02090f0126100209030a0503070c050114131406070b0f040b0903 72
    0x1404005018081d001d80000c0c001c0e511100b0200609200704203880051000800322603090030010382500050040340241881c0d4096a035683c0d0400030301703840070350482c0da1110b00481996180c40b030280c5030358469070188040200c40c0043c0c0180380800d024840711010924402a540c1c040713460054801404810b151007071b600081070400100e0340000d00071780c1c041780c200030200e0b4846520090354010410303148003d5000c8181d03090401031080d446030708410000d640346c034541450124207004e070010b01e0101008240b040c0400000311594464005175400400604011007200110340c009914118100c400d109400d0030030b0010444032140008203440d0440d880c010310030002441904945510588400f8812190000798088142d20200011021950810203503901c6203210301d8803624059403031152034000742500020b00b603c01c03003a500321000d1042500f5040d4002d807410508041903001c1c8003565600140c280700c0c01d00852104d41d1703036620480619803e41d400d45030a10703203880b4003a03010f400081c070b9900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 906334964 1250 906333714 906333719
    0x6060e0102150601031d030304060608060c07030c060605120f060105041514010216090506100e01050d090809271305120c010912020115090522150920010306 69
    0x200450240c1042482d1080607000d6500c980050b000f42950f1041c5009003403111288002410340440598001c601c12001030103c1503658003240d555a40544500d03902800c20031010000030b000b0580c0747c104078030500000c558240d58000081d0f0904203032122008582090b0b60601c110396080c0082d90240c60101ca0811000d20f01c1030038400981240d000e1410001c1c050080d0590507802000600a0541d41840145d03045448070b103640003801c02030340d4850244038049260300429009403001c52002c1810303074541d401d1040d084038000240c500064242c40d403034001c000d80d1405440321044421082d0b00661503242409021a0f04c540c0c401f070086c0040d122080704586400000e00205d69200310b10310b40c001e0107483c1c01501501398014000d03114020311481c1c00f503001404498044d0410241d2400b031001070820b4694a1242c1015600125599072107641b0311203a00b482501c0310014030010a0003902c42c4000f541301c2c404408202c50080a007610003000c5160000da0040c0c08036600700d60782c0310a2805100062 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 906336214 1250 906334964 906334967
    0x1c030618020705010b09070f02010501060e061c060b2709010b0702061c02210f09060c0a1107060329180402120d2613080c030d150906060e01 62
    0x10000d1180120194002402900740002500200c18004006284500c641048003000e000c100250303c0140155080c074000044407401410b2002144034060316042c50451a00d00721040c00301440e04901140b6a240703404180e06203403002921200140080216014440000d120780011400700341601c29900355005220303002081003681c02141e8144d90b4075031910801802c3c1101c1984804007020200c0c8085401c20319010340a03620302c60030744800390070180e83e00c1c0d40f415826680c070102d420301c1d9142d01c0403020442000100700100720110031071030040032071030b51048040c0c03c000d1503a205200080d1152141c02101c1c8240c64120001c902c00941b1140540c1b0000206a042c0e420148500000d618800081c0a41d1140324a010300005441c007034540f440c0d82000003401c09120807a40c1075190414058052240000c42403c9000e0000720035441212a6140d4480c0c1c100c0e8045104500c0d03900082c082800d07192028041c0704110064000180609418804208225015a80094104016510780201e0f80c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 906337464 1250 906336214 906336239
    0x18090f0a060c1701051503040201020a08030a021213020d0b0627090f071202060706110a080417040f030b130c0608040215040b03060910260d020a02010807050c1e1c0306 74
    0x46e5000e20544a54072800181d05021204201034441c2e10008100a6039011541c0180b044800d003400c42215600c2c0c144064005080a010003500503080c5d894180210726501121580081e0080100200340000c102c1d030340102d004d400701090040541401e1200301d01090104220080050b8001d0840300e00d0035021103030003001d60034007038002c4400041810034003140c0e81215034003401c13041d10036035105a02200141581001c41c3d0507603807881c0c1c00c000001480d006000311801c03034151000c6001898103640b200c401c00d580180a21742c500d20308002c0500001d440000c4e920040c0b04640344c64160345001d005110746006102840710061000700700500200c0642800d07290440e8013512504e01a6580c0c452808400c0c42e242c220842041202d42c65405c610000d20f24085100070a00503101205c1401c0d130143c0c1d0b9111102c200030b011a20580000d141c07184108080d00c2809201011607144e031458130034440340080c05040b5404940c0001c40180701800da42403005403030740c5003464104881d03450020440c018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 906338714 1250 906337464 906337489
    0x60e0c01090e070e15031b09101407020d0308040c29092d0f0d0b04080c1912180b1e0d020f190302040518090f0a060c170105 55
    0x1809002c1c800b10700c0c8584500c102103850f0101410f4240c0f241071002c1d074914150400c42e10070820011400440c2c000440640643d00405e8029261412040c0d181c1d50035600000050001025240103028650141e92030a60107103406000781c031002034a081c60b091184031400d80b41c01a0700c252000c0404401d40d00200c181e64482185040302140d04c8645603c005001d0b40000c0900080b420f880c2e080d10711800c004100d02825441301158035a806103000d030107003c1c000002c910060110301c2c01f2000100412040c60052400c050380030305984610080006541d00318100d1720054480164881c074407072260f5003002d0f100c04840b00f4140310700081d918000719000c007441040c2c00207c000007580380c01155840c1c541d00307036410326101180540d182d03042d07525260902d4120340300540342c0a480e4824140924040c1c400ca801307071600944840c1e80e45407200750500401c130000e8400c034072510401503950100001404025400740c4103200119200300c406c0310007000301c90184110002030711020010030a070f135207510341d0514 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 906339964 1250 906338714 906338729
    0x250e18060402010807110111092112130312050301090f09050607121e050a0b0909060106031107050f0c030705221d030c070f1401080f10150903060e0c0109 68
    0xd945e2514000c582c0194011543c01286d0708200c100c519004034240a050b0101c03003a56403901c600818040300e0707112004440c4901d00c5400484103a0600481c0b100107110856102c0c00581d150303030f540e9449210015a1a80003000038401200500c510001382c09604200402c204041c05010110b445940c0c45500240241d024040c44001d007003100c240e41d4000c0302e10003540f0a46010340f0034030b1811200151508447c0a03001c40c0c0380c039140301104d1901d0401e95001c0c00000b0700a2011f80e0908805078000e0100c3c2141741070301001405401c00059003004564114130001014120203041e8106061801070176030041445994101450960501584d00f100301680b03840300003103052061150300c07400a0782040791280860000080c402034844000031040b04482d0303d401030700146580c8801c00a1080102900c0a000404006c00306903002002e00c5101e40000740e9008403007134a959000da00384005031418041000c916106d10410170320145205908180c0b0b0b04001422180340f624000820442c80c3d40501f14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 906341214 1250 906339964 906339977
    0x7021c0209072a0c031505010b0a141e0702090604050c0a030f09050d17090c0f10110607121b05030f041a04081801021b060c250e1806040201 62
    0x181c0c003c3c040b800502049924060485521030076003070420718121a40801e40c5e0941c10b5200545c9031004901c146412910507481c3d49040440003c401c0320102905c0080071901c030b005100c080b15201c100c0303102c0e61140d2212908a540e03100140305010741550024001c0e44a03915210410501d00c0f1a181210302490389407400107030028104403140018865000054454811480c2c0035003e02c2c0c10940f94800c43c1c10304980b92030140e85288115560328034001c1c0c06900139250361007809a23818120f00341c101e1801541803040c41c04100342c02c8140b80c060101c446000181c21142800748000d02ca01c00d22040c0701241c07a81001172080000701420358400641072040084000c000601402821580260b185440c01007210107820070f4100105240c20800020849044946492000e58000104c01d0041d294440010f24922030403002c01040380c008189a1003a4011405080038041c1010071400340c543c10719044c1c0351401d042021220500200600090550540e1614410100710004913694042e50901e8401c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 906342464 1250 906341214 906341237
    0x60d0206120c0903060c160f02040e25060c110f180106031a1903060c0e030f0706090e13060c110607080103031107050a090b0604180207021c020907 65
    0x244541c031862111440054403030062040e00d90407000280300c001001c504861903900c5118480406100b01c070751040030200e260000c01c00043d419500c4c448558001040065014400c034002414a12500c00212a034041c030250340e80440c24038403411014041901c0c020341088003e545204c07000034160085446801d038409a40b401d0b558540c00030030080c04c926040700555a44513409005400c040e10410842071800145014505000001801d814110b0782c400101d10b141d600d900e0000c240c3c84c1c0c0d0282c1080401c0389407400300d880800200100f40144402421020300c6e01c00020400111a00841c600c1c0548400b48008100c004a036000080c1d042503001404085561007074400181d030100c060594000c26082060054001140f0341c122802901d0356900c04181d15402507c828260082550003001140240200091030740030205c0b002d03028102a01c0c10792980210038022460f800d03a20589500003032250110b040101000c480d07002d2184010442400b181d000401e0106d004044104001524005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 906343714 1250 906342464 906342469
    0x80c04020d02070c060503151807030c1206030f1a09121305040f1a03391203071e080708070204110c0c0306093903030d0608010507020a030503060d02 66
    0x403a014558011071407454580c5e207101c06020364000300d610300d41568140441d030942e400d100296606880c56203401e40707501e0b038451209800a0044540b07810420100c600da006030a0203512600c4003450281c1c40e11089040c06141287c034013280007801a8501c400c4c142030010350039002272681303400803034540010b0311080180900c2c0b407070400b190f0295500c182041001c449101e226404140c280d440150451040070040c814503690f90740e4488031001c44ae80321040314107241e144c0e04a002100282d5035110420b0356035100000c0b41240d10804450603504002082001c010b08198240880c2100300f9080450040c41e85400402d806582c01c0503051410004101045580d5030388070142105500c0301c1142c0310751350681c03129990000050254040c0c450600400c030b006900080c7c841c08841e202c12000780d034410103110f00b8021194010015100000d1307034243e41c861382e410b00c00b922001d001200005200c2c0d1400e400c441c29120090008800c3d90031024200000c80d60100880358084403e407240452986140702 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 906344964 1250 906343714 906343717
    0x14070c050a0602030f150a0503030a18030b070f11010902060a050d021603020f0106050607020f0f031e330106110a050109050a03030c1b02152a1006080c04020d02 71
    0x100240228400400c11801070000302050780034071b007504100b0503130620361403d10070b4144c0103003c0d07164168004d11800340c8061155000658a21040a01240703a03030b500e40d100d07404e140b000d4401740d0114110394030040b40c0d1648402202c00e44100c1c50b00038029180e00b600810741034842c0205900420100048072440640140c040342e505c01d51012145003c400703d410025100d040262003060305500340500007899140900075501d0303060300244248400340300c0c0000c1220b00c02451f4441601030142e42e107200b00950002e044950700d0b51031803010b03100d1b0b0b4000b01e99480741400394030111503907840c4600042059072a070519050540d0410b0034000c8000302d94aa1a5250140110700103003690300340019203080050101c0c0c00941d652094606114040002e070f400d0742c100e10b0380441e0041c072605400c0c0c100e000d031500b5041a881d003018406910300e000340d6001102e8403001c48040d2031415011540400c09001803c108060b6903003000300c1d04020a0307040c600c00356100c969048032284150b4010880d0170060314640d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 906346214 1250 906344964 906344983
    0x50702011106070e031b030718090c17060105040606020c0d031b0501021213030c0f17040b0c06060619030e07050a080610050a0303080c031003171b0114070c05 70
    0xc040310b089251048008000d4560f01d00b0f841d00074021a800c0300c04048011000c5199400c0007000740a130b80e410b12003451440f1181103503d22005171240c08000c04625014134410240c2840c40b20850450f0300400d40b20b240c0f15041c0d00c06402145031403004c01c500344d40032031207051120b070445104803411814102160703c0c0300c1020350f0303199240c4074503034030010040154006c042174180c002e1454110350322080000c011000ca0f01e009800b1805036201c00000850100fa0040310324852501e201c81284d4072490741e038480d0040d4018403900709001a59411043c001c11159901c20402c4404518013048004254804803070221070405045e22120481440002409030101602c409032010031496600c44995641d140d06030740c02c1a81345d410302c2003c03407203042498400080d80e4043e207034014291545c103080c101a60005025201c09040c0b8440030002504003000c65803603480b80c807041034480300019203100e502d48580595070b9107603240444203005c02c0c0c910001e050380aa85420700303640d031100a0403c0d6041c850b440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 906347464 1250 906346214 906346247
    0xf01030605060a0e13020111010c0f201606300c09080f0a02090c0909160302070507080607170f04063210170705060a0903060f0906051605070305070201 67
    0x83d400c200841e19030b0781035105d2090013641c0c2c1020811102107054203d500c5021004002441e411103890a240a5205c46040a030044503c8a000c00601200c0b414803d0140017003041c06801034041040c03581c45080d03100250403544203010610460100e580075810980a040b107007070f844e80c0c5525400c50056503c80000c0a8039810782d581d00560111031030300c40c3c0f0311080032842400d0090110f071080b4091819125103a5001d80300b2191502d0b41100c8032244600c3d001505e040540030000e42d0001407060003c1070003007203040300402150605440203021410700c0201d840050040750100304103800026041508940c1040300003a1306401c8250311501d854010402c0c80500c525429110700c51144004010b00c80c2e284400099020b40c0c84a010311500302ca559518482544100303070900c400d2426900810008825040080510f0341c0c1c0d540c0e40c8166a0b003156841d069654900b80c52051003454003070700364010b01c80c050b5558890540407002e4494010718001034200000496442c045902607002c2c05a0761004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 906348714 1250 906347464 906347489
    0x20d2309030a0b01152307061b0206040605070203090f090601020a0b04201008070f020f0a0818040606020d03050c1b0309041b211b02061b030f01030605060a 69
    0xc504003e44078500c20320410320701c0d0805800329851148101c1c64101e014480080040e031480039003600d404a0f40125409481c015540c2400c00c0180390000d40491009145402906651800742022012240020808025500300b0410507103503a840440c1c2440c040001c55800400d0b0f214100100d1410040400c000c0c0f1441031a414017050101200a4502c00c0000d0501c4556000741d01050040c10304c42e1800f110045965140802d14060003041e0040d000c0c0b429204a4410303501d0322441b03e01d0030034400002d0300c0602d00000c1c0d80b07100c0e10021030310141c40714081d0303802d01985280000c0255522101107001d02095a0344010569004048007202c2c200a1421034002469100c422000e4417603212900d04c0d0b10031854a0854141c42c4c502a030030504ea106552107800c9000d140360070001e009e291018a0b8000c250350340c1d00b40700d050308100340e0703071022402075600078065441c0088204400d021510034004400358280b00304050410031041081c1074a41c043c1d0003007480c1c3c5901e40840c0c948441608039503250201c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 906349964 1250 906348714 906348733
    0x804050c0303070f0605010609062f030a0309031103160b13020a0303050901020c04050910020d110c1507020601140105070201200d0e09040b0c0702060c0a030801050a06020d230903 79
    0x3000684d40c6013a901070681044582d83c2c0d2a01603c45100f684914030220f0302c01c400d100c4040e126080100d0340000b1403621182158403002c0005c1c20759000c0d407000004241e48103041c81c18142d01000e45a1900b00113401545400c00c40d00700d01d911050b481c9001042c940c100800106103114814160040380d80c003400501c8010340301c1c58050015003040081328014441c15034004003c1c5814040c0034006c18407003015041d06910211007001a511643c812010135485820442103180c000d0020b21844c580314024204000c444104410308440c0074040d601150701480c01030001503401000070311342440c01d0901940c2d8101500c0180c5a03004440e9140340c9401541c824424094804030b000794414140c2c2d0740da106809160000c001c4000011743d03025101d503003000001001c02440c0c0004040c050300080042d13040140442e800c52825044980450000b29800010040b9003000c40ca420040c01890028010361115040000e0151200c0b0445181c0750320010001d030424030b010401c54000a101034196200482c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 906351214 1250 906349964 906349973
    0x40c1503020703142803021b010c02010605090907051c120906080709030f1515080a03030b0a2103050c01060b071101090e1306020f0a0f0f030e0d0804050c030307 71
    0x401030b203401e4000c1030b0f690000e050899a0801140c2d9141064144400d44048442c000e21548410380009030515a00308020f403250751040c3c2c0c21410390002c881c004954100c43c04002421341c2c040e5485140680c0154041c840c04120228031941a0381054071200a0307c000c0010b00c1c2c0d00040c41300d6001d0302c161490188402c200394040003c00075130b5980e0301e802c4200d80b142c0c40c040700c0d05580c81c4805816400305030340000008100800001e1a600c00c20b0300171450b880e01401e000c07101c1c103140c1d102840079417118803410708040d0503003d40c1c4030300f96040f50284441d9283c411500108041e440c65000541c04003111401054080c40990302d071500080001c01000c0c0c0c07621341c441c44581c0840025120701d42c19800d8800e0a40c802d900070015100c203c0385284103030b281d40c070b4803038520401c10388100e81682d000d01c1100e8a100d070b0a4040c202055240e5541e290580d1079500151000d07035030f050098205410411a204401e80015584101c840c40d403429031003a694a007005810242c514a0180d814000000c40c1000d10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 906352464 1250 906351214 906351217
    0xd08130b070f050f0d020706030203060a0503070e07020c0414070509030a080d06030209010506040b041517160e030c0105031b04030507060809150603060a1a04090b0a0e060609040b040c150302 84
    0x1034403c03000c56006040e00b40e1160f0741c03031541d03e40b404010780c01f02c0800e01405100343c02450700100090302982c0a0342c0c490000a082600d2500301c210282c900800304540b07954108900e01740d002c0d0a44003005a21905030313442c011324000601d0a4184000090307912440e840030055140d00c0b641000034140c90f1682c014450001c0e068074441688101c0032a000400d40d4500302040728119070314881420720b094030b8020554800684030000609200044580844001d440e10303680d480740014000110050100c124082c01e426200766130107000381e001916200003a40c100e02103e81281c604a452401c4183e0710109045600c55500014102d0081850000380c26800c16200b6005050350070940e182c40340c031000105443c0d03001f151920b034964802c0001c9203840342244e100206041e41601901d4810190703401040039110070010072030b400464003040010742c46003441054252240c510207009582400000502460130103000500000b40c7c1402080800828080070070081c04050041340c2c0c481c10342000540207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 906353714 1250 906352464 906352493
    0x30601030f1107031407050601081f0b0919021b0a0b090609120a1e091401030204030c030809030c03070303021b0906010c240e0120090d08130b07 64
    0x1181c1403404490460149000c0d2002d41520192001d05040854404407178180060103e060107005c10070160300800c800303010381e0303010384800d400801c940c00c401c0306015400c200840748041c8485c5480104402d9603907010030250021240360b02045141c03c0ca6001300020712a0040303003032020540391106030107160049801d140290058000940954540c1c0440c0e4807440103e0b040225504007080341c00f20324002d02c0141050011a140c803ca200384040c0f28100d241c1d2640030010042841090104070b0f848501c10817003000c8000380b030207600305441c5a0381c0000c82e80140c00002c202c86000b160b21241e0340c038200306607a141d2100a040300c07060b03546da007806511051501100c080c03c81300d101c24a561410250100c03401104181d46000340c4845c1038803805544240d58903854000d081156999440708118091003641d4010100005900c1e06000d0308400400001c0440d00d043d40d90912607011035a583d40002031040340c00c81515030380ea48007922030680b00e00c503035001440c039200c0202d1400c0c10f000c0d281c44855003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 906354964 1250 906353714 906353717
    0x9020a1206090b09010e36060c0a050f180306160905030c0f06030702070e071206140f0607030509031504151a12010603050f030a09060806031e1e03030601 68
    0x9854071111000300780d0b03900e640f50980003091007004001100d8024001c0d0b500115013480c1008118a400f8005003038446d02c0c004480c03010124400d200140d4081c0181508651094140380c940032030007030090064007480ea2608412000810002812140c1d52420407000e078006081d41c405141c640d0010525100100c2c000740002c1740e6a00214460400240a009d5600e00030704000c1c80301d07003090410190b0341c030040c82d41c0304500540720f0025902900400c6540601e52a031a4003154030201c142d0380c41120107543c40f1001540c00c2d00424407264640c848052842e000541e0b05d15507840603030905a40604c903010f8100d0b0076104884501d04980701c000d070654010340c8140401a803514201a0308004d60360503903c0c0e60205500e44144004a160220540714409004000410032680d6502d541e802d03e040145648215080080c07001800d55000d07006002511640c10640e202e0300700000440d54400c000400c4e800c9215007241c0754100d4207030070421042001404c0b40d0700c14048600107509030b01c03078006541190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 906356214 1250 906354964 906354971
    0x905030f0a0f1d06040b180409060615050301030b130507030c08030318010212190603020d06051f0f18110a0903030e030106060c0f0809030607032702010503150a09020a12 75
    0x4841d064070343e402c501d01d0701c0700074120303410706081900c41d11050740134410080c140d410b10382941c81540c07500d0246da00214040d82001520078900109458900001c0c040e107000c000081005000041d0403048003a08019030803000200d0b80558030300203180c40c0c401c1e000604022800b020009440c040007009510445114075084c2030b0581010b0741c42c1c240d0045111940b10003c0304400110300e51500317040000c08074070003080854115542d4011805c605158041a983d490b00c03002080981050700f45c5908600c60012140046a441c020030700301d2070501400b48030b4141e82d001c0c1c1e44034015102a08507564045000f11132a03034900c0b050380302418000c23081c0310480c00701e2641182c021042c82e06200e00d000b181c0c00368543c0000c0089680c3c9900080c000c00c80c0031586100280031031040c503101000410321584003910001000c0f0400142005203940d041084000d8007010103103040140d9005055903000004481c11142c1c1302c61400028000003001d81080345c000d8800b00380041c0c80d41c2d02c4030141c4041c034011030080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 906357464 1250 906356214 906356237
    0x30203031b2409070e09060a05070e121e0f1005100905070e01091e1707030b040f260f0c12131a040b0a0507051006090e010b0111100905030f0a0f 64
    0x4a0380417600320307148800740e0004800580301030840e0f004680e00c4800d616028080c12080b03800103880c6240400780c11001c1d07006443c42245100080350030100c8600c114001e08407040103801c4250b9500006d00004052038590b03000c10500c00c0e10000200142400c020300b80198a0282c00051a20780c419100500150022100041c512110011850700c2442034000d4100c00f0b003410318500705010441e44074030040c81191070020202d0326030540c6038010380c8142d0b0710021445070b6052a000030070002d40703001d10308c8952131440c0c0d5101c841c2000711120611449400740e101c4444030702140c10904103414103910704000180812420803001d00e01d0082d28912171207402c03c090303603041030312960290f8000c0d018108010040403030f8080c020005002d50320312507406c882041c06100c01070310990b22142e0146034880d460710a0f108003c40c081c0035071700541ca820318200380042802c00041e9a00c00052554446040c1d03201e180c0c00c14000e042c002c841514948107140356840c1d0320118000c3c044120407104100107868030050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 906358714 1250 906357464 906357479
    0x9051e100c120c0201020307080f031611060708190c02060601020f150a021b010905031819180204080613021804080d0b06070203010e160f030203031b240907 69
    0x70611504036074072a40c0e032406814256595010f10038268150b20080c42100c0008000c0c400601840f41c82c2c8144039220300340b081c603c981510303121038484180601000703050300c0c00b080081d40f5030303000300e80345441c5c0c1060310703060118501c1030302400995a90700c1c100421000429000568140a46802c1c1d00701d17070008106c1e0060300d4031483c2664010344896249808030342c0141e4250040c014440c4c1000e00c1c03c1005007215802c900312140340e02c0c2100e80f6040403d19992445c908006900c00132030030b4555004041013010150301c02012400b648001c03124448003c0464081d6a040c0c0d0301602c048403c0310941d0a02100c80d420f1001c032074408034410582c0441c049450103c25140602442c0c1c4104401c0c244841c10a10a000d040b01c0404150042000e1001c44051381d42401508414122000035141070100640446c040e900684c0120181a02e01074003080161000022100e0a45140040f038000c070320000f58141c10010b9101c042500e26215200c00c1c504800c0c1d0040c500d008420a0080314006540c0c0c240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 906359964 1250 906358714 906358727
    0xb010813030206180312040b0624190909140f01080a030f030e19120210060f03060b190b03181603230709020c0c04090209010506070309051e10 63
    0x100140c1002c00840c4c00b80c56203c5522a01180110650b82010400620311080003022034040d0780000c1084213000003810254240c010300001d6583d01d40d5400c05100c0508a07a01c02c01007000045c540b07100a41c00c0061007184c00d40050103c405d800d200080c41103101b80b0440324180c96100c508a880400098a00c400040400c41c40798981c0311030100040360403081d0010300c1c40d85040e21490054070784108001010300c0034499054400c8080b950282000b500c000c1c540511f012024001510300710040c040c610414003520308880d44a40c01188020700c1034041074180203215541c10101d20707103c13008250150643d014520881c510142038409420002a8555801041170b8503140241c144905101103196110266504008e00200d10002d08001c09240d01e4503140b0307401042c00726030210340c05080c3c40050110039a6620207c409000100c940d40016103001018400d040c45641c2c001030440800d405042084000c1100421465014044004503103518925801e400e1290ba00c420000300c21500411 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 906361214 1250 906359964 906360001
    0xc05030616050c03120a091a1512120a0306030b0705030c0d18021905011103120f070c080a080a0b0d050c010318020301180c050603071d010908060a0b0108 68
    0x1182101e081005090540b815809034502007070502040214140445508040500481c04c040c0300191038107260500e00e901212450781184468404028881c1c0001007082c05015a2001c841010810f94800c009a103001c84051100030b540902046d450120360301540204100c034017400004250b13690348001101c1500c403c03152401d036242c0034051812034a00395800b400412002103842001d40003d078000401c00032403d000000c0c680e0344654180f0240d41d21241000c0c00419500066041034a00e450590980300000c20280409000c0742c001041c0c2449680c5040320250040003299444841d008000c01042c02101c08003c440c0c200780018427941081c8013000006034000c0702619042c08440c0045024213281075a0b1103041080070080d4015940a1041034503512807400c2000c03e8246901d480900c0d4251680100c5c492481030040000301d40c0c00400b90b0024500581c0104580f030460b2005980440c01071300085258400d5108000c032903011544840031100d400d88910281303550740729000701da404e100d9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 906362464 1250 906361214 906361231
    0xf120615180f231c150b06030a020915070804061e0e0d020406091e0e06100306050c0f0409050613110f0f04080d02071d060d08030709080f0a0c050306 66
    0xb003420000c0100002c0405460240100c004000c1140e800004d00c0d08103000200ca986040384001070002c00543c0080003104400703203c0d09102288050780040d006000c020b1180d1500c54001078000400e595402910407500c42d0b40d11000d840f80c00904010303080f90040c0c002c09010a02c0700b80314941d51604e808811291b030155588400c1c100c640b80f4140480c1c1c0c07048440498100c1e4030b4400c00f1a920320700b40074691942c06480c152261222840d00703842e050365810407400d48950400024043d0701d400107041842600e420500104c2e0325200c500e84103680348207100c01009662001b1401042a0b1880c1e0001402454129505802000e12202a0007201c030002d2030140504020410342081583e40b4028241380c006800d0107904142d51800300d0340c2407014010101d00140c02c01c03403040c070003440c00240354a801080c20401002d03525080000c140341880e185c0000c5c03c5203402000040280d882200800003030300c0240c0a0b91202c140081c2c030b0580d288080700c01160301007020355000c40c4d50306000030000d110350304a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 906363714 1250 906362464 906362489
    0x20d0609450602130503030a02010c020624100e04050f04050c100801091806020a0c031416030e0303090a0f06022406271003031d0d030f12061518 64
    0x1555204002913006a40c1910401e014400005042d6010b002914512066800104410010202c000c1c10508000c081d42a41e20700b52403560314901484040741c4030750001380c9580b104203c401005803120019410040d9106040c0001c0010314035070350301090b0166100340d04540d041c560305010406404e04c68209003001501d4240108000300c02a0001406011000c095030b42a0511f9101d4005036841401040c0100d800700604a04042d400310f90b00d0b5001c1c000241160030081c519120402c2000d1400026080040503880354071280c3d8240129034440a0040c080443c041e501e4000301c0c000c203210f1052001500882421a1480380c803680045211f080c41c006091443d51040100800c010010b043c9501c120704002c900700011a801c45201d0196285440320002c0c0d0b4030f5450010031130a0140020380b1040240c00015405803141d111894030154076041a2600f85a90801122802c150010720b110751401d0107030006507402c041040d202d6505a40d91200c112561a51204658408510a62125800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 906364964 1250 906363714 906363851
    0x91a0a0c02090a182303030c0f09040b060c0a0623041403040509070302220e0402040c0329181b0c070e07020105060a060e010c06020d0609 61
    0x510b41402039200140c04000102c1c400c90302c2004c0041290348504654900480004a0500000c2010b5041c0d100c09400294a14500f441e00003802c0d00075450b503400ea0100c0420854015a115004028410130140801d521030030600a00d50342d40b241c800c810b545061920310000c0c80b600c00c1d0444d80c04a060780e07070454061a00d075552061100d2800c0ea031590341c4c6000c280000708844c3c1d925250b03540140d100ea540940c88401031401212800c400b400450640414001c04000710102001003540c451f40494000903603900c2c2e540c0a401074074540d600d1360600c2764000503c2c031000d0400001c205009105031803601303105101c45244542d052050780d1040d0100c0e220a98149454880001451050000703400d5030031702651540e101d511500300740c03021000350351284100900d9003841d8a0550040c031151804624080c0701400180074401c4000740903004c1d40d000a09106902c0c4148c102e8002402a0322080142c41007148203410141e072040c05481c0a9071402c492012010f460300e0305d50240c2e08000036582c24214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 906366214 1250 906364964 906364969
    0x90105070b0c0c0d11070510120b03070807080106091401030209060d0305070b07030c081f061b02030303011508090109050303010b0304140f0609010e2d07030f03091a0a0c02 76
    0xa070700901d0a031000c0e40c200800341c0c101c0350a20868110003074980311410901e4484805e14203000c1250410b9003d83c1401d8086075016030701900015484480202c00102035944034007003800c050050b04010043c2c810400005901c01c0b05510010841c1d042c5101000102c3c40180407041604007840040c1d40a80c0d02004126107103003926140840f0f511034180b1741d1810390b007079403040c52812003200d1441c0440d0b600d040034094030382c202d07803080d070b101014a805c01e104801e10031480c040040c03a402144c0400582c41e42007407505a4100e00d503411141c0080840340c40b507a440c82111254940015144002800d00d004180c145105000d64000300c0d40c014007440c00c6a0078100e1071071441d00000d10580d44c600b9001e13810600d001050001c407150005140180504e442c11101030350a640055840b03100f2544901d28107082c4403a61440d8140e03030050341100303070300304405035100c41d140c840640c202405070b80803007054104158009251b00110780c004000d4001101681c42d00344e00f2406042144800714245844100061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 906367464 1250 906366214 906366233
    0xf280f03110712060615020d02070905062103030601140711041e020703090e060337120306080d0813061d120702130603020a1205010209100f0f0509010507 68
    0x1c280d41c0444900c155608611036016504140981d40c0650303c800038042c0b20700392808200344e03040e030340024210310502000c025596201403160f581340b560340720045003d5950300301c900c5c0c01c101005070f154142c5000850320385481f0742c0184e40441c08918080800355610390340c0016101500d4000b042003034070b503002d61b003448007400e46611252018480046003d000030b41520240045900940d14100958100311910700070180183c055846640a06140034032681e012804101120a1032001900951080c031601c0d42c0d00e04210000b006040c4d8601001c2e1303080d501d030f80611b040303441b038100f1100b03040b103a0f090a465214080c5c98404444402c58804004500309810107140e580608103600070000c41003101e9401d081c18490940102240042c00b1415448d103507501c00c40740001c281040101500c0c5900003101000a2300c01c980b05240f0801081e400e100702907054400741c05028100e90324403984800010071682198004801184a52924801c440c0c410390aa4801010603110320385042c0850711103c111 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 906368714 1250 906367464 906367487
    0x29061905040506120603010b01050405100302180402030103120e01080c0912160605070c0f050d0f290a0f0b090c0702040204080109080c0d05090112020c0f0f280f03 72
    0x61050811000070300b0384604000703204c2c08400071003111645c1880c42c00c16003500c403a501c1c0b40d410414244801c0c403103540e8070034001607044581d003001650b03000c0014140390454012101558400d10220001003400b0461301641d40c2c1421955402c00383c101c1120054072422015210202205801c1c00500c00360b00305505840c24911146048402c0c031a040002820004641d8101000042c00880e4140c100300720409104050b08840100b80e42490030100410900d04844001420240302e00c0c8010050094440c040307060307440f464030a03c000400c0a409039400c1141a1a4401d04d00e10300b03048191311092a200c0d5445824009221040907103500940ca43e940c1c1001505070703401a030030480000c1c5250309100e50445a03100d590007649038842c0440c1a4240280200b01030284042008080c44c2603070302040c10003441c6640030b8016118070302262494940300c180c000042c418401e000e07504004241c0040d48008486e090b030100c1940701d00b05c3c0715010044050040040c60000814144d800103030150114000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 906369964 1250 906368714 906368717
    0x5270d060b150319110d241208030406110c01060303020715020c090412050426010b090f010e0c0702030102180a09270317011e0f0b070b04170c01290619 67
    0xd004000d0701b68000c40310035034210340a400c02c500f801c0b40c01000c405000402040310100883c4030b028152200011440300601c024440d95468012002c04280310342a01c1d0301c125480001c020440d103903e4041e686454a00580103105904200c49016500c0040c640d01321503c0030303010300d500381c0310341e620700041c03803054900c40051050500020441e082c9100500e0030005410200c1250281e0312800720703003121f00c3d0031b00d483e0051844404001c0e410361041c15143c1100d904016840032070ba41d07601c43c07859502a20800030b40c9940005050412a540300324840404001101c0c01c1000c6540d6048044c2107503496800c559603603003031120001c60505411300420100740203040051800802001030140b01e24243c1110441e417910b00031a1010503910301c44503010b0411481e00d40200c5060450845090040720001041c1e040780c0c8000130104085035400d010348a100718192342d01d400304c800096000c0c01a4038500c81c05502c01c00c03040c80c041c184590b103256031414054a0039146c270f440004020029010030f4071610 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 906371214 1250 906369964 906369967
    0x27050603120a021b06281206030609020f0303210402040e0105090307060e031206120a1e060f0b0108060616050d050a080604090305270d060b15031911 66
    0xc100e10900d40040c260b9941a034040d000e8100c42d45850024402c012605601960341401a08010f42c0d031080ca002d04c2901e083d00c02403402c0088013044504d01c2420076444a81b904000c800000c03c12650814141d080c421902c05142015170014150390b4000e17442050041c0c40c0c03036281c500b80c0018110321150024005031000c140c000c101d00c1820300355441a14840e5495000007540c4080c006148554a039644104000d18036042d401a04c0300101c1e40c0142c40b40d489140000460900c060080011030000c542c000c0100280207042601840408080a0103940c003504000c0c85001e00342d12403084901440c0c0585805426031100310901043d500110b03510011131141c030142c040412820803c9090351143d560300c243da2603c0c20300004002c0d20015020f5070080d070404001e580060b400500b540c20101c2c41010b4000d40080c00415031030243c2900382201d420515030b54283c0f00b40309040d00801e5a041058031045801e140d0040e0150003480704660030040e605039004018440291500b050082a401c0a42d06 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 906372464 1250 906371214 906371233
    0x3030a151205030403050d021b10050706110d060e060d030c050a0b041b060e0108010501030c230c0c0303030f0f04020409140f0105010803090d06020a1119050727050603 74
    0x1001d11005040c2907505920205080080060802402c40c4072130031407016107185689407540b10702545004e400c0520404030340c02c21504061240065a5115030402814481140400001e650a0780140640240141004004225502000d07034031030045c0c0018000c1060031500b5141200e90911040741111240214141c5001041c54907082500440c0210030801c45608245540d104d00c00987c1d0044051014000c8d03100c00503a00003078040d044450070300b40801d042c06140d0044810405004410311130004c11082c070b6202d4600f040c050030040c0007202c102c801005c10101016540d001c00c4400000c1401c0040c0000e410407028012260424030182012865582c1540c0d00006242c4403c280d03041036100c00846d0414100c06d0040c940144004406945000058404102252401c05003e4001600020822161403051020386200e900740810303104075480108030f605411201c2903098541c0d10450a004c45d80c102144241c51070386c11459100007400340807680101c050f1200030310881d414054102c54 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 906373714 1250 906372464 906372479
    0xa0215060607020d0c2103021908090d030e15040f0303050d090602040b0c0706030b060906090f0a062d0912020112050c0915031509090c0303070b070206061203030a15 73
    0x103d0072654800c45d103c03003160f8100f1000e50300b1a24214420703185100c5468203c000b090b004107000c500c1040c9018001311261403401e04d42c203540325880c04540c0001540c0c41000a1607406803175040d000710101e8010440c004803850340c0c00c02d17000d14000c02d07109030003134001000005d002c2d0f8000d150f041d01c07000c1e0128201040343c40c0c8108036085544048181c4000085400982805112035005805207003010003041d5400310224240c0d004a040181c000c80e8006410141603841c50302c00307c000480109840940d64840000804048100703c03440c161001e0304c0704001000b0780c0c41d61052030405c025542e00004c0c40c43c108512000a070081011713414803504010001d038001c1c0b580140c41c4a0030b01491926503906c0d072041030010402c000049442c0c1150144244401940c80c0050100000821220043c4a448005406081010404207a541480005070741001c110420060510420700c81d0289d0b8405d40c1e07444140045209600000f0140350007c10024482e403003507078045050818500d84074811161150b84 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 906374964 1250 906373714 906373729
    0xa0306091506170709142b02010f0f0212030c0d050406020405030d031a09040203072c06010806130c03090606031406010b040e01120f080d200a021506060702 69
    0x80c07510034219201800c1c88402e411000004040c020081c5180d0340c2d02c3e1030140200a00c5450140f41001c450301d0422401d0f035910701311529400c0c1d1001a1102d804258141d00c01e00040c41c9002c202c2c04100b10800e50006503010700540d85c00301c0e41079006000b13041d01032081c2007245c3d4401481200554403d10a1000b04c3d01280300f0144610b00c103490043c0c0d22820502014580382010f0300b450105410846041d03102c25644042940f481020b03035000d01c058070340344000fa0030b05945810000404900254010101e080b40c5482d00b0340d030b6440a981c101c5502e400e8011100e03e1011500356801c5070500e580300c200300308140d010b0302c8810b915180001d030016199440c0740c241c841a6000742d40d903008031008901a81818030515005002c0c9201243c6803a240011001106005124103108001034000c04401e001c00314101281d51540404200d40d41d140d00035080d402012780e00018528255907100302822003000720111600c44800b03030020002c201107901c0d18280c8003002041c0d2030304081300340060401a103c124 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 906376214 1250 906374964 906374981
    0x21b0a03140d0914100f020405130902040902060f130f060503190e0a0c08070e061c02010c141b09070c140c0306181009020a330201090204050906060f060a030609 71
    0x83c0a000403910542ca9081921284132948601c60310408c0108060f980d0101c00e84920700404802080c41a928000200200a54400a5008200000c0c0d002c034509100c00204007201418800b03070040c0762101060711201200e8020b200c0414020000315590030035010350880403031892507003c1414014140c51031708149100034200c80180d04060140100101480420083d1121a601c107429282c03000008903c0b070b074110380c40c62076031540c0520b00c0150b91254080403841c40d000644c01e00e01e140040801a41d80308022041e42c08900580d1902e080c624000c10038a02038816036540030a410301c035494041581d1110340f100111407186000c000309039201404608c0c4a0761450141440c0c2e03500001c00542400101c01c0c40c0c881561071301d4600e40050765201d0b500b8003503070900e524882c81c0c9111a540c0749401c0c80b510f0180181084040b503003078104d5505400c441303030061003a1020300c541d450390b2248680c1d814080d2080c590011a55176a00c12906225024081854040c6070109495507103591040444a444 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 906377464 1250 906376214 906376253
    0xb040e06211014010812040611030d11040311010207050609062b0c02061308070b07180e150405010f0e1308030a0b10080417030712020d021b0a03140d09 67
    0x840034540d4245a00c03880f5401440004060110007a00704181855881940030f18800d2002c030f400ea20040d400c4c01c00035681c031589844400c1141c5401000c40b55299000351000b01c0e101030401c00540425440401c48804a4802410641c02e114140c000c01185400c2002c41c024000500900c000c601305040280c80d130703000400000000d1164074a10001d0902030300801d0000380b2101801e8810009503150200c2d1a9290040450640f640707508000300c840d0203c102d000032180c9007014011401c40d00048401c0e014103030f9241200d034003020380418042075079400d1280500d8000f802004100214031810210f0340700c0c00500803410101419030b11030030036800650b0041820f96540040000314100b5115130101281a8100200d140c981070340c483d880b81002509400c200e82000c40401c0ca11800344000003105224070405549503001c1220340c03402500710310382203449184049506a00000c0c0401c9400d08540c0603540e0041002081c1004202c9600100c65140c078035541c0c9d0310b1b880c0803540b8200ca005025211 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 906378714 1250 906377464 906377471
    0x150b0d080d1107080a05070c0b2703010e07090c090e0414060c03130f0309090f020913060302010504032901080321010617040203160b130b040e062110 66
    0x81c0801c20115005030680784489802000b400001c19002800d9402c814401e00c0c00c0c0381d0310000c91070501c0d543e05140d4000a45490045400056203400f8003205110406c0c0d00a00b0425160841c10142a82e401480240103900858020b009c4000300d43c0266120b00f0060410f040c002d680c480c0840200c1c84211343c180d51200020f01162030400d0306100303180c0c010702d0384c80c00395045084c422501081c45075207000c000d01d02ca910666600405001e1000c19004052a030810040c0b02c0039484900c1c0654015250188200c000d404030302c05910491003140c080c4c0350103954460401d0b045a8038603c40400003001150344180c1d88408040d2a034240b10400d018004810155031030328000511001500d103160070701c28112020000511840e0b9001c3c0408501c40140c0113004284c1d265800802d042012440ea2442c8031002c0c2a030204801c0590307801000c0780c800c0e10008080032075965400c1d032100e0095020720559120000082581c03843c0001c2000d420400c21640414041d101685035031900300c5900c0d901a40c0c0c0e07107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 906379964 1250 906378714 906378727
    0x70c29090d2c0d0317090c040b030604170f0405030706030b100309020f1e06031e0108060f13030e0d05060117060c040303050f131d07020d020703150b0d08 68
    0x1d002030480702080074010014040108014146407020075290b15502500100c54014113161003078207100040e03e0707101464415400c0020b400ca44075502c142c00d043c000ca0a0449040190900095441c481c6030003240b41c0000307405250380b4a0141d800a2a4101d4619090001048036942403150200912040d10300199203a0484148469100707901d07904000d0500c9c1c18050005030719000411142d010341115085540940d00c034085142060090f1210b0b0011004410400c07044140031001542e0441c41c2c002241903a03031080525903d800440d0307400406401074001c02c07401d0824001030800030b446401c15440901d14200801e840e4040d4810076992644210010042d0360601c808468108100a0241c0810f2519507c000d41511403031000a080000010f2000c2c1e00044030429524405644060000301c69540d2841011403690070301e4124084110f600465540b90001407449014070454028107103a074a1904c4002e4909119a65400d549850383c0404826a1f201c40481c003505204089003600d598 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 906381214 1250 906379964 906379967
    0x612151f0503040c09050624130e090c0d050d14070204050712050601030905250b07030809010506010c260f280801290f070302031c05070c29090d 64
    0x41303103a8000e841d00d43c41c00080c130180751910069046000b004403481c443c64640340c001c0c0c01c010710641a44040203e012440410344980740e402d402d0143c00354104689040e082c040406c04241846d41d4000e1995000c0307800c0d129814050308641e01d8580034030400b90b042c9043e640110b400e4401c100ca049c000200d02c0d40403100803612511070703940c12101c00e1800b00440031480c3e480a03516441e5500035600c00b800002548000210562103002426100140e070303440311414a0041c2030541d0a80f19800c00c1d50a000004055501c10180325201c0c0c2d400c00801d400000089a9001954a4074810840c841100f0040d004643c3d443c034005040702c0644c0128410044080c009027034403400307041150350400c035014004000b0401742c054a60090a440031a4040102c03c104808085d0306c40c0055001401c040411410181900880505005a0005004172004101508107401ca60301100d42d01c011070602c198410105000410703511004541140750121114001d200450f1040101c8400e01c2e2a4401d402c09081c50307 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 906382464 1250 906381214 906381233
    0x60e030a0f050405060421120c031d0a0302010507030c02120d11030309030a1214041505090a20030109020904120f020106080c012604140106050612151f050304 70
    0x80d070315464500d0825040c000007850602c00c0c0e202d0244080c8107031449004c04002d03000d003001502e50203003403024195154070b4058459000308105a0102d1214282c00b00150400103100022000040c4a200c0190469006640d1908480e01c05e50420416080e0100117840b0411309280b151407245c010110854440001002030b140452404103030340041c030030712501a90000035282002c80c0c600b4407818400302000090010022020040d41c05900e030000c5c807003400030100291a042000c00014402507940322142e039500c00c0c1c5810f0080140d400503034429410000c280c0c1c603850f086001000851941c01030740014404040540b010742c2c41903424000b204589811902c1881006e1480c0001d002051030b140f106a01e4030120380300e80307050190f400b0160071040d940ba1040c1020b00c4483d0a40c4000781800d0401c000c46400751115480e10b5842d190000c10b80313143c80c0c8291090030307526a1800c0115a260164020f03a13420350420107400c000c21021740c1c070300c07a000603803140a902d049540e03030364a0346054106030310030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 906383714 1250 906382464 906382487
    0x6091203092c25110a061d1c080705070209070e0a1d0703180c030b040309030503030901060302030708120f070c081b0a0e16081801061404060b0a120c0c060e030a 71
    0xd1000008451030000e130b0100c0c10070001c54202c200000c005c0b010354950000685413180c9a58640030b00b440e240400400e80c6c41e01000d0a0255403100c10039540e4a03001d441da031141d950080d41c03110b202000209214442c0005152085024000791420356981d01c40320343c0d180890b150840010004010440032550501c10070300a80c41030f01c0d1680e25401e16841e04501da80c80c1e4000685031008481c009800e050042c0003100045622070101e955030700c1d0403d01c0b5802040d19002c124841d005441000400c8140020014680070b400140d2514001740c0c0d140303a108680c000002100c1c10412a07a00080703c0100348400d040540300c0c1d090042da44000d64042007801c001d10b8010118014051041c8650710808440d1102c1900c4a400c1c030100944449003040e1071080142c00c1a01a91700700200030442007040b088000000c1c006403002c0c007909451b51704440700c0d4016203841000042500301140b05030002a042104490711380d0404c08040c0140d6217410094814140000500b80c3c070008096440c2c80d44440305500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 906384964 1250 906383714 906383717
    0x70f0c02330c0304300b0a021b16050603010612020c160e041118070f020c0a1d0c040b090d0f0c030b0126030a030c030e1606091203092c25 61
    0x75040c00076130f81105c0b0030b901d20080c0c4050100000101e91104541c100c90219594095018034000c0d9800815170390143e1415500300150710881c0001c3d2420301745d06403410380304241c0750200b900c81100100c40c025044010748061500c00c000035011403051320041203014040304800318486140c84d060004000d856100580d000b4801c9103e01d0b58100c0083d1100c54000801d450803c07508407441d40200e20380440e44800039880807440c28005040125440b500b1000310070544e400c00342d43e4903030a140d001400756104081a01404004c4500c0d5803600ca0000507a00788603a00b01c5d68a803003e0380300c00481c140b07640c204641d1b41408100611070f40412a1050140302041c2c500750500e005c86c0441c0d25240d0203526507002c20b058481e88540e1f06c0340d0094110b4011a48828101c590003a10703a0f51400340c40415204071000300352101d401164034820141404400d075050740720020714902d021045010a600f5984190104000c404000304840e0051102c1c2d0042c58090880c414054040c01803000714a5840490f80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 906386214 1250 906384964 906385019
    0xb1e03031c02030612030412060c050910021f0204050315040203100c0c062a120b0603090d0305070906051c1d071703070b1b07080a0305070f0c02330c0304 68
    0x101403810303007641103012944500c003c01e0380f0300c0410341580c1334081d406401c2e50002ca10719408450a90004082c10f10003142e0b00200b62500c6c45192086c228881c134001c840d050341003a140c00500002c0d00c40c1e22a080307031001d42166007030301c41601ca4000708e6100307102400010700398003a0102440300f6406800c071451380c403560003040346903110b017080841b1241c2c803000001c0c005100c802c040c1950195002c4601c00303c010f0b10b150340e00c1c940490215114954101c0c154082441d001c00b15103681c3c8640001001c1c2c07001d03a06c4c0c031803511701c41d0f0076140004401c1c415008000b030313202da81c00003410f8408240e4404812711507004120f49420503181880c408100e0034000040d0b40140b02c1d081c0410b509030656034004c40741609183c020580444c03041c8881c42503c0d00a89842d400282c3c134918550302d60710840c8603c02079038844d1240924030108179941203a01e00083d5008040c10980468500d114050307034a454005a00c0e22480454103000300c02d107412603030400e205c1c1d41011504100002c204101007020351010b0286a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 906387464 1250 906386214 906386219
    0xc09061e01080910150e011d131b03050609010608010507020d05300f220605060409021f0210020a09060c03022d010b040b1e03031c020306120304 64
    0xc800350110104114108810940480c030382210070b101340e24002544420034456810290b2000c003980c40d05100d1491001c3d40c0000000b0708010382c10385182503209540c11070121780c45402282250481c00001600c0d06013a150780c00000150720000c0b1001503204ad4040c211030b25100c55a507003116510b61201d41d8607410300c01089282607010810510810b02400c2441e120800e01c03103580743d8070320440440303c0d003103c80100400a03240544030044c0b05402c8000a641b950350740c090711160340105200c4009000306200755603400034546410450744420080c0002a03404407580029003c030380b40701d100c02040313102c0346451445030354140503614007030790311002c15854000070207001402a01c5074030426040003040315498003014401d10104100c1c1e41802c1c0c01c640c90405080030009412814940c1d45000d620707066841c9038908090051030094a070050035402060305a18003115240010f81110394035000400c02e085450706045150350300f0f035065403001a280d1500c08184a403940220700b449401e540184801c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 906388714 1250 906387464 906387499
    0x80d021909080c030f0c01140d0e07032901030201051606050703050907050a031e14030a03021c0519052a0a080c03040503030a1e0207030e040b0109050603042a03050c0906 75
    0x1086d002c2c400c00e203440d0141381d000c144400e00a00500d111161a581440e20600c0195000039441d41941d021707102c08241000b20321412120300351100303161120000300d480100050f41c001c0c80500000c013460170300d903007240c10301c0e82e02c030f00442d00c0443d131a0b004607903284244800e001003000312001500c1e0640e5460f01c02e608545807440020104034469004029501d020010403100342c2c50b00c44d0014618080b0303a2503030031076013001c0d0180d0000901002c4c29251008001d001c43c0345401070a005a2032940c50030000300003400e90402a01000341030301c0e14885210a4601440442c0c109060002c2024940c2500e442e1292001400804003500d9400c10103424000d0101088001c01140e030002d15100380000c446005c41104040c2c01c1c2040c980c0c540051010450b03005040d0809014180008111001c104006100c0010f54001c040e81c0140c640115080c000a000101e605421201c0068855103100c4090040044011007001c241c01c12140358200c200c0725401c90038102d0425070013207012140c1d407203154a10000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 906389964 1250 906388714 906388723
    0x801020f09040b0301060806131a061e03030f0406080417070b0a09030c150e0f010608101a0616031706060a0f0c151a04140103080d021909080c030f 65
    0x4842c0b103a82c1d200400d210603603096204100826140064070030740c0c64101c0305038007d80e415030825941c80c1400305841440c8580104040d200b160001d10581002c80000c07400000481d240c825590548020405480842170348409000203100d190740e200c032140307094546005066150000100c079040d081c00b210300013841c0c0e209096072280704218001010005420304440c4003a1102000d40449511965070700310100c941c005900a030083d808a40d2076101030046982290114401c1142d150008400035460781c4468000f02c1c000300400c014009081004070029040d80d10120514440c8036900c4961070400d5004880c4801d14601d615800c0c0c031a03e09100414900d105950840040080c503da2031255240280c10180200ea0007000548040c100d11510000400c10800101c0080300b04101070801803400340921114000000d4080341ca591031030345c034240c55030000000310001580a21480700b0400c010021421100030780d40c2d91405203803909400030b04145c4034916003402a084814101c03100c0c2000207 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 906391214 1250 906389964 906389977
    0x3090901210f06141003030207180b031e0d080f0c03180a082a15060d210801050f22090c081b0d0b06010c0f020303030f0f010801020f 59
    0x812108000c0e8114040002000481d0002070844003007036401c805005060f40500e10700e045028441c10300340c45108903905445000d11004005030300c06102409080340728a1800340300134040c1804680e51010000003418071303d0714086040146110790f140c550320042044807950f0140c450510740071a0074540355401c44190000d04030315481c074000001c1020b4405a540f034091701a1910141d03201341d401403038401700c6944117501600b82040b9007120f501045020200c901d10000c802001440d90034401d02c203114640381c0007452690b00040184c098404602a50800c41c10f2400c000091001c03080004006403e611043e0003090260350507404000098642a940f1105c59401103203090051440c40c0524018007506c1c480100082c0c084c94001174502000504c10700d00c000d807682c40d0001d01142034244040414400c9014004890b070310003107100307540180703030340d80415001e20701d080100642d98011038a503500955412004455140821810305088107919024159040080d8508070078168003400e0b0707000c0c08 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 906392464 1250 906391214 906391229
    0x1050c0a0503220b0a1406063907171506010c0201030e010f0e030306030c0423040c030804240f0e091305120c01050f0417160c0b070c0803090901 64
    0x140034102d00d00c140e6440d4a40300d568080c54880c141c2c03603c0000c1c00094030100c03035000498200100850311520b821000d03075020340c00003401c2702035881e01c0030781c0382141514840041171443d007041000c2101c4c40040c00b001700a048a6001280b40a54121001c0c0c42c0150800c0c490140103002d0b4107001c6646c0c1d1105e42021401c0d02481c012038a20b040000543c0184400d44000410a01d4861302d54240c3c036000c0003551107800214281c8180d01100820301c41903d0707400c0d040d0010742c81107107140f200001140e400190854001d022004a041c0c40e9a00c4801c0c560190300404100d411035a52014044c0e5440e40c0c0492034406490700c1500c0c541c500101619880000b040b4903c101c4401000500d0039a002c0e20f120030a44c6c0140890b140080741304c01e03d02c500d03809822808100d509100004590030b843c031400700d0280b40d120803e0303c0316078504070b03410042d41c0141c2170080070040c00c80190800b00300c00410b290044c0000c05411075960001c0c1c9004031480e603550b0f020145a420a101c145a1f030741d140141d01d41150344c1c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 906393714 1250 906392464 906392491
    0xa1509141b042c0f0303091f06060503130f08070b01030605070929070c0e010612050c07060f0b130b0a060908030901081906060e09060f030a0809060c150901050c0a0503 74
    0xf00b1450328242003c1c08014031040c4030110400102460000c0c0404d00c1403101c201c01e2440d60150310142003621014012103002c1001080800c5030b40111032808101103000b070000060f607400a60303811005600c0b285003035400820000040c41401440c1c4240760300b0400500f40307100d003189000010400703105000c680d42d040d0070251080d0300911b0802e00440d80119440501c3c0340000d80c540b9001c40c003244080c02200002080080c0740e400d4000c40707114442c010446040708034108111580e88038090400d03031100c0ca440c2500d40d0584900c6444440180e04411005000803400800d04c3c414004050480c0c0c0c0105d04101c0c2d200c004104c041800b104407600c5403020718001070540e6a80c0094500005e0043c0340700340d141e2030004000b42c036a6001010342110001180da05001e91141001c10000c1103402c0300c1079606412001000c0000307403203000180511480545090300302580804102c4c1405c015190f50403e0a445a0802034480028131500781d001c40741c0c1a8a600b0690107500c010700b00d000c01020400d0034400b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 906394964 1250 906393714 906393791
    0x3020607050c0c060d06150c0c050f151b06150105090d05150f011a1c05040c0f031505130b011205101b0e01030204080a1509141b04 58
    0x100b0320103c4000e000180040e41d882c1131640d403110081a00f4455642e16003010303086174804e0780c82070000500a58100c080d01d00290b00305410000200e0145a4065003d80ba1001c080140400003014045c255108004c0d02184c4c0018030a20f800c120004168190181c511800140b03280c3e0001c0c00d0705c50011080c1d8040343c00c0e03540c80c50401c0c6440002040d040c81e8002e40c204100844e00b05224a03816a0081032a9030442c0000c0c803203244642c0140c81481d619850202051586500558802c90f030090080008504c00c55803016102d41181154106840c1084a0b0304c0400360351100340203042d0070501c00011214241c1d006c1d11610703841c11041c0603030360b450a03411030042c0600608200111111424410411840c0300d0100d40d0704400f2125420100403c40307034440681c5075030003442940c0c00ca450314000303811001080d81c0d40b03410b42c08844580090440c0d4070705400021414103000030000c0c0c60960014185250041980925124028031040c8a075090009130411044940110001b81d07107041c038a401d901e032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 906396214 1250 906394964 906394987
    0x100b16020604080303160e091006030b030c040f0f151a0a02160608060f0d170702030f120a11061006120e1c17010e04120215040b011d040302060705 65
    0x450b551040d0f5061101009004100a420300300e052004c21580303611030f60245400500c042000c0884070210200451042003000d82d000350407108801000500345c030040b441060000302142c2c084c00d5072000059440c0032402144507144501108201014042142c9a00d400c85014805a083e109281360200c0441c2d481c450500803c00c50205405010b800b00c0120345170b0380e00502404003210030398400c07004031131800300d06d040c5008801209500404003500c1c80b8061400500c4690202c1001c0342c040c8610554031000a00601078840c01d00183c1d03101541c1d500003024000c1601c1c1d40b031850010982c00c21000e01c03002005116044080380c40a0400c00c1103d00e50b41c0c1460b0003060306048440e482e00032000c2e10403001451500da651824800d07140c400700d40c4100149001824000d003c1d0700301e03816280e00800e000c0358120070000c4944400b4030440e48001070010b503400c8005000e07241102c01d03c2240005108286602e04800a0403106403000b044510b480e4030002d64072400035101e10107200c1d00095071807151 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 906397464 1250 906396214 906396217
    0x3051513142532120c1305120705010f0e03030c031207170f07030b0613061e0e06090a080d0201051b0a0c06050a060909050604110a0e0415061715100b160206 69
    0x804c41c070f41c1d1004451422000c082400e61000aa0b071555041e117070f90115152401c1d1514902c942121002041240e0800c00103480c211036030100042842440c0e00f414020765000c200409050b01110017454540101c0078440d0904071002c0d00c0e400038004603182041c08844600740d2994090401001070384241c440e500d090300103108100340150400000105803c03843d012103188030403181142e8400340003504d00790508440d08040c442200c0081c0d042520720203580742c400c004c2c1212003c001c1106060650b00d4412500e011040350041e40541d4441c0204070144000d20f90207038600c081e0704003c07850300020810080400081c40c1009248a03550404911030201a500071005800300050410071288d61707040155540c00e04460440300c0035400e203e00301890030a564180200c0700d181480c03d00d50348440d40c03404000c804045905001c59500d41d00000c07080a030200031500381c12a4009841301d84114081d000d03407194000c1c0b03035820f5082d403450100003141c1228101c1da20a44201c0820700c030703c00c0510009409 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 906398714 1250 906397464 906397477
    0x30b040e0a0807030f1206030b04350334020f030a0818070e07030209090a1b0c030c02030114040524060d1103060106180603051513142532 61
    0xc9510301003008c020400c0c254044d5008500178941d01c0d6000d800d40300c207802c028402c028881031100c103000d01c0302c1d08180c04030051a001040111691b00e03104030514120300c0844507411114140d910002280c50860701400b800101045010103940f130164242000303401c00b81e003c0c0c0b1601c940701c044006500e4010301442600e028107000071219030313942015440200a5041483c007544101c40c00c030b001c2450103d1034411340d003030701c0c10b2210009010300c038080d802e0b680e0020385041942480924819640142d4081c840d041792115201012050342c2000d0401724540314010210504a01001c9000601e84200380e20740c0d50310550440e11112200d0f81803034445100400d1075070a80d0540321300b40000c034003e50084407a0b0041044a102044800c0d138070780701101920015035030803a030714440403020205400c04800104404501c03020110310110000d0818000000c102c4000420b140d100c000c1d46010850070411040070845e502d081090003040500b20454a0160b00308a4656460001c605400c81d480c5000d5818 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 906399964 1250 906398714 906398747
    0x20d02031507050d0c0924052b110903070e06030709020d050601020d05041d0c0c15040201020118050709051509040f020a090603110f01120903030b040e0a0807030f 72
    0xc01d07090002010740190042d03150f01c0107a5041c0082d21040c0352080c0c07001c800310b0b003103403003070004c0d610000340b041d400c184510b50880e0800c5020040a075020004001242c09101082a5044840aa50190021609440301c22002c03401c041002859956000170b041050f21540040d910350354550800182c500030311584848001030010139403a1910501e43e100501c261000e07000d03210f14030703a0440b045030070f44240d0181b034640c41074040d0b842041e5000c0c12050b6510503840180949054040040c8500d00207910303500c03000482180c0c04000031941c2c213008004035030181c418110f0f11402640c0d030311070315001d0600504203070070b66031000240000300b521490100414042d00e02c080d5030070a0301b0542a030b0a01c445050b03000d01c11414002804041e24030a010403260002400306a48500e030080100c00708100b030300d0340e042096445003500d030f084c41441070b064124881d4800041084030301052000751800f520031080c0c0c58000c402020042a540c10803182029031502c0e0161403d14000020750716044090414034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 906401214 1250 906399964 906400003
    0x6090f0102010e01141e0c0315010e12030706060503010e030f0706020d092604050d02010e03070302091014040c080408130e01060c1e0521090904050102190503060a03020d0203 77
    0xb42d099540c0f042c000d0040305c0802c2140015415031b8181c4002c0842038810070912202000040d094688507800d03103a240005140c505000700c5e605001070490007088040300c481e500300107070560403c070891060b5001032105400034058080c040150340e85a00400400103882100007e00e034042040d1a41183c2d100f03110013400700010407040c2006500c1c0c5035a80101001c00703407503d07841e0a80b03004132000d0354111340c2d00034503000f0510b0383c5900441c0c0d00c540c1c0110064252003940720110051352021047d912a070070510110540c00c0c0791041e4220404110000345001d140b8101b030f00a000c03580020340139805600110402d03500d6031040300c10b1451940c40e0388031007400c200203000482c501d940000481c01e09170144052650517145407078070036020403080c0c1d0300405c2a400120030707480e0040881d07100034910001c0303a502da042109410102e41190011502241e0b542d42c0002c40040c820842104e40300c80c2d05080c07520302d00390715003100030034808480c2d40000391180283c91440c4003117680820401421403c0b403401d88 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 906402464 1250 906401214 906401231
    0x424081f210b07110712150501150219200a09020c0307031d03061f08030f0903070f03030503011413021201150e010c080d0b031501080d08040206090f0102010e01 71
    0x40301d61241c40104982c446040c80c045040d1034031850050701c4032008400501401450113007010080c80c003040045610f05201e4141105211003481818000c103500a111001007611361002400d05000800f00a01120807c1c04100840d00305001303004101032400c410180b503c518000100c411030a80c0c450140c0e82d00005402c0b64140010010f440818400e40b6480b2a540c103654101051900306210701c0d40542c84000065030412103c13946405020b940011291481c0e2254016400c6601080c0c0c8080894400208900310b4181001000e0040c0040000e0210a0b41566002480381c803041c802c402c501c0a800c403200d0440e80e5a0302d0214081d41c10340c902103550708401c0321000c850306024420303143c0c1c076401141184003050007060018080d1205a503424405c80140c0c0e00c0c11400d4000c0e640c03610083e42e0301da0095030300c1d40b010005211110800087d60b0615803408201c6464210700d81507807001c100610702030000586400302a54045601120a600038100b4440100d00600c19440e0301540c43d130034802203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 906403714 1250 906402464 906402509
    0x30a090306050a0605030c0d140706090806010623070303061d041208061003090c03050312040b010b0702060403151e020d1103060307032010050424081f 67
    0x810046a00c118018841507450000d030034110b402c603100c0e041c0c268104060340b003098a44014002d029602c903849014120b184010880d01c0c2c086650040d4000c164504030610407084200b106030f00601c1c0600e49148040e51020400940e18002410803204c040086152410036020380c00c40c5014203401a0840c0c10b0342206400c071074030740500359000d4801d010380301c0c1d40345030841c40b078801140300711009004140b0303583c45603070124020300400a094030000360f2020302000151051008100003041c88001d142306080c02d0400e8008003406034408042c1e05801c02819005888010a17a42203070f400c070503415001130b90545120007901320816041d0020001584910003d40e00381e0181114505540f8104045405007244e00c03460300c000c1d500c0550551203000200b0001c1d9402e81d482c603100c501d41280700e02d080d0800002ca41c6940002da10703100030420101e401d00c5000364400c2c000c85510980c4900c1e14020300e0b0b926020f400f00201610700030502542c41c0007031201c1c45c0d03c032228030020b106038075070705102c640f8079002c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 906404964 1250 906403714 906403727
    0x32a1b051f1b020114070509030c040501060e091003030e061c06171b0f04020c150408040e0702030715050a0603050a050105010501090611030a030b040902060307031a3001020c030a 79
    0x1001c0390750044490b21800c00f40705110740c250319500e1804084198803445801d440a821040586600d0700c0f071121071001d19112070040ca8000c0c0360f41c0d15049442c80c03e041c00c0204a01004088803006410a41c040011a90040030f1440001064811a13178900c038141280c01c1d68050700c00f14402c401d0401e000000c41d84071010041c3c11a010311000d4520039103240703020f11008018103850950049007042011580c2c5002d600030706803480e000c0c04a5514a00c21040c8000c4114126006c3c0c0780c0d042e01103410460245040640d0790302c841c091001d585048516500e03820b03503109a00c400a0155950f0340011030b0440554000000355801c4011180801d1075454920b01800303090180d035000a05030100040c030341c1d010380b030550083c101c10406141044642c207021001013009a481d65405a107c20020001da00c1c0d11300194000c000030703a008901d12441c060f0004c08580c144034450300602c01100340c0c0710020005204000d1035110340d6048500e21003542119400780c040d003800190f8a010004403815650740092 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 906406214 1250 906404964 906404981
    0xe0d020f010f1a15090d0b0907060804050d1d0a091a01050301030206120a09060f0f06080c2b05060108151003080a050d090b07032a1b051f 61
    0x800070712040070b030905450181c880044100020400b00d903100c0c1242d10341081c40da03803021030188040f824400080001a5500e000b003006403907640505060011000c014401200504614100b100450904d540e60303d0341e51180084d000c3c10045100d0b01020000013209030400d020b07000405110905032207402d0034004000100014042c080344d106820400d500420581c5c0c100c0b0380080045c0d0130840075034071200c00702000800c0e0505140c0e64050290024040e4461156564112000019441140700c11002100c0c420303004540c50741d0001c0700382070055580d2003c002c0684c1c0c40140d010f03c205c22110ba103100010007070303130020b0460080200104103104000360801000e2547c1c040b00002d03454940444078811564000a41b0380101005640342c2e10b4011402080d0860801c000006c03900780f03d4442c8441d68800b80c80380c00000ba01c0d151140c0c0303400c402014a02c02c00d080c01460040003507000c80b0241c601c20300c07000c0f60512070841d15009810f100060010001c11a0000d40f28101e40211311302c2c0e40001d08006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 906407464 1250 906406214 906406243
    0x10b1f0206090f0607110709020a03060302131517030706050c0909010e010803030c22080708010c03050610030908130617070302130605030a0204090905010515060a020d0c03030e0d02 80
    0x45001074000a000a20303c0103528840c00602025214100c08607214204000038010780e01c10107000044400080c0b000f0195201169000900e2a04610401208001b1501c0b1032000034101040d042d01c01020380c02001c21920501141004401c190054a0550003000e0018180c28034082c1000046071501c00148540b08048400c110107a89030200300c0c0d1241001e01403072072142d0080c00081d401c00c4031030008220103070580e05906d00c03240000008060024081e0001005500012010450f80d03509020391410485581001e00003440c180340810010350303201034400c040548540d01c0c01d06100c180c0d03089414421503103211608942d1104809800d050900c0c038003030036a018220004000901c240b00380c0700114107007a60b98503039515100c0100ca580e00094016482e03658200000110a482c520440350881e00c12000440c032440e000c0a07028024260000b00c5016080401507035015560100d0111489003041c180390007000302a0804070003c4c240b58041030028070448041a030601d0300090401070a0058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 906408714 1250 906407464 906407473
    0x103060605011110020904060302100207090c0905010203160204180b040507050f06030a0b0a0b0c010518010c12021e03181209011d06070515070e040203070e04020705010b1f02 77
    0x710801124000b81c0390034a440990048420f0001442c2e00d07030000d264928000703102285154581d000038035104074500c5031402503800038404201d807141c24040e10b0403080307903410082c00842c6403c002035206d128098043e02034843c0c10359120304640d1185c2c4000b40c280188203980c10303102000e161400001c281980c0540389407041450003d028034242c819180320b548050b00217070840c0c4903c1c4007400a04580400c0e82da0000d0718582c08035400f9440c0c0090300d200400c80001091600b03288514605003d90707010a40c041c2d034101051242d480d07422030303883c1e480051100c60040e03440c00c4020207114421604020304c10880b5000090002140011880740c208a0202c4c09845400046080040051066120890118680c1945079100c041400f11034201d061010f4200f41c500b581a540303941c02c00c060300d03040481c820441d109100000354000350340f03603d024064804601e14108841d02601140440418610035900026400c003046000c0d0865183e40c41c0140903000f408600442c40d649003030042c0300020042c8507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 906409964 1250 906408714 906408719
    0x5040e1005010c0605060409060c0c020f030c011707030e010c031406011e0302073206072303090a0b090303061306030f0303050618040302032131081201030606 70
    0x4031261024201c48050b180c02c242c202103541c81ca0050600100b1542c1c2c040c3d2340f5560b0b640442d100703010b9561946441e6440c0341c03541100348100031055400b00c60b194000c1e80301c1c54200c2001d98000c05000c0d004c44815440c20300b2030303075213041c00c502812840000390810b50809400c0c0103140e4254020702ca40d1040362202c0f0141c2e941e120011580d107014030502218004040c804114406d00036402031074218080d00e1801c096800304070540d14001c140f403914540a51900f8002c48941806010080d080603040c0340000348400590282070410302481c03448594500000046407041600304100481c83c0d61012000c00140390580c0c24035220380007251140d000d00d20804200340740d02c1041c40b851050742d500c020340d00d45004250b20b046009010040100360030408411180e0300341c8500c144070510403807190380110b54030103101040c02048621000301710700c1d002440052041d038104011103058900440304030501420b207082690980c0b00780348100944003000000700c2100342441d00d0b4950303068034000d00c020701015a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 906411214 1250 906409964 906409981
    0xf0e030702030d050a12050907060e030303130201030c050c10150603090b011806030c080d021c0c1101020106180605151c0209040906061e0f050f0411130605040e 71
    0x403806500951580104003d50002c50240000d4055030344036140401c5200180c80259089541c01e42d103c103800d0340000002c201a6900807220030709000305402550550510000c4144000d01c0c5401c0203050548410f20545203500c140f00f0b61345003c4090086454015808030780c400100900021003800205400011a0490281c01031101042d03000004500070307032910300006803e50803405c100d181c2d1919044c000000c61000940760b400b40c4a9840a0a03070710380480c8000c0e00e492144400c0f494400c403400000c01d20180c000e0080341115410012054186440d000101e0040245404c007035184440060341c03001c0080c0d030350302031000d559080d035400540c43d259900100c101c0c001c0c4100318a41c2c0c2e46080c1920a070555940140244c080040d0002c211a50156901c1d410303030f401500181880c0d118681d020250b2060441910010245030340c52003030300741c00c007c085500000c0f01c5030b00a02071a1220341c2c40c043e1001e003504903903014038001210201c2c40c1c1c80d6003006041c2e40c490710801001c007901502092900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 906412464 1250 906411214 906411217
    0x1406060906030a08030912040602070f0609030c0611010905010507020c21060613060b07030c02040f060b04050f2106040210020f06011a0c12030603010c05070b0c0c0703150f0e03 78
    0xc941c0240104040000b42d615450f0503031000f00054514001c52a4894440b403035034000d03001508582d0040d0a055060041c0b003c000c0120b03074844000c000c40100f0410110f641e404c4084d06036100703490701843e031100800450b8054281d4102c000e00307641c40d103400c000700240c1c0801c890300c4001e070480308800340403120350300410960b01c507403160452900300c80081000e600d0a540c40640750502140040348480e5142d8084040c1c0d00070b442e0070b0b1301040307800300003000710301d030512a080401490f0001004258100745040455015a01070715008184c405c40d103085941d515549000c031450950781021850300242d8186455440076142240201000c60110200e140003040104901d40d41000800c1d80d40e181c03000c0540048001401e0240304102001045103030132003071046140145410281c00c1d0703242000c40a040c211031701c064041c4100b020a00c50360700003c1034210007030f400c044001482600c0e880f240009a080803c00c0d07100134481d2103040943c110300c0c056604a401c0d01c440c000350412002e0001440300b03071203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 906413714 1250 906412464 906412471
    0xe04050c12071407060f0617070b0a0c0807060e12072001140c0d02160305190218091f05090a0b0c040f030f11011419050d050414060609 60
    0x50101407040d49000040c07503201a03480006450400e07080c0f01c2014401c41250f00290301a0351460300c0382a101c5203004107000f44401440313011140a8988514081d0710f8036054140141039840d003000611103d03544c8128440340445810001d95039a0b207406190500091460f00d130650014041c040b00c42d031101c2440d0069810b0980c00900000380b407450051a48003055207030980c241402800203541102c00c0d1080082d00c2202d901e08002c1c44182c81da45406803030030040040300d000c0c6000c115005d10020380301240806030005040b0740300c00e4284203440044d203141c000140201a9a02c000c003000740e45400050204c014210b40059480300100c408000c0050703520456962010307038010b40c02400082c00c0c0310b076096400701507040c1f0342c1d00b025100e0304800e049005940c01a01c80030f620400b42c6080c0031080203039100004007428070141c4111507400c0050f030303030040c6550706c054444c0503910040460b002c0c008848078802c0c601002c1005d0328051611444032000e540756000240705100016400c1e00301001b03102e01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 906414964 1250 906413714 906413731
    0x1020a0513090b1012021209060f0109050702120d060902031303080903070c05010e0d0b180f011a060a0e031002071203052202031606091a072003012a0e0405 69
    0x41c0100d01c40001d8908850070181500d00303a1b820402da0724107409642180d40104402c20292141c0c1c1003c1c070200010b1101a002510300313911344030134410680d40000740c00da0001802d25010b51035044000b244001002c1d96841340c4212800001003201c0e0071000c0b00e10615041c03281d11742c1281c545078482035980d28000d842e40105500418101446658010881c045110500030800036000440350380340e4100001c243c078141c20603205004a075074810001d000740050750340b00364001c10514414000d58542d60689040382802103000107607641041c0c0c070401c0124254400542110100500d5040c0300000790320080081d030b100c00c440d8a1032403100e07200b40180c5000d008141c400c0c900c805000c0c03203403480000c082441264548156003203199081000320410006115940b254040c40d4585888950303000d910684403055403030104205c00000b100310285031144da07001d070031208401140b1004a4010300e510740f1284501082d880070558550011120718103052142c0d174400852082c60710600003a110207945040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 906416214 1250 906414964 906414979
    0x90501210818121005160e030a0b1003060203070c11090702060a0513061e140f01231e0a091802060a05041208070501060608010305250801020a0513090b 67
    0x1002d1140c40e000d2000710311030041c008a40284185201403800c1250045054507940f60010040c00c0b08407082400010306007800d18401c885000c800080c0ca601c2c050070003d211880e09400f283c803c8172054051405142d00800031503503400d25210140c1203000a660480c1c003810980d0b410203160034220705090141d441a0000c22142d21101520000303032030001c014409545070752020750040b640ca03004000e4115070340600e841e01d040080c14117000f911600d410071101120418184040e82c0c011804a034111605c49082a14050041a07110712802d02c00c2507281e0300001c40c41c00b42d40e030007041c8074804102450849004108030781e00c070b49100c16a0f102a120b5400301440d94000710241c205000105610300f040e02d0420714154445010007034618802106a0780c60501240400401c80c0c02d1040ca406044503050207045585581e4609941d4000784801c0c1011500082c043c2e0740d01d020000085010f06440700c0299154200c40c0703401043c17600103080341703102400380755000030340140c072031103500d010b00c00292014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 906417464 1250 906416214 906416227
    0x20c040504051606030212061207090203040303140906090105010f08191106270411091c080a180b2a15010f05100e03030405040e070f0905012108 64
    0x402444010425500c2e409911080102124410f91481c06002582c500684416100000d01300d10400100414020003810100c5a0b21b00300020380c1c071084408890001d60340366218542100500124109a5007a905d048284100003001046592062a10074000c00103a0390b04c0713007803058184d00d611940340300340c20003c0315118404c0703240307041c10360075015000d81e40c003021622020800c6175005c40c0414070040840a08a401860007000e40138500c101190244104a428005118140b0611080324440c030700200505552a103d41140303901d8540061a094a8220948025058a0f1144452100b030140b0074008240f81641c2e50550701c0203400300003503800550710210142d00c103606d0b0550030103051166880c032101104815041c14060400490a62100380c500002e100c12201245180810300811194445164400105690454504880200b00724480c00c2005007404036a8126940072a503090380070600c000b0303603048141250208449141501c408002801001a036400b0027000300d682003121 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 906418714 1250 906417464 906417469
    0x2010807120207080301081e03250501090c03150605011106011e180c09050f1e0a0519050306090303010b0406050310050409050f1e10090501150e060901090903020c 72
    0xc071001820305010041c81c0542c151500350007900260b21200181c1c0c0151b048000c60100310b2032580c65141044025810300800a01c54400c0b0003032050b020f100c000321513140350123104094010600c801d40140d44060042d032a41000d401802c0c10f01052801c01c2c0c2000000101548a210040a103d1004015181c00d03403d10800000c8a028005e500c0c9110f425050042880200c0303105100581007031400000c1c0d10400040040c4c0018019030149100300d44c0d85001c0300964881004e40f00c1504a1486200e160448942c0083c01124454101c203810104442d428010a0745403990002903590031421a2490780d1240421940c81c80240165002010144810030103140100085c680200e40d880301c071540310751610080b40031a81005403e071411b0f0301001d0300340030980060006210b03519000300d43e0024011004c0b80d00b580c40021900c40d18160340c0d80d01c640c50a03c0402c0d80304410300800c1050000d03d02e0761b289071800c0b8030320b8240c0f0726512a140c402c0c000524100f685c0f14000307100d507164002d0714400061104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 906419964 1250 906418714 906418727
    0x121091214040b0708030402031e0c1f02030901030e1c1106100b180a1502010510230105130e10060f020114040f03020f030307030e0601080c010207030f061806020304030f0201050402010807 83
    0x100e070036100c0c00e12b80c03901080c0000324402481900e00000c02441942c081088481071440c016029076281072141c0d02816640801200e92100c000e0902103050100c4c082c186207054400c0301040e44041303000001a0031507a00909109128104800321007107a1100450300f240062244615402c99000b080081c403d028072520391a80160010190380c0c0e1a070b5504841c041100c41501403000603507480080000080140c039100000c1c000c40f140400d11120f81c0100d155100004641160601c0008248450344240c28400b00b000340c1402c560190203828103002454100d00e540c0100d00200c2e90304030b003007118030f031051050405802c20a50103501c5501c44d51901c0041214001054085006460030314910076001c000550040e003407650000f03000f81c1d000401a00744072040c1c210f84181e41010003680001da034002503a60903260050742c52444401d4030310301000100803050003041620541e8403064140702070b69002d144194001c1d15600c2500c00b481604070b007281c004540090100f045a0301007000c80d44600d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 906421214 1250 906419964 906419971
    0xf01060c0c1d040b0708070e2419020609010908091020031801050702030a0b1807062616030e0313080105010f0b12060121091214040b070803 62
    0x4000040035465800700311440c0319804905034081482d000303100800803105a0305038040b0341403518a4460030b140a00074514501a0041403044003141c00545075074440c0000c000c4915651301c045c07a66402ea11110b000c801d440954060003501801b000a0807042c0180200d42c4603c0d40501c0c25031610003150100540b45c040b407007400041245c10325001001c812548292018188288011900d80011005814990301d82c01c6a4038101b00c1d05101d9203005032000540140c1540d0311082400150b80c1d00318408407003034100c0c0f40c03074100c07403040000c005200e40d0086c1e60038001d85c0d8500c00540c02ca922140400d8500b40081c1d0750403100301c4051443c54407061096008082c6804244141c80c40e0408105044038804031039086607034183d5650b0b00400049541007103810040c1034030410942068068003150300c0040000b031425043c000e0035a40c07080f45428900c0c0e508004030317400f8002c000d44446800c007180e00c51060b02910010a03da050140d5801c4a0001500c088842c80d500443c6416691b81e00c0f103801e5007015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 906422464 1250 906421214 906421223
    0x11803111f0f09052b02070b0d02070303091e151b0311040b040f051008070909090c0b0a050a0908010b030a030c0f020d051b0405060901050118031b05040b06030f01060c 74
    0x3d00b20b04000400601610000d200000005d084580c420717a210310408000301c80b00400d561080008000c0c0d8444c10301500c2a040c0d4880c0e0050b201ca01e1810190080d00c031410004090190794154406c19405696040c00c0c0705000d0b40c003411102074800b0b02d820890711002401ca441884901c14000e10600c2034100c400140d901292036810b181e82c40c1d592903001d8206400c07028185400c5002070007281041022800c1d10000b070301c1d00300c0ba90701784014068191301d81401580c4c0d00c2900d43c2c10340000c0c40900346c80c02004003c28000e081d62000f003280c1c01000360f01300f54420400180c620300c000821050500030100c1012005016018a10040e41c054070242d12021048a410801480000243c1e4559000d041054001c4001d001c260302a10b10754941a0700c281038440c4600e18100503c012034460300a00e41c1034401c2070034070b00c0c4203075640610507c104966600052001190320745800540d000098000d04a0344107036014003440000a0800c440c9010448040c075034030905400400816200d026244040c070700070f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 906423714 1250 906422464 906422471
    0x60a031a1e070207090b06090604030b0405030f0a05180d0b190f090b04030206010f0b0d020703020f0a03030b0f12060a0c050d0c050417010203071d0f03011803111f0f 73
    0x5030076026075032400315603070000360704054401c01041445014080702004101c038850710b0601484c0000300203019501003d0102d8905d18006001c11008004a800210184150036120804440020510760104800b44445807105808a40c0c50030b2818502e81c040d60700003000c81d15580c0300900c900d203020760b2303500d0782103913a4940c24500c4415002d485072000d030074000c500c4000b6600e014100030303103052010782c00811044101d0604200000f06001918111700e000840581e507002c0604080340f4281e0300107043d0642d401410070120070150168400010b400040d40e00c016000d0b4000c0800c1000b1201c0005541c1c5600804002041c211107944048400d401f58100f0238201003001310f800b0100d4038078024220201da0005002e00507aa0010840e0a01d204210f00943c078501cec1ca0840249070742640c1442001034803012484080956511707110360801c0348003070020400150313114580000000b0a90b01500030592060301003540c92404101c94040e00e001c3c4007402050380380b20054038001d010118024620300e56 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 906424964 1250 906423714 906423751
    0x1506010c0b0103060603121812030e060c06150d0305040312050c03040303030c08160203070f020a080a0501020315060705070b0a03020d0609050a06080325110d0812060a031a 76
    0x8141d2031507000c2e6004110000303041c0d05600c1d118900308881070300036051080d405c2e26245e280100c0c54109007501c40000c03601c031074420245020b6500007400481d00341d11120200300c40c07000d01c40c00039109100700d00040310000d000c200d02e0b0505c40003184040d801f9000900400c01800404c0011160441d9141245072451400700e00300001400c5030050f8204400098403520420f400b964810410f60304581c140101c40200a00e2a402039524803401c04000c0030040e034800002d0a55607200402e9004008940c1a60780320402072a0141c000d6104a481d410f5224208904080701e09204c1c09444800d40c0c414010030049040a100c01d00980100ea08001016000c115000710580e0b58041d10300180303055400442c50f800c00100203c26940d02c0c2d00720f406141d109104d81038102483e003840610340010b0300115615606181819030b0945808001c403900100c100d88000c2c100080700c1d00600344101203102c403800c503031998000c00888402620004e007403038003000440c13891300c82c036900090380000346040400c04440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 906426214 1250 906424964 906424973
    0x206010603020f09090910090f030906080c030412030f021b15061c1419030e03060408030a2c210c030901141e1b070510030e0a1b03021c02031506010c 66
    0x951004080f1200e40074010003004168014be0b8600103800b080c1003500c000d14103065280c1140c0801440940503040030a2030115a80c081d83c040202141c070b8900c20355840081d440d140d00c00e40b40b206000c51a9102e00c0c03a40c0d600c1c0d00d900c0c13480c050044000600340da0000c094401c0e0f88080e8015240c1c141d4014800050300d5a03200340c1004070803a8201116104d014408a074200a420f200b01698002c2c003a0301309004000000d510101246da1003528420002204d4007410308542a052880000400017071032000340030442c0c0000240300d0b001c2c6070321428841101540112100b1075010f01c11a0542990041c040803419602403550754418001500d03050782041c185003d4420041002c007042e403001c07040018060480d41c41010800c000410240003170a00a1421700030400c1810414070940406039182000043c1d0700090115000710745d045a440074101400070303944280d400c09407008070700c540e04003d10701c3c000e81d8500354509000c07600100034100c03a00b0049062412004020402410081400b19000004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 906427464 1250 906426214 906426221
    0xf0311210706030606080403120c050705010f020d11040326120403080901230c090411040b1309050c0307181809050601060c0807031409060304120206010603020f09090910 75
    0xc03000504100745081030150844200750401400c0180800410010030b81044420194007910b0f40c001803200301d2140c080f1140c1c00f400c00000d00a50074202046c1b80c020b010740103480092403448040040704003001180744280f00c1c03444014401c1c6048201e0342d1200184010b02e500d008011035805107401a101b40b80002010102c4080b1b0100b0440e03401d00040c00000d00c00c5501610700e00b01002c810041540c0c0c4104940700041071010080c2c2c002a030102581c50300c5d0400200000c04c10040d6440c0ea032a4007501c00c45400040d0252000034000f01d0000380c40d90742c0d004a50281e90300c18001482c5032160a000c8900f540500b50115502c0ba0014002461801d9045400704504a0b800001450460b3380b816500302441030780301e00108440c00d03c0c1040804d817900121a05540e0508007003020400205420b501401900001607100d4008010801445202e444440e02e40300c19600355019682c0700d1307105808900920420790940d01c2c09114940642c141701000a8008000104848001070081945400e9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 906428714 1250 906427464 906427519
    0x71211280f1410110711060702091006020c01140412030e10030903170408031920040810060b0906090a09050a022104170901170906010f0803040f0311 66
    0xe0a091548540c0342c418188040014100f00500500a8264481d250816801001000b400740d0082c2d4000301221360715a02148c00565014210020307900c3e00d0021a5800e130058031951003d80960700025405601c2803000300565645d10706094145804d00910f41e4103000c0c0d89000b00c0c18003100c6002080180c0d9110303c003115200190b500401c810f206850002c01414140104d84d41d90020001840002240c0d2030517a0307072094082c4e41c4c0c11800e0440c512034502400708035000e54840391074090420340b541c03004030090040d03400c804115403110140801c0c4804840151082c00d4107001c0901401c0c4652400c08005d0228107001061000c00a0f1203020480c101c800a6816000c503d07400244a46050f0310b84070314228035007451189074600c0c42c0075202e00000e0110303402c0c1c008448000084104550380980d9481c00c41c10a0800411040e24000644581d6040d003800b80f4104004030440000b1003900020480e81681c126610003003a4500e0365946c100341d050b500f286c8607805103181c0c24a00e00c494a180c6078544 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 906429964 1250 906428714 906428723
    0xe121501060c330f020a020f0f030405060717070f060b01050c0703020f1302040b0315060a050f07080415020c0307080705030c040e03040b031e0105090708040212120a0302071211280f 80
    0x2920480680041d01c0c10188c02c0c40e49036140c0046405c5030b0517820220998088520581d0100c2d0354042500d480c8005881d4103100c100f003484086800c40501c00c400306507401c43c504c41c0008100407040b140c01910300d03000300302e04038400e5481454203000505010031110005800a81449204c4001110700020390308a0340040c0304680002c403c00458140a841e03190101c00306076842442e211307a5600091951190740e004c41e0160400148100070840784608a40007001903880314030f50300e10b440c5002911504000d0010f48a0b128026000c102c5e101c0129092088550040041021294900520024007110071031074071503000a010000300c80e030040c0300a6110700d00300100d20300190740c1c2d001e22107400c680603084140900780c8041001039540d0006005038000d0340403596003005104e0b02000502d410740d0441c40c1c2203803100220710100c05c640c00d5005407030f03070174407688418800010046d400ca8048000a54041c0658030450b90f440200281440480b115180c07808800c0c0e4a1405442c1c2c4a1559a001c00854 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 906431214 1250 906429964 906429967
    0xc01140c03041d10030c0b090d021003050a050a050919020f090403050a021b010c061e0f06090e0f0a120201061a07050f0c01021b010e121501060c330f02 67
    0x50501c5481c0f403e0b84991914031540c03401e41941c41d0b05030b8409160185541c0072a001650b04800d598250504440960061980701551a10320b8010040c1006803019441079080602003031921416005051190401c070000b07140d0090082d2020440200015040c3c1e00820043d41410b89600d40e01403035407049000e602d03002c0d510f02100e4002481c00e44900e10002c03888211060300d10043e80d0200100c0b8a01d0b401040104500204200c4000c507041d400c1c406600c03030b03850114503440760b41e4984c00c00f60031126030070400c01c141c0c400340d00d515850f07070740802040304160040700903200011003620b1031074240c003524400029004e0b11401d800b152028000501951104045180e00c10050b04100b000d412041546c044c1c82c8444601c0e001030744d0340e03100b452210300001c584d00b40300905920510980c800054010200c040c0c0031a80301029440340026603010141d111000700105070180510082d65100d41d121040d200320b0055104208403101141e80c90840c42c039190810420003030054040c04009624000005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 906432464 1250 906431214 906431249
    0x1030b060403061815050603063402100c0e0609301e0d02070306050a11030a09061b0806040b010909330803040b030702010608100501060801050607050c01140c0304 72
    0x1000d4000300100041c5d034035800d10302045141e89001c01c40907003111500f00076606d0940c0d048211400a0406810305488001d59915154a0f5900041d00300e1681c01c604010002006145802c1318050384035014141c020a04204025540c00e29038000103074004404681440006405c2115a5803000c40b000302d00711385d01550b40058800e9060407440036000e00035004001400107504080e4564000c0c0c800941030700d81d00c400244c403030091904000c1500300c4034003d0b81d5603450120f10385001440d00c103d00703071041ca107002910f406032640d442302d4651541264840f80d020380e40308400c110150050350740f9a41004088200000e80840f1406102075a880744240c240d000f40d089111403402c090f405203078190340d1090640c108107045021044409a400d01c07500c199507035a619109034050038403a4444400e501c80c849158a0904082e40310310f0503241241c2d52040c080c0d0384d403010030081b8011820081c14a4110096100e82903010707410503003840500881407410304402c1c403c00c605540041e4002420b00480003010b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 906433714 1250 906432464 906432473
    0x7060609051602060403031d070b03011a040e04150b090703050405010506091e0a06051009060e2b0f02060f04050114030403021c020309060409290f01030b0604030618 73
    0x14654407001d030b1200300718120b01600e002907407100b0242c406020b0580e03d00d034096242e0180300000c00280c0307407101211480d55407121030b144107a10074803540d40e03041c8000c40542a090500c1d01100e040b00c03071a07030f001901504c40703881c0c0075000800180000d84003655000c230308442d500c0c4c8032103891041015440005d00344c5814140740d425120000d042a00c00c0c541a000c1000320302d83c00120a2130620a45000c2549a0366070207442c2c0144900d80210f035201c010b1900b0078003116404045807068031440da50b034081802c104800d20001601d812100042c2840c4e00c4d2401140c05400703400d60000c180569214401c0d140c0d19000300d0080da0100e002c66100e460005428001941c111500c40c5404040c0f224240c03552500b40c40c029202d0003105080d0040c10050000c0742e02d20382c4204251070442c03000070002039071540d07a6000600140743d0007000704103014a24003082c0014034503854800a01001030500e588024411004600802a281e6410b41c406424840400801c015100c1d4220200e0740c0e014424402030725060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 906434964 1250 906433714 906433721
    0x90d2723030c100909110f070506090f06040f0f0819030209101803080901020f0f03030411030a05071806090603050102090108100b2a010f050411030d08010b09030a0807060609 77
    0xd4140508943d040c020b83d45a404800e2400712000410005078000140301500c050388101e4425030107140307012440c1814440d0105109025580d4201183d40b4001d0700780100e07032100c1c002c841c090134007840c001040c8042224250007031001c80c400c041203841c0440742d540d80c5208240c04208080086e90214501d0302c113080081c150941c54a0343e0502417881c0c42d142c041651040d450340001010120046001442c0764000c00c1495924001041569502c440035505142d40b42c104440944604c1c60a0322115042d040200c0c2d1802800e030890081c2c00064105185c0a421209042090700c9040d6540c80018009210340702d1240a5481140090fa5441c2050001054050040d00038801e105903d5810800104660101c80c1852a08109007540c41c0101d03004035642243e40c014541503500780040d0000c0b48005034402845107100300b01544004010300d0500d50380f8a00019104e0100355450010300104c2045005845480350017012641c0c01c907410b60790760550760090300040f5040d07900c403501445404400e00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 906436214 1250 906434964 906434983
    0x40923010609050904080708070b1f0501090503060609101a1206040228231207050a021b0a0b0a0f030c03090b0406090c050402041805090d272303 64
    0x2070140c40b22410b02c0002900558085c00041449000143d850104001c16064501e0300f6004082c1501c80e10300004101c1001240030f000b4810020490000302d52503009988510507210050014411a92040c0500c01c0443d03000d044c520003d441c0e040c00141140e01c2c51008215500861955521000e06448000314600041c00b1030f0303c40c500500a0000500d01180e10041140d6007151466010440748015240c07903003a829a459124031071321140040040c031030b0080c00703102464035100d82c42c3d5503101c0c8115918010400042d005801241d031380400d922500014600d114401081c0c00c0710350341c0e078401d03018955102c400c80034080345003c02c0070600d02c0c0e00351117802c03500e080e9400e081c80300000c9540c50341b02042e00140700074240c903907500c06031081c414121120b002409018104650725030301c5a4074401c03148050b080c00300c1034500b4600011104130000c0341c1c60b100c0d140e1644514051400040013200311070f081e00c3c000c0c0b8032010000e000180380c10420705140c81840c0c24074401c080c00710a00051600303040542 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 906437464 1250 906436214 906436217
    0xe0613020a0507021806030c06031e100503060a051b0a022d070e010803030c030a1e05060a0b07171e030a05060a0801020a140309030f070c050f0312030a09080409230106 74
    0x917004c000d580d441c0070603008000030007202d002d941d9503100298549042e40c24410700d46400802c030204001042c88140c0d000a9481c101c5c22100c1540d905014181079640c103c0b9035499030030a44010f01071503901300d8083e0288035941e00513591240d1150203041e51510035941d50301101c04a1418a00c8103020038007505029104a00c0303004059810400699034038440600580c5c0d051000000042e0002c000f0381c004c120600500c10312060b0450302c1c0082801078071090700d6551003840c0381c07900000c00e852100100c840507540072101c45064070000030024001c0c1c12844401803841000c0c0701e003141039080c0310015485841c0388940019203003000c1c014085401141c1c0c01140e802d03803042080340d0130306800180c02d81c1186004a1145e5036a075400c6a41343c00c1d030080c3c0403181d14131500440c0c0d180c20421134a8048040c0c0700c080d034420101ca403804080590328040c03000225103815041004c1034503a8401d0300404a218000d100e46031500d030b61480e500301180c00c2226241f4201c054800c14180c05100c0000180c01041d09 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 906438714 1250 906437464 906437509
    0x1210050306070e010f03060b071208101d0604110f0a02010605040207150507121a090705070b220c080d0e0a05010f0c0230011803090e0613020a050702 66
    0x180b440500008106030701035051000406140d01603500c20342050f030141c01c0003001540c40720003628180412030300001200c0042043c4400181d0b0280510300000100d4000380b100e84011a00406095031420300076116a8100d9141c0342c50300303100c0003c40c0080040400e1082d5055a48070302c90002803c43c0c1c12908001e204500420003200401c80d10300c03044d001c050034800005143c2d100c15206841c41480454030710102c504201214604500108810401c481e0683d680300d0b00c0c2e6500c4a04031110310030703c0e60090040e103003940402d55100000414020040300701d20490030070390064607030382d000f8a40c0798020451a40042d0000100e60740c070250001c2400303015290400340c0c0b401c000000e003600003400403010400175422682e000751b503541c04940c02030b010b8015509400c2c420341541c085003620280b40ca00c07003039802c0621002c0c5010601d602041300729010759694a609040420084944801030480c1d9031000a0301440d90080c00d030b0380300030000b1520b1612200e41e150818070500242c42800000300804040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 906439964 1250 906438714 906438721
    0x605041811094f0204061d041b08151f0305031e0d0f060e0106020609100c02011b05090f03011e020c03042d090203060a0306110f1210050306 62
    0x904500c224042181103840e19200384a0000722080362101041c00019003e407859030080980075910940b1020f4029a01440900e896840509005d4035011400e109000103c0c00503000c100243d1b00e000105c03107640324004600381e55901543c505907070880054042030038841805422541f10000300300c40f040703032043c1e10b090f180345403207040e02c0b400b4600b40040b81d10280747d81395000b402c00804031410701c00781c05010040b030540e120400000307050740d00401c0404490301001242c1389000140307540c4614002d2005041e01ca00c9003030781d00e02a005403400784042d903403901c1d07001010403002c000d074441c0c44040c0c1c0e03507142d214200a420440c029084003007140c0680d151a0700000c8005140c2400300c202c2d40030100c0569100d0724003c40368518443d603849070700905c680390704045c200e000c0f9042400e508403140d040707020302035250001d0408922080c0c038002e41c040039865041001a1058002800030340c0c0c844141428402e803c2c44134a4668070000c1d032011405036120420443c281000c04580203482c09030028012842d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 906441214 1250 906439964 906439981
    0x303050a0e120a1403040b0c0a03080708160e01120c02250605090d0c03020901030503191b0b06220f0c090806011a07081909081b0103020706060504181109 68
    0x70030704040d20380304080c9881a1340f5a810401c40b00103000014420b0b1340c50b8040d190311034440c0080c04080700011a4100454041031040c01054003074030072104c0ca0400900036810035202141caa088441c140f00030030780ca07841d41042034803c088083d8819006882c901c8000d1174900440079400341d0000384e64004e12014031030141d014040c4c985003041542c50301d03140c040b50300340291400610b510096008440c80000301c00c112011002d02444d50441c1c071b0780d40100c41031131400e03501070490f4203941c1320080c0300054150106081d447c80d15046240540118903a400c00308048801c5440441c1e05024107858622011050b10b03e441000d00e10f20715443e107218a18144440240c6407403040c461450401c240249001c0e0304621402190300031a030080d10f6a944044201801202401e06401c03603011543c2d9440004000c8070200d12070300355144035805065200c4c0741034010740094000f42c0080e5450750f9100d01c00320340781d181c42c03007080780b070300e80d82154107100041a19281003050f0320074052a001b68088001c1c040e004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 906442464 1250 906441214 906441223
    0xb061c20040e0a15120314073305182a0d030201150e060117010e190204030c03050c0a080304260f0d1d0301060503060606070f0b010303050a0e12 64
    0x4036a480c0000b142a210792607030b03401800045002002c0900c10610009aa03001c02d40001503071880707516030040d00c0e40c0c0c1001900313071030003001c04c003800c4910842c00f929400c00201003810305040318003240e0341120102d0722480c41201c00885209100342020100300c0c62200d000c1110032041c420200b2101d1140440c014241c001d40801450f150054a0070390200080600039008070014001c481d003c560300690742d54004e26802000d5179502e000ca801d0590b881e01c000842c0107003505941e140c0034542c07410b448001c08100e035140780403550751003954280000b100085804803c000110301030802040446c100f08204425020b1a070300c00129a4402c010800c04441c4808001071007101051181e000211040241c6081144c0303a2503002c01800365000031200c0d81d4101951102d40210b8178102c0f000407003018145800c840440c024170b903042e402400001d40310700e020802800001d11409041c1008400359403445c002c1c3c00c003030304102c0c0416008142140c1507984226411084901119a006060b0a03906020b495 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 906443714 1250 906442464 906442469
    0x31005041101030c0c0503030f0613020c0a081602130b0922080a031b090303030605040b06040e130b07030b03010b2e020705060721020c09190b061c2004 67
    0x603d5120072a40c0d200b24000e008907001d264210065940d245000c03400744001c0d0004440c2da622031441a44110b2080d1464426107401000b550014001600c0685503100c0301c2d003000d02d00780c5c10400f8444400700103881c0c080c600546810303021008140061450200880b000c00140380048882c40c03100c203205100030f8031003180202c9411244c201e03500c080c2580101c0c040c0051240c0030620744110481050140e41c000122400c8038001e0307408005558441b002c000a075400400950340c0308001780702c1400801202c1c0340550700910001c803040880d00e41d50f91541c49440045034030782c020907a07500110300070341000e0040c1c03008140c04039503040d6030202d000120300d41d4040100103034550310088009a01064000c00036903001c0c0c8401800161602c0755454604241d411000b03030103800784d540c4600d81c0c41840c000106800414801000c4003203c2d590001a00c0707405516545c0b10f801c46489046681c06034940310010075944409042e100c40704003402e44d0100546401ca020103d0400500a10b40840d40c3c8190a0307809 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 906444964 1250 906443714 906443717
    0x6010c020d060f0b0a06020d0206010618061107090509031b0c0d080a09211a07020606060c010207150f05090601080d2f010219020c0303040e04031b0b0105031005041101 74
    0x120100b00201c0e6074024080940344c25001a50080045800c50300080d0503044550540d00f2520541e0700d0b403104480303031601880c002d01c03e8444020b0610485000e0708202e0b40d00044501140e038465515181c3c2c9040d14030a852040d9190130010f040464040c01050354003000b10151b0050180401d10030104001800a030b4001c0c018800c08124840e02502c1440c110000384900e518904441100e41802086001003200444407010441620413941d207158109034170510481e0090282d5607260303010301100b588492000301c8a9542080003a0004070210803080b208200050001401c00c9088100021110007805041ca668004401000808000961960511401c0c83c00800c0c043d490390b00d40c2e042c1c02040e540540070f0605103410b8105050158050140c0d110100c0e01e620350440c0310017060b40c03101e00c041600c5800d600100020722507000b05078000740e00b00384245800c0302e509500781c801d54555000c0c0e00045030064441001081385180030040c0f420540003c00041095040c40e0ba20344003010b55041d17200c0d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 906446214 1250 906444964 906444971
    0x203190302091305240f0d03020a06050a020403120503060307050f0402090405190b0d030807260a15140a0e150d0b0402100504030510050613060b0702030606010c020d06 74
    0x240522a40544025103805000321001e0380784080390401815003240c601501e22514039800707022044100075000300c62005402e90705480340c0c10080c05418020f501e416803d5101d02642c1c00c0c000f403128856a44600005c410068445080d4a4040c12040019503454100076007401402025907010481c45d04991088031542c02c061190b201180180c0129904140c1c00380c601010000c02006080320f07000c1a248441040122400a204000341c03254000c1000d40020300311000120181d0141c1541012800300c1e074500c1ca5440606403524041150440b81d01c90a140c86100c050361800e840c901c41c0010340840420443c60450700030100302c00210501c20380490940c10008540200005401004004000b5044060640c103d0501c180d0340350782940c4c124006c1801100030320071a4802c03029207040ea40d000b40a4152001c0015110010340005080e84d944481380300d4800343e2030805031007400010003c400d03c0030b4484605004240c1822030040c0382c01d061012111500e001070340c45280d502d00b01070784420000b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 906447464 1250 906446214 906446257
    0x6090c090108060a0b0a090606121103040b01090c090f0308070209100602030a0e1306031a0a05070c030c02030f030a091d06011e14030a0207022409121204090615030209010203 77
    0x1200d500859101c100700f185459404030340c142e8031240d0072b00661100d49003403010041c194410907140c8400c44e005070125044000600c042c03a0030360003030500000a4034021001c00c2d2502c0c0b014611160550080702c0755040000c5039021800c0c514a5580d0005001c041441c480385012000394507485410750003020020002c815071a0b45e51030566201c042c1c2849202004807039100e24050f1350b009011301c2c40c2041c011001000a1417021a070280c1d40c402c07082c0782d0f200c00c000d1b606aa02500c800000031400c0768540075210186540c404104054045086e0344c0c0d6680d5116841c0412020068180610080160420008100c840c0c0d0b00440b00c0328020360144800215000807400c00c5403102c102c4040009000d1001083c400d18282d1074000d0300302e450088030555041081070314401511520801103000c4c50f070080c040c04c030852501016501c07400d1841425914140180c4801e600e5a501c1500083d043e990b8403001400300c0150045204d0b1442e045040441c6441600c10000c0e5981c010075040000c1c008600d500c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 906448714 1250 906447464 906447469
    0x90f05010c051c021e060702030a080a0b13050a0b042f0d051e09060f0105150409020f03010305150c04090c03090602180112180b060103091406090c090108060a0b 71
    0x7070521800f0501080c40090404003c000e4440c491401035001810004414290360100443e1071806000503800442c60f10b40700841c00e03981c011006160580d0300d03a0340c1d90a136015441e44e40ca01691080103c1e00000c15203480c03001e0900f124001e40030107002e6850440300c80707280c203020950710003c01c0d0661040d17000040d22021200982c0b1411031942900350034541400990394400b01461303061010301da441d5105503951313544035030b85007411aa42d200301c8941c1001000241807400c408c401680d0520012441d050712260300c5810307a40104800741d03c00d40008010003c0c41700500c681d180c24030409c08883c034681000c0e905800b4034000c0b03025041d03165981d00d982c66040da02a600517058294440c41c10340d221201e0040c40c10000c0d8407504100e010600c40042404c1a1246101d180c101c0f000c400804d50201d80e05465804180c0d6009002605050380d48002001044514000c10b040c42c0c1740d00300500d000e01e0005a10303030422140f5045680100c60341c50041c81022804100c0940c800002e10000902d005007500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 906449964 1250 906448714 906448723
    0x3060303040317090a09141f0f0f0306050109020c06241005071704080717011508061b070f030305060112021b060618040f030527030c01090f05010c05 66
    0x1d04008400300d403400c00f504208003138044610203c604107641607448401c07509685221140d01c50203034141001500700d81800646444448418401c8580e0a07151001031840b00c41c41c0d00881c2d207121614000704104490346c01480e001d4005808151308010a0f41c0380a80d4402c00075041d2565840d090740c0c203a5088103560a1101403c80051000349120300042d000781c1594840001074515008a24050304500320540494003169041002004010316005522a511040c100c903c030055480c0c500700d4005c82c2c0c4400a01e0081e1070424043c01d06400c040d408510344845048020701291070070700c00c480c0803031000054404c01503010704001c522541c030348004072824507036004181c0a591010541041031803030040c20f80e04406030f0740304480d150740380d040401c030401060214107595000704400180008040b040754000c000e2103410514200841c0350101602c21441040e485880c100000c40e180b042d1404010b00f4079080d8087c00c0540721582804400300a245040c0180c3d410700c1042c0c0072113000c0000c20071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 906451214 1250 906449964 906449969
    0x3040810270b0912030a02030601170903031f05030642061c0e0d2a060209190e040204050a02070f110f0a0e070f0f05040608070c0b040506061905090406020306030304 73
    0x113034140d5403485c054161400941040c0c03101c5002900e0b6954600f80580d1041d03070039001c2c0c00444025801c55446a00112202014000f0095624084a40000c1070344080004038029910420107400f141d4040c0c5c1d400800c0c080181c180e06813000480c1c00c6200748104038043c00304004040d03550f02d070749400010b46c420304c0042840303250b0b0284d07117480311748200f1400210382c849031140340b80c0da114010002100b0382a152101015144e40b02c09440b04007400042c5150b000300030540c0098004404a802d01c0a9520066401d5003c194041400d004000442c54580329003503001850b00811410903203a521012030010300a0002441082c1982500d0b0541da10b01440d48c07210b40700240043e00ca0354071031800c010045000c3c1ca43d0408103031100305201025000f1140c10880915076902d450400749086021240c1c000302030310aa062100310400000403920480300d091185026400401d010300703160040c40b81026180003000010310010300140142ea4602d51000d801903088040561a900c031640003d0031441203a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 906452464 1250 906451214 906451243
    0x90302010e0409051609050612100209011106070f0f050a0c03030b060d0603060209030705011707030b13020c30090103051b03040308041a040c0b160503040810270b09 73
    0x107007940f40305c01040d000c8020358600c40014410781d190401807012003060007803c140c490f044240c266404401c035a000e00000801403520780400c800f01031055003080802e8480c07100013081c104082c052113400c00da00720950501d0f490201e240082c9c512004004000c0600000d0405449510720340e03c66848405403900340d55400000c00c20a5600d213051802980b04255080c040d00610300005070560144080e8011170231f0340a050400f41e03440b48000c800804c2e42050a5034458582d6107015803101483c8054640580c803c8010200c2072441802d40030900604022101c0b5000c8841410045034407800a40d84030300b2003030030042110f440d40400c1001e500411200d19680600101c104030030715901442084c011405520303644140300031407015080c070020850b005003480d4461a0100800f2a41728005c2c1000740b9440d00341442c048165031400d00f55805984082e590380c3c071403804040100c0c0d0300c0c070030751004a82241890482d4459009000f01c001e802540c058040701040300007a8025100340044034290080e03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 906453714 1250 906452464 906452473
    0x504090c05062209090803180a120905091513200711180c070f14070e15010206011406090621070305060904050c0f01020f0a0c24090302010e040905 65
    0x5043c19a100c1e04101035a60303203001880d40d000141d0050500c115407509801c290040e19687e02c044602c00b6044020240ba00184101032194010400f0076520460700c8440d039940c0002c29140008200071200b000d4000c2030818021024074585980b80d000301c041a0410140c0414031070040041051405100e1a00d91500040026003504000f9800c110302c0300000b08179001c8846620a1400d410189011a44001440401c2000702c001c2259000c03840c0e445032140340b9420384c01603203800e06404c011080d4080c40c0210300746814014108201001018100300a10082980c1d6241c159407804081c030a20313101d80100380c00698160a0b03101e820423224900742003203041101c00d01e80c05c2c010305421350454030440064549004941a0f203803100055008907004401040d80c8040c05040040c1c01c002c0044c0b80d41544a1401602072925051005010045c051904c408071503141c12561031004461880c0019001e2020b001503003100d40003400c24040d240c081c03811000341181c0c0004078005204c84c58000d40039125 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 906454964 1250 906453714 906453727
    0x60d02132406022a060712390c150809010f060e06152502040e0703050d0c0510050115030b091b07080906030106080403020f0c0a0504090c0506 63
    0x6400418000344525055446001ca80041c0181960a8001c020068204507414106001d81c0034a11924004440c011003444500c1e400084055104001c01c50b640c4c22211400700c081c2c0d400c840c24120902d1003eaa90385004400500c0402c80704109161294580c7c044031400300340b10003150b00402520065194110b14614a80b0113000c00404a03000712240d800d002c4c44411a990724000d075812615069610300e00d6840300300030043c0c0c16891180300349150800b44a94115072503503440075500c1d401000664280c4445600502c070aa4030300001041f60740c4e110070342c100001000015000c4c103210300740c43d001d136461516107006030918501000e411a000e041c20000700700d00301d65901080040100343c80800800000205000c090030003204c400030004c010300510728104085c100100390031489006072510f080716007000511150030a13000480091004002c100c10546c0412145280501c0800184811103603034000424420880c05558010349d1502081401c1120900d8030030060040202502d45605 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 906456214 1250 906454964 906454999
    0xe0a0609171e070e060a0302010807050d0f1a150408030405011b061d0610081b030a08030c04051903080702120109050703050f07091404110a0f0603020304060f180308060d02 76
    0x2113020780008a03940d2000709202d4a4084040c008403039042c5c40c2c03641c0d40e0340c412030240c1b056080700c4002030450391260100382001040c1d100e21068a00e00c200762000c5a1310303200c1400652000c600800e003c07030b80100414002010b00205580c1118400d28240100d05200f120411100c840c2040061a45042c021a40c040c3d49010710141220780f410313000c492641e502c0304004a25171103203100c2c40d11160400407181e11038014280040c0d29a12002d400c4500d010260f503901c0c001640b00f290252500e80e0080303014005403030a800e500a050325440e244001150550b1503103005480b441c44024810621610360822810080d080710b241d558002c026150956640d0a00c2501c0305400c030243c10345c6000740307140421758100511400d4020074080031360368195615540e4421107012440c1901d6030140d4440b80005000200003030b1b80014244a54000d6240d04280c0350000948680c0503c0382c110a042c81e1660029803c118045034070706401d40f40545c407940310707840482c15503000720354042d402440e08000c0f43c0c01c80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 906457464 1250 906456214 906456223
    0x110d1a071101090b1b09090907050a0611070e070306090e0d122a02030f0c0106050a061b0f06020f28020606010c0605090102040b0d0c0e0a0609171e 65
    0x903a11511000180100380c8105401c03250000740041120f413100740895072080d8000c242003403402ca03980c0864644a006000501e0300340086070340b8038156000301000d000505206c10110020000d600301105019808844662030740220701510030700700c14000020744500d129030841c100600c0005000c00070242100c0040d600c4007051081e90340407588035010100308119074445c59440c0c0c08060300550480780359001c00d68020748522070640031444140018000e000301e4200a00c41d01845900000720107203440c0620145e07070415031020007400103010201d55100440400000e505601c100c06c00650070440c40d2401c000d000b03440d03208003101c0c1c01080d600086240c11124450402103080c520081c00c0e0088000c907521034045030401e0005100070046000607000340c00c829080340f5510b0000d418a81c9a034200500754201d0f1100041c401e489440c00250140c0013800e040910106445003c3c40ca405c018000c1c0c0891218465621500034440a0390441c002c10b000100404466042200d910101e080030f0b02c3c1e65 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 906458714 1250 906457464 906457471
    0x180602070c05060933031f0b070b01050d0312051e0603010c022d121908160f020309091e010b030103232104061101020405030307110d1a 60
    0x1040d56455000c2683d290050030703a002d8401c000c1000309008108001026041d00c4010130318002101101c04540c01d45221019500c500700a08111050746c04030302840c0100513241d44003840c174001c02c000180204410298150555806490058050b501c80c41d00301c92440765541c4181e04246842c080c00b0348040400078130a210301030f000c804070751501c0b4001014200e4a0001e03207800503a108060312a01c200007a980000c40c045a8a140020582038031103082c2016580600e248000704000f03082c00d407103c1d180d002400d4812003803400c40410f107404090707807404d49070100c1040c4c180021303007038034441842c420400c1301d0030f0300001b030031288130340c14048502c0e134442d9142c40c402140042c42074000b140f40c44944040e0303412a60080411a440c043d0603030703402d01c00384141203010a140036076400414168800b002d800c450201140120b42c1e61807900d50000c042000c01e00780000c0c2e503401040b003003207103035800030a44d105181c100222240b00740b200000039100441c00340d0001c0c0100c0301e101c0c58003103048051804034813 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 906459964 1250 906458714 906458723
    0xa14010b0303090a050d1e050a031704020f01181e0602010e06070503040602070c15020606091501080105060f091504050f0109051f1215080705150406050901020118060207 75
    0x20240100c410035489000340404280c102c40d03030701d0b403c0025190512240c1c44003800740c0c55210780c05031f4039101980f040754080015901c0c0d0380444509410503902000d8100d0401200040c0205420643c6c00142d02c4200707071503e14104004100c0d581c0c0c061171030700360050040429035414042000c00080511529505104d000050751805000c80e0003507030086074031071180c2020382e219803441c0e64a40d503000c020f400015050f2f4440382080004905070300c1010480d1824005500282003a161140402121040c02800907440c8915200c12031056604500300741d040da14120f0b00710b5101e13018000035506501803140c040da4002c00520f0340403010700c1440010015a07800b51000c040301c44580005644140a038030403d604120b02d400d81804103c49002d001c40100402d10b01000d2000c665510381042c1c400c40402402141c00b826000c0102c40e0080084400401c004d13181c00c1c0024251000000c840e000c5c40c0329003014404c001170311070700581c403e50040025a04804c00c01d041000c260808000035008403e0482c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 906461214 1250 906459964 906459971
    0x403081215030f0c12013309060e0a1b0507020d020303070b1306140c030402010c020103091b0f0f1512090f0b01060e040504050c01031a0901030b07090b13090911030a1401 75
    0x46a096040c000c922087c14000b014a0b03041d40e4040e842d68064107171058902c2c00b43c1c18401c0105443c01203000d120010060b800d900e2a050401c00400b4040369200001c140102e0042105440b011303810200ba15601070301103030078002000c040d001003801c40c49031107001001301c4540e1041180b400d410451220805004510411103d040110740b2030b0b100c40180c0d58903a0303400051001400543c400d41c080505148180740c0800c0210710340d5100e01d881628440c00100a41c00d00348140105c0c401a00b02070700401480c4855100c403441c044e034904074074104d1010401041010941c40e600d414207500400340341c5170b01400c005e0b1411110b0400c0c40307412500380150710000701041c2c181c4103e0f00d003a0003418001c58200f00a04440c8501c0700040d00207162205800598081040c00d42c03403180d5600e038002e0f000f5402040b115a6520b0b0200c0f0050100b41103400c8071003055001e11601300c041d04682d8404007a14140100040c41f80745c203040142404044034622940341c400c20f0710403800c126802c90003c550940c2c031402071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 906462464 1250 906461214 906461239
    0x302030c100903020c21071712180418120e09132307080f0c091b250203010e0d09080708150c0c070b03040b07050403081215030f0c 58
    0x80d02c0b069140900140e1100d010f0f051285803000401245103002040d10a482500c4c1403500c0c1081242d0740694141d0740b820104900314081480807071a4000610245440c6c0707281c1161300f4401081000000e80a190f41d1807523072150584558100001a0308003900050710b0600c00001480c861070101c0fa5806220f4481c04141d0801040303501c981c140740d11003005142c00440d0b29032411100b440985400d0b19101342040015030380700034402c04081c40111005040010701600030702107010405040003410b20540340c1ca041c4060a02c4040d03c00011000c00141c80c000a5000040114000100069411f52034208040a0f0043c0000c000e05030b0b400c41c0c2c4890044aa8070006207840e41d400303102d030f45003581014019015400030511001e901c0b80228908505215a11001034a000b070a41c00c140500d502c00802d00c01444680c0d16490b90040d000c1c94800e11701401c40da2030341c055000e8990100711041510001c01c403400301051034400803200c050112188484860b81c05951000304074845030150700540c500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 906463714 1250 906462464 906462493
    0x503100f200711060d11030402040c2124090f1104050f010309050a21110a151a12100e03070209130512040e07020c01020c0f0112180302030c 62
    0x3900c40318407100c00c5803410110342d5101c9404071070300c125015511440030807240754074240d284034202010b410508216180d182510502c8205c96984250b4006d1116a13030b12150450803140101d003402c1c11040c000300c0c0d600800600e400348100001d9903040100b43c86080400c45804940c07001c68401100b00c0d00703015542c1c8241c100000d61180c0e0203640e80101c0c200020720150350003a0082e048051003a4211021280152154160180150f0302a288030241400e19480da0b0b9000341c80160201118001c1d10004017a40c0d1022a00c0d00400000d5140540b502d0728107400450b007040308804510007500502d000c5c40b421071203076100c40da80e006184050345411000019004000103581d880303940603161940ac0c0c1c40d080c001d00c00d140e00c10380d002ca50b148180401030410007080c101a000a1906190341003150a1018000e4105a03000d6007190440d4031141a090465440c07581e019491a421b0070b00e01c41a040484071400541031441c165105110540804810558000f00600100200b001624800c205100c403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 906464964 1250 906463714 906463751
    0x2913090c0e1920090d080f130812041820041a0310052202070b0103170c060a0b010c1704030c0f081209061209060106120c0207120303060503100f 64
    0xa0f02d0b24500d110800c05003110900001800804401041030040c40891740c0c4040250380712200b0b110303002601160314803040c402c028400c006000c016014280846000d240a005401030b840742e4011104500c114030414055a0b0042c85509001c044144003980300e1f100e0342036558814414082c2901e10441c000c192044a0000d8030f00a1076910040e41c1814540f80c10000200d03a1081c1055421000510140610710944020300c80c10b4801c813400011989142014248443d8050551128401c00c00c1202c0080c500410800d5000c600000700090120300d40c401250344e504115001040c1440c40e07000f0314110034440c7d0150ac00c0f24403400003181c071582c448409201c1006a88901c0c01075501403404640c0060782d4001074181d0410180005040441c481c0c45100040d60a40d000c980f550081801801040d83c4900c2101c4425100c9005005142801a000350b4a1149201c1ca42d4410f0700d510000041500c40c0e00100000d0a000381250444152030b502d007001040d01c810090252894543c907151003030210300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 906466214 1250 906464964 906464981
    0xe100501110d120213080706030915060312080a0e0304060305091902010906080619150906261e0718050f010507020607030c080d0b01032913090c0e19 66
    0x36a034103c0d4410002e01d40d006900a004d03001600a901c800114420500f00602c00090059903400300d440700304c508241d1a41740c62103031240303020b0741417540c188007241e0765081512040900303141c46441d681e541c40c480c400408031522000c009000000300001c0e0b10303506d600054040c900306021740d920f41c00603001000700b020801c08000e010602031082044814004e0800c5540060040c0050081c240c80d03900c42c1c46d41d502c0c3c0750482501c0c8c2c52007482c0311800781e5101e103011016146c24104240c070103038500110035480e0b4680b5032006070440f0b4200001d95809a0716510841d9580010401d04c26041501d006000d81c2441c0003202a80011814002190301d0214074103036074000180c44031403030120039070240640769200780710560501044104000012f040710b0002e00071141321401c0040e404461000040aa4140c4070440c1705060140000640c0d0001c5440841064642280c0c40403900b550801c0b160050182e00f0009040b40da18804001980650340140134454001c1c00451130a900e040b507000000c981011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 906467464 1250 906466214 906466217
    0x9090b0a050d140307030302041d0103031413090f0e060c03100b0a11100c03150302100f140403210f020c0108130c1d0c190c0c0e100501110d 62
    0x34203080169041c100401c4034420300902e000c100c24100c0156503461030b8040c000850001c2d83c0050f040100088441d0000e0201c00000c6420b00340b5451500c3c008d0040703980307040c80c80000384005200d1800f0b034013200000c401030908100900414100c4608180104011070191480c0d001d041c00207141d002644048070307c500f60b00c10400443c40e08007000d10205030444048902031041041100300e905208020100d044d0049400200d0000c3d4802c070020140c89038680b40b100c00c441d07074102c20320060341d4915a82166400910b80ba045114451400300c0711101100041480100c3c0010048144848803180c8074100c0c03628001ea100d8012100b1040310103243d078040e400d0040e0061900d0780e485e0340c418276070300d50080751007000007500940700c0c0c855060313050450740a000d44814201028000b10b40c61030700c165000190081403401c0489422100a840268403402010841100400d1040144845003000500104001100e031413a000b281c900e48a0700030302541d030201e0f140e4011060b455100013030040030b2810a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 906468714 1250 906467464 906467479
    0x408030405120c0d0f030603051f0614030a06180c030b041a070807030e03130e090f0d02030d05040201090905070c02030115050a060e131e0c0e011b0507081c09090b 72
    0x11820300b00e0f072551211701c80e1000c160b1201c0380003000c40c4040040348803000b252000d00d490300e5035490541049443c503a103d400e100c0c070b49460030b000655011942500c20b5402074008250790300c00050044001760340c000700500040b43d2140100511240c0205240702d18468803205010f550303003000d9051905c1c0200c64078400178550b2000588200c0c4aa04280002418881124140341e0442201c1035030108540101103104580c400b045403400003006510114041c0d8005403d03a482200402901c82c401c402103011169204d030086011a4401d4405900030f20380312310100f000c1d00302194014150342540c44241c0c0f04c0d6082c03c5407508080c2c132450401c0100d60005001145440c50b01c2411f540c3c00450b1510a1760203220210114804101c500455011701407030780e80809060b0004292100302c0781045211010070192a0300022140d8000c843c1030410404032501c0400011907180c6240f81c45442d4001c0680d42c0203c1e0bc00c07004d212602c100a06410a143d2a480c05054985945108441c1d40300c0025500442 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 906469964 1250 906468714 906468733
    0xc01030209061b0109080307020d0905061303080322200111061501022a090a020301030c0e040602090a0b091e0a12020d0605010b030708090d021c030609050408030405120c 75
    0x8846210031400001c602c00421700031040d072155030b42908201c2d001e50141e0460712501c035101e6401040c031005040b0441d0403908040e002d240c1542c0e4900107010003084098000081045500c81c3c5d01c1c050302c0070007150080c0d0041c400618190b10140464800d400c0b0080503070841e01800e6000301c6181301d240103020003c01556540d280000e81c400c0c2c8032422641035010f1501c1d1070030409401d074400c900c54043d640203109410340c0401403020128000b0140030806105100500000701c491205500b21031600580598945071424100003c0c81503203402e9501c40103810000847c4061000540907442c2c0888800700c0b2000c05048842c041c40703c05e000203902c210402400e01c0090052110494601d001804204040001c2e0f0764540803a28203800660340c0550110070002019805940a0f9000e0782c140003605080c0110140030790303104201008005030052030300e404503210b441b81e4404001049002000d1107141080d0521b1801a441580c081ea03060191194218030060000101e5161140e0003009100414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 906471214 1250 906469964 906469987
    0xf050715050a0c201804022e0e0f0d1101030b0409080715060b1b1207021f050c01140414011803050f0d02070b16030606020c0108100503010603050f0c0103020906 71
    0x500d003820011200300d54a00310301142d185c0f1996107105058680d05c280c01420f040c010040d0b0a40c6c3d01840303252360448440204095601e600d59a040b520050605201100c84400055210340c0d41c0102d864100784503082c4201400780b00340c10490054001e807400c00c0707071816003428003068a443c41c0024060781d8040049000066809940d8012200b850500091083c2c4811010541e07a108144c502d0404a508903a0f002d03c0a040c0b00e502c00700942c000c0318a10f4113480c1c5c0d011546801c500080e1694811446401d88140c601a804542001b4840c1d0004c1000060140010440500540302550500c41c1c1e0b080000444005204640b440045554050020001c540d0102d8041d4800c00040d2482c0e0014030400104040e507001911000c2d220740038011080ca8500866445c0030803c1c04d01030201802d098081141d41c3e00455046c00c100c42c02e01c0c00ca081075840100e0064100d4040d8455a015843c000000041c420701160700d801030368510040c2c40041c80203200450580c044c844105030b00000422010f00c410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 906472464 1250 906471214 906471233
    0xa0e061023040c020d0e04060e18010f0501082b05160305040f030609060b030c0f010f090e07050a0810060207090906090b0711070b0408060a02090d0f050715050a0c 72
    0x85800c4110401862100c0001c102650003c484500142e0300241404100d00c0e00000d03d0840d005c815141040300c0e624007100c2c400300c030b01c0107450300102100e108078041c4ca1080a400c00f075050104030b2810700195959010942d5203115205075110656a0020700302c00c3c2081d030310407208001d4002d58072581454160041c2110500800c031046050103406c2000041c011580c0b1031000056000c1d08000441c6840c134103046007650240f4800c03907c240c201c0c08103040140e80c0d030241c4180d024001e10384041d50140c0410180d40700c120981003000424902c508020354654004010401d6040d242d548107080e403140c00140c070450704c0b14054040960001c03071042c8080380b411303440391004900a50010030a10704503112001f402005952080000301b08104820302400c00b088050003c2c8050580300e0f00c0c041c03a0903006900c4da8406402401040d0300002d062041d940c440c071480407031603084601231134200a2840c040b6543d1005e032007000b092110000003015070030300407801d913080c0311980c1d00c2d581c22209080d550011320 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 906473714 1250 906472464 906472499
    0x611041805040b0601260406021812100b040b0d060203010311030d0804120504031a0709080c03060606070c03170304020a05040c1b03050d0906061d010308271003050a0e0610 76
    0x951050205403180c612038031b600070301640c0181d50043c1c0d51060000c42890325902d41d000036000d00c01e44078008001d4a400070780110705040628001540420f41e400040180c00f4100d4600e5001020005200074400e942e802981268030858600c11002824000d25803500c2c14000325102041301c003000503010482c0d440b882000b5081d01e2400c83d18142d125940d140f00700c01e580001703506410807401000a000d4201d000c20000d003a4010044c201080000000f82e95802d00520080c0501e030007090400c1041072220b0420040d66000c04484195020320b065500b454204441c240e22500418500040900302440f907511700c05150b9a5051606210908a00707425981c038104500b000000c00003114011014443c40001c184240c0000c03c0e15031800d030805c1c500c01000b600f02070781d0b011560010400150418204d83d00e24400d69080d2480c15840049248a0000700b4407058100044c030324418280ba0340b55210070310038030540c14108024030840880c5541c03614215192810100300701014405082c850201026 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 906474820 1106 906473714 906473747
    0x12040f0c05090c160516033801050607020a090617120c0717070506040b040510021b0d020d02100302030708010e04030c030e04090611041805040b0601 66
    0xf0248100801c07000304000c00d255000421078244030100c848100a22035106003036503400c011003140d190204542075109211100c2518041801166800d003200301d9500800740e0801080c8a0140d002c01d04c1668840888940007400700c01500030a8007400e1101341c861000d1803214070b4545000284a00169040410301c040285071200142c8401200c089442001d103440014040310705000268108030307042080040c0110f1404100c2008000301d17201500c400c0403054120340220781354140b81504640e5204007424030308081c50629180703581c00740000c2c108610136000f40c1c001004010303500203050110707402004015010350800c1d0154014107060030b0803c0c0d507207000d0754014070340c52a03200000c0c1807200a408240e00d40e100c990000c460107620100c200300c3c1c0004005020610f42241c0f140e141248600c0e90340d604840307a5402a6030080380c0c00000c04006031a0702005540c005c0396a008841c = true := by decide +kernel

theorem cover : BRFrame.Cov 906294964 906474820 := by
  have h0 := BRFrame.cov_init 906294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 906294964 ≤ n) (h2 : n < 906474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
