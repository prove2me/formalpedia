-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0431
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:46:35.056698+00:00
-- url     : https://prove2.me/submissions/203f64c6-5d62-499a-b6ff-36ca2f2e8b3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 77338131 ≤ n < 77517987 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 77339381 1250 77338131 77338141
    0x4031101031505010309050a1401020a0206011e051002101d0c03070b0d0207150c17090d0804080901030e0a0507080705040b0307062a0c171b06030612030f040609050306 74
    0x2810b10a80111410140d440b0118000d00204001041407260001400c41c0d54505041406d401f039481551040c01503c614000043d8070ba510001e0b6403070b071200c44440f42c04090300701030400c49246500c8640c1030840c86444204406440c05115180182d261845070040142c80c010070142414a0010030a100e9081401c081050b83e00c40e404032005003100c640b0050b9915a80d01e016040400c10034600003031580750001070100c0c1030304001c003500e4540360000300034056510325210b20341d11400b092518000807131510101d000180e03254040e04100078141008100c0781440702015207840041e484c07e0710b8903800b01c2d100300180c1100b403000f400501800e0710140b10300a5001c01095a81d80c0c107110382c00401071020002c4040b8002503120481345440307046071f690003104034180f00d070258410f80252114001d4426401c0000d941c00640308602c81030040d404901a48113204101b002d400060405402040c885103415101c641070000340303502c03981040c04a8855003440700041c08650540c22150080d03220340c2c1800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 77340631 1250 77339381 77339411
    0x90509100b0402040e040b060301050c0307020d1b210818031b0c0a17060105040504200a0b0705010516020102091c110913020f09060f01140c030f0403110103 69
    0x19000549080c0458501a0500818001e01c44c41d404481440605d5051004100c20710201501070b1808500038400c94032840d180003010f22040c0d55080c05070b8400e5250040490103017640100c0d0040013882000d80900da62030310810352030b50b9010001508040e03510989a1604101c0c0242c0180d44002e000d4003030032081d841c17181c1d00d1080c821201c8002c0e19079044050820000c00c85450907032005000d400c03d043d55808440d010051410f401041409400008150b0381014840d8501c6240c0203803d103542c002200c07211801e0130071682e9050750001024070000c52802803440040c80b0f842c1c03140c0000620303464003144114012541d030000030110390042000d03088550b1040840040a10051041c800030a40d42c900045480b4082c044190082c180e00100201001e801c129000c05170300a0303070300c0b15030b1034544e0303040080c03281c4220750303403a80041e044003000310329480358003150681c0300d0310f0210500c0c003401030452520b150495a03265000000010b024000c20109080d40b0160070030a0070203204100d40301d0303800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 77341881 1250 77340631 77340643
    0x80603030418180c06030501140d020409020d060507020f06090703031707030603021509010201140f01060f0c0209010f060f0c0b0c09030c040c0503060f1f050c070e010618090509 78
    0x30700c544140740803000030039600300d0f804484200089905035403078081500c1c0030589a0b40e203101d81ca003ca851b16000282c80304203858010078100c001800703203003100e01c0c039420800108070030b11060340c122a800c84041c00140d528864503010b894181c00810390404068107280c540040245018403a8000240c200000b0303030000b4440440f8814640490011b03662550100e000b481aa4000b0354007040d42051242c0380081c3e1002402900c00c03e9000388940321a1250042c6c03610404d031203400b900c003024401000468070880300c600740d204640c90b04107189500360300019804030081e04039850215254104200316a00702d280340080036624144040903014580300c06800341c000800c0d030030003004c00260702c403030980c4c1c10f02001c140110010b204000d440c070001001412038100300c4d9a0740c00348102c0f60800900740360840700f208030811840c012040210211000702c90580200318460b4041c8100300340440c580c080c50b480700b406050544d031290441b01e001500c05802c107089a111950891505082c000600e00204079 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 77343131 1250 77341881 77341889
    0x20903030316022103040309090b01120c0302040f08010501060e10080106080c070605040c050a08010209150901090f06030905010c0801080d0f0504080d0305010314060c120a020904020301060305160806030304 91
    0x40d0030091a468426801c0c51240c500300d21034004d0940d00301c00112200f8004c2d6015500a603215034120b0744808580d821a11030315845800701d000f00e412040141d103140c10408080e070032460701500b056078520600303c021000760080d55030741e5124001401070691003440980d9000044401c44001801d00402800ca0b4806015040422007034130006505500c6100c12120aa680000c0400161820741002800c08645000d030740d00c1107a40c0e600008082105009a403800070f001000d9201c02200900c2e400e0481c3e20507207015060000518000440807c00c00c5180000c24643c0c5010504500c103142c0740b404c68a40c00c400600703110700300b401444040000100b045103d4540d0800c00e10f01e0b401c07014141d0301030140703500840080c810015629142a455007080b0b04a80c8600385035004c0061028816407560800c80301c046003d0014012442d0144d86424225080658800010b14050002c80487c0a0768000d0704030201003529101070256180380d003901c000c0d0709040380c070744010b45091000003e5120b01c56482 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 77344381 1250 77343131 77343151
    0x50f030a180609050c0f060f0d06030203070b21010e0c070510050702070609090207080307051e0304120e0a030308011208090d0f021302040806070c0f020a170f010209030303 76
    0x581520300c5544210040c0000880c40780c280103040c50520301810b0a40700480c0d040c015005000664144070702c5610307500d40014011410010f20288258050304840880310710f0715150640000580c9007800040c016154007995a9602e01c0a10900c03503107920001c0c11120341d96004001048170382401d10310290400625101140c1d40c40403814610710b0101307010300d0b15420a1400040c014110340000e0b0017412075442e52a429040c90361640350608034090712101030000d11080001483d110710070720080486414840240103084d40003150403134150002c076402c4410409000f140d0403183d4104060b299220340448407000d0075802c40e43e0040440c5810301c50111400ea02c95610000c02c035086082d68407065015003060000c2c2d5490800c0c2c007000b107407400285c1c02100403540070303080c3d0b211074000c44090300c0c6040000c01c0d02ea00c1c0c801d0120f41c1102201400d4604038101102900180d41b444109030040943d000d03030409010343d001c0d42e14100810b203050345850b80c2c410000007036070ba180481580e5014015070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 77345631 1250 77344381 77344387
    0x9030309010e010224090d030b180414010f060603060b0a02070504021b01020304060207060e03070b010b16080c0703020f0a0614090f030d020a0303051503100f0b0a090e0f03070201050f 81
    0x20040c1e00d09402864400745c4410103c086018442d81155214451040d8008171521170030b000000b60304940b440c0d6201c1e03411030301d00c4aaa02c4190151859250058801c1c0003285500e83c480180034212030342201d240d2902c84e22039804200480d81406007002812280c802c2c0ca16190319260060b51f10340052007124016a0040b8a09801920003107c0702030a600d0398000359541e04d0f1074501317440254000d036070449920341b400072613804c00c010004c02d8403441540007414482c00d03420a0805041500000740008003222104c180d54000f60724040642820a4060014001d0301d0861040224540da860085400f07081103040401c9001d60250300d1a0010300d5071281c281d0303285010400700d0703000505621403070b40506c07890401c2020705074006054032095000c0d5508200c070303440c0ca1400c0602e40b128020304a91580c4000013141034411582c0c44405840324003680064010a61400300c0d405002561001c1d6405a0b141800d1400000c01c0c040741070348a1540700918034000072540044c11368000c0031520000c410000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 77346881 1250 77345631 77345657
    0x50906100f02100603030c06060b030112110d06140414030c0c0f0a0509010609030605091507030b030a0506070c0302071d010611070b070c05121c03020705010b12010606140903030901 80
    0x24000c410044070340f10000c0c0b080e140c42c0d0501401040b90032001f1a001440c100000031540400320a880c140e034111640140708410688440070300007a0882d07081da20902c2190500000b911621504a400e10545442c12961800d4200050408612102c242894004103ca44282800440c486d21103520032246940400700c0500400c00180090700b0164009504000119a440d0050140011244160414480b03507484110450b2945060010b2030300916080001c204124040c3e0060600729001500306c03840462207440c4c65142c0001941c110b0b0100b07258618200600d58144560340250240c500306105801e00c00b50007440c041c50520559081001c102c20341600c0c120140092802881f00392011a110b042d40d0611014202e03240c45003510034031241d076100d080b4400120f02d080584103442c12030880c0d5500040d05801039401198101d900355078602c001c00036a60750802a11030143d541e00001075803410b03c030024242c4464040607039060103051108100550340081140c0c5c030703404286032108481901d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 77348131 1250 77346881 77346883
    0x1031104090c050318150408030703150b030117070f030308040813081b0907170903070c0b0d06060c050604020d06110304050f010b040b150901110d05030a06050906100f02 75
    0x11a0007540c081d07410401c012040d181c2c450051801095030810b0031000964801005030354805201d01002c2c0200b114001601203440032000d954480080e04011441e503202c03c401c60360100d115040b401400c1740c04801444840ca0820200c901d8081000007410310a0a0441411494603680320003000c01110800040410900b44103464680c0b24000c03860410b96100d040d10350f229a0020300310750000c00d0085040c00c10307151442d22180100c5040d120654008200320000040c403600a003d030505103c104880d40024800c130100d403000b4120359003015210007840203080c0960700a0382c040000c0142005000c00031480100b0110382269048035106200305151400c0801341412403aa07901c05d9a010042100b03100c0d001c1121013020100c1002044204004400c2104561014003400e07002541c1406082c2da0310990f400a0a4052050404540c1007050ba81041d180010f0f89880c5800510b000c006c0c4250010a8050b8401429084844184e64500b01e40415030817070100400c4c10030440c450254940941c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 77349381 1250 77348131 77348137
    0x810020307030209060d23150103050601020f0a081c09020319031b03050c0f030315060c030d02070305130504020304020607020d0204090510020a090b0f0f071b0306090209060d11010311 81
    0x2401800381911003090f00d10510051240c102c3c447c00c0e138103c4011485030996206000c512840c846c0060590a6044070011001094002c2c0160705611500c2100d074030703046042002c040801d214004a03992070802c00b48042c0c1e13541d0007010002c101c41c20900000d00607a004075010039040740c2122442c40032031315407c080380c00c1c0d123810207140d85200c5c1100b04e91040c182e0010003400d0410000084541d180041031072540d0b680310407900103024442428801c001c81c0b80c00c1d801403c040c224041201d061054104000080347c0c0040e0040300410000690400b13a01100c0c00c018005280842d81181540351075000b00f2043e2051040c001e2152920068500865480e0f03070080c10741c541c0000c100d41070200b41d204498001d50000c601d00021900b00d20300003c100f46184225441c1c0750a80307540300c2c05c280c4100c1e00c04103c0d0b0000007049504100c0d05284110103100c0041000085008000c08100d00035280140310780810b000d0301042c0030740700202d8400041041941c02c0c10820000f8a40059225a01202107101d80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 77350631 1250 77349381 77349397
    0x18020715020705010e0724030e0609060601120501050108040f080c01050a05070306080a020d0206070309090c020109030e03011404020906030a05030c0105010f0b04030f12050d0905070801110408100203070302 91
    0x81820398000c0d00c0355405000c5841c4110f00802c030404030b001c3c180343e85900398812503400c0ca035020003800603269001030002c0000300500b004a00020441c2580303083c84c0c81110050300550004041020350369020a41c48001801e0030f00800695051074002000d580000b032000d8600845508028104060b141c100c039509507091001300800d06000310f44002400040e00c003240001c0c14807a0220345603402268036083c06500905030b1035481072542c00e00c202c0750001079040d0188440c01d00000380303c0450340038144404400f80d0001481450502c0c000d8031452448005500980c074000321049000c1c02d0791001c80e04203070102c42c0c100d056581e140c0024644030310101c0041150101141c40c1b0f000100c1500503c1c140d07500c02443c501c0c55030300c9611800c0d20740030390310003c0c0c40d001300440c003071000c9450b505501603004010321b030403440c0100c0b04a051082e5108618200c450f030307010090410a90800b0302c01c40d01d4a07205052086d141c50f16000440d95034454110303290780d01550000c045906c42d4001d134111003040d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 77351881 1250 77350631 77350643
    0x3120b06040512010c1d091f050a031a0709050310200d02040e0106140f1e070f0c0506131e1d0708070309020607030804030e120c03070816180207 64
    0x3c0074620240602a08a001d0410003054132142c0740409143c1d00f00d19054011406040710110f070f604c0e1041590202d00e07101c8441c002541258002c126522186180000b030740c020b5100f19252001c10b001c107184150010301400c10072955100a010a99011440310001c08035030303001149205600e01c2c900310344850040341d0700d0021000a40070752403003560f4001c1d00c00c86040ca40e0ba441b6503a80d03032000765245a2030b203071040c0c0c6d050f0080101400794014031000d001d403a0b0598075001069288030742084101d0380091410f641503105c841c249810421080708900c083d220583e0401e051041581d07010003d10400c0c0503201c1c641c0c0100954031070000c21101d0b40b100410303038507074080c0301c6064921000c5100842039495a00141c100b00c00074200e00e00038041d24080d00c3d8042c06140c9080c0d1a03440840d122a400f6000300c2c2040b5440301d1400c0160b0300c07404c0c800411503041002d084c0300084407042500e040540e600c02901600198424140e03081c0c03841e450411208103071204140c9550b21842e4000034403c050008081c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 77353131 1250 77351881 77351899
    0x15102303010609060909020a080c07050c0d0b090c1002070b0a0e0303070303060611030a0c06020a030f0903030b0a06020f061b071407030b0c13060f031e090201090f0303120b060405 79
    0x1c4a500441d02003c4482c15180d44170281c3d03c80c0c50340d2090f445800002c4011480040201c0c130000c0e01c140040c0032b1280a00142c0d01c40f8900c1e02e00042007100041015a00848403000380300c1c01d04030600004e501164120390302e41002c3c2d62280041c2d240c05440c42030125003c00850400001c81c050b084103161038000030150395458015103800b8000b0071482c0a10740c00101d1021110320030f00340000072a68007601c50f8503840e240700031994661000c0d600038801e000401d51109001c2000c07845600071544610312035100403403540d1703c01c000d0180031059940128115400444018403094011032090b8000b0250401d00c070a101c000c0005050074815000002c01c00c607480a0307010140c3c400800c818040d280700704514191504d5040c20b4407140d00494000500c62018800f040003640e000303448207000032030fa5003404141c480c0f1901e1010130048001540ba03d00070b0300c0b500807404660f4000240c2c40500500039042c0d005604540b0000c2c0b01c850081540000035903a5500e40d800b40c1c0e200e0007a0341c020300004100c5c802e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 77354381 1250 77353131 77353139
    0x6040b0a12050f060702190f0203030307030608010c09030b0c031815040303060905060609040b0310020705030301050a05060f03070e0a03080a050c10020901020a20150408061510230301 81
    0x8429901c0600503902030283c01242c204004021a1050080030170b40d00400e80e080b04450001c500300170b106000c0b261218240c54560040e102407016510500721610000344441c03510f121542541d40200095003041a40b800030300024034581e4440342c1000b00200d08c03c0e245c0e81c5124500100c08205060604188254850010342c4252281c1700c40c41036109940c14440540e54200c00d0064078020360b09158444d1062154018906059218001d01c0e0001030840d5420440c550100040780e002c01d0040e0b655810000040c007041c100300c89403c0c01000c080c0c5246107400f05002d6107280c24000600028108456440c101109a4801e00e440024540025900b9501d101a950151259210020b003040700d0040700c043c0114508ee0b8401c0c0c80e80e1036010f802034813586540c1c3d0740d00400c080740140c00104d0110f007400440740359107844002081c003205810746190f8603810300e07a84914207940140041207491f00f8035110384031a216407000aa510f0000d041001103007041044041c01c1645c0c10b10703071451076800400001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 77355631 1250 77354381 77354399
    0x190e040207021c030e0d0b0103061a09090d0e0609240f030a090b100b0301090b0a1a03040b100302030d030209010c0209040b060a0506040b04050d05030403050709050604050906160806040b0a 83
    0x3d509980b098564908081c800d0b0140850319500610181105920310010004109281c1084240c0c800e0182e260040800d01000550020300a0750346150561041c0d10f225565a040105511003d104403900c5041220a90014035443d00da0245c07901000c0d456a883e0403c8081a41904c0d02412100180c03602c914180704000014010360409a42091001d00032a402c5004a643c04013592030000314145075030300748030340701e8081d0190500d03054001d002c1c1a40000c2140124407602000e40c1d100c4d88030340d0740c1d04250500c0c00c075081d030180450107010003140c0c00300010b9800041c18266500036007409030321451480010784a13640c101d5006504403010101f0001040401c0c15903510502e812034440c6401c0783c80c0c400f444040d004500034050494810401442145012200d08400c0d07071042c421a4030306912550b80350b00380001940510b030100d072240e060042c246064003034103a008507190010315041c680700e0390403041c0714285200700041c4100000411501c5e122500720ac10414400703440d01c400f15940781842 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 77356881 1250 77355631 77355679
    0xe0a121706090910150e0a0e010c0212070308150618040e0a080706090503130306060e0c09061909080a051b01020309010c031101021902060402031002190e04020702 72
    0x40d04050003a00003404524002d03000b9030181c0c40d010014003445000e0b1242e01c0003403250045041c0031030407603007000a03411158101c05118281180e000704014070f00144250035205c840e528582036400c1303448200805940c2405640d44281c0600e8404059280d0042414008070000205600890005030720300c01c0048600e40f0b0512080165000c10900012260f03071a103400107044014465442002080080f404640100e1000c0e802042600e161564429003000b680b12a6481100c0041d1180004c105905100b061150312007181c0100c00d00e0306000400003040e91040860150b07030000040b05031010745105a84441c05041440c08452505206051066803110b00c0c0803e1104424a05990000c0d03510100507201030040685071003420050940d0150b402f036913402c2d40241159800d01c03210702000c061304420249030100360060800c0c4d040038014141004001c1d50741c42c898500400c10452a02d0403000c80c048250b00307a03e4481640307450940010041c0c4610b001c003030341c4048800412100c00080c280f00e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 77358131 1250 77356881 77356907
    0x16060b04050924060a03020d1401050405060901111303150e120d0b0607020603190e010501030308010510091a0c01090212070509010e010303020718020c0d050a0315180e0a12 76
    0x8002d000b01140003c44041880413101540c0041d4800d00800050a148260b20b1990344280303813010305c0c0500380c0c10780c50854030112400c0e15242c1c04442072040c4041c0030310440c41c6c000012212245028504042041c0400852000a140e41c0c1e00401c0d0031215646940101100303030098003a03560041760451416010381207080c1d4214610324000300d4100c5850a1407c5440c4150b000e1718035415a034440002411200f0080410b004042d290800450f00719820f110f0035020398869140d0030044d50401d4103025081c0058031918040c030026030014091728050001882207480e1030002c05586100000c001805001c13130400094000e400b403034150f0724060011940200ba24400c1d5495800c5a907030b000c02290019081c8405000750300b00724418000c184003071803420031007400c0600262901c00d40030081d171700d4040c103601b43d503001850109107400403540c0341c00fa0b00210500b0031403551075142040044000c1d107604201184070583d85207840e14500c0801d04c69442c1c030641203003003042d032864103510151806200000f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 77359381 1250 77358131 77358163
    0x4030302030106270501110a30050c07051203280e0102070e070302160803090106051003020c0c091b0c010209130c0e010e030c03070303030e100b0616060b040509 71
    0x8504caa040c2203540d00d004411480d01c110084c401d04e48001515120482d580a621702d008080303007000824980484545c000200034544188a44007940300f540307003a04801d0100411900700300d41010408002a003100f6624200c506000e46440245505e240d80b152001120340030032003d14101644e204454800610401138a514000c040658012601d40d40580130b4000310060260229141c1031095019002801c1056039036100c2c5115070311941420740080b202600160f450310400e101782c1c20300900c059850a0b807070a0650800380070042d41a120000003e025004001041c000380d900d540c4014011190b00c0703540042c603654003c050b00329010394050240d1500942e074014449000d030fa20f6110324106030703e10703030340c1c0d000f41d11244001101e202d00c10000c400d61510405c051513000d546e003400002c5c011032280c1c8001a80003021101542008940c81004103c03a2401720320203a2926110b0880701d000303505400c04041c809191604c1001040142880c0350094941410803107095070000c0c081290903200c0c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 77360631 1250 77359381 77359397
    0x80d0215010515034003031410060c060b0402040305070f0807150804060615030b01030e010515091003050a030801080609010608030a030905011e06030b0903070201020c010c061404030302030106 85
    0x1000f840142030045803080c120f49010400140305031101210b0340e8204202c0c407010080c0f00040450841c00080c03080500f020f00c00c44049003810160584100c600c907225485481e0144d180c442c43c100b50440d440d220380b4040c4440108030b0010410030b81d000d2040c1007001881191204c0d241e042039540e0316a00d002e64101c5180c0c001c0d0101d0003402c0013460300119456110b1000518005802c21914800c000d0021a1390548541c00400d82c200c807003060958458840d03500142454280000406440c0c4005480000380d01d00030034001c0401031a0070250040006941115054aa581480c039840256038130103003050003000c04150030103a100d020507040b00e08690441d40035441c4d0340c034064206c41c03142c8100300346648200805000355000e034104540240c003800c00012142c5a04070000510002d40e64140d150f1940d9101c24010400c681d0f441070f40020718040110306024042d40080e64600450040301c0c10f000e004078044040108075000340000080101d44200c050038180f90250180d0001c0c013644000c03c1400e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 77361881 1250 77360631 77360639
    0x1308070f060302030f013005211e0a090f06050306012006060f04020d060b09011b0b0601080c0409140702060105041e09050f03040b0405040506040c0c1b080d021501 72
    0x41e00941c5d01949940c202d500c0e80380d00e000e2514803001294122402d0703100b41d00e104d00030450320802c1d280100d140102c0281804440b00203910400400031600e03203003110000e010b074201c5c804100c2400340300d41226900195030f88591910a544101040c0d10082150207501c0d40810607952000196010303100a0701d9400d04038018010b0400c00c81d5140728000541e61012000500c00d01e403030700440d10304d450090b01c0145801403401c1200c05441e8140c0200184a074001280d03c207650707100c05480801020078054150708441591031a1007240003414883c10060130a0200f080481d8200850b00105450141000700012800307141048480480d203000c09809038074000901814a03003c0e003d501c0c51222100c0445142c46154071000700395000040c0c41038401e01c0307500d0f03074100c90800c0100701602036162415102ca180204100a941c0018001400345040000d519540f581110240011540c8000704421511260020002c6005035078803108003407081e41d028120131500802c1ca0640b503455024481c01503038035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 77363131 1250 77361881 77361887
    0xb19020712110112020d02041205060f010612020a0504150215060402030112081b01050108060108010e0c0109032604170606060c150a0915020a1b02030d050703051308070f06 76
    0x2000e01802800d0302c0c103007540301503100d4900440c0ca03480c0e841c40181003584da90f501004a82054000d900355404c1118804284130f8100b104c40d90150459007810f86540c10580000c0c00300c0341ba00026070320140c0228008400c0d42c040c00566010b805802c1080c040003170140c034025617a001100d2949001300816000c6444c0713040c140201c2e4144c680c44a0030002001d8607035030b030769096407050003010807003801c50030741409100d428000c050082a00d40024580c1e541800030321403c5486440c0b00b078555a01981501607540d81140162040742e400511014030884000c4d150a0b1841c1c004010f035462080001d000302d0003106c0b000600e20504801400c44a1036a030718409c0c003003940b017a650b40d0461680100d844450292182000980c8400584000b1501a8055680321083c00c00c424000168907000b051411605500010701503480041480315020744082d5000b0a84614990340ca0740d0400c44c0009042c414180120100c900940c20800500c418a54864160380c840c031940c041c081c0700104112000406a01c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 77364381 1250 77363131 77363159
    0x30603280503070c240509010c1109011d070504030210080711100507030c0207050d08030405030c070b1902010c0f030e150112020405070c110409020d05010203101a0a090b03070302040b190207 84
    0x1c000d4440d81d15095545c1d0040d9905000504101e0b202092400e41c02c2440c0c4030000020300038901371141e9507504a0011540d100d8400040c000070404c0f10a110400245c1d5421400c81509000390506c41c0303040d11000e108480c044181704501d4050b10070803243c00e450149a0344400d01c201e0090360100f000350039906007245c5a5003188900d80c1c0c8448e0b129254004128600011500315201c0d1040741e180ca15082d00540c1030505692082d0180000410400c00a40d58000c0b10000c268581c0300030004048051030182401c1042c4c11184101561843c0c00c80010004102e9506100d0795800d41340b0b480d40e5951050209015102e1040340214144000b0600700d6000e00d111800039a0705c1101e124222001c10188802000b101d88147e078040102c0c03001c040400c13403c0c0300540c0984244100e943d860b03800c00d4108a09440b0b0040601a0703c0c60800107098030a5000c400402030320096112650b6035110000114064020381e0000203490360001409a001c00e1103005120340588207400303071003001d50b03038859640820b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 77365631 1250 77364381 77364449
    0x619230c07030c06031406060c0304150207050a0905040f0b1005030a0b0a060603050112080a020106050a03150e0c01020a1b0302030304060203071a0c0904020d060f1514030603280503070c 82
    0x6c2d40d40e03000c20014680000a407411504080c1200d040c00d0395202407201041100d50254050b8103e890203100c1801d09541c09009404184030034007183c1055036400f0105038800c0000703042d52580901044c80c0e101c210000c08010100241100c0c640d922a09020320981c60030344e0004502c0c0d01d4001d00041e80e602902805040301c042c0e25010107010410388030f400403513001d0443c50046541e1503001042a50b03403900c0078400f03140103900c071905440c03240e5002400c032401c40d03080307c00642c010925008603a82c00140c031507556a05c10103201001000402c0111050001c1d007009503d030201103004101c040c0e000020342107060013540410f08038401c0100e1003000c054161120101c60804000c02601c50400360000d01c0c01100c012000100b6541d5507000c90100301c05a003041c525030302c03920b02d1049659405010007400d90003038a8224a14104800081d13036540703201c818054080c007441260b40d549030258101e41c0107650444141ca61b07550340d61500e0f460030b8500c0d01800707140c1c03c00c2080e0780015001805d080d540380 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 77366881 1250 77365631 77365661
    0x6090c080a1a090a020f16110108090c06070f08030405010506031506010c02060c100603060605040b0301140a0903090e07020102031605030405060703020903070506040f0807050619230c07030c0603 86
    0x259220601c009810010100f81c610b6401b080140110019400105140180140540348031000e03490812000301c2410b4001e0304002912040c4814401c001c42c04058a00086274004e50341e4116240c1069031102502020f000400084204401e006045d08602c0c45981d00300e00b541d5000c102401078080d40c9409480340c500140e070703034112100107040031801031044810200031641512210070500b02a1f510700c0e081181c0068a8a81c00c000c6400c2c80d004506050004400901000e00e07591141312051100809255070103072501c1c004070a0500400e002c6000c1e2031009002c6c003480c41d1100c0040e02035441902c5030300610707441a102e400224454030590303000c1d6a2060240c4503030b40f540c0000b00d0280d044080500d80c5801040d80015280d5100740083c8028111003c0780d656040c60003001501707200c003603030110303018040400c0441054007860f030040e00400d0031400c1c50203518200301c00c00100d0150b12109852a10350000303000785011400a00001140c1c41849450002911a8800c034151107040042d4414 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 77368131 1250 77366881 77366921
    0x90f12031107051531060e07051c020402090a231c0605090c031e060106030219140706020c0109200a03060e0a020306040c0905060f0904060504031206090c080a 70
    0x31404444c404a80000f410903103032048000031606030311a5408a88600101502402e10400300007150103586c08426060b8060030030a4980008604144901e21800c0e184040748002001150307910b60543d100703568060483e21107991920b072a07001d00002800c000e02c146948501d8103459103000702c0801204181c030422800083c590b40d460f08040c10001d00010781034000c104001125480c204811500f01020002000c81021058419410031506070441c40805004001160141d901807010000c40c10302482d14240344030403181041664010110300a1030907000217109a1100030541007980014040c0485005005406c95032270004904502600d0300314420f0407041021602d640c3c428004007002405031103103d5126400a402c1c0601194116020074002d401130007030390000d03c5182d91142d015981c84005810502c00140c41d41e9000b072005080300d0301c403000501010712402d003a000381c5101c4042400440d49070b000040140518500850008940000180c0f080350342c0d010746500181d0071154044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 77369381 1250 77368131 77368153
    0x403110402070f060506040e1c08010905160804050f07031505150a0b0901090e070302130b09032e09030302090f0f180402060c0307030806010906080f0c0c01090f1203110705 76
    0x4042c05c0020705465111b65282d1003002c60b6001803054840c13001c0340440800420740c03070382005022644181c2003203051038500410800d10103d0605c40c0001900c550a0040081d642c03840d18a203040350201080401c0d0203415400420000400c120142c040e0340c0c1e1a00388042d549610141d40d1003100101d9050b84140c08060400c98607001d0f000402003601e0616114070403d0b2600d052030b0b01d0311015152040025400241441d14500b152181000f81244034515483d02c07036041c1c0040e644400150925070b086a10100307500d440420ba0078100761880c5080c0d000d0008001c02d08000d4001e4000e0080d66000c0d25100140000914105041483d6110002d0003041800001c070364140032440010700c201d810000421030340401d0102080500b00251203aa0749103228030700000010f103403800782d83c0030205102005007401101c03400c0817100c6522040060505407966005900d00e80500010080645a8066500b80405101300640412040b01c0191000d0102444140c3c07411600d1080d88406406c0741c1044d21106 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 77370631 1250 77369381 77369393
    0xc08010212011802070606030f02090702030304080904051509040605010303031107150b21030409110307080a0c140a0306090b010f0c06091109090a02030114010f0b0723030403110402070f 82
    0x4110f003104a07a0040c141070f440c0e520181200d403242c0065a560482403080710071883d081880c035500c46020310181d070031802c207071352081c01f14000c4603021445940c8543c0018211210318120480102004000110360300340b90034550010700e402c0c08190000ba003030080c0703400d2245544c02100d1406a11500030210004a84c0c02ca60040850000030b40d803107a00214441c40d520f408050107c100741003000074554a038900032101c41151a40c000441046006100300082c00d41c01901065200281d0381c40800c800001140c103e07400110b440300014050360106d20b148205505600c030f6010748030402c800308484003984005642d003040034607400c2d00107120010781900260141c1c0003000d410748980500c4898002d440001070080400702c4a140c02980242c41c1c0205500e4240662030300c1c0303400c848840080d0350414010200406481c0198003d400b00002c458003001043d480c0700b2a11305040ba5882d2000c900d48c51600c0e16036001e8441580c0b86d2149012030480da2500c0d208481c10136600100468100744955030b18 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 77371881 1250 77370631 77370659
    0x9060e040e010204090203090d0221072603100f0506030402090711010e011b0e011403070c08090d030f11010510050f040e060901021309060b0d051f03050a0c0801021201 74
    0x1e07034015502844005844100790015500800c80003016010218411800903e01020740542c0f0074610b001c1101800301401ca6001c513803000303801c001103c41c842840a03140050781404424020b1280001042000980c40c00002009440e280c011054031385981d4401c210745030000ba6000780d400318032040442c50711402802080d040401400c000b082040000c42110700311401e810228051f100c5d40c03070f6210409540314925a4015134242800c4403e04500c5c007910890b400300410078028000344500c007809004249094420700d210042001021080902c0d000704a40113a05202e0301140c481c0e601c6510424060103424805e03690801c0405295180808024101d4080010540c00903134a002421078490103001d814402c80540f00007503a601902e40c0075175414040c2e0751006100134078001081c0040e00000c011200305945548001c076454403030800c424403000c0100e54203034002954500000822101081e012000c0340100c444414103a5104512800d031301c0350710a250040c1c080c0b840140403803200401c407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 77373131 1250 77371881 77371901
    0x2090f04200406080709060f02120307090905152b12120507020601080d0c0503091e1201050603011505030a02191a1b01060e0a05060420070501060609060e04 69
    0x2070704076641030300c2000d4045038403a4100400041a0b4030030003480780c1d008422a0000d007140d10304440c0c2070896071030080d00c6010005685c080c1c1c030787c00004194094031845c601d901501d403100c0104000e08050080c038550446c40000326005c1c41c3c010420200e20811811180b0340940c00010203100b4806a5803458860501c01c4885024070032500c1503201d1000c8988501d604c181ca1580040c8950750510108900d01844400c0800030010110001c0d0700142c000b000b510707007664096580c03003c03003141241031900e0760001040f010381007040701d40c1000c0920415000036004410131343c000c1003400054800c000fa402d0301c50186540541c8151003520050130b040220222030081f20301200032032070b1503070b8905401104110140380c90391000328945524050380c031594425054804002c0064619000096408002c0205480e0a055850000500c40d860320b0704818000110345440e2240707400800440c9100b500038000a0b60158605180410f060380541e0b00c070001d03200c0d40e480d054031209020701000050700c035101d9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 77374381 1250 77373131 77373161
    0xa0b0f1206010512131a06060a0503090a080a0c0303110f161109150a0824070c021003050a1a0120030403060e030a020609011103271b120102090f04 65
    0xc40d2001c0e07441c0074040c4a001710300c00c0360503102000d12402c00e10f42408011440d45e0801c5018000e114a40e41c03990200c030400d113007609005840360b03504001d95041541110001c0d005400020f14007a5a607402144d04502c03920984013007040c40001c41c3c03004460f000303440007050301c0001040381442104500c00301100030341c4504a019031892284010554054085e070304200c80c0020740118203960f20300a0312100c041d00740380c07005101c040f8072070501c07003800705210b5020150303000400082050a1b100e0701040404a4000c0d040702c2c0c1c00034036418010000d08080b0b0b1038001d19490006080c000f0f801101680096032030581d5100b0184001c80c0a1300b49850a180c4030b46000d100401001001420314011006648a0100a11744881c1c0302280070341405401414034410364500181c0e451070914034400d9a0f008001e44400402c1e80c491440c820a51062264203000b60b4461344901900302c0c08100c482810858007a43c090010030b164031a41030a03401149a025403206058504050904044c1d004880c2260081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 77375631 1250 77374381 77374387
    0xf070611071a1606150504020304120c0f05030a020616030b13021b0a0f02100c050715090306140403180b03150d0b04060507031401080d0804060209030102040f050a0b0f12060105 78
    0x1c9100d030340181d08141140c00e01d0b05c0325401d020420210500c0c034018482a2015031443c0303819036580c540c5054605603107080c4100c544190081c851038490401c3c929078000d00720380d66207a003042c0295481004813040074a80000e5003d03080094824000e00980d5480680060211882a41f4441c041d40040e1096400c524146a201c002e8820804c03d91115070b00420b003a850100300d50050001c80f4592400c54414040c0328144100000c0001030324108441c0d820b03031450b140d1448554100d0f4841c20642c405000c46007080c0711a170707a4500c1183d0076406075200b43c54a2800501000070030b80000040d205100c0240c0f811704c0003c101e803a52410f0210701401c01418140b241e801542c1c0d13030822000685094459640c0e401c1000301c099054401e01810007a200c2603040e0340e40c5451089542c43c1c00d8096080c2c204590070001ca0100034480d01a604032400040095480b075848102c0144441024071035540710742d030704136400602c90000070219040030200315070503850301103880715400c0710110107000c03281001020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 77376881 1250 77375631 77375647
    0x601020c03070e2208031503010b10020609071505040b1608030903070b100b03040f050c0319050709060803090d0c0f0303050306040c020105070e0f03120c0f070611071a 74
    0x244510000303060403c4409805041034060500e40d4414880c03800b000a404110b103e0208840b001541d40c0242075241342d40007a86a40c2c082400351000e04081c0360040940c003181c0340020b4012031020b105503214004c590780d180d5a010b1280000e20301404103c04102c003048180701461000b00209074844c00301362412405481a81e400905510480740e1b280e40da000800d00c0340c104052640042d03003259114045180c05410174141c0f03c0c040c40042c200420240c00340d1011001c010082c402803042c504001d09944201c808601c090030340c50304003002224180103a0001281c5245548135800075a51140005c3d42009410b9041c0840000d454209489604c0c02d20b100040a42441c14201c004c4d503c26520b8a80f641000380c14002602d4070840400c096905200411107201c4e070000540803030041c02ca50700c21040c14000c0c0420b0a000c2c03800d9024541c200e00240101345064006941d0007903005040c11200c02c513641d1213049a84003100e541950a0383c10074001000b00c031407440602100b200a1010103403400240e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 77378131 1250 77376881 77376883
    0x1c0c030c0303051207050c030406080406090c060207090e150402010c0c18020a03060b0903100510080303011706010f0815070e0d03020f06010803070b0105090c0405030d0302040e10030302150601020c03 88
    0x4941e004500082d40001c40031000001c0032001c540005030350038034604090100300b03042d45900440c012082003004090004040c00303c660004509160000d440701081a101c00c0001e440c4e24503030103440c1d021410600840040400040c0c561007104524442c0195030702ca503401101e50046503541911010742034800814a1000c442030000c41c10f2844034010ba80780c1e0130140213415148140e0090104a50038001003006403008a01d1144a00f102d40b00084e45649580c03011020380040d820884151101000124404043c1c2008680121122003210150b0b03036544100d04240e0100d0040c021603411501c6505003800d030b411040b07600803030136007800021030f0342610101d002516030a8080d001a40043c80341e445000341481298090036403100618030300720780e9482c3c100d044881849070360f000d4070415001903203030351035101030782d002d800e0080c180d0390b51b41800d44000703000e5000f9000708031032200310b0000b0440d510341e000034000c07c5a6240c3c02400b0b40044d101c003014054100140760390705500843c48151340a0703030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 77379381 1250 77378131 77378153
    0xe13020a1d06060301060519050f1812010e100903030f05070c0c150c020d02060409050408121023210a0507050907021e070b03040b0403120b1c0c03 65
    0x869400030708100407820000031840207015006034066401000103115241d07101045507400c48054100400768500102d0868a600c107000c0d4080c032404010500e40c104d5102e80d07007040880c1e64101c0e45070082a604c068294220390101140500c198002d80c5020341807642504002480c80c042d0a0010701503110340145004e4440445003400015400f400150422030140890800382040342ea4800c101d080c0c00b1006404401d002c1c10184c03040e0b84941d100000c6655440450300a03207284a81444542441d1a04c0703c02500469104880a540940091f442100d82c2811f0011100942c904000020000075541000305000c0426601b106030103c401000004c2048036481040c0721800400f00b45a0b41d0402c0750805200342c00c0184144083c00512101c1070303001498802c2c0000d4041040c8a1a0a09804034504013403640252030040020081000348a4100a868421030280d02c513183c0c0c40d81c44003042e100721360745a02130b164445188015016204030a049030301809124001c042006030b126151402050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 77380631 1250 77379381 77379389
    0x40903030506030105090607020705190305150601020f0105040302060c03060612010305100c030902060901050c03130303020a020f041509020d0b1207030203070608190b060d0207050f060705040b03010e13020a 91
    0xa6221810b1148905003442820360120324600580340703609041ca4001d4980303143d8031625120b0b00d85400c070301d8941d113a014801801154800201e540c130509100030707811400401c40d003440c05030003402030f101c0400c44180280c6110b90752581c0a88240e513034262514038140c1015103050f070001e500f03105200d040003e03102200d01844c0a43e00901d003010124403060107850002e0020001c01d41001d007008016140c110917210710340400d085c0309496802402001d841c60090002d0710b0480b145000d800001d06801146c400704150081d11580c001c01d180509120641710301540402400c0e40c0e10313904001c0004540d018024941d018900803451641c41000128090340d082c20311946500691020021450b080025000034051814100354602d400e0001e40c2b00d480d05100c0280b4175545482284105a03a04412501040d015001c11500c0d40080d0500560341d080c80780c5042e513188100804905034502910544089405426009245030300b40700c864000c8440c0980a0365549107220302c1c0e00300594400004202074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 77381881 1250 77380631 77380637
    0x7020d0c030c050f0a0c050303040e040b1312170c122a0a110c010212120604090c180c0201020301050307090f0b041b03050606160b1e0114032503150209040903 70
    0x5d000300d080004130032496074001d61095000300010040803602e085000e600030303000450001c0300e5a5480320075811141d40e40d8010071000344011307500704090700301030052a202440010410700e9a188a006501889181c14131202e804414000416000220680210004040b550840c1c440c803654114070703842d0011041140400c0442d08110450741c010811549546c609100902c03164000020761150351150151a000d40308007480000d840c2d45842d04001596580301d03010802a569400c051482c1602c0415102802c03400c000540e02da080c070500030b032410390788002c02411880d032070950b084004007580d48035100340544400e9441007950b210f11811003c40440c800044e4002101500142180c2000b054288204402d101e40484421500303400d240c0c099200050000c1e644601030724140482106800c0c10340030898030000b2800b090342a80304c2c41421020b50459019241e0b0720000e014000b51100d5800d04904e08950400100711206007509101e0302e40200140341407208004642039035805103058000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 77383131 1250 77381881 77381893
    0x708030c010209030f0102031b130f150806030601030b1f0510020106031407030804051e0d05071d090d051c0212011809020307030201050a05090616170307020d0c030c050f 75
    0xf5a0600303100b051418003181c4000c40c91890443d0592019100c0c04400b0320701030b40080385615610411400b40c002420450351034550303040c0d40d5042d10242e506503207410800900403e011880d90300b0b0005049050320f6100c694029661745002c46602c0c0100311002d181c556608515001850707031142d000d045e0315601294000b107095415410100b444ca08420803c4891340d00a0380104049680101681c040d21030407100d1034014041810340b20a40090300b00e01c03540c410451007807101013003400608041201c403007144541d00d4501c2d600044c403406508950701800754006c142880b56584c8680d00071b10803000ca00e0fa4080130803c003050454203e07009940795264002016005011106803004281b80e0074400c91014400181c1c01e502280d10741e070313480c40000e0500001240701da08280c01002510f240f5100a030447d6200c0f140582042c8200a401400745d910f9042c884440c5545076040003280d00c01c00c01a0001d040e500b103028400c135000032a419043d01041001f010010000303a050091000302c040c0d040003402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 77384381 1250 77383131 77383147
    0x1b1d0415140103200307030216050316060c020114060904021206010801090506060d0f0615050d05060f160207030b0c161b0501030b03070303230a05120606071a090708030c0102 77
    0x121078142a615440000141315808040c0d245401c89501844078031300982c072000c42a03103060030712500b100000c04030300002c10701000316810f1020582509014607010700c1440c440b26001da00b222180101120840601c40001d030903805c001d600303643c2003440a40b455001d05550090b040c01d1103c2a0070002a60351902040070501004102281d0406811151042d07110804d5032100704c15035424000501c042d444995422201140300e00c1d5000902c0040c01280440b040b40c9440c640f00c00d000c03503401c000580e10501017241240f82421900302424107400a00e10a42162619a0040e80080c24446030782c404015440e07604502400051105200c0c03000741c802003110084074003210149400c2681003610385a0031000c541c1d00003400b0f1089031b8060400c0f61446480540c848003610b0040c030032707402c00e60300050425812a4443c000300540300c5141c1c51703403955860320b400b00401c9109911019109980307141c07800c64903110000945401050bc80100d030f0240d943c0b03420b42400c64024480203649039501040c004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 77385631 1250 77384381 77384387
    0x30304051c0c0303051b0a09030204050a11090d080d09030f030b180a020a050c0712170309030406110c090a23010b041e0f03050d031b1d04151401 64
    0x48040714003a0240c01155004036001445040d030000c2c00741c10592100080f5050605403000091840780b605125690707807500d140007034201e01c00b510003207029174600b05c001100c5104500ca000002c001c10b4010a00d80a041010031080810700c51080e981104c0400c01072240d01024441d507000c6601c40e84512032640d681140c040c04444982d00fa00d8040c0c6140c80720008810301690100d03500c55070b9028010307100c2d00c40340f4088806004201000c4528402c012012a10520303040c071103a5818441c908018859000000b100260f01040c0e0301002158070510081c40a070340143d40501040900004846008084c48002907901d0810b6618022440c0c0e078002400710302911036620707410011108003000317481d4500501030307079544604c3c030844040da805094840007001300e100c0c4000040c87d40f4501480c00300d80721305146807545546155900401c0c0740140040c0c03201c02805480c00c02c1c0b11192290011601c01484410408502d0144650701075550417000c1c1545800ba01100c014150340440e1121001c4024009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 77386881 1250 77385631 77385643
    0x10909020a0e040b04030305090a0206070507091b090506031302060d050907080c0307090510050303070b01090f09020105120a0f020a0203030f0708061011010609060b0d0f18110d0602030903030405 86
    0x200008400c0200f0040894614100a60804d9051400050941d50042c91504000004800a60041001411000748640021404181d0f59140f10070001c60342c0b5100030621344501c000c002804550281e100b0855031400001459105000703184042020300e40d6400200154011401d502080342d4070800d200d1242010001c0502a140000c010304881840340f000035964062407050760b040725160400078125072040e100741401800040d04480d00c41c0d0040c60640e2510030b090041090303c500c1d180300d04200701c4080c0111800c0700e4041c0c641c40e00d041083d18992480c0e07903000b484508066110042104101c09a00c010030038001140d01a42d10303801e0144d404c041f50003000d0220010440440c0c1401119a9030070382840c24440e5904245050f034443c0c000c1036014121651202d10642d160480000703816491768028083c02040c0181001181d0718403007080101c94181031a80340c2c0e10243c0d00740b41c00060307040c00d01c54507803140200b001d01822034540c2d0b0f040a17a442186c0f80c1c20b06800100c28003041220400c0300f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 77388131 1250 77386881 77386889
    0x10c0806030d170a090204090305071a062817070305060f010b030f1302040515030c090114010c020303070b04060b0a080d0203070b0717010303110d1701150512010909020a 75
    0x50007810024140041211840f00782206411030f424012504041841d032200d0001035002e0b00c10710084c415801c0240142d04004000d0355000c401e21002801980c6505904d0712419000305510310f144c4c0e890f4003586d485c1e0080c520240440e1544100801c69401d509100464004490000d0140c50304606d4828100407014002e2500300d4204c00062000c43c90030700c1a40e07030001d001a140c400580e01d00c48a0440310502c041c2c0a90094506014040801d180c0707003000c441ca01060307040714400120702c000d0264800c0300344a420011146c08141c800c0c65849809140c00d0180014100c81c108159616180d0100c04241d84c00c481c3d8968502c800c8196007801142d03800240320b00d201401524800c1c04004c0c0d103e128000d0000d03d48605100010242800ba1440e91901d05d2000002403207981c50345000307009024090341e40301e40e9110f8051100080c41c030560180e0406143c640c1402096440c1404440d42944010258030074800d00740700c1d58680f40070b00c0f41c0b506c0c02801d0080005c00d60102d00e0050100b07446682d08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 77389381 1250 77388131 77388133
    0x6050607020609240c01060e090303070f0f020c060f0a030e07450b120102042d0e0f01060306140603040b040c0f0605030402041d150705090402040305010c080603 71
    0x11440c0c0142e52a14242e41408905546181d11100743c4400c800b003582078060300e003004100c0410284880b540543c04801910311034901c500040d01c0307141545580f0b000440741c4000086082a481a0152140c4042070b001c20050046442640350384000075004d401041c020280d000d0045000b10070786905002d501c43c61481c840c00f5008850400e131070071a003545024030000c0721409041c032214074507140040f0071403001100700740d802b083c06003802c0700f901401581000e144140200b0071403032070108043c400c84085071404440043d008a0000541114401114030b429190305400c400142c0b50141c0c0400e14418040c1107692a50303581040e0020702290344a4000002510021513082c0c40d17902c6a40480350001e4003d0b20103070040ea501c0c0350500051610780c010820700b080c01100042c102e504030003e140510310885040c0804000203240d40d8505445804240051303010304a02a410019810002d401502c02e107042d503e03180b18600070030241da0265000711403da40d1003400c41c242541c0b1031251ba40003a0110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 77390631 1250 77389381 77389387
    0x22020d05090c09040804031202120a03090209010501050906071e050604140d0201020307080601210c03090b0906040c03020d06090f080c010c02011a060a032c07090b090f040303150e0109060506 84
    0x2840d05c0c24140114007004208078140d0342034502e041c0c0200300700c1d144000c1d05143e00da590500040000c000d400443c000724000c13003840d40007090f1580940140d5545060203080c0340d0800016458914009050a0034001c1c000395034206040400c20610010b4822401115503a4426110001080c900005400301c081164418405d001e02e080c1d100e0810741d048413003403a1032440100c00e605034000384654411000c2000b850001001c00c55070b05a0000c00340c49016a0101035595112503216440740000c52700100600d0301c0e00000c2c030040c90032a0286400c1400741c1e0380000d0035040c1e5078640c00d48400000301524040c03070202c1c5804114109005540c1024518802440700992001442c1e440311080000da6102d180d0202e60854640d101c0c0e48180009620200303203860013210385507000540408003401c0d010602400b00c01050000c0c5c45e010f00000540050241d6006645006c1282120080a0022010551560162400b40c17807101e8a400140200c0719003a0002d515100d940f5040302c40f0b81d801705025101c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 77391881 1250 77390631 77390633
    0x6010803090a06030902061b011508070f2705070c0b160801050f121006050103110a0507020603040c030b04030305150406050f0d0809090a060503060a09020d0222020d05090c0904 78
    0xe11155045500c2402c012421170507620028880d809200d40c04807401d0307600c4219540c80d400c15081400300e0007401c66034402007a240c5204986034120740c042c603e5590010502040340b94290302c103d81e44000c003114901000e041c11f100440998000790796520004020b003413200148000c1e80802c0350441d25900049640401407400684841414414039105e40d41010024227151a0030340a40f8074203440d9021b803580010030310b0041009002d42e010b80c50010b4645140c8004403107034007084a005514a85030b0310305195281d820403841d94001041265248003080001001840d4102c85030b000300d100e078a02042619020100009214617101c01c0c9110f035042ca10b0401141c2c840440080d46618183c4000700c10742d5290600020611540a070182c0040380401009480d2002d940b01009940c0f045058544e07984807030a01c031050f60086040a54020890504d0301c00500e41003980c106240c400b28a50a06e00c50341895860481c0c0065010348441d68840e020000c415500303000900c4103000c200c034120003608103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 77393131 1250 77391881 77391889
    0x1030b0904060911040906090c080f120a0203070b090105070e0f0d110f030a030c030f0e090105040207020a08060a0b030f010507080712091e03120b13090c09090f0201020601080309 79
    0x68030103090682d03070f25142002c2c001c0c091800303443c070580600107000307041891800c240141803400c400d5030207030310102001c54415404035a9003103d55080009182c1d0310020080e1450701e0748214007240640c402004080001181d1500c514400c0390032030b0000440d07190039003000e0506514803c40f20321070071201562402940c1d8038041751a48a40041c415507105c24108041075500c0d100c1c0c400d5545c540f003805030007400c2503840000c099200f41300b40d941650081c81c11006132214805d02034040c1c0d0007070030040180418182640a054040d0004000c111015503402c0b045003040c2c0300b035a0741e40c60309440d22115050f6003010081c41c5140a10000200007618000200501e01d44000c0c0c0002c04000490508450240c190780085960a800c4500e80358501c14000701030080e100e4010003140820402c4038026001143ca10542d01d880750003820042c0c1d902100c0341084018040050101d400620100c408902e0514522880b4013261140d0a04d48074040b950002a1401c0016400702d01560300400c2a031420b529 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 77394381 1250 77393131 77393149
    0x5030406140412230105060d120c0b191505030d03020c0f060a020d0c020114010510020f0f030a02061b040504050c070605070c0c060207060503010b0a0306050312030603070501030b 79
    0x80c00c0d1401d0802400150a004041c1c80746a1011480581c5281400107201c1406840590040901d6403600f04100703802440342600c0003220740550003440e204c03914001c100d0184034440307405000d190000803d000d640d10b40800d0401541c116604030710300503110b000102c0d10322809205242541c84110b800b0714090000b6a582060301585003010740200b800d1846600030014440d5402d540b03419140280341c1403041c48000d4000300c125440c000e0510350701009040c010320924034920038407100350080741c1c03e0000b40491040a0004801113100d10b10100111407402e0190f2182400034030041d5030b448140b600024a00748024004050140c000c6243d5080321146000312801c07607105840104d015540c1e00c92000c13040c05001009071006041200300400c440e8080d0f13003007015511800e4080c1d0000e8588008a07070301d003031034017030240456010801803083c1c1e401d0b08064648040c152030040303031407500e410100b803c0c0810f9100d54203540ca004000c0c81007500c0c0c24059400546400e00e41080071498200c00a14817071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 77395631 1250 77394381 77394389
    0x1090212060409080708161109070e040e0c0a03080306090106050a021f0902060d0b090912070b0603010b10050a0e0d030c0b040c0e0c0901030e0f1e0c040c0801080c01020703050304 79
    0x190ba5110f0070010094560b0646056a0300542e00c41d80fa1355003c904403145d00e460321003c58411012904d0500180340020f42c1c0f07805140550b4405140308070341c1040c07100601c565103484103a44a0341040c41c07250760f60031110b1800f5511480800c0c4e141d080c0082401a4071030181c02000070301c0b50030701000242d01d60004090242c10900b03007889055100c1160440004d00c80d4800180d000600080c003100c46640d80d4006015610054488820a030b803008000340d203032003042900440c81c4104002c40e01c0402d82c1c1b9401d260b0405001400020325003411000a0040c8081c3c045010100c0c4000c83d1050f1140d030800d00c071005044050300c07c001001e0865500800c4c030f0040c00e100801e05c22640c1c022600380050a401c62016080444030b43c0365600300510080540d410101d5090b0002e8280154008101408595450f1506964004000044000c44081c92400c6e005a4016080c8030300041b0300d08540d614090603e20100036101c00e206541011000d42c1004020b9078078905560000008000103400002110122 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 77396881 1250 77395631 77395639
    0x7050102150408070611030105030f0f0607030b030309030f0a0c080105040201050a030911030717010c0c150c050d090606060818060a0b0103020904110901030b09010f030b0a0e1c080109021206 84
    0x142d03500e00d00400705010750350014014504d0f00f607130f00700b01140c01c1b0000c41c148ca00032012214010840f11a01c0d40d00c0c42142e481c00d015410040100780054040d0300080e83e10342d0000d054a007050090300c0802d00d8004188696001ca0b032140b91200c0611403030340740f800050040c0b00003c7c031992406400207000b034414000c006003010340d00d101550500c00701030080d46040ca0000d00744c440c6c1c41e030b0f290b120051040030000000819440c00203d00c0100b80104c1c4c910604c584d009811414461041000c42e00620340d0340c1842040c41002c21071000840d400703100b810b41040c0b1075003000039524244003009041e904028035140e4048002c1c460300c2d440c10380000360035a000191341ca01080b03854503038004070080d00500e1031480c1c2041c14054590540b1100364003800421a080e40c041164020740000c108695000703209000d000101c8100600c0482c080841c2d040d40401003000100d25011203141036071801c0d280000100c0c44501d1618440c02d255400120140107240e032440c15401d105100c1d00050035824060001445 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 77398131 1250 77396881 77396923
    0x902090c0c0705010827060f18060c0c0304080d03020c070515071b270b010302040506070305030402030712080a020f0d02190f050307050d020d030204180506040f0213051207050102 79
    0x1b5203601c00c2d100c0807400b540e4840c202c0c104264006100c0d502e4000341ca0b000c0008060070f0021391a2a040e60748d00d0821104840200f9564803a6007018605a10440119640d4003042002103665402000680304001941d580140e903441140c85550070005a50010762044070b1114204000c1e400d0030043c0c48607150050644050071030030183c01004084280e002c1c00c14140007000542302180b4242002207104090701c001d019989840300118200c1c8118002c05038491000d01101e00428805d10145d83e0291002d02260034043c2c80f50404100702104940444008500140640004da0305100030018001074000800d16000d4000000e903d0b01c40c458100015082d88080b42d1007480724810306002b4440c2c0200c181c0383d4400701c80c10f100d0341740c0c4111201c01e0050301c40c04000c4c0c00401d11030b01c200da0840b0007002c0005098541444600042c210103010190b01035156000c0b8491400c00388001d000c90a40d005004101300e00c0c00c42884080c2c10150002409504103410410107070340c01103a42c000c07130300380c04001043c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 77399381 1250 77398131 77398141
    0x10f0f0e120601120212061303080a0e06010b1c0b130b0102030417030901110a150b060904110309070902031611120c0c090606131e05040509010902090c0c07050108 72
    0x98251000540301e540c402d0000009100b86961030000d1818001e540c948807615400c181596a8202504d2a4400c0c0290030021004030b440303003480c5038000c1410038010901150f01040e82d89002c0007038101c194404800a88240040703428030520a06d0061007070103105881c6c0f00c1d000034242d0b0124100c2c881d00c298a44d4a0106c00360310900031180a8560303211802c0c510124800105e9890700f10540c00c03030100ea2301c900708000c0100000740b00190158440225401040c103021b4070380181c1201c50300c05030015028828910b1680d01e50040700742c4100280b98443d22458140390a51400400f0790103c03045a10410502c442c0d1002c20041400c603d510b41002058150010640f6140c4003c0070212005290082256101b522011442c0c040c08442258084860749038082044035034822000c41c103542c4041c213030007000110744403a04403c1c0b01018049035980b15680b8804541540c5088400344126551070890100714075103403061641048805c0241c034141440000203560301c20090040b58144654440020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 77400631 1250 77399381 77399389
    0x60402040f14010b0705010e1507030207060603022211070201170403020c0603010e040c060509011d01090f09021e040303080a0504080d0c020a050d0228050a06060609060905010f0f0e 80
    0x190a81c04408030b9081d1982d450300f05800c10303002000201c60750b50a21003404c80c0820002085030284d041c00504e0807280e00c41820583c029030101c0d800715480c9407241d10010150b45e604c40500000d129020221607151500c106d44070445100560850401c041407100e60b0250f40d01241c500746c035110700b81e4410190740303440c14160725080000c2c501d603602c15000000404c0351100c10a40d6030007903115030042c240716174448e0300036140380c041c0c0c3d01550f00143c3c102c9105c081c3d00c0c200003c803101d0850181409410305840d00401c011903002c98110010654000840300307000a42400d120586051100c441400e050459400910081000e8402d4000c00c2d201d80100301408101c004071149544440810003165040c0d11000e9103481413100c0c15241406901c00c0002450300126884060b00059180c0c1a002126002030f0103804400c480107480c10300c110400e020002d4014400c070070260403d5102c07403420b6440d012000b000284140c11690400004d800002000c0b5040000101c440302c0d541811404010808081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 77401881 1250 77400631 77400641
    0x103110c070305100b060405130203100e0a02070c0515040b0307020f0d1e03050f0612030f04030302070509130308010905090109050601060503070909090b0c130305060108030a20060402040f 83
    0x81a03607405500700010800800040040c031001141c201440f02d4a068010840640128440c2907045030101120303107188592603008550081c0c40b050b0a1801c2511605482c991000c00ca44013294140d0000e4140d0902c128000440028103089400c200040320500d0a21080e00440c8280d4040c40303004008551b0307580c024000c91445c01700e40f01c204c6400d581c060702c000301041c0c0031500d40007a036108a030080000724480e000303007480744c0d0040241d0200e40d00d0350010320241603081c4040351150302041c080e4080152030030000704010360090380102180c41c1006e00b00308060202074400d100000c1400800c50009411101e95811903408010028040d554003d20501402e01080010101e01070007001142640d000000707907000e0402d594849200d281c4030311100040314000344001d0300c13103c14540010100d05051000b0305a0109440ca0003489954a0f44e50502e4244280c00498070b175000484c40d0340c0e005a0240d03045041ca0004115409004240c2020940301c450250000e03000d16200c0d031481d4a13008181e002 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 77403131 1250 77401881 77401897
    0x615010305071b06021803030903070b090d0b0901090519030c0b0714030a0c080c0403030203090f04060513090618021039110904020919090602040306021b0706020c010311 75
    0x80100f82030350301c0c0362280c025800103038110f01d100790341805040301e0b08000041c0e4803960300140040401c00d080c50284041ca4205c199190b600031854940c50f0b001444440d10f0361301418190300007081c112002e180250400450795254461440008400f00102c0d07440f11003802d0407a0020220340040d1105102240c5880458100c501d0104001003400040c500380d034450b206034031203651010010b07200c4045815072449648000b0740140c1c41440781c0029864001100c5041d01001000014815620740200e00d404c0d0341300c2020b032160b1380e40c1c207940e0f014481c042c080c6200c1e800c140c400500c40240308d0780c00140c01003501c1c01c0c514104003c06c045841d9072048424002e404051180d0b5510b8140c441c45000d400c2012041b01c111b610b040f2485004103030303080910b1180c0c01107900804403011a0f641d0413099003038a400a64090350f89484014480106000388000c1000d0760040b600545d591a00d10f400710400e00040d0031a00241d4840309003000f1250b0300cc600b05d22800c2003440c012807a0604000e03000014003821a03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 77404381 1250 77403131 77403167
    0x60302070f1509060c0509041428020403210e01030902090c0304052a0a0911090607060216060207021c150209120105010f0e160e100c0611030a0b03061501030507 71
    0x105c0004540d082009020800c0c022902484516207000d00c00c000e01d20242e03042c0c0d00b085007032118680002c504d29820010110800d03001030805a580d01c41c09500101002d00c001422185c40080044651003452891b000c402801d080c07066060682c04500c0b405030044c504450300201001003801c20909200c2554416500030801030441e100440e0b6554141a03040014480c41d0080000241c00c6021b006844140c107803155400e00b0101c4001c107002865100351003c5031600c0c2c2c204042e0400381c0b903454420915502a020046e03d6610601c18000c0e002080c2c00003d0b00503905000c40070004959082103000d150760040090b807203010034008500c294217a4030188403654200340000c95802004088042103035210202c640c100c1e2103061080950740e9641040a0004080038070108007400d210802c0c0c0c021030020314220806a1054030f40200312483c0b03240f50300e42c0c2103001091140420300341c0242000d0701021406040c8a090040340d11700b0051410b519a13061640f80e4000506281c020081c0c07603290501d2007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 77405631 1250 77404381 77404391
    0x40e010611060105011d0301240807061407020f0303070c0807170c0a05040b0d15020a023a1103180109090b0108011208040b12061801082a210601060302070f150906 72
    0x49e20503140c1d2005000c0d150b914030400300001665403040c0520344a23034a01030007007890300f803464091001380181131072450380520041092200040001141c2c0c40208501e0300504030701804c000e0b90b15120960300b12081c14580c03000c000345810780c0d202941d000885004607400207442c0882c00104e8841128000c018000301a00c0e189045601c0709600141038404240c2d00b0382c1e10012030100e000142c1c10700b1200001c903043d140494020052402d0360544100c240d24140203082120121045186910400d00514070065468484695580042403e0050602c4150601c048030120000a00d11001445102903016211441405008000c03045030050400403000b40c1e070320009207652840c60760058410302e003e5880f002c1c00d490381e89160104035040c1c2d803040340500305902c191074040d100310010740400055140031101c03003203031540e075154030341d0f070184400310224050030021100314206141640102c0c240b41c0108000d0000429200c500b4010f10b80c40007007100340b508500011001080740c00300007000c0d00d10342 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 77406881 1250 77405631 77405681
    0x6051203070501061205030a0e0414040f0b0106030606021f110a02160b0304081b0129090c090609011107090f050108160303020d0e0d0503040e010611060105011d0301 73
    0x100c0100002405100240001d0355281c1c400002609030210280190304140b203030410b064800c5407400c2c48000010400f1401c07041c800c185203910001591308645c0c1c40522031141042012144640d0b004221508042010500e4403001940f40d450801540050100b03644600e0582000c07035000901380d02082124607201c402d2a0300c007035076a1902d0300441640f4804440c000400483c01e00440344142c0d07206e4441d03401c14404034180f45291000080440c0295201e01820308140c0141c00c83d0001901d8206407040e040604006010309440d025000700701c02c6d2800c00200c6015100d0702c0460307040c29002e1030222203480b90015150306000041d00500c003028241140244803d2285d0009416a140002510601d100304109044001c20512005000da00f184100721500341c01080e11155050010b0b2420b0714020a0795180c41c2545e00c6500400e405074403580052103c02e80c050b500c110007a100c40010016541414000780c601003402c407a518600041021841160703c080d080202c0c0500c281300003060001003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 77408131 1250 77406881 77406883
    0x14040b030c03010503060a0903090e04021807020615040603110d020d05060108060411060c06010501081f031a06120606040f020c03070609060c0201110412030c02150408060105180f0901060512 84
    0xb0070b04c00e40e84a8410200490078030700c1c691280300c1d43c096061b22414085807400c007100050550090050340d10107000344150b01520140c80c0c51600c1031840340c0c05440d039440c1a12400c0e8144505528a80c01207141800510010b180004d00110310307101220350845001f0a07100103000e0600241000f005c038080d0318000521040000f8029024500c40c001510100301d00390240602401100596540c990000c001003155500840c0d04a4200b00104821101c3c05000e0340307000c0301b20700b16610880e071809903041e100315141114000244c000c58101e0f050292001000312542d074898000c8c000718401c0d590b418040303128400903812a1044c03018007054035141d0040b82443c90092003040c1c0c0c192001410030a004c2e4031148188681030a00c803d46020300d0401c0c0c00c1810b41e030000002c490741101808401c00d05a0007503500c070030b1200c0b1000340907100c003640c5500780700b04a03040c81c0381030380140d02a008400400491103100403e065201c001c6515800303c982e5540030103409495140c1c03101da00844076403804004250 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 77409381 1250 77408131 77408137
    0xf050705030606150d0f0e0d0e0405130c09021309060b03040b09070506070f0206090604030b04110319080c01060b0d1a0f03070501050703050403150204090f0506010203090114040b030c 81
    0x1044003641c80300e588030000c0c08210460640c1501464134100440303014024242c0c0040400410380c4c0000070110304103101c503071500c1100000d00011034490200d0260a26050264981c41510715000341031a080c60398644085907840e02560345400e40200340500240000c0c82c2c698020030040800780b2800f42c2e20300707002010340d1047d60103460424120340011070030342c40068084202e80c6e02400c0c051030800d460726890f00c1011f0021b03040b42c2c0101d003001190541e580b008094801f0310b00881000d0101c0c1084c1c40d08401698500340302c10f02903000314809030482d02905c03d0407403006d81c0048000303544440b803010309801032220743c00c54070500708042944401240a82e22402444400c1c0b0b07114802641e0302d00030880501d16503504658554041103007030240d544120f025080c4c580c800e00b0300b82e0515841380e03640d52002c0380d10078019001503400b0804001d41241800795540200c05660200002d08080700000e49034860b4424050600160b104030011200e80c180441d00100a251005601e03410200c4003403840da4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 77410631 1250 77409381 77409389
    0x1a01051c090b070906170f070c0303020d0509070f060305102303010f0c12060b030406020f04121506050d170a05040305011410050603010b07030e0f0402070b09010501140a0902030402030a0f0507 85
    0x80c00306c00c40710421944046905005455159015905581c0c0e40340846428056100c11801c15070244184104151a400340e140640c80000c0501022030a02e141c0303510740003035030340500d0406003410103001500c000c00030200c041ea6880c44040c010b40801c0c2c40702200300c60044001e181c2640c40d000c5a0b0500c80c4050380030b140c0180782d84d43c43c1c10104014200001c1581c900b03002c0c5400d2118200701240005d4855402005001d03540340855041c50364500d4019411040d03c0001d45001d0320302210400500094407c20024140481e03241d01001840e803200d14500c0001304079001030000000c1c1911450f401242900d000f180d00c2002480151810105200b4164003135035481041d904a4a001c50a40340c54005d481c141d5041c640300900388445034070200e559442001500d5080340c003a020391090790b00c4600050510a0007070b4041465400c151040508440d0141e016071100b030112550540c05035140d5130310b00110307100c0100141e100c1e01c8500002e810a0002c0d4030003403411a40107440000c009000c10740108030703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 77411881 1250 77410631 77410637
    0x714030a0f14091615080a0903181410030c1b020a0504111201050108040305071101030902120102031f1a070512070c0f0b030412030e0f010e010f1a01051c090b070906 73
    0x304c1c3d44c50800c001c00d0290440d400c00810201000a03429401c0d41d03121091144c0a45008a07500d01e80107070340300719078410b9004419000c2409200c48541c2c14860540102104145002c01c181406480010405540040c12002001c40d003204107080d90341d0464008080c2000510803c003540a90546c20340b55400a0300c564001c94292000007103640c0662604d41c4102e416442e035510302011565600c1c4068034540540d414199101032120144e100c16220200c411850400140d40f420960003a130191192400030f0505055068800e005034480820358128076216140d51503203880c060700e051403d1440080000c0d11050740810b0320014841440c280000300e079840c848425619440c3e446594243c1700c01ca1303020349070000d00d07094801c14902c00d034000c1007640b901d4010340b850001400e083c5825122440c41604a130303912000e25030880901c2d4801c000c1c0281a041c80705484400341030000e05a402166001105006480a4920001001e420041740c0030b5000f40d210045281000014204014900400d400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 77413131 1250 77411881 77411923
    0x7091109120a03090b030a020705030f0904051003080d020a0e060a030204030c0806071e020f010c02060a1d151b07120306120209061011060f0f0714030a0f1409 70
    0x580c0030041045400b8540680e50024a5403c1900b928007590019050107541c1d5030030440003021500074005429160041d000707071992024100100429100041c0c4014100c016201080000501240440d51001e84000c0d000d81c82d1201c1150640b100e003001e106030740c1c00060001d00100030300e5041d0b00500c2130b203108907220070700b80d0703240c001280d55440f003100d484001c18a0805045426141ca00100d0b88075000303441203e404000514103d070070f50308400fa07080007607807002003801101c4003a8000c0ca05001c0c02001c0080c0100e103529200f642e5141d01d0b11346240d035a9070741404620041c6100d4010307482852240307601036441d40141b13009040007220781d42041c00070f40703000c0d000f140002000b40d0f10002c43d0780042000016484038010810007010b0700c07401c1e500b4024400300d14506024180712642c0720342c0c0d070840401d030103103000380c0240604240207141404202000013402c01078101081034a130040c111003400514424655004001000020713640c44170f0404440411070000800150103000070366108000d40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 77414381 1250 77413131 77413159
    0x80c04060b130303030b150d0509010f0b030c040f1d070906050603090c281707061803110a120b070f11150c04030b0c04060e0604050f1207091109 64
    0x1030b008a868901031a0321080701080440d10a400c00e07521000700401460703040010b107990200aa105202d04480292520104402070b14207208443d40303100c540c0d0040c04001000e20000703444004400c6034070310451741c03460340d480e03444901e42c03211300390065482c2c043c0443d01a10010607952200c078400d04c80b540341498030200d2241023203000e03640503403441c40003880050454000c100ca040d180300d01c02d00d403150040941228501060705400010000c90310306505d010b0341c5468907401d003012600150240040b420b006c2d04101c80101151003102d82004244486580560000d1140700c2c0e01e5014030401100508040c1c2806510066240035000700d89554031168081036058803001d00c2d45094041c00c3d00b000e4428808098003401143e803001d00245941d25050b203c0d80d4020b400d1406513200309250700c01040501a083d00f0034044c20080f48210b40c000d091030714001c0018604001620698095000203421423101d80b8100440c10140020110038480700d01d4500c80561a0b402400c2d60600c21015492840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 77415631 1250 77414381 77414399
    0x7031a07021617210706050a02040e061c0203030304210e030d120e03040801020307020d090b030a02210108010c0906030501080d03230c04181a010e0a050a080c0406 72
    0x10088042910b0501c0006142445031254440c0452041d03440e4000e201078000300d04c2e50040d60540c0d0301000f5100d40d80310f114504082d81183c41c0108101e030801c0c4108014031a280005101d968882d03001c69421940018480e10003102240e5124002d4141c030005c824003003089a07a20417184e440c084202650074420110b10100c52980c51044103e0b096040200d452900c6032290301241441c1500540c003040819483d004646540d006034050140303654040248030480c0c0d418000080000558907215104071300781807401d081e41c1320203045441c115600103113408500c44402004107054100300031002d000e41c1e490f07100c00e01030119040f2510000f0410840840c00364000c1c42294142d90b2a04010306481710881d60903002049004503800e41c41020b80c4a03190182007030b02c3e01038851040c880146407110316251034140402407040300c488043c1c1c00c10071b1040300e4100300a498400603600f480c1a09144000360085041d10303481d5000941c00540441001c01ca42e4000603080d0790000c02950304000655541d4959 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 77416881 1250 77415631 77415643
    0xc0806010c0305030601180315050f090d0509011209060b2d040c0e0a0b09040c0302070b060d0c090905010207110d030207120203100c081906050105040b0c0f07031a0702 74
    0x52408078054a0750342010910030800382d43d20000c1810f00041748952000768449040041c0c1c01111420882000318038000068001c168000b5192400002a802c189050f15110041c94000c00c0c10814041421030281c0e20400e52100a11b07540542000b682000b0f0134034501502c941c0e441d007401010000d40b41d80c081d26616090501404c983d00c3d1400702e02e2003000c00c11010340090001030041000c00c03038602c035065031210003800041c2411041540c0e1030b012601400252066a205802494818010f00000c59500c28003103500a504030b8840ca11a1380c240b400100c000000d4204905c000e10300307800745081000550003000f4142c0281c6400018078400750400c44030644074000100140c104c240200310300d15070110f010101c01d200030b050341c071082030390000402210070b481780e501d0008401d0803e201c1c0d507403e45400244010125032003131151504201c006401486070744039030640300708000380e8070108000600080003500e8861007541c1465949007410600c030041424232462208140010400b01c500000720 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 77418131 1250 77416881 77416891
    0x3020a050c09010612050907030501110d060506030103080d0b12030f0705010b09010803090d0312181109010b031306060e0112211706040e070303021c0806030703021507050d0504090c08 81
    0x1005081c070034203809035006e000302a140744014842c0b00c40c0400011000e0207006858441c0301211a160070704800010140d40590744030601414040005001107500f00003219000c2c0b005180111b406100c081c046928085800d50101030b0380000f042000085c21800000c111803400f49000b44209492801000030b405428400d01d129603000b0021007115051045149109038000d0905202548503101500d0a1340d07400303c041c1d940481d030f41400b8000c00210b510300036200da80640b00030819605051b5003560500c000f40100482111481d1014200415500f041018141e40c052aa0855a440400200c21440c0241c1211441c01c8202d080e00b041d038140c04546a108280e603a800c1a03040076040083c00c8402c0034200315003154035500510151442008040d009521903801809480f1302c05019045a0700001214810448041e044c803c407941c00141c1042587d404641142d504801c0d41d01100040c400e01d60004d08601405003c0000181c216018200320341d80d1190500c240490b0450842d40c1e2502116 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 77419381 1250 77418131 77418137
    0xe0a02090c0c0f03091f0c0b0c0403021017071409060c060f130c090506060d0c0905011d01080609090a120804110a21061e050603011a010212030703020d0903020a050c090106 76
    0x107070010f02c4001b100540000700d904022450300301507150b500c03196070110345810350420001410801c504110f040441c0124103840e10604580e40300240841e182d402a01ca0001c00040e41800410340440100f00d5100305030040c4840e0303462005100c11505c40404843c12140c030001480080d40b84100b248503030055039408000545d003a42000340c0c102c01010094036590f00309a0078007480281083c50b00c15a404c01030140c070f68001c10303803406000400c04000615600d1480b40049010000341e40c01242d45600710004a0321400241d4135658210b190400d4500050500080300c1210180240c005401da07018a0141c0c001c0e03241e00481c4420b00101c40030078403034060580b4452210038250025014004452407080e44042882e8200b0030b01c003200c0101c801d56584944e5507502c18840103284c2481905001100c0308000e0035010128000070351502c0038003074104005100000018940341c86981254003040511004200c4103c80b070800035a07481c00d00104071210b10407442954524034000c10203d0490700556 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 77420631 1250 77419381 77419399
    0xc0607020a06050d06091a0301111813020f19090b040e060d020d02030321060a140904050120070308090105010b030c0903070302090f1b07150e0a02090c0c0f0309 71
    0x10021501c0368040b602480000381d0340c1e40085280662402a001c0840d0401c2d6801c090349481f00401d402c48032803090000c6220010040b2100f034100881c03c40400c060125600300c0e2000f0301020f034074041c2c858086502030131103000840017010040c043c0702c2580200c180c0d40d4610420386444180c0d14912072400b038003203034021410004035035103002e00c101301025101800701ca40709074256010078a190017919014810440d1020880c10b00400204850b611038012101000744c207141c401c0680a034501c05100c030b8020f100b10800141400720035002110310f200e40d034484080c09003122103039450582008008a0015510401141c10f071041405282c1c10303103039240403091842d01c4000740d0f6a05540803161042e00340c0500d00001000da076403089000d11480346407207504950300c1d22a09040d003c0d45203041b03030701a02100f40700030300c0031490a80c41f0301c0c00301c4000740001038080e01851006e407500c0c4400300e0007544801c0c002c00300302e0403075106009088051000341c110b80c2c40f0510081020f131a4001c049078241c100c0c48007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 77421881 1250 77420631 77420639
    0x70f020c031908160c060323060603070c08070507050103050601110606010f02010603050304240203070c12060207080c0d0e01020106080c0402031b0d0c08060109061205060a15030506030c0607020a 86
    0x40a901d641c51142c90421301d440d01501c2d9280d0250140007080e02c4505240c0420010b20341c160241004c80302c010f680c0d4840c2501c02921135221004060112805a08040002540c0900911921701ca068101030b60a454440c41d00d05984d0b605107a009803400641054081112540030b24120031500a04030094441942c0e29001110302650040c0280115904c0d660300201142c400c1c00100b02802c00881c01c1034603c448030001580c0c50140d0f11805045500030060100031030501c11058045d20000020b1080c00b0b40d040c200040a070007502805440d00b0000195001d0700d03100003a07002a141015282c3c40740701940b0800681c00c80380d1500c207070125904000032583c552300e41503004580c041508080000d1182e601d10f0201030302c0d0030507801c1d0142650369001c201c03081c0c0e8000c440242d2001b0240303095050581040b0008014458030020429040d866030080303442a41c65100907000341403260240c43d456030001c035008029010680304280079000d4000303403060504050048800854018004c944000c1c64 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 77423131 1250 77421881 77421913
    0x180506030a0224070b01050f0a030506010e060402040b04140f030706020a0b09070e04051f021602061c1517010203010510050a030603020d0308040302010c020d0e060a050d09050303070f020c03 84
    0x495801a020f583c1905035420041c45000103488070f24012500704640d07604110602c804280840e54144c402c581800c000c200095001a441c0e0540c2c040f8282c40000d5215100860040d02458100340c05021010070b0101d15900d4180c450b040c01d8108407488030306001340b4014951641e40318007441c0c00582001d60140b002c54510041e10760003150a2003101d07011983c40c203000e40840002c5e04c1c1203a01e070700304010111644500388103642036000c003400114604242510314910f1041c5090700240a00c1c00460910004094030803081414242e0010a014004600140d6803045629001d01104044c0201861841d12014800c4e00d060303e00c0680003681c5460a442c041d11190002148182050b84032440400161243c20329409554425103035104141403924001c0d0030750ba50071280e078046502c03030780c603042807594000c14082000b1801d9a40d290f541d00034090440e100d2003200c071046040c500301103100307080090001c002c0d0700c511070f966a10b221461000c10100c3c0c48045803540c0c0c980c5544450000449485 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 77424381 1250 77423131 77423149
    0x10b100503011a0f1201080d020d0c020f010201140a0f0c03150608040203030d0c120b09070c0311010b1504030c08060c120a02040909030c0519030504140105070c0f180506030a02 78
    0x8200f180303041c01d201d205403030425406000301081c407074803190040084440400c61070a40344034500241c001d5022146006004100d10403003e842a800380c0c0003104181d0007948440303480600e04000d6034261400f0290304005c0d020f03956840c3c03099460300c1780c4114118401e105410b009403840f040002d29502e030803012210000c010704160703407602040100e1104038200e4420711005802a85803143c04144150808080724890b0300494010300000d420095800c0d80801c00c0007007144c2c1410706440300e00c20144040d00420701e40c0000e54020603110548444541c80001500450f0b2255001d907444e60b480ba081592240390030380b44803c0c02c96040c02416180d41d20840c2e11948034500980040c00d06558007000000d4031402c120030340c08607100000340000d1080038040306221640a11081036034108994009000344518420b600f02078035500041221f6031b10450071100c0c00d54102449060540e224442c050b05d20078035126050b00201c4000440210207801d0140f42d210315402006480d0a403815028060488 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 77425631 1250 77424381 77424419
    0x4110f040e011a04020a1202031803070b040201030605090c09010f050d06060503240d0807060908121906080c010c0215040b04060306090603021003090507090e03090306010b0c0604120207050d06020a02010b10050301 94
    0x2cac0c45415046020342e070800103030049034014420484182020f00016080395150f07040b00d4000d888001c1001100302d44c40c812122254002c1c030b1b0036075180c1d11f00142241c6038007a2070714003200c2e036043c05130005202d07502001450060800040381c3c0c604495000504004a002140c03d9800c1400005210042600c2c1d40c007400941e8044d0001003034a113501d41e103083c280d520646001d000002110140141580302080e00f03e00602241c0d8100241410949104d50b2904040400790401284207041021500c6520000150803640038120f601c9a440b6003032440c1d15041030080000007032511400041c05551401441c0803242c01801c10118880300400071070107807800341d0044e0346601c034403100003d035a64a407041e49101d0551001a5490383d0001080500b0181c06038002c1c4420307101031061a85400002ca200340d00594400c0440091145843c0141d0a2180c240e02981c1d02000c15900e003000e1290680050a0714140c3d580204541740c4c4103410852081120140040022414401480522080d01c0f5800c100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 77426881 1250 77425631 77425651
    0xe07050f04090f020c0d032c0a060507030e190308011503140711070e060a090c200a020906010c0c0b090d1403041d0f04110f040e011a04020a120203 65
    0xc10707241d0001c2d10541d5050240c0320061980020710650000060240300c40d03803c028034080c0b01c4c1c207021444041e03070307240811081c06048a51224000a014040000703901440c0e00210510007407404003030140041848000400160192080001d031843c052a103000c8140d926490340921642410304030841ca000317030302c0381005040d580e6000e50070900c3c001045601c90600c1c0c0c1e031101c07100d030000880141400d000d6441001030890060502c40143c3e1200e000c0d50079600f034090700140b80c828080301110305c0c0c00b4280c0c80e4a00d140024071400c5569201042031a541c5009417982a96506d9050044903550041d502c042c10480c0c51550908c030701c1000c58002c0440c52030040c2001d000d161551100b042c1100c106480150640c800541000001d40c180403c581c0070107105101c458515088089a0b001c207002031004001c20b401ba0008030403a9a0380342004a10440540100000c650342100c00303008240700e650945691800c1848604207182c6402160540081692417045e0a420812544082d400c00792510903a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 77428131 1250 77426881 77426887
    0x110103020d1803110102090102061f0509010314070501080606030609070207211104060b1c150b07022b0609050c100210050a09031407060b03030c0109110a0e07050f 72
    0x4900c140260b1494800d50400352910505030300d00030b0415080307009102c0051340140030038001030b0780116100354408111501599040158103280d81e40b2461a081642d21007070120010051260340b00364542407a1810044030400c80e104c800569200500b00d821030b5100384200001401030800c41040b44d0031a00c2c0340121804591950080c0c070000404104003d0440c4000f80500300b4010340004c1c0002c0f88500391000c125882c02c09081b14014810144280325462082550805900c0554010700c81a200441508040e5803140190b2100b68001c1405038400e003860500c5031035130440c04212004068080280003000f105035a150400b4008a50007076500b8015120130140c584c54050911101140d540c1c0070300303240310040001e0f004843d000b500b0440050b140ca910240081d402c0011200381e10b8640f01403c2c0c90341841d180920151020014554041c00041001c6820301d40c150000c040d414499500d09a5596100c0103100008517640702e200303650800c1d0070104000178011001071a1035001c035000549 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 77429381 1250 77428131 77428147
    0x1180603120e09010909030e10090801110c0c040510050d03020307020d030e030d020601050108040305160215270a03020d03020321041505040c14010507060f0c03052211010302 77
    0x41021000c803003100490600000742d50319107003840c40c490240441100801054003551001018512a6102d4a025107818603086070540d004640103c010510000240000d03070f06e9400e074032541d8004800c0d040f914030a03100c001016103094010340d440307941d403800043c029a281008002c40b4011840c03064096020411200c00507855000316080c4003802901c403140d5603483c3c0c00616217807241082d010001c540010005000036a4000c5046401c0703a05403a24503103542c0c0399022541403040704203000b940b042d920048100480c2c0080082c003c89059410303038500c1d101c0341c441c0c4214502e20410700e40d44d01810440091005180600315025020b005c0e10480303080401c03110b03000c40303110310007041d1a040e000070804010411a242d0152010000c1c1032806016609056445412410b0b0602a41e14400c0213078603a029143d2088040e00d060a0b0020002e2188409900c8418002c020045960780024241400111203072070b181030702d2200041240f07201c1d20700d14050708c50744001100400401e0400d50200840c4c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 77430631 1250 77429381 77429393
    0x81b010e19091d030a0503070804021c030908011b02070b0d02040b0309070302030c01050702010507030e01180605040f05120303070507020d0b090606030c040507091e080f100609090b01180603 84
    0x10700640016680000c844141c0c5034a081c49040741c41a00c0729641c01002128101c6600006603a0881614101440e043d2a5840061800d01e40703d140e104040c822000f00806140c1d114000320201e4003900020032011f00504040c5904aa180005001581c0224810480510b501c0f00400f0072560101c0c0050926440e40c3c070707039034540e4030503180d04899500001081c000c1d85010300c801d0030010b0090922901e816074a82c000b8209000d080310140070300144140702001c5034014020120780081c09442144890b03103031000900306030058007954400c40300c056400725071410301c010784540c2407030070380000c50951366060004c407030350b03401694100c0c1c00040c0c0070181c20014211011050007030311490702034402842d01100741441e00ba81c50034002d01c103609200c10b00103180d422000d900c054641c0211540001c40400358440241e4219502c411418490060100d2103407030f000c507e032040c84150b41c0052103102d0750340e402c01e0700b50740d01500c1c082d22080c0c0800c0100300c3e00322981c29041041da540c2401283e810b640762148 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 77431881 1250 77430631 77430679
    0x9010b0405070507050f060621120a02010903110c010203030103170408030a090501121a0409021c1101170c09010503071701141c0b0a020a121503020109081b010e 71
    0x2c1c5010410100c1d6040c10094240705049600e054480105114034008001034900c404d81a4140d20881c242e400c0140d50550a000541c005e002050616580d0041440001c0c000c0040150070340000320180d150003500301004c5814041d13400c0c164001d509590941e1668200c6120349842007504007020400000c410744244090480da0040703403070b842c10342ca19040c009851010000c41c100f00780c5181100d800208801400a00f01f841815100000c90321114800300c0c80b0401c5034816031640c55040c80c1400e0801c94a001080e84480c1c0aa9488005112244141c4480035060b41e400d010300c001070040b007409503c20b00c0603540c4101c0c0c81c50000100c61a80340410000c000a03003104a01c0144500e0b851014107041180e102000019000a45000c0301503c0305107100102501510b11141c00040e182e142e94440d11040c400c0d03011380101044002060380303c5500420442c031089000c2040c0f8800092811307000700740071280030300d20854880509180d10044030042a1607560b07551041d002c0e100404000c08042c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 77433131 1250 77431881 77431891
    0x6012102190806010c08250f060c020a0c0909030c0b070e010201061508060618030706080405010b010302070218102102041505101b080d090b010503160e09010b0405 72
    0x40181d654060031215050069450860001d01044409000c0140d900190724500350341c01000050310b80691f9240c801c03006420440715441e6250440349501844008010900054400c0408015002001d501682c03180301c0d00710050807104021008110520301c6410000495210340381604005400b03503140e800814060b00c00400003800322041402c1560240700b154040c051501c40c2005143c04c00c4001084040c0080001c2d00903480030840d14030403000c4074045104040010b00307850341c1c242c80c0e1310f0007420744100b2070b4144c44030740c241001c41209501910031150340c81d801819842e80e0741c1004180715001d46015202c0046202d00000020f1001340a4800d619407440210800145424500401c000d484051a60944d071300c1003410704100e1551100d503003290003101c07410922a200012100c81440744600709015156000005e024074980b00c0c207602105c2c0191054030207400350790329441419a074003031100604501070821074092001c0100c4145070343c0e04c400d007a8004101e800e0080d0115083d50b1080d10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 77434381 1250 77433131 77433197
    0x3070302030609060a051011010906021207121a01050702011106011d1027090b010306020403060f0b03100e1c090501080f0702030a0e0418200a05090406050601 70
    0x3041c007002c0e207410903029800004c01c4500f1213043e030902c40054414140001810300b84101c0041200082d5029003001c256950030000464a4411009620801060845803030000031149101c103140300041e88a8101810120300d6080342c11b41c500c03c0155615030040400381d040c000c8190713400c102050200040c034064244c1849049419412030a9080e051348041c04130701c5200039480d8180320441030b6502d06103552400d02903ca03089038200d00140024035500d03078040c1c80761404800110501c529600200210b9204003c10885040c05c025140e0469202c0e450103036158000300180600051aa0459525042142d081d01c001110714105019005290280100451600502007000c0e6030841c0c0e0f100d034001e40c4000b400d4958500060025107a11445c21440280040c082800042c0d8440b0341c80700f00c000b548a06441c6404081d41042e0307545400c0c400180041c8500000e4404060400581c0c81d4122080a0403003007607601c8599580000c0c1070f0041020f03041003c00e9015054110038550300340c1c034180c0303000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 77435631 1250 77434381 77434387
    0x40b0f0c0f07061107151a0402070807030c020d050f010209090112020d030e061b01060303030c05030108070b160b10050a0614090906060f0307030905070603050112140c0d030504080c01020a0b1308090603070302 92
    0x1000b00300712a40c0701f40c8988103910511003040450041011900c416a152030108480030b0306100045c420300d0981c0018005119210681710306036015802408410421680d00302c8980c0d0783c2c03114052909220380d00a422400c000c901c500081e010b040413408402004241c5420000343c41c442b40c40907003c1c1d13500b1140d01ea450320b404200381501486141d01e400014074002d031540d81400b00701c036980d600501c1068040074001980c954401944040d195105134020151802070415804c807450780310050150303910924600c400016043d004ea441c003a103080012800c1814244845c0400036000c45c010500c5410142c02c22011207103013440030080d0300c606000e4a000a00340c43c0380c1081c0c1c0c58850309070056011b140c80d0400501003500444400211b03954031844c000c0040404d060042e0031302050100060b0014662513800701055080009082900e034140c4c129100502c503000126541c211518014000c41c9080000c1410b050744a00c080705100e001e10302c5140782844020100340158021500c00700041c2e808 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 77436881 1250 77435631 77435651
    0x6090f0b100903020a0303050304030c0804090e0f0303070f110c04090807151404060b04090501060b090102011103010506040b16050a0818010e03030f070c0806040b0f0c0f0706110715 80
    0x40012149680c895242c10a0781a066a0226405107030f24000a024803a01000241c1014822940d5018255100d282c4585036a503658429000e0320000800d43c8040c0150102c1410110380041568801c2c1007550b181e0000f11401c8500f03413040b030440c410150b00c2d03000320085e054543c1c4450040a8041e446544900c1d50303807900341800440c1c1081302601c004040d050042d2408050880a5059002a0440350005c2c01000001c0042c0c000c1070400d00080403035090880008e92180311001802c0c0e0b445007a0004d01c114207811480000a220900459901603018081845250b04c01c5001d007002e11490100c5c03a400c1e40c2c1d10307140e0f1480e0003e9114206c6a03050009004c151041d2804000c4071205400c1c00c2c1640e060501c200000c1d00c034058050309250b5502e0200d410000d110b80601d80000811500060f1003882c1842d00340382201910444014000512000124001c001d10208840b5000003c0d6032282c18010503076500c40c0540420301042225034411f02c03801c404204004084100c42c040c0d502d00084003807030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 77438131 1250 77436881 77436889
    0x1203010303022d0a0204020901030e06040303050106030b0303030f070807140c01020417010203070905040e1009050307031704080706020d1d0705030d030603020a0b030c040b0a02060702070e0415050a06090f0b 91
    0xc007040920303e0380d6a80e903540d00d507201d0000340207618590440380580c9510040004a006114031a80302c3e00c140308e20030070322003490b406600041c10b03900380350360902c084542c1906040d81c074803007a54010103081c500000101c009105440c85900440f03145030811a420b00300d0a1031500f500802c9810390540d50016007004417031070701418000208002d800a500354a449040070381085041c3c40780600907078a40c90f820003000270134010300a280c24003840401c9901a1b6003480781d520380003400100c0c0401d5010256211030300b103940c0d4040c4180e0348002d045152503034903540c140103500700d46c03507062000e0f848800040040ca209184400315680b0200241581031030281007520300000044082c0915240010030300158071440c2e03105059a103040d109130307501d403514200c0c81d5a0f846a50f202c3c0c240001e012601706511540403410f14060201c2e80d0031219082e032109912119403005840050084d220f5800401007500507401071540f00551540024503551754001840a48010142c804000740d660040d50b51b041c50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 77439381 1250 77438131 77438173
    0x3050706080f0103031e36120b0a11091f030501064b110705010e011b020a0e0106090e0a0c090e0c210103110d051b03120301030302 58
    0x60b000340c550034039407454070050074031003054820440c0c510301c0b844089441405114501035402d0145e0500789a0400c1100080b0648646a0100801c0301602d10008100410b0300c0c0b0141c0140c0c2024814189840c0c07149110300800c40c00301d00c220401d009129041c19555a101c8e400344054641d040a60403d0b10310742c0040403140142c11050602407004140001d4440107490051320502009005201d0504034130055014600300c05107290014400d0603e00b44654030141458070002c5a00c00c07500300548880c0155040c0b02c0032003a5500050082045181042c1d540420340b400078000341c4940c0384103171100c00c5401c18038000d8000b070700800c0c400c1c0010041003005040d4213901c00501a000c001d065890500141011444d1151001c041035000c08509180b01c402c007282c2103800d070144180912401100060000b0909120540c2e5020b0360751081c035200e040152408a0b00d81c0e100d40a08651005003101050420941148513018462011600fa010200400a44c042e500a400401c01d600c2917030300340d0700100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 77440631 1250 77439381 77439391
    0x60a0f2606010308071a091903090b04060e130e0a08160624080c0307060c051f0917120a0216060504080309010b0102150c030c0c030711090c07050307110301090203070305070608 78
    0x202c1c4420400c004040c0114010007400c1c22340045041d2403c440c1401c50b12802560800d41100000040000301a1381102085030000710a5511a0307078091810400300031517030500c0303413448c6a4002040c4d04001034510b900626100e401d180c004140b031616512418101d03140c0c0a05070144540c9500781c2c1c0d20306110048540000c0c29004010b1000d00708090212761581d80b40d224980030320080c02e140c0d4082000500080c2e000d900c0c8d00c04040c4c0000c0381d804011b0042c0c0307211082a81d240b4107402d0001908007038001140e26424042c0041c21141e11503005802c0254040c07002c180018040316071100000d80e103801a24081d40c000c2030210344034100901307040d007112480b220b6141994003403501100c1c41003004251581c8408075040c01c83d1242e84070b44824301c00d0b02c00d400c007241040c0030000e1180c04106103130660111401c010784504202c0d40d1030f01760303010240c03080d008086c2249d4028040a000a040d292541c1040390018001040c0608194080f034074000f9a904121800d400841d0140065540036076103e0f441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 77441881 1250 77440631 77440673
    0xc06030501050d0201140904140c040501090b040806180c030a030302040504050604020316030b0109151e0201060b0f070203160305100e01050402010e010c1106180108060a0f260601030807 82
    0xf4a040c1e80041c20418076880c140d1419440401d00d4000b0307a440ba84000c600803543c44104080d0700e40150b410109502c203000b06400b04650714000b0894084080076a0250f4900070000c0203251290f10700381c50203080d03240060a240c4112001c80130580c5040c08401e903202d100e902e0161b1100d0400003004141c0d0002800c5038090f5106000f0410311600070b06100c1c2485044e030400042e0b90400d500126011405508028240404038a52113940c030750011458a103840700b40c00001940d450b01108030b00340c0ba010310510b92240c0c0180300154088001b01e00401000e88000c0407a025084600d90501d00d9044d1035205840c103402841884504c56294020f4804001ca52002000289426400070b03007c18400003110381041181c4c1c407901e0410654034107000a401c1c3c0101501e07221180b14640c40440342e88020110f00082981c800b040b12801c226907400d094421180b4008152030405001100e840300e40600740e0007440100746d552582ca8002d01010703001c1c5000765000d0742d480b810340c10070b003110181d0400c02d4030078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 77443131 1250 77441881 77441899
    0xf0306040305030408070c080a08091201111c060e0a15060801050d0b04020607140c0406171506010c0c0602070905060f030d033801020606010c030e010503061c0c0603050105 76
    0x1c1d0b009040780d1303200b40d2040708203449510908025a61740c2035034001088500c43e01011809001c43d40780074011483e011101981441044125103090f2803070080141c0d1a00300074010300454064204421200384650100016003541d80c011b40100c094080d145a071001350b4811010710494154042580642010704001105515050109002007000c0c5405403144600c2408901190340b04c000b110f0100380c000e02131250a0240034034650301d13021031481981c030035460034500268140039402c442a5036400e06000d002c4d884a03400c0070103102c440040c8140e041120a811210009907a4500140034120b190300401540e07080c20043d03070413600e001c0c10061103040702c020f2001c15540c00059540203010b061a0110319484c154404c0b10488030701440c4405004501c1a1071380140c1310401d2403894a4009900b2180b080d100d400054a04008211000d0300041c265901d0021650040c0000d40d040b00010300103013a50b00741920341c0c0d0310030f01200c4011030311403c440500700f22156060140f18054042125103600b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 77444381 1250 77443131 77443133
    0xb0c0a080105060d06030b040605010e150d0602030601020703020a080604050c041a0d060b0d05030d0c1e0e0a0902030403030c02060a0213030605060406080f0d02011b0e12010f0e0a020f030604 84
    0x40035805101c2c50384203000000300058070f000b190708901c1c0203543c05a048905410b0514111000d40424094a40b159940500281241d000340900380d0040102500303000c00c2d2410b43c2c42e1a4080e6100920060652180704000001130312030820050040004202500142c10145051401c0030748109102e44900c0c00c04040b01c86040074078080c0940e0040407a00920001401c0c544040a0b090404500d980a4107413031800050080c003000600b810280c0000400130706402d1b07030054410541e84000f42d030959070344061060025000b42040703031050400400f120031055445910a050740d008139011000251a01c0340300c04a560104241070f0070011500040d400c00340400e01a45408059100c042c249a4468010800135110341e030259028120711001da070103a141e0b00546903940d0071030480c000019841c003a559505c00c194400f41b1003500c20780303035200700030303205c2207010064150301c0c000328080311355030f21888400100345a200707188441118101920200320180100f01000c4082c051050280e00500200700c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 77445631 1250 77444381 77444387
    0xf0a150b0f040515030d03060302040b0d0309030f06270b06010f2c0303070c050102061f05010503040302010e010f06051c1e1a0405070e0603030a0c1103031e070b0c0a 73
    0x5041d800140e0380040c040d0350310b10510000d02c1e440e003090b5405005081d110360005605030051404d580c0256000e00c44120b0420a02c20f00c40726880001d800502803900500025860356601410540038200104a00010121040210b80c0036a5856020104a0444030400c900d0550483c0d00140c03d080c80030301007081c1d00700034081c03a403454030f503002d50713400d00c11041c1c801c18003110f01124180001d02242d40301c61301c0c0d140645000989008903405403003060b00048006221240d100d1481001503c0c203004585490010343c3d80360001b40c8101d040d55203402040c2d84a40d024424a081c3c0741c600840451600d10b84000c0c0011a5505581002081d11404038407010810b0303014504030851442251000361021828141d1100891000302c4800300c40790000d003c14000300040213800c2d20681c18024580d0b031520702c1050340d07c0c4a62b590290128564485160100300c1c1300c44810b09042010341920300c1c29840c014800040450024805000c070004140d210a00a22000380c641c024400b400346403419000f28009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 77446881 1250 77445631 77445649
    0x20a06030212060108100e0108030307111902011803060203151f0504120f12080a0510080c011404050301140901050f1017010f0e0109060c020601050a0603050a0e0f0a150b 75
    0x41c60603c04d85c5404180645080d8450388000c2485181c640520758480e684640c81707600648419000601c0c0c030b004c1c5103058401040d05180d40b0070000e005400c0e40c0f8a070340151049009100423002c00340642e000000403403030070b0009510034101c918414204100140820141d5407000040c521a06000b180e0181380a030800211025551a00000882c4004510340b0000c141014003000340107640d0440000f94460f04044440d0156841c0e800074402030392102100a0340305080d2241c4691036200802d11420f9501800845540384083c50303100d894a5160004242510340c1c04030b11181c1d07241280c0800101c01000e10036150004001d0702d444a95040c61044071176540064000c40142644801d25680d04000951211160030b2201c40b0a01a100c105103146009110500064607007900b4140300c86000c51000c1b8996050707440040c00c4840e0582018001c50050200604030315035150b4560b0000d20001c0c0420404115480ca0001403840078942e10b40001a220749101c1c48410900b003542c0880607568410b14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 77448131 1250 77446881 77446891
    0x114090607061e4803020901031b020c0306252d080115080c0d020c0c04050a02091302030c030112110a03051c02030306090103020622060903020a06030212 68
    0x4080340314a03001c1216944007400301c0d000d000c1685450507400c1c2010256040d0804003501801100c202480d0011031136403800c204060700c84680036404100b42c118002e50113090503a03c180740000750301c1c00c01240703480c503070010803040300c00743c2d022a0030244185420040603601c0440c0301e600800ba9900500d03550f0200d01c119016109100700f034401c101120702810640c00e02c002103a070204202000010014054890a0007011008002482000c0c2d4040c01380f0940c50142c541000c0c1075140000742e1120f1002900004411308139030250290041a6a69a00030b10b8040d03103074001e005a459956104000345240c005c2c3c503100718140140204030000c80c903482030301d0454036000e626042d0300e61149410492140304042c4254450340b411408810b000d0300142090380c049251040c03c0d0007041500050380d50b80021506180d201000c6001800141854006800c210920b40084655680c1c55003507150020002e821150000700340c0368003001036182004950f0018480303400e0451030708031070300e00240689000402c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 77449381 1250 77448131 77448143
    0xc092a030509161d090a02030604170403061104050a060f091401030e01020310030302060601020a051903170a0e0705060403030c02011d150702040b1f03110d0612020114090607 77
    0x82180d4014844005641c03c61807201c00d04a856103078a0302c0010300d40880301084284400003c034603403000580000c050b40c0003001801180d03a190307034505104004514040301d046051200100080b110f00822002014003040c107512a0300345418494500c0c61a48400100140031010b140401c1c5c02c060b1900a0301c1100d041c00980d8040d80005070040c5c580941602c07802c0d07100104101c00e4000607200b07101600d00c05c0c3c0c26500b460312a00e00490b03652541c0c80b009031031500041d0003060700055510041d10f40c01d20178100b0304500c4c201151b40c00000142125003d1040d9201d0a030102c011200f4070030100a0a070840301c00e4181307801d50702c009080c0003100400030f0510415407641203106425024035011490000d00c5240400040403000c43c4a4000d550100d0280381092801c540c907292544080e0341684000000c4044000744e007108501408011160403030031081000078810f130341014000c00f0042c0c900c504411040c6661440010215a502d1740a51510142030200d1b8a282e6101c0c4200d414842d0402e07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 77450631 1250 77449381 77449391
    0x3031706010903080f030901060e090c011b0206070c08060f150103020a030e030c0a060b0303030c07020d0c0518010e100f05131404031806050f0a03020c0f06040c092a03 74
    0x24010b03600781050ba0400303401c0d0140410600414401070700214401d0200328004c0c8075050b62180101f440ba6419034026806401400b1600d1b250f522035401940d02c01c0b181c0c0142c20301001180c001c40c1c4503601500058442d02080c036010301400c0c40403c80700341c014081e541e43c20306c24035110500c51821051441d54504264000036040c50b5a40b080c0c120305500d500203010369581e50b01e2401d100344d81e002c00200490b6014101000d5080314030380031007500c0c4030b9003409a01500c1c0401c550308000661180000865808840e4407010416803510f900000d0003a014800c0300e00039505002c03968009000040c200c4080e0280d0314401d000c1481c15038181c00464506442c0e110300e043c15151464060a07488640d0a4032011110410090550040c0c4c0300d0440c2c401190b484501c20348400003220180f056040b881c5940604000d244c000500c00d42c01450000c3c80c0c131050b11305106c0d28143c42030403c1030a0302d040d580c1c24030f20f000900441e1007600c1040c0d5800d601d010001d4595284d603c40410109080310107500b070583d19 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 77451881 1250 77450631 77450641
    0xc02060702030d0f020c061606020f07060c050405011e09030b060301020c0f0115050a06080411040e01050406290109050d050f03070602040612090f0f030e04020d0203090c0901030317 80
    0xa14166840103600a05844401990f45002807842480c0110701c0010311a003000c41c0d015040c2002107603040380104004881007001500d804020390b00503105005213601c2004420089185489001e00c0703040c1e00d035981e5550b00c0c60040010806146820030034584850150b8540c155074100e16a001103e905c01c0c0040d4040c0d44050010340203008003410418a4041e115500d0b1520406600c0003691300144050381d0542d60305e50040c00100c40040c01084042810400400c02051440807441070501c401070001c0b4552100301c0d2800c1c03c0d03500640741210b0302c5460f941140c6080c0b01541100d0329040b4803402100a220714a00028410501c91081d5400394004000c9101400001d21001100011a80440b66203100501d84813009512070f00c03591000410300d040001d81c05441d809180c0c6c156400842c0030314084490f4590468148017031004900f0301c69500325216907912640050080d4856041005842c1d10303101780401e0034019500810b40c4214800c3c801072000982225000c0c0c5540c0e02031880001c00d03610 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 77453131 1250 77451881 77451889
    0x20d03020316050708100509070b0d060b1c050a0e10020310030b070c170a090306020903150c040806090309010807050a17010905090f0105010b09100302040f080706020f030c0d0c02 79
    0x1800415a0101c01c1d4100a1003800300c0016203c045170001d4040700d1220440e44d01d180b08440007501c00b402503400088081081e21405005003803501ca1080340041c14179a900380c082e00c41c1e80284c00c2814400e4604503c07400e410707001d00c9460380c48148003c01744000540f02c01400d4490301c69205c034a406541c08004281d040c107462082034080c55104051001d039080445014ac02c501020780308680d0040301032030b00c0710110b40303000c290b5100c1c10300c1d910b84000c4030f81155100b43c042d400c104c2ca119014450841c0000c484041c3c608803901070382d085c4d55200c0d501c038100501c07075081c0400200340c00050303072040002c0c01c450390b4404800d031b9104009203803d80c1c5880c5041d10845c6c19a00c0e08450300310b9440e442d800491011004d5000500070b40408c41140d48145900403818284d4500b40b0405660074810310610b456070401c1e240001c3d120006140c010304e001d441d405143c10004007500321107140d50249400b8000107030104040c90b0401d03440402503042a03880703603000342d071055018806400c00040603034100840d15 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 77454381 1250 77453131 77453137
    0x6060a03090b07020c030d0504030f170c01060e0702010f02040308030106230a020318030f1e070503070f090b030313120c08060703050406060f05030a061805030a020c0a091107020d030203 82
    0x10388108040b90604103124029610240f01c00034612a014140d120400c00707003d030003100c00b101da00102d1440040401d4580d20040c400b4801001d6000a0400c81c4200c406402c0c4580c401420403085880c80d6424502402421180c540010083c042d1040000b8404900c04c0e1003501d0450309940380140c404030b080e0100c90803002214807540000c800c0850700b6405c40c0d030007102070006a107c20000398010003440d401c0581e00e01c0755143c00a081c0e0007440c04030000060855420040c0a1400b003101c007013580c0c40000c00c0c5814103590280d50b110003103040a20440e4594068500704480840055090041c40501c0b802141d1881c0b052140007107002c00039104210f80300441000410202d400d80f103040c0b40611014002c3d0808030303801c9032031504c0c01c9000f04403040b000d10b5900658002500070144440c5603640c91000f04010050020b441c41c20340725841c0022020801080c485044d0f40c064520300e207060080c460501160b81000c1015428900001c3d95604007009071800d40d034045440071802c0101e0709090781184 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 77455631 1250 77454381 77454383
    0x2403040204151d0c03160e060415090503010e010506130f092406050102120a03020d140106050a080f1501050310051203130e040515040c05100e010f02010c0806060a0309 74
    0x201c424000050503030607211110350203040c44044042c0c2c1d55800784a03030000c0c4002c6402c19070f10310544000b84401b500c1021503d09041002e04250b260031345680d40c142040e40a0706064000403a1002c00740b00505080c040c00d16210945402480035007007050024108000d60070f444a0300c90364600d140702211504e80c004c0b4602c541c000d0401c0c01c1403140449911003082c84c601d0304114007401c0c400d0004943d4030004400c0a4030700c0c6501c0842c01e03c58001c000320040d501102d000c0c0041621600700c0d4240340f07481080580205442c0c1c89442d5141034261029012a000a10006800a4180070028841090020b45044640c01d203401a52569603c203043d060311a1600001d81204e01042c8200c01c008001004007024443c802000380c50307607501c1514000c1000200c400402a81150460b441d00bd204e41100303a0b0032900c80d08071485515100c0300411110540b0008105c00505250b2803402c803541c111038102c1c2e01030001d1000b80200b400c017150181c51f006000e1310b051f01800000400c10010351090344081c0e466 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 77456881 1250 77455631 77455661
    0x130c0b030c041d06030d050f0405031207020112050106020a0627060e0c060313121e0302040302090c0c1e071206060302010924032c0105152403040204 66
    0x40d0030400103020300c5800c10b005504051080c0f018032281c03800090020784c403440d4014001c0c20a024004030842d07540e00034201001b1240e00600001c4ac4569060040c1d00c6101e190f5a10799880780010b0000620a12441d1301052669140c44018004e455002c2940038165420000110710300040000c6480d800392680c400304d40062a070044401001b400703420102820500100b110002e84605c001c100360b520080d41c0900c11812400000800101c0400801e49030b218242800c2012401c10011100c4183c4d107101c2007000030b0341c00034080c011482d0041c0503941040142c12058280350310b0042e080da444109101c10340d00c0d00e013014404503036000200720050140844081d641c495a240c0d00e04400504460b004c00c030b000c6841e420022401102003122084103248262071403028101a844c150000c002520800ca0065491454107141920395601c5103030100980c0000240303441c1030003104040237503904943c0d101c3c41c00c0c0c003108010300f25101c11802c400244060115525116031002030010020101501c201c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 77458131 1250 77456881 77456887
    0x9150c01050708010509091b19030807030804062d0b19030305030907240305130b04050c040f0509030a080c1216090602030909011404090204020d0f1d06130c0b 70
    0xc0b6640c4901014100c82c0f051350909000d403980754001d500c8003000300365466107241100c28141645000229140c4c080400f030600500d081d02d035218403038a07500c1003c003900483c01c88000c0c482044424415004d0611111441800910b081170100420310b042595601c210781e103e01d0901c0403680d40c00c051504900130703194400f8081c1e9130303490080c00e20303001101c071aa15401010400542c0506005140300541200300911410050142c0190004c013000381030100080702d245540310000720b81141c0940100d008000038544600140100020741d03c03516008001c0300d081606220400e10004103580c0072100d0b50414188030340c0d0303039a40440741c1c3c01610110314041d04901d0074030039003900021841882c0c10075542d91004041d26010207036a648a42004a5000003256004000082c462200180d000c100184046070041c9039800050507604603c540b05030701556003074070b02a8030380c807449489002c41c024000300303000020100700a0744441c0c006186035592640d0001902c01c010401034074034090280c0f1418192 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 77459381 1250 77458131 77458141
    0xd02250b180301051f0905010b1903020f04060909150b030a0207110d08070b07020c030a1707150b0418020d0201210e0606011b0512130902160c0e010b09150c0105 71
    0x1c1e4200b540c00710071784518200e280030482000c1800384505139500d0112241c502044500b466001d030414419000c01c06500f4040d000d400160030000f80001d00c0b443d07446480351802c0c2004a4101c0384803040f694151940c0850410020048005403503000c04910001070711503a013401c00c3c864201c220780c0100d40c414811505da81c00c0103220070241c0b4407640a005941040c1c1c0d0343e2001030343d85000041d00d09605510403080726001850641c0a041007420441086041600030b03640e03014180d000d2040000403544035000c00480342440d10a410819804101104c250340d1039801140400c1d0b01c9010280c100048910403201d064001c001442c114080c1050821111051122164640c85c00759401c80c00603403a401c0b0140004030801820183c581c0000180003648104481010720317a00040c1e56490440f0300c1440060110308a10140c052114144166614102c032890000b00035139098018141507415400107010310110314060300c0c40b501042d91050700030301070a04201154054140d4108066003000e003005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 77460631 1250 77459381 77459401
    0x607051602042915270607030914060f0d0207030c021905040507030c05180f03030c0606030708010c080c07080d050109020c010f06060e01200f0d02250b18030105 71
    0x104000074014041145060b400d042003151045542d004205013414400d001d07a402070540464049801c403400200615180400300700c0d113411501c810341c007194244100700807804e0050211f07901000c046138418030f020285140c00809009104480041960106d5640209070158041d284003503001003586d00d0714510481071400300446030103501e0240781070001003551340e4041e000302c18203118031b03407502814981300201d08200018001c48442e4002c107040000303185a101407004020b442d01000c040c0c00c02d89060307000e2601c5d0800d1a400041103070324007a00110351a60028038541c2000e4801d111654410b4141040021390055119983d0052b15110002404442d01c0c0d0040442031034440c02488105013501ca810200e07072081c410030003c07030070444c090707030440d0711400c6181886440c000c51251080d03540c00c11103291403e000d42410307456100b02c0340081d1240d01005040e00002c4da54041079511002203007854290b01e07003449244100301010641d0100c024958050301c944090240007006a40340c504110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 77461881 1250 77460631 77460671
    0x3010b04030c060512040f0c05060309010606090e07021c23030403020105070305010806010b0a032a090f06170a1b0801050a050a05030604080a050d0525030e060705160204 75
    0xb280c82d00b5002d070002410038080d6043d181c03403803505000025241d0b900d440d0401c510304410811070300829a0000030800b0307510038000e14058128035000050240c00c120001e01076079981d4020741c5000340c3c100100311045900041102c2400c00411920025840d005030a840e0011b00300c07103030400010318419819080d140140034500c154000d9000b8880d036200c0b00b20076421a0401e0040d05000e0304400c1c01401005c0901d030050001e08198540001c0d0614100d40c42d10300090b944d101001440350003844120041d0344159030368050450198410b5040346080806450500966206000305005500040010880e03600c03425186c407150720f40780354800c610700e00203000c0c503070900441d0302c02d2005500100300b41c2445080001035034005401021aa101e9803030b000101e401500401c0d04100040007043c1034034000e406100d0044090805201c5001002c55511110030610b010301000c251400d80078404819000440f80d40101c1d460502550707629500300405003504503040041d40081c00d25080142d501324403012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 77463131 1250 77461881 77461883
    0x30a03121a0609010c171c050112030e04271412120403140d1401060201150b090402031003021c15022a01110f091201020a020a080f040315050402030d08011d041703010b0403 76
    0xb08023517a00c840912000010900000d0300040703003180d905040341015801250241000070560300700800301d8410522810700020201e034000c80c5000e0203200c00500704510b404a00c00d16043c503040041031804a601c101005101400b00400c040c2071032480d400c0f140848400c4040654240004030b0781e49c600003075140080c42010300644c6404800d09040c024148860300352003119455510704001d041c2000084e40000e0208070641911030400801643c40c10300c000230b44842010030500072501400d10154500c3c4412007404058010411076408501c06e0000394551014081190040030200e2041c90041000c4817211000400003d0f0310150300d5206005841210411602c42c0303920141c04008600340d016150313480b400f41c2e014065000004000344084c08241404000e410305141c0c0d6900c3d0100c080e04045107503500306688005000540c203092128a0740b24040341005001949806a034003e41c3c11b842c504800100b00110108081107101031420340700c400460032054803941c4900c10300100780d0103840 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 77464381 1250 77463131 77463187
    0xe1507020a050108090a110a0801020c0a0b070305190504050a0203060a0605030c060403051903020a0606150806090601120f180506060108010614030112050309030a03121a0609010c17 80
    0x400040c0c1c5600c91213041d48100c005034082d10403450329613500000d05401007810307030f0b21580903100412080b0091000e0305070a6000c034000d09608a2a007400404008043c00000405003010100030140c6a0780d41903030800640f8800019080c0d480d1f082050030f08800901c000d61600405050010148107504000244d034421410b45400024600800411b44160f100082040d045501610030002da0103990141141c06401946c000014642d01c1e4070440301542c1000c100040020f00c64000f41d5840455607a11544c282c40703549550401e480080c0210343d1146a10180580b280c044605c1a85140c00004010035141c11200310070203103150894441100322110b03030001c0c542c4000007035003501c940401d2414002d4210380910316420601101d1040a40107c159024803040150042541b1304102c0c0e411070380e000c1d41e9a540c16554501115040d10499590708400580700c401c2c1d14038660710801124049403090803c0e6400b400c2e24a4101c25402c0c001c20440c1d2401070104001c1607440520003185081d080f41d10f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 77465631 1250 77464381 77464399
    0x14070f0809030f061302091315060e1302010c1113020301030803060306090a0c030206031305030d0b03010c050915090406080d030504150606120515060a0207030b01120f060902010e150702 82
    0x303c0c95612103003154a0000381040c07211000241c1040b01213035400100d610b240d0342d902e48140d124041d0312100d00a000c2da9869452104104681c1200203164101142003c2103500b03030170350740008100e2040301a02400c112090a00c05c101d80d0386280740c0d070901040401042d03460f9a541c0c180349842d40c200b2200e15001e80680b1000a00e50070340415028402a03010300007181503410350b020301400f50401400c007120b1000808043c2c0102e40100042d00c52101032550100c0e401d0315583c20b0509440b01002204103200d010700c600451903803401c182d0b00c0800075501c0001d4a403024140000c001e03109640c8002040d000d0b00d1000200b90d589034220034400c0740991803440c80564030b4010300701100d5040c0301e15000128111280200d807103c9070040b907001090400b20781c0c08004550001200c540c40201560003580c40b0038000c10400c1007030012a4014100c8203810442c2e1310300741e15949501c9040620050a2999502c90a0300710ba000306101d507222600034042c0d00c640c2a22025590b0190f2002c00140c0c4108008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 77466881 1250 77465631 77465653
    0x311070305030417090a0e01090c03020408070b071b0e0403021e0c01110309150703090e07080c03072007080708010c140a09090501060309020405100303050a030b03070e0702031914070314070f080903 87
    0x4cd0088130200c4065170b0040c00c225103400f5400e03038141c100c140115510898001c070004808690810980601411010003200e4105454040e14012406035601710100e1031400c1003800c81404035082000860a090800065421f1480385003188507000a0300d60191040c0030300030a461400c000b900149110341c9804100342c0e02c954445440440403202031740043d24410000d0f003442c0b007640c003850b01b0201c64207240140750803111101d1031145000310600d0301c6a118490800060400304500c10003409800020010841c220030f0007859008080303c484904800000c0e0084500d00c1400044024800300b5410841540c50300c01c010050410042d05901c21741c145000f00b2903d28051003840c00f142d6251719030304d01c1c242c6284001d50103000c020440c164180150346000580b2080c44180d248a00310315405035590344045a00d14200b00310b910250410000c42503601011501d52904440065816041c511a1410501140c0700c00d03110720500100b083d01c5260b46141001a03d1000d002004001c5069a00d101d180c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 77468131 1250 77466881 77466887
    0x30103030509191401030b0111070905060f01180605090604170d090905070e040f02120f071106040510020f0d0e2a01120b030a021e010311070305030417090a0e01090c 73
    0x540c024401c18130401c1030004060360107030f84160003000042c100103030702c013010441080c2410056800410f03190b868004100e0286005004001c1700203007401c090802d4109120700300541009409001d092000010f5070070190f0303454030192801001d09011800c00003400d02c45058035000c500d804000410184040410844200d020b09407181d0044c0d0f8a004410780e00e101088003a001145030428040d6003005541003610b203000c4034a1041314841c00c000d0285c00c18003802000d0025a50300d04000340c01440901001070700c0814140150b1000ea4030158849007500e1900919100340200d080d0298902504001c800401091008450940507180e1040400c242000441c00e40c805042a0008442c825402c03140b4055034465042d000c00901262428103083d404181d01052104240707460302c80046079900190381c1401a00c225444825806080640c181c1d27024025020152004000344004603540c0ca0444c0c542d421307207001d40c000803c0c154001d0341c2c620040000120038002e420149003052019240140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 77469381 1250 77468131 77468179
    0xb041b0e01020d0c11010e01030609090c170606030a080c0c2205010b0a2c0306070801090f020a1d0d05030a030f05010512070b0d060504020403080301081e03220b030103030509 77
    0x3d041812100172202d12001110900c0803408890b0505554000c0850904114420300b90040c1c8108640d041c43c43c2070403603506100c00782103032080306984040c0070400070343c5010801e040c0c19a403140185441d0303049003400906104001201541015040f0380e0900e00104d032141080000483c41780402c01640c942200601e54813036690301e0b41c003080e039202c540040c2c465140804c0714284400c1401b070003039451000010b0300744041510080d000906c00c0b030040c070401a29200300c2105640c0200304526101026002070119182500c04030000144403000c3c903926120300d01d124452561000a0340d60b1146e000344090010b10f00b0000c110520380c41c1c88004144d5090864116048204010042c0103107881c01140554603406802502145a1110300000c0e09445030300182024610035100540c0702e42c1801500e07440c0c940354181c10300041c40c640010001c0e00710040202d031141250003545c8800c1c124130a0006040d000181d002c440066000000001410340c0200a0034019400b210015a03c6050309000b40d0124 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 77470631 1250 77469381 77469383
    0x6010314180a06020313031101090c1215050106200610090518100c08061903020609150706020307020d090e0a0c0e0d050105040201030f0216060b041b0e01020d0c 71
    0x3100601003503050031107848090481c68648200c40104209640d440140e80041e50a000341580c09007030310007015000a503000a26925400030440030a580d01d81520401c518810b01103255180c400038010f01600721043c001100c6005424800c2d565102d00c01031400c03000d9140001c02030007100044003d504086a0b050152090200001c0c11038107180d17000008240207004008008003140100d03100074810b01c8030a140494000c40095070000e681c00213060303240c0c000c0c5907078403138008800100346001c18460910252a0107490b040e8444414202003044801e404c40d98290f41c000204103502040401d80040d4466400b130b41c02e43c1c82c0340b45402002c1d601d0004601611445841e1640020040c2c01c07d607004d9110800e0074501840f00c2e804039030105900c0100001c0c15603403079440d4000c0000b075581500070241284070b81801103281002405500d1b144100b401c5000b40074948070325200e071041d56650800b40d01c11219801c1710b145601030b900d01a0003c034030800401e0150060341d52034480b41c1c0c0126003a400407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 77471881 1250 77470631 77470661
    0x71101020f030a020f090306070c020a0603060b07030f02010204180b0a0905010501080726070201090605010807050607020405090312160305060f0a060f0c0b0a020c010f020f0a051605060a06060305060103 89
    0x1500d83c4014400a500402406900c1c02424804001c140d6020041c40380102640d032606444106540180507c01959401100505040610400010b0306000465801d1501413070a180d810140c09000c0780688542e85c800305100591a070207000c210180d078829a02131400301c840c901402e560f420f032802a24024820f2502160003500001c1c401d9004021424505148603c244104215040c030348280000980e580700060b0755401624007008110b100345405020004000c01810389402e0025030745100e03041009000705c0d1500003080b0850310410903a8000c195400841e012441c201110165002c40403905400003410b040c003180c01410b00701d0394801141006070900c2d01003810040705842100200fa010420060107c1080c80403402050384c06028491040c009031ba2048000281d9082d1402c9084035000d06204000c0104246840003c443c2c40d0305d05801c00036100c0e01f03428003844103401c44d2940600140514801c1108211050303001d1802e4601c543c07010811a16050011000c89100000c0c030804 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 77473131 1250 77471881 77471887
    0x60b0d1808160807020d0303050f0601020f0c01030e0304080d0f1b0305030f0601020c03010c020c19050604170319180e060307032303042907150b01051b06071101020f 73
    0x100e82d00c1031036203015042c0204011441d14400c0e07808511a04a49401640003036610002c0c458443d48600c802c64200000744000c25200410240190f01c443e0184040f40c1032680e6222004a03400c41071058400070061481540c1c0191135030031002c2d22800d201c4185c000016040710f8103020500d40d007183d0039a8039406503a0142142e49560100702ea55001404241c10b503c070301e014140041c0e809010381c00071140d055000e0074400404c0c206100081e56070301d1020f503802c0f80700d89c024000e40c3c41d010113070f0f000c60700414414034000408042c4503003184901d4500503000d84e003043d16483c540780c002021000c0c111f403c04590f61142d540d0342038451301d11804d841450740758004200030004612489180c0d00108405500511102c202031403031461035016500c182d890095402611032110019015000e9023203006400340e1604186603640c1500f1042c0e4040c81c04040d03a242140c8003941d01c1501505c400601c404483c082d034400f0720b105169522070460700040050031810101e8015031043c02075843d085202100541 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 77474381 1250 77473131 77473147
    0x904050319092706030203160e010b0f07020f010306030203030304060c0f0e060d0e01020409020c0105010f0b030601020601120305130305010b031605010c0618021807020c040212010501081801060b0d1808 89
    0x60380301c030b00c402c03000c3c642510b41c140070016135014040340c0016070f100d00049000c51710745110a07100c010143e01c011181c0d1000d0207404440c81190089540c41c9504071082d0b00444550300068009080d81c3c0c1001e0741500c800300400c0100403440e40802003103045a19100c840c0d08a00d0011510495a6191305800407000e01410428000c143c1165030006200400542040c1c4c9907491442243c0020303a5020060b9111801084080c6151000b28060400c051069245141c0100040d50310728040c4a10503411410100240a040c481d006031002d002302c0e040f078201c2d416035905080303018242c0c071001c0ea0301c03900420303803800e500d00040c3c003117002181e8040c1c42c0c105c03000c88680ca40c00c0c01001005100a61410354414040040c2c0c0c0d90412100028407017495540c0c03a0904500003403038a4807206d0054050b9104101c10005c4014004030541114800d191503201c5a498085141a1100c80c0b21030505c0d541c204103010a40c107080602606100704256020000581c4e00003000d4212b20a4507005044500c080201c05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 77475631 1250 77474381 77474429
    0x8060d0f020d14030f04140301090c0b0d141305010c0c030f0f021e01140f0402090402151909080c0117060d020a0b03070f0908010e0c040c020c090405031909 69
    0x10340090041410300080c0300754022150540d40001303481185c07010300050500020002e080f50703244468094001b04118400e80d40d840069420f0383c00b4001c00a1004110056984c2180d00002513010300b50490807020304004003240c515082500003103d16500f0440e012101a2046e400011202d403d6030341d40752941000241a250704c421b024503403046001d01d8041c40800000e4092101000c488078000040a2603100910b0380e0b584006400e41052000360828040544e55100742a81c0040d012503e4540384c0e480c1c01d23070085180c440c4107075a03441950f0511350310000b180c00c58490070449000c0b80c01e072550503c0395001100d48440f03561070302d803604081001091007810030400c890442da101401000815840d50f80300c2c21203810484080d00010341c80c0080088056204191400070070080c00280020164000030351340391160a5001350040d90b9407105040307840c0c400c104690000001070300c0c460442c1000e042c41920303540908064010b0007000400c14801c141f180c0d00f058111803940340f42c414042041c400341 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 77476881 1250 77475631 77475649
    0x102070f080310050a030c0611070308040e15090406050a0f02070b0a0b060c1204150f0e0103090c0906090b100f14031b0c0105060102010f060609060507060e120a08060d0f02 76
    0x954070f85094030002040b82d44030103161801440c05010040c2c083c615220b0020400500c010318031f149a00605810000103803c80d041e502660303110349209207166034031404080b405609440047d40041004140418007040c0d601c841c1c0201c1d80088107000f01c1801c0821003081c1c1c40b030900300030f01340e0407850002000c10748190f025048400e0000c0c155482c10311611b181030310b0700c4580d0b4258a442403000504100e200400c54106080c904c190a04c807c4c070521119020b010300c1d00851078241416240d055070340406c1103181615010f410380d00001c0100a4403400c0050003448d030800303014090080e14a11a190900455100c03501c1308a60b61680b44a14200303101c0310b22500f01805c0b1345255245000d40051070983d100282ca00e0b050120000203040c42d08500090139640c01580034610390703190046c04e001e481d51000c8002c3c15030f030983c20403595414041c60300800400c1c4404004e103040c05800c1420014007040c000400c003046256642540688034401089040030102038010144205a50040c1c0181044008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 77478131 1250 77476881 77476891
    0x41503170405040c020709050702070b1c0902060c0d030b1c12020a0204090308040219080304060e220902010914030a0311030d05090303060a080114180a050a031805030102070f0803 79
    0x40781455521070200d41034070380154039031000d600f00c0320061010500a00c552a4042c0c1d1a1005010252610b40d014449102e8507203642d0255404422000f842d10158011180c0258081c1c01c083e075807840614215140d5500c0d44080b00001d04008010a0510785035407010a4506410031809011241e9582c038044400049200f40550103880580c0d0050f03540d0f1b00c1464a20b80c001d44440c0c401c0d14080c410003020b4818094800b218800070902070240800010a46060319003505040044280a10000d8010001050034046002020300c42500300c01c12078000224107032003070320790200340d43d222143c0761001805882900c4c1c1580c011008440807d10030210340c0454034002064170f245c40844680e103403c1d03510468000d15550b00c00000d0150078108800c0b4074009001000c001c00c00400c1f03500c3e6900f80d564018150304074041d400041e02803103402c01d00103101c02c15445001c403004c4141314503018200b0014030082c11045525000002031074103044c005c45d1256a44011802c030411040e90303805001e0707000544 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 77479381 1250 77478131 77478173
    0xc17160f0b090d1e03080c070507140609030105090106050f010207060509010518030f0601030b071112071b0f1409090c040f0b040e0307050705031504030c0611070602070b0105041503 80
    0x140c0d0000c251059000f003449892400d030441308500c00d00f005400ca282c040c0c01060044000c2001300d0110f0800b1403101c007920310007022844000000710019001d80034800d14036a141d46030000b4401c01d079005500c03081c11108140c560703102112008006984480f9039105000220b041005994031395032042c00240014611301d64504c01c40d500d40e030042413600070203100c403420b542e01060040c41480618003100303074000c610307143c11005108814520f42d03c40b40d05490244620b075001c1442004c002014003000181e90384092003d00131541c0d1601400038804900c240403001038009540c1807981080d45420307102d001d0840092581c1c282c00c60038840100000340002d2f480a5031180102c245030703150300604c2100c83d083d5000710340b28801402d209090000e9984400d10036403029041d8030302c07030101c078079580d0f4006c0c1c050805401004c120304100c000343c190000100c0025000180d844204440c5034050305c4180d000d05014880c0741e0700c0c0d4040c403088401002403095100c1c0c2c05001000040c518078a40000401e081c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 77480631 1250 77479381 77479399
    0xb180102070315090204110f0a05091206250503150d0c05060c0102070b1303080105060a03060305010603240b130906020c06011413050f070806030a0c17160f0b09 71
    0x52039982c003400c8103007508620070b604c4411200c190701d040d00849a0012000800300e240011440240e8aa8800c040c0032074144440414602c01e107581e510f000f005400300e40015940c080c075100c030868140c903465904400f0310b00460900b0789501449901079174454109420094020741240d01004031944554400b00c1d510030070b444c004100b549401c0040c0c46041c41d51800543c649a0500d400450254010300a4014182e03201c2824007081d40818614111201560380958031003407200c0890107403416030000f80296003450030001c01c1160000b0b8040b50780200035080c21219080301d00178010b0b90340701c840140d403200040c4903407185000c0d642d11108800d48180c80061910301d4680ba15824480e00745d004d84407410302c8001e03004280c148004002c0c0030300c1c85007508101c07900e41407941d00582d0402070078100170480c40400154581e00d042100701d0030a0340006590f6280307544d45c120b292105814450f03240355409843c0424004030000e02c0741d1815a0b0070281c807044032600380304640c001c6c0e0b0052000e00b640143c4803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 77481881 1250 77480631 77480633
    0x15090a0e0c030a060c11030c060604110f0c03041a090307182d0b12070303030b0402041d040203010605011805060c120a020c011d0904061a040c0305010f0b040b1801020703 75
    0x100100f0151a20032040403803c0804900050600000c101d10b00089800801170076200300408a815a84003c0842e0000356002c80c0d003420060318011940201d070191000615800728450000103001180c50741c222401071361300807400b009110702690b814560103a001e80810300c1222484c4040c841c554410480c0002ca40740200410400043e00141880342c101c01500f080c01c0c0c00c203150069000c400b5003510728820344486602260396a8186d0b101c05010986c1d15192108241d40e01d03012500240451801e081c0d00d10f4074444c0903003a001e000e0b10100e20961a2420018003540981081071885401c002804507552400b8180816540f110f5090f5410b8024648401201003101c8064400a800365000304808148040003400f2510b0065100d0504103004032040b880703a462142c5294031551100010074601001a003840e0a1880041d81c01c0d807160420154082140d850b03840a4101e80c204074038812200c0c0d89401e070540620447c01200b440c281c082004202105650219403049481841256581036807 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 77483131 1250 77481881 77481883
    0x81902040f020721020111033105010209010e0301060803040302090c190818120d0207050a081602040b060309030702100c0807200901260102090901090c0815090a0e0c03 74
    0x40030208484d6002d86081c9080c40c0b034440704503603c880c51140000c000e0344600350342e00102800300034000300c5a48007403900d010308510045816584040d6940b0082c2c00c0040c05d1500318080c2d006800741d107000695500210ba21403405000d00003c4400b0840903500e41800c0d070302032201209008042d01c0c40140304000500800d09080d12030304200c80070360b035440c1442c1003460350000d00b84503000c001c1e0541e90000c0031b00130340407100d04100c890b42c03a1010001a5208075900c3c0c41c42c24013002c407502400d0f81070085854210b0034507410212100c544201e40c200138079400c0b0030400c07941c0c0c08180c1d60008694800c0c04500e006003000c0e00102980981d41c20514842c0306141e566649a5004400444c1c0205c40c080f2034103044040c084c0d03107134a010000c0300c4184041d810701c0d072580c2c902000b0440345940d03d0b805c0844844030040c298111120031078044e001c0e0005684503119000544090300404001900010008203045440a998103225500030610103540d15201c01c1440a000d0408290119010342142c494090b50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 77484381 1250 77483131 77483137
    0x10603110f03011413150608040f1506051003090b0a0e030d0504080a03180209060910091a01090506130b0d1b02061512060c0c0106030807060902030606010504081902040f02 76
    0x16451120f0074a000c150b418011000d950305d20b41c1104905003040c080041c105c80000710309a514500d8034400558450902c0320a06c4241c3c0406002e41041345154246044143c00403419124165040102c80324048421021211178100181541d9550008181100c445030040d0440f0702402048a007030207000c00c020b03400c40c0c038241c0701140c0010700010a044842d406015005a00030400610f0284440c1c54010502c914030081c5207600c40c60042000139211700030429240d0262500600401c00031072115203004080704001051b41c00714814441c00109490108201c8148a40a10310207403001e28102140c0c810760403d01c0001c40c03e64650304840c044000c40c00410064611540c001c040500380400f503441c80940d0346450074020035241c8488113800b48001103c1d5007003000d90840f0740c0da941d0b010040c24010181504010110382002549605002240e00904825802207066413200d481340c0340107544a1040c2d205d40c01d865084200c2044000d04050751102c0701c3e0740050808071303d407400307981c2e200201d078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 77485631 1250 77484381 77484389
    0xf0a030603051609150602031615150801050c030c07030c02030a0f1a010807081203090a12020601060201050105010302071509051f0207030e04020a1704080d05010e09061509010603110f0301 83
    0x10b0080f10040202280c9401100309080c2c02241c061010390808200940781c1c440c89100b41c41ea98980c400b1b031030400c8034282614509081da10001c0210404030a0011019001889103190560070715000c9902040a401140e0261043c17100051038808581e40a85010403a880140c2c1c0c180206425440400c080342503030740445214504460240030040e046154121060704080301ca5071003904203020f0340000151080c041560740302e01315201d54034203049a00d412010000200715020008410b0002500022281c3c16108603400900440ea210001101280129500a4807c40c5007200c403003060456a03010507800c5000c1d03816501d1580d0054102481d800700141141c1c081503000a408081c107511401f00711000380b08543c20340c0f41003510080103003084160990340201036500340100301002014011034229001d04034007480b140d070792803950103419041202d021045000300e0000411851170100505c13241000101031413450b0f42008000c030000c081032449074106050400c9402d020b803c0e044040c500070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 77486881 1250 77485631 77485663
    0x5070e090d08040209060f03010207150b0909150601081e0c090102010b090c09090709180b0f03030316050309071e15050c0a0609021503160e01140f0a03060305 70
    0xe040450311a4900322106102400b007100040c14800140d80b0000b02c26045441111100b6044a003080002d0082c400c1c108020701d0039280703107004220031129402a0b04036007001c0715100c00036034489243c10303100e15100780c0054255200d113000400560040078040c1d000110103501180d0003141d00b4160005503404c0e01c45c03401903040810554210f43e424010309400190070343e516181d41c240b0f40725205560195945030303481540f200e0001030b0b07198840c41d050802003510782c1032800c002e04c84d900c000d4000d01440c1041405001c1d111628011030a00000301c0c1d00407510403212084490751700301c003180c1503000645544020301585200260403460300c1c0314030410300f1502d469822a6840c00d81c020751201d101c60080414807038140089168010301182d1400016040400420032403a2407000500b5049a400c3c014074102000c81404050401601e174201e565034a0340305e0001800300031005442e8960540010a48101300304140c040700351809001e09404101e50501044068a030754a05040145044120940b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 77488131 1250 77486881 77486909
    0xa03020604021009050d1e05070b070b010504020406081305010615050d05010905070f080402010c0204060306020a0806010201020928030b0702030c06010914040b130503030c21010807030308090102070507 89
    0x952602d25103c0204080701c0c1050030002d0310307220100d402002604000381000c00b141c5131140149480d2410304200c190f00c0f40a40360500e444540990f655001410152801140305001203044d00f42072003290183d030b0440e1a50078a950f20f210751a010203036060b10843e0700755250800096500341080410b44820426140e21b520354008001307540440704140c0c001e803141401c6c482807084481d00b1070b2203101c503515145841d03d5569078030300042c0c6060303420000080d00145840070010030710040c0e5000d0100701f0010340c0c6242164852000483c00d0780248405541d011703015104640f40201c11114176816072009841c03540c500740e07032521000501c5000b29809009a0400219401ca05c6401e200e0b082c09003042d81d408100c1e010004005607a590030080000303120300060008100114205901009080c0d13000b001c596491900340300128158106040d0780004016142c0c498114408400711141602e00010091443e14655101211005000350031f250842d5401c105650200c0c40c2407007484080d16110b02502c907 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 77489381 1250 77488131 77488133
    0xc03071e0305040b0d02130b07050d020111031f03050307050102040e071e050a0507050a080a0306090b1302090105120112020901150e0111010e0106030b0105010809060c07060f0204080a03020604 85
    0x100d0048840050030951991400010000760800c080c0c0d81a5001c0500c1c06894501c1c580b00318009214071696014080d04447c400144060300354003c5c210300384101d060b03a4140c1c003844800e070b02345d40e80d040c0002c0d61040c052000916400090796540d905036102c1440102107075803074990a0a640c130041c4196006c1c2d40025040c009010b0a065640c1c20280340c0c0703080c40891082815441e482d08800a280301001701c0050401c4185124405840340150400d0685181003400d14180710240d10640d082c0e004a0705042d40099801080c0c45144003c090141802c40c210703d041c605100254444403959040c0b06003030100050302d036020034699000c3d040c403001465644545004219044205a03c0b00b200f000103043c283d0580c40d405003010050070800e00300480ca404190500034050124442505560340c6040400018040041047c40c120388007a280c3c1d2006840e65043d05e43c482204070340e20b10001e80200228000100310358050640702020210040c00c050319403c03450704001c0038450640040c0e10440c1800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 77490631 1250 77489381 77489393
    0x2403060906030703030e040b040b090a4701050f040e09011d0a020f0310020705061f06080c0304020d06020304121106010501021513140a050706051224060c0307 70
    0x1580200c0110b005203102807840c0d50003401402d20f010194001c3c0c1c0c440c031907030713180da2110382001d020500c004110780210f1510800c06001446803005601402954000c206c08041416075248110783c428000000621040510718620704031400090781080360030000c2e240c0000103400074002421082c0007000032030500b03244040c03d40780f240c00d0b07403425a82c0060030740c0d4001d0000113405441a40c10b840c0c241080c003000000a00300003400002d000c0f41800051203204001010808078400d00c1e051440e40340c20300424455441e0540e241c0104400304450501144000e18204091030303000d480140f804034128480e644090590f001640c04860a81040c030602c44129000740d060182d810b00a002071600c0e44c50000002e5460b07110014140f02c10700000c01148050000044044c225900500801e00400c01c50152503540c4105039400c1d241801004004650140301d002190300d400c0d40f54500f00c03034949403500e003082a5001100950101210951040003e46035031028148800d081380c00f55498082900b401c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 77491881 1250 77490631 77490649
    0x90c0303030c0216120201020c03011a0418020d03080a09020a0e0403021b060405010509030f03040303020f070f030b0f0601020a06050703020a0e150a26040507180218040b240306 78
    0x150554000b80d200b41150343d4608200383c11a5445c0010002c0c2c281c0f1400180c0c1030032003100e00c498040d400e103100031123a038803514400b021052084e1410000c14a52051514034400ba41c803009502c42d07c4510f42c00007103071080c814150459500c50380000c140403580e002a0b26000207a11070a410052074080200381a0107000140a0580d40d0002010100c6400c0c00204c2d20310031409404d050200110b003400ca140c13020020216200c400341c0440b41d07100e440f030502030354134074901b00104424441c211002c2444a803c02070641200c0d4802410540750300e8582e0000c0088030000c100a04603c10b00c0c1500010490038090303140100a40e46005980f80340101008160b0951880d116024590303e8044031582c1e01c219046640a80191038105c4030503c01942c00e1464205a00810391351003810414030007400008242003003100c00c841c41d41c0404841000381d420036801091100015488c000b8020324450810390042460010020405959224180c0300305451152240c1d008021401c00b00401449041007184 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 77493131 1250 77491881 77491901
    0xd0f1e09090b06071703070504090e070906060c030206042918010612080d05060105040e04050601050102061003050c0d0606150c050d020312010911040308040e09010c030b0f09100801090c030303 85
    0x30580c54607650b40c442450402d8040c4170f540945c0000400114401d20940c140e40c0a02521082480101d1501804a41e1407083e8085e50441615241001450b18000c0020f0409a07515401070f000300d40d03032500c40344401229400c00215400640081003003401c048120303a8480c1103010070028012411442c0316003122565000304945000043e4808082258007080c3ca04184001c40089a03507503603900125254045d82d480081030745000c0082c0010084040f8000341694000c0e030840301585c1d28201d620814444500c4050180d03000740328050020304020901d40302c141d004000104006990380348107014100d0400300800040c02c1861a1300410809000780100302c41d03544011810700b903074071480c0105403d06100d83d01c01103a9401e0f100812220343c82c190740003560403c81540e141c0d40d844154079410700c0c044490090039444c0041c1c0280e41402449080f49048015062001205c5a581440021a00030304214040c00e800c084c0086d500030240590380025200d555203200c0149149000fa0a413650008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 77494381 1250 77493131 77493139
    0xa05061c1d030403110402041203260c07060507020f07080a15061401120e0303070306260601050d02040e0706020d120c0203091314151306080d0f1e09090b 68
    0x1c00d404024600200f41d0341640d40101019010044040025000b07214645c0000e0406641e40309410a042d00702540b04d010751050420019030308400c000f1072681e0352084400c2400800c040c00000045000c69004580c0b04003280101c074180750314081c0c0f09191280d0b81e1b0102d0829840b14030710704104880c0d400841c982c1c041c05402070050505244030394200c8590400143c1c1041400c3d0075526807440d2941220781c0c400000d100360b980c0c1e4203040301c0060250502e0302480300340a8645060199001c04036590008020210b40684141c0e400c200400500442e54801a40e004d078a422b103070a10000c1c03d000740b0000300300705e0300202003454800c80040e00411342e0001d035910307203441c146160036002e401100311500d41c08119201520700c1d02d001d0f0040d006140e60202c5d0325440040c042003100280000d408103003495801c40d81c404141000c48065001d96855009070b00464201d5840308203a81d0240014400e00c12040c10a03800034802001e0402c0c070883c800309000c0008a00c0901008800b185126100c00c201c400c2d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 77495631 1250 77494381 77494421
    0x1021501150f020102030f13050a0b01060e0108130f08090f0301051816030c030b0c0705010c090f052704050f0a031d0a0b1902030415030f15230a05061c 67
    0x48070b031f402030441c014007090360a04600784c031204012003844204803e5901000040c12540c48002c01440ba100c10201c2d1800302d0030100110b03842000b100100e410281c0d01541000ca00380312517031048820b800c041c920a820005402c02030703903142d4007070180c284a9005141048a5000c1400a1070310384102080007021703941c0100414400324001c100a402a81d0b000000740c0b80c244c03903441040b2858031441e20090450352034500c0c6901c00b03a6202882804890003c01780d048074a84610070405002c126030070078030444180b200960301d540014000641d00900880c19920440d0041d41c2c03040c00e003131002008070001450051514006541504018503501064039021112800c1801e4168607102d507451660000b4420081c5103a03603442002247d000c0c14106e00c3c4031007100ca201e01c000d40940f102c80c0c104584030341400040c204a1216a40341d60032542d0000800101071325101400070f650580300c11040c0c100003041d00100d003644820000f0b011292081149030303040e1006120540440390204803100c001e10081c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 77496881 1250 77495631 77495641
    0x614040b010c1a130209070806090c1908060a080a050a030801090b060706022d0417010c050a0c0c0306020307080a0f050108060a020d0b1201060609061107060c0201021501150f02010203 81
    0x41030321000f88080c181003003a03941c0f80c1140c408002e0310b45120080d800615403040004903540075560a020b082e05075004030042d15611110180e0b801200d412010007a0502181c0c1e200034410210990844005014460704580710418242000b100c03807010340d82c80d0300802d66042003540c0a0043c82c0100403504080001200d01c400081592044200c090601600442c0d10341051800b000c0b2524800040c804000000d501c4003080c1c8201c1d001031003201c45055070069444000380c0107004010f6030000c20390704c0ca854206180009c1ea180c43d0b4545051390210f01c1400e0120005105100840c000c0301c2c03540320b2070050703e4100e00308403d65081088994410303052000411480d80001081600130030741400140e246d038441c3c0f807204010700242204035444120003048848000c0c065000700d081c1c0c0c8480d5901650325071a40d10279a9565450401802c1d6644241c030100081c83c4900755500700184144140c5030100705182049601c50404c0e00490300c00b4445070303821000141c01224140c1000900d000a40c20760cd00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 77498131 1250 77496881 77496893
    0xd02030901020c01030209040f0603141e0705120313091506020a030806060903100f020d0b0a06050a120b0907020f2103040209090f0312090d0c020d060b010e040614040b010c 76
    0x41140f114181900829940c0b030f5962503811410200703002807001c10880d030f62800c00c0360403040b0348910410b8600800070001c01c086c140112400301c41e003424000701012031070030003408040e41c038928100d002404181301115801c070855001c04001c0901c140c0c040b0304108041c0c644400f2078815484a003c1d0342c0a115403c001a41050302a54011012a1520384621220020034140741300003840040c058070301540111602e00700e9014000e08a440313502008802e881506002c06c3e40c200380107510121300140000c2603407a1185d007108801510084010900039a2078012400204081e50050090b80241c0e1004240756020020309281201080407200800015624903031503110240c00680184400800a602220100320040041d10158201c03a83c81490780c0c0f480c5a1000c0559110100c0d008401e81040020300c14011f41d01c0003500100001d00401c4255182c10003003060010940c148800328030302000c3c580d140d1103131400603d1008440d0403061401c0302040110b075501c403441418415101e18020101d94 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 77499381 1250 77498131 77498143
    0x2061908070f0f031a0a080a06050f0402060301090506041b050a0305090309010903020613080303040b010f06020c090a0c02010b090702030a030e060106050a11070b0403080418052a091306080d0203090102 89
    0x101d421300003902e010407148550b82858451100381c210790303a041c0014442d04d0000b02d5800146c02140e0801c0a51220300440c9600706040e03501039407101c010f04c01400042d0445d80842c1d008000280300182c0d1003002c088080100240c100d924010510114040700701c550180181d940c0f02c3d0090028514203035040001815403415404041d000d003801090141600d10703044820740142c1207041c02c0b29101d19191808483c100700034010120b008104010009545000040d03264684030000d00d40019a50b903102d1000080990080300c004540d00c9101d040040c0d1079109036207025000950103580d80350311001c005029214141c4150b80c1c15441140100300d81d070b034450f090fa04c204c1e00798a0180b46600755400d01c03504d0103540d03401080c0b00c040000f40000800c1500d100070b00850311000140c54101000c0f010420803283d04994101c0c401c13008000c2107010f0070503143c0f0400c81e0040b0405013401c03d0729001c0482d8610003109040c480b60f60f80e9500c2848800c070100055240c85505200440c5007200703100000f07458032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 77500631 1250 77499381 77499407
    0x606091202060715050105031504080a210e031306020a050c0904080408070807030c082d071706010303080c0a0906200a0b0403030b190b0702010c02061908070f 70
    0x10010304090046588000458007016001000003160158078480e41005003002e105541c440e204400301e401540218034090342c030907a00182c0643c14109088030a0302c1c5d102d00f01242005c0000d0f150403d0511280c584548803400e1a14002142c0703400d65603a4101010b202600240190340c480100400000c2d800210301c0320b10320301a80c5d07144564031185401c80d003d0003140c010300b01500900c20b001c14461400200c1d0380440340078503454426a641c0b4600152600e250303401800d40003940100200d03452848003007200f0f810198004451340c0c03a41d41d0b880710040190001c801556070308070000403c00c0c1540308402d2504212a800d005207011245800600038501910404050000358440341c19072001080100007500c2c0c200e0207540303030603a081c5400502d401c000c548c1180400c0ca41241d9110342c3c01c00c6982d0100704030b9000a4014614100801039074180c0100c0012410410740c50b1800f001a207441018250390303465150b00e4505041c8a08018203060b034004d0a8208200c1c80100c55006254450001d803012 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 77501881 1250 77500631 77500649
    0x160306200306060c0312190c0e06070303090507090c11010b1c03030509070b030a0905060106090b0a080405010204030c031a0609060a1511030a050d0612020325030b07080712060609 79
    0x10040d1313421150460064188001c44600560700300000d05c004d000c22002049101641001440410002035507100d013084c0710103410810a00c50702002074005d41c04000d100e400b6004407004560f65020403420385000003400c000080715500e8040f07001d40d00b4016550081001c0311000200070525031540000c80d450140581050344420100d0700c40340b414030030000034004120186980e0b191540c02503024080d080380403200d03407007040000904030340724042403000e460080c0c80c42c5140c030b0b80081e0110750400001e0029200c5540c00c1000000042e500600c010046100b203d8078400d690420030302c0c14441d10010202ca0154000008200707169441500f83c80a50b84010b1495070310000410040300c8081c2405640401c503c000901c1243c07441d00b0002400003400c8000042c0500740e143c2d8245d10310440180720007034040e031101d81d0404015854804540424044e1030300c1d200499070f80d841d01030002c1810307190680840c10308801c0c403483c1a401040c1d0480008280d906001803440e0500042000000344100821 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 77503131 1250 77501881 77501887
    0x6030417090405070e120c010f03020c0c19050306091615030e1501050a080703020303070303020a0203190e1c050a020907170a0e1507120f0e16030620030606 69
    0xc5064000e007590302600024108000710710740100050031070500c4a44081c031032040c298035840303490000690440d110380103945008250201c41400e5019400540044c40c090003481208207043e25045e00412080f91400b41c4611001c1c5000c1c281800e02c00701070540703080d6400c00006010108400e003e400c08444100c0d5920404441c1003074218000d00d65284500c019004694400160b80b4030860118140e4004035141c0400e1a03452026640c3da04261100175016001030200e800032a000341d000c0d00030300c2d0076170045d2458040024240726aa403420108031380422035009445520b4100074080c25120140c07900540801a86611000e981324414080244121049800101240d200c1d175074100034217189540010090a120030b041000d003140302c4149030948180e116482503020503c1400d8000c004580b0780032011080c0040f0f11000d80f05402800403400e480c1c01400d1050681004040c501c20010031801c1242411032034001c0130307134440b041c906e2441d036141c000c62500000328004a0340c000d48119a001d80e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 77504381 1250 77503131 77503163
    0xf0c040e060f011101090b0a06150e0d031709030703090b030603100e01060f0b04090b030111030f0405160806060108090d0e0d060b03070e041a010608040b0402030a05011a12010605060304 82
    0x13941000e14841010594200302c405010021400358442c082d003010401800540e0b06c2e00c40456001c400c8214841c0019804403002c091400c0c801141c1c482140280340c0b1081900c0340403045221104240c032310307050790741c0001100820700d940040240b0150201154040c07842c14010002907650181003011022075584000e070f42c200c0b01c801d5104400a1100d03000e1034104a60341c42c003010a035007142c49800340250500400c2c203210310301803041d001c601810394141c0f8195198103019180300d4000810450b414803c001c50b008901e40448039a2008010342c000070581407a06c1c1000500b00d0501400039565036200541a00d41d05801007125400d000d001d80300001c11202c01d040c01005821013148260305809212000305a00508400b568480c0c4d001d04d5030072001c82441994810403603424403662001a0104011400007040c2103403a94120740014122240d0b901682c45e0300c2c0c211400303c2d405403a190007248007802c882c01c01180d100d15414542d002040310a1814004c00e82d80e1000800040995201840d000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 77505631 1250 77504381 77504387
    0x80f0f070f032004090b0405131b030614071e050307030209060d0e0307171201090b03030c07090509070602011a0d020303040305060103060207110f0a1509030203010908030f0c040e060f01 82
    0x2034040f088209075000c4020004940484950082c007400d40180d04299800e041c0741054020b9500034625140700041851441c0c44209114403e06180b034010142001c001012402a006401034030442942d0030320182030442000c0c01c0600710b009440c070003030032101003215182d4000c02503d44c005680e040259a4001c00000aa29880381040c509607240c81c0547e00c074800e200000c06815501c0c81490304100c0409000454400743c0074540340410302c00149001400301c600c6940007040c80003000390469080180284c015814a6029040080d40960381d10070409600300401640c40108940d000030803480c41070301c3c1000f9a8010310048a40103412100c10502151000c004840c021500901a05c00a5850749080400b0350322685e02a0341207207814004a0051034840001c2c0aa08e0b0010a581007161521101e8450200701c950400b040c84a00c090020260710203001d260711080c42074621035a2442c000c045101d000401801307100c3c00c403800f0b1200b070040a1080c04416040b11085a0001e100307180e100c012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 77506881 1250 77505631 77505641
    0x4050906060907020a080309160b0c030702040b0f060309010b01080a230402061306020106060206180c01180f09020d05090a020121020417010c020d0519050c010f0e0607080f0f070f03 80
    0xa1480c4000403c00508d02c0c000b2880c145951a091315030b007159035840200c0aa580241c0220792130a410030012400107142c194030100d0795120141c811000300c5071034000181e10fa0801c5581e60596511540144107541c1e0110560b40d02a509d20401c01c06039422208446241c40c101210b00c0c64690344c08041015543c80c2c1040e2811841d40c4640702414607240e50000b0f0103800707035100e070001501c1003c0100d004645104408408081081d0040503100d8140004440005c8861090980140d0721a00030444030400f8a40d803001c0d25000401581d18141607507082c017100d20003090500300390403056450340148e074030505040c1c0810411020090440d00f170500440280300b02e51044000c0d0700603080c130150684e03064005920001040c1c0a50f40c1000890400761043d20a2a04000b002072220780a11051030041016050140c102d0000142c1041d000c07144038101c0340d01c0c0707880ca8801d901c00070030480200d81c44034580780c1c022080070305800c050901d0094040340c100050103110900c4808030046281c140310760f2003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 77508131 1250 77506881 77506883
    0x130602070507170303060d030509130e0c09060a0305060f180604031e0f050a1d03030a170108010209100c050109050601031203060618030f17030703020d05010504050906060907020a 79
    0x4215035810440c41d00a80d80c400724030400750400c010b440d40c1e01c84158040309a034031800300648480e20074034041c1d4045640fa40085040355200f4000c200080340030f0784c240700301468620032000802440c02d042c000c011040c00d004052600c07400031030360180002400403c1440d00510500c0c0105a142c6541c405a0810800407106c8040c610416023004185913212042541d850310b00700c0040c03420b0b055000c040301c008100c4403a0300003094080082e00451882850100d4410f41c0c1294118034060803d000681141d0118003d04006030780300c0017100c4210181c0d58030b140104010002185001001303408502ca916003940c030070080c444881d0f1070078117110782900040341080d4070000f520401c0d1303101d04e80081310311070300b440d0000081d01d444404211507004a00341c08050100c3d20b6000c00b01407450b030320560f8107504200c0842d04109564040b940018038031014500a0603544c80150311140754403082c00031070343c050340140e103d035050105005003481c020410b030750000425141c2d00d40366612900300340c0c506081a04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 77509381 1250 77508131 77508143
    0x211b0705150a140c1206010e190f060f18140105160303051902070b06060306061c020a02120a0c031103040b04030305130f080619140c090a061809020313 67
    0x10040c5030300c0a0750000c3d191091034a060b014548490301e410701d050090010301e01e120880ba20200358158001c4103101100c5100030160001008007901e04150002160300c4400009000d80040c80540d0304546a0a0b070030f201407502c0c80b02010152001000c8203818490340381804400c140e56103450348110304403000e00c600744c508c9a003241c0c6107260040c003c01c0d040300d9183c0d10030224043d0203440364850080f6243c280c2c02071b0f00d402042e00c4450402115500140c01280e03c03200030801c0d01245a1103405007198080c1140c0d005884000118000c1e04006500c484d03080c0d020020005000300340d820039090f401c4281c040c83d0002038103241486603488c5105640102d14150000700b000000c041d4084020060040d12241d4640582d9071107901003a03000943c043c9481d10b4100000095061400940c00b00c0c0c406041d00004c504946922800701642d00c0c01e03034061a550100107400c82c41400c109510a00811861901c03100c441090050142c081d0118090001c0030740c4c000021030a40640000300f0880c40b5040301e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 77510631 1250 77509381 77509423
    0x30b030705060f030405060105090c0a030f0f09050a03021006030c0b0711030118060b12030403030f0203190908150705030a0b0301110a09080601060516030c0614040602211b0705 78
    0x320003c0e055800450302202e0780d104010000c103c0741001c0e50040c1c0034080d846151420007180240a5000d0700c0503206042d02540c1e07415003062480c0703003406000806c6004401400d400310340f42c10000e041c402c100007090f140c41e0a105003040080d02e0b40020100700c03250182a44c3d1241e81500e400031008260310140b5030b03d503003400281a4400b441440700055184103642c10845084040b0a00551319101c50b54180c90390400e020800200b4021042080882c0b41e80c4162840c19100000144034403440546180001d60720b1030302403110400400c80c11040c0480f100400b101464064001002440010000c0240607190801e01603943c909401c681e8800c600d103462a0b8681d20008070050802c1a284107000c0c442c40707148000078000b8024421608025104e16142400a070952001d030382c14a0241002c54400e43d54400d604007003584941d00c4c078020b074891580540c2d07030b071514407000010542c980500c80b1544800f40030f000300b1001080c3c0030200324410200307c0341c4032001e070304119003400c1d000303156043c911803e4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 77511881 1250 77510631 77510647
    0x108060d02060918010f050d0c05010e0607050d080f072f070306023001030f020411040506030a0e071d0612011d0a02010909020909040b04061e02070c0501080402060a030b03070506 79
    0x1201020703040c1c6d0740040d0201c5a565a80040040d0082d000d2070181c00c1c002d100e40c081c45154401c3c1403032201c80d9005400c0c58540030865458515041407180da05001409007000d1000300404060900c0e000403070f902d080e02d0503210342010340070700c0c201054100b001103001d0001c0520900043c07101400a6802c1002151a480a820324001c480c030081040c007110712006519240526005003458140c81e000108001d41501a42c02c0c84010a007000c080007000e001400000f03259500c041c005d520030003c07410042102c04e400c105651504000d50001201d1a14241c00c40101801d4819140d0340075800b00ca034140d170320340003400442c0186007a0305e4800c028001060142d41400001035400300492003a41e0320845e0340d940b20b0b03200d400ca0041c2c20145610450940204020a10040c0d080360068082d071000521140000c4c80c0d40c80002c1021020800d950b00410250203109008071500d00a080c03c0c04c10600f5450543d0000d1810300c80c4031550741c14150340720812241914104062802740c100a04080da0750804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 77513131 1250 77511881 77511919
    0x1320040303090e06060a080a02220303180b1e030a0f090308180d0c08070201111e01050604050103020906060c010b0a0b0712020f030414150706020912010b0108060d020609 75
    0x14030f000341000c0344520000300c3c02e203003000300c102c1d091201c1c03d80e00c1000307580b10300761404040e621480c40c00034081020002c2d5000f4407140040705000354030035182c9119108403150b02c41c4071460f1551108079150418011109034a403020382c02c0f080f10b07812041250b50b0390b0319411030900800c1c6810b0040d0f1800c0c68891000b0030544c001041d18080e05400140202c2d0425003e82280d60b42520f030040c2d00040c840800e2000041e400324040c040603803050400040303280020070801e2902d20107014607000042700305080fa42c0d10300300b0712a443d00080c1c01e031003e04c041e40c11342c0c000c514140390240c040740c0262000a00a560311030294800300394114000d1110035000c1d9a50076240050704102011380d200e8003020048190320b4000920100a903150030081c5091501d4104942081c0d0000380901e5001007965a00300d0f0f140d111107000b80307890392080c50300580700c204441c180301041c2c0c49881030144c40e070300d004408121603070024080b0380d0000085580302c12450003440420454042c00391000d40102d20800d020103000c070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 77514381 1250 77513131 77513147
    0xd080f070c03150c0e0607241d030403120e1516030806040b03060403080703020c010609141006050d02070201030b091602011a090408090307080307030c050105010b0304021320040303 80
    0x40280300094490b207011540030200c0c0d00f41da03c4000813684c1c117511148141000390103000380502030507141c0360584524000c549507000410000e800d50356600300842081c4130031224014400d40c40b10045050034110765400c0801035039024403109000a06c00140f800f50307240c44182510440c003985068407862030b030360304000400c0f00c500100c0106428074000f4000b401e140c4246001c041000b0001d10751501d80f0348090341c100300301811110405030200101e0318004400d0040b07000802d00d02c2070019003104c00416140045d40b02400d400001074034031604201141d84081031310f200c1c031804c110050752240c1900c0160020400500384c00e40002418041100804610340d00302d0600356150002d00407003408060414101c0e032003000c0c1e141c3c461032907804100071a41c1180a408000307806011142038984070001e00d4959009100304600050304110320f00304011003801407034010421030001d1419400d080d0700107151100300710965441990b6400340ca00750764007070040d41500c42741d5142034281c0e035036140e003402460b000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 77515631 1250 77514381 77514383
    0x6131205010510092901091a07020901091506031e0504030e2418030a020307080307030306050409350313110f0307060c0f0203030a0e03100903020c0d080f070c03 71
    0x2441400511201c4c0d60103031390390803501030f050080020403500d90000400c182039802030420641e0b40000c580000c0b10758442002c04015a0107a8850046104220034448140c005074501405c020482d40125240003494060b81d28a080128ed0104106a8100c45103880000d017540c60341064207100a142d040407443d070355850252400c041c0010180c03200c01051080d003110941d414010044104c112007030000c02c141d880da00800f900c01004003500001e143c030755913030851741c01600001151000c154162044c0c0004080940d000e000e652800d0711398801070241d4400e00d804a8841004e02d050f0381b112203410000001044c070000b0388904090b0781e0007058101d011800c880c548491082d0003107902c1e180445400c240d4009008200d11810404100d8042c801e50008986081c0014181d03c01030390f00307002030100d841e55541d40031565042d203000c00d40340c08444890308080c145031030f036040e010039404100d00740c600000f911018440f507a1841c01c1a0301b4450300004458800020486504000301d0303d01c000c04036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 77516881 1250 77515631 77515651
    0xf020d0c020d080402010e04150504090b0906070c0b0c0c0c030a050c010210110708090a0801020a02030a03050105060c0a06050613060b0405031608030d050604091a0105151305061312050105 83
    0x2d29801c0c0702607400c00002d40c1c0c040c0c00704485040000b071342e16098008010380d4100c0c4032107024856850000ca0141c41c0a0501201c41c00900d20070401c2e210340070080d065000e4481d01d01070703c0d44006034540c445804d00107032001409000004680c109041c00308041c1c9040e0f5800303412a0311901c85824059119010524654010300941c8080490b82829010b100d80c0080708607125031900b04d040e660442c3d5a071202e03001c181c018526440000c4c4186003072001c2c140318040e603000355646180340d42c8010111003050b0070491041400b4401c081c0c0b0440002200c844443d03101d840000c01e80c9030f40002400382655081e20202003420404007140c6081d00700e02a101301c6000303900b00d0b00009446060202424182d005012030359100340046103c446c4150000c0d5000138010304002005100c0751030b54004400c8451100f15651580401003199082040c1c0c035001c0380380c60031503113801c002d1800c91030104400d4504ca85803240c1c102080e80f6201c440f1655801001f005c10148a4030b45d028107140441c0a0407048a002401d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 77517987 1106 77516881 77516893
    0x20c04020c0c180a050a110913150906080c01020705010215042f0109060809030403060e070b19090506130608100308132402120307030f020d0c02 64
    0x843e000950b421040c501d02400d41e0320a480c409003d8181e0380d40307054100a202c00d09002656920f00044a000d10100e0000e039000001e444c1501ca002c1c44401000800142d0202c140e200c201100c002c0015281a40c200c0c80043e030b1a16407510405000d42c000f070f490029441e42031410194040d10400407904001001903803989850748480c4065502001010003109035a0001c084c1c1000f4405494101141d2a042d46c13455124003940c40001c00c220b4a40c03542940c0340e0420301681c00980142c01910340c031101c0040104110401311001c02000c14080400894503040c040101d61680b44055500703070940c2d1030800212400342c0018880800640003040c007000143d58100149061000042c54442143c148140b0a400315000101c5500e0b001562a505800a401082080740e80382807601168482d03803104002d402070510420100381345440000e80c400c041103194842c40300d02c250b550032202 = true := by decide +kernel

theorem cover : BRFrame.Cov 77338131 77517987 := by
  have h0 := BRFrame.cov_init 77338131
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77338131 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 77338131 ≤ n) (h2 : n < 77517987) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
