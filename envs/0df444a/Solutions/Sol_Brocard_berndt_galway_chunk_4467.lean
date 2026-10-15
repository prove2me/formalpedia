-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4467
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:42:31.426486+00:00
-- url     : https://prove2.me/submissions/6592df60-3b03-4996-9412-b08bc90b4e93

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 803237410 ≤ n < 803417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 803238660 1250 803237410 803237467
    0xd0207060207050f091504020a1101050a061202010507061d101506080612030f04090c0f0e0306160516030512090102090a0e04020f04090c060e06030c0a05090114 71
    0x9001412510009444048410150002e00301110f45410310941c1c0000030201034482ca200b180c0900369495610041c80d422140b80d0f14034121a0b2803d135070f9425150301421038204d031420032800340036003510403d40c00381d107a90909103580d0303c0016180c04805001b268801c0011100d180c0310004101c1070125480048032103825040111480e41c3c8480000210240600000038600100040060070181030030003e083c1d1070001c032400d10550100403049076125400c4002c0e42e03605c41200c100c2c80c0344c101d041c4a403615042d040003660380040d5400303e07695030700013000c2c5a00014040050301000b802142112341140018901c5202c0c91440d00b03000c0d003540d20014039041100c4219001400212040c800d6a01d6000e0052000303000501e41b41da0201c41c05030140c8180d80c8400c0091f50f05680b56120712a0148107403040e5000385c40b640c0390070000b410240d048000d007400761208004200300c201c005022151900310a0403c41d4640e668031004a806496a44008580d11030006400c501300051001c043c150a02610 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 803239910 1250 803238660 803238673
    0x1020d030e030405040e03040b0a0215151807030204033f020d0c03031415090105060a0210050a060f08010e0118030512041511030a050106021203151507050d02 70
    0x28044044403086400058160030520042c4042c1c6002c1c5c02ca03202c8001d550049904164403101d0302c0f50356a00c14200c1c080540d1110440402ea020140c403034652051031090301c2d019100030f60000c07440003141c50345005a952201030005580f180260305a50265810500c3c840300500c01c8a0649060000712050409645034142207e660813140400c40300c020f1407650103460007610501f800d48ea542081c0300110185503d45032032407008040c140f4003034402c4003c44110003108181d40203002e01d805068000f640240c100f00001491a600052882c450029240c0001004c0d5240f10b0144002d0071140c01081250104000020340d03100d054202e098040c4521008020408105524440e14100004000c0200d1018046100b01e100d1075150903500601440d20400e1071507403d6090003c0355418940340e00e011101100b800070b110b82d58032410340501820300086c05101450002c0920900004010354080440302480c0c0001d92542c15907a500c60b00041c0c0c0007612a006490101d48411529214000500c20344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 803241160 1250 803239910 803239933
    0x120d0201140c0406021207080f0d0c0e0f1005070c03020a0e09010b010c020d080d0609051602120a080117150a0e0f0a0c090c0e0307030308270c040c0215040c050102 72
    0x202c08440440381d454000b00003280300c0101c440351030f070010001035400d07400c14440d582920304210010121014002c100113000884200d0141a100e1000c4a07036024000412800c0c5071502d036901040b803000c141d403c06940700c12682c40c00401ca10741a0308003c2d004110700310300082c604d503440f5505000d1000340009200e8040c401c001111101003215000e035000c1640800800402d900b000204000c0c465850007040c1561542a4002500c03002e40d4110041d109501c07011a40301e5041c80600d0320340700c04c0e0744182c1c9080803031940185000018011120040301050010946d41820005940024144501c40300c49140001800c0f00400b42a207542c801c6004910241c030000c3d0001c51622800ba07808072204aa83e0305200000000f400350020042c01d0110201280e2000e036030420484000314801d550b00542c52401041c0e184800000081c0280b07800000a506140a00089240b0a00013400e4800052450b56407408a00e020790a00d000c4100180100c00d000511421b44002d805844082c0c0071290030a07001d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 803242410 1250 803241160 803241181
    0x31202030717090102070510030e0601150207270e0708011a040606030902030a2a03081806040303120b012f010e0a11100504180b0f01030207080711120d020114 70
    0x110484613006800800e420700040c41c2c25590a004900070b803030002411406112440d152007420303000025103104800403000090703810042500501700c0440c909940040d2a0031000d507032089062000109900d81d03120600c450001c100d0a4010801880288030b1b01c41d00182a002081122078094055800e180c408102a4041d000c0c0001099010340201001c4040e84c80d00b200100b0a20741421960840e0031078010f107484500c141c81c001d580144000c070760319010b090807c083c030280d88222501401041c001000482c3d0044e0040303118068a40000c200810303400012a09901c2c9040e100d400d0702d41e015001c1c901e81c2c51b504241200080340c0b10003046441c2c2414102652666850b000070194004020f400e0400e051820b000341c21441207040483c02c0070740341c4848242c001c0078240c0070b80f0030503500c0203200c9191070440c2080d0080d16080c202145030060a4840c200c80d03200e01400605400708403020310750325440e1117400c407041c0d00703074481660300308000124000e0180c650394842490041801e4007040600c0302c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 803243660 1250 803242410 803242417
    0x304120318020409050709060b03061c172514060106050f0403020f040204031211250608100302060a020f062202150702181e010f0b070606031202030717 67
    0x504940c01c014010265007000054140d00e6070484040c014203600040480842c00b946014000c0802100d80b0391511000f8001512a00e0100c60005124254444080b401c10400f000740803945245550740d03540c60b48030b82016004030048103001c40c0c05a07840d8009010408003e00340f032072107050544d031107039a0f10441104e850180c0d009000c40d104003000100700500d042d14440136a942c01900c0075003020342d80d0321160021024444400080b138100031600305000030a00c80182001008041000c2c0c100540110031010307607240c0100b1040c00302c044040390340c046482200000455008103019607170903081300c0003500e40300c040d00c200707800380302e040c0218400c64130031040c01c20580b240040401c0020202d4082054481c0800e941d50a41d40040016401580b034807103030030a544c0b00440c61012030342064905d4403002c102d100705c1c50503003405400051202407043c45880c82201e01e903151300c648420442c14140003c3c145644018103c080c00010000315a0b004000381c88990300980000040030740c0406079494920 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 803244910 1250 803243660 803243681
    0x90d0e0303160303090209011e06050406120203060316030507080705011d06130b0301031b090c020a291e0601020d080604051b1201140f091603091703041203 69
    0x10400d001c003080a100c0800d0b00c10b600da000b8980440e1241c203680208000030320a0b04092081641c0340307002610b01020142c0d5100824a910700185841d02d005801031040441c40c012400c0310703070004040348003a1b4040224001080da081e500250040d0f40e0319003a0742d40d8217a032165030082e00806800041642c052070340241104881e94000c0c406140d00030400800c3d500c4075010180800c060301000c04c0b903904036070185001c1c501c2100580741c1804486504580d5580980c001d80005003491403003003e850740450100d40895020311a6106c605281c5041411070b00c40b0131000402001080801c90058100c804205d110205107001140e26101d0b080120b80760006c8404e02401325003102d002c210141444d600c0a40d10900341c07010801e031141d526100e040564003c1308441584045e11006024000b000a89406642c0d001c86030707a60b5112940c00030400c4100010122a0b024040000a00606000e50404914694000d64440b14074002c1c01c18803030703190002c2c0e400341d403004d525420b03d0307543c0c0d0b00910400d00b40740c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 803246160 1250 803244910 803244913
    0x20a081008012c0715030f27060b0f03010c030209040e211309182d02130e0304081c030c1b020409020405091e010510062a0b090d0e03 59
    0x2020344248204114920312410019845881d50000300300c0600421060045a90f0746c021030280440100c60066491030b07140c0d05100400a5075104c012000380d0407055086034050004691495810b0004070000075400703c641c2c155007030440704c2701002d615900605440744201d13420011484040c44041da00c210350310103603011801540480e200200c5844c06070003034411007030b0b12070301c002d4513450800c0a4030460ba244103c10300d1001100e100301314280092030030041d06c2c11300004418081c85000183d1210321800a801243d183d040c0a8007207160b0703000103110179030480840c0d59580c0e071207415660301c070294080603a10b003004110280703205200e4000d1184031003260340c03015051648519000d504504c1003500300d80c0140d0741c201d010010380b1a8010b40c2e1061941c8800303000c050b20580da4054010201c3c040103e8103914000070408841c400210300015240c0c24508560080c2d00700105891950303190b0070448100d440f002a09041007003502c4440d100301c40b88030598a04628511058841c9038129127000e516 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 803247410 1250 803246160 803246201
    0x3060f060b070201081b0703030e0c0108161107031a010501140f04051e0a06030204081e06040605100306050f07110f060718030b0a061401080705040905040213020a08100801 76
    0x156100d5a03040c0d4004842646c010110301424103e10616446804101c002c40d13203e20f0341c40c0c20002c003405030b0f80c0758034030070309044603d031034904030412405915134541001d014070b03415120841d01e42005442c02550340129440c2104c040500340c00c0c1d0390502403003107a001400c03e10405010790a075a081c0c4e90310340c032041c100301e083c00d041204100d9082d81c100c1d0401c500154450100c0440d980e503440d4500184034071b803030060752039080410071410b101c607040d0b1a014040305101322501c1007400240003944940c0112000031103071a440b112445c400da0562014150506080c140880c1072409040540141e5042e1185404618400e29494880002101c03407030043d0403000004003031034040c021400c80010f4a1882100e807a4613075641000c0c92405651010703e8030b58925092095440c501e080b141c0a00090800011600d0310103001011361049006d0000300e0f6450300c1c045011511440c614442c02141c4101c199154a804140104107a4044412040400b41510001018481840740a0b040288129855003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 803248660 1250 803247410 803247413
    0xc12010f0311220f090b0106020a230307050307050f010c0305012321070f0905190213030c060807080c031e09031201060f020d08060913050c04021303060f060b07 71
    0x9441150b40030b561018000710f4010a0002c083c0700300728078141e2161000030f501c400c600300300d20305c00070580152040d50721802504012035181000d200344a074041e4503d900300300100e000c0300c4c194001ca0400800c10322003c601d041c10408041340a004243e55400200040108040708800b540c2080c450680e04140ca015101005540f42c00030080700b80000d0082c40b17042e12422090000148002054011504622024450020300c840428002d1101c44001d211900300741c906030031641007003143c001400d0703030001d03400409d9000e141804000716084981c40b41003039a030300400351551104503000d00010341c2c000005101d0001034400d807801244240d16140e60b1004c184003166603a08054503007152407006105c410080b0b840302c05018041e00070359403201840d103203808002c0e140400ca080304605016003801080301c1a1204d0005e55406109030261840807102c40c2025424904040035540d0031900010f003008003c8400650407040307900c0703a0820040c440c94039218004683d903502400c05052401c108210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 803249910 1250 803248660 803248669
    0x30109050609270a330c090e100906030602030a0510060504050f01050c07080307152f1b030c120705150402030f07080625090911040801050c12010f0311 67
    0x101c0d00e40c541c00841e07074813082c1500d8040c1d03900c0b107200030540e1142d4806000c032424801c20103000c0700c5440d941014040b14078030f04805460050705011750b00d00395415500080a4020401c00175000b441448000c004441d01c3e0305052010354802c0b41e100b007401d8240030100d03640c140d030024044115101542e81600b414281020000d03000f5a20300c185040010500c002c0321041028403968005150300002146d403a04985400740224241c500c01c40180d92402013440c2034600841c156140d1003803607045074942520090181c0086000301c208113006e802038446003d5000100100806201e04000203c95062038244450302c2c5074400c03407500074030940101c00100181a000c407021034106100800b680c02c14020340c100c4a1401860303a0020242d81c2c010020b10100c0c0c0ca03e5898030001e0028040f001d0a604403000000e0900d06552180c5241c459070340540203224403504050320013034102c00b0000e125a0400020320300303594200072101e0101201d080000100c10920002c840b044950003007501c000005a0400c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 803251160 1250 803249910 803249971
    0x1d0309011409040908040906060e06031302010e040e0a050d020f2b020c150a180501051204053a18140307030b24090c070b0a0b0d0305030109050609 65
    0x2a600282c44140134000212440c0281003d05480380c00003886910344140101100d01c171051050243c01c08105110804c0f29910b01e0000d215021f080c0011011a143c0c007280c014a00100512001e004a00909040040c08501c008000100c1e5084644412008442c283c6600789001c13000300000080809021206081c1d1580c0c1d1120000d0040d9030003007040704041000b0120b08440ba03200035000081c900c29242e040142e82003181001c2c1c84c05c9948038101000a80315121762200300c48001c4200700020b0401500300301d030710720040ba2014080151044400342c2ca07200a07003269881014003402546150440c03141c07080010110034110041180c0e4600b0520030f0104907040300d040e03014000e0388400700108400d4016a1300800060381100124500c0001e00c0b940c0907a01c081051141185200303101c03020008c1307829241910780101c0840502d40741d06007402c00819118148540003e03c000298042c940c000e00030b50b04071100c1d05410b101c0c0303035642e0080040e0010211215001191050303175444a041c4540c201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 803252410 1250 803251160 803251177
    0x1b1801180504050106090e010b34080a0309060f0b090c0f070516080c0108060a0b0d09050607020a0c09090201050a0309110a240801140f13020c011d03090114 69
    0x403003800c90703150404181901c2d02608843c021940c0702408202c0d100d4a1b81d0002c0c01003244c00c19450078007000720305040d01c1d04804020b08242503a0504600d420589041000c03600c9a84044091b68880950402401400c02404144c0d01107142c1440e05118030701c503004182216000620252407981c40c4021006280c202e0b013032125600b9000c1c040c00f00068010007005020980318040041a103241c00c4107140703001c1d2601c20f12810030030f03c00300b03101070781c2c6414041100703a071480c03424251141000d07001600180038501d001783c103900c1000300f4401001d401060140c502c0c1c0c003401003a4513072502c0f00444000c2d1481860001d0028608005000a50348664000010f1601c04c01c04026035480070000504c038113a003504000304903003003668880d014500c030702e010440c040814149099290314060080180c410b81c1c1100c940600344241c0b500106580b000c9800021603400c0808640300d1400da083c440c000c21030b10401001d81c00020000c0c071240300002041c1c0e422164142c2d621410280418051003050f000341c1617 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 803253660 1250 803252410 803252447
    0x10b0a0507050a061a0d0b070e0f030a060606080903070f020913061a03010c1103040306020a031e0615031b030c020c1011060703021c0b030312010b031b1801 69
    0x14000002e5061042100160290001041d080c03d081e042c1c0e409091101e48052080c00c8042c0e00380000351205076059400351803410310707030005440307107000c1140102c408203442d50600481981c4000c003c0142c5c0203e00f9507995968084246d5981a90199240320320320010300500c0318405090010b00e448004654880d00315001c06803581d40b29a9141c094400c4603c8160070780008101100a0b403c0c01d01c10104102001d10b819607030041a508220384034442c038000034144540000700510924040c0e004007110300c002e06a802501c0800c500c02a00900c0036000d5080600480c01c141e00c5041d1290182d55543d8a14040500300c4040400c1c0550007400c20800d41019030040710310082d92580e900c0e01643c0351101d1520340318514030313032422000d06101e0002c040900749441030001e0281400381e4192a00c000f40c00440c000740001309007002902c1d6015000740300380340c10004000450005d903840b000d1400740400c031801c94200c0e06d0060b100461070140d89042602052943c2c1c0c004519032103100400d980c41203c54 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 803254910 1250 803253660 803253667
    0x303051801030f020720010801060c080d09051f0f06051503090c1c020a12030206060603072d02010b0306061e0a0314011d0703020306160201020d06170705010e030303010b0a05 77
    0x59907070f0305a0b00000802d0311039005401c0c6001c680f50103403004c20268402442c0564540d8100b00d806400d000c810365026241034401b080302074032180c46038401480340c6c1c1c1090444610080075121051098141e10641a00e9800c10580080540d0903003c1c1e84280d400c002c1142c114840300000040a91f04010040040f91140111340901c50326240a02c0c8000d9101c9002c461004425005010b01d8000755030180c0f102050300b030100c80100b80d0104040303410510032200030380c0c0c070344611004072048004200d2100c0070020300005480605202c240404101c490768000f80301e01402e80c0c04145c0c0703030f200403644141c01c080c00000c00721804a00303105090144100400e41d0604039141d45a03e41c0c00d804480c1031180b140e540d4140e0072819007085050140031518a401840883c1c01d507408640c840380302a003070300c1032a40084044101035001790144d80210321440c20421a641c0d444201c0651400480a8118503028a50300030481e03500c00d20010b490048007800a5195034605035518005074020144041084000d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 803256160 1250 803254910 803254931
    0xf100908030601110102070605160e060702030a02101e090e010902090906010f0203071704030528060c03062c18070b030402010509061323010f0f0908030d0e060c04030305180103 78
    0x348181e50285d1031041010b840850142b00c043c000580d43e4a0b640d20400c003d102d03010040e90006040b1070354980c103444d4080c14210f1050103072217451070340244002e821803e1501c2004194490000c2080b0f86911a03410000e0740e890071031000304e1090748003d940004600c3c0c000350480d4015901d0b08050906881180e1404941e07440f403202c01d0706480800b88500c000058100140682009200182e030002c041c4001c2d00703040c516164a84950400000b080b00b40c071000a28100c0740254005001441d00e40b146c4864004503116941e42144800807041000f400784020030000c0c00d01c801e11800c402040c8004094090030441c1c02c040a80000300203d04000003008900807940302c550141010007103510b82221460f0400c03c0d401c0702c1d180004030000284410901d1b031000781c2e0741709040c00440032030b600300f200040d81018012121340340c9036000080d2030b22000404030f550080607880082800c0c0400150740007600c3c2d032042040144030320f11001c0c000980500481010010f07040300b80402d200e050400042d0b81080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 803257410 1250 803256160 803256173
    0xe22020a0203040f0512070608060609090702011b031803050d060f0326090a050f0a05090c0c060c030601080f100909060608210318150103050f10090803060111010207 73
    0x220340c006006030400b02d0104861020b200c060f0014000480f034000f0390080b0103d00d1581c9002d50b00c900030800480381c010030700e075460703410480c1c91500026000c0c60041ca09560068060b2103094480d00f5450000c0558102c2d592081c82803d0ba09581c518460304c80c0c1405480031030302c0380c003e40c0b04c24002541d0760000142c000000031b404070045214450086081656100d000c0c200742002002d010790f04420007007060250b541003c550706a820880700001a600024081549002d02d60800750b001031410090080c0c1592250251038134091103011a08250303128050504240410384105010a62980215440005019003550b03c07080a03008a1031803640d0352007001c1907a50303964080d034156075909814400300c0424068400301c41d20392030642d8005540d00741301500318480180449071000c2c07140d03001c140816050111054203040307142a4082940c50b81001502c0311601c9000d16814814400503810003000c6000b1210040d4111000c41d003903659030801900e000c407156200150656003002114001b654 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 803258660 1250 803257410 803257417
    0x7061409030d1e03020c0309040c02100519060f1805060312040b12060402031b0f0708040905010603270f0f0b18101811150307080406050a020405010e2202 68
    0x3225039a0700103840700030f5400451082c4035407100042500412801401701c800101f03e80c1e0100c3c05840c009071460350f0840032424040968140f144081c140750610910300c90400c038085111455117010802c4550b181000c00d00d07040c8138400e4038029503c405000c007a04525620070b540c1302d04040c1c291901c18040010b1500c03030303912030380003200d42a201080d80310074a404415000c0e44071034107403021032840c00e00207481140b0780380c64240445000700000f076840540d600c1106407008a50b21000051300c0340d8842071000003070031090003440006440e101008010300724120700000500300e2411040c10194240d01d54103401000d68400f501c2c04541c10040b20001502440e105108100000024074500903d110841c00c20007202c00054115080980814074180924600405198030101c002507000282c0086150080c400f46e0304c1c0d80221001c410404456000303032a6034841c1d17225420400903a903604000208900480c01020b00003564402201003c0c107115030700c85048803035540030f003c04400e1070000c0c606991 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 803259910 1250 803258660 803258683
    0x608030403032703020d0b10180207060b0d0320010207120c0506070801080d18150203030405010c0c0f140111040f14090702060708070512070f200706140903 69
    0x340441490b0800764000d000440000034100448903c3c40d1a50300000c08500010070301422038890440418603140600c02300000420390b40146034410300c160041d0700020340000000b521041d0810b25041c900340303400c10044801035450b84450a40c1c2c6100070852401c2014181010348543d400c0140c08003027580d280380c42c00702011980d944812080c80340ba240d410418003402c3c1c1c030180007100005114181011425203105a541d2400f500e28803071034a82201003103a10b50040c18158008044110503d501100552141d0b001d4402404030040200d4126070300e20080001504080d241c00c040c1d00040d104423400c83d942021b40001045c04107180300741110650060303004281c20b140360001000f130382d4250020201d103c2000c4402481c0d84c9081d181c00780d00c8500c010590300800c0383c41c07030001c2c80301030140e000e84164110301c060303620541c5000c200203041c0d40500b2040c50049158890440c04009001c1190500c06101e0800351040c1c42c5000403d480c18560b00c0c8111013244011b2110291540b0704001e42100749 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 803261160 1250 803259910 803259917
    0x1b030c0f08160302090604020c152511070509130b1f0e040b151c0302070614070201020d1d03011109041b0c020d0f05160906140a1206060803040303 65
    0x40c5081901d034601800c8000100d05039225200400c0541c1d26000050340c4a0400c3e0b0340965220030092a41d403c0003544041916400050b600380b0921500a08030b400c82c0904644e030301d03a00c0510b110415511101c0e2024850100c0d449001c0034800c1c0c0c149230704906e4110186401c8410008403594440340010310456420307001400c0001d08410028041500d40c008018203815441c10781080e8a41c3c04803824010300c84021225001c481c0700854aa03585101503034090b14000380c50b04030a07850000d458001604c40d01e0300186020a040302180c148004460480343d058008003014031715a0b07000c2d035040440e0742e80d420485c80e042542400c20303103080c0502610070001c0c3d40d01681d150341840c10001100c015864143c3e140400d484006412500f01c0c1600040c40d80489410005541c07524001e0103e803448600204103000310400f0b10b07001d800d00040130081e81c1e14a40c0500105d5107070311549400c0103036080c0c0c859200311103502c01c02c40681440c401411003400f441d00400c1a42e10341000b01e19540c03080e0f0048001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 803262410 1250 803261160 803261189
    0x160b1315020a06050615070b040c0e0c03040c050a050619020f014101031106070816020102071509091508070e10050d0c05040c23070302011b050301031b030c 69
    0x4000e4184a070700e9000071704568131b811100e00030030090b40d0760151200080175101c2c0080800c00f8010326501600040003800841c1c6010300d0414a20314850700144c0341202c00c600c0440020899241801d0b6034000e541d0050501c6013480a4889022507aa070301e03500500550181c4215440410400e000d01c002c03021020b040303032241c004c0e0458022050300009603110a83c4064001440d0061900300003181100d40080011302120160000204c41d8800c0f044010410000082c5071150403000d0403850b0003c0d0300076001e0b101150b1740ea090f40060000c01c01e0030a000680460000e01075003585038411011914400d140c40011502da0400701d1800c0210342040303010900c1c04007000648803204a1007030252005851400791070400da91002281c8155000c1d0034880c980341c905e450f044e40d01c1a11110200b400d1001c0c0401c5440081c1c6015075951f1004000f64015428204942c24400d00c1721550a15620160b40b21461607103076407259044804801d002b044c8681c1240c8001011880c282c8006001e011070403034120310f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 803263660 1250 803262410 803262413
    0x15091106031f080c060906180603040f050c03010525051c06171906020d0e10050a1103010311090405070308030c0d140402030c09090307060204031211160b1315020a 72
    0x800076410f41c44025540c0c01455545000d403122401e03207840c12815108540c51b4294019040c07000c01c203000341c040d0880c42c044104414040e03800900700328140210709071285d1085038001c1c5070980d40f08032005650036040c08104594800d4842c08940c406825152032428100489010303070000c0c402d90826940d0030789488090100340105000c003c00016010020482d86c42c1840e8612400c200228024006680c0401c0010001b500b94000e40f0050a141080e68908901c40d8601c0d0000c0005840180942e40b6161021200c61960800c90f4103882d0003010145848840504000c0040c0000341704685900600c1800000a0300b94406140a0308001c0e4180e503d520900d901001120741560f9200c40c4116448180300140e1400301c3c40940e1328000740c501001c0d030740c0c5800c403141c590310608200411242c4000b40c00418040280c0c41e66030f544889554140d0b04c908400c0c85150340f0000c1e5000c100d01314a50034810403030440700400030228202485c2c6080b85040e650840a8000c10840344c1c0c205c05038000584060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 803264910 1250 803263660 803263711
    0x5060a05070b0f040b0c040e0136091b14060903160f080d080705090f281a0903030a1d120c131b120b030307030c1a01031509110603 58
    0x90313110390f0300801d0a00381440c12030701301000302061241030018503407008600c0000d00110ac441c4091620190556001c0c4540d143d50300c001c1c98011004d550242840103103500403410841c14004980129620400542c014010000c1c940d00c4500c0c1030b94140b185100c0211a020048043c0c4002c1c21490400b21000b45400c0d40f160421328501c00b440200315402080002003500081035464040381650745070b41c111580004501e401d50704201840035840080e4682d107602981180321000d071680755005c20200541d01100c040b00303005980e50036034150001d01004990328890110080c01006414215a4014021007ca03180300394081e01e04803150096880c0b01014200240740b1440002401c00402c503107240c05001e5802050b6540e101d00c01c1080324540014400165040f050628170300030181c80d9036001c42d103000f03071103a1034003038086425521060003841c1c04d00c4010000c034100d1360443d070414121844104440014404c20804984081c000d00d114610340d00c881014502c2590220401c01054001d0280d91 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 803266160 1250 803264910 803264933
    0x10e06070c1806080c090a09030c05030414010909020705070605070c03020d080301090b01090302031e10020a0f02071521021308030d06090b13022a0a061103040c05060a05070b0f04 79
    0x88a030f00010821000c1e03250702900b01d0f408601f01c1c5000a05140d603186c12140354402c4540580305200c0400c022903041d40e09408060301181c04d89681420b542e59140003c142d002d0b601009d492900b041c9400c200a071301440c001c04000c1e1181150940154590740014449601c80c4000d58001b24080014800c030503031071040c000c003040b003420600c40940ca542e0000340e840171002c890f4807204414507954008610704100c64034504550740303025501c0d10003d1100500310384d1a41404001481543c0b03000807003991164188010010907500c40c1542400f05454980d08220061700c100100d508116044090070207a45c1e0402a02110f4095a80d0f0f50464515100f03840f100d4210f1048640740810300c070003955540d080d62607007012800c405a1940c6c0c0d005494002511200190346024108024040e41c00d40080340045480c1c0c8604010051544000b80c010402d000844004291801c0800d090000d4903004004e8805281a80342844c6440c0071940c5400c02d022069075160032040210051008020b00104032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 803267410 1250 803266160 803266169
    0x1b0a0c14161d010311120102040801051501080103050c01030515040c080402041d0a0b0405010e060907260a02040e0f10020d0c02030f0a08070905120a050723010e06070c1806 76
    0x8001c03030301d10500c0303000000c02d5041c800200051290554080c09032500010740508200600085480300d035582c18031030190a044581040301da0700403c503264158000e02d20a030582e41c001004026440f402c000540040001411511090202400c0741502d03603a00d000c0c844500b405a910490141842d1042c00f05495039500d0b14807081a504c0c02c5040c44510024203411070b140c000642e28090b031520b0410341e0042818003001400d034044c0c1410401c0c1d01000050007412506070f405000c1c4c000c40c3c1c60340100b030000c0c1d91f001440304640120117001d000d4581608101e00006980c0159160821742c011002c1c47c268081d40c009400c55004507604032243c02c10700c0f0b14000d2052030300281d4a41386030a0010405449002c6424040c1f210300710100d80c0581c85a0380c6000070f0000505290020351402c1c54403940c8030303880041100c0d50710418a0200b1026142c1c0d100001c801918401d00d0a00000e9200543d04403101c0100a9003100f0103200304400b180c00001840010b05403e1030781c941440035003070401c0c240d4019400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 803268660 1250 803267410 803267429
    0xc11070605070308060a121a070306060c0803040c0915092004030b0a0905011107150c0509060c010e030301030804050a1e03061e0c03020a171b0a0c1416 67
    0x404101603500103049800e50b581c14604000c5980c2d03440c0c0040c4500285401c0401c80f00703109545841001010420840c4501201c8003505042d81d03000c0c0c0403016100d180c050345d4009440c820390a0300007400880a5a041486090b510300016100c100844c210b801586c040b003400102c02c3d4040083c0b940d24410082a6542d01072aa0400310215600b59294491840020260310708940050001e20f0240e110040c4558800c00a20640143c00ca40c501143c0101c0030030b85060314202410440c0c2507a901c600800003500e521443d040c0030142c0c0402505401c144000201c4e5500c0342ea4590f402c0c9414001540654071900b0400d4407141080e05101c5450b0b000d80003c180101d80e080003109009010404004503230b80254042582d03014450f85802240c26a10307010340060070200780c0302485416402901901a1556400d07080b0900741c6180105d1140030341d404103102c054a4581e11301612920000e10401c00c04e810800708040c4542e60305000080ca240c88400f01d41c008025110442c5c0f50740c158540100003100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 803269910 1250 803268660 803268673
    0x6040e0a0b1006090320010c05060703090303060509090a08090f0315101a0306061e030703050a0b0f01051c0b0d03020601030303140403020c0108090c04020417010605180114030a150c11 81
    0x60794122540c0140509000c1b07100024000d815a80c41100040d0701aa4481e0548125040c140c5001c1d001c0e000c1144100e008c20b040007030109141c202503200d18421101c0400610003072240d9107850300f06a0105025a4100541322600c0c64541c42c00c03c604166444002d201a105250803900c502c4440c00c0c3d0340142f4004006d415003035014181c08025241c012004590302a641d140a107079556030410341c02d01682000401008010700c50342c0540c0201d100d00c02c101c20038044040c0c010200010142c0e0403c269002c02c03414403e0107100c2c0424080c1d520f003110514000540070904400280304540300640c1240141e000b240140109070b410b00690805006013582d502260510f943c0107511031350200400e9040024400010b2403281040000b03441101c2c1c0540700315950b640301e501001080c40720869081c0c8560800c000044e050510410405616904a00301c1d1040d90a08458414030510051030390740c1842042034031804110170060f80d00743c0d50600c00002801c0811031070080c003000140000d40c829900210b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 803271160 1250 803269910 803269913
    0xc06132109080d0801031a060315010909060c02160306050a09021807020106050a06050307051309060605040311030601050904080a030905241005060d0c02010603060e07061701050607020906040e0a0b10060903 91
    0x704c42c07c06108a0102d0107503680d90709030101f890300307500900038601c2c000024000100c42009a100c401c030310340154014130031415140c006070396070f6100421034940454400d80400c0449c5180c0d101a81111084001092100c12600025103d004240151403c408400140102d158091103100e00400c42a110520400d00d0804042c105010040140040c80301c0040d4003e0520305080010000e40304001080021755110000140582c0240c0811030702e010941f24150481e01c2e002070f1a03412114020084041071b41e0701e50b00c004894215042610900d071b250300b1860700090080c41032421011070002c2c0b01e03c3d04180c81f01d090240c400040c1c9240007905280d1070510041d00c0e030404581d4610760b10000442c40c1214548101d005042642c401b0307080500c1c0100041c40c0200c041118800c0321300030f0703407220464a40c2c168902c0d1009130078441c460b4002000c002410043c11b003802c419901c850018800142d1115a200560402440200440303291502e50108086034a0020880c03010340421700d004510b840c01c6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 803272410 1250 803271160 803271173
    0x7050916090603050a02072301230a0e150705120f090606270a05100602070b090118171e010b1c110a08070504050a020c06132109080d080103 62
    0x5002e42c504241d112000a0503034100394045440c807940c001c40c20078135006840b84450300111b095813001d00b207509002c09503204085083c0c00c100000103110840360291140c140f03440051000c0c1120100c24015510301507042c0010041162181c00d4a869a954a800f110810307001c46e0710003854001c40000d0711060103141c0600050803a4405030070303902c860001c04566031128032611a900e00e000b61082413810002c60b44045d820560242105004280045846031401d98895903a402402c980307030001e12860702c4940c442c0c0609054000c255407210301040c0c803111403882c08032403901c440c0c01c2984071800c0780c040c0480601c2c4854002c012a00204001c00c0034000040b003007000c41c82c0c0642c030940c0070500d500521265000e190850600140140340403941d4095140d00c410040c03052078811440c02c800181c80040b14000c842c40990264003401c001d80e02c4402004024003011000d55641041010822108554428604030030390700da00d41003d22860140e200d07240403e211954000c000c034001c01000001c10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 803273660 1250 803272410 803272427
    0x90609020a0f0810080a03020f0c090103080a180509011d07140706050a240e090d12020313080f0409060530011404030e090709030b0c1809010807050916 67
    0x41c1858400f10b6500d51051207146402e40b0782003e40203024100400d010103400050003103c5111001c29a00303580b4400c01001100242480080c02d507003000c10280c000d9a20403450a1143e10242016a801c0d03611580880e0f2200026040814000100d0303a0380d021000e511041035038007031014a01605a1305940d0a004014054070500070851500d40c8042521181583c00029000710305204592898610080320025401301e8071450b01d0303514801001c5803141c2c03001724000c07041d4515030315540e5488001c2e00c4a100250f0000749440800401038914000184424000705656a6001d00040d01d9508054004003110b9260307001a111342001c407801c0610b032000811020481c3c5c035545404008082d000c0a15014205901c007005030004a00c081004058100d00d40e001e1205040d22100403a0ba201c08007900c214026000140c40c014400c00021844000c03c001000526442e08010b2203030a0440c01045c28854213810106994104410a00990400440f49948204092441c82c02c03551240c42c06003000b41d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 803274910 1250 803273660 803273687
    0x5031c1407020103020403050a03091712030f09150a05102304020304021302030f070e09060f040e0a060e070602120f0915040302060c0d030e0703032124090609020a 72
    0x3102080c000c0641e0f000f50305403030095400600340c900c5c0000900e0024001211030103058401c14107041c0c000b50740c460014075032444a03031a441c01403554585000840704100c00a0012040c0e210780307a21414642a5030300601c1c05440040ba01160341d0811240141e0a60314a40008176007010081403440a000c07080161100c440096400580d251a00c0c008244042d02c02d420303c0240500010078040384250203040c02d4401e120b00d0744e500e041c0f05064010068496001e941480d80312100710f45010151410742c0c0400490400b503021150102c0301603031003400740c46001e88540c1080e00050390400400342c040c016202d80d400c90001ea1440d14038111b618281500450032180e000c4c1c0e6407060b040398196100021503010b590000c083d0740c0c483c160881119901c28110841c400020705021002040781d10000d5940d05890f8151507004441c504991141c60311240d810040c00113584440d40031100c2c0664021403818001225000000e442c10500c1503800c0d10150750080c543d03584100989201c0561010703503c40e214 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 803276160 1250 803274910 803274947
    0x70306090812010303090603140c0904050928170304080304080309030403022e031e0506060706020c0a0302070506070803010501271202090a05040f080c010e0d0905031c 74
    0x10012410096a540a800403180b084200d1400210070300d90000280412101190780c20b101c2800001c40940d405982901e544085c02c9040c091060b480c42d1540190303a110140404070381c1220b0900c2c020046244480c6c3c510038610000c0c042c00303400c0c400311803441000900c07140c104500e036041c5982d5140e86444000c102418001010010904028043c4121001075800500c0303140c1040d400402c030181a8030054a11800164100c250121240203005841c403000204550b40b28072800d8041c00c02c050300340201400e40c040720030010700340021002e101801c8a080700030300412841c1424038010b403030204541c01c034a11404003445100300055104084a05513142864401c5500000001452810746100c1c5491880c0c0860741e000301c0c070041c4c214130061701507000f00d9040c021521462008800c660042e51302600911004040341e01103001c03800141902d5840b440001050312010203c0c1d42400c400c4a401c01c005403040c60100440e150400c2065514800b594a40b42c000784003003806040b14008200c07840f0031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 803277410 1250 803276160 803276171
    0x60d15050406141e0a060f02010e0c01120f020d020309010912140a0e010c06050103060b240307030b010c0c03030804032c0906041410051002031309090606050310090201031d070306 79
    0x6051500c22450b04c115010307000311095a00d404000e84010000c03468034005610b0b000882d60910400120905051010b03110031541c551180d0881014001000c3c1c400d038010340070800400e03080c0d4903100561168072200000540482c4525024410703c036020b0024040109004460515403110740441c1c06150362030404451074284580142d4070904025406080382d49801d00000c1440b910380c0260300350f04800ca4202165941c0305802074519407240c451811031000900000704064020341c00441c0d01801410141016280340e0703a85000c5403c02d400450000c1c00c0d401c148403c060b04a142d400003d0040202c803031001d0900e0140411154a801c0b905109994000218049443ea60300210052010781d4034080700b032034410000030f0040138600c19503008004160b42c11903114404070944243d001c01c404d5255074185014505005828521002d83d0b00703503654100005c86681c100054104560300e180f0100308442c240c00094112640c0e444902c03480080714180e041c100f90085800b4043da640b08100064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 803278660 1250 803277410 803277439
    0x13050d1701050f0a080d0801030203070506130306180f03030b0112020f03070807111e37030905041a0a0f0f090f02040801060f0f09020405010c030c11060d1505040614 73
    0x180e004c83e41c04507046014125030300d16000e034044a1981a00c0c002c1d4115000b140c0d9510511825100c0c103da80702d408400032106000003038103030308621030215540d400345000d446547c5460380c21004018044010964030500c40c0c4071941c1100040d940000301003021410560348040246403888000e05ca00104640500050300c481e01440b0448908040c0300110b50044040344002c41c030300038080103042031038480c1c90400f02c400001c203031820113542c2010076016080007010300b034404081c0003013904409001001e240800c0b0340d2218803603049101d40441149060f00301980500c4002c50cd240c008901049040c082440442c040c030504104465100e81c0c00600484880c5860740203000300c0c0c02c401088c1d420848000394120240c843c12098071815003c40d481c56640e034400708128401d41c03207114007286000c0030304030120740074100c007002d0580280f290902600030350001a509034071208481d548107949510550f2010b084400c810040e100030340301009110308103580d00219a0141d20403510400351441a0320 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 803279910 1250 803278660 803278669
    0x10c0308062719020a170703110f09030f0303040f0314071b0905060d02090606130b070507030209160c02010806010c05010c020f120c0c060913020a0f0e010e090604110f0313050d1701050f 82
    0x40840441501642b52060342000400d19480411010300c0b03841507010181c3c0513180031045030300595001403203003041c00703107a42d0540d01031140390304062000f8801e0117590040358030604000702541148800c0c600490134950840b044484c05000c090040c80600c58540040c3c84c1d0f04070180d0416411030344c140d1640504034050072041d8a90300081b18000380482d0203020854005240c0003640d100b20740444a40c0c0d505181d411401c1c600700b88410001325400300140155000b080aa83c0114041c03401030352a0303007a0b48415003901c6032118840016070100d8207441910f0030506c51038514580088a00e8680105503146c41d40e6181c0c0c2e039140300d01c100c50010762105195196054802c4519127030034155281c0714201009465002e100701500c0c00300d041038200000e03070b61055000081e00d1030024040b01c09510b800042c40000c01c4004e01c1d2501c8240308000b80300c04002140041d521a8a91140c0002c041c482c40c5040c0342040041c20140c024000f41c0c02501007151624000f0300c1c11760f901540c5080000300d0400008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 803281160 1250 803279910 803279921
    0x705060105151219061e030c1707030f060b0423060402040303120f06170102070308010e0f040f0204020c07030507050a1428210507080309010c0308062719020a170703 73
    0x61000490740310350486484a00781b003080890307025605016501d0340d2050f01c4a1000c100320a00402600704007001d00016026043c0041910301511001400000c1031012400303e403801e401d0f410062103e102c60103020386100c4581c561001303046c1e50a50401e46180d802074412002004aa42d415071036400550840c0c00a80c880c000500700d46414111980500c01ca0900139800800154002a10400085160403144030094007541c0d02000442160390f49886d44040740146250491380560200104840b034a001c1010402540c040c40242142c1e502c1c040800c20001c010307034002c00c4003031042039102d80b007a0f885510000e02203100805410f220120001040100071242e04441030004245200c0080c00a1503041000606c0c444c41c103e031891a1a00d190582ea030142e9089140010340b4a555400064400e58145800c0701d005064003542c4540386181000e40d80010b28190039400700041004030404420842c084110308030740b001c42c40c040d21050020711500c29803000c01d8600861002060443d48071f81e002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 803282410 1250 803281160 803281169
    0xc0115030f2f041d030a050a0e0d0f030f03060306020a050d1a0a05090a09050d0f0f0305040215160f030810060804170a050d0c02031b1b0d03110102070506010515121906 74
    0x117403903465000b03101c06440c0c3e801c80c0813104000b0308107003440c0d8510308000c0840340388035402808525044000b036400301c1305080c81000f0b060405072118400000a01d00e800504000e510b1901e9403500ca0418159800031520b03110445101e030b00d0900703800d01068440d40a1030041d164184c480c141650346030408000545a00341000b801845850019100e455002d03440c855100380c10b55031a081e028011300200d0a944045d41c0c003075840115892412550080c0800611003903441f941c0c02640c0d1896911401c5210003120302c194007013001c1a0401c000d084800340d0034009841c49007003d20f440d05241e141c4240c4109104107040204600150b12503042d0b010b507066900f200300c46001800045074211000b91660454100e040401404075081544040e0104008054000c1c0c06a001d07034442c20307001040040c800d00f900a40500000c0b034500c0342400000c5c0020034910303014800502555160100b03000d500c002e202c001d180f1000003840604d0f14802c9480d460740d00310301030751043c0340c80d001d024072a0030050145920 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 803283660 1250 803282410 803282413
    0xc0803010e0105010e2709011409030403140304030507120602091c0b100b07060c0e060a0c0b060d0b0406090203071214010b030a0201020307080c0115030f2f041d 71
    0x307507000588508a0588200b070781c400c040c0c00c12a000b4032401081c80142d0030b401c040018103041c002d81030401c0070f0f40e0002040001103100c404407814110282d00c10f40d4041880c0c2c0002805105205103003c0c0155008043c500452519143d9111107480d50710900440441c002c485d0202820301109406035007641e00c00034556001c50090282c0040b0404099108954109004000407820b0000040c0e000c1240c100840c140d280542c00d640e286d000306003814486062040302050f032441a100c110144c00400b04545501680752014100a00c0c0004020300f410b2140c840c0714000c500060b800c08d50142c010740e000c1c1c00810203000c10f06c002400d102490b001120300141d08100941130208590030410100c400320020072080300000f060503258600b04501038090783c82005040300040e0b600d4020989a10114000a2803520341081100350640c26401900ca00402ca1030020078401c10340548441c0b03505d00c203103c4000d9070300a1402040240c01c4410a0b20a95560f080e100c401c4500f9101c80910b4600c0c0310 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 803284910 1250 803283660 803283667
    0x1230f0a0b1c020907020f0c15070c0e1e01060c031b0210170604060b0324040504080903010c0903150e0a0b0435030115052101060f08040f02100c08 65
    0x2c900e8800c00d80020141e100f40711500c041043d003400400e2115102c0c0c0c0e00400391110014440a1000c1141c2245070001400b80402110001ca071029a90001038070084012043c181070400101506600c194610b46004ea44000100700240c0c000b0400f42c4070f10781c10f0814032244031484489021310240f9402c0650415039100340ca909140c0d014110402c880c0b11044414200d4803002d05100c212076542c02042140482080481d103150340b21120f00405982811592a105215501190640d00d0039070307085484480c046100c1c10340349000e028460360030680f8907014404a1a58890140907070800020004c020b0b947d600090010342c06006950740690081044182ea003498039051034035046950034203c08500c40d5502000083d0800070426040e03201403d035505603402c15585030b40400d1419030241c01d000080046104900c050401400c00c0914030140586c42c1d0302d41100a0f03e042c6400c1925010803400300100300010f00a454280702040d01903403851070240070301405035082191150050061407010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 803286160 1250 803284910 803284939
    0x151d0f07210908270a0e061c12110d09060f02010b0d21050a140901261f060233010b07052a22140901230f0a0b 49
    0x4800501d801e840444c0e180c2e090040900c40030b4104c40400d921103a0050391040c1c100103001c4143d006982001d0010060f01c40c00628400c82da5141081e48411110701c0411943d8401981d0070841d01d03280d004091015203140584600014900385050080e041400140791101141a00c00d60060b500403170003600d1030400e010b40341001d40c0710000050415400349800844070000510880c10784405401a4803440700034804030a0146031078210094041c10000140340c900c03100f5545000c02c01000ba200c0181d4121800d1485d5001c07a0401c0f82080da465080404008106036640060756039030ba510041c40400004180c080031100d80c00c1d24105e090f02021442e400807820503039030350061848500c100101c900c0001c00741004407051492031403802c0019038600c2a25090700b480c01c0c8500380280107c122200141c40d000e02c1c48203e450f0b146a0a0b08205058100701100109105400a01100c10881e00c0c42000e201c07803140c0011802044108bc03500990003191200c0d0403034110681c0c544000303181d84043c8204 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 803287410 1250 803286160 803286173
    0x80f040f05030c120a0b13020411090a0e0106020a02040203090106050d03090e10030c0311030109140d0806030a080f0d0b1003020304110111061303020a06151d0f072109 74
    0x81e0050340e2103401042d01d1001c0ca4a0300c0d528074042e045420001d003020b03131800d40340d100e80040014804c1c080e240e0800d04800050f681e511803074500013218075400da220000c0d40e082c4000080150020003510010310010300c80e4680000c0e02c011010360448016079607a90f880c0c969030141290340c0c4050f8002c07001c510a0410150412207441c10f0710180d208a0b0090b5603810701d505488011840042c0032a01041014004a18010204034281c20003800124400c03907181c4c6c4080404d4072188403503407507030000030780780480503488081d0641042d800c80080900700d2142c1c4400d070071842004851a180b000010300010041c02e240c00c0f43e06040303c0200a01091401c0d2800940030354000c640480d0013040000d80c0348010344c0190081e1003e141da1000070107d036a2104100c1901350319694054080d446481d550380001241d600071038081c8100b6440c0b0112091034100d100c18030200c144002606081003008001e100890f0b21a00c2e0f40c00891403600800b500d150f0b102040c4103841d08034524818a0802004200b440310 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 803288660 1250 803287410 803287439
    0xc0109050a12030c050d0f090b070e0f010503090312060a030506040f06050601180504230a090b060d03021015030516080606060906031f0b19021506030a0f080f04 71
    0x50758200d25030342c800110441c11280c0b82c10a180204034148000c6c0c4420519a2208525001c1d8800020718072071507032074060303558074112446c800040c1d030303400e000041d0b04008140108081f02821300505600381150340b20380340c3c0180d4000302080c04402000456a987c1c2800c0d070307401150844142ca03402d01b45410108010380300702809a40203400c050200b0307144d500c281009003a507107410022441581c04d103000c1102a080300000c480d206100364001d00a043c0845d140d6600610307000d14001500c1220f490015003a00b0000c01040c4141e41d00702520f00469008548a0381c02c10004000058040e07003500b11055122450300094070b5403080241c1086102c0340b50003144141c8041c41d08807041036540740100030140c4100c2810319000007040c4007103032083c00d485c4100800130b036a118849002d03640f00c20403101030f0780228406a60070410391444c0303210f1603010b001c0003022000e001d42e444424900000441e03074903a50300600422125100b1003074000c0c00308840503a00083c00408469540d10741e20402a81c0381c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 803289910 1250 803288660 803288663
    0x51303020405090a1514160804020d0620091c0b040b13061814060606070809040b040c020a150b09010e07030e010501080d02060f0106022e140411040e06010b0f0c0109050a 75
    0x1100c046c0072402c50b0f1480c0148040b060b40030754415409580729400c6c884030f02a18103007110420384590302e00051001c0700d410f0902d40001170500c1c640720000c1c0300030400d2074803035483c513039810b2003a00011a012400c18940c0f581d1058001c0c0c20541641c607000205030b4026107004000d0102d034940b1a1032031a5000c0344140548103801460600d03038903000c0103a1113495840c00d443c61680078108100080006240078054000c66800030000079916082d40f0200e025641030310480401030700003108403401c00c5900440e10303050019040c02009400040408540f803080103018001100c8400400100c03221b120383c00c000c1122003050003c0c051540c1d25010b1310340e904081d070741110141c085d01d4001000843c642140f40c0c100c41c0e07a0b03070040410105100c2c441d0169190203000001140740e041c55007a070110306000301444d081d1810040c0c0c5162810b42400d542c0d001d0626850307031180c5c0c1040094240c0c1e040c0080c00ca41914002003800d0303582c4c1503c1c46011214400c8128002455090034110401c1c040042031802096 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 803291160 1250 803289910 803289941
    0x60b042108041403010f050c19110316030206090307023106030c08010b0d080405040c050d02040608270a08030711010908040501021501030308160306080f1c051303020405090a15 78
    0x40c031a1b0150b0320705840b42103e4074054070506104e0440498441884854a0222418603120703020489200600303560103540004a1004c0d0b60040c2c0003050b6040200315031008000c8051130a21070b00d41e001a8450052111007500e00b00c03032000c0702c0524034400d2901902c40c01c200c4020448255640340c00380814186100d095042d5180040020613400c00c0b250308001164048a030500d828207050400008085514500382040028850000c1e600f00500c001c1001d44940d4884620300d2404400d03003240044180b171a615840d001d4040e03807241c1100040c12400e081d5024111641720f55400f06c0444080d10b072654458011b600b0a1800703c1070103108001001642c0d42a404d8580303007500f0580094002d0307820301c80100050788500014105800300c00d0340c00704482162a02003023981d03451402500d031151822501180f0381100465490300201d003046856050014100142850082d02c42c0d900725264a00c40030b4003035519079000841d0104188200c40c1210b03803024120407078035480001c103001041d524052a40d070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 803292410 1250 803291160 803291171
    0x101403131502040f121a0a0b150708031b090402070c0509010e04170a02030f0c010c0908010501230d02060a080a05090c09160207091e0f060b04210804140301 69
    0x3006228002c4a0684003000303200d42d285485d08211510141540e54203855441540076040080d8020030b200e94059103203d5000319841201e08100038002092400540540f042040010002007c03003003a00d50240401300d0606200083c0e82c0c812203548609003900c1d40c400d00c002034000800c1614401718003642c005442c90042c903a203882d40141601400e0710050034000e0b414482d26001521764005000514552055a04185480e003a100c841e401c484c52492041e512048100280c07503200c020400107280c198000c1c010780d40f511754103000c030508109082d8003801201590b200141c03a10210840b07041d5001d081c2e5aa03a415001004107680b01c10f5902c0f110a0382420f0104018540000d249564440e00403c0030815840b03003030100303411a225803960001c1d8000c8103000035035150a84503064040d184045901e1031100b940d5080c000711384000c40e8840c9564030302402800f55540800c2940e099a41510301130301300544086807400d55100e16038000b058030b04d0014011486007590080c0c0e4503000c0d4185c009114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 803293660 1250 803292410 803292443
    0x10030f110c03070f0507090515010e0301090b070311040e0906011a0712200a060e25051203120c091f080c0d0209030105090d08070f090510140313 64
    0xc184030745451444242e10600c0001c001c11000c0208a1909100c2c504a841c080d81c0c4407114401c1d10b03000c0320b09002e000828145440715582156082c130078444110000c015804030399032804c1c2d2880001d01054200350f550b210750100c0041328030840b005081600125440751600c1810f840c0d45030824081d003186d0840316480e100c0807005150994503300ea000b02091002403210000f01c0760004011044002010000000801d072101070090004640c0206c00101d000b0700840d42c50b51030302c0700c1e005880c42c02c812501140c907901c8401c41c50314001d5400c00c807072400250401000c1c561641c0154454064511152024030400d0481280140180d41c0140c400440041110138007000d02028101c080c3c02003501900000d80d8680742c0c0006281c1c011030140700608141040c0003107400c48400f111071102950041d81d00c00e00c01034004010320713800100ca00d0144a9040d010360010302501302c5114803030203603204141c000b05550240c2d0900500005005106844e440c001035101030085502009071159100d1400202 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 803294910 1250 803293660 803293691
    0x619030b060c10020325090608010f0e0f0402030a08030108011b0f02030913060b310b0d050604061502150c131404090c17060a0507080708060a0510030f 67
    0x800b0b401000b000780003007500107100c2c0e101030341c00104156040302400101a480f18200038070b03000040c5803990744100f01820090043c0c20000f06800031115034003550300400003c1103d030382c03140c2e014420300031400715503c6610201c0c0c5030001d00d43d4000e00500022001082d001d00541c05034150890720015014081081d107016190604000111401a0020041ca020a040103a144441f4004004000410943c5c0f40382070881a08000c81d40350f06504c2d044032840c044071010810420140c400140d288005241c1090910b140c400c1d407403501d0405441e48001101c41d540c5a0101c0300400d0040070014003400e8906000391903514580c44c0d6040300184202080b880e00b108819036210001025484440c141400810415600e102d00c4995009407210b440306d002511340040300d8024100c065020089c016240412400d200c0001c10083c80c10346040d04025040340d1201004d03400170716a0a040d000741d2140b40c003054034001141c101581014000310840ba0307075a4580e0061502c0300c088001001030095280758038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 803296160 1250 803294910 803294917
    0x20f0a09090203220212030301230f01092c07050c15010e0601051e0a050c0f060906060d1e050c04200901180e0c04030b070c02180705090619030b06 65
    0x8400c41c90709400c0008201641614562130034001801421241c00191100d031856109802c10382500702c84c00f542c14008103003e03c05020300c450403911a20007151210000300020003030300c2210031401020540c4030704081142444150300b9024481d40f0306900d40b02e5009000c550017114982094444c401c441c1c0b5088084594160580e0341c1ca42003500c0b80d032120401181d0540010301d0b01c0249021401021201c524454000d1104c4d1005881c0d40f5100c0400d481c10303034100016004445165041300c01081040c800104445600c4481142c2c0d03800444e0f401c3c2452500780c2c880b0040c1401360f80f00d60101c0020320200140440f03200350f003280c0a10150301e810000700141640480b0b1100380110030302804a2030b40c01a18050442c038054a01d051100d940c0e070230a43d4501030f064400051401000038103000b8004949802980824941042001c1d000c041d8003003118065690302461030002c0007030104543e144540c08072003520b030005040580b0f8003d150215024500e014a02c40c0100b031505d01c9a00d40c41c10034000790f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 803297410 1250 803296160 803296171
    0x3071a040b011a0d020d050103031e0906080411090406090b0a060602030d02092d040f020c0606010e22020c1501051c0203010b10030e160b0a21020f0a09090203 70
    0x403441c42d928010a0100d0303009424880e0320900010300079001985a80d1010f8040300c0c1020002040039407450034050070101ca034a00c04075024034149c440c00101c0d0341080d204001c694540ca84801780380e40e14209005103051380c11205e6400322024092105100c038070741044401d41e010701884511500c40080c15002c840c030900c20307a805a0418480743c0780314401c0d5409008480c0f8064185410b4001c5a0b030103079001400c080c504040320306490407124050420303202d0f1000618040000b10301d0104c00c0d0807400c0c2c0e5203400034103070380c1003060b10b154242c140e03150194140b01010341c0030001500d441d04602c000010b034006240d014050f1040075000300c80200600c80c110f04950000c1c10b111040382140ca50412080e105400c04e03038041d901c4680c00c1c00e098503100e2400c90052259940050100c0e2056a56414040003210761102101680000c0c0240d81803107084811045044c10040c6249500300c40d0b1190040c0402b40090045101042032841d440d10384000740810307266580e03140a00c50310b8540c81e0b0200d0000b540d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 803298660 1250 803297410 803297423
    0x305090c0a051306030203060405211206060304020a0b0c010603051501050d0b181b1c02030705130f1104080d0c1e021c14010c1112030612030c03071a04 67
    0x341042141083e400100600103001c5010960b00e03103d4010030b1a00400b41c030112403641c01602c401c0304130401e0000c00300c0e014111614031441c1000245240340304900281001d841150700001088c1156180c007084001485a074a8490b15610018407013402400644000e4444d80204c01d002110b0800407062076058543c000e0240c104d04106803a0100909070003840060221b2844c444594541000c024103012208016070282e204481ca0781072200724511205030811307040b880603050f001680d021403003006641d0103032850001e4801520014010b000b40402c0100210700d01003a501b003c170303000c40041099841000865150007141c1c00c0880e10b48004810192114440c00040f005200141000c0d5901c40d00040080c1200c24001d64041c142c81c8150030b0407034040340b00c0b0081a6421000780208081d040060500c050600301081a25850b081c60255104a548000001890700d6842e403810900b00b41549048030780380c91400761040c3d40ca0f80110300988090703210310900003148c040919602d1050754000c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 803299910 1250 803298660 803298679
    0x40c0b030711070e0106111b120a02040608061e010608130303020f032404020a02060612070807180b0d11040c0509060c1011030405061303090308190305090c 69
    0x1450812504054500720030002e15161802081a04000300700181070100d0184865525102c4060040340c0301c1c29080e20035802c068014542501c2c051035802e061034041d50064145101490402e0811900c00d0000794004d240c00004111484006070040c440e0621081c203100b803208190071004440801d02c40c4000048034100000c519a204101c0551268803d0401500b041c820141c0c1c01910741007102c0c25200620b031a250100c0301618955018401c0e074055034110724000810308001d49611009100f2401105000c1d01c000c25031104010b114000d145440c25220318603140c2114201240c020505031040ca03040c09540c044514088400340522540050700100d402d8001042c84040e21014101409204050041c620703c0d8680200030480d545601016040811580d0a07507022182ea0b140900202c11043c003c11000400c005901030700045410b8003030401104a1400716108601504014a000320100d00480c0c03180c0040400d442542c0144c40c140420741e210b4524994440c44a110940d0004504 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 803301160 1250 803299910 803299919
    0x50c030603070b0f0f04090504022b0602090d060608030319230709271410050d0f02040c08010509130b071202281b0510050612060f011805040c 63
    0x102c001d013507400e400d050440c100b0402e41d00d4102e441d000b079484110380c2034a0f00104401c40c40c10314100d00c010b14080700c000118400384404481c80651019005100b264006800b07402030341d0b0f00d288000c4079540300c002030001035140c04005840c4d800c10f54840d80746401d07a0246008000300d038080c2d4000d421852603403105401003000d140000c80c1c005840903041c00300010b408911600c2c03c0003d46096207103040d0f03805105220325070410403640c0301401c1304807443c6503805000a10075191440300882e0000c0ba030104402d00b0a040c90755642c015118029401031a001c0c0d454402604020300c507040b03078401c0351001840c3d80c03034800d0f4019004c4c01c0040144403071102c4000510b444e02424000b04078102014006003480009030304c650003a9407009818007441411941c030312a00e40e00c1080c134000344d01a0030070022040034541c0c80360f42d1095a0314480714001e071900000780441d03c9107005600510700440895903681406d40703075400c1d007000c28060015004800c03222402c420086000d0325014075800044100c105241 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 803302410 1250 803301160 803301179
    0x91706040609060f0c0503010f0906080307020409020612041a063a020a0f08060c04080703080f160b01090b040903050301031202120315030c0f220f0e03040306050c03060307 76
    0x40e2100325221aa10020042424050301c1911800368050b1502c0c1e87d654108000440001016800340c0405410aa0181304c4000c01000f622151681581c020410501c0c40c0300088440c003804580481080000040005100c40c2c5280405504849400f080007034550b1014050070190016541d11108618030481c081000c03402c407030007010402c0c51400a801d00c810f82c005120700300550300c16181d13a24405003d0201c8a414004280c200c8510030f1264603183c03904150035200e510510015000d000c0100b03407051868001e80440e280c000407009030009280716450800000740d0203018007101242381c007908400a04292080000168140c2c890600b03680ca581d460b5080352030701d400f030441140100b1010b010810140b001550103101c002d1034030034038848640c041c18070740618104024456400904040e099031100c3d6480c628400740311003030b0903950308141c2e0080003a019500f02400114580380c054540c414000c0081d1083d43d10501d001c0c030950b1524940c03e0b0403400103883c100c4c1d1503008040b040107422036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 803303660 1250 803302410 803302421
    0xc12020f12030c2a0a1809061d030a02371a0702151012120903140c04140609070f0314100e060904120c05010b0904050d0917060406 58
    0x2100c108680c600703041c04070107504181582080700c00000800c0d000184d240d1000000030700c0300005440a007909860040d454065102084011005035070300c40000041c4461a000441d0380d000c440d0581d802c0304440031000766170350f00401d5804018090940410b02c450140005109515000b500380264650b03c60b069982c9036040c1c8404840a040b65001c1c4c0003801c2e1489a05d42c4220103540180ca407400e028500c1c02d1607108018039a0003a400f8005040c0301510b500300400d65040e070040e030482e8000304919825a001d110541010b0300e5115040d80001080c0c1c0d000035014032024060320140250031000c1009000160150341503070307101d80040e0000d07000c240701303140d2024018040d107400300300c0c50010003030000d854030140c904680302c550141d000c0c001000b8510140c0e401c64400e440c0344546148c03a444000e544540c58030030004200160300032106115007500414007188004181070081d04051404569604000c120b0401007280050001040c151360700b540008180540050a21680c41d0743e0750100628 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 803304910 1250 803303660 803303689
    0x906090103060504061706010f080d0309050f060117070e1e060105040f0b19050304030206040b0c09031e120a0210110d020a0206040209090f0a14120a0305040c12020f 73
    0x155160000a40fa907101d00800c0c0041c11000b554403080d500e55407901c0d0030444140c01602011190300010403004000041d03403500c1c50224a00010203d19500d00503007440e446500c1544244961030001c56050700c0300c920309100a095600b2070300c140e0390b240704004a0803001c42d09220324070036040c80d012003d960140199804881450124a004d45a41c40060702000a1704400b4001c14042601c040403162100044a41c06850428504520302954025070355440140024207902003580440c0d07004001d04141e5080c904001d040d18402e400000a41c5206074500351840450310407100c454a81191210860303a014170640c0c090140d45245086040240004450059070003031b04024141281582d440948080c94090b400b034140e0341014010826030180c041d10340c0c2259000900002c2d46142c001581c1403c20354401500e20701c0d0440201c800d41040c5e0242441c5e03a4100e80004c0c10540541d15038030142c841ca1003500c904c40c186840700892804a0a000c02c02500503010641700c0c1c80c83d280400d001003202 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 803306160 1250 803304910 803304917
    0x90712181e1416180225020a08010e031806090a03030f020709090b040314090a030b0c0f045a05031009060f0e03090918060c040602010c0801050609060901 68
    0x200106499510785400c0100464203540841c0f014003190080d030b00803120f00d002c0c809080d07042480700540341c265075903580031010460350020003000444d10f600c10340328018800e5000800400c500a6043e42d1a076111180003081d08001c41005000b92410106864038000c02078100303540c1d61709603a0151540313045c1486d92000c0d03200d000d0000940c00d03850300622200700d20907641481c1e94109803601811120a503002e8004014041c4000c0c040d58903664481412250841c01c0b20010b901c4403e0f100241c3c3c0300303000b541e0700c0980700090041444034005401070381c83c0c1f41d10710300000808554054400a41300250020b614038403c41101d00e9159103240b1020848140401424200390351500024608440c00c000303140c0746500c403954801071040c00e1103000709204410109109070829035601a489109100f00207105944a20200e040380403403a640290006c01c1070102c07a81800d0595104903190018814000158201060345000c640b00c1c0329210b0480307901406c0213044c070804c401040755940200d150389040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 803307410 1250 803306160 803306183
    0xf030a1506090e06010c1e0f0602030f0f070c02030703021002150708070f1e082a0322020a030b0601031413020a0501080906061e090712181e 62
    0x4601028484002416252540d600b082d1811840e88015400144080e045c0101605403a02103800c82051500d1010740f40003200e0200d401e807411036041d4a4509020f0192840402040098142019001c1c0215240c0342503c170f280e603d145003200c031500c5103200250141c021480c1003005042450608940e4500c82c0181c50399101c000f10500c0a04204584480001d031440081c8140d1a801100c1c0412a5000b4544180c2d18001070381d90066265001d0203010411410a0005403801d01240300c2049030140d0b40e24050701e1180000c004122500242e440d41d903118401c26091100840340b41c019004694064910110b1600c0c5845420b0542d81c01884c1034181515001803010000980e04491300c1500d01c600d0f07110115029005014a21440c0d0b04942e06205d9860148841c048002580a0744401e003111078100c1451a50307964075000d504180c2007038010361480f0601000a8004c0d20350400c1c44500b020030810014014004070100503046405400c1d04c002c86031841196040030140402c15008000d010007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 803308660 1250 803307410 803307431
    0xa150506040b0d11011806211b03060f0e06210c0d050106080c0907170a0f0903050d0b091005010c111903030201050f0613090203120307031d120f030a 66
    0xb4800fa88084030645924800c9101c07560308030400c0300911412061440300e46042c0364000d40700066142e54072184080100101c0d99100b0150051448040900d003600c03c91440380e903024000d09900e005100c40d00c036950001040318441c82407004e00c03908005140000142c545046c548401c0d030a12007000590081d403c500b03540f034850418031550181300b2800010b81030307d003a074402d00340a1541146803107106090140516290f0004801c601c130444101600810740b81d0130481c100401d070158049100d1070820303074001c0600d60800080c0090325009042488450013503001c201125804844054081c0302030304041c09031f5445100b0161000d44540341c1e41441034803120009590319440360106210740d0600c1c9040c4105035080c00b543da040b141c0c40700c40100d60f04000340020074032443d101c003491410350764010034015940d080100308040f090101d1140d940c0c2c1001e14004019242c241c040c080d0040004070030007403404000410701d038207044001030f55082071100300001850341d1010b031050b156242c841c1d58070381 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 803309910 1250 803308660 803308669
    0x220b040302330a1d030d140f24130f05060a1809140609011d0d0801030f03030f050a0c021e1b0d0501060605120702161503111611030a150506040b 64
    0xe8018a15130002c54036202042800810b5030400784d040c0800c6a62441813015818421103d1904560079101914101120301420410800d0700241c607507000014545690b03070002d156015a2246e00080070500c0603990340c200b80158441c42c1e00c1842e005003c4c9100d40c2d001040d141d40140c2c80d2078403d04260b110031602d0034250389000416100942d190355240c07602e0307414040c4d400d468036401c80e00c17001030818603c0d081c0b009410044144409007080ca8008401000c0600c02e82c4818a40742001600b00203074249802404024015400c1c035102510030004034503007a01c03441031080702401901c401400c005403815406c40a00941059941d0045003c100308070010328207004a1001d806a0303500d454868030808810411f00002500f030b0b0301503401445002014104941040099a240b101e1141c07605803e240124010404802c0c01610040f010800b011104aa44040c00c3e020340662450085119170400b01515000d80c00c0700245071005c2c0714111b8a040701c2c560082540404001d10000710900700c400403a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 803311160 1250 803309910 803309951
    0x9060f04050a061b06020a110609060103150908091003090803010902070c0e041a0c04080724030212070e01020c06180a09061409220b040302330a 64
    0x208260011505000354100203070303003000a00f59450321a500d0400c00740c0342600c1141c0c0703020282c01140c0004981d1b46085c0a4006910b003404858225906454040f0703a10792210028041109c1101d06025882c024103424050f0700303c40e40d004a035440c5000504810064000541441141850340360000f0b40d0200c1c0c1000f010714000e1051205c00359449880d440c00c4101c1ca10160070400003100314905100110348140207032505a100c2c4c0c0c0c20070403151164219440307140140e502060091044030300120301d040c0f000845645c0444541c04a0351150f004901c160141c3c0140c9401030b050101c00e10014154034410011103400a0f01030068411900c00c403004100158058541d070290760707400c0c0c52242d146040030304499000f0250f1060030007546050140301400309552000140c41001080080307040c4803101210358a500c02d0310a40301d501682c09103440300f41c8620444064001d4040c0a00559045814420074000800d00a41903900500610031055a20700007800400c074aa035540d40c9064140c4415948 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 803312410 1250 803311160 803311177
    0xc11030f0714010c1a041713060201110403050d080406111602120c010206061509060301030b04050708011814030c120904060f0e0c0a1218060b0603041a0604020906 72
    0x241c500541064084000300041d550348030304005501d0340001c04100600d903c00041030345002e03000801d40b103505160101d41110782104003002030004c0c4416091440310640e41c1100e001d0740080c0803580d0114822103a9000f50711000d80b0700d80100500021503031040904c0c41e40300c1d00c540c00008280c90036986070a807607041041d10020005400002105601d0400c004500c4481c00400811030130003401c0c0001e4a844c000752003e40100c464000104001c40c140d400d039810048041c25480d202e40e5a0308000d815404180c0d402d0b18680103a16000c214100180941144043c0d0640103010764a00c41d5204840140860300d100b1304c9000c02d02c03100c08029010312142c10340c0e88102d40f034582c54a00910800045034910343c8040840709100701c00300145180e0319502980500f10448098891007010380540d42c11013094400d16015240803c84510340308000c400003100c3c0d001b00020000480341c481449514441a80c0c050324450203880c92110321a031613640c1079841500900f016040c400200003003a50342c2c009111 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 803313660 1250 803312410 803312413
    0x5070b010e060a12121416080a090e09061f080115030b1e0c0703030905070f03060606050f19110316060506030109021309030c0f0501021c0c09060c11030f 68
    0x81c0300052401c0601d90000d0613130203400088085040c1e4600c00c5000700800c84900344201d0058404c0a810a8402e03640c40c440c0092661007110034900c0c0c00340055100003902000700d41c208070080b0fa0200d10364101445024800024a6161220039580b444a04519400301580c942c000c00448c0c810420b0180c400145a140302414166041d0720380b1103107111f0000c0c252800344850f00c071039042c4010043c0890742c201100140040c0d5411450901710081c2100050113006441402c100090320b070340b144840800c480c000e040c100145134464400f00c90511514030050f91040c0c0c05d000c200341c00e6092881c0f89c47c00301c1c0181004125820125502390442e04811580d00d90b41d241e03010f6407828482c05009181d4407210890003003060b2580c1e0341c005107103499140c1901191950f5400c07248201400b90400300304071030b0440e4041c070529070030b45405801703540845040e05414413400f40411104007103000d10b8081030219141c0303441c41410001c084800e124640e5054880c0d46200004a41d6604c090240c004003200f01c80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 803314910 1250 803313660 803313689
    0xa11130e010e101b0c06110f0406090501090e36030a02071505070807060b040513051006030c1a0f220803030408032715060a050612040204090305070b01 67
    0xb000941002d2002d014004154204101c010b1304d08801d40c103040320051641403079494403440c3d041c004001c188254400d9a0f0900000f12032050119200162045031419506c0c0080d03981c54100442e2000f07030601c01c00841d8520100495207051036805550150940383c2150031490880503030014001050780a0035009400000d02489801c1d4140120000303006800c04901d2682009200204107100300000030307011a101003010020130215810030b1410f440010f20030320040c20032280940c111445000c0c00c030780b18450003818408078200e40c022141200d80006203840d07428900a04001d030352000c038050030020031003001000c1c41307800a0009401e01907600c10000141c15411600080d2000164100c0b14069000f4001c210014580e0700469500c8607091924401c1004290a03505c984001c86110605a0065a501107009061050003a104120440750b20b10404c1e03980c42032050301d2180240c003414882001e030005001d0b0a0541013000568444c3c98091b182c0801c40d1a1000741420a801441e441005032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 803316160 1250 803314910 803314931
    0x101104050a0b090612040f1b0509160f1b0b0f1506030103050c0d0201090e090109030e0d0213090503090d0606090506040513020910050d0302060105040608010e0a11130e01 75
    0x140710303180507051541500e840d00306000700003a2a40165008041030111200009040000b0751603020704130355201d0004c8502070540c26500ca990041806450301030403400002071150b20782007664981c1000c80307881d9907518446001045a0a9804250620a10444030082800251100203141c441c4407032100f08a61070402144004000030140e92051080c8414030060010590204040d400d6540c100c440c01038480f10b520050b1045c445650145038000340c68410002050019040482d00718400c0d0340d0003c2414044040001221a44001940040000b41e84262984003503101d0301c0d11a0156049a0078460300f10000740c04814010011079026440390b4080000c02640e018068000b00203c034244201e10300001c1000507020f400001a11411041000c0b4004000100940000d414050950303448000c49080184d0746030300a218107400385290603c001200d25043c40b40198400202e405040b054025131200306e0707450905e0300410303800b401c0a88107096002d1a0700c141d007001c4003414000b141c01201d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 803317410 1250 803316160 803316169
    0x5010f0c0201300e070614131211040b0102120f0310080105010f0812041d060d020301020c01090209090309090c1b1014071728020a1e030e060606070510110405 70
    0x42940e4a140755005010a0090540150580e40450a0005400c1d201c0d0380c072803001a40001c03564009c11280c0c50480000081c4034088103681c1154505660500801d0030a0f00126528400c00f02e108102d40c83c20b0000c0e005500d08000117640004035002e010f600ba9880b00003060031910280d001c180c0c00a031200e000c100782c0c48284010a12420b0b0700f00e4490410346000c002c0c031000d007000c3c2048058a100800082c446540b6004032000403034024008648400303a003281c060081800b01c50036840342c52800c00103002280e0000883d11038110117031003d521600d62620055450308003010300648100640031804035085d0030450005980c402e400e000c00c404980040d24403101307501401c4c0c502007240024071408000d188040040e002200060b00085100030001544c203803241c1041c048901d2400083d5030103034603038012028140c01c10030044401e42c03504209029000c4551403a558205608520f0000c1c0c0c161820030003429001d070007141a210590300340051038003240d1150071403041104004c102403005042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 803318660 1250 803317410 803317421
    0x11103040b0907060905060c031318111903200c06040c060315051215040b0618150f0a081005160c05060c131208031b030105010f0c020130 61
    0x6042c0040c0c50f40030700780308006121441900038540109400144030000e2201001114240c04d886541944070580b6625162219490b5040c0111041e0420400301d407610480b40844499000440406c9141313851078000360050421024100c1008100c56411040c112009000300b401c055014060102c0c2d15051514800c3c0b09110f030405004c02d4600481c0c2d0340d104030100349150646004954034044000001c06240ca444030110040c03050b090203805210400411444403401100c08803900544c503000d042c0010202c00080f10500d00e0015041882c42007030512004025500c0800381128185c81e845046c49072070700080c480702982c8565034004203c810740181441c03181d00000c40c98010445c4141e5260300e41d54900150440d078441100180741a1911110072521004001144180c00d0b40700c0141015031f0640c00c211135410140c40c24102e01c1129011030000c9034141c41c416110b15100c120f10640071104401c0e0b03100101d0521800b41da09081008800d522172117202120391413400c04442150b040000d440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 803319910 1250 803318660 803318671
    0x1302090303071a0f040803270304060e04060602190f0204140f0f01082a0307030c0e0f060a03170a021608071d01150807052106040b0919020d020c011103040b 69
    0x113600e418000090313101d0013201e400c9440082c0d400c1810201c01c1c2c400072040f017100c900140318800082c0001e00c0a810018140700745504842c02c02440307545080c260f80354080e150851066100504040700004c51990414010600113000001c1c0c103c0f620f51a0182104150b8503d000c072a094070400002e984840102030140c01d030a8003410350310040000d0303001804280341c3c121801c00c54070444446584c40c1003041c1c00046822003819900e40f82c0d100031400c00c44d01c050ba410208140403000103907050518016600440343c0c0140c0701b24214000c50300644081d04211805030440c000e401c0c02c0c041411004c1d603407030003500150000e041c1e00d920f44640f00b8000100001d0b00400f030209100100018080703000c18400351580c506122075940c1d1f940504803203d01c03401c445c3c958059220a032070080d089060280038800d600a480400203040d00c3e80c10004143c0302100c0c6444544403120040b0030100d401c1e00640104940719801508160f8080d00c05070030345010040c02e40c1e002202008000c18010002c0c0041c1e0041d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 803321160 1250 803319910 803319931
    0x605010e1819030327170703022a0d06020405010e0409110409080408012405010e09160309020d0f170c19080d0203090106060e010513051302090303071a 67
    0x40e40107101c01d40ca03650070b0210741000c80700111228041c0b502940003002e030303c1a003034403602d807040e00d00018040c00c0903c0e410645901c0c0c0050f01031540c001001c002c0710038854041d0000c2030040e00c2000e0703980443e400038034007007c40551003000c2019501c2e103071041d200d1544684400340e02c490416000600c00c400b04103001344614100704a10020400f6150101034203202541e0109904003c5d0506907024401e60744030030070540c6006082008050382490481c80c48600442c4440c09990756001141d0810f00452110361000114020505540064100607220380c0b40e0708000c0764031121030300019103005811205640d405103d14040c001c000800465100300fa0080846030b0038600240c5e01c40d0b070707142543c5c6416403c081c003100500080c4101e00d001c7d6115401d0203074041d0740d2407500c6505140030340a18450100400c1c0d0002c440a03141d07010380c0036125110385026070910154076101c2003012884404e8501203413207508114070741d401d0310f0030300090885a015600348411a88000d901d17020030341700145604240e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 803322410 1250 803321160 803321191
    0x1a09040509010f110a0c0b09011812020601060c0506151207060507060507140301120503090d060b030f01021c0506060f040b120a15060507050c03010501120b100b0316030213030605010e 81
    0x846d086402c0c0c8803400d40141c0c05144590300c04400c41e00422950354000031490529241408000310400c3d00c030702b6003c19500381c84030769030f03035600079942460309100061035a000a000500700c103c184407811005000148050044107440340d046080140640005000450008448040c08840c2c019550042d10b030345020702001091107410400c0d13001c1800b51386102800c5d41003840074003100300142c62460708002c1413030703040e000c0303904d401001011451441806070081c4840b00d60003d40c184280d8125080001c54030980300914190302d401010010b04043c0e00c48000c0c032102c14101258805407000d45000d11140d9555188c0c9181b40c01d424100400021001d41040c0d0180300221030b081e4450120b0309030741000c42d190321041c5807080c1804041602a601503107001c000040c468254498540054000c84000151361603c20803c0108940c40c0208501e900c0b08202040101c1c401c200400c10000c0507240c0141170210b10000e0741d09500300b42c0d0040d607a4076100c44c0103101200c0d0b82078645801c00d005018440d803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 803323660 1250 803322410 803322427
    0x90d08060916080907030b180c121e0709020406090f0b16080f0c101e05040c05010e0315010603051504050402010c0b0619120501050f010f1a09040509010f11 69
    0x4040d2080c0c82d034a41000780200215451102c108041405143d00610845491070907404c04150111581d03201d0000c1e00c02c50380301810314200540101901140500a48042c074084000c0aa0181d00c98060301c40c113200c0d5100001d8420940c0c8003a1000e00030300d5407807106e91480c0000f0060b645030580c01113408140100050b09000407101a0324411380e23405180140ca07030101803810000380c01861100045800b4400b81121050342c40e9001402c1903040c1110904542a030200180803105c08031001007041d0a80d50043c04a980a00c070840c201013401411140041c0b0b04161102010500382d020401007500c1360203010034128050310040e43c400301078408124034a41900024010030302d2860207410840b034040491502d884900d8a14901c3c0460300e031444002e07a65403c0005200b0380750b602070717845502c0c0c8004582c9460024144078101c451a2458101081c03d101d1031000031401c0c0301071000c10400070807110021b51924000c041c03048200e500006000381c0e0841400c0241d42d14a048a04034210030080c101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 803324910 1250 803323660 803323681
    0x31a01060c06110d0f0509160f2102030d2a0816020604050d03020a150e030307140d051305151324050c04150f080601030f14090d080609 60
    0x51280d080b078000700c2d10007031540941055201e00780e411000e6900348020307000800140d0304250b014119180841380710707109550401015446600802800821031a42000011701051410b1030051043c001c418100c2125070001e4900340c4840d0050000c10081070040d01c824049500c40310b03940020030300210944899a07034804071803060341c1070340507000c074490011420340d05c40384c0c29200601800f07450b09807c54003500b4043d41c0d40d820780104032403803414035104001400b943d025a64403e0450802903081d0340314560240c0e10960856550030030b00000b400380511600ca0f901809000706400b0345070800c15a0241072042c1081548825001404052010310245070002c0d1120601d0540000340300c0340366402c06200040e812820143d01131081d013010140603041100070007d10490308400d0810b0303034075400000140c8811310500c01c0303040440c49200003d40350394000c0e04480080204100001404001012803c07580a000d660406a81d4130865981e0441500304010f16040310040b103601c042d0b4540444d408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 803326160 1250 803324910 803324927
    0x11031f141309170c1e07060801050603070309050106060e0907020f1207050703120f120b01020304090b190303050a030b030f120c160b210601080f130206030f01031a0106 74
    0x1601c25a41e42c0008800d000c0035810400c0024404894150f440840d81107190341c1d1080110409162020203904c4c2c10f04142c00901042201c4250320383e119140c0ca400100304240c0c20051540342455250070100000130000e205203c081d0070161034002e541540300041c0101c10000a004009540c02100d40e2200a2030002d10610a013044081d0b203603480c8090300d80b05062080c19071008000c811401d00203161300c1c2d00421f051194640c0781d501c08451682da2010726058560000e0b600d40541c004000601001e50389802c510301540c030150060000b0001480240810602540150005040410710204180d8140505080e4050450003060125503651983c2c0d12500450150700e000d003c001000c914082043c0700703801e416580d4400b480c0f03007030b951820550304c40c7d03204a045056503540d018035042c12008048241d40188010f9440c80c01b180d85070744451028984c080c00046902580304812401655074200a51183e500c1c2d00414206500d546000b40211488080c0d078811101320100520070981d014401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 803327410 1250 803326160 803326189
    0x7061b080a09022409090108010c020d0f090524120105090105030309032d0d0e01140c0d0e01110a060905010c1112280f12051b0d11031f14 61
    0x110520084241d199006104002c4174a80102c4142c0c00041c0ca40d80651000c101c4480c150266005040d00d407000b102e1800c403035580c0c9001b2480e1200144003d050555a02e4803c921200000841d002c0182c40d105076a04910207107860965074030018000e43c00c200e85864014541603000b1030803d1100d0000940b40c250303070042041c10036119200201021500c4208040002030607081c1d459840051710010400400340d60750a0206210b2154251680e0722032080320599500c21000d0180701d400381004507080e016000b482c90400100711240c1044c6041801944007042c8a1840010307580503038500942902e00c1e074280d00d400d0104600c11100400e0300840d100c0750060000109640e541d03010078201c103813502202c041805035200e0204004103140c1156042c14181c070303184c954845014110450b075050b1202118008407003150601d100560104510103400d403413100301e00200355641402e1b080400d075003040359030154120359181001c40c960041032070b0346c007c4c010004074449130b00c0c0e00c074000c20543d5200210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 803328660 1250 803327410 803327449
    0x30c0e04020d15060c050606011815032406021002030105090f040614070c11030604080d110c0111041a040308090d2303130e040203060403030b010507061b080a0902 72
    0xc500c0500790030b03948101c4801003411010100a500c0d840001c0ca10107480001720b84e0b038841c01c404162a98010b1480c540714480c14100f05d030f591070602980c489130182400705901815150101d0350304070030400160099071b4608021003800c240c601003000303141c00303260000da07016940f0402c0140010307107903203400075031120b10301c8100c46c0c96403601d240c804010445000500000c501d030005000c0ba09070700c20418100380307004454461560406c51304040d00c616003560020301494003004a522102d070aa0495041803090f841381c41c2c1048803043e141400d461083c0b0150406900000d02030040400410078413444446003144581002c1c1555540320281c0314651000f0f104000d81410601001200091140326104412411454240f4406d05c5641c2c0d400000455070512003203100450321611030403c0d03174441d6400500416180d1200d48068000b0070803c144d10341001801c21814010620600411442c0c0c00c904038a0300c0142500e24005140392009010212424141032151015a039480d200c140352504541 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 803329910 1250 803328660 803328667
    0x21140c1b0a0b0c0c010329040b1c081308160605091201020d05040519080d090507170601030b060603070e0114090d0c0503061303050403120203040906030b060a06030c0e0402 76
    0x200000e000c01c49560150107a002c00162911100a0104ea40c81e094807007a20240310300c14030080c1500001c2a42e0381c1c0890a041c500391030407141c0c81c098015201c50303034016103003101c0002a0007203101e0748900344c0820750b51100000394442d0b0580c001c4040000074100740010340f40701d00d281c00845005080c9481800d0800c80c0100b0600030f190b480114240007411078a00855860060358a900302418084606503001d00a859440008440c060703400c8034040e601225040c078085507503070a203008200701241902c440c8580e100204500054000003022109200001c1c0025891840e1410902c44c00501e070324002c003010300500c0072498008e010050242c40c24240b0301031070440c0c11039000160140c001030b1380d4005600c1101405000d001e0200c0d80688005505031241c95882c81080882d0b00c1480c0001400140304102c104042072103160f0715403e582c814415a07140644c1d4603108401ea9500d900300b07940784061081031141c0792074079a00d204000c040c2410144001e02074888050644804ac0108500484c2c000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 803331160 1250 803329910 803329963
    0x702010204080613170301091b0207050f120f01140f090c0604030b09210a0306050a0b030c0304060605032d0c0a14040902030d020d0f0507050606040902040921140c 72
    0x1103d42480c03804501c0405616581d5400105c0301914484013800d501c81c027142031100c1a00d02c089900c0e0701351400544400c980104e03030001e0004151003400280350301d0040c1d80c898101da00080c05400100c5014110341905824103070010540420b01802000e0710354080d0800c00e10075207603001501c04490b0020400f0f4256915440d1960804965440c480d03404412210045200b41c1e5071005000007000680e002c103e040c0c0c848082c04006c07059402040307408402071000a8504c84484020340e480740c41082c012884690300c2c004607140002401902e044038511040c003890880300035180b680709544e000010315003100800702140b06a6424001c41c01c441c91008400d440ca501c0d203400c2402103e50280445d103003880040700c0207443e8002044640009650851544941d601c40c406031215290032101910442c0c844c00100401018a00c100300d030031580302d00e4080c0100350080000c41c04182400c0c1d200c650080d40b408000c00440d0b840c0507000c0b466030b0901c0510401a00003174040c0c5191203141c000c0c040c89481 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 803332410 1250 803331160 803331173
    0x306010513060827030304020616080a030b090601030513060b040b0303040308130602031e2a0c030709020f04050906011e05090f01090302011e05161a0702010204080613 74
    0x1000304021030680600c0000841d15404401d1520034140c103a00d01d501034000e29182c1d0301c0040f0103130101d0b0440e403040c00072601500d40640200b00b00b5809c9042c00b503a202c010f65510140340c200d459420046070b56815810507078108040c01c0c65126600f4a001c00913441c05030340d2080000440c0c40040c06d000c0c0d4a000194240d16664070110446900608681d01c0c0c0d130741d81c0707044803da500800c01508200e03490b4100081050001042d1100c0c113041103030312029810440345c1e41007240c03c0f66203141f110240700c0030303e13066065550a50401c0000c140c809800c403201d154007030520b01032607a800820600d10401400d09e0b848092001c0d034041c0c4000720740160054944000488000f8421200030007014030180d204406150003100806d0381d05c50940300c400405160100640d611140c07031001a0100b05004a41005607000c0d5840190503821420440c0c1400c51190242c02a00c3c601903084480382140500c1d810001c1600d500e070355000106100079031809003040d20f040e856880141404000405083c80d100c02c0140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 803333660 1250 803332410 803332417
    0x507080c15031620030d0f0b1c0f2f09011e03020f0609040507080403111c03020a030905010c050d150f051c06090f12090f0b0c070e0106030b0a080106120803060105 72
    0x104002140c0d1180c2e88440b401b401409a000e0030b000c0c0d01e1402d04aa40682000c9139010041404180c03044000012504c42540c0c540d03002d1401ca80c904000c050855500b0004611b110103440c801a070b9001c200d03a140144003c0041c1a00204540c214041203403c240c43e110070000240d80d41501e444c2600410708021a80341c3c0110140380b81e04c0f03400c09007044142644910250301c1503000355034542226120744446501d40b02d0122140703503c0c040917a0b83e551b0b201d000f600207204a080b245800180c0d001a9107805084800075003a0300002440041d8090034600c65000d009608032040700480305040c0b07441040c1f004000700b031060500481c40c00800034010704881094414103a00441d061010318014607128041d0809220100c5404221843c0b0044062154803880141e49103c1d428403820760803c0c0040100390001103061515101e401000300700c00030300710740c1e681c000e016a8401280e488160400c00c01d150046810500060380b620000b0040990310300764010b051504403440c1ca90726128003004885030321 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 803334910 1250 803333660 803333717
    0xd0201061410020a02030a0f02100807080f09150a020d14010f0909020a1e18020307020703030e13020f030621250b070f02090702010c1e020a0507080c150316 69
    0xa8002c0c0c030781c12301900b519003042e600d1003111094094500040180c0d80c0400c01d980345000250b0031000140800402003195402c04841022034800c2140d00c00e00740540c01c021103903003007110f4001c075000140090744d00621100781a2010504500d42c14100302103c51150380c45604180340d181c81c0200255100e010701a800340414061641c0f23005034190b09040114020300c42c010b0304080c4a0100da08000092003540c0c000d502c80d5000c1e15000745581c40441b0900c0c10b1980503170b40250203020b190306075007151004098000410303031030f103413689040410400450507207038820b419800080302104c46068045000c0e40348000b0313020701140e814a02c0e11208110b0189410a440c01d0364000798143c103102d8440d2108406501c00c0391010616940d2203000c0382600c01c0c04a441300400c0290745078070344498880d0507003250709800384101c03050405a41c891515240456116046075000140c07c0f09490401446a00e2212100f01c03000d480c1d03042001c0030f8203c0c4604841c0704002c002220500502e191088121891000e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 803336160 1250 803334910 803334913
    0x1d06091e12070609092f0f0a0c020a050d02100813080c030d06170d050c0c1f12060311010e220c080603010c05160f0b0709080d0201061410020a0203 65
    0x2003014052951520302e40511004210158400a03401146014000000c3c05a0051190381c400e00e0740c0004d40282c60000d1301403c9001441170700c814605c20805406201c41c80c0d07403a60210440342c01800b10b015542d0f0810380c042c0c0c040351600d0015071591070503402da0340410300d1300260540d518004a1072808684000400210b400506400c0b1808004041d2145081030102000444d503900b200c3c1ca054102d64902640c1a04a0003003a0700700c1d4002c40151820305110030640300541c50f42800030340c0c00d00160b002d0310b10860403544211040765100d10740611181d4801c004214550440d2621400e068080400c1070401c150544417102e0b40c3c452070200c0312004111440c03194075030398040c52003000c0d004090299001441c0382001038228035050007604512800c644440385001e60306003a080d101c13100c1c0f41050b41c0b1a0646158000014100c15002d0300c101060f03940c000b00e03282401000c40c00c0408294083c400c5a0500c0414040324003200f1403519100c40884c0c40e00740e040801c01042c3e0030084080c0c0040d515 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 803337410 1250 803336160 803336179
    0x2503110303010e040501050a0b0a0504020a02030d0f090b16120c050c010c0305011e35030301030f032c1908120a030b0907230d1b1d06091e 61
    0x102d10003c96080c041d522880003442243e84909244e0b088504485030198030940e20314040100703050550003040408800c0c8180c0e850100e4403041303201580e14a0390b4804030150f03111140414000102d50303440d01300083c27800c480150301d98a00b00400d51444240c071680120f66440c00701500f10b001e441140d9004040e68001e0010005030400030b8000c100910656914502c280301d84040d810210b003204041d995102c503c800c12482c010904810241d109038122061602c2181c5a0b030207110030405503008501c944200408032510741f400800038070412041c6825005090f29541d45000b55808030b8a0702941500c0c0300d040410310441c540c100c0d012950103510a40108040219030180103401000b02800c961410310040340c408003440704d07004040790381e500019207120303401e1904490503281000180002c091385050022042c1400c08031179945062800d400080c0d40c0c684a030310f8021082c1039440e9184000302045503070040c003007000340c0300709140f0610408410342d03419082c0a140c00220340c040c0c0c003c0e01030a076 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 803338660 1250 803337410 803337419
    0xc0f01051501092d05061b0111090306070c11062d03090607030e120f0a08240d020402070f1202061012020402071403161502250311030301 61
    0x20003065841e84403222410440c031400354001da040400311448604108142c04022125043c08a007059a182020003444000142030b43c800e0007401004901420030068510303600690b030308481070b80040d1703480382c04144101e0001da500491001d0317008866040c900c506868500d040da0241001c410540d600810109144803101c3c070880d06001d62408030b000c1e8002070f06c600320080e8241c0c0003c0360b525000b94070800000c2c5889200b031304000e000f1401e48048940c40581c1071b1590f11250451f0300d100c452a500400c0b804a0143d107d00c21680000002c024810402d0070b00040002c0300003200d107074034050680c005080c008c54a40364102da412540046010018905500c1e0404402410340343c850700501c00c0c0c41c0800c3c282103903002800c04440c2c00c7d0b900208a04990382c20710000c0d4000c21010746940e05240100c460b040d02c240010060b40d041c0403c0a000c00c543c92404140180000820080151042c0a48089900d10b041701e800c0340d040c100c00054100ca500c1c5011200c0a100020001040c040400000b8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 803339910 1250 803338660 803338663
    0x309032a06050c03150d0809060708090f01110c040b130e150f0106081b1306020c0a0f0e011a1b03090901060c0c03080a0909021803121602040b04020c0f 67
    0x14954450740041c0030035101d52008011a020540300c280c204050504103000c01d1038074040c04040c1500c600781d22410701d000000010070681203d802912803041c0043c410f0450f05c0d2032140c40501c60300900303240010405a1503000d58411021800d40e000300d586e041c00355003a43c0c1c5d003400e000007250f0b6030b5410b00800150140690300d40a5041e68140340028030320104e180c0c907600c07501080c141d43e140d95031400d00b0f03500d201100d042c020380d11802c916401c00400022400341d80610a00019242c650000c3c401241000d080c084240382580c442107602c101c2000034071000403a40200c1c1d045540441e00704240d0200c2104450051044810003040720060203201c042c2c2c4203010004d055a04e00072542c982c00c91381d031040e00751040c40c04880c0003001102604c1040c00000e42c0c6402400380340320fa925140035182c1d2506c00c42c0040b64404031312500c02000482c0242014035040040d0240f10a030416243e00f4840780d100307100c04138001c0e000000e00c22629141e9000c0380744c50359410b0f6040e00010804907511032501c04c4180307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 803341160 1250 803339910 803339987
    0xb03161206080f0a020a2405070821072003030612031c09110a0326091203070501110a0c030f1206170714060a0503060d0f08041806030f03030903 64
    0x8900402070b492002804031210b47d114003018460650031349130203001314401c6400d0343c00b5080465070030505010b406e240f40b042c80400005d08211a0f8610101c1c14120f501600d981511010b1080d450503c00142c0034011011098030340040c401d884200011445001c440d0139806200103c41408200c220781c3c264201d8941c002048060203100c1d401d00300c0820406001714440c4d00d00000d00910600b18008800d0713803204083c007005501c41c43d1080c1c100002d11001510401615031801b82030b90000c100b40051050038410f10003074400ea013807410324080c5000300240040705401000b07410720050041200c6164002c000b00110130b40e900000b045000d498205046100c820030030700c02d40910460f10085070301184840c150541e440000c28440c00c098150750211150351005087c40e80040e0140e8603200000c8a803140611400d00c0340d11305e2500d1354204900c000b01d2036617003007964245c0d40c200a020008240c888414101c59509841d000c1084d100d14141501c80d4440da00141700c50010345040750000300c4e483e0fa0b14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 803342410 1250 803341160 803341163
    0x70626041b06140304022e090603140f060904030c080a0903030e04050105010509040e01091a18150103031d031e0c01031e0b0d0f0b07090b03161206080f0a 68
    0xd0025254840000700c900d103800c0f84081044100c204041005071800c0104400c01201508000b1440a520070414415419800d1242e000c44d41035041400b11641501580c0748101a0700c003001c2a82c42d107000c08010501c005020980140607900c007140c06c0c14403d0310302c4c540d020703008101507540300c0c139000000f8602800792100703a00151100240006900d004c0c000c0301d0484c2d0050f5205802d00c04003c0422006010b2601140300c02e42da01c01000000a246618103c4414240388074074401d883e202507001c0756101d201c0c3c8050341d680c0101c0d0f02c1503900340d151948141500d4042c60000420080c01c40f000680010800301c440d8188980c03883c002c02448510b1245483d240c003001941c1c140400c0c0001501a1601c0305c0401302801e00e0381510f8165007055910400714590b00600c40c0702420243e8490441c030302541d034829503160058008000c400c54001c098a0005c21096041914515190a81c03500c10081c22500c3d01c100881041c2c801c0c14926142c00c644040d25070030b815030306c0381210b03c403419603a01101c110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 803343660 1250 803342410 803342453
    0x30f0308090f1b0105040915090e0609030a0804150e0a020103200915040f060522060c031107150909050f1e040804030b09030c071707062604 62
    0x164050804100b451401e0b8503038009108201c0381c42e8207000401900141c280c10041d05020006510f04180504c10903a24101184180113040001ba20103a03400500c88907025444803003400f10b021000400c0f9559820b542c90103140c44e0f1124500301000c0444031410010f01418411500c0008102007410a200b507c02d0304c08220803041e0341e030403540010f10031039041d503108000d014140b070500307281400e41c50032100e024941d4942900c2380e585240320045a00700788002034002c158190b10340000e032200034200590a451407096441c0c404003c0428042c400000d080100c1881070b00c18010301000500060101c0c3c400e80d1110942d0940000c03c0610140300e030700c42c0741d418840807079a910803145e9001d0050b00480b0404180f403c4031102001408009401160700f501c003007000102242341c503100c55016914a40295940b12902c1d0b0801785002900d40290914110401d050500c4400c00281c0000300c45c000d040928003a1980e50340071410b086207190242e030860300d80302003000f00300c100e9841d003443e11400070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 803344910 1250 803343660 803343677
    0x12020a030519060807050607050f010509070306060b190e0a0509090c0a0e1302120721141204120501060503011b0206070e0a3620030c041203020a0c030f03 68
    0x54001034450138455410107801c52641880703142811002810041e009500711070004203902001e6007110011030300c40c441900b0680081c820004940103600c000d0a602294a007050030348144200c3e40c6900401d0760040c00380c410600a23043c0c4515100b80000c0c040180320500b1483c02017103513520740c0d8002c0001803141204074404545843c074a10810f014000c0d00404482c0d00e2119401c1c801e1551824404200d24442c80c4d90006420000b04030040b2040c0d085803440018540b50301e01043c0d16000520b9280c4941c002c51a0901c10101081c151000c80c0c0c501000403403107041c1400e00e140180300c2d64001c20303059402c00041c41954402c02c80800034000c80b942c2221a10707942d0510407540410410100303684000c00c1501088210000101c00111060101e10200034541079440160075070110180c10329410f4580303242c0071804a5850711800d48003400c034510b614500e880b8240e007030b00344201d00400a88100e003c10042c05d0520820070030b242e1982c410b0400000e192a0306001501c00f02c5200220000742445 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 803346160 1250 803344910 803344951
    0xc1b061e1506050304030c0c0b0a0f08070c060b0d0512091002060108061f12030807080703020f07080a050702090109050f011a0d09031206060809010b0103020708070b0712020a0305 79
    0x2841501d00c078404007a405500c96050503011902030b44040d0058040001602c2500c020038810341210004201400241d540c1c1c62480c1c00c09020510560000e000348030700d01d010040c1c4641c201d03050301c500c651310010006056600d10002954444050030107440c910403107040c404c0840c0524003d04054000325245039582c109801c041380c3e169824090419541c200002040c03000c042200e01030301802d09000078480c40c0c0e448411600005006001c158005121013060004030783d001000a0b810410360302c3c055240904c41640c52440f072084a078003e06010001406c1181184120300340e440480c0e00414400039940d54051410241c4070986000d07201258038000003c101062002e041c091200c4804180c2c280b0071000000d40c024510b0480a0341441142c0d000718490383c0c450301c5440042c0c1411b4071090302c4c1c0c0c02c05e229928211100d0042860603d481001903a0101d0504815210b0031980891b10f06aa5503c80208403806580d40380f8a04205001151108034960983c00032442160040064054100f99 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 803347410 1250 803346160 803346221
    0x90f040501032a0510020115090c0f05030c090405010b0408060a0506010e091b0a0f030b10021e070902042d030803150d0c030f05120c100c1b06 63
    0x80c44002c1c0843c04180b88003004030001d0004100c031803c40f00c85103142c180e07035202207403602d05160310810050b5511000042152103896603000684002041044190218140a030501203101d8011003400b80c0800000c1404078410116114160301810500041d60754240c1c5910b0780c0c0081c01501d100c0d01032400081c00c50303501c40c4a01c2d4030032901650307a40100b0a00300d05001618901600001c102d5111080d4524003841410060007120016034501e011071000740c100800711103400c516548661491004820364650008020800a2034200d030348428841c0c1b0301d0040e00d09070b11035109203540350000c6000203c1c0e04001c4003030142880309883c030f0711108807803215102908c412400001c0c801601400494048030004e0390210303400340b004c1c000c2454014140c0b03c0107020100e903401200c9440800c00b0315010810240603143d040455101000e042210140f60f0986442c070f1402440709455648006131281d61140003070070705034000326140c10341c010b0503800c001d0042d01c1030013400640d09103c100903210f010301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 803348660 1250 803347410 803347421
    0x70324061a030108060a0e1e01020702040c110118020d030e0109030c0f03030f0203161e020a030c24090501140f0a230f090613180207020103050c120601140d02040803090f04 76
    0x10359201500c2980c40c1081000844126030b0300ca2301d1380790750902c200e40058544c0c1c440d61083c0500c0f601c03088c030318240c0701c040d940c2580d4a8020600504000c40b2041e001601c94810040707016a0608002b4400e04911004803001049680040c00c90640300000107600b041142e11041920701a50316040c030b9088001059079030b403081d040c030403141008249008000c2112480c900d15044001a100c4260407100c1e00000c0480301190010b8410800d20003007000503540750f40750080c840040e26400741e001c6004035001740050980c2d100d80782c18410102c00c00f07240c11054800716048030303040010a41c2c4034082c0fa400104802c42480300018850041c240c248804018030013a84c048604200f50131340303024205007e00c629030308442d02d00e04000c8400300010486444030030080342e010001900050b210201800010709540d0050007001c941242001906400e48801c2c9006a00036401e003040950041110305084a40c400c10701c9129031584082804912924048010228000101c0d0301800c1c12004030100000c641 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 803349910 1250 803348660 803348681
    0xd0201050d05090f010c030f0e010501030f0f030210050c0a143c0703111605060a0c03020f0f070501110f030909040807020a030c0611070324061a030108060a 69
    0x503814480350801101c41d0b009694454000d00035540380800e00c10391030f402e50b9400211038000c203807511303c1d10403100454400c0e4044880c513070000b480740e9491501d440012900842c4050100d0002e00583c20906000300903044400401c280100454588541c1d01c0c03c0c075412012421000443c4c00d41c1c0ca0f14100d03040b10648482005801c2102100c802c0040b41100c140c400c00e00c0c000d00e000072441c00c940c0080d40070002e0403a40d8080c0d151814540501400c103824181c20151401100304c03080070612940c0c4611041d0b902002c21401c12122510b0a800d042e03203401903048202c022071060801800e4042c0d8089000b03012210300381c94500741100b64450b059200c0440c409000203940c41408408814680761803010b41042c0940340039841d010054001c00c02059140d00f050310f104400541c100300441c5d0044404a5102c1440090b10140d411581c908880c035890048295441300407410b001c9950030f0030b500c00802000007580200d16003503565a50f5009410074800d888007802540c3c0010302500083c0641d2001c00d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 803351160 1250 803349910 803349917
    0x5030f042c0f160c0503070b09100207030918090c03061e29180405060f0705120a020310050901090617030c0607081008010212060a0f03020607020d1a04030e040b0d0201 74
    0x40ea203003180f480602207611440800c2001c403203600400714000703200600c121405880d281c18203140c00e041d03407441d0205a100061580e44104007400c003080c3c1c00b81c071280c166541c09110034040f985030003070300700607000c8060050a00840c0442c00420442d0561200713900580f8400105600340b191f40301c0300c08030341c42c0c0d10540d020241c2e41c145060340400001c1000042c0300d4000e01d11400000c10740d07442000034804403000c840075031008081c0290b21295851050b4840c1f0b5610305070340303452180c804010340444007604541d8410b8020020a503141011036403540074080c0980214032540c3d641080b50040d240f1803043c1e41403208a940d00e007003106008002c07911011081c1005203402e495018007155203c034000c04e045074208011401181c8000d0a000a180d03000740c250319543d041c1000420060040402da01400e11621003c40810050f1140c0381650100c0350100e9100800750b14030708204c0c5446150780014940c01c507920003000105504080350a40094069504001080000d010f2012102e070089029010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 803352410 1250 803351160 803351191
    0x60e0904080901140a08041a0702100b0f2205060105070f030e01031b0c140f07260727090c09020a110714010816050a050705030f042c 59
    0x70600400c01024440c4041c50550342d500910707902000340d0b403c0724280000045a590901040c0080c4020407615606d094031004940d0800c0d40f4069603440a00745102e00b41078460650780d01c959281010700300301d1800684500700308003c28580301240c10f02e88500c0c0b44031529080c00708915512a00030343d21000da0001840345000d4080e101611100e03043e154940c1015205c0300340c0d00401110213030360700c004491520303111781c507801e28545465000c0710b4800084803903000c9101c8248041c40011203508980c3c00700c550300715040c0c002e001c840706072000540824aa02c0390010001e0301500c4240d1801c2200400482d040010300000414401d4542e1a04083c042c410040c0f030900c5150806c2e03008005200c0281840501c0300c407010036050034034a50350701c080c246100c0c40c1403100d025600030010319803001b084d2320400d00000421348003611030700402c010702e0704004001c1030310010400204225605211001c07021070700d840d0303a4090b8641c40c40200034206410300508a5448440e85100902800b4104d1100f10002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 803353660 1250 803352410 803352413
    0x4170109050c0d050709110409050604140a180c060203030106180e190e0a051c110712080d0e03030a06080303070f140d020c030a030b01110c04090311011e06060e0904 73
    0x20b0220b02c1e590f05072035502903030100240c0314489126014920700030b108256200e03442d10503a001154001000300703000e5070a0a9658402c96014004168060000e000018542001b880451210400c00300000d0279441000c9012811907000809107048902c10f644165414143c90500b1001ca12584644090034410a000c545006d00d01060703103500f40030454001400c04d10030300d41180340c09490340b070a980d290840070f01e0182410318210442c542d441182800d8000f01203030782500d036542c2a00d1040c40006d26000040408000c8044225014113044c01c3c801c1c04010b4006040300c1d120b6009a41d1403182c585030180010b9480004415a485406a6114645007280c01d480544034020103180344401c00e4403c00000002c1185071010380030301d04004000f10785030500420060212a004c12010341032180c0d40200000d065400100d50b0407100d0305a4000c102c0700c0d19450256400b10b002d5100c0c06240d401d180700000d04c102e01c051400e8926614040030b01917a59111070a803030b4007102e02d8a0b60f070004100c200250 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 803354910 1250 803353660 803353669
    0x10020306040b1801151d10020a050609060f250c0201020c04110304150212011205210903061b04030305070213090308040c210b07020109150204170109050c 68
    0x5030300c0600a840402c2440310400058a0040411450041c40e03025600511660340d98503003554044001e810440c2c803400c15162103480444400e480184a0702c00e4000c2d64406502c2406913445c401e41c840100c951b24100300b400341781c544c03c0449800310700742d0b50000051044265080e800e080040500c0c9148101c0341024811a00e2108110050b4194843c90b4400b801c0703510b941c4980c1811164440c00142c0f2400c05103072413103075002290200d0004600600c4014170544200c06032a0440301c40b034034941160310461510314180b44160086c2482d8448240324007011b107500400a000c5000b04a0030f440c8180d56604a00c1c003005204612400300a03018007089c000240070341c0050170614002040750405103a4040c80c0c00075a1070000d801c8001412620611040240c030700604000340c80105140c404c0103030b117031440a400b5401c0c440083d00030350210000c40c1c1040d000394441340510341c100c030065000c0b030000c5c022207001e50302900c200d8024032400791910618000c180b00304092540e0101c00303054454030190801 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 803356160 1250 803354910 803354917
    0x50304020405060d0b1009180503031612050a06090b092205030f030c041503050c030c180406241e08041e050c040e0105070903080c010612060902120a03021002 70
    0xc94000e40b0f42129000803c1001001743d1041040704200c0040c0342c01d00c40c0400c04d0784c0c001107500c0006e40000c40684005000402070765801002100404400740d5407581c1111120926902c6090180c5414284013003401d0300e4022105031003011000780710700c00b40380d001c4c030181c09030031555a46030031051a00c85900c0d030702410350030004a01071000c403400c1c020075030704c030401561080e01c40b2000305000041c100000100f10416030b4421605007803c028501d403000c02c0e1007041c880104007400d070010026031410f02d6030300c40200381044a4058130421001d9210000703400d034262600d502584005646603649911072003092582c11110f02084549a20340c003518080e107800001500440711701e4000030100f075100d88054104403400303020303500410381005844180000c84160603000b07421070341008100410950000107890442c5c0e4450006070b5649180782a4a0050980341c000054240d4041d40c44003c0c00041e40040c00100d0003214074005911261701081c0d44d408183d8002005a000b04041d0507a0606070b6025 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 803357410 1250 803356160 803356171
    0x4111c170c0616090f03080a0507080c010c0210110702010e06090117040c090c080c0702010c2402030f1503280b09210306010509060c07030c150e030102070201050304020405 76
    0x10503091581500585040c10011141c040c242410a1040c3c0140f41c1e21555010050940c1c41009181e1411030710342d05030341d1107005c0d0200b090080000780b4030304111464044070a500d592074020064014109402901e404204e04140c4416061000d22141c0200c080c00302c1d5240765058442c510060140381c10309c0990341014200c60305100d1986690810f10603030142081c07240303105082c0c02e09002e041141103c2260341c090804000c00c000c460800c10b650841e082225002d42c0c090074035202650320352410b0421812045070036030510200c0301e50015072040b240c0145009201c0c0000e004d0f020780d95000c009480000e0601000e51613480303e05640c5130011013082c41000403090440c1d84410b0384e07440d144e040b6984000d58103581c9541c401103204020980d818816007141c1c01000455140d4104800002c2141c022107404510843d00009c04c56100c86040000030011503024141203407182d500e1001000b80306d4180d52040c0400c08610b0030a8051a0610840300200d45c1611868115155602400000e020080c04d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 803358660 1250 803357410 803357453
    0xc020a0e0a050c0f040302130608010c0536010c05120c0708011d0601051323040510060f0603110d0c0f0f030507080c070302030913050a0b01020303061008131a04111c 73
    0x300400d2501c03080c0104111101c2584070aa61082a50600c40e03602c0701010f183d030440144480100000ec1e02180b4488a620742483c00000303000243c00c04500f0704065210a408580000600780d2041c580461302d10b0449020900030402110350107990269038800b2401c01e0419005040140543d240075400301109800031030b0000f4140030324850b40071020100d240b80c0264007800344100020000100300f8250704c188400c905000480c600b403000809030400d4001d62042c580c40d08410321001c0500001d4941d10b003031900c4280050207442c14043c011321695140303103002890a10902500314000d0080b117000345d4155554018076914142d04003580c2c3c01c6450308030114042080044420b55500300021094000b600c000200c034107050505130103c51200031180d0554105004005559a40608900e111081403c041069a8038829107003000e80c1358400c02072031140215000c150701c0c1910000c003485244500419194055800200591040c0c191104010110707551450000200c800c030030700d803880e200700c0b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 803359910 1250 803358660 803358671
    0x509040b06270106051305060703020606060d0905160509010e1003021c050312010f061715030a08120406060f450b031002190f0c020a0e0a050c0f04030213 68
    0x281640b5807a1803ea102074001080818020303860302081080200410080740c4051030f0800d5039401a440d07020051800d442807601203001003001d03581c1d40000c0d250b10f40c0003040c1e86403c611032114801405460142d24081e00002c030002c9410514082d4a5008503602c0d41412881c0b4034503420007407038045001620b084d004078034220b200060700401c054541d0b4601c1c41103000e801e40c14440c040312005082c0c2c0c410010040380380c01d90703c102d401003403003690800e0703151000c11f08440c0310201082ca00002d0003030040c4241b8001451858035841c84a9084c0611300c5504180140d50340c0740004403014000c1d0050f030111030402d903110094041c00000150130742d08840021490400890f0a0705850400110004d8440ba10340201c803040e45428080d50010000c558011070900c5a505105400204109003a505200e00e202600c10380c2401510031016040c1d0003021511025202c1c4429031000703900360b0f055180a402c1001203030640040310140d035403200f042c0c22054200f0b4655000c100d18440503101014209523100d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 803361160 1250 803359910 803359969
    0xe012c090a060e0c1012110c0d1e0509010804030905030f010b13090305030112050708060c09010f0905012705040c0206061905030307171606150509040b06 68
    0x4118640c8110502000381050884030b081900656154280c820301d1600500c1340c0701c0007950b032100e075402c445001d45040c410000081d50550010868501d1408a040f000f0518a205040025031810307601180d60700e00c5081b000c040a10b8840c540c000008201050b4107015000c2154410201c0e658004d0091814144196803040828140b10640e140245642d44400c2d0810460810491a1b80d0307405080300c04101001d2192001002408103015070080506480541ca040c400d0806c242c4029140281c261069403c050000d07440715400309560501166000320414403090182c00c04800b00c540c1030f1103446144d18070741d140b48402408400c2040406510b888007240545842c0704100c14107000f60001c2c1a141000410002405a80b0104031564071030380a090096072000303c01e8442070703a4001040c003070302095404003100702d00039502503140b01c0c05010131a90900c03096401000d00703019980303180d03000340c1e48a005021881c10304643c0680000040c00109545050001402400c04c03200d1240303844810b280c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 803362410 1250 803361160 803361239
    0x90303090a1511150402061605060c030a050703090312022d031e1e0402131415030d1b0302070503030f04140406030f35040305160e01 59
    0x22038022035420150b60682c1d07548281c00400314040c0300c1540c0000c000003841c03586a00b00d0740000800007400f507800800d82303034030040030304c108010f03220391000c2650030307520b02030305210303883e8100301d4298040038100800310300303014000e11400e81510307010b98a222020100c0d0818074040d40c3b00c10094080030080d000d459040c0703084070f255907840300f00300c040840d40d900b4407070315511001e9016461064030f06036a406019403070416400c5aa003132244141c1c1030b00c0d01d40e25400060383d4102e20010504210341082c0031000e0b180204000c00740307d42c0b40024000c4900d084041499500c1981412001c003241e0701142800003804089400c504c820300c030388100c9603d01e8464000c0b03411500400341c80c000e482c0001c9014441521024115104c140d402e03641040050703e10f440f0404c0d5640140009800000360b003480300348150740d200c0b64000c2c907284070100850004110401c5905a030092006030b641e8000d0105000700b1101c01120319080356000f02d40b44000fa42000c21003003000110601020104c08040c40a2888141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 803363660 1250 803362410 803362429
    0x306090c090d050c030c0906030d030c020102121602070f05150d020d02070b07030c020307030815040905160317070f020909030d050a090203160b040603090c090f02040f1403060a0209030309 83
    0x100d98080c1013628201000d06180003a1600618412640341d000c00c10b090310002040c40400925140200d0003000c0540c003a80240700314110031601b500d00030104800c3d51101010b402a15015500300d56000b551141903400000300d5000b07803584904544118140c114420020b8101e042e80c4050051400c0f4280b8501c030101d07070200c0c4048038828a05820170002075054411034a0741001070020310301d4025a9074009004c21802030800c030a846542039041e9041d161540035442c0c2a900800726003411300d80012140c4605603510045582c804440920340d808482013042d580c803d81e00511602e02441e043d8208040700c00d008000c40828031060003910808980750082c50301591821030001a03440c5d10b030051500b010300440d10350307401904144007000b100039900111001c07120241f4001400e406681741c000025042684420110b0303043c07920340e050765000ea500500840d8400c81c1e005803516036507031202d03103110150710b00d481d07242e0802c00c00503000c01c0c45e64000b0250381c0e5004090b02e2500320a48000b654501c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 803364910 1250 803363660 803363663
    0x1627080a060b030f010612141e06090f0f030406030b010c1502030f0702060f010303180504020c030c0606190530010605040509010b09060d051c030222030201050306090c090d 76
    0x1919151503107081d05041c004c150b50352550100a209940c1403042c440355840c3d4040d0002c0020754140030454010005000800c01400c4140b04c10a00203040017409603110002c1e1003085541c080e14807516541c0c0307400601c20340c680512001840c105460076100303900400341020000d040c80043e001120000700d1503d8036900700da4840e0030040c0c84e4206554146400440108400c0666120750207000c60400c0007040c290440394541b805ca41c4000120320f21900c0c3c071002c1d610240d0041e0000c145c0780048240480501500d02000040ba00140e0314a81003010f184061400c0c543e1940702c007001803007a4205040181c6000d400f01615a400d034007602d02d442d0500c0030070000c0c484c842e5500d4005104a18090007415000f02848000f40f10b55440c20300080c1041c04007a050754840c8a50b455450b0802c04103200d11070719400c8415032092000e644d07090140c065440141c191031b203820168032612410030341081381c000340da4041c0d441500310368402050101070341001d00b11a1a4440a111603111542e0750001030502d503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 803366160 1250 803364910 803364923
    0x30c060c1905011e020301060507060507030e19110303270301181101020c06031e040611070c0f050324091e0d12020304031e0504050406120b1627080a 66
    0x10162034900c40b240001300e0803044041d0040004100041e8484c090750191500181e00003031544520b00281c0c01084001c80d03c4804d030140400e4049180590402c0000c0036002e981580d030041d2000d010181c0b41e00c5442d031250341031030000c03140e0341c0c80303d40d001041210b808001e0b0001903180ea0440303180200381e142d0a4101c80c0d18218501e04039003940d0620011501c0e01043d91074034103605206441e9000c5d52003038400e0f0356200e285a4001024020b154111820500704c0c40d68141d92245c0d1400c007442015414041c01c01601001800000e150038000380c240b4401131982d00620340c0d01140d00b140e22a2010140680490384140000c121264160101440c182c070002001044940312409010341185020386503414002c3c41402000046500040000282d00602e5001944076048280684860140d40c21141d0400e2030444007080c201c5111042c480350a000b546040e125036100b206c0d0448964400780380c130f0001005c2c100405c070948540d0545c01c1d48100d44400b076205482e1240c01c50391030a04080300039582e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 803367410 1250 803366160 803366171
    0xd080c0a02030618010e01200d02091804030f0f090e040503190206011a09100806010c0f0b0609090c0a06140c0118061b1b022704060614030c060c190501 67
    0x403a00c0074800c04c6c11081c2000001c0c0816034518044846200011002504080300007445d0f050446040e811918640401003140140ca000802e021541280444c0d00f03c02250800718070041d814000e100c001e40034004c9503601c0161500b016043e1100a501070411203507480188062258a5100c65001d15100c44d2980203150720340c0351840d8560030240c3c03890345914000d070411650700182c4600b0107105050609003011456900e40b10300403601c060300101c1c090501e290303845a40d070402a01c03402e1a070050344101c6e07c2c920151544110181c9642c0502c540c254011840913041181e02e00071001c100c0366526222199040c056440d529500352813011101c1048400d0b0004000c042111500c03c20109081e8403016205007400484060503142024007001c8900a000c1001e400319556401b1400001000c40705044c2500112018503901c00015035003101c03180c0c248400030032001d641c184d800e551404010001d203200300c000e10900081e40c0c461441c00803140282114600129a0480c94183c40c5104000000300c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 803368660 1250 803367410 803367451
    0x40b0d09111008010b09010c050d030f11040e061203160302061801060605030a27030c03080a0506010e1c06060e040c06050301062708060a0b09150d080c0a020306 71
    0x121074800700741e1144070b68a60066041d46582c4189100e0548441804144e0349801440040e20041e4030240d00800a00c2041c5c030140f44c40390705030441020700b40d800500748219103040348480003c1c0914000c08020040840004506141900180c01a2240d420071307a4644000c050040d00c100b2091041940560320450602082c2e41d000810b0444c2556500c3c000c000042c10400c0040c542d201c05801c1d000040e843d184c0b242c0258801200300702a801c1e0751408840e88100c3c0c3c0c5005040182440f5083d800304007082e00181e01d01b901805031034401d1031b05a40701440c0c80d20130010404030a45594082070400010400f8000080f138510415000d0401c02144c0c0e08646068a040074030407000c4d1b001042003000c14001041415000702c0f5045883e04081100e180c24941740300c0419240299a0224002c0e1140f90203000e034540c85944040800d0030180c1d00489143d071203000b11543c245184051302d400c01110700803c808603100304054600484220300380c1e400a80f80d500086d1030704200784c3d4040c44604d01d00d8030480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 803369910 1250 803368660 803368673
    0x1e0f1415130f02310c0206060a0501020d1d09010e06030607051207200615010908030708070f051002190e01020d02060103151d070501080c0304080f0a05040b0d09 71
    0xc0d804540c030070498120500700d589000500e490300301c0083c010b03209400e043d22500100105503451200240c0201484c13141646503e0241c840c0c1807140c8054001c2001180c55411b0840940c015500c041c4c0080081c03824801045030b0b00e00c2d0341c074008020748548036510380302a43c40000881c02030020b40800a00c5007007107000c040c18240007a10744014130401f00401c8200e0302a400c0c46591008450600c7d403021090121188425620b03551501183d004000402c15007548140011050510a9982545035501c0c0e80d0780e25901d01c91004050041201030280320002406a040343c0c000030b104501780e81c08820002215010380e04030f410794842d0030703807404048010140c0c8582200b0a1030024801002d41c6e00c1e02070006519001c044c0806030442c50030500d00750840001c1d421003c291040000381c0030000138500c03011503e81c0c0d80d42c001c403800034a003000800c0794541d140040c0e0f0b005680181c000c0d4504244090203101c0340e480a12140c003804014040020b0b010000409464000704034080800d01400c9480d00c0f1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 803371160 1250 803369910 803369953
    0x27060901050c0c190f1a100602010614190305070f1d0c091003020c07120501050c0a14300402040b030d120b0d05060709030b010b03041e0f14 62
    0x51020340c1050081c0300c01000001440b081054402c13031842e0303001d00c090402a40d0f0700c1100c08080c21800000e03900c110040c5140070740c14841e0200300c0c00100c0c00350719000102d0907990248144005100851a09040d80c82c01044400300e804103841000c03c00d0b0f55a550707003401c14001d42c0c0f00810280c0846001c00024003181c000041890b1b060214244a01d0981d500c0c428500800282500440180d108050000e001e51b045540c0d81c8014403c8483d076075034440303484001e200401c0040390554203002c007086800040006881c2541081e4655130500603055081d03c240d60040c01240040c4110304800001120b2050854030001b84591514456450f280c010b02c400d9400031101240254020b00301251441d80c0048580e444201e40080819424505400105800008031003d46540101000d005140e90066601811203100e404458043e0780e81c0c00026405000496010b00550b11641803030803080034048511040b1485440100c241c0c804645920b20880e104070b920389015400442480304103884031100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 803372410 1250 803371160 803371171
    0x1b1207061106010506040b460e030f070b2107050d140603060a0b0607020a080a02130c0c0b09030c0709231302150c10050609011502060f2706090105 65
    0x501d06d417520700b000303001aa12407401c3c110515603041c01e007805002c103413043d6400203d0b02c08001e090014400d4540000102d440300f4083c0210f090321000244600380414140a41710501d0040c2c0110b031301e0702c0415821540500441c0b10b0741804004604460300c0124545400f41d07a0a42c1c40d41d4a40c150300c1d030084111885441c07070784a100c0e0403034200051642d0000d0141d5002e101c1420201d254040381c40840d160f800b600e10700950117a4040404a1900700009125415a008407582015010240c0d00c1c0011a8090102c090004030300021500100b454800a190030243c0c8004691400388444007150804c1c541c0d40140e030b14a601c503001e901c0580000240449100d41c0022081410305009800000545141ca0006c4c011039924281d00300d0307141c1030029111510020b0080d6140c1011050b401c000900040703500502c58403500b400802c4a90510b00d044ca0100e1a80d00245002e0311032042003000340c140101401c50090500c410004040c044c088407400c50300741c4100501c07050424503000341c29030301c00815 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 803373660 1250 803372410 803372419
    0xe030c010f200726270901050d050d080606071b06080109020c03030a090212030304030315151d040b030a0f062409021e03040803160e031b12070611060105 68
    0x640700400c194401ca03000d6421100b9a100d030000c030803400b040890140e5002104119992040e098045c0800010318010081c1181c0c490340c1aa242d40401c442e03030810b00030180103544408003030388400e07000d22907964109000410507408e03d000395607480b8202c0040c10320300f01407403100b0b042008200c3d003140d5000c1c0502803000c02035007070100c610310040c4d072400010b00c070541d81519900d0380d00964a03120000c09d00e500035002500d5030f910b02400c0140240117880341e44803003081c005400082030310780c503000c001c0c19800c1a82e07048030582d00320301104ea56407518801180d22550391f132400d002d6580c04014035981c03244101940050b601241c04c2c280100c41916800002c0040302c2008040303148080a80142640c65900006850301094499080d660b012041682c00101d400804d05c41404880000b030b505ca040401044203e1440b1000b040b1858015141d05507055070103030700040030b102c0300740740c8114a400000d404210441e4003044000c1c0752446650014000c600304010810302c00005004031800341a0656 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 803374910 1250 803373660 803373667
    0x9062706080a0b0c0d050f07020f03120601081905130507050d051c090902030403050405030c010e0f0423070c031e0c080903010f090804060e220e030c010f20 69
    0x1000580391420300d0402007215a0000015072003030b54138015202120030390f140c10402813905660f401c03186081a200076015100321840c520010030000116500750f40143e180543e142c550100548440300040c0200407400d4501150703198406d500d2080306e124405185140c15081b000381041410140b2640200e070041c1c3c03031215500003040d0002541c0704020780c2c0300c0000101e42c800880c04c50b100d20b826000b8000c60340c000001e1106142d404405801965011401e0341c1c26269500b0041d1100c1d014030a03081c6c1c010000c0c10345049903240552100042a24150801030746031601c00040d070400f0421102000801d00c1c80c03440500303265100790b1194107035140342020b100350189151701410f00e00c15203c0040c900180058055010f40b403c3d080424200c08506040c001401075161004050300940180c00000d003980d40324001601e0240b1102e94140321800c2d4480c5045400391089000d4840c0c0d204444040c80200210018203609100d07840210719507060025080311119a0345581003d09406008482d4092 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 803376160 1250 803374910 803374919
    0xc130506040f06050705030c01050103150e0d0c02130f06120b1803160f140601061b080409090204023a0c0f030b010207090c0908062505090a09062706 66
    0x202c00309055406a0400340e0b1503681c14504a4030794424025459010b50800e000003003040542d00c041d0034482000c8805001801030001e2141e41c88001d80c0310200001c1d18003d034640903090010701c4840880e190701e0042200c554076041281500c205034441143c2041580b01c140c14000816022074020000c0d4a06003d0841d4082d00260b99000d0388481e03145007450740c81c0900c1001241078800443c180c1c0310180e420101c540c1e42a50380c88050911602c00440c8031009140b10308880340c4020000f1507841003446040a041455000003050b2000d82240c01c2a807c20212690b411001004181d021481030a40e161628081e060320030548241180304050342811543c45103250008031016100d030302803034000f41e1000f400380100c0c5414241d0307002c2421b032850500780020300c617408202c2c441512006412a043d0f6101e810807150051210300410645000d5100c0d00c010091144004040c038981c014150f1058640720003010717007110003d80c018020100d010280c00c0d0902c201a408040c00c0ca03071071108004142c0303030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 803377410 1250 803376160 803376179
    0x5040201020a0305130f080d0314060a06030e0304120807030f05091305040312020a020f1209031e0705211e1b1801060c05061311010302210c13050604 66
    0x80042c0241401000315101801d0328008002e14001c24030f1003017818144e07a84140325a10740c0c2c1c0740d0b100b1000281c20000f000c85240b0348200d02e180510009044451901d1030100c0440003406086400c0d0301c580030800000615070b031015a010342440c051403100ba07079003d4510b03000d402c540690380c00c14144201401640c0259440d0300001490030f5500c10049503c0e030319442e0480c1c6111020b040300559500c045000c440c503e5000680381104a5003030102c1c0e0350344d0104a000c5410b40101e005082e8564410b001302d0040862402110b41c1d180601412603051644480009a41009846035480300020107200201b0769501084035100025100d800124408110074250341c8030348040e043c8181c14450b0041d440e9842e01c2e6400500d18401d40c01c1c0c000400741d6100d000051041e410040251250321407080803901c12480300d02d40f5000258070a03100d4024041880041d80a0340050301202001001a904003040581071440c0c01e208480f4420415912106403a294003c01b90581040d40203802c00d00041c043d40701d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 803378660 1250 803377410 803377423
    0x5010626010b1e011b14010c390804091b030510030b0601020a06020c03030f010e071710030503071b06020309030c090c1e1c0513390f090504020102 65
    0x12481c143c0442c5071102001a502c507214182c40d05803401c0070340c555209202110380c240741c50885081c002d100c0301c2d28101c002c45491201c030700010b000c40c09030402e40e008084508691410030400c85100daa1009182e1104501074201c0e81c4107106c529240c07a000800040711600c4255031700c82c9810208403a091035211410001914040202481ca680010502c00ea00800030308024503400300040d036486003021001038030303500f0545010110b1012800041060140300d145544030356025502d050844010032101030541c1000703482d107144c40000f441d020020407014802443d0003402030055510180751418500070303044061740700400b15042801010550380d40440c00c501820360403100500c40da03c42100d140380d03500c0707001100305040000d942e00081580f04000902a003900c22004000951404480801952000c0f210014404499002c10000820341c01c0400003201010256921080003034802842000480d0f06c070450148100000704090003203c0c0c0401e0107441c5a000034072080c141640003030b42d281c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 803379910 1250 803378660 803378689
    0x17090f04050c1920071401020c010c170f0d0209010206011e0603020f0910091d0f04021c140c030606061e0313060504240902030714010302040305010626010b 69
    0x180420906100c2841040c10340c213508051458010b1031880c0c4001c20b690b90070307103214003041c02403141075002442d8004560002d81580c1a1100c8039016030540d10798481c1e0210b8005100100401c4c0448000100300c080508003e2900d4800103903540000000a40f422a05070300c001c0d00d950502103041c02c440100c0600c10100c601a00f030142e11410004900d0541e800743d010f42c0c54101c44084d4050321101d603c68a44400c44450050103158501e45005601000c20201c51441d0740f1140034002c00c0060a1802101c0c0c0958420911040300901c1360350f0f082160004040106040d80c80742141030003030314050106940220040324490b25000c001c00c007029150b0480c8100860503600440028090001e82c02a00c0e030050340304808214500d41031404003031062621002c201940042c584072404a40c00b44505803400307800500820700d0514202d81104a24941d03228103040503003d000010000c0e03424005c002c06080022003440a40707072443d080a000c10321641e90148540e040c0b00800c030380c945038142e054507087c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 803381160 1250 803379910 803379937
    0x90d0212090a0515040f0909020d080f070212030301080f0c090103060e210a08091615090e090a02040b1804032d0305070210020c061f0317090f04050c 66
    0x2a01650005810641558032164216812001c00d83c40552884d0003042a04e80007100d404c500d075102c140304802c0320380c105002508009040300d00400326103e80090502201a0050703103151282c50b40c08503081c2115400034108544c170102c0140040700e014400503804a81c0c11000300340188034140018103855040c840070380850340e42c50510704c0904003031100c1020410101c00c0c0c03400e2010039035070702e044a91110264200103152180814402c220106205104800c00641c01801d1414506900d005c042e10412500501c0710507000096010442c0010728840c81444019062440d03140c0184010380704001c1245d44911000d02205001085080200e9000707501884d01d0742444011510503440746065410b0038000038107610800e40a50b905030401881200740da42542d000022800d11030b0700380c1c094529603520b00c0d08450300054400ba80d8244505410101d000b0a4071070b143d0383d445070741c5618400c9030904510794000030318010300d0500e171031608040c040644007004145001761241c0f030140544031504001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 803382410 1250 803381160 803381167
    0x501020c060904110f0313020102073201030b030d0503040c0605090607080a03090b090c0a2916062c07030b010902211003030908010506011b170301140306090d0212 72
    0x11340001e030141e075101c1c2c281c07400726581c90900d82441c03050035020203803c034018810b8410103e81c41144501da04d400d0f01001c001d5402042c01507400700c1c04e11069100840c1056600d1906902c1550104a03140300d0b442d29413901e40c0d8034145420007601c100e410303411030000c4c41000c01c0210000d4a0b014100d50400e03410080303968a6040001080340038085209014200904407818050080310224202e5000041220581c508658600030322030300108060180d80c0f411080340101b2500748180c402091040059400001c141c0040e5541908588441141b120004546004800b00c2100b04100a8422009000900e061461036413401d8038807105000e101107040d00409c91341283c10640a4600c08110f003405a0005498441350209401d02188002d03400a5500b01000a824a040c4504c6004020694407400340701030004201d41c0d07000000800702c1d0208080b48014400200d140301441c007810907042c842e5520003803542054608240600f00c1003160f000440844c2c4010340000b01e03070f44008080725a061302c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 803383660 1250 803382410 803382431
    0x301050c070314040509010311030f1b0d02010210060f0806071b02010c020418060b010e0409170c0a0c09150503030309071a13030b0919030206060613090e0114010501020c060904 78
    0x1600030340d030045e50000703411000032007084072030402482990300c254222002da0360b01030400c0381d4640b5807420401100d000c4c103440c1440c0d4248124120350081c01030044420000405030160111122680180726901040001b48034603003090000079003042080c0f80102c003460406001c910602e4400c00021305101c10004c11100710340310b680081205003840d5510320507013109410281e01500500718214000354107000302c040d4a2826200d80c0c00b410381c001120342c08451a0440400d4507501800403d01039114100481000911103c8810301400521b480030500d03408000c600d02460003da080140700342c006100b0021301450001e032401c11a41c80c4240701e85240c000c004030a43d21701c507001c03400e540c102800e10048140440110b185000b080c00302d040300c80103c038500064011300c1c44075000a00503040b8074082080e80c0345c400c01400c01e10107020300802d0203503510a894411103014030401c4071140d4640c4101d5003a48201c47e4178074010071083c000b0f00003540680c800119140700390701c4458803940d696480c154 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 803384910 1250 803383660 803383697
    0x612090516030303060f0e040f050102070b0112020f0103020c030315010e3a030f2109030e1003050105030d1b062a0207050d06050703091509030e0301050c0703 70
    0x451036003100c20345029600c0041680008441800250007080c10301a000800041e5483c601c41100c04c042c8102c5074546455071020710003020503605950542d000d0214802042d0f40003500307802030132212017198030881984140074040c4091850581814810312184051042c080300304c075400700402c4000e0400b0701e07c40006032404628400c940e500454900202d416040100da100354040c0c1e2420a06181c00e885ca40401140940c4140010f0004100380038a110140c02004026030b500881880184900c400308082e03000c440440c03100780c0000b030074000700408604040311400d802020318602801198105004255154000124282000040d602d001c1440603c0078038801d03055401ba8050003544888280043c0c0000c002030074284281808041c904460300028482d0200c990103070136070103011210345907000100b200400105c145038942d1842d400103165036000c1141c40085890025105280c1e04000f00920f40410001e03000380c0c904400c0c020240000301c01d5440c6d1540c14644620707028007106828 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 803386160 1250 803384910 803384921
    0xc03070f0f050d150317040503101104031b08010203131a061e0d140105061c020907030207020d2a0626090f031c112b020c030705010e0c010c08040612 66
    0x352002c2500d4030300ca01e00006d01d6005004884040b000c644070301e401e4192042c01c464002d40c00248031366041104200003803a051a40182a0160400c0405280d5a000b4142603074070448102b0300110240d00c1e5101041080400d540108041081e9500140b901001099520703820304501a0150904c0f0519400760340d44c2070312080425400344100c4503030381130869104d01800301602c860f4810301a40034803d500c0d00840041c4040744d90001c3c0080d40380c0c1c0352510190000d510190090380c0055404041d10041501c034400f21240c000c2100c0310820b2601d0340030140d010000349801c404100001940025800101042c105020880c01801984181c03142d881c0303140380c00074000030302e8001d002c0410303041d920b40e1000168082d0100040c0040c0228001c40103a106540b0443c03607103481e00f400350101d84486003090340790809030b202c50075001480d001200c031a013440c50704601c50031581c5039140d9012007580303030b024003816483c4071003030070300b6520708003681c0e1603010130b0090703019070810090036541c201754020294010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 803387410 1250 803386160 803386163
    0x309060c09150c010c0801080d0516060b0405070c0b09010207170d0e16150f2001020f0714121608030a060302060d02190504060507020904050a0b0c03070f0f050d1503 73
    0x31a41c910070b02200c3d031301800300382c0040008110028000603500d840841c03070607000c0c642ca80e51a03103051400e500315402e40305488001e81e40e07143e03070750440c8000d42c030f0701d200f01401354550303071600c081e540752914009240f200c0c01801c40030183d006120600c00034801c050b0500c581c0304410700729502e4080004ca010020b005c80740c4564458801e42020b01c0c0e075848290000b134182c80c40d001040018188100040d145440c400d1901e2000a54802d08100700b40444480e80001018150000d1316214500a800c9015003115400717a80711071034603661a9401c0c2040100849510741e412401d07007081000840090401e40c05480541540303000800190075105951192025640c0103207180c2e25050380c0001d15009412070750003a8a0440c452800d045400c1c05035007910b0440d003141c0e5070306240c00c08550900143c0d06028004581c540320b5000300710009000700e040148900d80c181c12142c3c0b00c0c5400c01004100e0312210840005100c2c4401d60710317500341d9100c0100c0304180407804011506111300c4103140c400104680c070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 803388660 1250 803387410 803387449
    0x203070b062e020f010b0a0b1b071401120902010e1203040302030109210306030507050d0c150201020a02071418060303090409030201020406090501050f040e090715020d12020309060c09 81
    0x10205010007811401002c91555803c48903034142203020b2900301d0300305e0f4031030030f03805039071480c0410692071590001c0401c0e10280ca40405c9500741001c0852030169550003042c1c06110503500c200f201c2d688030030090000c3d10340403018040b055143d00041d00302c1c200601d0041c01074030078418003618018100202c400441d4050700801c0802200d00f8404d80400b15045030b40e2401d01101140174089209000300429250084d0141000714a44030400c01600c00c8141e003207038055050f100c009125200000c1d03041107614580c0001d83e50b800030b00b00003401e1202c503821032141400803913014030281d100c2446a01c15031200c070301c0c900001d481c0c0c480081c0c51400385204142e80710742840041001c260341034000d031048441a444108125480324015501c0307000300d81181141010600040226440d0340d000280c110f0030f90015151000c1e2a4080140d8400302013a00001503401030741d00480407a800302800301c0c1040d50b680d0440c11414881109504d03103c0140000c0ca07a07600c00304001c0c03200d95880411200c060807000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 803389910 1250 803388660 803388709
    0xb070e0a170303010e060d022b140304060201050108032b0e0a1a010f03050a060510030c0905010e010e090c040b0316030b0901060b21041b0603020d0e0d0203070b06 72
    0x40710140d403a8000d0152006015600c4045009400d10205a24a0031b03801017500c801800c3d0040c605004424000403080303822603c4d5a0700011900c000c000b5a41040070f81c000e9035495080c4040603081d5501a80010762680c404c01481948003582902a031100410710b00c072000c0d83c2d42d480c040c28041c00d00810b081e01c450250444010070880d0030040c010f403101d10541b84422580ea40c2c9181442644c003440b0240c46a0044071a0b000015001d610256004002d800b814484948030341702c100052959400c5860a1580c0710300510040c1500c1107001d0040242c4401e43d406440c00d001e0b082c0e00c42c0e080241e600e01441e200d031000c0000f607400344804603118090203050100b0682d01e050000784e511003a1800328683d441c161000c10720305142c40480701070315000564201701c01510801034003108802001034501e40025420703c42c8030480d000c8680010700107a40c0250b1125040c11106080710305281e42c03100c5a0340903000411444d5004410f07541165003103200b201c4165143c0340030881e0140c44044000b04180000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 803391160 1250 803389910 803389949
    0x1230a0905012301110d18030c030f0605090a02010f08090c060a4b02031909060806030a03080106110a0c0306060f0b030105131d0a0b06011403040b070e0a 68
    0x11101d1030180c80e03c0b42c0010440f60f1090054406203511508001a80c004001101c0440e0081980d524035022504c8180502036481e01c0384a0060034607081124120005007031113050105a010b51a000b0a00201a0815440c00e07400038142d0000315003984103206c50500000d885000901032001c0722003028000340e5484d10301c1b0700024007041d40c805045131803140c0094410303281660f056028090007007a0200081352a48a0a00f90000350383d0072140f011132004004080c2d100d515103e1a040e20705060315554036a42c1404806132600c10002e0599001e130f80074165440201c1e0303021203920304484441c01c0a900225038864120b0900b0a1034401800030444010000104080c2d07030b0010046582c200041d441003030301e410000b9040d21080c89120380c010b49601a00a510302143e00c03514141759401251109001014050380c2003040c090000d81d00c404c0b403d403c0202c035581068441c410001d00b5041c0a02e50714240d2703038414110b8406400b60040288800c440e0206841f10140c4102a0211204000401110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 803392410 1250 803391160 803391179
    0xd0f050d0e0a080102030c0405370f06030b03060c031024030506010804050a02010e0402250b072a0314040b0307030b040207050c19091505030f0601230a090501 70
    0x9111490b018010803840000d1403541072003901d0156202c02d0b0128506072803c41040f4040700f081c810604c1c1e5040120079101101050003088080701150802642d2161400c1f091710300e644c410368442400d01d41000e0150407140e401264032030780310500e1444207032a510307502d074200d201c0141c54002004841c01c06204e034502039a03154200700405856036081c000b5507260401126142c03810348004040364090025440198090000d0084045024000504282c4005620200c03600c074410020300700300e9402c99000901513806416644100d03d070902002d52404841c0200d00032640f42c41d03501107840240303079001c04c252003800250740f160742c8a11196191521000d2941039a4025200070020900d003103041f801c0c0341010700139552607580000190403400307540018043ca84110758402d03040301c5030f607101c0400e40038141e101c0e0030ba042c0c5210786586015400d060925140c240390007002206c2e50b000c20010080d81daa0685004046119003044400c046142400320380a1451a009082418100000442e04482 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 803393660 1250 803392410 803392427
    0x14120c0f07060207093b060a0204050105160c12080c06090703080d1e06120b0105092512091110030903080c1305040614090109021201050d0f050d 64
    0x214001910910a000c009465692405105a0740541c00100d410030032034080b41e10520b01001403d191440e00c813a1886c0084d5880403941000301280e501c4429240071030020011242e0090701824110b15190600002030081d01035401d14610200c06901c05404008000c0c4602000304a1800c0f00350b00c011703880c500300100c0d412025a4407000d116440016034990000550007080300e03088110949000c201446c1c05c0013404800c0d103904200000c070002d110181040c0e05c105002454003981004d511011850306050100040e80700d1031003a000e8809002c20507960b018074036814070051255005031101d001064541e01303200761030b0001d11494000b1001c00d00c03011151022421100725203451054003000b40540c105da40941001d000030300c505001810f030025410080c4010210140090800c47e51840010207564194100f05181c000f1450004118102400b4031805084041760540c1006200600404603090510846100b21b4540451105012566440c0102d03030350050152002d00511a901a00720301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 803394910 1250 803393660 803393677
    0xf09030d02010501031a072d1106010518060120070609050306160305060102161e0b0406020a081c05040c081606080c0307140427020702010503040b041412 68
    0xa1445940c28661040c42814184d981c4580441c2401040202c10000700200814540c14004024010350014a42c3c0026083c0400070250783c0c0f400e1007410f0380c0100784000400d21140e050340000d005000315946c0c114081d0104543c0f6540c030f001d07a511000121080c80070500580f02d41c0e40407c901d0454043d000c203020f002c1d00c000d91103406100382c0e00e109140e66403404136005007000780a0b20703440c4241071094101c2074110b001481114000101c005001499000e00e500015100106000b01d130810044c841d0300790014030000b03000508180c685003000e503d035030303584100038079010002031115062003248003030f1101041c1222042010749418506260100b003d030180010344c1c815441c56402040155012109580060780c03483c4103621600101000b54001030034000502206008040b05000c044d8043c20042c207100c500912a240c03070010861032902d41400c2e1021460040100f100980d0300202200d8001750302041d41c2d0b440c2c1d41c071402d1070030040030038600d02d100c103014103120040310004120141401e1b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 803396160 1250 803394910 803394913
    0x100b010c2603090d090b180d050c060a02010e070e010b1c2a17010807180b030604030f1b0b18010906020414010318030e1002010b04060e1e101401030902060f0903 71
    0x201e444c0d8106c14a18041c0190890740403081ea20b400f803407401d00490642503580701d01d0443d81150049400242160410102c0b4030050799203510300d41c051842000a05c005050321503c13800c1550400e10000782c14891500b8400c800190b900011080307017199070141c081c0032511000718001c043e80720320061102004215a8000800c0850f155240a00200826049409007001000711519049441068480c45110708036100d5880720b101415807400e000c03452085100f40d5603001c0390341c0c14880181203030440310024829841c48440d20000940c84401a9811007000405850030302401c3c0d01d11405080e0f4600010040707400440c0000e240010f0002c42546003000340c800b40041c034608011059501c66085003e40041c0d0b0483c0040d21170300f04441c40038806a21440086014400100401e0603280c0300d03809415030700308580030001c0c0310914513005800342089842001c220300700000207241082e0980203881e400c40c00e03001a03002da0380c040da00500d001a80644440c0e2a0050a1050a51a000840e126009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 803397410 1250 803396160 803396177
    0x3030a09240f030e0304120b0105091605030103020d150e0d030c0203120a092315160206010b09060c070b0a090f1503020904020903010f050405100b010c2603090d 71
    0x8400800c0c04030071400d10581d501941011211411000341842641e0044640010000800d55000c01c0120400762030103030312001400c0d403410061003000b083c028694010011444d500100481d4040110703811680c0403100000c140007603007015049403200c413203030046051511440a22000b404035004101644a48040140c0400100142c2c3c492141c08030810b0203144030300010344103001c1940101111b5000365044040d06091580503950b0031584170210702660f000300c0407003210258070941543d2000801400d1a0070000100300651746482c18018040020004107407007075152206800c0e220107140f502c00b201c0074255030f02503c1da090340c0800c4007140002c80070000441e4440d070b04008a002c442c40081100b40305103418404400a40200300c8040d070058080004016642e024025100c010840000004990505252942c83e142c240140124402e0600101040d02e07030b08014003c03922600b10410000b0380201c2d05502e0780110f0074281100a410002c403e2083c8000005440000003c403612654103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 803398660 1250 803397410 803397449
    0x3062c070507150c0905060a09090506220509030d0609063308090a02060c0625170c04150906090e0c0403020f0f03121305090112080304050c03030a09 66
    0x400e881003010142403400c1d0003040d683c4007002544201164501c2c0d01e003110794291208001603076507000800190000742e035070707400f07008445091103440d4204000b1601e60102854050300d250054a080d0001d0107001c0da1940080d021207000d000f02d888403014110100201c1c0c3c5c55110b000014851806858451081806801d00040850003116551a910750181c0c1e0f4017130452804030799284006020310054080c0301103440060f202c11015101840c1c280d03018010074600115407a080d1183c41200040c4070702d0b4500b04c00c8440390040c51421283e040c904002060781d4407420810511700c00d0fa07002d017442184030f080c0c04900d02e900071821401d96005950f03880c60b041e0384403c1241003010540e03a070301101d00100030070001803516010304614968003030654010000050002403d1030480c18080c0300e80074001030589044505070310500d02801c0c01b194520150750629080240c80040d045005180e024000041130603c1020040c90b079064400404496071354181c0f600040101c241803007607548421000d0117032107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 803399910 1250 803398660 803398667
    0x150f23011202061e0c0a030537120e060901140a050405060609130c080313060311030a020c07030b010b1207020a05060606130512030702120d09030206090103062c07 72
    0x64540040040e4148040d000d03001046005840c040c0d528130340104245c941c07001c0c0078018200758034000c0d228a902c400d038801c483c485940d0080e440c5841d800c034039a01c810075141031445005034201c15203040340e03a040300c02000c1402495500420101840b480c2d0401000c48070541201c00f29a4501c40321008544a00c10a502030356030640d40200180c00a5000031158104592055403107000d0001d00e0948082c0c5490b814180141070300301c2080c3d42c000043c03100001440e0740c6003000030030440c90308000a803510050400c19010180440240a40001b003400070030b14204007500c0030703507048039540340a541e44146442e01c651100381607940d402c41900000d00c1280c00800e5499040342c101000e0811781da503520401c601940034140c0721202c6030507808081384036103803442c00b9149683c0440080d562101d4500400000d4014504031801e660b00101c044d0181d20b9000c0000e0046940c165600ca4807058a000107801400c0c9a0300310310010241c1075a480e1000c1c18209202001c1c0c64407201a103080c0d11480c4046 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 803401160 1250 803399910 803399939
    0x1020301211707030e04020d05090c27060609060a020c19060e040e0f010603080c1209060a1202040e04030e09090705062215020706020c1c150f2301 65
    0x1d050580c08100e01c00c055040305000700442842171908901ea524003000140498212001d4107800599400400016401c1008800420101191108200c00030341c680c40b840860b00e020079006102000700458160740705c035004c9d01c200c8107004120540719042042d0007903aa040285110b40b10380388400c04595442103844500c1c0c142c43c800e5440c0e00d080301c2c00307105101c0507041c840c00014041c46001d19002d07001000f031165002442c412000309513240da80200840c5410409030395810044010808400e003603841071308840041501c0d081c02400d298121a5500c028011644542010301200c0100002c15074800076030240038504580450940d150003500076512030050107003a4014008020410303c036030495050207621002c01c1d03100c000d900d8580c01b040c54071850501494015902614050128079014804000642d0302500c491045d00e64601d4003541c0310b141100040c0100c0a08008020070640c0b40e0404403c07401021001d0100b07140e00040c0701203c8840301d034001c2808095200204070300c4415000ca = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 803402410 1250 803401160 803401163
    0xa0504140709061b120c0b010902040317030112240c08041209140103090203122b050c1603030209120709140609220f0c140108040c06030c0210020c0102030121 70
    0xe14050760f0440e139414001a80c44043e80d41480b180811506c0002c1520600601030503c52102607250b504e50b283c454040501e02445040100b000d00042c8442a11145500c0001c0c0d0410041030007200b0810580b02d040b0310a402d885070079030904000950b00c58010180b280a175214221141c0d8030020610704889a000a0141441101009040ca246584260445014603000805035440b9840004880085610040c010211312102d01c1c0b005441d4142180d80d14042d40455909001c40d1031b01e1a45140e0070f11400400d40005207441c0c503504c041c14400d0741a250240c80160281c1803c0d15400040c0c0d0f600c2c1075500c202160181064070350241866420695030042401401540241d210b01035090094001030250b03041212165203120007041d420301154080901981c0000342c4d540c20443c90202ca00101384059040c090503d0900c0001854800d01d1022546c4510f00010000c03040401207080c41c03665801d4000450000c50504c914003819401541210310110960164004640c0310342002428100d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 803403660 1250 803402410 803402447
    0x450a050d0503090708030d050f10080303010603020307121505030d0e01021f1103010905040b0c0a08041104061a0c101b051e0304150506030309030c0f0a050414070906 73
    0xc0a090a402880078642040848041e02c654684400d406443c5401128000d40b44c41c2d2587c050182007c20410101d42001040c2c009036455810321401580d00d00c030600c41e620070103500000050209101741c0d0200349085410105200300d805c0c1454612040c00c840c003c032031103402542c803540c24141c0954114080e0300c206030003800300085091007004903448040c0340380068035100c06031028181d4540006602070814004000381a00301800c2071b0000e00401020201451400c002c40b05c22542c028801591007648403207482c01540145000c034000d4a4154000301880070704454050740211140050800b078a410403ca4240390308641c0b4407026107002034460f00507028180c50300f20100784640002c2c103070003002150b51a83d100880c00c83e00407039807003101c0c29030f0107401e54181c00d4002a003600034076402c98401c900031400d251010f00005d8990800500c01d920503844404111110344035894007800601c401001046400c0c1c42640c1c10144003800c948080000e9910000490b2213401510f0700d40c8011340070f04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 803404910 1250 803403660 803403673
    0x12051c0207030219080d02031902030405011b1703010b07030e0414010512010618090b0906010b1812010f0203160804050304060e030307060e1f09050303040209450a05 73
    0x2001c1c450130340115050301c01c054200341808a41e4a104010b41d20000c03a441e401503070340d0451080c00d0140011070030300b0541190003c1004000d540c0c0c0c01400708860303030911440b0844000c0e030303403a240324060850001403a002030048000280c000000c00a080c100d40a502c45461041080c0204000ca50010003013202d00d010220040c045800d00c00119650342c590b41c0000991f064132813110100d14202d91000c580115140c604003010080e1301520f01c1d40003100a8014482541442060741c5540100d901c002d4103d2000714081c0d8060303540701c40a5500020200003040021a00042c00001c0e5000b11110702c01c1004100e040f650720f038410000603100c0c2d5004800b960820381070074812100903089420075685848144080b0300407130514404c00b000340041c0d4005001d0281a04800c0c448440c00c40c5203a00b005d40781148007404504040700326940507904607064841d13551242e10000b103045046180c4410030b800350451425002e0f244603002c0d9a150035200e070170800080741c22003507641c2138900e030014030640015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 803406160 1250 803404910 803404913
    0xf090f0708090703140706031112040311031e07060e0304140d03090302060d0e010f15210f151103060d0b0709170618030c0303040f020f090112051c020703 68
    0x455510b9045482c520946650950344d8890b600e1102020f203c408071a0040901084010b825100329540ea0301072030461800c01030110384007916054014806000d0011040280c82e4110040c01210751125909611200c0308036489c120030306540080c5400c44070645484019214540300105a50481d40102803909010303000c802441a100c3c084482241400015030300807005075030b04809802200b089450000b25a1034a100c050300790382c40503540c160003030302d0044102070130038001101c1030a44102c008500126100e0043c035105c108003a12000d00408141182d4800700002d008000f01c1c003080342070701449400620100200c80d84015500c003940320b02145260400545030050041d0300c038440d0b052000c1c1059a0b03c08040f00480e445045d100c194102408205052803c2031000300d43d2129180114100100b4038109540d910000d000501a00102c89070b00c021540c1d81c203e081140840a040b694095075228030081c41c07841241000c59060003000041d6030788610000101d40485541d0380203080c1c45280d0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 803407410 1250 803406160 803406167
    0xd1109101206030804080609060610020c04051b04030515060907211b03060f0b070f08030a0902043602150702010c020910080f0d020d1214150f090f07 66
    0x7912200038180351030781c9000022442420150008241c81400340c400c034605511210305111000744850f01c1942403050300f2400980c0011913100c04d9906880c0003c00b40c64800310f280303070441e40f031001e03412080000030088100800032030580d4a040b081180c59034161102010802118001c40d01c0c24001000000228401440100709011080312604001569080c2070051440b81c180440e0000100380c071020708005413040c03c1b039000c0042c4010858503042c11080c1e620f1680e030340340c40c802c0035001841c0031000c2242e04620398004912240e004004209038600c3d0000303181180c0a20041c0000d10380340d805030740e000c11314000d4521140e0768000c2001d02541264540102c2542100c1416070421003031078010001030310745c1e2500700d0040c2c0302d20084039a4145442103551074021041c40e000303025001110300070401600007824211905250412100007080840d003000100b010303244110741d58009409116100f107054401540440056071030203030342c00585041c0710400800381c2d45210420500390000780b0140c803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 803408660 1250 803407410 803407427
    0xa0c03120509100e0d051b0f0d020f06280c0605010605070c03060f0b041517160e0c0d1a01020709060e04060c1107031a0a060e390d110910 61
    0x70041c554001c05074030362a10b800d070055010440c541ca4482c0c692580e103030843c01d1288c122811100544814403590108944c40426165503008800100d004964843c502c80304200e0036480100c045500250f9850040030461105020384241c0c3c6044000728182e0b1041c011500d245070010401c1062918590f101002002101c0e4090301040e41c5030032048042d034541c018030555070614281c19401608046080c05007441c204000140c541c01307950800e026100e10306105044641180382c0640035503441c25100a54401da84001041901d480d005074044050040da400b00180c0030381c200c407100758449040004581d414003c00d480d0403807010000d40050459081103c074031590786052411703201c8540348589440003580ac201d40290022004031140c02e0601c0d00e0680c450311b000000d00102d0720b8001901c0b0005000741401c2e02890040040036120007802a06417500100c900315680b03101180c0082d07143c0c5800c42c0301c04481c26070410351262600040c543c03d0326400c134001080c1900d4a4920001030341c6508 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 803409910 1250 803408660 803408687
    0x1203022d030a1101061a0405090624070507030f12030e07082a100807020127030c02030a021c0312061401050c0c06030c120a05091c110a0c0312050910 66
    0x45d00c40001007416840a030740042444032081042c2d0302e4070b003403000300081350a0050401e401001d20208000c6108943c1d01c0c0382c181d20701c602040540c4c0e0712040c180b6905001003500007920300c13140b4002d10700070040307002c0c0b44401c92101c980d000c2040c4800c80d0301d06911a41c46100b07002036940a0003440d104009100401601000c51400d40e00048103440c01080710005010300d00c1c80451842c80030410f50980a004281ca10001e114904014a8003d0030032880c2c03810703061000c0c080203100410035013103407001c00c0080c002a4005051940030041d000110410070040300080700021079044500b40c5143e40340c010001520030000220000c0d1007903200444c0d0360b8100d400300e0452881030b0030407003481f80c482500a500a40038288015070300c240c609004840454090301c5c0004451a2004100070000c0221f600c1c07098041200d0150b04500e00c10000311101c0c880c03010b66140900500846070100600c00d4a4a01100d20071602c030030301c1c20300d444400c2e00c1d40c1c001c0110107508100d4040304d212084d44980800341001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 803411160 1250 803409910 803409913
    0x60906071d04180624081c02031e1b0118170d02040603060509060607050a02060d1e06080f030a02060115030608010c020f0f030f040513061203022d030a11 68
    0x224000303020100d5103104641c3c2510002c0e03a07049440d1308200642a110900821501d4070091107140c424095038134044818154050302c103074080003c07010301c01e10442d080200000b00120305100e21811305507080d44506101c102c0390010240003c0005010301034210f559015a0403050450002d07282c882c19484a80c80d4100602400c114095001e5051310140014050a03030340011018140303028080e07400300140c08140705001c03e2126500082c1f0016001a4450381a5245500d6420001e601d201800c1036a03003400500724504412090140203501c108229903403c3c040313030003200309031011540f00d02c6400c40090042c2c0110740180642e900905165411003070603d07000413101d0355031000d542150140160540180c00842801e040003c0800c0743c480b103000b46a020711f2038503242107000c3d002842184a02401790b00c84000015094255921840c01000740d0100d404500491b860000c1d01c0d280c2d00c0c141400290071643e0090701081d2102041045c0c1042075000f0b618140070718a003502c126000141400c082e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 803412410 1250 803411160 803411171
    0xc080c1305120a0204051509150f060d0225020a031103191101021c0f030f020c06040506011a091513030c1d1806070f020709110903060906071d04 64
    0x464859040c2c030301d0460041009030451610307070300c10401920780240010690f918840102001640c44401030b5820214610000840c4a10280494043d503035010f11140d01c11004078160718103504640050100c0f1a84031402d0071051441140c0301b10101003580e000e07400c0308050105000045046c20004a404002012903000150f4404644212400d10130304407a0300003140c0c0030103941e58041103062090108180d410501d40084500103107040c7d01401803100b010788540c1009215222503045800c3c0f16035030703000d85107185098200503030f84030340a1051140482108001034036010610099414050000f130202c04501d0480c280c1c24015009140000082211300300000005980b03001d02e1002089401c00b500c90f07180c050340e60300b0164032006159811651140c0e882d0b0b0303044003004c903c290340070349213081103d110402d60000f00d190080c150801c00c0030320720b00b0842c4903045036040d0192541540c22412130f1001d603a8010008c0e1210b02c29120318010403044103110581043e0111003801190001e400040e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 803413660 1250 803412410 803412419
    0x50321071e0804240828020403030503090d0207030b0705071415011805010f03081b060903130603090c05010815150a08010608010806060607141c0905040c080c13 71
    0x200c561100364102e03424400040d0810007002d11400048480000100d01c0d540d55050800207098400700604e6180002ca10041020301c04013030000304a06120380701c20864440e503d910300500355a1042d41ca0040074481c6410f0304202c0c9100055403015a030344442c012140d622844019150360700a0803003254145000762020310844002c01c1307048006544c040f811145c07949420a000e4107510811030040c01e2a050400600295403800c08480840f0303030160001d6601c0d0700c005040a101140c1d01c3d052590b40c0500c3d0240215404000080c00100300980c2d080300300136035522401d804464000c00000d28801256100b04407960180400702c3d8801a2044400040e0300208005490481c000301e92558101d40450700d0034183d80d00c203011a02422807818440c020f5410840016600e0388010000381c45480001281c9041280082c1e00400f0344140e20b00701c1c1c1c0c10b01350414001e880b2400060740b100020740515000165032500740105810701c0c2b07154541482036207806000002c6070f03205c81c1c0209100c000310400081d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 803414910 1250 803413660 803413703
    0x303011e230d12021b0f06120606090a0e0f0c0a02060a050a0213060c1412030f060307090c0e1f0507021c02092a0f120714160c05032107 60
    0x1032010404d41c040e0001e0441045c507290702c0100c06484601410300ca40d141060380c2c0700c00742180e02010034039409a05a6a0308400500b103445100e03a81c035088917440c580010b0744880d01a8682c0a6815007003080700d43c0c1c3d00e08418151a0040c018160f0060748400c1c0416003541650340b01641000301c0c40005490b002114070f4001c1d0b000caa41d48440005400442e0501c107201c00c0307448a114640c00000a481034259042000440f8000a464403441c1c1940b0301c0401c140d55020031403c8020100c40c1418051700014140291046040d0301c51680039104203000700d02291103480c5017240a140a45410381024441d40900c000000000f00c1503010500925610004d42d0b078801d40144034514040c9020985500d101d581242c4007855204200385803004e00002a01d54070240940b40d24a0250042d00d041e1360710b160301111001c82c404030180b106240040e400841910b0b0940140b070007802014401541c5603108181070741c8903e60000100c24100c0c0c1d48a50380c610f00704a00400229015500e0103041d00c1411004a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 803416160 1250 803414910 803414933
    0xf050c03120901020c0f010f080c04080a0c050405060d052805030d06030312050106020c01053a14060f010c140d1805030a020904021309140303011e230d 67
    0x203881d40d10340894402c04540e030400c42d00501000980d00407043c0401c61001a003040c1c0c50700c40d40803e01c00e90200065072161807006480003081c00034202d0784000814100341d0740000460140340d02a5060800092031400d10041c8e24403a0303580030009208019941c5070300c241541d0700d01009881c8200750f0f4031800100300b00308007811140c9100b00700011950b01c1d40c500a46290400c680f00b0100300d082c480100401c81e0045215601c83c242800d10a98402100f010140c110100f84041c107040720121400c06421040740ea0f4070b40d640380c21807408000b4a00085a403099002d82180c5091780244c1c05400210154410884024002c0c800e113407a40660440310074072802c1040f000040400100c1707284c0ea0b809503080002000c00100001d602801400752123030041340b075025000388041e0141c001d01920b200d07030349450740c0040152074008160f040707414850651991650b000b0f100c0c40b1845107032600b800310034035030003200c01c03040310f001c0a40c224009000d540c4c1c207820803200030f403d140d0242102c5d4a140202e50032840c107 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 803417266 1106 803416160 803416183
    0x6260a150207030e030a0b060a09022b0212041401051b03150105090a0f030b07020705090a0e120c060a0c02030406050412050a02150a030b031204030f050c03 69
    0x1551035401c4e144004c0e40510070400010140f1260000090007031504884482c40c5a5540016100343c0c0540145181c00e24107a4010541d03d60744044030747c128280d03545000d801c24030402e080810b03001080787c05540707903a1030300e00e07541c82680700f03101d115480980032502d1705001c540e46000c6103403804000e02240505141e500d20003000d81c0100190f88248034002d240c02c0c0d42a4480002000340407540c80129032806124012868290000c207845042d14406800120607030748409202000d88400078102daa81c2c001c80c41a110a05400703c0101314030490130f4024082d505006140c4801c43e5000036070300d41190400d00c02801030390b9200c000c80301141e89260080310302040c6400c28038200800d20720002d61180c4d0602082040e052810050407071900d0980f0300300b11400080e4245074440540a01d1480c1e0b41104100520006030f4000d20401c28030702410446407401040030100380b0301030300c0111 = true := by decide +kernel

theorem cover : BRFrame.Cov 803237410 803417266 := by
  have h0 := BRFrame.cov_init 803237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 803237410 ≤ n) (h2 : n < 803417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
