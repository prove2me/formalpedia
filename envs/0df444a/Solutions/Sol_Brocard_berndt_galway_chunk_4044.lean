-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4044
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:24:59.338993+00:00
-- url     : https://prove2.me/submissions/05109fa7-b3bc-470c-88b8-c85b3ea341b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 727158273 ≤ n < 727338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 727159523 1250 727158273 727158281
    0x321e01031a180a06050d020604090c05040e0a06080709090503031b0c030c07090609060b070f02040212040b1b0903120c0106030c0605190e0f24030a0e01060905040b06060d 75
    0x40680d01c0071a69550300b40018400c20001d20a2503070070300411440e03484408220300c0c0e11001c06c0c002e5001000304020b020320943d0380c1040c4040c0101c1d080082c1000d4440d900d40d40080c40417580040c28650b202e8042200407010070660300105a4510200312854080d1152501c03484010102d210802c0781450322054100381e242116141a448019243c0b02c0300c000100644510b603510441c00200d0170300c0e00100742000c5c00d100b100101d500d01c2404c03e00d0010310b130783d4007800f07070342c2800c0c059a01c15402e000c180d2040300301c4444544110b200c1c0c44210004d151090710389080400c0c05104240d54031007889100740a40700040c4000404a9220304551503040c0020300310302502d10382c0c100030820a0040d0300014003e400a02401041050032140403c0c0d824500f001c031a00d905040d0039a52003101a5850740d682d0130b28102003240060a07159413042d0f03ea000184506030741c400d5444d00c115956855810010b4107081c4585800342601c245d0074070560038181c503580350808000e0304452140300c00041200030f008417544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 727160773 1250 727159523 727159571
    0x3030c030b010c0b072d020715090e0a2706200d0902060d06080c120319030e15150a0506090a0b0a050705120d050f13140304321e0103 59
    0x1c0d048049000070b0146c00a07609495041a000d80b04110700425610350303080e61003100f0601d903070f00e40384840d10300785c120000709a002d07250340341890b40d440b5841016411942c07948c980ca82c4803000300c03400104600d03050084030780e02030f8101ca0300c080e51003200300e8502e00513044803030b07000b0060b2002c101c0d58803600004043c3d116102c01d5480961404100140304000445c07034080c20307074086664801d00084450600e850348200c44074620b2181171001000c0c40c1c0350082c1d211201444102d4121107046c1c0503850b90113400c10064507201c461031007401503080c41e841c0002001014100540b9800d05094000f404500e0b4031605002d0411140300220381c80405a1250094803801504041100c5001d60301c2c688882c580e42c0226950b0034443d007490001503658a129280350f001d4054400384c46a11030154891064020400710100d90900041000103009001550b03040c0c1c8044502c5882598028208158010880702d044410300850314044500c0301c00011101d2425902e800b804d01180c91305080d8600c0340280c04c016 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 727162023 1250 727160773 727160807
    0x105010f300207050106080f060717071e020f0607020309010507021003180c090b062701051e0c07090b0603010e100e0408072a050103091a1303030c030b010c0b07 71
    0x10540100f48076054005500310389419003610190105042303169111802102e0204c041801c03003004041072400c100c40d456100000b4500fa00d8100503140c0c002c0321887d407031180035005910200540843d014140000c50b0000c0560000b1480c0901c0c240c0040d01e06d0140c04400f902c241c140703c031000f100c0340c000e800101104806581c150a4400a45000700c004801806a8807100d490564120b1a42c01d03c0c01c101c8104800381642012101071254028600c10700c00d800483c1041000d12001c0391b000803410310700040c0c0900341c181e070761150040300000d46080c940b60301440c003690030700808141c00e80f141e01c2124191008000301d031006948001003c0d4014200380e00481e0001810f00c108001d1200400103090941c2c0b00303201180d42030122000c4007400081040f0103200f4011028800c1207103601a80c440047d4500c0341c8146007194007a080f083d081d8a4007211045402c1080f45e2014080680c58801d1000c166440d00741000004d01d0a00020300d803200b400d030020140060500820b50850044072124500348041b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 727163273 1250 727162023 727162027
    0x3030405100206041101080f0612120a0c03180608180f060f010314060f060402250503031608090a110102010f0f0605040e06060906060703090e090a03080105010f3002 73
    0xc007070000d584000445050303c01140e802070364585503128885407402544100346030451038503241e0030000380140207003007005c96201d002d0310704000362408005000b1209245d02c4100c9407460710b040180411002c020901c4c400c800101c01440010b8202d0002e640000e1001c00102400c620009008e00d8503860142c2c81da668480c000c104031284180b0113226050720701c42d6500c003d170031460700006651000141e809010001e44500050361a003096030240c00b10814924030010001000d5244d01e808103a124001e07039264200004003340d441400240302090001e528200600341341c006441921b0b08000640281001d42c400f03a0822240e02c00d400a100c112000e060030003d03443c1d43c141400003810305100c0d080c010790a01c1e00c141e00946010600b51304c203400260103070010341c0e210010001a54080d0200700e060040086c404501002c4d00780c00b04e44038064000080086140c1800c01404039a0140d224504202c01002c0515180750b12082c6842c41040320080c204900564021a11100360786240c00c0f00c04c5840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 727164523 1250 727163273 727163299
    0x160314070305100228020715170103060b1f02190303060801021204030908010b0f240304030807081003050a0204200d0212060609010912050a120201020702091f031103030405 76
    0x51680103024588030940129170001345250b0b400114001c0c4406200541c1084008008070a4030303079142800380023580f5081e09803a071b0f904181100301c002030b0419a10700f03650b081d4440752401c00c2c00d40c003903100c01c031502000080480030100940d59601c0000d10040200c81c0030b20201058002d80001c130140054600030b544400b0301100104034442c2c111410b0300091100c0d5400900320106205d00108a900a4014503050790342c8018003e48805402d141c101750f1100e560301010714075118001c0c602551103655202e107141042c070401001204050000140c21041301000c00000ea0b00203210240c80e0ba0548003c18101c070505000440e01c0102261050a1140041c0c560b8060102c1d40c010520551444070000081d01c907002031003180d0044002c0b590200d580c0d95400e00c428188005582c520920500848141003407607954408880503170000c00002d0303900401c0103011440c0c80c40760960300030318140c80e000083c1080317080f541c1505118480604000700b0f84010318944c0d2400e00032074020308405484e100e04900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 727165773 1250 727164523 727164553
    0x11150106020a12111005041403031614090a1205010b040606022b050f0c07051306150804050c010c020406080d020d12020a0207150c02150408070602160314070305 71
    0x128442e0b0031070300d00a081e90244500b5005291800d40e012400f001042040702c8440c60320005e00b00130388162002c0010300c008810b090b008000840c800c0034044003043d010136450001502c4040300c0180b580b0003003420f129074101515054054070889400b60510059945541801030043c80c01c848440e0700a420010042070042d00001d0710751505d417104109201c0e0000c88000411010248216480081d0080000501030b400c0600a001c59500700c03400e8850a59030b49001035811005207403180030b060f031103075010050110b444404540344170352414840c0310f030315141d5a069204c0c805428040d0500c04c010305c0c44415510740d0361000340070748445011200710341c0030315401a41d12145013a061000941c20840b003c400640341c001c5c0e0350f01004640081ca41d26003880b207580101007145054800300700107104c0d9800503a449848000d60b0400e0609078036603860501e203400d070420710184c00c21020755000c03012803d56010140350200c100e03604051245000d003400c0b001d0600380606544017400e188510401e250443d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 727167023 1250 727165773 727165783
    0x30a03050a0e040e0c0f01021006090903110307020307030201030e0703150902041d0c090a020f03180709181106120f06040501050111030a12020c07030503040f0f05060a1115010602 79
    0x9100da4a401420400c2001048140ca03130a6401c01401c2d04000d24201d8203003080703070641c20902c4050054030181c00b442d80c040ca0446803140d2003460120749070150041810341100e030411000d000000a585003645507000300743e4641c21480000e04065072400d206613600c5040c17040b240510351100c02052014035010ba200e000d066002c80c01d0b44034900d015602c0d011342140c18607a0404003e0580a41034800402c2c00700b090000300144520300d0b41e60204090042c480b4104001c40c414140403c0c440441f20194941c01d2a2041d00d4110300503442c44c10000400c140b110381d01c1103960070b500c00ca45400d50241a008681e003170152030000c080000c03440e414000c1c04104007418078850074050311300300000c1e0390783c0b001113a00c1a011040c0e14010381040005180d0984141260700d04000e03140000361a080c00720109074034160383d607841030750150004101409105082959407004001c00007401d68214200780020755184280619881031100c4801d641c02082414824800038440840b0700028960303480d03802a4580b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 727168273 1250 727167023 727167037
    0x9092e0212040c0b0c0601030809010306170a0c080c060f1b0a03090918020607030509010228170f0901080a0b1309020306070c0b01061103090a0311090109020a050324030a0305 77
    0xa041c01c2c080100d08138030300c4002d44190f00640402040c807640780da01d465038680d00c82100759040544070800481d02102020f03c0c4d07038006031080c000301880241e9013807440c8280c1003a0404110b642181065019503643c250035a5045019000d400b5616061901c0488030403810f80b045101c10301643c201041459000203c2c0f100f291050b01061142e0000c164151b60040040d0000035400041441b400d40800d1250740580034220040c0100e445110300e00b00000b6103071300d100c04045503502c002c2d4144d0041020900406169101c103418007400e0034600084070089000d0b4440076030401c0300d12000a000001070340c1085180a2000c0c1a012000c80c070029444003400c4040c209902910640d0040341e1900d2054200209054000b80214403076400c0c02d100704d41d05030b000018000f0610083c80601516507518100500940c4210500c0c2e914a02d9141488035040e01640001c01651050150b20030700d42c0c024044941c06071003a61104064254240544a01540d04400350341602c0350085031800c050b0084018031030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 727169523 1250 727168273 727168283
    0x2060601050c150a360f11120c100206460c09290d090b090601080d02030a02150703020403150b01030506120a0f2a1409092e021204 58
    0x280310080003c064220040e07084181c030708203171300e181500402d1010303800310f01e2a485039003024008a103803000601004041c1d5140c01087e005144504c0251410781418161065180082c1805141c4a5550200c00a20301c60310180c07515030100340d118242c083d5002e6016040d01c450112903142c0e1081c50349000301074400b100000f05544840200b004003044408900262070054052030120300103a52082d203811084d008000c1c00d484912190010700f0800c034040c0304400203401040300790b00d048070303103441c02140c01200000e6420400840e99015400304034041a1031941c100c42d8160f4030f400c0812002031189030b1014058061006114000b00349641101034480c2d0240d0703052155440c1c44080142414030003443c0702c01a4000800040000ca503c0d00c221112805111403446a42807a0300340580408414560804000103010a20000c02c2000d4041d0440800390b482170040d05c2c184c035116a6407106580002580c0b0413016103040b1031141d0840b415446e825040095484442c0c084078105c203540c0548040394 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 727170773 1250 727169523 727169561
    0x2040501090204120f0804051005031603090816230322180e070b041701180b01260106060908060a1503080d0603080406080a050604050702060601050c150a 68
    0x107010700d5500030f54040c0c4070304007055030010304503a036100700d640704240c0700b140c055005000000700380d03a407910a241c5030750061f120641d43c0d290000d038085903407040004490034145010602d50114861800352224080c3c5907000c2080748103c1d0611116064421110909103944100340c45400d400200c040c04094080d003c80c1480000030319804d003841e641038056104025002c0d8982c0c2c4c0480d2454024400c02d06490050311006611148408110703071044c3c0007144540508400034800004c00d200348882854801119100e481450340c90303112244040c8100c003e1010500f92150780050285c0300700303407400000d10007006903039928180509090b18a104a510900601d40000d15055143c0904d02400309050030803c0706c00d06656400b0166040580400041030b07942d900400000d4001c0018005001c054462010514000001a080d22002040d0600135410a0140901e190f0000707001c0e6041202401c0803a1101840110945016a920040009600040280203d028065100103501d4000ba400340d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 727172023 1250 727170773 727170779
    0x10221100b0706151d0a0c02030306130e06071e03051302060901030f090606080c0303040e180a2f04021204021012050a09120804080a0507020604050d0c050108010f05180a02070209010b0702040501 86
    0x60441e0031f55420304015800800001cac0561806c03041c469008050454001001c6201112840c0b6007002190701d60b0215130521000e070000c4001c2404481201d5161405200d0307858100070f485994010711100034012980440e007008141e000307400901134903c2183e010003844c41c0707a0a2003000352810340f18541060181648003201400e01100312000d4030a0341d502010583c03239940000807150025018030b9100d0007800807040c0000c12140c00210b07075000078085c0c10590740300c000c50004406140c0d0b480511031441001032107840000e4002c09984650102d91003a1b0b02c10a80401f6190040c0850404944030f02c0c0000b0012140b951750312041006020b1404814a00482e25003a140035100b5103000c0e14441050000906451140c00105900d0381b001e0b2007981001c3c0e80b480800d802801c01507003201c65480c00a41031009581c041c6515005080e000c40a012161408000c1000007440c2c00c01412103e0a29001440c9819103030125051180d003d0310180256a5034dc071405495049200304070b1082e800c00c0000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 727173273 1250 727172023 727172041
    0x910030c150c02090402040e060702031903020301211b0e040b09030f121023030d0504183606050c07170313080408010221100b0706151d 60
    0x4486201c10944401460300c840740c00b008514030000304101d9000b6150744900f030805409210490103100190000c54898010007201d0b44801036010030b2004241c814001001440c14821421016a0303203070400c12070a01c00c43c00c100090b10720300c000001c03400100c00c6001448a030b103002d03114480c5010303501c900e10640390f1b6254207840b4843c4089029021800340b0070342607803242c00882c06d0380180116015140c0d0341c0e52041e0b15800111005da0f0b2004034007904240300c0c0d140c14148095658080d851030b08e5407400d414070b04c546040e96a408030b000c015aa4440c58070146841116210025409045900b420285030501420406a400a00301c0300c003820000401c49803000d400603140706075030042c4401c15800e628100102c180d0401084e040c03c1c50034030034001e030101d0202402000076005020004d41d13103d00400c0c402e0440d4103666a041041100d071030400035900b400003024810780d1100d0765030701d50382d200a090440240150700f442883c0550700c2840010301640b0611604841c68211007040000e54881401d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 727174523 1250 727173273 727173299
    0x2a11060114120c040c0f1b02011422030c0315060305070e0c0d14060f0904050c0f031014070e030d020a0303050c04031b0807080d0504050402180910030c 67
    0x100407011100c600041d40500d02115035440c180000411503034078040300400501618407a00b0b502c004911000040107800b80e20082d08110200201130506503c1c40b1540001c1801e48104c801c0c0001c4400480c42050b04021814580006246110f03911071841d1a410b054040068900c0304440701a00c449402941e0b000c540a01c1c8100e903004406015402e00d810140404e6030401411006058010030046070802090720440d4890b10816200d55180c1c40c120050107041d2485004c414440caa80710308110000d04002401302c4e82c2c0006540f0b802c215070401c80801d1800a284070300800850a05844803244603007400e0701845100310b0b070340f2109011540e00600d516401c00300c1c1c0c0c1c0030041e004030301d490020074001d810460700070a400ea00c80785490b030340382c031400780d00e0212506000200003604000c000301041048900c028110703a001420546460001c0608107214078443c06000320780125440502d10380c10003007514004400b070a0344040d0710341481007640b0400c8500003160a10500360b0045448900109 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 727175773 1250 727174523 727174529
    0x718060e010f060e01050f03090703060c0309200307150305071805061e09060a03060e0609091906020f1605010614061615020a17090a11040e012a110601 67
    0x1a980c07000750070541c3c00c89048140d00045418810100403e554403650394005612903c80351026001007821858880d00f91604001d64104040c1042941c0d00070901050009400c060701407001808010b00c0e0300400e09080c0b1030760145c0a5102038107450060300c0c0d010b8101602c1585651b5800e501020790340305d00030012609019983c4c101005110302d0003800100c0c42c03d0b1000382c0c100682c16081c40907110006906500010400d070000c2e8564808002601098000b9504400112003d12541c509146103545d9030b05200c00034004051007800c600300b400038582c1152001d5042c821a00d64070441e0a031440200c0780c40750011101907280c00c2000030b003020300010510b11000c006000503d0502d14021422200c5948041030b2209a02c0d21302807007800c01580300810303014520762100031503c2d42e4864100d81580006259031b416410420381c4000045000180360a00c4404982c005a02ca0b1181d841500500302000011142001030381a0a9502d207445280418410030741e0b031b00f41d280030031501450380380e00c020304c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 727177023 1250 727175773 727175789
    0x8011e031a061f090810060e0408031807090605030d0801150e0102070806150a0b040321050c06010314010f06050319170a0503100e0403080c09040e0718060e01 70
    0x304070102030075090044a800c080001d02101626124803080248031241000102c00b28085650412040105218503c1c440c40c0c003400030440107207800094000008001c03c010005240000012003c881200304106400e9401045848141d181e50001008061074000c861092154400380741459104141a41c1610040803500c10080030556041c0c9482d0300045009056000e061000710b4500310801140e03100c2c81c41d01c1c1011600340014010b03c40d6102c55030b0862616400304110a201007046050124801c00d0301401c54901140600030840345401038050384940d0340601800007091049101d0f81e036986850510082107a101500103507000c680091080d1a019009901d1010381700c0fa02074180035610b401400e605501d03010003c1c011300d003a0f005c45040340124001000b4400305100220048001d41320b801008405400e00d41c4028080d1140201451011f2030001060002600c1c0c58000401607070480044032002a110140448030481450004280602d070000005041009601540c125002c071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 727178273 1250 727177023 727177043
    0xa02130b030309040207230d08040b04030c060518010f02091810080f010c1b030c0b15030a0308090f0601050a12081e0a022104090221040308011e03 65
    0x21504000a0581556034650501051200a00030f03120360005001b5941f141a60055031002100e0a802003441da2600c0744640e41b1100c16440325070f0300b001c070658100b0340000136000b950b940c6207800c0390f0740800c00340d000301454203110034820040350700198401500d808400074052100c21700308050403405550f200320703881181240403102440c80c2800da15045040312002200d880d89580c011868455688810707661695a0700c0d5040c1e80e01e92207850f14000340300e50100002e5080140d10001d0400e0290840901100e0642e40403842ca010b04481c40310090300042c05507041a891030030064801d4004a43e0402180260403015401d03400116445046e150000d12a03440d050801040c690200340042c0216100d810421080590101d141221402d400040698542c1e5000c2d41c040203044c0811440715441412050003290344a070342c4002520107a85554400580781c4244030702040320040c4401c80c0440b2a840c207070621062503400f021940c140c0320000022600b894a12203075081000c1b0f0b612000e0100151 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 727179523 1250 727178273 727178299
    0x61509130f091a0a02040b0405041505040e1608060408040608181204081e07170c040501090b21060a0c02010b1003050a0f09050a08070507030615090506030a02 70
    0x4540380641004810030400156064104041011650824029103003c01e16040741c50740d042081c640640d00c01e491090a508107413130100341800717901490040034891038407007a526000102c445084401000010810301c10091403004080e200c82d0f81c0301c0721000b02c0c03601c80c001041021000920702d006075440001540f07014649078007256010030207032100c500d43c0340c0844c40c0c22500104201d001c18400c1a1b540742030360355180652441ca05001d44810f61402e00d00c608134164a60000728400084568141108a107034000d01d40180c10000700300c6031194024034100001c41c004416500002d0034510581c0c0c070300c140c508c030301c0e0b0040c00c4440c10b05d0a441c00c56104a00054000d00c2ca03410030180060f40340004114040c1d883d001801000210b201c0a002a07622400c1020704200f40c01040c08250070010100541c1c1e8042d140d10340c854084c00c0c00544203401c0080c0b02c034200101000390000458126004200c0740c2a04500b9046021052054094281c14a00850307807524000c2415500d1542c014400c0e510303908 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 727180773 1250 727179523 727179529
    0x108010b01020a080306062b1b030504050a03050d4a0703110a0305010f0f050a0c0c12090e010314061b07111c06020415050c030a11120c15061509 64
    0x807000303030102310b00504000450705250300e408913000d074145540b00c045802141907040d234140c42600c41080e020541030805100c040388002ca42c2c0701c070181c4c1618140760354030001202100030f004201004260725400908000520304a4850b01030311205e400785500ca040c25006101c0341c03c40154401400702d03041400d082000514078045012501405402e1180ca581d40b92181c9084940340100c2c10480c40d1142505400d00540d4812558042845001000000f07240c440c01480a60403440003408140610700c004052405441c41100814034040302203205c3d84c40780f40800e1101d100a40c1d40400d4072a41d0081031140b4204000e40810704509841d00782005607503124081d0750080f0f60002504041103602c01e0344400100e852004401d401120f01507625841e2010f190501400042078004014062140501403400801111072070340041c5480407010111a01c0c00e820000103054100c0041c50002e00010906000304030308103681d040308000340340b030344d50302041c0300c040300f81e02c03400d00382040082048a415103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 727182023 1250 727180773 727180777
    0x1a09010b0d0b0f181608041a100308040b03100503070b091e0405070f0201051005011e0c0b1f050307060c03053718061413050d0b0610031a04090213090305030108010b01020a08030606 80
    0x2084d8480100d59195240c6070b6258bd07601c16007259006803000002c000d034088407101500c0080200b85d00070154076241400084a034040c56200c4c40c41409403100504211030310201c82c2e03859000003072040045003403008020f040f4084819115015508103000078103001021a0040308550040c0c48000b0039446242040800c4941040410107000d41402c0e54004285006d0030300b44121038860709800070142c01291220341902541c015482039100f00c00510400d680a10f50030405a03050078080d841e0007542c4e416000121a84100f03050000700058503481c10042070002c5011703400162100400c0e54140b0141c540701043c20b000340c00c081003035258640b402c01510300042400e4151901070b0101c081d01c8500146480d1491170041d1004c6841e0000c0c040b092820f081410400001c60a0400c4541d6001003d81002c1007101d0310b01f48115038488190040d500d401c9206034881040d00c5080110401602d4054002d810a01625040e986400c1401050754000548020200c1d0082101c1c0c1c290754589082104503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 727183273 1250 727182023 727182031
    0x7020d08041e0609060c0f140f09092a0a03231911030c07030905091005090a0e1e01050105060f071416091a09010b0d0b0f181608041a 59
    0xf40e9030300c01c4200c0100e071a512411610700300e0b581d035000c41400c285100600307254080440a000300070401c4032030a0600540c0c00c07a50344107010f0310f50980540d10b038051100700b42100082d0750350740300721418110b402c2010200100003a0396075032403c0080350084d002c2d5080040043d44410b21941c0c00c02d000c80d00d400d200f4049000c911040d01000b0030760301440305414406410540e03d03000d40d090007140720300815411a40030f00161078240e070350080c41e151070822003070304070080d10416001c0c002807404a01d0001803034003c809080c03603003811541c0c9020b4a000c100000c843c0d01d0114265946088000f2406184c420219648450049892410804030380c40b403005140c0001d15800302449007084e0140120017010301d40300123051041d0002003034010500700c001d1340ca000540303080c0301e00c07401c0e001032243e1980c820554928041281d40000c60071024404030310100d11985405a11000c1290070b80c039004485592907200301044900740850715a100000e40342060141c070010041c0040b941000c1c1210301c100d441c2584 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 727184523 1250 727183273 727183283
    0x90501020904060b03190b030d1b083001150e030c030a050703060f02030403090b0d1e0c12020a020d1805060f0c0f0c010219030504080f030307020d08041e 68
    0x140c41c40d954001000c41e80c69a110b8941450040304100640d0688002108040181402403180301001c100103900c0e1a12000044207102480050002068805010407400e80d40a400196221000385040900443e00301101c6082c2881c0303205002100c240203c80760481d29010a540203194400205a45007410142455014424840c82c0b691a907002c00842d20301d03e0144029110b42801c5d402c205080d1f075116040c02c465280100207200000ba4070400101c102c0b80700d80c400355100c0c401000d4090143c1005900000894520181071202d207000c0d6111844003000390303e600c07904610b03804160301640580b40f00f460244e04806004440240107a5803940164880c00000d0300e60b03a201c00000341c030794100302c04014514401045900400104111070700e44000b100004180711141c0c00c0002755500d180b100110100030782e40d83c0d07003c1018003a1003943c006d0841e07081178668031511840c0d041c0e0ba0f604112980001072041441500026001d1a07078180155000900d541410b05207058454000d1803800e41121 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 727185773 1250 727184523 727184527
    0x1107090e010b0a060c15050411040c0302090a032a050d021002030c0d020a1205030f0c0a020c0301020d020901031103040b04020f13021303050705010908070519080a0c0e0a09031209050102 82
    0x401030ba90103c048001d13068680743c04043d0740310b03810800c0c1700300d090340c40780da00562500c3d0901c408034a034804000c503101c00450b40403c05588083c0704a020340142d9040c2508100001c20200030007030340f00c08004081c560384450b444100b603280002d0740c0203c81c2d4400d2a4010580c03020134405400c20306824019661140100c900c0c1812a5490621b02070542030801d00603000740c10300ba000c00c1301040d0301c100003409516000c2c1c2035052140d403001216001a01c01d100d50100051940401c900030700801c164804014021500d900e4078480200c00381d8040c42149000170300d0b010f1140d204095410a5030b01413034100c02c08440755955035090181c0c66140c1c00f000c56101480021100d0300020a0008140458070110081c4c0401d1961400603e0b141c0260801810702c182e030f000520400b20001201da00329802243c40351981507000c0c4207490f03040d0a13600880c2e118000c070200c041c28411000c010b04100c44c00c4680c001900ea441454050440d820010024000f41c00e95000c1072a03424581c026100241c05100018 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 727187023 1250 727185773 727185791
    0x20705030a03090c0b0703020606010c05010b2d1f03020f070c081605010305090a0f080c060916150503060f042403060506090112030c150204061e1107090e01 69
    0x600d0364100a0340e420001c2d8440407150f0801c514920500010b040d1301c0703401400c1020b9aa0040e44600005207450b0401019000c41c0051020940001c24200307005402d0340188210014001c12080010511006045101d25012050f0525001c880c0b0700f9001e034601917a02d03100c440c40072000395100f940b0003c181402480b00c040440c200d0400d0000403c2200020445c050151541d406c8079041a404107060514241c00c00c8501076012402095041d44205181000300712460003500c580a82c0701400241e100700400c100d2000000942c00d1900c40701c200c0e03281485941c40c2d04042c03a502c0c207040e03d080050300a1000c00c4c503506046603040d031400380003840407640310314041045039002c01e001ca00e00600c1031620710030020720501c4d2003519000041503803506500c4d03041c0191200c54041e0600c1c01000c000c41c140e804014441c0300d10460400300071040003950340369900c0d00f00400300000c00c0c10740180914500b10300d115580c0034896481c2840003540261041a140801400080c000300000060654985d03440d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 727188273 1250 727187023 727187033
    0x40b1522150f09051507030305090c0f040e0111070c0608011401051c0f09030905100c05030a0503070212181f02100c0c050a080a08100303050306090415050708250905040209040207 79
    0x183d070300d80a014400d561181d031281002000d5270409400080726411850941400b43c072400540742c0211400d440c0454400b60017100e0300c2c01080003c42003095a0360206100003000b01401c1c1c844212543d56860000c2c070b91702c80c440c1100c001d42e081c0115000c5074040215202036040c02d540c0c04000b8400c4100050b030b40c2c9508011405442841c0000c03400920b0740d030018056850540040040c0b4a414680400032141a0f510700707030750384141146441070040c00310015035080d108015080074042142a0344d500c661142c5200044013040038210791207440c240700114022000c1e4487c0f00e113441030581c002c20b10058a146d001c40148114030286040060000d075410104408020754100f680c0705049240d034542001c0030040110b00c003d0041c04450510050801c042903200d0b003605d800101c01c036403504c5c3c0c54640d0b00e000c450200440c1100c41103541000100151782c1d800c040807a100d021484100c400741c0c00350303980030440459490500404220030b0350041c0081c0c107184c0d01410142201810051400040b5228 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 727189523 1250 727188273 727188289
    0xc0118080f21090307030b060d0213052706070c0510021803070611120a17090309011103160807260c0c0301060509070806040b1522150f0905 62
    0xc40071540003059a0201001d4000c412149148401030182032007502000252a4040303403001410382680400400d80035a51540740388107059008040320100515000d14030080d0504032003960707038080d11000701480031014440c1003401015801c05003030159180803090f40c0d0303869811001d5036030f8860b55280f580e0310301d0351380b00500800180c0c003586222401c0c000100b6241c000c1980000c410440b0308210303100c03d0b8a001808100010070340b02c81c0c0d511061202030480d11740c001c0351101555000c030641480244140071004029142c4283d80303510310740e0b0010103215500d20030040c609060603c01a60100440c0018001e44036280c0b00d89250a800001411240142144d40ca0890304040d000200449051020012494896400c0d03000788101807070040003030000c4500038158418043c20000060b0309a840c0d910100303005d00001d01400c0350000b18069407005d9049400140038000341c809841141d03025000e0300604480c100d0341e09510450b40300d5001c541440d8ac0035076030340500c00303404008501e55a42c060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 727190773 1250 727189523 727189543
    0xe04050f0303090325050703200a06030501050117060901090e010b0405071119080d0b01030f110307030f06150f1707020a060609021c0b1201050f06030d0206090c011808 74
    0x10065444840d00e0507800001701060002e0311500e103510000c0d1002a402159000891360000d5004a03179458070a00c040104808250480d4402894036010558580541c8654140e84c420b030f03505100884880c10740c441c00041900c515a00403459401044400b4082d0401140e07044110001b140150009011074141d071410780386600464004900316404480800071040d0449a01c1d805100a00c1541c450301c00c6842240c170352000317880c1c55480c0e55030103902079044410040c401d040b0801140f05070300410f0701d06400035108000080d060802080204e00c00d4019101501c001710200700300388141790f000b960b40740d844403120814007a40c4443d4910401a408040d407041140ea00039200781a828a840003c44d2850f4010180491051000240e0300801e6404002c030b03107580f0800001d0341c140200000e440b100c60a0401240e035800e0000304080501510541805164107804481c51030958000603a203079442228500b00e50751080901002940c4214a10911003c62440951905032194201030410174504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 727192023 1250 727190773 727190791
    0x1020102090616031119030f0e09090f0d0e090f1f030809010f1716201606080606120a06030606080c0f19030605100806090f0f060f010e04050f0303 65
    0x20000001d04d0780040d40112003104403001b4000300d116621409000c04e44840303028040108454500300d034240a90195808104003e00400951609c114055540d124842405006005207850f07101e5603806040c1000f819000203000605a607101140d903014881d00811104170309446d03140205103008203101e401d02540c0906840c40e41c1d030384000f0015001c82440004802080091a60401c5800030710045641108001c680820309a80c1000204c803160303084c0e011100b007800603220340302000390000381e0984800307100c01121a00655480c81a586402d0031680160820410018000c12107103902501c1c0d42b01d03280301c5000600c2912616860100c0d021500701a030745611248151110b8030b44003580c00c01d005411034418045411000d0b84100c65000741c0301c010910b50319580414580f038000e4004d034003d404100b085270480d2415186555640036030020f040380c2801817060800b0070324004500240f0038404881c00100a17440c0074880d00f681c203002041031300c05003c2c0d220000c010072020b00046001b01c01d11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 727193273 1250 727192023 727192057
    0xd1d0d0b150a05060307030b040b10020a1112030f0703090f1d1612090305160812010e070f120f050c040801060b030103020306150d080c0106060e040b130b010201020906 74
    0x49000c0c20303507800304990101d2054154041c10002035444c4011281d000996250104285884a003c680500100452541c0c800c5048004201b01c0b0380c005036070b410300360182c0e401c4504c00c1000000d21601030820340143c469904100a41c0c500d0b00204e500078060301e0700c02e1801040065444c855941100310340d030000740740003461050010540040d0542c883d08151100c0003c0401d4801290181c04080c41e41c04150035588c031074010350107050240040d0b610313036040421000000b04032454103086030b508c003000703c1d030410025800100b000c002d5030030260300c212002d49505100b05000300c8144d074102030f10024029000c0e12001241d500f040c050103010700500c0141090b40e11a400c1c020b419080d40c44940194004440900040002d42d40c0000c140e0b8000115400309040c00f03081101090140c0030b50600030309000d40c009019450b00c801580040100d916503921142421074210401c001d4800480d40135a020410000720750340c04055512140680c4814000107203401a24000701390681c000900c035150402035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 727194523 1250 727193273 727193281
    0x2090603011e08070806010e18151005090a09050607170c070c031209090e0f030f0d090f030206040209060a060e2209060b040b030a080304080f0f03090328020d1d0d0b 73
    0x407100e520342003002489c610400c10032105a440e654001801840500c4289402140d61403022000c5203004e04030103400300100307103401b14116019090314501120107100d00800070360301034801d10214140e400c0c00b814400f41038035104a40304081c4c1008070281c60145019000000281a41a041c40d903400c1c00d03100d000889113402c0c103a0045a00e09a4045600e400c1900e42ca200c0000100880c1c02800090408039241c040900d641c40003442802c0340101603154a80c00078003030540005582d88103510031101c442c2039035200701c10301c24605c8451290002051605080e401a4505030409002044882980c1c60b48103860903d6003050302c239010701c00c2d1030080e070383c005030401e41c2000c0c0a100154442540100b42000030b40ea62151f1078840184060960040402c034800c00401e0318040750044c0c0c1c003417020310703860342000744100d501e0b03a111200103d800030b00082d0352a41e42e1111041c22074034225a030042d0030040404241503440043c1e481c82074015014040100016a40c0d0150840c1c9283c06031141c08010704d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 727195773 1250 727194523 727194539
    0x1202090901080105091005011d04050f034603091406070e0102010e0114220c0605220812210112050f011a1c020d08091302090603011e0807080601 64
    0x341c21b01818055805d25005000e0180c0a410b420700d0006d07003100d4001680e0b12070904500b03082064200c40c0480c040017a6041c000b03400612002c40040202c0c0b50103110640900b003004120314001109140d41c02ca081444042c90301a0b405219a28015104220b8091110f81c0081c18440212641c4012919201c481c0840e541d091040d14680f21070b40001f0058410102c01034074a10200a04a10404640c4010100206422003103100f44540c032060300c02003241c4443c0058025001004941108121003080383d111140c021031220855040c0300107019030341c402100c0000d4641c0310b2125400308503020321498404051070780626001740345050b0796880d14030542c584141420700c80c0050400c541e04008811091424802501505441c2102c000191302d00108210305c4815800b000603504c4003544807074030240700c0014014001c00408452852005040705082000c034058030300f0950b0041c0041c401400480c00711515050960b4506203200034150b03850b41410b2174414281c01c0b003009508406c004000b010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 727197023 1250 727195773 727195783
    0x20d140c030a1d06040f0206070503031003151806050603070f09020d05010f0608070f1b0615050103140103080708090d0312110301180f0b0d050106080615030d120209090108010509 79
    0xc2074000309190311042101103613450714054800740c040e8031410319000c2156240812121015800001d8036101e00d405090013202050900c0b06550342848400301f0900490184244010f40c0099083c0750000d655649402000b010020304a40e003602c2505800b02e14400c100d00fa41c0c00405149a02694990190561030b043c0d0300c0c181e1000064012003038081c8100750300710186540c8505545810306103e03065100c00c0f01c0300307190295000e44c0300c01c1c2070455209124040e0428617030805401c21082c071444d0784800450450302501c7c0d0409002003d01c0051000958000050213001d000c0d042007070610314070317000080c00c000764010102c1c04070344604d044509007041b41c080c11013082018609241158076010703001e50b052000103140300340709617902070204001d5400c0c2d101e00078228002e072025443c400d541c5031150003802a800396112a10805001a00141592901490380c44014000d0000a4a2030b60241d540380840340d0502c24a9409028008094840800441c000c2140000100d11401c01d080a18200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 727198273 1250 727197023 727197041
    0x1404060905060105070605040804090903020d030c050f07031d04020a1d0109050f04180c090e1009020f090403090b030408030a0c020622050a0807050313140a0504020d140c030a 77
    0x41d09000800120361381010550301035a0b049031021880359a180b0304014984901d402160305949048030380010301d54001440c0d29905480d4030208081d0008090540d414064400180d010041c20401040040d03c2021103425061f0841c07050650400140b001900baa000b6048800015500d8020f01a8242c0810440c2001d03070000c0c28280382060408000c03d00f4500c05043e014021900c038511141220192036000090a4008080001054440b15040058040f4440c040c0d2140304605102035010510300c12001c0480e4001c1004076003003900c00910400740402082035007403010820b0005191304400c4025441548240140c0380c0d80e01d4140381d140c1c200c440c0800715004551010040110b24070f44102c19980c3c075804605440d08140c05d03481e1140c41e00f000d10800a04142010401d84204040000035102036541d40d041e0045054603000e81100c4107038006080740d440344400d60100700f282041d900600700c410401c04042803401034004400d000d00c0781500c145020b03000000802c0b18410007840b8180394 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 727199523 1250 727198273 727198289
    0x50105210f0f0a03140a0e09060d05060108010507170f130309090c0e0a08160b0f070615090e03030f01030b0a09021903060c03060f05130e060709080d0903051e07090204140406 77
    0x1000e074010710061a07c191116014000c60504000c01e0080e41c4401d044015560b21104546483d0384400e190741c041d240c203650301800300b48132640070310001e40b0880346641308244042c0e10f0410b80d0b48001418000d203a80031420350900180c004045000b00e11809050403414107074813600c605100c200e091201404e419888031529401c5200047c504619210310740e0115244130f410316840d841c0c1400c50101c1c501c2072a41c010600c928240c1c0031408c5d0508030740d0040413990803500c1005071408a0001a4891004946042484001000600c002040088480d4000403041780000320601c5560101c4c103458941c8000f100001d4444004104221090003070221000b01864140607040c41c1c00c0307044043d40c21500680784603008c803040f201c1806401d43d01614641103110200c50090800d074502801404135805aa07605002e01c0c074031904654003c10722a07007100c1d13000008010000000700c4021b09207111003241c4116006e9501f0014100e0300700d0000e80068045c4150400c0c0701d0303400c403040204076140340d400546 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 727200773 1250 727199523 727199527
    0x306030c1e060e03100b0f04140a143310033314060d050c0a1103030c07030c0203120a0908210a081b0f09090a050105210f0f0a0314 58
    0x1a82c1c1d00c01051100e150300d43d0841c04a06c1b91801c0d800510346000f103090f0b8580091130320f00e1000501e5224905180a2205032208000da411303440e00184501c6001caa207149090f406c000350200b48030801070800040c2c007140450b11082107408001425580110b4030040000f62103c0400d40345004440400059003000d103c4103103015080c01001c0c02c003081902c260034042c1e41c5007158104a40301e0b0803ca4540b01c0c40000e040000e850821003410f0750b030304040b1078140001d0880c448212600b00000880707000781802c0010780d06055075940c0031580c60031154000c907050702801c0300060742c1d400c80201400a0031103507202c01c0c180030305018000349813940c4081c051403c5407202d200e040b41d1414900c01c0b11140c3e6842d06c6c1c60b0309259500d42100350b0f9054514103060b090040050410701441005001c0c1103500421554044541c80742c4070164161102800b44c2c0e40e01120b0382a00131405042c40d00310503840c00d01c5034142c41b050603649a00701c0c10300c5105000c2c101039070044481c2c102007652028103001d0070700c60410b10394 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 727202023 1250 727200773 727200797
    0x1203270b2a012a031d070e010614070605060112092d120f110f0105160c1106090f04050901051803040e0105040507030906050403021b040606020a060c0306030c1e06 72
    0x183e414000d881d01c0124201d00004280c10352280e0010140c00d00208090344003408540078440c0c3d17400d22846a05181c0d8008000415050300c6207900015503440110307190b00385402a1144001840050b2045050280000c185800c032040c6005891025014022040182a42c07860f08025a410b41040002c0900c810102c44006520b015021051115a29001d203034507074a02d83c140c1c1c4550200500c0d041911403031188000d502e50541088ac03159612004080d986500b480041c0c80c12110300b80300a1441c01c0b90144014913044c1140601b0404070002c2c448107200d210800400c08803103080d02c0c01007159469004001603650300445440d9403080d82401513250034a88114071300c1c1c4510600800384169143c40110354000c0c820703000003800c29003110017004582031a15002e50f035179944ad6100142441d0300c1c242c0880034034052291004942d01600034000e0180d499440744018007080c403459090550760440480880e00103083e403809060910700c00000c0c3d001c00d403c4094036006680c020001c00c19aa0560 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 727203273 1250 727202023 727202051
    0x815030106060c0b0a0b060720010815040504080904020f04030b0c03130f02010c1a070e030f030702061b0715020c030601050f010503091513020a1203270b2a01 70
    0x9800041d803c9034250b13000341c45001520015240c0e00440d65400b0703102185010900c007440049488007070927054441c054003144001540c00480448241c1c0d0a01c880358210030351401c0c5070300110340c0306104556051400100c2000601241c01108010301442d0b80400c4c180200020000113a8101c120462024154589100c080c00c6010705400300a00d060112203038081164041c0c80004c608036400b0752024114000329000e03103407518044461200185821030000c0d00b50801142181040404d100554a032455540038442d03564032000392000006200c0102d040c0444c2d040c4082c1d00074141234807809040450310382c0001c2c541010030400ca48642c0055004010700d031b860300c081e1a80303da000c0c01c1071500c07507a9104c00315007807001c04110f00c0581c403615420800c03292120340c20005024400c45264807800d80710745203d02c2c80300c003003a0001e020480b0500c4c000003892000c04990510507560000300a415110b0280340d510350000b0030009404190f1060002528100d800800c05480c603080c020042c0354180d9000b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 727204523 1250 727203273 727203287
    0x50402070b16050705031c1508060c0903070b0406020601030510060803030403030c05090d03030b1003050c03010b16050109060c03060b090109060e010207170d03061707150507050d081503010606 85
    0x900d00d801c03a040100d02e40b019000e03c083d030760701a8221099070b48540c045081440840c2c4240f0003c0e404600d0320b1605500c3c2c40c1c403010031400f0746900d1130080145960b0305041122550000c0700d102d9040c807401c0d00000d02444420001c00103008198050b0040d9407661818034a0080040078031500b0343d041903418401d03404004240d1f0b0340030f501031a02207000300c0500d009903031351322071802d103250050280301c2c4a03800c1c0b45d0543c10403800c4644c1518460050185214110104e600075500e807081e6413410801003208402ca400a045e80c0704200c0419440c0c0c02182d91380742d00b10b0b02d01d90340454007952110707480d0100361742502c140d10007440380d00788542c500381c601c2c2c0000b080a0441d010304000e1014281c041413240e4820001074003d403400c0000030076842005880300b580e905145d448100001c2c1056400305121086c8003140310400c0315031000300221801e0000b0b05c0820341c02500a1807c000080c000240031a00410100c64a00c031641c07691065030505100021818901107911802681018000c100786648190 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 727205773 1250 727204523 727204531
    0x8070f03080a030b150310030b060111250f06090e07090303081311060c060a0f0c02070b070303110a0305150a050f061b010603080c0106140a091e0c1206050402070b 72
    0x500004c1000300b80001440130204000c850450076008010440401203500580c000d50b80548080a500e6651000444a0f035031941001c000f29080308041e4182e0740d4000003103524401e0000b1182c0c0c80c179902d81c462401c1c050b0031580b042d80011400c420410016000036403142d0001800c2c908204400c2c15509e014165030406441401d5a241032002c400170f02842c4c1d03052200c85c200003409182e507501c40d0f02d0401d1380c1c0c200a580d80b040302c0e490aa5082c45800c120300c1240c03100f008071340241048030318003030042005400c0301ea020340516491f0103514000e170085800600b80c0b80b03a00e440000c1c090070210510031b0051034502e2250f0088603d0785040c4619520140005c51808080340c2d880e80e60f44d8a4940c038060001c444d00709031080d42c00c001d80401040408c00103400d04007607000007000156034504000c65a400d221010341d80043c1c0191040c4841b06141d00003c42c420082101c1841050001d140041100c0300c1c00b421000090070f0480801880c0158000d44000303080440b03055080c04040d440e50103200501078 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 727207023 1250 727205773 727205777
    0xd1e080411040b04020f0c060109020c07030311030d0906090b06031506041d060703091502040b070807051c0503330f0a0905040804030209070309170c07050a03060608070f03080a 78
    0x1c500c00420703540d41c0c004801c1c258000c0d105544a40030030300c40340d581c1c0d040000e4242c1203001d20000440c20411034803d03103076192886001003072480d286d03480030340308251000880d4985001c2007103242513032052030052011640c0b00318800204482c0070b0920206070722024001c40d10a8000e50281403820721111180350b0401022140001c0792880e08a451142da079500080d40c5150284c44200001c140e09076000640b420300800c001310458208138100403c80c480c500030030010f4030701482100701180c0c0c0b0300b01800420b07100710304a4207080f4490074401100032104102c3d40004200104220007101c4105850010904040011114080b68411a140e200c1009203150003086403890f818441d65031940d101c001040041010440c034140740c10081c040341e0040c00140d025140b9400410b0a071840713807050042241d00286000d0507036010031009500c542c0417043d009628801d01101140b2070b914810400010342c803408002070501d20300750003542020020341c04042c100d41c1c41d18042000c201c6484c201c0d03603c2081c074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 727208273 1250 727207023 727207043
    0xd030801061d0a03050601050306060d050d030f0b0904150c0e1f140309010f2306040504020f031b120106030b01120302070e01080f0606030c0604030b0a0605120d1e0804 74
    0x7003400c000e20b8030515070072940d000324201000410320801042503416150284c00355691503460806216803134030000390040807580844224006c00340310ba8403007017802100c1d40c4041040440800000c2c1c0144003541c0a90300c650702c04040309a410300501c65410860101c0c10311105140e546800201c1003c4451903040c3d448445540505d030081c4100305501001d84560881c945a050030b50060f07008042da9901c001c03100303107004208480401c810000c080d01e0341c21845420000d07580d0030140005080080c1c01260840c6003d500c600c0c2d41d550a000004180b03030120110380c24088254100130400d48414070f1605141d1400b00d091002c00c1e087c0c01c00506591245070515540c00d1249007ca140426aa1140750303540941400407840410120744030744101c00000440e0303115106c0004160319140c0f0700c4c5a0320342c000020013041000032041c89216901612141c00061203d40d03613008190310b90301c80005d03500340f80c1000c44801c0415810076440d90001c82010010442658081b4000c1e000000241c4003600819203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 727209523 1250 727208273 727208297
    0x30b10110c04090f0f051b01021c110a1e02010e09130f11030604030504030b071d01030c0201090c06050c07140f2806030c030608030309070e062e030b0d03080106 71
    0x4d0444e2141201d0741c012845883e00030f541c100291a40ba5050160700e4000b02c000c8a08142c1d0300c0040d4a100d1259000d03129494640d002606448940c264130a00119005441501c00881c19006010040c03152120641c9503084807840010550000704603a54490740d001028040115031044842c900c140e440740d907145d044051410400180310414945960602c04d00080200305a442005081241c2c0b244080d0360181d110180c0903160b0740da07004005028081016913804607503119800c0350201c030540b8000042c50514644808181510365041400070400001d8002a00c0341c003008550000c0c810704d0f590842c1503142c2d90000300940102900310b48580c0e00c03c3d64000d6004410442c1c0e000340c00d0541da031075101c182c0d1000060094200031035a00c0129150901c000307603422001c0112403040c4000070281c100b40c0e080a005c02135240c0e01038420382e0059050007211007101c240040500c074040d041032014220a42c005402419503031044155400b50001c1da00e8840040e40113550070381900d845003490224461 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 727210773 1250 727209523 727209533
    0x15330e01050c0304120b06030102030402030d140708040e01051005040b1218030d0504020f0307060c12030b060c010204051906170402012604020a0b0c0318011e030b10110c0409 77
    0x259441810b42408000740018801a8444150703040c81d00c106103c40c0380c1e9549404040c201e02080714007a4041e0015440030036218401c442003001c0154024580d420285070340c030f80c8403882d0032a03000002030980b488018403440c03801c3c0c00024444038403490031324a03007400d0141d10400b5004055044241c3d865404c0481c4c440b2075001255402c8850101c200ca44414601020307078047d01c4e06403400d034001c50400b02142158200400c6010684501c1c1e21802d24206071651030003800824500b040c000c2658942e10a0600d641d584014a203130180e800000d6200d50602003006003441e2145803103040c1051000d420422a030b04500c0c9603122480022060702c1641d100c0c00140d802500d1910364800c0001400102d00803c00c012003c0381c05180251090707002e45868100740d800d5480344010700c2915074410300c00d0700c124200c03201410410100600d00101c031108075101821043e14510310200200782c9902040519080c10082c2110034500351400400340038900c90b0003500c17900b48408985c0555116031070407017889 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 727212023 1250 727210773 727210777
    0xf030a03050f16120f0f111810090e04061503081201140d0602160203160306060503030405010e270a0203040b0a1505120106050d0507060809010e060703051915330e0105 74
    0x5206e0500c140400741d0101c02c00265688080c44032218404401c03502c41d2103003002c00032212504015162a403806d03003000c102d041241402482190701741d4503440c100c13400541d100e0f00708000350322904009844012100a11a00d040141c10402898614191551855452541d041000c40d00004010381e100c00c8801490084006500d002e500b510070b1010228800141c110748804407401004204412600d52041544034410b0344120750000d0310500d00700200745050042550b00c0c45c000780703280d02c1950741460032010f1071008807250301c80705901100304400d01c1364951340e5a80c080030785501008104080e0300c402c2e4429025000300c038001e21500f420000b1600c000d5006c03001a050040c640b50426220b464229030340e0800c0e010791000180e4103008036003001d005004040340030312004041d1240e640e58403800c40081500402611004074074480e480840341d118481c003024281c1c5400c41125075428000d03240c618446107007198032013010701c00b0005001e541030401c02c08403103401c1c0307401c1c460300c00005c1c0105d03554 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 727213273 1250 727212023 727212041
    0x1b02010f050c07060e01030f02120601051c050f060a12021005030c04170a020a05090705030f040201050702192d0b030a0207080409050109060b030124020f030a03050f16120f 76
    0x58072414030041404ca800548088001209030b0b0280900c030a13510150040c5d0041c0480d01955400d5034000c5a41e940c0250003170b10302c07100303203011090030a180c0c44a0364041c1c0e10203444a150b03c805502c140401410a0082d02018003041388003144102c02560216814100040040013000008408221844202003c40c0e0040c2600c014042480c05514161707a141c0b08806406c91184000c010300007140c2c140384100714400c50582d16058250341e00c00e40c140394103d400400403410081d007081044010ba44500d907170030300e81046402840301182001c0f10405034500390443c45220400aa003619102c0c2e1001703c2c50410340c0d0502c07001d59120f45620b4405401b9004000006240803000300d80414405d100790321481c12203c0d203000a00146640c0c2c6c0b84000300744030030b01900c1d50018049a034030b59010415105030b21041801d104803105081d001002600b160042c0c6050b1000985820034441400c10f010700154010f51030707001c6200380580925014241d510000d450070001511290190010304042c0c0c041d00d21 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 727214523 1250 727213273 727213297
    0x7060e0f0d2705090703180c06030902030606031c1d060f0307080f011401050c070e0c07020f121c0e03100605091e0c07020621161b02010f05 62
    0x9001c030380700c006481080d400c1600c002204040a402d40c280006802030803c581d4054548400d6480340b070070450184c151040742e04d0f242c072840720314180058180c401410082c02181d400003501540d51042504007800540128403030741c08002452400161500345408283c2107081488041c9000c0322101c0000040400d225404580030440380c1c44903c0000040d845860180c0e0740308a0382d9920440070304608400e0040303040d500da24002180c00b41d40a1801851500c400c04100c2d003a207952440500c250305012101e000041e00301042440440c1088903803160908012501c0d40d000405406401d90303a8443c402244102496011240b00340b01d002c0e402840000e500a000d0fa810504840301c10005041c0750300c40c0f14044c3c29408000b900582d00603101e01c10070113100790480c0040d11807825030381403500404401d90b404441042100c002c030044110203070b10a92500545201032401d203c5c0181c600c0d2a0010790710502485002c10300a001d064040d5100840d0f0900300351a013415500001c494600600201101c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 727215773 1250 727214523 727214533
    0xd02040f02030c0306011803050304090207081303061d0307080904090f1e2001080411030c120a0c06140406120e0105090114090307032f2e0e0307060e0f 67
    0x10480720b080e00135442180e00780c071100c42012034911040500c0c2076a10002e81203800621007488401496001007000900913800e10f401c1001c02d851058072000c80d580111030035651035000342c4002c148010316150700b00035240079500b00382954a0b905e00740d10541140510079651001d45d00104054460a070342d00c6034019003480b040811440e002c079421201000c0035640c4017503c40080c41030303424a501e9450b0306031042c1c2d9610020380b81d65640f03400035a4000c400e55810f0042c1c0d1f45085094482c4204490491414002000c00c4840c03030a01d022207007a107422100820520003100c164061100c0216000c940041c07a0081074160004502c1000781005407507900d0710750a203400c4c4a04164150010903180214403807601311900c88444040d640c0c80303042801004920f071140c02c5d1a031603042411500010b0024070114111110201c9000e06261411110340011703104444041e007108120080385016605091081001007068034555540e4014418001d100d00e4803091a10000041800034403481600c80b800c582d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 727217023 1250 727215773 727215781
    0x1020f0d12141905180f1e030304052802060711031c0c030305131209061b08070f020a0305123117010e030301090e150c090d02040f0203 60
    0x505409070100005a03150401d018140e9007050301001c1800703146042e000072a07000801d08164058000280010340c0d80700c0398401c0209002c024030000100342110809080d200c900e86040c035000842c1c0d0045410154018400c100006200051351250603101000c1c200b048800e0400d03c8410032107400700203400c00c0340810300a0801100c60401c1105c0c0e80c0032000e0301d040606100503105050070301140c41c40001d05003a50030010a009030710680d0400641c03247c100c80c6407000d40701c1040318990503021000081010904000c42584000114000f212070324103014816100c0d21041d10784d01460101520355490310b83c0d408115980d07458010300075688001504c141a0f02013000400340d4103c1a4050030032901d5410341a1441200e0068015074070700070107010681800d000d5007011054950580805039035840c04481d0035a001000558001c003610349000c601c00e000d50f8095030402c0c104200908862400f00c081c06914210344050300d403005000d481c441c6990000e8000540900421240220020700c00000c2c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 727218273 1250 727217023 727217027
    0x50f0118020409020f12060103110f0a02010912090302210706050d021329030c1206060705010501090501050f0603071e0e06070b0f0c0c060105010e04091a01031506061b0201020f0d 79
    0x6d041c408196014080950b0740b4180190282c0301a1440307403074203600800a08810700480350241c80001014400040c40e6240e42d40c400d240042005030340301c080b40303008000f0801c61401e0048420002c40075869800809401c894060392a03078240a54000c1c000c000c549110301020503030655a100a9108a082826a460b040c8401a80000c3c620316066690346103001c000e2040a0304980c00f4000c400030720b03842c1200341c01c001d4018010103044030740d2001d02081100003054090080c28081c0810b544001815450b10b8200242131203402c104c40d00855003030041213100d98101e001c40c14500c600c880c4e048481000641d00b19002180600140c0c3c1c010070200e109028041e201c1002481f40b488030500849035110003046410a010342031041d003440d0321030801885654410000e10018010241002c500058180d40727005100411002c1000707802a03890041050014020303c039051001914002c2052600f0910001e001a10080c7c41c248200600603d200c00c591007080b031031304400b203034806803800102c00d0303200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 727219523 1250 727218273 727218277
    0x1506050307050322150c050705190f151e1404020d080405120c030705010203090a090906060314211602361006030515130e070b1b01050f0118020409020f 67
    0x5c0172511514245881d50b41c00e00810485484a8004006082c1e100300d1040d605c0114008030000c5070050407410f61040000c8003142060186032604402184085c00c405c10406028800d0828004850070080404425407030404d0140e0410f40550b02180c034040241440000b40c0b041e07510454000b414524070b0240d0034004501c1d6000000120140c2c0c1000395900e0049030f41e40100c2c2c480e1a4043c81c4075108000200c4c09610240419106081c0071078074641d25101d031003000c1a503041042441c0c00030150315100d038401044031044060455141c5003080029602c55184e0b207507920f0300038051020305910908800c1c5d8110a1203a2102d11060003007440d640f01e1072191225015105004030f20f050180209800c0d000f80111031007550800c600c050244004000c001c209650540e051004d00c1d13a4940b95024a181402414098507040d80210740d91005141207007a2566220100030250345003000f40204403205043c2c1c2411181410504451004070f08090030091040780e001c080740e40c0c40003846090510305200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 727220773 1250 727219523 727219553
    0xc0c011b020c0a050a0e010b0d06120b090c181302010e090a060e100305032709010605040f0801021201030201050a1b030e010908061302040c050f0304151506050307050322 75
    0x74010040fa680303d05205911525000b4410400d030f0142c01801030104500107060080007002020a520f83c2c1ca5013001603440c01c49406854100c909010040200400c100b400540c17182594850005810100d00d2095042e019007a00010340440d490103007568807400c00c408080354010718000c060305011401c10001e050f14462503a80c248200c00254880c4c540980c45c40840350000091460212031620100950401c40681c85541d02c0280b00c00e0750944031405894064040b9807603880c1d40380d00b4140b05010144050740300341c01c030b40c0c0104020204001403105a40c1142d034282441c0c0d032100f600e41c2054881641c074014000404d042540100189580001e54201464081e213881d5003079511105203d4580b0341c2200c4001c0c0d119500c04140d0014289079001940882051800e9820420341c1006644690f0081d1016942d0700002401e08070880c0c55486240c040380c04d030b40c1c2c520005915000703000e071681c00011f04030070901002000103445a41c1c042d02c20341d07022140c500048031804583c0740040326a01102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 727222023 1250 727220773 727220779
    0x50c03070305010e04120c140d0e030c0307030c0308030a02070819080f3904120c050108040c1a120a150503010e0312090c120a03030b0105040303080c0c011b020c 71
    0x40b0001858000c46805140280d07000312050031b480d10108025a0810410801114204482da2000030b00d100140704540c60721040d030b030f07501e07940050600c2050301d400d40c406219413281c1c000e18400c000040300b040e914012281d200207030f240c41e9603130122100001d009020b0060f02e01540001c0001c07140c0400c1600d42c084c03803042d0329120305a4698001c20030001c501211074002c1384d440c8111403881c6081c409642d50301d04906940f0900700b440c8403030b8480b02c90b80180d80324480760660300100360200800c905140c8040d003820710300318165243c10346510716008190300c940c0e03556a101031480c1116904d072170103c0d4034400007071303030030030440d003420303803510000713161400c6510303a0340030a520045194a01801010302c0c000006004500740301d03202950041c3c2d00805090f842c850b2045d13a107446240d41380c82c010940300821050140803001068100038003038840c01203100b810060104014030010703410041054200c07410300303110303519805c43c2031200d4010101e280c140c4c0c3c1403456013881780c40b1071540000d07074624401060f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 727223273 1250 727222023 727222031
    0x61a03040c0f03020d14010e1c1412060105030a271b030b012705090c010f0207060f050c160f09060e04050c01030b0a0e130c080d0e01050c070306050c030703 69
    0x40d2850504902683c000203500142c140482c0e00401c10b032038502001c000285000180811000c0c0310f4070314182c1c80c2d01024410001d0254803802c0c85030088140501d40c00e002100b02e280412440c00400350110003800d050501ca008000709602c40b54540c050f14610420709800b0600500211041d031210820308003c492070030500d9036600040404e080340c082201c0d803146000103d64200300d803080101051403074048010030070700c032044240301d2540140c50086101d2805080d5082c2240001032400008c8200d00003598048602001159030200001141c00310600d0000e0b00d6404000c1120309299070b4030344042e4100d00004010840c28403c212402c101ca945000400501c0e40da916510020041110050015042800403c0940d4004d0300710f140c81140040c80c003e1101d84403200b4080341c41c41034a9001402d0005c40502c4200510204800c0103885400004c0901851a21000b84a5154075030594100003011a410f0450702d020090318020710f5100c0c505000174034020100071200d8100b16482c100190034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 727224523 1250 727223273 727223279
    0x31b03050301240804020603060402070204020301140306090613240c030f200301030828081614031311060a0309021c02012003040e040b0609090f0d12061a03040c 71
    0x700f0000424a5541030301e54003082e40d107580810005400040034180c0042d02000b604005a0b11032005502808002203014182922002850302d040030042c4440056800501413150f19100040c0070034010303a01140c0032000d854041600c80a82002601c1d1414403070074054607850a9400da0000d03081d60f07501500801481d03030344002e04c43c60100c4070000581051030801c0140040742401c0001d11001102c10300c410012072040b480310700c2c03405007003401000040040050043c0d0200c0d090000010648901d446802010b000040460500c03001e001020f011340f54804103000c000754030444100e540002040561102841c41c409000381203110f80413071188218440601c0031802150454400b81e806a403410703d03000442c643d400c40c410304011824000e1000344000901951000211441603204031503280003800c040060160140000d040c031506900030780b40c612104070700060842d22a990074500b0455413428090f803000101039030341241c04a0324401c03070601c010039103a40066004600c039010040100b60703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 727225773 1250 727224523 727224569
    0x30f13031206080a0b100f1e05062d090a060309060b100c0c0803120606070602070c120212010c021209010c020303162d02100216030c14040b0a0e04031b03050301 71
    0x6001e00403500801000001804280b12300e80440400e20310030ba42404506440d807001480c42e410041c200c10721003c140034101070700b200c07442c030450007051401c0e9000d04048180c000a60b4044080c00342d2130802d84d0320280142442056007008114400250481488000c4140003c008500b068029100c40d00c00b10350016a8583c000300329100e580d240c043c41030054071944e042020700e034400304055811940a0010501140185402c00d00600101c0305c28000ca070300d42d10621088500891504a02d40d1622071003081e103a40116106c030352040c0b0080010380c0c8050060060314072030b2015070065054800411441c03014540c88a005021034000d0910148080983c030880c1508050610550300c0c0d9629504d10307100500b481d121a000e4540e650065688200b01107007100c90200140e403041d600c05038444010440c1405000100c40340c4842030b1000d011500c0700c1c40c041055041c0703611a250f850030221001a05062107001c440f900641c0c945030160a00515040c01040c0d90400e0091703104400700a0b4a11200c80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 727227023 1250 727225773 727225801
    0x307050a1e08180708070b0f0f0c031c0504020d06050a0e0f01051806010b07020d0c0b0316120204031e0303110d24080607030e07050415090b06030f13031206080a0b 72
    0x110508001d000c29400d040d2140815003003d90f58003d0323000184042d5110407900000743c030700e10100e24003d6886411004d40005030301100801c91202d2464801804056100c04106120781c40e0042c801180300d449420f400710040c21100148420750040e4a2100d88204041d0041c5008090074420325803c00007554289844100070700c22004039840800610006090440d14100c50754050b82081c506503a0350b1743c0c505096801200c2c03100c1c000c04c40391082c2c4030a90b0010010b121640d203039407085003001c2c02c683d41c60003642000c1030804801001496003200b09840b0380c12000582060140341619044081d00c0c14019040c8195a0801c1d44c0310f8001d521505440310425400f1142c50b90018a40761b1114001600184503040c003058680c0980758000c107594595014441c0514541325558412503e070160150489010b15111407140000304140a81802940125504040028101e8403401414a410f0780c030300840d03218110541d42441e200050000003c144075403250b008041901099075103405100d140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 727228273 1250 727227023 727227029
    0x10e120712201309020609091603110c07060c110303041d0a02030f04120905120d1205130b070e0a09060501020d0c02100c0804121b0803040b0307050a1e081807 70
    0x114400450300790354060756401c0066000d0014051b5450010726034040307089410101c1d41d890b20035894492480e10710394903210f00d030703c005880d8143ca420008018000f42d1036210610502d000c00404285000c213005100302d101011440080c11aa6600d80e039002c0001122131106299251000200024228200a000312032007a04501c088030b1066a450765440010300b1200f000408004010a011806481d80d4080340c010024050080000301c50220004001d5030181110034a04d5083c1030034803800d00104889440c1040d4040242280c07555145400c40c3c0803c2065242a4041c90b00c40e400519040740307500c1441901c0007a27080c0d4000014401c1c058138850f2003407000941007206c0e200a02c0b00180306d080070300d40c064440c010300c42c5013640d28150504010301c03161080e034054241521808003042a01041c5004002501c00f0b10304052810030f11070303c1c80c04000c0500e014800009440c5491a20980d4040e802d904400408100b2403070b5100000d0005508441c810076043c48034442c10900313500040c0103011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 727229523 1250 727228273 727228279
    0x1170606030c04020d0e010f1a1f0f02030c0712060b010e090a0509070305010906140105010c05030406080a060308070c06020706051e0903030702120606010f0503040b06010e12071220 80
    0x30b9079003120140300c020f5204622528589965006150528500380585158482281c00c003140d50300319515503807003807148080f006214001881445a60b4108240762209512450515400e40800c42d80140e04520a01c106108240503402e804035041d4800388041180900460301004002007000056800b1014200c1d0960310462a00c00214100c1d07141c0c20070b5a00522401c20703100c22075901d17518a0309445110100325005511000800900c503c079410190041600b481c0c0002c01d43e0160310350302d403284500e0265200304400c000014040562681020004681c491411a030b1421107090803c40c810307190040d000140101640090424880da0a441e03080d60407507041d101e007007a03815100c18264031038075541f0f40600003031241c100543e9030303120703944010307154030703002d410302c5c0c942480014036510100a41c7e40501405000740804200010381441d4031940a003800314403500408001003904074070745c003d010703244a002030100d00e800c500381c82d50a0181c49210309990103074440100c6102c0c0c1c25003101c9150 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 727230773 1250 727229523 727229533
    0xc04030c0609081c030e03042301030b0d060203040303110703021005150a0902070c0b040b03090d08070507030806032a0406050a0305190614102105070b0f0f0408060117060603 77
    0x9030f942040c04005aa03100342800120003200806c03181c05d64110b544520f00340000703510f07250408501c0602244a0035000d1800300300301180d40002490030802284017815240e404000030f001c041c003d620080205a690001d180c4441e01407400a5507046080301c98082c40e8142070224094281080c21a00a40401824078412074101a0260000d4104400030b8403000440e0304001082c44c0d0100060010b01512030166980e454035a0090b460305402d05031f107400f0400c000d010440641d40c00800e03964103640c10316040c0d41c9601e0700ba001074034001c002c888400c0d0011081c0c2040380001e249145692060005a0341848099500e00030403c031000184030140c5030341c00161305240079003016410880024030407000014100508004d5a042d984111000b61811b00c1e43c2005009040703049495203610012a0700e440b4821005030758442c1c407036525104050440030b010800c00e01020250007a295020f039400c07a00d588440d0b0b0785641544e0b031310081c81840300031301030310f4507800306042d02043c414402c2170040e000b04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 727232023 1250 727230773 727230793
    0x7082b0e01181112120414010f0206040807020d03050d050906160806151b0304080c0913020a1802090409060504020a06020703080a050906070209070f11030c0a14150c04030c060908 79
    0x8202c980c046141d111398011850500c003058251805040603100c548a410418040c3c500090030842c50090400f041d0341c00300e002c03c00003418080c11110380903410f0355001031701d070010310b019a200d0244a02c00c41c4c42c5820324040100071040000e60500c80e00c0048850040c10740401019034110300295440d80c0c100302420b403c0a2880114401400c0070950030f036510740048000038030282160403a0300500310310340104c2c845021507d414450036820103003c001c68841c5880c203500207620310b040742c03054881851040a912040c400c5540c152000a04003800600c00d02459160000003448104d404034401c13402088003055041c400121407055aa01c24406480c008888509a58640000343c42580c45001080000016118502070038092005510340c16281110307894003401382429101244200e9000b44000075100308005041982d1a8100b8540c807041208140e0442c1014402c40c110085051f1030414043da0100b031200400840f402440d043d8051074a03071100700d6901c80030344502c100703560210703040b070b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 727233273 1250 727232023 727232029
    0x181306440c040507112b030b0f010c030e0d080d0609020a023c0d0e03030a0527060a0207080c092401030609051513020a020307082b0e011811 62
    0x815000748035814100c0c0c0d141c20317808141d46400c540d030f5900029041701e0500d40022100041202c505000181001e014202080c00421a4a070040401030704204050740010280350040c40c2600080b4400b07842400c030341031281003001e0107030700000114039210b103000740000301041980309841d641e44041d400f803c0b04034548000340c40c09489440b1000c1031152100c0551100901010100403e9410000603101c4034403170140107000400a8407071180260010016002440d40c88811500540640c2a10385002c84200641c0e5102040f401c1a441c1c0000c40060b07a0f800f920740000d801f90445260074102c80090841d41c041c401c034900195240760110065442e0f010b80104441c0c031088a180061400040145da500383c284192803040d00c00010902090016500c5070a000081c0400710310700110030340c9005c4030400c1c0250741c1d00c6024005400c40402060170300e540c00442c5462043c51042e440001c4013200c03001041c400900b9200c0404a0703a40ca0050000350ba22901086401032942000100d52410b418200f4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 727234523 1250 727233273 727233281
    0xe06030408032a03070f021902061b24100f030b07030b06090406240908030f2805040e160905100c0c08060604050903181306440c04 58
    0x12143c0e0725002d28860010414221000e184a400c4596483c0c05280000c0c4c00039041c00442c100202c00c00084030944e07030245c1c80740030494101d48540c0d0380710b000f0107604841903130500c454a000c03446440080d2158007282141450284e0040c110315083c40d0710701e030307855400b1350011040d44070041c0048411000110b15900990201c9010000500150303d0640484006030448081d41c01c0801041580c81100c1c0b809a040306d003094030308126040192040d802e0550380d564034000d2004c00030715800c0004030306030342541e134104a00100c2c80b04885400c0740c259845003d41650014081e601c81800601d00203108440a048280007103900d0761165104141000c0a0040344020b248008017031044244003000020702004000e0002c5c000140039260a051640400c0b003580d0024141400c550710038080d144800304215001e50662108540d110180000b00040c0d1020344490f510101307d1401417000f0a14180d00b087c841151564182d0f100121603110701c84900030f0511000020300d25511000a51600d801d11b50300c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 727235773 1250 727234523 727234561
    0x309020d1a010303031d030d1104030203060109020a030b06072006040807030f061a210109120c1506060518060403020d050a0506010503070303050d0c12050901020a0e0603040803 78
    0x1008051006154640354840441d5490701d04030124201c0c010004c3c90f500d8420704140700820b90070214030150015469a407030040b20788001d0505d9030b5200816803451803104580003190b028046d11210f6035208440c4c4001c2d00b020241001107801c00101c06031901c0c0690850707804a41c04420411820f202c00d0100c140121b00808680c0c01a90820011500c240100810001184500e10004143e0303240d01e001c3d816500c50f5034640605200c1c0300b030400060b54405a03042007018540a90381d5886002000840c0581402d00c0c002c1c5c031058003008402c140c50383c000034074166207004240c052000219070b000c410803204248541d100051091040f03421405003a00c04028102d001000c503070416440c2e0b00021104144240d0840780c560206070740d2008c100e0180132040c010f0400f1000ba14245255460140c007038421710302000a09690381410700340386805908402040f80141030104114602050709078002e40c490210385000c540c440f0300000480c60010201c038032540d802003a00b070458a50014101140b22151 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 727237023 1250 727235773 727235779
    0x90210051e090901091806020d0c0e04060e1915060815011706060703030b030102041514091012090615080f06130f0335180d180f08010207051c020d030902 68
    0x40046d0300818194005440004404000000c0715002c41402900c030f403004485071406076052900030000642e500c4180d81d40465070704030300070110425000200045c02c01c101c00d4a4226000c1d00c0c04111558484006d41c407542d0301c6146003c2c3c1c0784805005654184130302c40055641c1c2c0b45c0d13200044507070a003a0068985184241004910b00d003801c000030f03007642c01540040d03480c07030040d107003a0340c501c0e511001c5007903a40c45144043d4a059000004a54200b40180c910401d00c40760054100c0c2100b1607520455915030044020083c11469094005030045a84254841c0d031040c46110850120081000c0d402a400300011038800304542d598048032820050090741800041803040c0d030344000080f1620321301d03220140b80340220381540c00b10540e108005420394101800105207100d441d04009600c0307042003281d060140c0103003500c6460404080c001c3e08004201101018005410041500a001410700c10415a201300300704c0400e10b00e40042c60903075400140d01c003141d0307009000d00079417043d4000780c00a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 727238273 1250 727237023 727237061
    0x506010603230f06030d1b0204091a07090503010c180e09031b011b08150111010b030a110301140606040b1e030717010807060c02060904090210051e09090109 69
    0x202a001102c004448511091000e481009140c1c6000d2103000801382d2242401303001c0809030100464010402040203014640c0d90b00004103100c2c0c808000304180081440a50552400b808001d1000442d84127950080d0b0a0100310351805000c4c3c0c494841c20310206442c44041882c2000c0144910b40280c20f2304581c0c001004007000080c51a03821100e01402840003140b00c903c2641d0040013025105031070001c0141c048240054420301413049042e000c1c003460309480f8100c00248550041c02040c0d000750741403043c020f55000300103e1001f0070303800721411030017007040450001d07440355000001c0761081c0e407260041001380311346080c000141000c2d41c1c01070440302c0040c501d2650724201703034030540700e100c040380607488586064940c245100d4013400b81035001d41415841c20b80003a00003401c05000074400d580110345803d41317031265444220290340043c600d17401102240d90190050744100304d8440d03a4200c0180044030070411b0012105200809403000d04160f00e81210800200380780c205001c0c01c8000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 727239523 1250 727238273 727238321
    0xf2802092e14250b07020706080a0c020f06010602010b0112020a05040b03040816030e03061609230406060c0209010b0a080f1312050418090804090905031303080405010e030a0506010603 81
    0x40d400008443d5042c10000006480032410009900c4100910344011503002e001c0901c6517a13800071405801266240010904e1460640141c0c20074021200b140b00038860000009441a81504000c4040740c00381c8a6001d1921054804170a80c414803483c0703004580c04110070403c4403094001554028003421313105040140000b01c0c1c03940018220740c00d50004419503000c000d0f926083c0031083d0040c00c0d03544903072590f081d00e680160101d085071040c0821446040d82c1c035002c428019120260f00c0301c009100301311450304c4100150200d1042c00c01603028a0980b0300106250340c4203012a4107041c070980717403020741d56142c100c3d24064000092050400314200c014002c002403002e45c6409943c005c030703160540c44505100e000d10403902c4c1c60382c0520105040640d02e03404030791031000b26415100c08003c04a0900340c207040180c41c6105040b91954441c844c04030020500021303034090000e4031001d03682c5100f5050044100f565408216102612681290f13004005203070280d8000c2c04c0080d400c441c001d03401d4403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 727240773 1250 727239523 727239547
    0x50d1218080a11041503110a0911030114090103110402070c231e060d02070516030f0606090b0913021f03021305030d080f2802092e14 59
    0x40168401d40302640449199400c0000c0e00401029000c0b0984040000041c120305251000c3d4807031001400d04010704504042e43d1300e0f100c900300040e040600d0705001010069001700711a41c000d102d034401d00f0580c0300041c0e01d180362482c4030a0490ba04a044e13000c2c410a03a6003004000c2d84104030884100b03a145e100007801c803c1c1c0f07003900c036020035504440070406800c180a001c10340540e03101c50f41d0391040044c445200c0b50748040c16640e0380f400d0130340010703219415485c000389420500140ca481034996080004104642203171007500301d61185030306002c07980d40c86003c0b109039403d0702c085507440103440001601a0600c0305c0d40c012482e00060070000e8284260305a221030380c0d45c444070b0000090300040c501c04080b800c2e003a681c00800c402e80c010170041c0e61107100117094200140c01410242c81c1c040101780c00c02030102241885c4000d00c0c640e01440d1600c5641c0320000d50048560178040d69611a08500054185d11107848007421102c88070a2132540b080115680e03940144c2c00a195182031120f10341c661 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 727242023 1250 727240773 727240817
    0x10e04120e040b0a0902030a0e0327031006030c031a073c031a0f01020c10032304260a030b03100509240618070e1008010f0906050d12 59
    0x305c0d0041e43c034203080a600c02543c59250003400c0319070007088074103900740380d40d10140310403606000b000140b1000800000e003403101d10800d414150b0b04020002c030078884911505411288a603003507400001c1900100e0603080800c80d001c81c0841c00d00ea070001c242030072030381c0c600c081b0395102c40c07105482480c1c984031911101041c01200b00065621110700c0941140784400441e0032a040302c00c00003120020000035a40c0c51070414041c041d1400c06d4125510a0003901710102c4400a1518003144480442c51900714840464090b03621148840103000c407640c2c0e00d071045142100c45030100d460007405041c207030040e0044d283c805da014440d200700d407003080569208050054840c24050704509032703240100740368081140620381e14407540c0c4040c4601a0f56400100303004810040c0c0ca414140c0d101d8000ba24140305414030542c020310340700130740d880440c1d0006c00319042c0d03030703c900d03400304c049440d0365812040312061700440e9000001c8000c010045000802e03507903400072862901d11211660f6103e01d1100c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 727243273 1250 727242023 727242029
    0x30906090f070f0e04080c1c020f01140c1b010c030b10030b03070b0310210201090b270f0904030e040e07082a0307080a0606170d030c020319090e010e04120e040b0a 72
    0x30509030908e04d1640c81c0d051101c1c507010f140800007072040c5907200240301c2c0e03800703000303014102c200300b0001d4659803a0942d06011a0109613400081051440c03200020740606902c200d42c2d846030324140792420305c80e40030740b080d01c0308290b024006020306801c000003405103a0028200e0302034a84100000194040803450031295150581c00c28031845d03903144005410746881790056242c82c00c1c280540311b0b03001c8102100e20002411010541000080540403504901e00b00382030640200f00d000400c003d05070410303207101010b001500c041005880500080341c0352440ca000c1c1e050a40c00c10315416001409809089010700e010300c50484000c001c00d00003d2518404da4012452504200210014840c281c0b150358010219100d8050740c00c1c5518200c9600c9100088249060580c0d03400000441442001691101c00c1c144100080d03081034401c2c0070f00300410503c034904200000c0750012854501da105400c0c044c41e80000707503400b15503001000380d80c0200e0344528190080e80c1c42458280f07581d1a04042001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 727244523 1250 727243273 727243303
    0xa0f030807170903120c060c03160c06090f0803091011120618040c0317090f190b0c07030605010b1213080903010203040b01060807090602070501050706090602030906090f070f0e04080c 81
    0x19804a40081071f003024401042c14800703641c02c0c0304020f2031000701c280b44842850300b8a08400c08104500d0441d00400d20180050f01c09004074100b1020014560000c42c01080d000040f68040384448800a0903192110f2940d81c4c440310a0268a2031390428481064006600802443c00701c1c501400440c100b200864007030f1580c140540d4100140854500c04c074800c0c035241c201c40303403400c1000d01c0410b0f40600014811401494414075000c848625110010003800040e0303100d655510030252a00d988a0b203030f003c20351b5564541800007620b10040001c40d0420040740d03061001036500d4090200740b10381301c08000c0e03800c0e920421402110341d03000e100031445a0710603500000f444d414a5002032a24a0042c00e51007804070401092200035000203181c812254246009580d80c15946850f0000e894840d0300100440d00100501c4a022130100d45140305d0190002210401d80030000b00940d19001c621840111a8419a061101c86c101000c82a4050b000d8030300d051401540c0031031240b030040d01c00c1180c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 727245773 1250 727244523 727244527
    0x105071e0f021f0903080318100b0f06071e020117090109060b030a021509040914010b01030b06192a060b010f03110d050601091a04050a0f03080717090312 68
    0x1145403400c1180090721641940d2a4800d02d443c0380606988004e00000e4841e0a0102c0042c07801442d19400e40c00451511341615074030084080001c010300f28184185c0d22609030345020b0342c080d003030510130b8640850b00014010180c80c10369131b100e4001900f5041c10303410046107280340030070140c250a006004100030740c00042e085000d03003007030400c480351102c640d8401d4000030000d00c09641c500f09035082c1d0401c1c1403807450340c803081c00000900034040c44800810f100340112080050796410341c04100000d00c00e880500c0381420350707010428288102505070094045e042800001107100d408154007282240300e4402711010a41e40004600790070401c2200c0306074981007211890350380081c00d030110880d0303800c09025040e21000c00c06002c0c001d01c0141940720b0390322070020344541e00c00d84001e0000d03c140c200682e0150070f90055032101d684036000d500e001d40856280040d100d410303039065400312034100d0700e03031030070030840360780d40e00b080e000c05001810070380c40900000c0031644c0c0c240138240115800c0070445c2c2d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 727247023 1250 727245773 727245803
    0x705030405070e280b0d0602041505031905040602091c0312150603110906040e010806011202090103020433050f100c3e030c1e0105071e 60
    0x2901d810300d0b607008041582034500500010f40358480760360007640d46842c0c00c441c1900406050348010101140c0c115800403117044200d040c05400d500500543d0181e4446410b110254038059516200540320300c0391015018020842030307a4a68043c5401034820200540303005185000100c00d17a8100c0820344070700c40710011719801c15030000c030103200328485140709001c102e03101001c08085a013184144030a140d101e0428582c010141c0c01241c0f0500c10040500d600c1d5030f160b000940c1130030024014031049200b980004124041c00100c90034100e58020490007e6a00315400d120150940000c6081000d204494100c1c0340f0800e10b408079540820344000d003070b44c54603150800c40070703800c40161103018204507000030300e40070f0740000b01c41c0051350088480c2481c02005075000c1c0c2880b5088461240000e01d550040140301d070b0000d81a0380c000740440c11105008004070070801000d0041480327004d441c40c1c00241c0740c10345d40100050b2080c1802291881c9a5200102104281140b40c0004640c21b01c0030400381 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 727248273 1250 727247023 727247033
    0x10b0a0902121005011b0206070609080c16241209080307120e0a080f12011e08010510210c0b04030201030516080f04020616050624010804060209010c080307050304 72
    0x103990045a699502010f40c3ca000000303400d4451400300400d2000c84000e905003503454a1086540999002c1001c0240c1116801c1880c0759400803048003010b4084ca0f081c0000c00d0b55074024100588411380301c00c105c0382c2c000714052694084840c144400381b1007018042041c0400034803c9400b04c41c000c0400d03550300e140c103000c020000b003003029040034010f28000322600e02010001b40f103e07500c1d0b0f0003030326655130740700212101312140507107540701034010070690000c01d01150404c070300040c1d0b2448030b5111440c80e45402c0194241c45044a0095402c49080820410502090f42072802008048101481c80103ea03c40714103a40c25038000096044000404004659141c400c20b0f5003c10101c840000c07802140c4401804e6032405040c5074003449024011a0a55443c1c0c02164030750a4a40040b25a0005070310f05541c41e171100301c9048840c10030180d821590300c000c07031a0485000c80140d5035960b080d921541d0364030017074112032403083c1004400d103210703070004aa0300d0045000c1c0348540c40e800c0d103030f02d03103841c007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 727249523 1250 727248273 727248307
    0xf0315030d020f0606061602300f060606030f060103050628080c0a080601030609240b040510050f120a08030129040f0e090f030f0a020c190b0a02010b0a0902 69
    0x78050040c0020030203200da20401c60b1f2622610380d812103403850038038003115100c1c2100170405000c2c4420100900c0f50900c1420000b500844d940c048020f90f050360341d900c810410540011a03501240c03a14010000e11203601c039500880e4000c90060140c00041c8805001e4481e1540311541e40c0303c2d007445400306000b2410100301a081550048502c201c895050910240d11a90103220040c0f0181d2038400040800c070030744403c40c03a240c01d0514609a03600d11001030351f01178520150514007662420001c10f8000d80c0d81b41544040c0d641c050005d4008010001c01d03c44410b0802508110a000e0581d40783c0004007000011802001050554003000800200b08003400b0342002446855010070002003090b031020004c40300c2150380c0392114101a0b038807205403e0418403040b200c00b40b94000000c11a10284815000e000c4000841c0c3c00c484c41031200c042030005039000d41340c0c46900e00728058020400c08100700020000314000e84004198880c04001150a2460640207420103d8010602109005540702d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 727250773 1250 727249523 727249531
    0x3020913020a180b150d0c0903020906100e06070b04150e060a090204021b0706031425180e06091e0106180f09050a0e07030302030f0315030d020f06 65
    0x6011003010565a0020700e1810980c400d81e1a2407110302c4540c41c01c0241c0d64030008000101a044191094200c50f83c41c0250384000550852180b512110030031480c0b2460718002665406000c550050300c5510401622511080b0000204058800100110740740e643c06060114072030071610100742024a00024001c2c1304660183c00c0343c4c6424072014110800141240d0407444486002510440d14000b080281c41002459400011800d64400d11071200203170b51411101c06540c10401507001c0031001d410b460003910124a0704520301c00485c10f0a802c01c60901c0315026034140200302004501c03c8003047c49407541700390080c0e00080b0422a0b1806e085c1041d0781d000340c00c144041a101e401c0700d4000b074140303018041e103010815125207c24400e10790340c2d03010300a050403100ca00315082d0390390f0745000a000100da2101c070746400c203003d00c18010000111001560360580141d8240105440a04001d1308001e08046c0c0d040e9030400400f03195107013030042000119295014240c1c00c40700d848110310b0200050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 727252023 1250 727250773 727250791
    0x210109020f122d0d020c04060605070309140103060f060201140708070f0f140408010209100302070b0c0d0f0905030706140c09091e010f080d3006090213030209 70
    0x700c078030700e402c000210b004580034240040b403078800c400034501da0481d100c0303c1240240b81c1c03140301144006a41c00054210840100300e4040c4040c640303900085606004650300200852030064081c0461580543c01ca04020b8040c0750000e0495a82c0e1842c44a07880140d00142c0541d6480c0095814440200e0340d01d94890714500f00500d0904042100034213400b030482c040c0e4108917840100c290540d22031000c90710104104403581c4d403900d403600007541c004c0d444498420320428002c1c50b0312024134080c1c000c0c2d502160f00402208129607442d01d40f00010340c0103082c0410b20130b580c0c3c40a000da0408511600301c2d914000c80045458007400e14191085841c1121012180b2290380700700034010316028100d170010030081d07a004e074032510749104540c540c411845103111050b443d44004a07000f14640b414100f1680c0b4401100d0501100c5a02616012080d0301550345820181c002452800d0350450301505c1c00c0b003410380005085544411000c100e800005c49000e1a086503241002540b81410009412a60352 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 727253273 1250 727252023 727252039
    0x7150206100b180118140a171203130204050a05150f060d1d0a08120f070507020427150c0306050306060906150304080a030c1803060209210109020f 65
    0x85140300b08280600814490a0354407800c0c0402c042c0d119900300c1108200b2200d407040c105440e003020341e08080d50075842e81e00922400100150000620030207890082c2400058008101c600e030032911070b5803000303004401c85100b203c1074000684540c469070748940780241c0001020f04044660403030905900306074500c9400d0f03000c805251699140d040300c05140d40401300140b8054418480d146542032200300111601512000307006200760000208400c15850300f42c0441c0380e880701c41c0f507141c042041c0c1d94040003400c1889840e005003850781c0401041d05101c51070948408001d400c4c10121180c141003241c10301941c0748030811021490140028020003418107000560a25020a545aa0040000e4880e007010004615951600f0000348903003150002000d5980c0382508110075070342e000c0451100064503058211819520074000070166a400e00c400385000c1c4e10b103440c1d82e03010350042d01a00b5406010103c81c03040088a01030b00c044210700420010807403107118010022505228402980500b4032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 727254523 1250 727253273 727253279
    0xf191e080703060626070311040306050a0c051602190305010e070609061103030a0b040204050619020d031103060d080405030712020a08161505040b07030c050d0e0102030a0305090f0715020610 84
    0x1031080d002207184070340210017080d540c0ca10201c010700940c8062200000c0002404410b021719908028031501260b8001e2111414051085490340b0841814450000450b10824018a401c0d00143c08103034614081c015541c4d2641c480d10308441c11410035032a150f104480400140390001121002820315043c51744040480b80c00e85520391000505000c41295903044070040c1c1d60f5a0340c15580501000b8000980b224070680c1c50303c0745034003010404809846034a0b030805006102c0c1c00358130044240501001c2c10345e290701c1c0500c00d82e807480d20422104004140004103d54404000050042100c4240d46d0f1821045006200d01c0090580041c00796401441950114035521031003201200d22044000b540c40c415250125114001d98211420014001480d00e041c0f40d403005081d44000d00800a030b07401c0e4140302c0c0c0d0507118285d003440c2031405030b0014004500201d009910180d405410b4400780c900a4066a12441c20160700341c000c0c0080c03080d1908410140c560401410f58031107042c41d81c002615007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 727255773 1250 727254523 727254557
    0x2710050c030f130807030321091101030506030a0203060c090406140603011a04030b31020f0d05120a020312010801021c05040213050414010c02030f191e0807030606 72
    0x100d90041d4110340300b0005141d001c03c10060700a24002d24511064400050722440e0040007a04a00640300b000c014498101126802d00d03c244540c07543d01c401d0908810903200015070150034000d00880d894041c0d003840c00090385040c08402c3c80758201ca15219038400da40c10403c4100c818171340181c4400704640300c3c0714074181c452108032415181c0c11740007443c000386c881107003504c00c2c4602d0704024000329081092049210010888030000c03c6081c01fa41c0f031a242c50041000290014803010394000d202d5041d58560b418100742485030030740200c1c00c0c0c2d2994090070820103407581c030407106800103a10000381401e02c25010001c0f64094032190b0000e41c5883c0c4d8405c0011100285008424801c5580781c0c0031404555504581c5403034807001d21401e001900d81070a040080c2c14200105107035950a100c51250403901c00320444804450701c02c003450410243c5c1400c41d00c40203881c290b030810b11407001a83d09101d8044012103d03400c003103681e03442e0180b0b403050004060368403030341c000380c14041400902d41c03400b1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 727257023 1250 727255773 727255777
    0xe1501030803060a03080f03010302040f0b011d060d0519050f01080a06050703020c010c030c0212250203241e090a03080c040f060801290715022710050c03 68
    0x25003101c8031a8072603e40c4400250b881030a64001800180001110090036a040c005103048a001321010803801044a411100340c90f030f1007001c94002140500c0c880c032041c5501060114011001c0d00d45414541000c0c50503080760b1054600301c511121543e406454000300f0300400d80e00c1a40d11042110035490210810b94a00844100500d0350342c80e0000211101e1280d81603d0000521100034800212140c0018000b4010081c10304014000c0c3c40161540c0e820179000c03208a4116484503075410254121140d14098044c44101d81c0f5014015240c090442850159851103003144003002090070b0000c280400032030903100c0000c500100300c040081ea506c010920040f0680c150519025a03518042c2c0d900c200d11440d000044991810440410301a9211601074107032490600240b000d9544541407040480e500307004c9028662040210100007002c0c1c0c54034010380e00c24040c015040031440414502e03201404402c08112a9282c0c10004043c0342440e4031076406001c03410403901c2d220442400e40d880e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 727258273 1250 727257023 727257029
    0xe01060305060a0e0a021c120e03031c060e0c0310061b14010912030608070b161b0308210f1005010c030c1712010b04080a20100207090e1501 62
    0x18a9581300850300820b41030100421040d0300400c0d0098200c2e4003034501e15240f0042c80150360b0071001d031704111400380c040c00d00c0c50715490300100114245000780140201c040e251000105c440750702e903840055402c080074030581c0501c010122142d240d140200c1c0000c2e1b00070700f50b8814420802010808003c001c4c1c00550a0300c078541082200e039686040c40e03242809001c2d224170003000d800946138040d42503689580410291103050b0b090304e000a58400c4611120301410715030200c5095800084400985144c0c01590115003c0d4400c0b440d01d6175030785514005801040101d85450380e048a015803007201030361401d90004060381e802d041420072104240485019000e018140000c0b000c80c1d50070701d40902400f03507015500090400e003001000340068515041140c043d08000c4c8604000b00e2200c41d0503083d00c00381d950301c0008101441c002d85402c660520b03a98000120100065465050341d12151060070780c200d9a50000c1011502d0300c0c101c03000301c0d2942c0064040c00e422000e0b0f50414501b0010b141411 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 727259523 1250 727258273 727258291
    0x6030c0b07050a14030a090906050f121507021b03011406040b0616060b030724031104090207030905091f120501110d0504020a0b041d040309080f100e0106030506 71
    0x5810451410910348101200040c1841040003c8113503040c2c3c00200502d150112a03075681c40301a070f41c15a8000b904c0580c0980c030781c0401014200092420030071141c0e21704801e480c040302e581d0315130402c031ba130703400b0340242c5288005030000481400503c41030703228561440402c3c1c0080142c0d801710360000041d5078028002601c02d58940e0000c0c103190f03888800340c5101c1201e51a848506140c10301d40a002415402038650081c0030300c4c10000340000d120261812200c0c100d4141359162540c04900300e004161080f140260f9100501c03000c81e2104240c809020207d1107a02d03184110783c1410304004030300400038045802103480700c2d600341c40c8550f030042040c1100c0c01c2c900a0243c010b840d151046c0542000c0c40603045041b00410045400e5085420450140e402914408a01900c44a07010300c148194001c144e0b0b00440c0d41d10601c030b1042c07003881056000740a07180c0590705075101c880160a1440510080c5815030000c0040d071401d000906c42c00c0b544025000003080454910b80d512a15090003c00743c2007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 727260773 1250 727259523 727259527
    0xf070f030902010324080708060705070b090a0f030f140a140c121303030e0916110a06020a02030406031b0c1527060b0405070905060912151906030c0b 66
    0x10459000b82c000d08004001e817064404051000350560044040a00ca0b8030782600c52a50009242c40011a04600403180b558406240c00c003107844200c6000400f0f41000d040d4801c1030a00e00110b8418400450160301c41d0303440d9140d03441138410003091707403a0421241024400421403108510b800c5006000f094010301071081d220032070500c9a60410700c141c600b6980741000080c4d4130f01002c00074107c071001d44e480703600da2505560045050281e0028101c8140886407900107034085414003650459200c03c000301c0484810900396506d040c00d90300540c01660141c0e01c08907041c08402c1d0036003c0c3e00300d800d10010010380c00d8014100f0040502e06180d0f0094074035003403440d07010f803d14036a8125600086030302107a1007496051a001ca06444104403050b10042e141400c20101d618080c00780d03c0c09144180d4401607400c0c00c0c04c00708200b5603c01d0300301135400072102164081420781401120b101000040008986203800603001058210703ea80c46a034080c80e002003880000c4801e050401910140c0d65002d07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 727262023 1250 727260773 727260791
    0x3050121030909051005031908030105091305010c0e041a03281a150103050f06040b060702090a15120305030f070306030f0b0619050a090b01020c0d08070203060f070f03 74
    0x2460808032070f0059506642048100400c031802a0941811150150700310340070040040304c00f0411600c0c1000c001d2880c8400c000401085c0b402a030812340190f0040d548003203c40e036079039845003115079104043d00412490034246c6040d00e018032800c48000c0c08280d07601148040040000d48070394142d02d4801c08040a02c0380303030300c6407010866440c03407082e0311200300e8880205100409845080894062107a07018400107811154440e0040c10701849101752003004944510003000302520581109941280c4240503a002503591490402e02400c2503040000300010440b18242118102d6004082e81a200d00c4003c00000c0d400b600703c1394003181c8112a03040e192980e03d001c80c045c1c07401d5032014240049a050308001e00c03030245041c50040e00c08030341c1c04100001b0903410307484c50232540c412240e000400c20010022100ba0350021452024140f05440d0240c41010000318400c00104081c0d90440b00410328408506040001c1d94001d4a000444603003032074800c000a1a40640d4142441010f485120b48 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 727263273 1250 727262023 727262027
    0x4020a020c032a0f0d110402210f0a020a0f08091c0f08070207060c060504140303190b06090a060507140609011e0902030a03052d0a0f0305012103 64
    0x10a481030014265050140e015000078050341c40c03c2019812042441450050740c41c22071094420464060a140b94406054550f09100400c51001c2a0041d070200104182c1c00340020710391404080c1e0a102080606001c1c90a07520210000d000a458600c100040542942c00500071700240c20180780055060b61210940b90414402500c0130081c2000d0481600c8802d0308400654bc4218540c0e0b1001c03501ea81d084400c036a00d1006102e10404a4104607a81020619a0b048280e009026590f205034812801c0b02103480c65000b142c41d9070300092010b606d04002003c600400f030400b441140c03000d0501103070500240c0d184000d44108414004002003840420200c401c6281f40d101c064000e44035035241c058505800317000c12107010050540b25191843c0c2401051045c4010550041c00504820980399005c0d1165480321102c40040b6400500301c85680912511440400f11243c0500d9212031010001070319450101c071090007494144801800b40c25015038042010b820690060008040980bc00b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 727264523 1250 727263273 727263283
    0x20603060607080c0d050a1106062b120908060c03091911030114010f0e0124050d060b0d0509031914071a01080f070b0415030b03011503020a0812030604020a02 70
    0x4139180c9800b0b100c000209094001002c0d00c80804691995a103460806407605c0d124401200c08640c400b80700c0320380c1d141c1d8082c4052800704001e41903184d45c0303032200c45841e8825420300840e14080001c01d0390038180b007035000c18082d0303d40080c0383c20581c90a6051002c020394494100603902207442030700007088402e0128444440142c040080d000300030120303142e0450500444240240442003050030720001d42c03107541c480603d04a500d0004595848a94945120b481c01440c51204e000c005c000d0166050b4180790b0310403140100703001c20f030641d0380f08100110f14050341c10051001405800911002c02e803400120b402200401c030902d000340d01551410701d061a18064180c2c00780c582602402d90054801885055906030341105046445002c0007188440e60352105000b03a1940810a00c41009207201542d000d07a010041410082010350242000c6400c4402115200103544201c090410a60400d00200d4028210180c05058005810340c02c3ca4541d00c0f0107050140a180d000901e07000903071080c44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 727265773 1250 727264523 727264537
    0x60c09331719050c0a05191e021b01030209222c150103030f14071502090a0603020307020304121104050c0a08060907080601120f021603081302060306060708 69
    0x400101d01d0914001c000300402e01071000a00c8186080e010410b104640810381d0a18807a82e583ca0746000d02070110103204440000024081c4207035603101c0700010359462030040c142d405642c02131940c4070f11080482810f030394510398141803503c10880c2c020b00c0c1c4c86000101010b1800040c10340d410300c014010040c0100101141e0b000740207204c5007404002d14540340c01521400080e02107494841031482d1400d1500000e20000b404164000350686500d03003e000030381c02c0356001d602d181e41094101c4e1141074a221043e000442c2840c0c0c00108084589003003440740c4080c1065160441c02c514110790080c0d036a1080740a91210710918404800400c10210091801500040d105008500384080d40c941140c12004100021510110000c2d110382002c491140c803030f14581d918141c3c6611520015211507480c4004020040e84404400055804a000801800d4400e02c8060074a09003414000c1c4101130140502500c0324107040c499000d41e41344001e032500540c040391a0f590310942860000e88a02c1004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 727267023 1250 727265773 727265807
    0x6051b030c03040e0c040f17030c0a0c0302031c0806010311091c0c080a0f080309031b06060a08010516030b011e05030a06090509100c02070e04060c0933 67
    0x18155200c001c04005441103aa002d82c45103070319103422840000c940614041c0328140c400c0c041003048a404003401800903510013a06981c40c0c00340d080229824072850716405d88041d000130500700b0441c1010440c07031316854801d90f02280f1354000c1140c006d2081760050103c40c10183c5411141c1700c10b0045404868207484000d014a01d4803580c078039541900d040040b01620000e80d4001c00044d01403000c07030220340c096031049c460040318229985001a941018020300541d02c000d2005815144003000703e0890085000010009403038841c0070800400b40d41d030001d540a0b4184000e000c0615111980781c00c46140034200401e008080000480752a0403d039400e00450801080561500c0d400c100150301032601810180136298030340c02c1001c244c50301568544826031001028803140c030300507804031081031140d10503241100c1d516600f200b14800260390030380d400d50b0381d800955402a000200400104100d0f10469030b00c075203146403000b0b100b002400660508003444035100c000d40c850703c5100701407000701d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 727268273 1250 727267023 727267027
    0xf03080915040605060405070239041d0606030c090103110328050c2706040b1003020c15090d050309030d050109020703110304050a172d01060b0f0406051b03 69
    0x80e00742607004c4c0c40d0a60708580030303d01d00300106050b00d1001c650300c0d494850038040c6103120003142460b40c0010340038402a2151680500d20205a40e4840c0078a403501c054054a0202000d4120742107070500034082e00c0756129a00c0b41159040507110842d001e81181c0c0c02c800c0000440300c04102207802d00c042075040d81c004240700700690001441080102203214080c5048070724180c1040240301240e00c2c1d030000598003000c0101441c424030300d0400079640c48900500086004d030201c00206000140481c10000807030380210311011814020400b8440c080360140d03208480b807c1c07501010b6181c00c01e0240c00401c010000000540b445c0c402c0044510310031203414200150741e9100d51000003504042d100f20005000c503080c030b0b52003084c00000e4130140c840c0100b0384c042d842c2c90001c1c0920a2401d40348a06014000c0d50b410084034502e01121580b0b5100031043d0038200d001c030454003821182e440c1c00c803940740d00003401010320350800d42d41580c0913100c0e0342c1040c0c1e955034925160000e20810011000000d8480 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 727269523 1250 727268273 727268281
    0x61b060403090e1b040e04032a03081501050403020607032c031e1c02010608010212190504030f030209030a050a21050309100207080403080d0c1b0f03080915 69
    0x8000324010842e07440c0700b00381d800e9840300b8400b02a9a292130032003100030310042c442406080040720b5200e800c18428180041c034124295105a0310340304000f041c20001c030744101800305040e00070b0380103680401107460380718041400310f0001c0d003180035500019010320b0003c20503908050042803044810010101b001881210541000c009041b03050b0105002e801220031000c04000d8038182c0c45003003844100907004400b6102070502c8034200f20a25031085648409001840b08400e1005180181608581c1c8035189011010001008040141154010b18000820000c658043c04010740c450562070050f035204c0b4041d002074a402031000c0c0c042c007140a240d40c0d10042100300242c09649401442d11040c2c112400070058880740001c8494404540014040941d001c0e0a80e00601c245442112907038280742d142c0d110440d00390488014416078903a030307130080c1c0681c135003088050140006140d9030708402041c0f642c0c0e0064001e0710701402001c0c0204980440d004800c1030043d40024039288000006074a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 727270773 1250 727269523 727269527
    0x20319060803091206390c06040204060b03010b120c1903241406031e130c1203170912070602121605041e050406060201051b04080c061b060403 63
    0x100115180c0d00c680c2903c2c5a0b04c05108002c100280300342600e500380c14502481074000a0121059078040306481050703138083d942041e4035000350940f03945180c02802c107403410748140801c0f00e220b42c005140a500c1070004004001011046903290010308030300086039101d14100000c140a19900441030600509200603a903905900402501c2c080003040071400001c101000c440300624054101900b84001c440322035814000001c1d60008901d02c0d41e162102040485105040c00c01c3d80c0518040324a80210300c24061030640740300c05040701032200316151040365006008005001010740d07102c610354001440b80e40003840201018840d80e0000c5641c0c0d483e034030300a070007948180c0c0c3c2440d0414050003c10350b0b800403c20281c21400d0a5103825241a007040460794a40014401d0840301c1c2000c2c071800f04207a100d50040740000c050741d4001054600301500301c1c010302d40007005044001d0000744000c1101200006141c41c0200741514040e54600003083c0b04012000011110741543c8145020f000c1055 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 727272023 1250 727270773 727270777
    0x30a11030702040203161715041505031203092413060902130f050115050a051b0304151e140c0106091802030708030702010e01030c0e030105010b0307110a0c09020319060803 76
    0x43d0450307644a0491f40d841900200d010000e9840180c443d94021010895003010f900200d031704003444070005149965000001c0c030300010010360360070060021041c0066044204035408030405078a4001080740000b080709000524001d000000844001c000101401300652002003610740117015501c06086000d8000d0281c41d100380f41c900c100e8a85000021072040e00ba2101858100c5503030b60603e8141480c00c200c4240e00401b404c0b8a4151244007200c5035a107007000200010402d9203101c007040c900040000d00507145000c000c0801411080d01c9051451f0702980c401c02241510340301645546a42d1012030040c05260401400c01d440d110190010b58200e000c0041094400c0b011074841c1c0b0b45685072b803502c0e4002e501009003c56060b4140404540c029002481e000e0720620300b05200d929044006429507100383d00000c0f580f800001403105140d0302c80c040c000c003083c40c030000344079050403940c030010b001d4003a2140380c0059030b01102081004100320442d088428110350188002c84d203801e065910390b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 727273273 1250 727272023 727272061
    0x1e030f02060f0d3b03070303021b07090b010f0305090a0210090b1b061e0402100507120c0212070302060d02030c0403080c03040602160530010204030c05090703020c030a11030702040203 81
    0xc0c410b104122000070109000c04d4420f4038914050350416078142d400754081c0d0040162041a0000440c23207090440e81048010010b041c0401e000c2400c0810100161041401d20700c5501050b040904001080310009603050041c0da040d564800002800201107c43e900541c000080d444400910f05410307800d44003501e8011410b50054541d5078503610a413072020a031201080100e0500c1d42c00140251400141c14000d040c801d0400c145062026906c1c03002e059000138111011a85003601d600550034610044d54411400400400c400d60844d00000d1300340c001e00f00300c04600c5800200051581e40408291001142d001c804940c41e000c139074a0454881d005801b0305001032061044603000c01e540700f8040c40031500090304081d00f0312411015102c80c440e0300025411404444240c00414682c00d100800055002e103046030307030881c01c103410089100c0340502908100b6005018900b0344050100844460304103604045503802c0c40c070200749066008080010358400c0c4040204000202840070031864 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 727274523 1250 727273273 727273331
    0x10f060810060807120f060b0a030308040507270e01061707060314041502090a0302090c1c0c05161505071116080d050f070c0f1e030f02060f0d 63
    0x64075840d402035590701e1364a40705110301050800aa140841e40310107a1031100350007008046440000c0d607000c03800128180d0300c00c50004044004001c140036041c000e00c4090540b2040500301c0300d001c2e41450f000849203003030120305240ea62000c0c0ca060a0254400c4000b0644036481c048441c032489460758640300d540c032550021a04141c1c0000d00e0005405546202d180d014401240f40c2e0b02c140c3d03401000790041c41c00307140c2050780600040b0140e44c030303180228030408000801564400040340c1241c20b008000c050106103134201020515195006801e9482c03908505c81c1c00d1001d84e0013802c140042d90f1003a070070b01410340d103883d062100059000b6154409103a5410846800144081c070100c104611846856143d8000100c044201da02c60002000302103e18801c99080a540380c4030548101100c4d400601a42c03000c0340c08014581c40c43c100f044801c0e104804868800d4a103803030b1801e425000c038000034810b41c00090284140c460304010384008400318641008903035001040e00d40410440010951 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 727275773 1250 727274523 727274531
    0xd1514090708041220250b0306090a15030f050d260708060d0c1701061d010b0f07050a03090509161b020a151206050604030503090f03010f060810 64
    0x300c0d6000304a818011640002c413010701c0e050440741126a8000c180d42c01c4840e200491894242000420806911418540600c0300c2041d4802c00041c117102964041c524003c000c0c410000d940c1d81d032600d0161302000200c404240009112104181d881d01034000604c034140c1c0a55080c10300c08000b0700e04c03003541c00580310b88100419a0f070200d4410081103080c141091942c5000a00d00c501c1a41c1d5250050005002208206916560501c0e0f0140daa000300607400c8a44d500b81000c40c0c0f0034000ca500800b640202031381c03611001c00403510451014040c581c4032001c0040da16000451080440d82041d41240075155009103900e4010304042c000c4c808d95125101e800041918a0f611442034003440d6801d0b10b030250025000d001e20101d840c0d0714007003640d0240e003641d00000c80b0b003000244a00b9008aa41d02c2000f80c0d1561201c95040b0f45140d000036000d60b0003840f0038000100000210b400307541c411503240007544a403000190141100c0d8050742104c41c00c2490000d00d2480001e0700100303241144100f40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 727277023 1250 727275773 727275781
    0xe060307090b0d02040c110a080c07090204080a03050304021302030f0a0f0203270a0c080f0d020a0b01090911041a040b03030c0d050a0207090c0806040e0105040503030c0d151409 78
    0x1000d4408101d1501c2c1d009180b0080000180303450b86c00006005c0040c144004290150200b060030040c52001c191140d01c0b00003000b5030a22424031203980a450141c1046003060700700038980e41e80d1f030410304006090100000c08174055540d00f10b41d955110300d0640c02903540b1318000c18a0350325460301362601800701d410286540002c0c1214000c1c1c1c1e104440300706130804a40366032600f042d010000c40ca994842130049010200104012290980c0035204813002440c3c00074419207183d1500c00c003000c0620840d044002c0e5030703001030341100350181111508040440e00e00c1e501d0500000490746c2c003440c96886840c001904c10688009000c0c42c600d003070211000c0042d40302501c2891703100d00c9240303003000721508000c0e00c1c0690303140550040c0218086503c1120005522010414103c42140a100c1e012402c6241084000e24240c080c45c0214901c0500034002ca0409a4515650b40130280285041d001b000c40c104c5d81218241d0b11400c181100c803d07054905039500d107031416405050001c2c4a016040c05000a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 727278273 1250 727277023 727277039
    0x503090306011d0f1b0717160219080a170d09030206070207120b04081b2a0d12081f0e0105010e03030309030d050604021b070e0942010e060307 63
    0x1151181400c0a121740c24150403408140580d408000c003220300000411140744000c6c81c0c0c2d0041c045841304800c00610541c43c50040200c41c002803946401e021251400134030200e40003191101d10a40c1c0001d0300c0c20340187c0e1201075500d5000760700d92000f865140000100902d540018020f00841040e0241d4101e66201d0401c0711001c184044050007884c03d80c408240001d4000f8000e1403441c00c0d5030303003100b01c1401c0b4001c618201203500300b0302841040e081815a101050f042c0701503441100480b200903440045560b502451301d0024040003d00c020240050881d01d0034a001c41503041041c1c0640403943e0722180bc11500c0d0f1001e014250001d24107240c4071403581800804c2302d0244200030002d40c20710f950590808040d00b03008022a81268090041c0c0a1301d0f140305c018501d02c1c03001c0b030005c0d00000c1c0c00c0030341c1c005003004006e100da07103540c0c0050350798102596070794981c842c0c031a02d1740081828002c25030208007042c0c08940366050301d446404000500c9618901c0894000c4c00101c05a410711940c0b1010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 727279523 1250 727278273 727278301
    0x314070c0f080a0f0803041a0c04030308070e01081f090e1e010603020a0915030b1501120522020d1209090b010305070906110c030f011a12030909040503090306011d 72
    0x40105203580c1103160202040c2100e000e16030041c424950b08c41c1d800b081c0d801303800101e60103895405c2c039807001080907c1055000031085901c0006403410f03115552600d00000c025060107002d000e041e2000060814112a5075000030703000c4c25010100f88904040811159039482902d02ca00c00500f03456200d9503041c0b403040c0030b440110703038006010302c64141c02d041c0b40c200109103141500c0a102000795000000410005070340e4442c2080410030041810850005010030003150502e000e0789207844100000000414015110010300404580640c0203502c003140440001e40e2002d018060f10510140c100b6501107000410384c0d443c11024881d0b4035070f079001501079540588070b41c8003081407200305000b03a601c0303041401d0060b0083c00c2180c01445894020038106500c582c0c14050f965141e4081c50000d4a895039034000c0120103841480030719480c40c0101d0b0b12030062800b041d00c190b0260380030400703001e010010f50b403c90000600317440555039105e290b60245010112070542018003140050318043c1c070250 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 727280773 1250 727279523 727279543
    0x240812040b07030f020316030801080c0906150d0b1806210705010f02031c051012020915180f1b1e0906040b0409060330030203040314070c0f08 63
    0x1c42141040041d60b0140d0701d06190581c0441180b03c140100d55001d01c180b07000c030400034020f480750461541800c4410781060f8a80d00450701807003015080c424203840e100d0001c100440303d080d4064440c2456250500904034106c8140c0c0e1224055040f0070500c050040d01c58000c490480713136150325501c941001c2c040304060080039250358101c45000c1045c3e5010b03100704c01d4040d0141c4141c0b81750030300c000c001400c0c0710307101041d480400da602c1d401c12030b5207007034038001001034913820050700c580d007a40b50b00180030303450010b104910b00300c1c0d0a44d0000b059100c2d03010105030003000c264402c889140c403800600003c1011140c0703029092480a10903e0444808112107031140d42704034042414400c20040000790348515411a00701408000020f000c0689402600103024000f0740802d8451850030f001d00038111700070b8500b4900c4100c0200117410f089108420360302030300508000d61296151f050968080e03503101502c10702d16400003808010030540a5414003a00c0c0c0d00340b44003a140e034843d10b4590340c44140300d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 727282023 1250 727280773 727280789
    0x120606120a050d180b031905060102070b071101030e03030c0711060a1e1e08180304300f0506040516060212030405030417031905090904080304020424081204 69
    0x71580c0d400f0284900c0c0e580d40038400304403101085564540c0f204100794421140c0d05004001c2c0300095081500c240181a084802403004110150400040f0f641d14821800c000380546417041d442d01d0141d019030010b8042001403c11380ea02c900d070841e0007441c184c0c8043c00c1142c00170384446200d0904d14108040e02c2c813405107a0340310290307201092072030741085880b58000e400340302c012079501380303103a4001d24088520201a5a20050f074141900030b007407000e400d018000c4181e04180018040d89000601e44070040c0000d2071a040e4402407600313240e803805409131019118a807560f0248040c403100195031030080e44500c04603aa0380600d40d0705803004091034041e2500603003064241c02c8441719514003031900140030303d0030341e89000c0c1d030740b0280d61505000c0160780200380c00205a1071080030300d0050362940002e0908242d0310300400b034000103410490082006108510110205065440c0d41d40503a0780700036600740741050380b0b500006a840b6000b09115111081c85881019403030405040c1c2a1001c803440c031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 727283273 1250 727282023 727282033
    0x90605011419030f1a0306010b0414060a090308040b04061209020109050f060d0c090608070f0f1209060c2703170c0f030f04170f0a12090302120606120a05 68
    0x103501100041c1644442d5608164850707080d5035490f1111700c0b6144031040f4000641c200146400d0506090010581c49454480e00a100412001039104808102c441089404a9682c0c0031a00240d918480f50380010300610b4000c038004c500000c0031401403043d2550783d29440b4441003c0d03440c1c6026a070308000000e0010b10421810401070410228100200c0d50040c0400e00b4808540c4d90101180e2038640b442d000140a50340c10000d45402c00b001a802c0030303251a000c048010016809403401401000c42e4041206088450125120550000d20450f52042003440381840444000700035000c09003800c03007107400d03004061074801032000202084a0f0f2028100503021900320008400781c00813010314800c0e006407040840a041c2c1400200000c24044404907190f9081ca850240010003002c0303001840d50141034050b0004c4c0000940124043d8801c40c02c0e803082403504030484d5100c1865100a410070007041c40d07035140b003d012031620300ca45030a40e400d100c030213031445005d603444100d1540034015402c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 727284523 1250 727283273 727283287
    0x12031506090a0e0c1b030a1103070c0519080d030c020d030c0c170f03090a0b10050904060c0203040b040303110d03050f010b0a0c020603180106062c040e0114010906050114 75
    0x1565114580c13001442006a0a00f20100c0702891810010020300030039402c0000d00090460b001900100e03030701c0c02c484c006d5040c01d22076a01d070441d441850089603c105010300782c0c00d01c0c2e440c6582c4243c001d02442402d0f5040d8045040c0e0180290584940c40f0000d800f4220508080174070900c545100b810072036a8458144d009501c4140088456880401710f02000304008403180f50000000d5000300044001449520b00f103047c003811042028040380c070a000044d00810146d41c840302003640050f0014000507061003107180030707451807240c1c0c2c0c07109202c0100030600105068101c40000b502c242d44a00f5141d005d00400f40850071210120340e4035607407814585c0140404001c58000c5c0401140da4100220041560380002c1e840c0d800480301a0f12040d40f070040c14a070031000f03000d01c1008203034a00f4030b07a242100266041458450343c1345ca8203015848030586600a50b00c1303802c2130706005203182c020000070b03884101744100074109001e243c91240c240703140080e80394450284000754165042c0614200a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 727285773 1250 727284523 727284539
    0xa1113080a030f03050903040b090307050303040f17060601050d0b030109120c0201020609010506030d0c1406180f07150509031510081c09061d150a030f050907030f0c0812031506090a 80
    0x50001078bc052103001e1001c286900c00304000d101925140c4141e0010a20f00300d0740c410484068912045160000801e0050b41d0b40c0000545506012051005c68a1008500032078010300f80c9202c00b922000301d100d41c0100740c3c0c0c3c201020102e424000e9003a1003040c6d8400090318240d480c261007994040c3d1200301c40201061090500c00700300307842028202c6200030340000305c4c3e14040c429600241140c00105000d40030310805c1180010b11100e060150030901e2030001200c40c9000038400e0360341030103400140d110817507806020800e250001e0010301c03141801c10a0210380b044595018890980c460505013000c00c0069000c01c01002c0c1c0c06540e03403508142850710840f8040030310484114409002c0c1450001991510403030080c0364000c4034400e49800c6004802026180824a1815001c1c82c1500303004083c000030480e501070302d401040c0b045076030200d843c0c0310312039850039400300310b0502803550030b400c0402c1c881c0000e40c00740c040c14500d20308164000d01004500e2003200422a030107103c0306020031060b5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 727287023 1250 727285773 727285777
    0xb0402060304020a1a0a090806060307051302070b1e1b0304032f0109020406050f090a0c0c02030f15010501110607110f030f070c0603060e0a1113080a030f03050903040b 74
    0x151025002c040c0c0786a503030f5802c030a09100b506170110401c1011030120085075120100c0f200610403000200241c3c03d00e07101003512001c80d400f40d00c0c022103143c400c00f080d8035155011078004643c0000400010710b0a66114040c07070031403a03046040400c4c07881c04600000340182e0303040100e0342d80301c801c640345460b07a40d4103031040310301c3c41c8468800210006440e4001c049400e143c90032401004c001007201d0800348100030490b031071604094804d00800006441644540410b1036000c451400005204501214165503c9440140095142c49040c00d03612a010f0701203107082c4100c454040340c000e81d03600c2d04015201000a8210411207903c0b42e000554014440c040780c11612032640151303040703000350500041c210b51007003440606040f0006012420401d101411100400359131a0401440c2d0801821402201e000741c51030280079180e13240c10000341d020f1400c540401e62203805400c1d03215130700c200164070b480380030100780c0100340d4000d0754401c014040d0007201d1040c003903a0042e6140506240328200c944d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 727288273 1250 727287023 727287031
    0x803031014030712150f02040f06030207020d020406061106010f0e1501031d0102120906040809090705040e190c11030a0c030507050105040b0f150109060e01030f1a0f0a030b04020603 80
    0x51044600c00550550005410b04e0218003078641c02c01050360390300340700e401c0d01c01c003040c09004188104010001456061885401d1759100d10b400744c0d1340c1c0e48500015a258404120180d4043e1400400190941d0010003072010800745405455240c2e0380c0e072100400d412100d100e217103100548000020703c6540f6540011014090506002403211021041105d280c0303441b03009004140c0d030009000c280024a0700c503055101c683d100041c4604c1c9003c1d41d40e9400c0e4058086440d02a1105038042505640078201b03440251448601d50201d80c238102c2c11109a80c140c20060200452038110010541c6224030030054101d01940019031a04181502c00c0f80c2502d400d00c0140e0400200b40031950024500303004244c0035070b000e45420b01480c10310982c1c01a422102130408510482c00196170480c903600b2606603000c035801070030181644881140180c01a0031600b8412120fa89032641411411a140340b05081d00182903c060804c0446141407040750b1820b400082c062906074000a401450084011948 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 727289523 1250 727288273 727288279
    0x702030705074e060e100b030a0f050f1c110c010e060f04120c030201090b0a0c0b0a06212d020d02040e0f0c01080c0703080a05090712050c0a0803031014 67
    0x40040f4201a0341c451840341d140840760203031101c4003a070b60304008001440c52244055020054000810700080e84d074080120000d00030040750b8989418414103000c5503500c01c000c00207680c440518001d0104840e103c0d00040c00c04103503141d0f0b060380044d000091800700e00034181c50781142030640c1020420075420118803020403003402c00001c0b5000d10200040742c035091041c058004918150701c00900000d20b107400c1800e030200240542c0d455903074040c502d07020740d80d00310044041680340e4040b584082c1002e50450b00111240c2201c500d140c0c030031074902d558414003917008422211400c042c81d90882080c1d1041d600518a903108400140c42c007440008a4103200500000340005410f00b0b60341411a0442500d1843d0040110801d013540c0120306540d01001d007031a29450105213507000b03410f04002030540c40c822941d0b01c00180c40c1000c04c0103803502822500309100040706140c074001d81d440800d108801d0040701c14880001c2d14040010580703028511900d20450307414100302c92001c030405042003880e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 727290773 1250 727289523 727289639
    0x8270c0307140307091103161407080a0314100614210a05010501020c10180b031603060f08060402010f0e0405071e022d15070203070507 60
    0x1805a4040000400800403150501e0391107125404050900c550381d40a404041d0911300c080c08000c1090048960102d0b0503800302c400045c0a8800711394003901c407201e45468501c00140d80c000d11540c1d5001d00601c81d410398051106900750030f0316424101096a5542c0080041c41d0180300300c40c000c4c0360903021411014041820030281c03800301c0c482d480031f500c0003a100b50140301c180548441e50b80a500c0c090403003800101800030040e40420241c00402c0424030810443c08c81242c008900c001014004120700440f0075204c0c01c064000c0c0c0741d09030b42908804007080c078150000940b6902648240220764401c805012a075503940c005481e0f440b4058071280c20401030301418080d9035034903c01c950040c000e903910100941c50b0020742c804103c035a016110107550040c0720301ca11382c01000700300040c1d440c840b070101d40031190000440c0d841e045445007440030459020081183c450b90000c0609502405481103c651607928024100d10b50003201e00d404c080b8106440520308540c0d0040045080e1646252a030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 727292023 1250 727290773 727290793
    0x140109020108010b1c090602070302060a051909140604060209010e0904020d081303080a120c110d0f031d011406010c0c05010c0c03050a06090b16080f0606040f030804050108070827 79
    0x20446146c071100304c580783d0380400c000c002d0650403c9525030143d8107010800c014207000590000c14246404030250094131003210300104880e41881d08031090000341104c0040c01d15162100c042e410010a01c0d0005404040422503882c201c0d001600031074020f040b9101c5250992500d2a280e40881840c221304200f208000000440404c002d0041d1440c5a580340009481c0b41c0310002a03c0d88210400c0401928101c11409038802048a6107445580e040804000c03802e000700307402400000040d40011028005030802a020640101c08206c56406000d5425901c04c4010b55076610f0000014042d080d19003018841940141c0c0b1081610780560700240c0c5441c0e03030350764403803800ca04e2007002c954094031550488208290304069581000103500c01111001c03080100070a0000c00501203064400e49501107070752900c80100b110082e04400c407020607040d45070709281804d80e0040c881d090000300a4000a030703184d0b201d010001e0180c4825038428611410007162546a0f05000301c40b0880390048007414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 727293273 1250 727292023 727292077
    0xf0201031d01060f140315090705120c040c021612050a12020d030c1d01081b070308070f0306030f020d050f011d010b190b07061b0507140109020108010b 67
    0x840741c50405400030405074205901c03020031050310ba1115502c0702400b074001c0a1560040340010807502d02d006050704503580c1c00c2074940303002e1090703000941140d440080c9141c00c0002081c1c42c100d41c070007950180510007804000b05d0b50340010114070fa0019078143e100344941c1d583c10810303881080c00740e81211a0000142c84200070201c81c2c40001c40564131180c0340031503460b098020400c2880c440d09100d070b1100c294603925000840c007010b5082c1005100c1300001c4400e04028516400000c1d15071046444d101a450081c0c40b40d0404d4a200c004102c1c81f6040c0c100c51482405480e098075401155200403504035401e010000c0c403c02400c03500350180d24001410700c4002d02c41c3c445903040034100e1201581d85045031030f08480c040d51000303014200b03200d0801c1051907204202422103000e07011056682482d800d10000801c121120071321541d01d041505000503a004026105580c0540407221098005001281c02c98001140007408210700c01c00401c40c0c604400054166007600340903036042c9400054017 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 727294523 1250 727293273 727293311
    0x1d190906020a0504050108100b03010b0d060f06080402090f090c0f010c02031533010c03021501030f140d0804110d0209010e160503010b040315090b071d0a0605070f020103 75
    0x80d4000500003040070800f560781f0810b581e40100000320030010700d505128840c0341d83e201c1405003081301c00340066490107007019035203c44010070507800b00c40a01ca45440f0006e00c2014240d80980c840e0601c07801103400d40403030255103402810040300030500030092200b401403841d8808251410712542660100150700d0602680b40003010040412400386400500115810380441c02e86660780b2285085420180002d0b54500f1a5002401c01d000c408085240492800860130340309102d094144000004208071040042e00c1184102d4411800110480c2039551b12100090f0701d03400541c0c400040741c041501142d02811100b0044c0040d92100340c560041134141c04d00303900c606c10a50f2294100410121810303c1c00c10805a00d25116146514110310440c00d4020360001502d0151208864011741801d503011240c010307030007860481d0a244c22107010381f10088a440d50328031460100c180344043d180644030201517071225191203080202c240c6400b021400c01c608203c2c140340da9440d0f0314a400c4230f4440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 727295773 1250 727294523 727294537
    0xc1f0b04151701020a0e042403050127030206070f050d06120b060102012003190e030c010f1112181203070f030c0f0c111504050a1d19090602 62
    0x849070565180c0110400840d0070401c41036426441448000c3c16541d000203070300c1001c4811500410f055034061062803104410714494070301e0034098a40081084019000241050104900d00420031504c0c15000024103101000400503005440011034041c0218004503d40b401031501d80d04011688180c0130888450b038005010641c0301c0c0c00c01d07808104c68011000d5000d542840281f294181c100b1200440c00158140b882d59403c02100250f1032042d001a4002044a85030701031144561940c0203a8a90348504101b90542d4204000c2004104003806094507040c048100203280035034170f81d59001d6009002e081000d586010b5101c0220401c01000000110f0a060390907665038100208060504018504440180750508051021030341e0000c00c95a09101981081c107141411440c1c25001071b0a4000c3c55540148142400c00130b100c65a805001640d000f9100151000c0d01c80c01d1901010800b8500c25603227802520000f1191519002910303920005900c01007035600e00c5580703910691704048 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 727297023 1250 727295773 727295801
    0x130608240f07140c0c1201060315060b030601120f090609110a030503030106140f03010b1201090b060415030b030a0507081506030a1205190c0209060405130803071808030703030509030c1f0b04 84
    0x8c0c0081c4140456a15004200b00d916241007040303503d00100b012442c08020070b40c5051111840c04805110a0b54010f6030f5403488041c3e0400041815190000062124280c140c0f0340d09031420003810301e030401c000b10600b5a50020011410f42c0e01c0d0000450700c110741800004049031061182c07181c4000d444001d14060a00700381d0150721544280c4441808141c143d216118107410000c04002070388440c401c81e41615400858034120703507500507094024166500d4410380601c9548151400e03c40e01180c02c6056824010650b080003a50305881500b100d020340d5a540c1c540c020315090030002d07407a802c40c0e00d28901c0d513007001810280e40b49030070b207111402d4113000c101082c3c2071014202145040c1c402c89510030b07c111400c01990421282010b02030405c030300c006061010000c041404140511040301002102c402030701900c50302c816400c0e0701c0390040c4008070082414003002c20351a020100035510822a001d00138200303100d00d03181904c808410b1103000e5078003981c3c84094070030b5070b200c60051010200c001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 727298273 1250 727297023 727297031
    0xe03070801023403050f07081b0d0905090f1e070e0103110c06042d0f0c05040b010225050901060c03020d030b0f130608240f07140c0c1201 61
    0x40b1403a00680c01c3c008000c0e403004000b685520000724811104120540610346982c803040303200c0d8007013068491030101505100f404900b0700c03176240c00229034140c010403500c151001c100d41b403202540c0511342c07405903541c00b60084001a980644801e405035100ca28080c02c10020900702c10702c07403e8102c01b81c500c540000d040c0781706448a035030940546400c0d00c06110080e444e00406210032501c03234802500c010070140b00e1054140d4500101d060051192801c1840000900103d01d00050004c13210b0034111180c22120cc070025152400e482102c03d002d41c1a0064903041b03101c44071b100c038049201041d800b21503250f600d02141c04e844801c00d0324040d00086d1944c2c01182e41509004c2e2a00c202201000c0405060040c030722072503220b031080f03002c480348241d03080300b010400c0320b40180c00342000e900b00d281b446c0304100e0503103e4842c426801005560314007088241a8441e0600c1e203003007000440707803c03011442e604404c02c02c6000c410010912042c850090340d54215808000610080c29441c0c040030907034403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 727299523 1250 727298273 727298287
    0x1311060d05312f03100605040605042f07170d0f0626030408060f16050a0c0f022206080115291201080102030412020a030905100e0307080102 62
    0x40c80aa028042d00c04000318200c80c0280c1d1580004944a01540020702c031600d078020000036501e04050290100805807070100c1101504400103100784c0c0b1880340714600300b0320005158200b0b4843c001c0342022105c100c0e008035041c22813040c00009030034410102282d0400c07070480898066542a400d0381c4a0411084d03131000321004003425540000a40341040d49007503001c0282c030042c40d4841c1034000b143c6401002c10300000b204141140156401100343d80505800c100c0443c2c0511030180c443c1c80c00301d598a00c40c141d0100304070740d1030107200c12540110300c003142d0601c00f180103180131190384e0344010003d0b4034800081c4603040402c402040400003041e100c8205000b00ca50a000d41110445072000300300390716150001000500440b45111029110101060310b002007640b0200c031240e8040c00b442c600d14cd65102150f40c001e40c001c490590b1071454042d0201d441520200d82105542e415540c1e14000b14100002c01010500780c4016100b80118004a07c03015207003400560001c1401200051711001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 727300773 1250 727299523 727299571
    0x20121020c0604020f06030709140a0305030f070c0f030b06041121060307120c0e04050705030d05190302030105090f07051c090c0b0c060106030b0f041a040c081311060d05 75
    0x170800b199900c5040103000b003103202540142040120394100c9000c1207182c1001000c00c5403190250001781c41d5005c000b0349518109085401001c90300c2c0306e81840d0010fa585c0e07007542d5016480c60300004218640d0b8201080092805800080407855014103840c80c1c024040c180c5141d40342902400b0b030130702c0c02910405c4580d1406120110040441c840c030210881c0705c035a1400c0780c040542c010704115039090008a0107000d800c05c05070001c6c2c5800780458094020001000d002d6810649005880c50b816200c401030f068824005d4038100c40000e4401c0c00340e03455000e40c0780a0311074020008400c0201c28803040845580c040c1c0032802c0244074050005600300107050800001e80144c100884180042200e05411100010a2030440d48285400203650b005000081c00318800358003941d41c05030408928030300d0054030100c20790b00114101e8041001c0c0300e620105688102c1b08440ca5030b81e0b2100740c110070000c00c66000c040452440700600c55072400b8148500d05040310301c1a91400c0700425410885004a5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 727302023 1250 727300773 727300789
    0x602150a05060609060d0f0e0a170f2d0307050408100203010302010e0108070c0206030f18010501060509060904060b03010807030c0b3a0507120f0216020121020c060402 74
    0x40c11442040c00103140c000c000c40c809200759100b8074041c1e0000600c1003400c0c0400c1e40a1004441d03560014040446002c030066a0364140c0d002c26168616201d807102601d4600b032040b80c03800d481460890b400c0131000f00e50800d690300400040320032410255580c040714078400e001188a0445512400c0e03c460408a1031403501080301e069a1003644108010300160fa00081e100c103e03040c0c2407038072501d01e543e240400c590000103103030000d4000d000401402100071401c6005441000020181c5072000040a0740c10b00b642d0b42885408007144c0b040003020420708103a0000d2260130006080803445aa030387e0004510b07640f09a00107a403580103107030140104140410450002d000406880d814560503030b28501001c5103001c80892048010881b051482c00d2204040c007902d048020700b00410301c0e144402401c0c04640c2e41190308507601e0304e03401c0b07140818a88240c0d085109002492450500140e006584480d0407503158222072851040d24a403203840d9000900d54585900058003460400e807040c8400c035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 727303273 1250 727302023 727302031
    0x2012f19080d11040f141e010c03110c03061303020c0904240e0f01090b0c0f0322020a06090519032609120c091b03010e0a02040906060215 61
    0x840038030010034010440d03410035218190640400090311a00710050845144542e60001d0389105601c6400910800f0740742031012401029101591440071000d0140c8000307217094407186c0421071000304900030a00c100744285072080307000b04a8645600d110002480d04104070381300d03c2500d07060003049040690521890824503000c1c1c82c000d140f401e19a0300e1140c081d14040901d9604030400c00302405e82407184e0443d444011524065544042000c8200c0c1e0180140c1a02a82c1c00398800d40818205a4204101d414400f0032943c0700e8110344440c04615005901207a42c0c02010395284650382c00351b55131544020091807c0d4a510341454501010700590050700008801d0448502800700041181070790007801d4403c0c012046c40c10040e945400d4605030240c03114568004403591115181d10500085500e4042400c403040c032f8071a501d440704840e030088042e00c01c075803821092004020164404800b9230300010114005070800d070700c1c0c000d80741c111000c0e03a100d400107074041e81c4403d02d031242c28001c0d5900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 727304523 1250 727303273 727303303
    0x71d0109060f0821040b0d20190309050c0a2c100e0714130302031e0304030f0c0b0d0b040f0b03030a0c020103090f030206040314090a1202012f 63
    0x1c40b45403da890b40c44240b8480800070010180c1c1140c0310100d0118100e401800500580716158001d59002e40010b20407030856940b04ca04070010451510400000d0b200b41e03031240c5448050000c0c80c0f1400310003030510603130110391521560640b0030181e910520724030007800f0100206061254541140c0e10301c2c54040f4440c048003504a420f110b101c0f0101c51600c1c084c3e411100b4003110315280c0c50030443e40181643c00c011a044008134040368070029843d490400c49008404503a000c44e1180d000c0842032400178444d4265600c200402c000003800e000382c81c140c0c1d6004080c640040c82d6a00c00c0c1c03404651040070011541a9202c210f404540303040d10804428140c445010480c08003007001090b0b07a4072880e003040040c0014495140c00b103a100340c00022520350b01081c607400d21a100e01e0069560300041da0200c001c40d500591607100904010300707440685500401410038549010b0070301e0010540e9007000e03810131881c480e0f842050b0341003803034903119a000d00308600907010010041c00c0c1012043da0300e40700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 727305773 1250 727304523 727304549
    0x60916030c030803281d2d15090105160503071d04180506011a0c0d0e011407120e060a050f09040b0d060504020f0a030b18071d010906 59
    0x1007580300d0390303030015643e02a12076035507512455110f0740d07002c42c0240002443d440c14504494414410303080078481041c0000011400181605a035071103d405411654600039041c0b45911908075084880a01c0c881184c1a2901d020b00d25034011400c03281160300060b561345070740c10300c888958082c50803440010a403800d50b0450928120040400079a991610b9541e020f02c05441503a50347c80c0d100d00036a0795401c0285d4101200e0786003642d00d0720424407030044161106104071001c88802c00c11519020f080c400a442012a5007206440a20414002c0341c1000801c041890004034002e004100c1c07a4050041c01281d042040c0c2c004014081042c079046c00344d0024041c0302d80003030300001a038400030f500068898a0f101440701080050804a03551a03004610070780481c140030b1564417040c06680241d801040020b1440c0500243e060725110051107a51900002409014440d4410720800d9914040d1050980d0b1400c2c40510010605210b02403250701800401c0300c0122071180600811507070b95064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 727307023 1250 727305773 727305779
    0x1320070f0b04030e131a0d080a08041a04060e0d020c030a020418050a15051b04091508030c070e0603010509071203020a06060f080d0c170f04050a0305060916 69
    0x10460a140180104030009900120b01014040d044070402948007400201c509580000300c00064039000246d61554000821245900d080c00b54001d4580d50308444c0462900040701001c41c0c2418000b0f10643d100d030a0b0122010740c442500707c0103401030f8003400020552160004000c0c3c1848100c1c1c411805560000147c0c0380140c0b0701003101e001994040394009520f40032000c00981c56844030300300800314001d44150748100400c8013107600304011a52810402d55071000030f12198130300481c1c008020744005200400464520b908071407a00c41c8003070445846643d9624003a460342c1c10500101c0c0b650b422040c004d202003031072140c07000c0c4e01090440090181c1d040800919443d030f28a4050f8103075039043d5202141c00d0600030000c0c0c1c00d41640c050004c0049564503000c81c0201c0780c107401808101d00580a4111045200f260381030b00d503c0c0c0000803064584510302c910203050340041c0003020790341001d000001e502d65a03951140000d500400c064416868511102801c0007103400c00c121107030081410074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 727308273 1250 727307023 727307033
    0x4080d091401181e050d0b0f09060402060706180510021e0f0a0c0812130b06120c04052701020a112103070e0405130201030606021203150609132007 65
    0x4a040340d4400b407898004104104d040c10481520360011504045441b808600f0040d01200c194490842d20a5a164a03100c501000303071030f12030a0b68043d500c00402d0200a0105010740e0268402e04a01010100d00200c03540e902c904003c076200040e5095039000c00c4107030440b6411640d031911440230405883ca408580241030742d050040441c10810070082c20141c1081014813801c80d681c030111448131b034410386070118441100c1d4295400031912900307048003154650514003030511140448102510401103844203000040c0030080c00c4100602646064003481c801840305041070b880e05000240e07803006104400b03840515204504146580050130051004901080c4c18520104c40c40340141e50362a904d004070317450034001d903115074460702d0070080c420181a080c1b25100d1140c0700fa24188460303503031803800340d88622030f019481d031003680300b00700050074101034421304048508020315480c01d101418020034904000d0300301d0344102c50754030b00c10f0303155a0a071070041c180100e2540c0b18a501e0407015030b40d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 727309523 1250 727308273 727308317
    0x20a0519030215060609060706050108100c1e1e03060e01050a03020307031b0b0c2d1906090b070f120507050913060803031e06100e0d060204080d091401 67
    0x100500850700360f004548140d5400046440d41903005003029100c00850512a008010a00c1460314506ca444c20038140c0c092240250041c10015440b80e42d10024180912580c0e580c44000000801c820518a851040d5005102d036007080000c0e60002080c03401c20b49102031110301070700314600c0781c0701c10801000103a800088030320540b54072607240700f070004e04041c1e1309658400e182c0184014230000301d18107222850000790082000b201c441c03000440c12284104c1c1c589500c40e40b2048200c1d4000310301c034088030300c000040340032024818240020307031507825140c180240d80f040c1d56070000907544c1841e103040c0c140d11040040d60380111000030003032400c0c940c0c0d015010f44155900c2d64002e6038100b5640d40c0914540c0c0c4808010050b010a60350741c1c0c03405c9a01c203803010f00e5070041c600c10b802002001c91154103114400c61004420b40c4c480541030b5580380100030b200328100d02d080320099000c00c00400c5109060140c1c400039401500c0f203a055030b05103103420b00002e0f20200445c2c1084403d01031000402c4502e01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 727310773 1250 727309523 727309543
    0x50609070e01180e0a03030902031506030304050d02011b0f02011107140918060723090d0b04050a050115030b0f060f06090a0f030c09050612030a0e0d020d03020a05190302 75
    0xb869210340b5250403114409004c40b00e035003500601500440c1801e040d01600071840d10b13172003101500e0103407440d001d03c40207050044c7d844c2901076000740400d000e14144601c4212260740141428803c1080680f07011b4083d43c2080d5003160f103055800c960204650b003190b041c070700030221741d40a002140c0c141a49048003030051642c040c490506103002c2440d030242446c403d00c0301c52200c4d094030b03171510f0003d034050303d050f442c1d9080c0000e8084810740740d080c449045066a00a480042114050104640303440c4490303080034000b50f85500446100c400002c07024801d0700402c00f40910018640d9256080c11a440c2d440144482e1602417001c041100b15550345840c80d0132440c040798210b03181c50001000c160002d216400c9006000364040001c4140440907407018100c0380359040522040c0c2d120000d00070245411101c50b04254028060316210394007500410034006000381100c00c86106e903400240020105140c2580580c01004c44003003400b04c20704c1000140131540005940c43c4001c2e0b60000e5a8158210f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 727312023 1250 727310773 727310789
    0x2010e1504120909090b0105030705100905100504050d0b0415020a02061b13090209130c050406030f2003090708010606020c0d081216030501050a0515280903050609070e01 75
    0x1200c070b00074460160500380301401003240e040100c04030a01d4104031500003805000d10910441c2c0c00010340c0d1505085c0c00b41c8035041c0b40e4031a44c03254544401d1044100c6c0b1f41e03c114080c884203100c04655511424180580ba81c0038440100444c2401e09281c0c00703400c0e020748002400b900401c080340202da00040c225420110314200b5140c000000002250940510100001120704044000500101c2ea402400c9104c20445203403a05a5401c010700d8200e4440c02203100101d94103220130081c16001e03a1090701c020f210780e0004190351100401903c06220252806400640c000c01030080c441001c00c02c0c0c0010f400ba20000700f042c81e080c0360300655515455521a032244014291080401075224252085100003150208203401d003c207420030307a854802c03041ca0000380b80100002d42d034a03001d46894100e940180809481c0d10a00c0d0340c4001c42e030f016103a02c00e5107130030201c500840101c00340f149150040850350b450750390300c1c254980103080550143c11109141d009070405c0c01012003032456903045510b01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 727313273 1250 727312023 727312043
    0x1d0f240906130f090506060a0e3130080c09041410051f080106030e030c160503010b0117060d0203160f0f060804050c06031b031602010e1504 62
    0x4030015101000e14a0070144003818060340940003010381e00001c00e8030388611709556441d079030281402500c000d2442141c005c602c0741000b0a51494401b0b03201981140080301200712954514031486080131004c8084840b1003032414420010901040b0203c4494450380c00a11201002d10000340303000702c0030780aa0905100003e065050b5541c2e5031180da80d0b06045c42c40084c00f443c16030302d90070042942e482000c0c024010751076403000c055200c0030300c44d20074801a04c80e94410707400c184040f001030040000012461008000b4002c01090411883c00c0000800c428840d000d401c09090600b50f481848405e030500c0b012519a03035400e400c0d8101d403503000c442030703e03003000800f40340c00081d29040600c54a00b008038114400418111600fa1100c4151918504640134140e503901c0e0031141c1c7c20301210040c0c82500040ca040f60203180c000001e41d080049045845a60f079200e11000b040d81e032080d01c404803000c00c1c1c031081840064080c0910241e4240180280000421441001d002008020402440940b107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 727314523 1250 727313273 727313281
    0x10302070b0109051329060603090a3903050d05070c1404020f0f0a0810052107230306060108010e0f0712050a090506101208030a061d0f2409 62
    0x48240c000385d15002920b0f40305c814941c0d150b415074060030b410b00204041c11140090380600300f6004407409400768500403c103015640e00e90354481c00c011031419110b80e0550303010300d1130204043c4424150110500010399034915500e410341c5040071f4001210180802440100040f40d28000901c1c00c460300c40c9508500b440b0f43c400060024810020003491400b0040f88000c100e44215001d001b51905545a244030ba8440c515440b0b040b016a10981e90300001c0700d01070381d8903000b030840007160748040902120102515490070090000c030040058190443c08031050f0144c0c40e042003096080f0000f03085c001c4a41d4100024100851001080c2c4900c0c8000c40c00814021441382001945285c034802d010055401c181d103040010303001030841580c1920a0001096511603100f0419048800565a5400b4181a5620030b0984c0d00300401070311460366a07070000501c107103849900500140f1200c00c15401841c3c002080a01141c3c00b1300005143d05010072059000580a082c086a44104075000c00051343c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 727315773 1250 727314523 727314541
    0x140f0c09062503021b0303091e0a08011802030106143601230f10030e0c090103060507092403020d0f0609021b0a0b07030b03030d0c0504060e010302070b010905 70
    0x70741c42e82e11a005810601200c01c3c194045402102109960669a424000402003503640c2c0104c503032995124020203040140000da03a24405483c1c000682980c0c42c0b80d0380c0358605400c4076079180020881d01d1000052a0442c034081c81014098406802540300301d0f140740001c00c051241c000c0d1103041c20f0188080720300080c1c03202c103804407000078111445001507840700f42008032181031650618550820201041072490302013051001c4400203030103010b00580a107021006080036079050701ca6402800d0140c0241c1d159100c00c00c2c0038501581c0040b846007402c140007020b010140d4081c86070a009403051ba100001640940301030358985240250b2912042100c0c0401007000c0d075141d81c005032600d4400542c228054024000303054445903d00c50b0847c2d0703071214640305d06940400405616491340014200b42c000c0d48200e004403000b5007101d052050500c086001c60388043d160a002c64004541084040d03800081180c00300801c0c42c0c01e6013410210f80c5d481480c040c046c014000810303200c0c03001800d0340d9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 727317023 1250 727315773 727315807
    0xf040623092a07060c02011d06090a032604050f210406030f0615182312010e0f0705090112030215060112140411010509030601140607060f140f0c0906 66
    0xba003040d002c0000107005c46029000701549664160f44200415040740074030004610207220304820b102a290030b80103543c00b11550042c5010220f20109859005481c0c045c1d040340c040e1086100304010482850a404018a80301810700d03603841502c8443c070f0388019601e808041d1402c4034550300b804282070440041030b00c00b8001079000b901075500d88150f210006e644c81001041c07502814030000c42e40742e845604c1d20302e0010403010785c60141840454031121900701003031142d01c1c10001e0800010823610107a0071500b0914a001c02d415a9403001da410301c45403501c41030b45401002c900900100c000c020b44c0e0f002e529000c8040007803c00d484440300041859001e035280403030f00201c0c40c8040040340440110040484400d0714103a6184203a810404c4a07540210115680c0747e400400900c4241c3c80e08108060f48109003001540001d8103004410010f01240503c400380305045c240070840c0e1600c1500d0385000d09006000343c0448a181d002c0c050803408078412546080700590340e0070f0791481110220342c804 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 727318273 1250 727317023 727317037
    0x50403021905030912030412080c0a0606060c0c050109230d080a180e27010b090f01080d082e050603070908120c0c010305060f040623092a 61
    0x882641c400141c00c1002c04001002c18003030480350b12503e1454008402e0303980c041c90188551100341c188040002c56250000342290034601011906005403a03610391042e01c14036030204011a046045500401c000050300344050002840c089003104d20300021800d4075008804512441600e10951050326100c5501d051100c45d0002106070750342002000090810741d0b089103080310b8201e400c2001c500c02e6403000c80c15001e46583c10071000e9202060b10100e03813461408119035915961143c1e80d50b044d45440b0a104c0c45400c020398100c201c0d6250000207030074010f00c000031500300700003a41040056212009403039a1103403269010294901c1d09460484121020780041c0d0303100301702200b08005a0382c40350081060300d180d941512021800448024100d00901102030219008491040a0344d442540002d0740b1040082018155041a0003c28200d070701c80e800403441c0050188503606000044407a180c0c00708401d03514644545802c2c14510090f4040d410140b07850314101001038000e0b005607098072a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 727319523 1250 727318273 727318303
    0x8040308040602070b0c091e030a12021f0b040f0c080a021b0a05010917070b0121020607121d09060607050f030c07030c06050a0e04111903050f0606160605040302 71
    0x101c3c1c10031414441147c3c1015056912036a000174003061102c44c00c00f0065505d10f00a030040501080c10742e0b42c5d1080b1209034122200710b210f0500c0800c0f4202e01c1000040203240c0b500c40000303000014806000a4842d460544030445041555208840f41e01c00e07106a8001a0000010b0321041130841403000a064514907203c41c0c802d0104860034048103600400401d0300c00c2417121081c0c1003081e02c1c4404d5000752080074001c41c0b01d100040000002c4010f0000c01e4404200c0d1080c20141a5800201907411005c810384410b0541000745d000560007201c000349490340c0c2190240740c5034500c00040c1e80140000d005034000c80010402e4020003800f000302940428400c002c2d40e0315a01014070701c41c0d440003107200070f451028403c00000750443c0a031040b2410510b0301e594a8203290740440900010b046503580034140c2d02802c000982c0401900440d12401410541e400324030340c10000803225000c0350282602c0c0c4142c1040240c0c0412a0074980000c142d66441500894140d560b420b041e81846d0018004900d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 727320773 1250 727319523 727319543
    0xe03070305090901120308040602030a06030c0303050310051e06070503071403180103051005011803151a0301020c330c03220b01062f0601150c030804030804060207 72
    0x104141d08000501001c81c4141c1c0e901e0203e81e81c030901941c0c07401942d44090701103039a407004280441c5941d0025903000e00c000c180030407000d0f901d0340c40000c20000d1b540103600044000c03091085007103070600a0030052008951140005e102c074041074085c05608a90b491140303400094841c1002410720540d030110382c00031109140c1c0c5529180c59526039103e200c60aa900045c0340030b00b072066009100d40c074022440403031a5400c150920005580f03040c26165010b501e2210007100000080803c01c0c810f0200d10440400b1694400107026440d840111510041c442e900510036441601c0c0c000400300b46000c0c3c40000390f103140305004041c0c540303074a21440d0b40c251840404104107811101d000250b000740659001002d804c8001012208541c001e8080140241145001000114030552010805020b00900f15210302405030400c6004080d03842070301e115810840040105010042c6910800400d90801d8040000540e030010702d840ca0081005060117681d03008502800515816121400d6010900030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 727322023 1250 727320773 727320787
    0x607050403050f01050106081303121a01030b03060123010c0c140a170703080306010e0604090c0e01021501060302210717060307080c040f021201030c030c170606040b03010e03 77
    0x24016401400280c6036449084041044082e052044c2e41c1251496940c5501e0350701c07031003030302c6000700d60440f01a030810072803a90500c0122014841e03106120300f0802e24404103007040e8000340c140e41110320064880d4100e40700400c003640e008000c0c510904090000c02c80841a004016280c101720214042c01c00451044007151301c51400d100052101411200000903640d544106525005540d420310300f190000703c410000100176002850300218141400b007800c07080b00c4041a080c2e0840c2d44078000b0641c42e0700e40000c100340c0040e500800c07110700b8030291012907291800c4008618040c8070306070405078000380342014109804118420011700c0d200d0000207050041c40180150002560b03011041c0d0000007080503841c00041403421600c4030000792074141404000c0200a001400c00340d20a0340c0c0810401c0c180b0122050f15a01a41c400c84800f0010f5065041148155800f0780214048a2000486218044e0002041030340300f0401c59000c280103d0003808030b409002c0e02c4110340e50b684004140c41c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 727323273 1250 727322023 727322027
    0x80a0f230f0c042306010318060b0a0e0f0403111203010e06030d0203090a090203040c0504090807031b11120f12040311030105040f080717040e04110a0503060105210607 74
    0x900761420740c0021034840c00307003034400c0000311112560300c41c0054666a850f807442c0d036200403c40c0c1d8005030506001400d961a0021194500c124000848070141c1d100c80c440c0032864640398543c06800840f280e050076291010f06414400000f800240a03c40000a0b44015004c10840b0001c5041e05901c140d4807075946650000156409555061280c0074440d91078a01c41e10000c2500c801e42c400401d0f01c1702003880c0114800095001030703c165601c59201c80302017516203c5001d040f02040c400c0781d20780d5903150780d03007001040c0d59805040020414000d45180010404c40c1d190221440004c03514400d0180b003040e88240780c0001107007203c8403030060300401e041d84620240900226801003803965a03120218040508aa000306e9008007003411940ba030002007a0210064280f55100341014240703085140c2c0405541d800c2503100c500410400c00411040111146a03116844800d4407810310041c00c08001949030309050090704d0080a92400b500403690b4514020040040140150b50441c2040140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 727324523 1250 727323273 727323283
    0xb042621030105010f08090601170a050706051c0612020f0609130b0f03070e01090203040311010e060105040e0d08010911040e0c0a020616020703150f0f0506100306080a0f23 76
    0x2d200d0201e03080000340c5e60500c0c050308032030f071246000401810030b581c204035681e00c904205101d800d88612460b00080c0024400708050310140c1080c0d10f481d074503040c4844501150642d0410860011814241c0810801c1841004000059030481d40b080005100101140c0b041c096012815030101c10003110750203c2030f0316800140e0881c01500c0054a021001042c5660303441d440c403074100507241660040010000603406540c009203c0e1030302d084042c40e0000010700303507a0f62650b400d5840e00004010002d030310b441c0c403800032403d00c90405406004058080030700b0900f0148148070025807501240f405044c24181202c015000020085003503090049000c8a075411941d04c8070b0240c8242e50100e090715954103007038850001c40d6801400b01034116030b40d41c84403881100e88000900c0d01d4440380903000405015a10140d40d482d0340000d45490000b081008425003400c030601030509d07000043c8055400803900c2c0103044e400020b003c080c18600c0c604403400e10510300d20b0340040e003918201c20440c0c90010178 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 727325773 1250 727324523 727324529
    0x708280b0a0912031116020105040503030c0f010c1b11010e04020d0618060f0b090a180c0e06030c0d0902030f030403030c11091501030509011b03060305070b0426210301 74
    0x1a01c0101d0f002c071440607001c44446024140d48100180b10a8a003243d4103080502c04a1041c94010b00300f564410200b071440c0c20081603060160840ba0f114242c0c03031824482c0f260305070114509461202001d07580044a003c01d8880a84011240300008882c0d0340112021840110003420840d520340e641d440480003408c1a00800005280c1054840c2c81d001060141400b41d81c140700f06844224504054a0440d42c0020304094200b201c41d0000101481038003020a000300e100a404079890b00c01ea2002441e446417001003500c952030034400e00544610304010754440c110a41c00000d034a035070758000a45446411150707607038035200000c0c000c020103900625000c40103125000944407900302004000c1110301c02c85001c4100d43d07200e102d0304040e42c401d030461038000340c0041c00084d08404205621840e0080000e95001090f01c0742d82c2041000b01c10050344004250054031103007030034288a00c42e542d40c4040242c840300b908080c41800807080301442007440b545a050700703103010031043c0703607440c4100d4200344 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 727327023 1250 727325773 727325783
    0xa0611160602010b01021b2b05010207140c1009060507110a0324020f0a0f0e030a030f09080606151b0703110a0504091a131a0f090708280b0a09 63
    0x1d42d035829240b0044c1800034541f44010542c4802080088601f4103103100d490420084103415200350000c40d000b0700c01070800c0ca001d6001c079207000c0a4284c1e01807034002041c24a9005000e01c000d02025294407185100c19a691480e2071540c510140c141103c141c290b000440b41c2c843c56801d000420007506800d600144601c3c041054190f110703041032581203000c0d0f00c28181031444200443c0d445a40721303501100e002481818004401c4c034074400030a00d454801c4804030040703004130352000c01d500e40004056000700802c100031300007460900d010078401c180215900301c0b0038002060b00c40920f1209880f900600b0743c0c8004075100b9603542d0a150135200c1050113004c2c080d180801e030220309400e05005070841990000c840b6060482e00f00c040d000211002440c0d04c0100300b0702804d400002e00d402401c03c3c07082c100c01040e108182400f002d800c511710005414901a680804c40401c00e0900100c0c0e04941040e58114480ca100d04e8040c01403000501d8000c01002001140204602c15800d41d00c0040014003030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 727328273 1250 727327023 727327033
    0x506010806030d0905040b0402360a080712140f07031502090105090111030c0106030b0901061203080a020307090e0406020d0f06050a0e040507050d0b04140304050a0611160602010b0102 81
    0x5941416120f2180f2000c031000250010000e0000d800c0c65040165420009000186007002c40030170340807118124241c0410b07159110800a0a201c00919040000030085410841d00b80c600580240e940c0d40a2080000810782c01514106010481000861684040041e6060302c22840056a00c07207070140022240884144410700092441d1720a407108a072060b1a610f00d001031500040d1020400c080c0c01e074a841c40100b01428980d007003805094021846010150040d00f0a5107415095500d141c1000c094408640c4422010036445a207140e00f10807144030059881d01e074180203c401404032340114090032140c02c107020800155034003c0c180d410488000b00310741840c40d101034080c0c4045108403a442031503a5014040e040c91110000e41040c803a00c1180d450303c0d030310b9010520001c88214182c0705002c0010800c414048a4a400c02e2681c40560180d031509041c5000500721401d0b900a4204005055540c42031000c4104003400700b4031a00d0b014809125940c00000f400703000c001030008c0c014021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 727329523 1250 727328273 727328281
    0x503131703040b0906030603011d0a021302090a05010c030909110a030e0f03030121060908040807081c0302030604092f0a0807090b01090b0c0a0605010b21060604081005060108 77
    0x481a90190b40400f000b1924003c03031502041402e130005040749030706561b290012030010485441800341070f100344010b07110a50060042000002c403800b400c0b0031072401046041001d9869194440540d9800d007001c5c0c3c10070401c2d0504566001090b005480c02500e0024146007032000040a00480c0b14030355000d121494506414640300c0c120050b4850140d8020300050050303101c08151810401820546113401040c542c075a01c054608041041d02e48031b400040074440c01c00144201c8000c1e09141c0000e01d403c4403400c0103154160656003484042607408404100c0d02d9803107411110303c0540240404590300b545001d01c1403540d0468842c1c030701c203103424542400399060038645102128000e4002c0d040b000e190200100180c100c4100141c10010700305004982e4980a4000e48820a040801841c42c0000c07450440c0440d0340681000400d40e0080c841c080065140107860602c8402900141c1e51540751400418124000c941003035045001c1e440154015600036888030384940341c00d903255200c41d1a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 727330773 1250 727329523 727329569
    0x40c0e0901020301170d090605160503131d0f040215090d060b0901091e15050d05030406120501031e0c091128121104030206040602100b010302181507050313 69
    0x4004186c0702c000ca11500d6040051a0051019003d00b01500d10f200c030038039403d6514541141e001400442075100303048428422441500054089000c156001e41c0103400d086a100401402c000d100030b10410109000c880c0d005411810703070303869110180040110000a191010140c000040f100f40106801400011084440d010b150040c6840516550030310b2110350019000e40b10f00c0d074000411717070f44200380080c26031a484494003c4d51700a02c042e41d01c0d9814a94000c0450790074072a0488114240070043c804244c0c01100b400190f00f840c6280b408419007454011581912688402003031807030014072850b1f903c0101c0040800c0b0486c1c8551400115401d941c8034078030500c0c04042400250a403091544030030643d8002e240300c035a080c0d03500b41450350300d0f400a94207038401d0f0040c50050700b1105201c0a4640c2600950751481401d0805500b805101c0110207003d602c4111907a2003180c1c42000410103a0551040740c1c0550703044429642c3c4c47d001c80d4030340c00c2c150b1181e11038050072140e03441c01065850 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 727332023 1250 727330773 727330783
    0x2701060509041115460c0308160504121a1009060e0f0609041103070303030c030f1e020901030902060403050c12010c0806040b0315010e091207080d05040c0e090102030117 75
    0x80720489110b9282072020b48080c0110000100b035070610084501c0141d01c3e00d9201c0e03c04c0010042c1c2e1b444c40d501e2a154580100600000b0380441c076030285803d195000140c1203420707282034456200f42c001c8800d41504003400030071400000c11040b2900b180500c6803050008100006441c2c0d07000c010b218507039440c101080b2040c01205c00565070b030910408188180b0305580c0c5160020301411042810f0112040028284951a40100c002c40c1c2e0710450f105846405004540503042404030400c500301811018440c400300d0982c02c0c070700b950740c00525055960f000e54001045d00d90060300454035903440340713403c5656046ca10b94040c41042100314004400105000c0d4400c0c6105e140e03240c9045403603810520014001d500e009030f6241c01443d9505807000400e40042d40240503043c841990360814007101420412400c9840c2031a20003040004045040e10045402c44655240006080da039141810366540000d074105200c00d146000178001003450540103507044e00d252140308a9800c40c5600300c15510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 727333273 1250 727332023 727332037
    0xe01091406061b0708011103040303060503191211030409150e07090b0a09030b070c06060501050a090e0702030f070308090712240209030d20062701060509041115 71
    0x1140e82001030384030b41c09505020b0358580d0103400485940d2a2180003840c2501d07072041d0900c1403807e02000704400c1c140e05024440044c076040e409401010341c40301c100d0070300303414440024240041640407905c44038418100c000500c8451025240c4a948519140d0054030900c6c00110105080810101d84040d26644003405540540c0703e814400e4500800b0340c1c4141c01820b006810f21030300d070b000000840c58030036405204491035503502000003140d01e001d80460b0801d80042d4100a018044141583c0c0c12048503015190419059000c0c1d03614550101e00d11300c1f55001c01500c7c5840841c00000301904100d00038000c0800d20180c40c1d03030f070307480e400c031651003141840004d044020054081c902ca640c44a040007103149080706c1c050702c0c111002c004a441c0684c48081080042d2802c140d4845c82807060f4dc01c0f06070300540401400072800c0030000780768140e02d46003070712611006044007075104001c258400f400500c0e0140034519946014140080e11401404415001d8840d0940004010250008035103074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 727334523 1250 727333273 727333279
    0x80405160f09230a09110a060e040c03060612050907031b06080718030201031e060f0819021f0507150b01112b0c0c0323010e21070605010e01091406 65
    0x4995901c134001010306240b5070269091040d080c0c3c46d00d0a9262100c489005e0701064403025802001c007814002140c1c0c000e44004101450088188138a560103140000800307220000803c02c2d072204100c85007400c5895100400c03101d00d180300415950f503c0d032107500480d400c035111101c04e0741c2d86030790130b0300c2c00204a0360040c4020003280d0188010f40c0250300101c0d400c0361422030001010031400c1018105c50160300f109046941040b020001c10404001100b07900c0002048220a0005540030a20114007241050515000c809841044500c40e0082e11185508070340485881c0c0c0c10a803241008013a080d0302c0c035000a5607600b2003091008001507460044000c88240d42a05040703200c4100031003452030501003000420300742540811752048402c80a540518102c5408200001e248440c0c1c0100b411828076590600c0320b820080b100c00b16080c01c03020001955400711681340301d0851000d218100004100900d08000400d110080b00724481c10307241410340130020603ca14080c0e4408a201b00c0300198 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 727335773 1250 727334523 727334591
    0x19020123060607170c0a150f02070b0105150c03180a060203090a063c081810020a0c021804140a0c140402040b04080a0b060d050d080405160f09 63
    0x40010002d076043c00c00820f02419050502c40126605400e181d42c0d88015107171f9180075a80902c044c403082c89003040104664400f1441d1040c0c580e108034103001c0520a45200b011006c82006681d0414000c813603400e8400d009484e5941044403c1140c8410032000007402584450008103105000104460028900808000e9800c0c0303441000c4440841c4000709c03560880c40214007118914100290041c458032002c2c02c06140f200055008000b8440145110541340c106a400400d00001103400301d21126461000340c3e490090640070b460030346074540700a4201103c1d00b22041500c01551815020301c4c490210001e491030007000450703451201100c0a40540c03030300001042a04c4030066500b1146c4400f030320150030266a88106075854000d503005a00c10740180c943c10003081840e0b5042036108a007184c0003011f03085151106035455056101000038800740b00702007014090104485c01d025100010f841135804d880e03403440c100390000c03403040525184c00c03c403022041c641c0612115011020b5106411 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 727337023 1250 727335773 727335787
    0xc09030b1302010e060f030103050c04062105011d030a03050601141617030c0a1e0c30030c020f01020702010c020d2405010302030c09060a120206190201230606 70
    0x1070748850805049060000055207018191200030240c040204c005000a80ba0340c0356040440c20f014602204900c242d150100502641c8a000c40048290038284d500c140c6422407858145d00414507843d81c800100c10151700502c05410001c010aa032122503541402035844040065503000a1703084100c4420f9802d20041450060b402040910300e40200500812050b12444250013540242c2d400318a8010000301c500c40c03e0341015101c80040031511418420000c1401c0003080d082002c10f0003442c41d0071603800340b028954a4601a985540842140d956074002c5040c00b800400b6810b4400c3e001d4011030f9210380c00084103100752014540c043e151ba03696104194200300705041a60002c86260000c0710310b00d02020264000200103401303031900015254158010540740c12860500d41384180004001c014468540c050390701d04541c20b00c01c0072a1110800d01c00180180a1010b000c110100c1d007030140038281d98150402454403032000314444d110114401c1c8882c80d07820844004d07400180400c010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 727338129 1106 727337023 727337041
    0x30105010f050c060414011d0102092b0201030b030a06090b190507020d120b0d050604020a120302150a0609091104051e1302010207030803070309060c09030b 69
    0x350404455640c920340d03d0b04010401051411b01035414151100250031800d80000b40c2005c050040744e032100311600030b4005d0300250b8401c1402c510854400740c061b10200400420540b89107694004070b80055003c0c1001104968042c8110008607020170501d100e902050b900c55544072009080441c20b1541e40d0120b00c0089102a24000c248440a9000100101d109500d810714081c091100c503080c00c01007400c520801d40001400303141004001c0b02160031031085108854024220751502c001d070699112400009015038001400d50013200441c80c1c030a60304c00108440071800a80b034100740c00596004440031607160400140742c1000d8902802550b501084009a0b0007520503001e10351000d25402902000d9807040b41c001703d50540e44240505c602940e08813000030784d6270804520080040c540c003201501c6c290316100f100d440c80c0b80304107500c004407a00000e4001003900c2e44001 = true := by decide +kernel

theorem cover : BRFrame.Cov 727158273 727338129 := by
  have h0 := BRFrame.cov_init 727158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 727158273 ≤ n) (h2 : n < 727338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
