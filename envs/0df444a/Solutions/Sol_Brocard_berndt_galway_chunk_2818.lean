-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2818
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:49:45.967095+00:00
-- url     : https://prove2.me/submissions/235f882d-bb92-4898-9baa-c44e87c5a0f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 506654676 ≤ n < 506834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 506655926 1250 506654676 506654711
    0x504090b06160c050315091b0f03070909020a0509090d03050402030c0a080a0c0b03160c1b0e0106030e01060b0409050720030714010c02030708070c030f03120c02151801 74
    0x107200303582900c166074050200742010b101d45a10f006d0b40440000241c00c00c0c008440e80d03204504601c04002c140d8000002455035003491046100c400101201c0c0e20f03940390a1908001d1a04040492103130440300d0b00082d25081500b0454411aa0080a011009507203001540a030000500c1242d15002e5600031910660b0b400824201403c0154000d118054540c41d04030384004040d000303000c3c00074003071042045940886c140301d4807085031454007038100d11071807420400680381c090591712910745001c4045001c10103e4800c034126641d0759010700507030340c803481c070075089518500030075000110402c41406850419008550072a41074174002e07a00d540d170100c0f05024004d03c0c10403681d01d034100040c02820301c580300c3c0b02400090741c1c08008111504e404c2c0c038065602d00c91483c004044440203e401e405203c08190b60000031504110500212009480c0c000e0042080e5000020306070324140c00421003d100184106440e041e6081c0940c1a0300c40c14500c0c0881c0c030041c3c000d14032940d00c0f406515010400031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 506657176 1250 506655926 506655967
    0x1909060f060f0329030709020711190e01052709010c0e030316030f05040312050304140f070308090a030215070b01080f0607080c040e070c05010c02010c0504090b06 72
    0xe0418504a908040c001020551401d03403500400d410100e2924003101a000c40009136511032160b1410183c4210120341803580c00d070b000d00c011610108511040c0401c5440c006c1492808517010740403810061210f0210703540d940140d02480c9103c0d8014022800c000408406055658003d800c6089000307041e180b0002080b0342c4041240d4580302420810b507081040201692402c44c081c60030072800740d086480c2c1c543e202034040d08214000d000880300c58054411100516000000303d90f8805407808040c0090b07000b0b9500322141201142401c0c0e09007c040b800c0d0b045401401d01a1144078a1903c0c0c0c680c980c1c02180c692980450303105d01c00001651500079803842045103a5015841d20358500f0000e01d140c00580c00410181c000203603601800c04042a681da100c0802e00f81005107444080036030426000350781154444103291818050031903080340d205001d0500c20b5000340884941000100d0a03540b0240004020a03000c1c4400c2c84400140d0f080314501c010090036950401968080b94503039507204d07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 506658426 1250 506657176 506657189
    0x31209120e031b09150d0c030302060f0f0403230d0609090632040309031403190f0c020628051308030f09060d09050d030c1d0a05190906 60
    0x1520005825003018030100304805042081c030f4100310214408120701c0b50000f84250750101c509040b80b55580e0b00d1140c5440b600f500141071120f0030351645400f1759107020545403500080d04450000e001285008a07039071140d9032540e940000b03540700e44060320300c101d00001e101440b40e43c2800f40c0307010b00d40c007440746400804e21410081900700311404c00c10100c0700b41c4030711300c00581800c60707060302070f00341c1d41d201c00034010003200e0310488507a40c0341802c9030440c03420b8000030704810041c21582e801c403000001600f61480e5030404003142345011403040c3c5110a03011070000c04a101402880d002d0315016000e01891142150301a00703071030784a000c08080300c4003403452601003400441d0408840d1044c02003900a040b05000461400341c4e451040001c60050506540c0709070800202100c0e00d0b002500001c0c807480d0301c0b204644120b88141c5024010380492443d00002600c1c1352110b0350a04034000000c5c0200d40e024040701c00890a003820700104031800d000c90b4a00003c09200002c8503e018801c0c0001000e1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 506659676 1250 506658426 506658437
    0x3110f01092625090905030412060b0907030203060108090a05120c031b010204060f230c101a01110a0b04060c140406030f0b030303040314090310051009052203120912 73
    0xc50b44803c40354428182c1000c0c0d11140703030017002d43c0094000401ca0381178882100030f410404081303152080140c4195102c00b0340048161081c480520740540246000d06002d0303c500c545699411005503071503001d244082c205500034440703214003e80c81c3c0001c0007440c0015095078a0112005065440b004050f00c030340340580e500007030402210703a014400300c4417071802d0300c6c09805201400c04000386070381070b44060009440f000240700300030700d204004121150581c5507040c0225446450301e072805000244d502404100d443d4543e00328608045480000d40b41d0210941c10152559211200100781c07009000040c051450740310702e000d1208001400051146580c00b00c0c50f902e1800c5100241ea00c8988803d0080c0c1c400c0c814480020f400907030500c6107044203060ba03501c40c3c003c02c00292400c5021400010703141e1800041c000085210380601050740c003003010900a517200d82c4c860380200340c100403a02c09031140c003200110000303114041c0c1d4100c001c0401000304602403070f034460681c0042d016042c0b0001c0b84 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 506660926 1250 506659676 506659723
    0x905060c03060f04150303172a1908070e0409021c060b09090d0f0305010e060f03030f13080601080309030303070c050106180207110306060a090b0a170703110f010926 73
    0x5908c0814844452246181c1400c641000040c501507450070040f807540381d80b455050b4400b10500c89007a204110140c0d41200d03240000300501030a169001e8070114002804d401000c415414540a0705c1e8401d0750180c8215102040a40352183d400745507102100c5c0c050310395802403055519401c03114000d44640003d008a020035510181c00e540c0f03e101400c00f8182818010032a10f0261002180d10400c156500154841d04600013400e42c0708400c0d606215100204138440f800c600d1920000999212608455203070741c0310040b0319600e008078400d942d03156201300000760f41c2601ca0320805800f00c2c4940000700d400354981d5070403400351030300c80c00340601a503010402805001d02d0203948403030440154050022810035101050b050003080c040c0d2035800762160303040304164840720410001400400c004549480342000034a41360303d0a4403050310481c0d46c04811000d44c7c90b0003000701400907416152004810f180021403541c200c070040070340f889148514880b044c030440500c500e2091090aa10480c40b60 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 506662176 1250 506660926 506660933
    0x140a080406020f06150d05070b0a030603110411030612120f0703120501030b070c05070f08070305100b0603040f020d050109050f0114160e0d060f0b0f040905060c03060f041503 77
    0x2c1011094095141d02c002c05010217811000851501315000740ea0402c411101410030300c0c90101d00d03511042d113a220020381e4194040d4103600c9501640c1c03044c03004a024000110400c0103481d00c2d49900c068802c0f080012482c0b91414020301c4540e030198070305603a103e107088810356000340c20801d00c540d00841c2c00280c0e6010180e0200160050700b14200341000254150345032a05d80346030081809042c84982c4031101c09101080102800800d8649509015181c031a0000d0341c0300c0f02140b01c21211403150a586000224003409035038100700e0090001d605650340d540700d1283c00f80820b4004c1e07030855000300c0c401b004a08207009208003d0b015900415819850a00b500d0031038170a1081640b5290400080c0490001c40d0101900c010b4401d281080740c5070002c0380010007900140c5001001e140c40c0a0100310354155030303044203a40302c1c0101d0300c10500f10300d00800d000070b444c0004801000c0d50400c100294210b0710b034601a581012014011060908507403002c14105d0729924145c3d60b04810b021010000c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 506663426 1250 506662176 506662183
    0x101b11040e0d17070513180606080f04062a030515040b01050702040e0c090109050405060f01060219030315080703020901080c0a14030307081c0b03010c02031204140a08040602 77
    0x54441c00d0010884040c26250060901c20194004560014207101184604d07204009807849032065402c0c202c48036640d080e078524038220100c41403120706e0403c040040d00300c1c0030360900b81c4103a180600310f6003d9034503076840c08024003418665040020100c2c0711070316805e1454003040040003040c1c40009250402c244c6604c0d403044440c41081c8280d0038484c40c2280b81c0da000c02030f519a03513410780e000b04203485d50070205814172144110194000303d4100000038001c04941115014502a4061300c00366100e02442d03100da140240a82c2c005a4452091500c03070401d0901c561440030300a280001d803048250203040c11403445613110341030a0703201c96400d205600e482041c82d80101075140c020100d003046407010035541c00c041c0c41020050b5480300700e003d10948081c0100c403106513001101580c0e9200c2401401e4102086180310741d065846c0c04d001c070000d802e05100d0062400c3c01034004500384100b80e00400c0349110000e2044030030b48030158507030101a4040000c4a110340c0b0441016483c0c50030203070003d18 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 506664676 1250 506663426 506663441
    0x20a110309130513051f0e010917031b1803010e03070215070303180f06050603070b0316050c1606080c090907080402061204051605010c0809101b1104 66
    0xa00c0d00100030600050b40c0c0d0305a090118824044007152682d501482510641d540290290450141c0000304440800b2400c020300c500c49255020000001085610b03801c0f650380340c500508081030782a15140842e099005160b2000f001548441030b50b401a210403000d800c94101c5c0d002ca0403040c02420300b68502030254032396000340c071b00003141051900d40010703d0380785003503460808031000010b5840c145440303034015082e4103d4403400300c00480824034260054114a280a0720202e19000200b04a417a0100c0c4481c116100100713030a003540c850303140d2032948203102001d000512030208000c0120a40500c50740341801d5440c1c0c2c4040d001c41c03810314003405480c0000e100e1000d224003009212407a6032983c02507500800d03e881c03c00c9159035180f020456601c80c0d41564022480310701e04001c00c0000c00207022003050a01214400c806075540300640d0740c0341000314000e114100a101561940c00c1c0916420051042d81c640121129070881d0324203040e903a20107041d0b0f8501050381825441d810320340903410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 506665926 1250 506664676 506664707
    0x607090e0f0403210c230313032d0c020f0603090a3804050118171e0c071715040b130b0a0b0405070c0203030d0c0e06040b1b0102070314070c09050703020a 68
    0x24036500d0404400c034581c601f158002401c0c8010130005803007001c03440c8ac1c0009458080a2034000038038656070064003911618008a1094400542001490505074242c9001303103da84000c04200d0820740c0d1300044142d82c4a000306800341c903411030248004d52080101c16148407240c0d810140d040500f00f10b800d4507085091010200019202c89000407440c20251454803a0800015210078452038215540b601c00e49031420081c501007020340281c42d01154407022110400300e00c889000751004810b440f52080f05840621400c3c201c002004101d4402e942540400302000d440c040e47d0081d92102c90341d0100740e400702c102c1c130341d50a04208642030a00c00c81e43c009801d030410401401281d80007940d01d100360380c0140b08444d102d00310500d06902031094260405030040600352103603115004c150203900301d501030301102180130030307020010300c0184200c400040e05650740c41c90720001040380c03a4440e4420007044511110b11100003c0e0516503201c0c0310b0294509030350260ba030305046007009203c501c0d440e5041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 506667176 1250 506665926 506665997
    0x603070f05100507030905060d0c020609010605060d05040206040b1303110306040b071805042313020a05091806041109160905010e0105070f050607090e0f0403210c 72
    0x184401c0e62148440c40c2c01003010318085980d981186000c40e03095005500c49030300032201045005103003420b0f80007186200440c3c0d08070380403940da10416a003a00c01034804c10350070003410000d003424000300c0e40109611500141113a46880e82d01c40340c1d03080c903a01203481241c9071140401d09004000002079640c03290081140101554242616101d807041d50227081d0505100c3e21000d002101c10040501e00c00a010040c400c0000110700c1c0100c2e40400f0195491407040d002c02c100041d400480360441d0020240c02030000700040307082c00d040c0702000c000540964901514940c0103036011104002051103988602c01e80d4400142c0e00052101d10440a01181c0a03805903061048c10700b9800840311044900074a03100342466000c40040e20310340f041c40c002a0804a10425540501c140000ca6601904050356440d050b1643c603a070110f0070040aa42450b908103520003c203010034403500035510681c000000722213818096030840c1c03089441032143c07400850002e07109441d8a5040c000c40a888580e00b1806 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 506668426 1250 506667176 506667179
    0x30b19050907120b09090f0708030f0f03100e040f0212011a01030c090e04080c1c02190c080102072d0b0624030a02030118140406051803120603070f 65
    0x1e0348260005100300b0420080044000700d218a0350450240b8030302c007800000480c03e24102d8181c41e00504000280e03548941c08001441a100100701c884103d000015281400c03004034078000c25034405011200c2e0070130b00e00c20100f206100c1007500c0e8000d51084800327040c943c81910520031442040c504011032640740c03031926180c03c00c200820051006007441c0000b50811050320980c0c200401d5004802c1c0d0403501e104120400c8910340c010145402c00e02c040781c0903010108140c52404000c2c82c0d648005800c680c1344034001052410241107000c2c854000c8814403602c074100c0d81e003280c0215800352020302c160304c1100e050803030410043c1045440d074a0306143e241e9880c1c61780c0c905418064100c50003145001c0100c601e59034915441a9845850030342c041d500e00b00884800069007081c05040014001c405000009540078803840d0403100181c588904d01c1d0b0307101d407a801c00401c0024654584007141c0b0004088040c020700c0104400b184044000c00c542c01c1803824140f802001c2d03004092520030a200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 506669676 1250 506668426 506668429
    0xa0501110a080a050601020f01020c0f12040b0d0e030d0c030c1206120f050a0b04030c050c01030606080c16050d02070618050a12050c030105010605190f14160206030403030b1905 78
    0x1110342d8094603603c0089659100c24004074070385031002e074295002e54070104111047d03290200b094902510360300101e860f10002191041900d204074030400e8440b030b100300284504118250003c020032603502c402d031f03400c000f6000402d0003590202d007000b41c00659183c001c0c408103600701030f04d07400c00c0102007006c220490401050b0030602000800103440c607900d170300003c800c00c07004020641c0b406605c50300304901c41c1400c2c44e000c1c04211586400b01c4030341c090560142883e5100f0301c42e40b0115211665540125150070401d12603035441a0100c50140b03605003c03100110f0030403c0456002c1c0680d60081031400c0c0340c020002d00210360807072041540340c1c681104209655030001c00c8015240b206009611010861609d24a00400d01c44419015400c202c00011959000f03400b034403440b00340f42c403150802001c2c4039003210349980124001010403a41003000001e007111001904d0301c3c0d445503e910046003901c1e000144140c1040b2000c90000f61540d07441110381c1009000c00002118510303940c1031043c100310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 506670926 1250 506669676 506669687
    0xb0a0504120c0206070f060e070605030907051c021207090b1207090b06300619170a08190905060304110d0c0513240815270a0501110a 59
    0x340280304004070b01d00a501903683d01400c42d80999445810700d600d1052600e4240e001d40b030354031138130450b5004044000420b5402041142e1290a101c4050880d407424007041103100d10303051402d81c442c12201b40030500142c03903420410420081d5580240045807420000405407400840c149000d440e1403403c40c0d8040324001149800d45440a50116038441d00341c01080485c0110007514020341c901d8031030000e10070071110031034804020401030350a1543d00d1030140540294028a444420502c209082102003049080d40341d0600c500b505031201150301e030f128501203822921020b1508603400d0b424410103900725003200c009001c04c0e1006420351171301e612010305034001903c205d40120080c4c003003030040002181c01440600350081c801241c4003144400303607000346000310301d65054454401d41c0d050030a8000c00b062049501010081c40e4031245004032a180e103102801c10380440c41c0750107150350520100c40c0b01a21600403800146030b001300c82e0511a00351354402c1202804011f041180700822648030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 506672176 1250 506670926 506670953
    0xc030409020c0a020a0303030b04050705040b1b010b040c0201050f0106030510091a0907021006080c22020c0703030c1b060e011b05120d11040b070f1106040f030b0a0504 74
    0x40c030050b114100c10380e196080542c012402980003101c10004010103801d5400742d600301c181620208080c3e550201c0c1901d140c4a240038400c031845041c403010501030031074141c070459a900300d4008180112074502140a842c0d650b803c00c80035075106c408000d41b83e14a42000340c0101058582030110341015000040c24441c00d000d03150880d5100c02c103488a0112400072112040c00190206080d450300350300c025102c40141c80ca000c9014100380002035601000203242a007018014903030f2311010001284010710790003122000c00c0340c5400703110650442c9000d000c240002d40c040c4d140d140000d9035518000064080c009402c03c070705135055100340308241e40028031040480003030900b904030030000a42c0c204000715400000300140315041b440d941100401c4085c0980c2c0c11030550600c02c10101190160041c0514000e211070450180981d0700421081341e6000c5885005a0784440111040c00c08554168840d810040304400741c00d0041003040780403480a54455032040b410801070910350307101d03d40038010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 506673426 1250 506672176 506672189
    0xe091005090d080f0c130f05010e041416030b040f020c0d0207080601060c0302150901061409040f3e0109090c090302010818010614240904050406180506040203060c0c0304 75
    0x328400940c90142c04070446d0826910705004001c0c1c160798009042d00303407149014281c001006c100e001603282c10540a5100017440c080340740907070359640100721072444c160541101c1c109512440030700d00320b40b2148604448040398400250b035682d0104211840d00011441d000d0455018403010401c4043c045050b0381955050300c2d045e0149459424101d140080041c80300740091800d6082c8254410154000401c0354403120846050fa080b41c000c20040c0e180494019101d0020f031000740b00060200f500d1100301b51505420602d0030245a8110422051210441c1102d0301c0c80050040103503820120b500001c141c030010034020740e03007603440062a42070f8034840241445a8040412010041c460b80700ca0310040e03c2c00204906c40d5a4850240041580c0c2c01c1c070781c0a034014003800d502e201610000303403481d00d1151450505e00001a000e11000b0100100266105035440f03242c9004640c1d000750f10894140140020462410907004041c02c050003c0d000d50a003e1042180d0501d044011040e101116075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 506674676 1250 506673426 506673451
    0x10121508030a08010f0b092e02060136050901110a02010506010e04060b090f280e011e0605090109050a03031107060305090d03050414030307052115060706060e091005090d08 76
    0x2141c1a22015803044585090244a02c19232907120550f0b0000e07146048942407070301205454256000c03804a01c0e007440303542040700466101003984108981245400c41c030804000500314103030a24031071254024070300060050351290140031041d030b40f1400d0508928800c40b01004040c0c40c14071020300c24401c94a44c03038011004240d4a0096540b903201300140e02710031400c81c6000008014800044003043d008411424041c00004600103074445400100c058030003000800b07260030a4001c1e00c0300d4220b071001d24100880c0500c04916510740401c848001d512903140d0b0b0180061401441d0300f00f035510b40000007090702d002c04004003a000010364065150090400103220b0b269070510080754441000c0d8402244000000d01400e640d000004101d240c03c4603558420224402032402e44058095451a1040c00f10041400452800000610f409480744800040d2165551130308e1715100c2040350303644007980183e100020500010300545600c126284d01801d08045103890282034600081c0a0000095 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 506675926 1250 506674676 506674699
    0xf05030106081302090901020c1902030d1b0813090c02010902010f0c150525080601021203071707050a020111041d04050f0102030c030711060610121508030a08010f0b09 74
    0x243c084103443c00f64019040510520304004403d01079441321080d04a2803040e0501052004540c42506a090398000c0262035072014a0208030340d284480328a420000102001000c000f40c5500700604408201e940900441c1c1c0c84c000501003100d070481080429139040030f00c2c2d0740050ba03100807020010740c0542441c10010031f40d42402c0c800005000b0202102d01e00c4d2009001410b48900c00740b080e803d4928800756190f400f03d0400315403008081e0b0f015805030b80400e24009a80804402440e8001601e01c0c047c00d54441c40c01c0700052541041e43d82401190b030024403003160b65828020b031000700440308102868a0700d800309011140003541c1c0944240850803010404005044c0100d8190750400742c002c1d510b80c1040c00780141c0990082c0c400718045904000407035032110001ca0640e00c03484000304107108803030410000350f0760428806480c424031030352880114280b11a04076120040d000040086403034800345800503100d51300607000300103d43d42100040046031640c07011101c018600361129150382 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 506677176 1250 506675926 506675941
    0x15020a2402160803010f08070f0b0a0e09040b010e0a1512020a0b22050411091e180103060e062a040e0c0901080601031e0e03040806070f0e010f0503010608 68
    0x24040c2c01500040031006007150001d102481000d90b06981201c956410020b5998804641d00c50036403184044000071400100704068055000d00941c0009061020b40c240105002680681701110100d071202481302c0144260602290800d034000705080080240c04418086145030070100e00c2a064100d00b251417140440d2240c0c62100014024864116110000088041d04100c400c1e03c007074001d030000c28000900791505014000000382c9101c5218079040701c0205002c203a01c000c1e8214440100c001da080c00c03035a1034400804035440038405148202d5410b40c0f40050079600414502d25542e800070b01404200803545040c1a440e00003d06000002e2030f081d08406c0306d038080e651144c1d110b200c3c1003081140c10340c100c600034104060241d0761100d19646034001503040302c0024090050b085812041090804520386c044a0320f031001804032400d0581d981c00c0c551421b081240c100300001c00c26605290078940201106074002424200a1035100003040c008006010504c2190b08000380d400102d43c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 506678426 1250 506677176 506677181
    0x130212010207050129030d0c020d0507080d0c060b100801050d0606090c030207060e060c0301090c03060305030a0201020c07060905100503180703052a060405060307050c150115020a24 80
    0x480d4824028043c800c40b40307004030032400c0005c18000744001403d000b101a850045000c0e07c140d031641c1c81340030492119400b03000e034096401328201c0381c1d071290a401240c650000c0002c44003101d45961a050070244c9031601c8000c1d600401c0c07145008620000c40c1c14070580d040200c0c035054503010b650103040d980803401e002c4080c05a0340d200c1001ea9241c14001200349034507400610805010309001c1c40200d2685122a0351440100c507240384801043c40144800034554000b98003403861403a001c1491503e0f92112401c1d03a00030907591000d0703940058100020003041c800d4000a000604140c540185420085194826005250302c10030400100007544060711501c50310890203e0000c0f0b50f90143c4900d4615a9414206803c42c03041304035040800070f9045902c1c2c00200c680c000f078011030400c1e141400f40080c42c0c001034108010701c0000c4c8903604240c40d0401005031040c0340681c031260b095140c01011490061060038220464010508603004038020b102003a48109907400c460007101d1618044100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 506679676 1250 506678426 506678437
    0x120d091d1b130605210f220501050c03010905010509090a02060d0905061f0906141003060b0c03030708061e0907140705010608121e0f0d020406170a051302120102 71
    0x340400b1004000c500300383e0080c081d00c3d480f0305604408a20502c1d0085d088030081040354012a42201030780003580c0c2e50343c8400700d0a01c50ba1030303100086008031a80da4030360a40302c0c00c4035200b070350b000040010400754507140101d82c0100401e50300c0b2200f9042c84809561104200c200190203000006200307000042c1c5a44136006454001090711010b00700b21403d040100f40d01355a501514000c404040752500d40b901c030310300c1100c881d4001500b07044202d509000c14482104600018182e0b14440060015040d400600701120780c0343c06107540f03241c225009031401c9006021140205140025028185071070b070084001400100c0e038201c55565200012115030151080c1400c40d54400b0504008010301500600f00b55080941a2555040c0e25982411580100d460700340e0740804218902000310b2540f0700810105040118041c500700c01412034a003a1785c0958030006c0014090152103200300c950612950308285080070038806070420640c8030000c0840a1030103441441c0300030307016800c11070943c110381 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 506680926 1250 506679676 506679697
    0x515040c050d11030615010f030f0b1207033e49170f07050715030c0c080f09010e0306070c0b070201051e04050c120d091d1b 55
    0x2c840c840751409101003406150740d68003a00c206804110050060f01e000380541c0c0040c0d540480320011031800306d02401004100d1010a0f40e14802840b0300d03201d006103c3c004001d03500c02807035150f2561a151895060485240160304e1407a000070140702c0c0d401c0c00044003504002000e00507039a25000080b60030300c400f0780d40e89040c44238505080b0f20505500b031030861185017401c128007a4041c40006455111000710081c0300d4003440a107003000c100b1100140014102440400e402c02009540380c038a081040d4111984407658445666141359044c090050b6900c0c0d075143c548548180350380c40d20301070b0141d89400c2000e51030111303464500742d1260801c425400c000804807601414520740160030340810080542d1f00c00d80b42e50010310130b40c0c014010b1a0240000c1c4e41c0e4444c500d41102e054065008c4040c004440302d004500c001c18140d0345215007284103000e5140a4626150085e034040c10703100e00e80e4050500368101a2089031915000342c1c03410740c00407c0043c0340a000d456a0b15181d5035100303104449 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 506682176 1250 506680926 506680939
    0x140d06062003040e0a0207030207080a061a0f030a0201110c0613030507061103030601030903090801150512070b04031b08070b09011202030f04030e220917070515040c05 74
    0x4080d6400100646141080c0d9102075503041d80c01a032030740b41c1c4100d0003801c40102015000c41d0060700315a00814134079003e44140d0f644191580c2145081c16003034034042e40d000341c9a034002240c00880d5a404001614100c0d6501207015030036002c84e480e03649003007003e414440d820f002070303024034014088a8200903005000c5690b4861928003080c0814141c0010388440c070130408003064040c022060101d0041298008500f1582c4002c01100030301280c0748210100104043c000031000024040c1c00d04015120103841c00701410a028400c1d880c0815000d2800d030780c04a1420004440514119000d40350403034111031601840761041e2007000d03001d0b485640148a05400080c410007c0c034042d00340081c09998103042102c844103140300b6400b066030700e005003c0040010400180c0105040c0c8111403001d00108074000000c0741d5607c1c01041100100d040355214441d61081002c56100842a00c0c180c18600b414550309444181d516006540f1461044058501180a104100700440300500005004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 506683426 1250 506682176 506682179
    0x9190f09050313090c080c130b030f150321130506120a060f0e0708040201030f050a150b030f010501050d1407170a0504051c0c1b03021e060a140d06 65
    0x495490303011004214843c0c000b6140420015a240110601d60981d82d64140035612424958491548101c01081c0110100600000e0500d03811003d9032041e070004c00203842d00c1c81c09001c0000f0b40220b1680c0c0922a800c42c050316100e48031115044200c20b030900550b161030b2004040e00801c01c981e281c0000d98002008101c407810144e00c81403503031041b08010703c28811591b8500c000c403242c400d10b008180b140f101090010302010b10550050b5071050052401089903541c40701c84074211001036804407401d94503000c0600a80c0b801078100d5000b48210394082d45145000c50000038100707018000c050400400207440780c809042600300400d04109100c3c46041c6082600f4080c0c05040c0401c100800903254600041c180e149a1080e076125a0b0081c0c09040541c1080c407051134020b000340f240209000c402c007480b4011601c1c500544440340c29211003102c2040c210700401540d04000003200038841101c001d10011500c1d00030640d04c56a60604001004031041102e00c0359a000c0e01c00c50a4000740b42400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 506684676 1250 506683426 506683433
    0x5011e03140406091e050a02010507030e0a0b0306210d1107090f0212130b06010302031e010b091f0e010c06110c0c010e03030406023a0c0213060509190f09 68
    0x4000c504500c05c2c1401510419034040f170354203460607003a015001c0e80001114001550142004000283c4603207400c280d00001040026031900494100840400020007040001c0c00d01c82d032210b4103101844843c2420011040e8207541d600c001d114100100402c00114440021003000450080c100a040030312840c40e00e440d003200250080901103000c0110640419125104042454806a0015051a11540d8040064019510141103034117444401032145502c203000029050181c0428102c031a594040700703017007010b840c00130110190140743c00e445045000d50002c4607000208028202121011100e09050b0010840940740700e80d01d8800180f000c031440c03004103240c40020005d8840303c031142000414596640154058030000da0721030a59401404039001d016140e19a000c2074010b800f03640b9150706031400c510000010045406084000211b142403102440c4280300600d0400065141000081151101510511014040702d81d400d01000c055044440700141c401d40512202740180b0b03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 506685926 1250 506684676 506684681
    0xc050a12060b0d240b010e0102060a1a0319110906030d0f0c32070810020d0e0d02030a08060301090c0501030c0908160602210f13211b05011e03140406 66
    0x10103400162170080b441645601420607110080301c10380c000d02c0203603905410000140755620301c2e06041404016100441e0341c0400416039404405008040c02880e5413034030781000f5001c000340d14810702208082186a07200021455180001d52400000380c414002040c0d4106001103000740003aa04001c07500e40c2c0445c14441c00d81c3c00002e641c1d4005150701011aa0342e20b5000c0b6001e51070150700712004042030418980c01038508138007803100010700c030050a0440c81c6041982c0020b1805a0004241c0d0040550000905607110100790300038400c07841c0580d103200200440303008040c141580d5032a01540d03d4801e4078a100509039841c21148144840c000c002c1c414030551107403100510640404208215110140042030920740c4285420503411140711590364110b07504182038481481030014801d0508103000080390100c1341d07017401c42942410583e0382039943e007501100c00c007046141009030ba41d000501150902c008100351441148004048018041040c3c0b412011803015050100340101d13607 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 506687176 1250 506685926 506685983
    0x5041a0703080708040c140303121807060c0b04031b0f0b160306150507050307050304141309021806030f0a1109090a0c12030e120a0c050a12060b0d 65
    0x82e1a507603a41d81e20794200b2104954201e500900c2010064400c008540f415010300c090800000c1c181d0f4101103010031180300880741202e0044c20080784222484840308144013540203090b080c03400c045050081c2c0c5400d1f231080e001400040070400e02c80d0b4183c1418608210241c42d040d482450b40c007140300541400141c803e415103860207440440c0c0018003c2c41c0c000e2003400304032400452419882c0c041c801081d5280e40181405855501082050400250042c070040010b020022504003069070350b00e087c856600c0940700890401880c120100e005651590200140c0080c0107106481a0f40c6040c0400d0a000c000440103240c1e05c24010b815041004040c005002c8a0056030205225070724070b042c071984c83c590b01c80054075501109100307020203259000c401022901905040126942c4800859136110802484899980060704403404003e01c031820b610045c61700300e900c90805811704440d40c0e03441035080d1008103503d503203010001c4c10380c03200c50b44640880d0700140c0c03a03e409e15800c2c800342d4016902c1e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 506688426 1250 506687176 506687183
    0x5010902040c2d0201110705011a2b0804050301140f090c130504061d060402030f0d0e04230103081c020403150c14041d0105040203091c05041a07 64
    0xd0038414050288211100c0a10302040c100c0000110b00f518028441255241111002c5540755240381c1100c0e41e03400028820385200b0000000c0c4110303e420b070304020b0079441d92240c0c407903004103015070425910020741c1c514402600d04c4072800110306240441d914804c0b9409540c040d402d250082074291064034190b44180000407181909903240f94165486000407280c00385d002c00003071081c6800203148d03400641d01902c103440010b00303a0081c5060010140700c1296100581d4005010002141400d00111812171001002031108644010004e0010760040204502596584030541400300311007542c80c60f500210181503001d540c59046c014001e49c482c000c2c1e101c410208402150304a82d03503100f11030449030403120341e54034200720f440702e140070701035844000c4104075500c4da80010a8101c00300905c01002c00503112090051591342d1004d16000503488240704901c18010020010750106110000308030440c0c034275041e0300b020a000d0f90700b030045400c1300e03410080c0d00c920740d220f8901450050215500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 506689676 1250 506688426 506688431
    0x6030a050f101d210c1509010b01020c090c070303091a01051509010219020d020312090109060c260d050c04031106090a170304080303040605040c080a0c300501090204 73
    0x700003880c6a91032603c140722562584451407003040c1101c0c03618031100e400d440c042c2052400341440002460b110000f84c803040030700d019400340b14202d0003d20418901c2c00003800504980c03040e52002606100b8003c2400240d0400081d0703520406200e580405005c680c88100c20002e1000b032100d010360b442090240f680904401001700003610038074800e490521005a000700999452110418a10b4100c1d83d070898014090f2400400140ea003030084040701d0301d01003141030f21403a04100041c00110140d01480c1400304080e0190042250340e8086610002d0004a900050000400103d42071041c20b044400c40c030325003c18003200346491001481168081e62906011500c2c0604102c0c95114075664681d100320113140801c03258900a0001246001d4081940c9c11b042d5201c001c18150350045a08030360403503443c010031040250010414020b00301c954001c10005000d0380e61011101294002e0b2210103440c03d40c60b0424800c90341180c0c506201c40004000c1411040c5031846c00b03050711500481c4500d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 506690926 1250 506689676 506689691
    0x1104270311070e06010f0e091612060803090d0c0f080312070f020c01110708030a0c02210604030c060b0a0605360409020301020d060806090f1204050906030a050f10 72
    0x89000a092060f59440012003207552180ca0041d0b4078004001070050038803940c4a4440003c0e554a0207043c481d03500c0b01d2003506860146000149640d4218040d29034140c949001840140d03400010707140b14000a03901c500c00d82200c0d00301f41001403103941c05124107184c3d2000c04503031400040060402104030740d05690807a01c0310f201c255125140c0a90543c0141e1041060400ea50300c0f941d811100100032100383e95140d6141d240f20f500b950710000074500403903c091507903030450610381a034504400c100c5a446d52070200790341806480f454060000340401c0302c01e40212050150b294891032094038000d000984076940c0307400142c4517400240c481c0745000000f1f8240e82d17412290301c00d44890313610149004403d002c400005c010081001d080c00f603805650a010000c02013005100300c0d8040d020b0304004004e01e2900c200e80070b18009812041e010580c00031292500c90b0070b1080d055406440088810702d181e07550751400300b4a0001001c0025000b446010082801e980020443c04075400c2641d00034040e44 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 506692176 1250 506690926 506690957
    0x801050a0902181003060c021b09010f03081b071d060102010504020a0501050d0f02042702090f131404060b120a0f1719030507090905060d11042703 65
    0x12910580007070341241c2186158006a000742e510a82e0000c46030f40140d0b2480e445c0d8554a040714810094040540d02c2100680007140030000c4000f1103100880d4040712960500d20701408280007444010300c454130220360306804100440410030b80300b40c103008a40d2a02d41d80c510440721243c0a0082d000303008c4661010501551040c01030a00c40c0d60003400f0b921000e8a003800440340d0382d01050000039981d40e2041c8660605140d40000d000404d00164100c601da040451034004069000300451246841040b0340403541c1c541745075070f059441d0100d8980030b03850b1412041c0005003400780d042240302c0c081e541c104002c0042c4c60f4021121349e041541e49136401840100d8196072240b00c05009004d6000340c6620f0300004800c01c8000b0403681c240100380e41449100c50b555020b030840c01c030714100071a803a00104885668400c2c01200104050320042c8514107040e408a030f0b0034960542e01909520440703081800b0703610749070050b0b4040d0207104800f806805150390303443c030000802007048001860070307811030794207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 506693426 1250 506692176 506692181
    0x40b0f030117030c071701090606170607081003021e100315061403130c030203030a02030424051b0106050604090b120102070c1401120f0f060b0a0210110702030111040801050a 77
    0x10304c2c008030010600786090a01c1140d18507295402c004c040e42d00c84110f0400203200d401303128018000e0502100c400f40c0c00011039070070315000801600400c5110300400c00020424030300d050880740c050340c1002c11600004984859662445c80c029081520090559040c603850380c811003080c1d102482c0240b480c2c0c3c0b10f110448040c003008a000e081e5100a01c007107602c118000422006c0144280c00780710100b65a540824110b03040385088c100583c0000c07408000410440e881452a04424152404020035180000d0158000c2041c402d80c1040940c0300f03d00030040c2503020701c0140800800c0c2c60b8071142d4610098018100c81030304280207000c1c80c404c50170f4144050095614213640210003225880c01c0483e002d01c0d2140303040c491410840c05143d038000400e0340d4402c08a485640c14000300303040400980c1030042d103020742e100000d0008100f090481e0a50301240f51000c0140b03102001ca40402c1c100c0900d0868090804040d5040d440c0038245e03070404000034003e00c121a0403e0080c84281ea0325010701c401c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 506694676 1250 506693426 506693437
    0x30905040612030e060702041e060801060f06031a0913060b03060c070f050703080703031b11071509150504031a0c04050607140d1d060f0409050c040b0f03011703 71
    0x101e82d16042801000a4043c1e01454180381c4007030b1415041c064260001029a0b9000140c07178040c04180301109440d0203907024032005012400e000f807001c0761401c210151060400d00c620000c141d910344002000109225102d0a4400c0003403007510a400c1c1010103c2d03a003030f400300089400740e10302000d80c0f0650602081c5c0500c0f0b400c40340000c80c18262280c95008030503e9002c0d040b200c0c1d000d2060003000250104010b4100e01e402607400007014050702107040660403480d40200300740140a00c145440100001c0c41d80240c812603c40c0c9017802540c07184c251040c07607494100c610070440080c11840c1e40e41d8090040e0003124000c0d000644280c241f0a0301a046200a60b400e40c46500200710070300c82810910010880c0b03a22449404441c146180d54a43c10f2241024141c00002c4886001144023245440b000c07074207410850701a89403200801c5613400521880c840ea10800c0d840300005110001c6030000d480040c10791200346551b0341908c48036aa52a8802d00500079809c003210381400590b10000309a51 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 506695926 1250 506694676 506694689
    0x705060301030303090503070501090c1a121512070b12010512211b060a0f1413050a0804180612081602060c010c020a05010c08090604030503040524040309050406 71
    0x9203540d00750380303045000c0c0ca0007600940356480204000000244240300c1c406a40f0b0003540481c0190b070400160a4999440014810040106005808103650703070400407a040040544c044215442280109003100b4000c1d00c0000300f8025018002460000c82c0c0c0285403603122080e12003403a030707214001c00482e4075402000407150340c48080f40712031a18564450700a4005400180350030002103281c455241ea10900030910300740c1140c0207110b0504260702030410725160300d000501c1050000c0f010101d034442c0007030140d91000b024007020400d0050034403518000c1d81e0030900715580c598841d064081d490010110304610b0515182000400141120005d40300d29404492249000011900c00000030003c0c58288d902000070007020003008401d2040c140403c0c69034019000b290107504150b030840700c010350002d0501002c001004039611000c59880d5001c0e502d0300380503840e80c84070b003041850110039140316030a00580310308001d4030301d480110461259109585000c0c54035111414801680d200b485042d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 506697176 1250 506695926 506695939
    0x305010e010303050304030311031905010614180a0503030307050703110303132012010b0102120906093a1b060219020102150a140901110d4a0705 64
    0x10302c0000c0c82100199081800380c9000710340380c98180040d117455030081e1039140f42092081200204207007d802414011f20701410808c030040700d100c601c28140c0c0329482004001ca50160101001d0b595a40501c002420001d01107a4030707450704031006400b80e8170802c4190003080d400c4015003118000002102d202e4019900c1c3c030103452919a548544418907040400e8011803c1d40c4101d6058498000382032038400e1010003c83c070042440006405c01900403050500080b0406ca60040c0361070300807c031031460505440003121000c004848002d400101da2800022514440400c01201c01c000450289039019010801001d00001104003014105100f020b0250b0400c2a10103880410754810710021801801640e81c0c01040c021801e40c1050126a005009980c1e07080040400d111040030640c040c8000c0000c00a14a000c18020440d000741c12240109039100d400c000600c12a00f80711002d0b4507500318020f010039260150410a80c4c5070226404201c042c02200c4440800001401d5005c9a0016210 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 506698426 1250 506697176 506697179
    0x5070b0c0304030c030f11060907090b0603060f10090f1d0c070f0209090a02040504150c09060801050402090a050409050c04050c04030b06130905030c0a0201180302011209050c030f010e0601060305010e01 89
    0x41c2d0300d600c01b980c1c0b00010b0001228080301c41d14014003509100d00c45060280114500b00600c01007220550304c2801e020b2402882000320684500d00c02c7d504403081200c402d0380b03580c900c1c001100c01c01c441d500300d4040c1802600307000a0700c0001030000c0720a00741460001c44559a030140b407244074010341c5005880301680152440240c10304010303180c0c21015042c00d5550a21250b000304095804c01d0f5421a6485001003a02c00c0c80104c0313104a00e880e2030549031442115180c400c00404030081070050314440c5a001900c01231503600c0580880007040c0c041c2042c44040341e07509005840d81810700e4200e0199091400090155500030102c40580e540700d01e188044c6e8a5900600040302880e1402810740c40ea50705000011440401c06003c40000110050100211900c00144184a0084000000d0000e1041400180c0e000580d880380c43c04000000203104800741080d0380b030500f40480c2c0c1c5403d4090b0700e006401403001034214134100c0000004417083c990f83c2d24411002c440007486581c0400c5e83c0b0000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 506699676 1250 506698426 506698433
    0x3060b010e0d033e0312090f0d120b040c230c03070b0903072a0806010b040902030907031e1e050606011b06150302040f1a01120608060705070b0c0304030c 68
    0x4c03421441a00c107040e2000142c50140355031030400140100e1250b40d8408034960140c0c0300034050266205a550029000009017085215074a90308181481c0500401008903038280d80154449003a03464014404e101c03020941802030110890000d81c482c580c1501901c01c02c0c02007030981101d070035404490003185001c055444106500b07002900e0b2418900007040444042911789110401070b20300c1011030070b4030081c403140c42040208694800d03040e9070008401040706d1012841030310212600f8110250750382e40c841e84070703d0518159030801800040c20f80561422184040040c2486910845607800c5010700c400c81e0b14283c03004060002c040341e000000168480d442494810341050012200011244071591044240c0f4800301e00c2562003144003d040082d442d25001d80301c40c0f240429010010901540064002d4029271a64641800140f400d20202c461a070f40c080c3d00202040800c2d5041ca080c0210300030031a0f40581e406991b0f9401d0388000c5501d00c00460100d901959054a54406200c1c3c0c0e6139 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 506700926 1250 506699676 506699717
    0xc1116061809020c2802091305030d0c211a0d0f06060e04150513081e0309031306090b090103111209060402030f0714060c0309030703060b010e0d03 65
    0x102030184031140c1c40c0c000620002038006040c00400900181803500c00c101404101c5841a02803a034040c2c540034510700c00750300d0303403c3e4003500640041d85100d4000100e040052462040d0500c0c0400d807490803e40c00e11282d44400c07081d010011b50030340c3c4041c1c240541c1070070007510440c0e940c070052030142212041c0b5504d1310400100c4900d00c100c2d19812141441d0300e903041143c0560b44078080f01d081090030801007111040c4804d0b09549200001c20640c10b20100190300580c06240c01019000b0010328100d16040003c90483d131101100c40007a0b40e41380c10700748151a41c12140c00640108120b41000c00c03814058021041501d041e540502d0802c00808011030180012545d1018418003c000550584219141c0c0522603009400101101d04051060500d000b0750040c4500d4a81c0000c4010b0045100361000500b0603081141c0750340d140c00d10108050f086114032003080c1c0d454402c0760000801c205090700500300461098991141444850092000101c510240100080c800c02c503001060502e06 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 506702176 1250 506700926 506700947
    0x1211100207060935010e0c120c010f0315120203070902040e070c02010c06090609020a150e0d0804080f0a060e070b0f07060f1508011802030c010f020f030304060c111606 74
    0x804d042240c611100c54008000a0700ca4264103681d44030b8244103852901008002d41440c010f9030350745090b680c116807240d15000d03900390041c100300b80d0520384514640304ea089044242c42840400410940e80c43e54811a0003209404078000d000d112000100140184240c4003283c5594402c4082075880d5607040b1250752000c4400c038107005030341c3c09150106105102304620380d8401c1e0030020741c1e0141f500408c010150079910240308a00e50041c010307540d41e40302140d440084030980e0350358420101c83c036040485000d66001040e4500c25101e0038110000d00141900d00c05008002c20001902002d69483d11100030780228510600100300017240b01101c8401803000034040c03880002c071155400c0340f08094690702c10514294585150060065140c20302c10346910100d60401f91051010580c0401d0305c40004000381c41c1481900141005901e00920050310703400b02c0c02c800e5a80e030340352524104c00141110041c0c000000d0881d804148044030000344c030b6002c808545486542c10745030600403113029220 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 506703426 1250 506702176 506702219
    0x30a05030403270b03060111010b130c032a080c1201060804031709010f060807031208190c020d080601230d0b19080606090c040b030601050412111002070609 69
    0x20046401c0310401a200f240c00f61503440b100640c0c81c18031780001481607141c1c901015069252841511496443e604a910207956205005c11008040b80c0c1c1039008001d070f02c021503404820030702441c1501642600903503101034261500205034860801500150040210a480c251226801402024090010590b00520034a821030014200341c00080350120305583c0c00103681e444a0300925140c0d040d000d500060139810004180d094a5501c5101ca440e4010041d0020b00403160702040e4a00c04255500b0190f1201580c2846200c80005000350396503400c1d000500040c102c600400d2556100d43d01e0018164800c0072183c103440350750b013401e070710a034001d5a818405954a0a4407010b549070500e400014444448050a0184c9003040050034440c004100500ca10920303030401031000000002d56042d0382d8020003060312565010010b03100d521698100a944d2103550800f0010008845404110796105a441c014841d106200581e0b03122200c0c014600815041c400c180803ca028803030845c0308158 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 506704676 1250 506703426 506703467
    0x52e14061603031401080d051801031d030304170a021b0307091e0c11070b09030a0f080c0d09060c20090103050d090e0c27060301080307020a08030a05030403 69
    0x800c21034500c0a0141c049048022a8031001070007100441018a6401401c10740080c1a80080c0044020030078411483e140f0707a00300d088030340750446900c25072108281208400311a01910400140308c3c1d9283c208a0b0f01300c68001140c05610702820581c0240d444c0103c1c1500200740301c096000c580112002c1881d80903070581320300c4c0d0300055520850300407940301c00392410000d13240c14000c00d45101a504110104414080300c0350390881664000501d1408660845116a4403034494000181c18100401005001070302005d40030410700c00b0010092088021110072140000c10100003901c000f10244a83e00c0451300c0c03500840c1c0811030750744035503010101414084030030402090015501003803e03042a00c26030301c461540070702c09420a6109020303207510450348400345018880307003d06101c0d80600c084840000205280c820b081500d2202619600030210b680380d607150b007680350b901e800c0004140d100e44116880012030317103404130071114a60701642d034040c03840e50390b40c0303090321202c10042c1000c08642 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 506705926 1250 506704676 506704687
    0xb0321070201170703060302130b030a08030417030703050a14160e1f110f060c040302100e0409050c2b02040b0d05060703050a0b030c370801052e1406 66
    0x90f11074488900c10801034074006291030550040c44511400e4074400034031180751410743c10160791f00042e0308002640c0000280c2e40c0e517660f403900040c010001c8003d01c07201c0c4008000d00ca9110780680082d03114801c40b000c01c2143d402d0380004502c441806071250000a07000034041c0640500c15a0020315029004d441c400315649015400705c20651020070900009140b206016848201440021803825140006007011705080000316214456032100920410703070800107115540c01500000740d0b04000500c10000e89615040c01522241019143c0c4d01ca80c1001020100e281c2c080315001120071442040741d40c0c6400c10340d00340002800d02615580d8480981e010000025104120091164400b5030b004280340c1400c8504e00b0a0f26040c41d590351113034104a074000f560740c9421301180d0000182c81c0c100505071000c60a46519013015484c460701069000c10049941c0c04150001c42c002c01d10b526003040031041420580c190507a00000d4002c103042140c0741000050030b40c0040d04000c1000030004d52508 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 506707176 1250 506705926 506705957
    0x80106080903040b0c0d0e09041518020316050109091a1306031e060c0804050c0d031407060501030c0602030c1e010b0a080a03020606060a05070b04050705030618010b0321070201 78
    0xa40083d070840400c6e6000d5a91101101c1c1d0100446407000b20a03511aa81802c0a940700200c50401d007981d541c8482e40d4410310517410340100d80c0300040580190580704032443c0107003014103200d414001c041c081108060300050100c12032184010071183c3e40c506961240720740701008864a020308020070b4054850002102041f4040b001800100d01d140901851054501c2c104040c1c0300a6900c0c24203200c45001003001090b0049070342054014115480c1c19500341c2843c1c20b88142d000c00f00d0044680da03000c100c2408004180d0f10460680340504003664400d5501d2604076680c2c800e01031403080507081041000c808640d082c2d070b09009121440d00205110100b800820b4031a22076a004141551180c080201415010b004881e0030441c04c0c1d80301840c00600740702c00750180c0701d0801d00a10440c0018001414040148003040c0a01001015620b040c01c10040d405808141d121400106501e002c11100c5145000a100349114150340c1042c41003d11244d0035282c56000b603c41a814001c8004291411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 506708426 1250 506707176 506707199
    0x606070804080609070602070b0a08090a1502090f040903090b1c09030e0f010e0603060d030201091202010501170d2f0a080c0c04110409050c0c0106030501051801090308010608090304 80
    0xa0800540244100e213041d200c12441e0141d264460b00964001085c1402090004011100840418240115191141c407c1c4900d440070050000e406201c1402c01d900c018101c0f600208160130301290062441950241000125000004001d0220f480408200071911024000d03104a5a10544107000704000b9802d820036188600c40c12800a030000e031901c070795841c0109401d0b840d20301c00e01c0c01d500180207000c00300f2424440941054031440341020381c8001c0502c00d400c000a0103621a480c01c040500c0304001074042c0000303018020041e4011003c0d1000500006001c06030f10303000c2d5907180b0440030040545d5079200f035800901e840c15681c0310300391120740c4010005250483e219011159036a40c41d506440c0c109240603040340e1260341440c2411400e0804003003640d0650f400c4078000949615009034201252241c00c400041035402c0802c004140401940304601c188008494645144403106409088030a5070b03800401240c95500140080e07031158050b6a401560f1204a078541034485682011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 506709676 1250 506708426 506708429
    0x40e0a05101706070801060e0f0103150317070b0106141204061107050d141c050a15030b040308010509240102030c100e01060b0408070b130504051e0c210606070804 72
    0x40b5980030300148802980d120030100c0c0100210710384035007045d8450001900300d0101030b04403810161034825000410b4054119900116484002e00160075001c40350b40c052070700290030507501c1d03c003241c0000941500908400c056002d2141100740b900010451403030301614003510507100b80d039a51260303000700e844000040440034007030030003440706a580314002400c0d04035113110307aa041841804017080303030070920303001c0c404c180e000c070401140710740d10006100004c016600303005200c0a001100002030160000d81c0314010380c040d1b556000c15a895005100004805032040b0140e00c01002008010000360415600c05034814415030f45405840d84042d40f80c19000e0f041b07000783e591786156000c0455424800c800c020301000483c0f0b8100340c9880e1a40e17485890703d2003002090305000647d211303038844018201004e4030005004200a09111842c00c0b1503503100c80c1c0801046030034102161400312004c00f41c2e80d00340b540a01c582164502c2052220350000082e1525030402803e001007070019808002420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 506710926 1250 506709676 506709719
    0x120606131e0c0527010f0809030f1b0601052b02010908010237020a20030102040e07030f090213110708161e0804062607020120040e0a0510 61
    0x1038841684000130380511110b00d091941c4242c00f580d1601650340c211502c3c41c0da0315000d0824200d00e584908030141580f00f402c180c6010900002146032080d018903a09000300d070011030894404d6a00c1e1130601c803a042c2c10080fa0030701035a1904035000c9400311440c50f510100e02c18501a026030b03594003506c60a80e0002da14400b084450b1085c076215420300c420801e115401541580d45100c41d44210203034039074852900c0a4441d840b8510b59100078003187c0c9540c2007200c8040c0003199201e564a59404c82e9500175102e1500090070040d070440d0040d05405403c3c00350b0740003008107040300c1c0c548008900030025000102c21902042c0100400700c2e408a002c0d186502e000319000a02e40803a16201c403240704c0d6249208a40c10200c01c00c82c02003526802902e0996103207090040c0c00341003200000c0403040303403a00440b1040304050200720b5100d40c190046c4200d01070b50303001d8509128810340c210f070180c080d80c042d038201010300c0d80002d080c618150304529008110014807500c0ca9403175084421403811301d5003c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 506712176 1250 506710926 506710937
    0x3a180c0e090f030f0306280303080a0501060216090c0306031b17060f0103020f060702130b100c050a020d08070c0807150914010818070602060402120606131e0c 70
    0x480c004030140064607200b510500a036240c4080003d080459000c003606050148070410b8125619005540d494071031a1009040700c0a05582d0b4034005001660803517500a5141c104000041c10303900000b0f524040c20800341165640c80d08182c4014028001c01440e001010b403902c90010201d40e04034051142680c800014620460405040c8048480c4071f4079010150780c00901000106554200aa41560790440f40b51249031811030001f0014000c0c0382019610540590840b22840000e900c500401c80c42030b500d110b00d0b18a060020340b0380030522400030703010750426180000140b409189425416105142c00386c105036003031b00c401e04940d0140e04884850741c2f010006002410722a17541096000042c901403a05508000100d2014900c150400d03040c8175455010951711250705684000d1030881f4401c80d5145030340d86d04003e50b100021b450980c0119805440041005000302d0000d01c2408094000815503859220244c01094000440034140149551150400174107004d0490300c4003241c0d489 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 506713426 1250 506712176 506712181
    0x403031d03031213020a171e030319110f04150206060402030c0f1c1803090f0807181808040504050f07090b13030f083a180c0e 56
    0x115104003100c4002507219034001d2020f80c3d4000c189120b6640e12030074008500703040360407130b202103031488820780c04c494162480c55415142603c0d0014043c48076121840840303c1030101c4140668680c40251050200454111580760811b81c003500302024030012062503038030b04414944c4002007908540c2000a41240720041e00f00c03002c4e410000301e0b4001104460440c51402e056000100c0340c4540d6a600710107041c04203581000032007a11007440b80d98000e403030a20200c0d540d101149010501c906044011422110000c00d0300f8561406e01c0b8241d503258402400040e051000024403205100354078844076481d0f1b403104400034900340500303410b64480e041e2643c4a6082400b00800d4500082c0100c841301805820420300c10b80c040716031000c5800c3c8400380d5a0f40c0b8000d50103c8910781e200c0d0400f40018011580040802401c0303001410305071941c0d040001943d4046011842984142007028604009079800e4400140d075507000248099118030900610300c10b0340e45140c0070f0b40b00e03644007007c4030101008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 506714676 1250 506713426 506713457
    0xa0b040b070c21110d02090c04090606141e0706020c1c03020703121e05090706030c05040e070e0a090c0206090c060405060d15030f06020711041815060b040303 70
    0x900d070003c0c02d0302094014210703140302020b42c0032003010b010284c002c140301007402c03180751100c0400780c002d40d4000d000d071b5815103000a00f0564690040c42120072040c540400062018410600700c110000068545460143c2e034052441c80e840400418401c021010031000d0001a042d10061007036004440c050000e41200c011842d90304603484002805142c01086103500090740080450300b00780d4841e000190390042818803000c48801e000c00e10190320f1a06040c1f2440d02c0c00022410100c2d66243d4041c80081200902121207001d1071086011180e804000301e107280303010f40000540d040026003e008150703502c00c0400d06888203a030918025800450030301c03517071250034443c1c07079a101415105280b4161604001c54158492481c4081c122a5a140140c40c52081c40001c10021600702c00c0c890080e00c41b60404c074000354401c000484040c5041c400c180401d0405008050b002a10140d8ac41c140e40c810b626150201e1480301c810f02041a83c1343c001042600c5030350043c1000d180030b41d0303d145802d042d000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 506715926 1250 506714676 506714693
    0xf01090203060c03010605031b04080d051c06080d39120207180506030a0609080319150e0403030e190203150115050f0405061209150615090a0b040b07 66
    0x40464825510400061100307d401c602125007148801101481549480b03d4041050040c4c0d00401954000c04681414650b40f000241241001090695500020b140041012038500b4414421143c00c1120341500c0c2c0384c00383c8070300040c0e400042c0c802317500ba1100c24050390f0700b1220101d000c8610381030b1000d1301d41030000305061210102102d00080a107907003401e401a80c5107410481034940192150300041c4582c400340140f02c119540003909010411003032070448002c0e0000c485070b1001000c6040000d40c0c0a041e406114951803031203000305811810941442c5083c040144158181030725030020f501c5240e01005513560b070340c81e050315012003001070340304150800300b100399801c158a10741801441070241c07090604814901030300309281c0e11032106402d43c80d24040c550140768003650100d82013440118440d89207205c0c0081209482d000822521824450501600c01a401c40441c002516250240300014040140c000f062035a10300c3d9919108181540240c000707900f000000300f0007804000f41003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 506717176 1250 506715926 506715931
    0x9180106080a05150f0d02040f0b030d140d0911100e0f090907120c0b0301260a110105090a27051003151a040906090507050d03140f0c0f0109020306 65
    0x2106224505044c0000d800c110020a503080c45080002c241c086169500031501000c0c5074042c3c0140124400021200010300408100600900030070041601c032030311480d0701c41e075200c8034003640302d00301085202c03030900415240004a4012003c0006402c06503180c0800060f01e01079075554000384008401402460f030b04142920b800380d404041070201400c1e0124001041da0440d8443c840e0018280c140700d44212143d502184402c1d80000001c08c81c400000301e8540b41580010034410100c6181d001e195840c050100040c1c00529040801c0c01030f036215100a0503054030082001480507103510001c05030a4800a18103112602d0301c0611071108800e000c0d1130b500038400800b0321011451601d5000c402d60184000da04a1075031111280d02040d40952001e0300c0003000380003000185c0492806c24000c0005001c2920240320703040e40050307a85820084040000e80c199110340c02c0760090f1122583c2904600000d0704401c0081c0701e5003403100020001603000024010010070b0400a50050500b003a202 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 506718426 1250 506717176 506717191
    0x503062709011811090a15061d010f05030604050c09060a080109150501090e0c070b090c0109090b03120c1207240b0f0f0a08030f0a0e0d02010c02150918010608 70
    0x5451901000c0b880034a04c000c40c1020a8842c90310658404501100804c510303c1e0b65007070142c45000124020b40c1c0400e122595480844400100040f800b0040d103080384072825640001d582080000c003182010341041d81c0100801c0708060900c681c01780003410036084000403400107591700c0e004006901e2507010307172100e400320620700080103030030800000d06030301203070203001e90030268072000c00c0100c0d201070103e80103560850651911405c000c071f02030743c4804001f0f10b41d60018107505404110501c0368030940b801860001c000f007644203100c4a03442000d07041304600d822580910042c540514402c030008000c0d141c89154911840c803250803801800303c3d06074015200c29443c1c0074850ba210785401803c0140c1400480e44080c03802d211200040b4400041c1d001481180030214000c00307013108031800b400c4010025200ca8410104081c2030200342517070300c0800303030000e803c50f0068005070429400c00c06056903c40c4850f8500f240220210b9141c2812401c0807104401c4c0a0040100c43d070b0140d003540e00b00d0f4a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 506719676 1250 506718426 506718461
    0xa0906030b010b030c130b040602060601020d0f111c030615090f05011103070f110f0d0206030103081c0c0903020f0405060d14010209090f0a05061807050306270901 72
    0xd68940541110050040a151900c0003003c03d004410050660f0402c0030440720070100c554540032502090b8210344240c502501c15403001c190150300205121051480315946ca6000078558030f41100c0e69621074072220598012802c40310b81030703840203210501c100c200303450200343c0750302c1d008690030101d1a4031080c0080105074041403001e1011a00342d141141d0b42442c0215101e000340104034258030500d1300040840100b06040c00c00c00140c988543c1215400300c1d807003e09807821500f840801650004000d40c803c0ac20401400012030840c007a00131900034812035442d010100540030100e4111842010200700b03100400c00031450001488001220b043c1c409010307604040300403c0c030f1161041d03401011803003450750304641c644003507040e1039400c9002000140c05042040013808400340c04c0e12040442d0741880c0015401e4200b003012620841000e01c031444c0d03199203441c1d0803034842d00040d280f01d0b80949003001c0008400c0403003910408145403201711107043d0820b44a0b49084034880d0850410005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 506720926 1250 506719676 506719679
    0x30d2c060a05070908030a080103020a05030c030a02100203040509011202150c0d0c02041e050f09060f150102120d1b030b0f0d06060509040803240d02040b150a0e0a0906 74
    0x800126400340c10060348a030102d03640c1c071810381c1030300c003040c19810601880c407010440b200d400303901002090480c4d000f03444240881c1d07280c03002d054807000d04a0181d5055446409000c0044c03d0840c41d51000c000750f44181c906143e00e132000121945003e03803141c500e61120005a1065280000e1040e046a618040480c030b072545007111241c0f00d81d0141038400c00d00c4402e2035010150b468640282c004200b0b500702824801c04031980141c000d203415075556414043c00c10015507103078400502c031401409650345201003540c9501c04e5403a2040700f44105411400b50380b2340ca0748441c0b11100a000000103200c00858080c0007a0200141c8803d001c4d00b0504150405401820130b498000002c44510400c1d030342c0e240d90014134107161001c0d000c40d41c0035980002e5000100000d106654020b907014400d0142415003040d81c25a84906414100c4501940803443ea5030030360051030281c2c03085000740e034094030740090005090b81314002c0d80c01c2100c44030b001c031f040a081131190707182150717044002e441407460800c007a9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 506722176 1250 506720926 506721011
    0x30203060a140d0b10170c030a0b1305010c080403020d0201050609190e060a150f0b0306040203070c05060903090a0605041d090313080106050414060906040b0f03030d 73
    0x241642c490142282d004264800c01d9844010020900720b810015148050502d0f14405244900030f10a285408424601903c40110302040d62145131900a0080a190201d521254450407014100304400c204408400c80040c0b0203003c3d210032005251564480352910f410042d0401d035240c0103010440e450801081070030340c2c0d070f00700c856004031501d001d800041a40e04604401046060f00880c050300c030b030100b00518010103800040c0c10f0041c429081d140580d60720305000300e00030280506a60300205000080b20b0f4100b90f0b01442c0e02c0011361502044107101c545811b42400c80940d010381c0c4079040020085524104609410020005807403c00e18040c60700c620a1213840f9090460b41001c2c18900100720414401c106617820462502601c002c40d569802c001402041c01c1e205090156041001c1480c0055241d800d99100b4240500001100c0e6211403c100041030f032548080e074801c071442034451458070100007030440d041c0b42d0f4100088654156800111038095a40501042c015410401041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 506723426 1250 506722176 506722189
    0x1915050f0415110909010e0711160501030231090501060903080306100e1008040501050f04021e04110d09050c03010c0c030e030715051c060f2903040b1603020306 71
    0x40b90008a40000c10000d810120340c5a031140148603130740140301e13100206409032803240003409108180c5640440c060b9207041203466001403562820b205042c0c0300d0800455010760018101403d030707614006807500c0f281c03044c440190444842200300a60310b1006102c0c2e201c0f24421980500b16070304040e00c4040c50359503028107074400142a940035007100082c0f108030500482d00c040030300c1c200070450070801c0b021400042500c60101c8003992590309000100f20310749600c1420f036000f503070003429034048008185400720101c00750b0058140c20640e20034441c0100c4203154060003a49200420114040d00c0c50b050440c070305001096101c0c8a41d2408401d0f5040d00d420006046106905081181d5100d8540000074241080da50040184503000401101c081d0b5020004143c1c0982102180e41c04490201e50202181c031a0300880319500030100d410b01c1980f1190f4030410740d100503059182020003001d0b161907a150001d681c100e8090b5111010710402d00034030300c0c0011000e8410300d021400e500c0d00d5070000e1003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 506724676 1250 506723426 506723453
    0x303090a0611070801050f090c100509090411031c11060c1207020a02030111070b07020d050414060403050a060b10031a060304050a0c141521091915050f04 68
    0x500502c0030050b207030010203000120080c001c04000300001d1a2032601c002252004940d60003403801040180c076020f02d401000e8103410340745540c1d0035041c003402405019185001030070507519441417008040007940d042205ea0f081310240e00140d05038081c40c2d14080c20300c00c00d03d170844811f9000942001101d9200c101541c0042c00c9003035003a038007a15900c400b40d00f0521a54030181d019424251850003146056008001f00383c41031106070703000c4d955140d040f6181c00e207059503680080d80821080001c0c601528400e49454001442286019a02c1d0303076582c64138400100c11140303d03440d004011200e103021807949070081052300341070202c0328101141e003a240b40081d8800d8840c103070210200e0103201040014142d1240c2c8240c5440f4495202c1000c010750401406860348202c07070082081055003902401e4607488403181c41000c0600c04280342c41244081d00805045d842d100714281030400401142d29011427501817201c0004505140b0325020544000800d40443c094a41080c4400100041d09c0b201 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 506725926 1250 506724676 506724689
    0xc0706080112081608070b060f041404030f030e031b0610060512040314071103010f090b010e1b0d06080706090302010206130309090c0801300318030c15030b0303090a 73
    0x213076191211041c2c12100b0048400142c07070b0a6010a82008121460112600030107080307850010210b4101c0412007940d5a0364207007400e0784194404200003038060124082203890505000c100b00341405007903807854102c4801c1d00380a141d54a0060031541341804020303040b0300c105180c0c0d0016803c029000c1c10078464617626850b00c061501c00a02410303c01c0c0902c3c0100d040398074801e80d84086504101c03a2031108418140e02c294a000c80c6101d908500c0c0c440d9142c2103a1212107180986e20b04628049082d10040c124000b001d030490307180e0511621000101146c50000c0800a040c03424403441c0c07840e05c5a00d800500034003200c1d05040c80581e800154056000100a9141041c01002c0c6811140100c0903841140410b0401c0590904030f50043c40d4079040e5068040d140124104103087e1525100c48904034115000843d006440401e22900f100304000e0541c43c09282055a2592010001310b03c540c003083c0e900e440c5040c419605a0f043c01200d02e6000d00300c2c015824170a4020001c0e000c0d0b5098810316 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 506727176 1250 506725926 506725943
    0x31f240302150d060f090e0c0102031602040b031c05210106080406020307031b031e0501031707050a020a0f03111020010b0402030a06031502040605070204050711010509030c0706080112 81
    0x3241003d072513401240c0a010103202d00745900b96030300b210101420780200101c0c9213014541100c1c096503c004191045001c0d0f04103d40d220381140d400340001440314500140d0580902c01d041d11412100c0b0400e41c1c0e401c0d105565841c0c0e2401c16070503880c400d82d540d404180c140fa02d014010045103601100854005801c803e0040e80ea46540d20306070000c2030150080c110a503240e0070000d001342d41641c4204c01c010035008610840d24043e42c2003c08603003003400003c10b80010310841e90441d410040103001080c0c812012140c1010950b000105124510791280140c445440400d20800031084007421182d01c090b24010380c0301d076810b40050405c0999000c48240400086200b450304d05003500044800c59003c0d00855603410400c500c2c801030700300360209542d9250f507003400031a500c00c1482214100c0750310303980d0181001d1061b0b08002c003030203028100c0c10810058045c00c181881c804c2c804c00b0300a003460380045907603c2141044c0b50411009501420900512000402c041880055554070319940701810703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 506728426 1250 506727176 506727187
    0x30806010e090f0a06141f020a0605090102070606050f01021e07030b0c091c120c030903080a090311010207050a14151308011d100b031f24030215 64
    0x1210349494030070055a101007041c003844480810040c44a0240c603c3c40000c1c840d16859000c3c540c10381c113003010719a400658111050b0200c60345280c0501c0c178080c080c41600c90360340c11512007000b50303503080d03401d220303565030004900081180c0c921a00b402000190f54001d0300c4940c840020b5160000d4054444052003884402086903074140440c001441d40241c2072039242c24401c0700103409801204516000e052a0b40d00c4e01800b01180603100446588080d4034403404c80c450100b159003c1e1440d00031014041b8084011000800c5000a8000e4500c15a501480245541001b0805e90300c802d409e10305640022006016944850381808242e503103c1a544108140349008503480050862a1410060b0086080715010690420000842d605000240840424401503d0700074004d480c1d000307a1648000d41c11101c2d494141c004034804040201603900100e40342c0342400c1c04202d00c081e842c90076603541c184030b680151000d010110184000d05031503400d41c190b501041d0343c0140118088130204d00880d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 506729676 1250 506728426 506728429
    0xb01120c03060b0f030f100305030316030603080406081608100b0c0c0307060908100c08180a3302070203071a07020d03050309010e01050910020703030219092102030307030806 77
    0x1910090490910342ca603141d6804c80002059041614010301b80e0b4203002c041101a9005200201602e070000c01031851900c1e82070b6614103841002c071400b010305403258800000300c0c0803040608010301e000d44030f01e02246412040003501754800002803081c40005410f00240e040d070594108140c5505062a03591651529281031401e16640c10b4503030700d0712a080000ca030701e9901c81581d404855080f03040303400da100244040750580301c403a190000028550000128002202c06036400b9111160060f41c291100b03a80314031030604410a181100b0316640000d00c0030f00c810f6500c000e05550300300e0000314180354540d0700081d11440701d4441ca00308030004101007011015200c0c21a4a6541d004007154003000462901400c507800464500e0303031551034100784a11000c0306014003845001c0c0e210140800b00408511b81d4003d400124069081550032b00c4904285c0f00b4a0341c04e44c146400c0340c1c40d09034465180040c0340d20081c00d050000c080382e4014031440001030f1000026036055941c141464030042c0d64200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 506730926 1250 506729676 506729681
    0x141b09060c1015050108130503090427060507090803070530070b0406050c090d39090c051303060b120d030e061006200106050a080c0102100b01120c03 66
    0x2c108001450108900f220111071120201295000e8a6607542075031004550040d4131407041c000390a680040201011503d41030388080d1243d0788a9045c01c241c41120070542e10b03010fa011000310b90b8282d650b0148103481c0d41252807030000340b08400c0158900320881d174800751901081c40c0005144080d0800c03100150307500c60f600d60582421001201c1d202c8102e810400d4a101090b9400d031200c038580008900004041800c8880b42500500514501da48a58950790f0302c0c14035000c540e10000000d6800800032140848412140c8200494140104c0c2012440b804441052111005010040201d149036030040c0c1c0804084039008170300016206400c0010900300140180341400600800c00410000c903015440001654440422a035155403002000003811550b8007a403030103e42401c0c02040b2000c00c8180000380302c858400042121503403180412015603203a000103a4507002043c2c030100550741006880707014050380c03000b880003c1c1454006030280c61040000c45a250301c44280f042010300a8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 506732176 1250 506730926 506730943
    0x3040b0f0c0a0807030e0a0506090108150a08011406190902071a0717010b090a0509040203011409030403050d05131401030b19030b06090601051605070f0306141b09060c 74
    0x1905682844000f850010b00c01e6009820850120b4520040c481644c140100044142c6001070b1859251144250065076044801041d012480c55000e01002498580301c000c134009101d400c0002c00da1481e00001390340407550082500380946807030706800701500c9403500000100d4052001c0141e075156541000320904605001406000c42e246040c40009980806a0700b842200b84110000998a81c0d4405544d403203001e001070b5202030307150000d1121340f03404406150814030043c000a601e80d81c0030034125441004944000c65a003010500304284a4140305200403107842d45040e510b400100c1091120100050050940801c41142500480d0740250301c19052110020b20204a420380d00490080100c1c0500080312040c2d21980402ca00303003490800c081c02024140c4a51381090038000005c0082e010340300c07003900e85124100380059114040040070010710f001d82c001182c03280c1c091050000c20100a0901010310350044081101c0d070440605881000c4d81c111401640e0300039a0034514600b9040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 506733426 1250 506732176 506732197
    0x31121100906170c040e0601180204090903080f0906010e27060c0c010b0a030b01060c0203190303050f090a171e0301080307111009090203130501050a0f0612030203040b0f 75
    0x1042404510a0502044003401c083d0800403109100e41c0d080520060350107943d0340c042d49a1100005004405040c417807070910004a182c014101503480c000f01c07098940300c4205a022405600074400079000e0b005a0751341c402070420040601e035141040400054400030550451820480001d08001400d103205040d0404108101c030154105925044990340c4500300600c8a586403040a03076032400c00712421002c6a4205201110b581e28100055a40540c6101c080340e060140c001c1c00181d1100c40c1041d001030364081e560002d05032820200d849007900020b0555900c0340c0c465007440000800003205c010840c1124070700e840e215000320460b021900c2d0f1201082c0c444020210002c40c44103c000041d0034007078050581210000b0183c800d202e040e542e13204400d000500c601e002401071320020f030000c64114600d410119012141c03610b81608490081e0307111b1440316180d0450110000041c010180541140140005210303010f68002c1e541784a68410348602c07400c0402e824608090b000d060b926144507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 506734676 1250 506733426 506733431
    0xc0a021e0102150f07030902150a0e03070617131a010b070b010b04080d0e0a152c01121e050403180e0727030203030f0310150e01030b03100e0d0311211009 68
    0x74280c0c009800d0740620b00095010f840737408800184284106c01d40c0c3c1e002c0e42c03001c004507650b071035528407814840e06804050320304064940b80500303401d1402b40c0840c000e000b08000d8684a80c00391412002030703401a07100717200c0f09400740f10500061002084845254010b0b00780003c240d600300020544640459000e50400741141450140050700501084030f0854a4032400d40b05640200711141c54655000c4a07034005441c0c01003150040d001c5503c106030308404501c00c011000b010400c054250f8008480c101c000400c5034420740d0000e450600d00e10068051710340301005038a013201e00241003458880d01120303034072000c0100314000c42c001e1a8600203150090241c3c0c2d0396101602d02041039600545040079000d40300e01c000240030201d0300d0b8010001c405943c60134140304200b00114060191080304503410300914208a1110740d05c1d00c0b074249032040f080081c0c440c1c81d0510300d0240c00c441030080c82011040c001c02207400000c5c01d4101201d501018a081d01d001525000383c45405415181c200c06800b52 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 506735926 1250 506734676 506734687
    0x3020909060d140715030e01060f0e090a0501060b190c030e06090402040807300803060d0501020c060702010f060602010203010b030604050726040c0518010b0c0a021e0102150f0703090215 82
    0x89150b002440c6217085070300c09221081d4030818560803104507109a414008041100780003001050410301c1d08220b2403003c403140c03019503466027402c442c41c540c00341401c2d9a0000d0100082594054524a00c1d10141480002c03190740d40c50103030100008040d540d2054000050a260755070b80d03541a12701612000044440c0c1135114000740303c00b808200b2980e001d904420b04d080200145d00059130140740d500801c094156222402440030380c1c083c3d17050842d019502401105062082000a244101900c2e400440d00b00074590780002120841d411034000c69004000601c0080700440440c1d070400400e0390000360a9a4845041b9041c41921820300ca14912000e5212201e130354441c4543e000c1d5014420400040342d0f684108460b15040c40341c41068039010350010803083c45c14001401e94101d041054810342c801c250b0006141c2060611444550a10710949400315603041040b45c0058407008100b01e0f40b400c00119040c9c8003000204482d0030941c07505204011500c070b210004038528011925541ca85 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 506737176 1250 506735926 506735939
    0xc100e0304050103050f1b071109070f12020a2304150c0506130201020607030932060a020705030d0c050904020403060f0c18210503030108150703020909060d1407 71
    0x250720510589002a007051301154803040003521407809812007950119100d01c2d8800080100d030480e21007501c2c0411a0491044962540032041d0f12070003040d41d910032400810a000707041c0d61000c648580c0744070b20610202c1a211303000119a030344400b044d080c1100600480f980c81546200d207030403503803418000768070940d040382d00b103202844d9552261050f981255070350300b9518485684d20760007900503403011000c0303521316001e5441108003d025002c4103134075200e50f0240035110060300300c1620010381180c0c1c1002c003100b41823100380d4100d000c0800070b52030041c10343c88040c1d907400ba50b84207080b4960303a04000c514840c0144101c460182d000b81c01951116603030300700400141030110030b9a00d480e0810608a45480c0325460b248811007032503207107030001410720040c40010149955a0701c8401c512601c402c01060081003c0c50003440d03d10000c102074898100c0742ca0510700082c4c05e0034249401407161506513501d411070386074440c406480f00140070001d0b0a00902e00c442004860810703000c1d03140086140c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 506738426 1250 506737176 506737183
    0x30108120c0322080c01050a090b180306070c060f110406050a21060e1005011e03021e04050315010e011502010902040f060f0b2113120f0806010f02060105060c100e 72
    0x4480002c005d80386000c002c440151a90b2143c080000000b600d24202030010b2400d50001d003517100b0203894040c1030580d170080401d20b4907000350381440c0443c250265580c20422140503201400c0e16000041c402c040c152010205d45001c0d03805042d06005001c204596494895204903000c0700c9aa525104c042500306039003001070000d03004881e0000c0c0154001000c0c40d86d4800c0340c904840c410b0b581d186403141d41300e040b0084c0710040b0118030101a02004074525456880784010448441600c105a807245007500b054603180c1254894a0b10030815001000b060012850b5141103c0b558001891042055503003280144243e4500a502a2511514060307002040d0f2002e029580c0243c25002d0150301c803046421540905d00bd00c0030b0711030710703444c1118a044201444980000550a14040f035a42a0b600ea41283d0b03052080480018940300310181c580b9031058000e50001000c1c20000700302e08096130000d4803038005008007809240700150f0400240000c0140207542850507500300614400110503c0d01d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 506739676 1250 506738426 506738429
    0x19050a03141612030909050f01180609060906080c010206090316060e0a0c1809050a020d11180a0501170c010c0c1707090b0117130c09230a02030108120c0322 69
    0x217040000c04907800368240710782400389808600d5071010360300e04803940100c081080808c10f0510703142c500000b140e8480e4001c180c0134005071034010a41c9414282c0c140c2c0380c000811081c43c110b51003036003480842c031000300071181e4440c044408034003008010b00f403010240c4080c40d40e810403882260303004020720018008000913110007991a4900401985002081d0b80c01100041e015801005401005244c04400d20078502c1c1702c1c018007020081d130750700001c51158441c40e8400000c50b840007003025030405032103960701600301c0d444003682040c00c4021940d551040003030000d040c416a560705405001d4084c0d002ca0040c45d80038400302e041c84211840d952038010702d1051000650801509102179030103001400c036013644008540600741e0700c900f054101148a680306945103484120701040341c1c4c4041c0106010b0a40c03104c26034041e031100d1b051a0b00042c0d030044c01c20811603c14001800740f6000442c840300e01c03042901c13525488050150f0b03224194840c4a070f180c0206091003681d4141000d0340c646540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 506740926 1250 506739676 506739683
    0x11011b050d06050307060207090203040c09061502060a020f03063714030a021f0302250516180906020904060311150a12050a092019050a03141612 64
    0x40300d983d46105056541100d40119409a04810340a0141800643c061a401802980708a9401ea9107031016012510b107a040b51000c8a258620742040c290100041c80e00140055011803030054800c100d03d0440c00040c003514411403051241055a420300b407201d504000380d440071030106c02c0020f14070000c06230f124400c03a680181740704076203035461034042130300c244141c2c01034100c0104d2100688404503e58003151366400303259007402280240f04002c4a0644030203524514400b41d44440d04155140076108004c03d03000910301403080c42000d800d02070147c003e060820303010400601c1442d00e00c1c083d004107038406030454a0043d00005020780c18594905d038500c1a1800c1803280203400e9000502e1084440c603002240b030311840309440d203185510065004603041000500b4030441e648030f811a5070004001d0507251681e4070314814614041d41580e500710352520484105903d88800308800001c1803101500c1c030000e460500301d0f100400d014a5110260017131124002580362000d6041200200354140c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 506742176 1250 506740926 506740931
    0xc0105072001110d020c0f0d02030a0e030f0d030b0105070b040606090c02120909070c0803190513030212030a020415080a0b2d040f0c02100b0d020d0311011b050d 71
    0xd041110042c070a24a0000388680c640346440b10034131a50010790f00030103066141e0301c03446803401c0d03075100c06000f02199a0210750145507101650f50004090710030f41d61030b681c4aa0002131500f54210000903030448003030040e080c01702d03043e01148010713a5240288880a044800701d5010042048819030140041d1038109000700140700410310304a03603400074036084080900c01040039072003a25128903090342c80003451900828601d12540c665402d500b040e9400500413a4044410203c078110b40940307030384929039a80c0d07408902d0103510001e44d150502c18080020000010105540c0003654040360b0180c8002e81240c90406e01c40a00145001801c40d00c0055503460440e50000c1071503c89111010343d084258518903005a2501d003150000388010842c0c0e0055517840c10440d80d401c540114182c132a45134018210744c010f8480031405a40750010304500c84d000740428080140e4500079110348003a050310b0041802c1c810364440900403c9014070b80c00c445045032048641e965808001809102c0a80c6420f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 506743426 1250 506742176 506742227
    0x408070324050c3403020d0f020f15100512030a12060b0a03021c0515090108010905030319020d110307030b090709060507020a15050c070b0301050d1401020c010507 72
    0x20100301d80b0103845500e0000d000f080110961075001c4502d050180e0400c0d90945041880e506030301203851341060071005a003100c044021615040203500701030342d200d4005429034a60302140d4644510614001980d4484600b02041c031002207450500050400030303040306a200b1814074416640d1700b10525401c0014144c01203500d0101040c000c2c1412121b05100d81410010070040c20340c0070f504124020282101c10202810140889016007070103425589041d0950a030240144070780c00c50140c001e03c0381340e03052111102c00a80000f0849900c910000d6001c1503c0c0010004031001e441580c1d14a1111411f007103000c070306030043c50002c41c01851962010007c074885c4000b40241c0710403ca07501c0011070f696140800416001394000c00030b0070720003001810307015180d405400000401d0005000055004160124032401c10056032014215400300a07080d0b6141000217060003606840c001c11200803074020a55510b404d4041d60600d40c40034000740310070b141031074000f031100291070b03541c00320000204003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 506744676 1250 506743426 506743493
    0x605030f0c09010906110120042105030304061503050708070e0a0c02070302090604090206040311010e032e0e0d08090c1e0405090715020a02031606050d09060204080703 74
    0x11074980b0b85060b1a0000010315102080c0d900e000c520f080d40400755224100380d040503081c604000040c0c6005610651501d040c509000c80f0703104031500d0180c04203c00140d50010510002c1a2540b00754818004221941c4403da001170248030f50f4001003440c41060004941c200002c2001815140200081411952002e446c44152594403801c5409608081002e001504008006a60064014101184101c4c0680c041280b80d0f11035801940d900c242c0d0f400d818010360340014500e0120004400504181089106c1001c054010f00181c9003c02c2013440c1184405d0b025402480300e0340c00320025169807008014000d0403d01c01100e1428160242480c80245803a008180d034502c1c00f42e07a039104039404c10b6041440028000608100b030079102c0d010f4002496801c80c10302001301d45040c0e0180c008030040744185843e00c3c501010342e45440056401c28800c0c9a4064140c2c0c804154405010800794020f0a1800080c1b20380d4010004a0044100100a05c074506c400d04803e07481e251501040e01100c4d10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 506745926 1250 506744676 506744701
    0x40311090103081b01060b0f0c160f060c1502220b1e0c0102041e030b01090c21060801150807080304050a061101060e1009050f0708070c03020a0b010605030f 69
    0xc000c00d000404d018014500c80080c4100c803040407048000205192148403040150f04407a00c4140f070440c0014800180c0c500a10000044069030b04c0406c00960034040391100c0c40f40180a00d070704100c20f0b80d01844c2440301d90803280ca0f06081e4418215038842a020098038480080205400702e80c10302c11000607090341c82c800f281c5070050382c0c0071a10b406c02c24281103600e046e8011040c003103d9640a0001241d020a0049001140b841c04c02d142c1c080b030f91452411500003001603200400c003900e40403221850f00e400c41c00071000c40081050030402491005201c3c001040700e504480000c0d0319208003500c2c4190300e01d01c40c2c010b541c500003c90700b9203a901d00c50f560780d038850f502886030062510b02c8108103590080c051507003051092400803421030b403180ea2441d80d070203040301ea18201d038101c88010001000d083c0303d020f40040e101c000d0580a031800000c060000280502110b08006201050f5404e0510030301c5001c10301d5a21082003189969148801820f64005480c940b801c0c1c1c025101003040d07104001e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 506747176 1250 506745926 506745929
    0x807021036030e0d03020717060105010801090b03070308090d1a0603100902030a0b0621010c0f0201020a080712020408060c07021801030f03050a0e0d0f0b0705070c120302070b0a0201020403110901 86
    0x5940da04003c00070001031103041c114084084041d0b2040f45804901c003210a480000003058040c01002c03151301d420700040908406900070120980f0304050706e00b05890100741c6206a80e0005500c9540740000e90206500815428000c3c0000805d0f6612180c1c80c404580814010301e401c40807101c1484083d010501212405071340290f0580c0600074034000282e0300000a548803070000d104805c85075501070703695100d0a4100c0c4000050f503442c46102c969540240078000302d00500c1c07000b10702b410004407024120550142015090004200d901004501c0310780407140682800c40c00e13034020b418140180c80c4280c00408080384100781a0050341c6810741c01ca10780314120703a00180c0201c50300c413464600b9a00395000541d204204142c83c4403824094843d2600c0c3c555052182c0d107881c0c003c4801d820000d03400309024100900f00b05080201101054500102c00b0030745124011a1103107048a1806920b0001264000e43c188000030400b0340503a82c044d03010b002207174003032a03c511301c01e07008030100b00440c4405d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 506748426 1250 506747176 506747183
    0x41511121804051e01090507080c1801030b0609040906061a07051207021c080309010e0606010905060f070209070c110102070b070b06123a0207060807021036 69
    0x20060714248a00e0250003240e04543c100c02a14000c6816012202000b04240c06c280010b0f500c1d00184004035600083c074550182e45000b03020b00f030950445030000e06900c801c102c103040603200c030030f4100b0940d207100c21602c414000902c100000c2c1c41916041010b4495440f801c6d0f0040340350f1a940701c2c1c5985044c11210802e911101a12915618145d407611740e8000c070a0a03600451049504142d4400401030300a1080c06034245030344a10701015000e09603034120000148a41100041c420b851360002c8081301a1601110f025894000301000305819010700c500107944120108148811590004240344445015510018842e165107006980c0c0c1c40080c0721b503544000f0100408404603c02c01c410300c1d044000104104540d06500945502e40310314101441001500302110004400c03550303c0c02100541c010300c81ea03071903010404000c0c1d01c50a80e4030032101403225800c005400c81307109111041c49031400706410005004055000301d4440c1e9910703200c000d12498140a682e61900c102001c0440c40d50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 506749676 1250 506748426 506748457
    0xe010b01030b06090a060f1e0314060f01081303020a1b0f060311030f0a0905011a03010c02010b090703020a05040b0301090f050901092303090402030c0c1c050703031104151112 77
    0x94200225240c01f5100c0480007044081c1f4a075181000758080340910807041d550740856034558070190303e01882000f0705940e100c4c0b076070300100c841e03207903040204154050340719081034075240d09500701030707003081d00080b0002d109400c12044a12075504a10f101c0054500c80100001850b89030141a005c0714200c4080800d05941031000907001c61105218962090f21000042102c888070764481d800e441d40502c07a061b111b04003440d412140c0c1000d218407501c0d041944000d011a0a1800101c1c1c074003500030300344a0030981c000481d541c0a60040e0b048400800528a40656941e0355a0205d00113140b240c0800c0c0c5098208408503103406014000c400070030390008860300c01c25082e441c0c1c0300c40078160003040c0700031808140104112551035102031403041c055244001d0390340c1c0d5200291418060100c461400d0489007241c26243c540c0d1103c150343c48180d041c100052090140107005416000f194440c80d000b081002100318019845022143c08401c0181120168003508407038803020f01800c40c1804070146e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 506750926 1250 506749676 506749679
    0x705161211040b06210402091302060702040c020c090c09090a111b0c0a0905100803040303020a1e0b0117121c09111203040f0b2a100e010b01030b06090a 67
    0x3610350f000b5000b10100405031894100c960f00c580d8407142c1c25a68110646022404000950030041d000b150f024011010811042c02c0640c0028051700611001a0160385d5500d00c10545a00030050b03002c4c600001401c5500302d141c09803540000303611412140d4011581c910120b1155001400344405a010400d030640c2000701c2000c1e03498010a4031400000f0900c50001c81090760780300c2c00070280c0501070b40071002c5030914004210f101e500301140d001c04110351041104002103540441c1c0902c0e240e82c070401c81d031070900d004000c0b40d5000300055030140c842c88058000080300b55041d00d40710141010081600c03031003100000d0035002802010202c0030703014800814040e05010b80c1c1d000c202d0281c811034006010b9022140800c0c424551150b904241e81c0c80090240080d81292407060008c0c41080d6005281440c2a10390b84c81c0c40c000304c4c104800600750f00506d0920303403506210722030f40030b01c3c06030040001c1c1c80031403d0306001c1c02e040d444040c003285c42c083e07030b810060038640f040740c2d8840c0c4064516645203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 506752176 1250 506750926 506750929
    0xf1805010f051513060f080d0912030906080405010e060f091005062101060801150e090601060c0209060d02150405150903151f06020303060f060c0a0206030c0f0705161211 75
    0x503201d280510481c5e544400206c5c040c2942c3c103030f000241442e28020104026100b00161a40040f0b41044407112070000104001a40c007441d203400b95203179403401c03251035150340c40c2c0036006d00400450a0a00d000e10f9003000141c40c1e110b40098442c2d86440201c03010701411f03003484400c84000b07035a403d420900c0310602901500704054042840f01c055800010341982da04200b9007103508800c005207254802c0d44082142d950542c01040d04036480201070445540350180181100c140710700020b0141c0310100006810b5901c000d03170403e20341d4000d4180b49400d01d0342d0785044240e0b405806180c2c4a9401040b46000448400c02a540302e4000603000703110351640d440ca44c8c10402001841c0d07060038504142c08610b102107190644c001068560003e40d12410035a081141003041c1100302405000180004818071034002042d0210680590f80c1596a0f16200b461507a1489001049002114000ba648041000c00039034006007101ca1803e0803840d40d211080112621007036040944407641000075002103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 506753426 1250 506752176 506752189
    0x210020a051b0a02010906020607080a1508010f06170c0f120a1208040b0105090903071103250807051903030f180303020d080105031911040f1805010f0515 68
    0xd00040c2009418110050004000780382c0d64402c0303407150b401c06007400b421940c0002890018154a0000d401e1a1514500c010460b0000400440c0380c29103407a0070003062007045041302e02070103d1400900c0101c100142c03a4020300040d105c1d840c0c400c030003a00541003041e00410019a050700050148409420340010408401c0c0c2c2108648414058584501c002458201074a01440d090340c640c4092440d2070f051240780f801050340001c0c0110240800c00183c15804001c50b01041d0744038000c0002d40080001181c80e141e4408011b101888100c01c076420482d540742407440449020100300c2d890180c540d0144552150400c00c035000300e4240700c2d420300000e40241940140c0f20313414944401800b12400b0400c00c009903e074816030240e04110b5101002c258041211800b4120a0300240000801a16544031510030b581001d80100081c7e81d600001c0e075615000380c00c00b94400c3c03009014040036902d11440c005803844045540b0742c40e1202c419140d0000b8018a031003808440c1030028080c15403000c0c80306 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 506754676 1250 506753426 506753437
    0x7080a11060f0a08041e170724020c010516050f030a0b040207030e0108130c06180503030406020d08130506010306020d0212070f1101050c090607050715050d06090c021002 75
    0x1d111009004010b501d41c2484042c046032000c0f551076012505290404000010009888005440b400b441d01001304a002c540b1004080064140a556220380d0800036800041c0d09208190b007086626282d005407050b402800c10751440c0402000a0381300c6155051500318051014400b040040c0440758066a407c1c0213036501019003800030622204000005040b03070300c203071421004201122072140311540e101c1c50f215401880440c0d200704004c2c2c0c0792200b41e034510041c441c0c0d4003004001a4854802c0003600070000c02810f000c2c0480ea1681e07102d0802a44561808410000007003c1100095040d11000f100d0242507802c6005410b29900b142c070340700080c3d40045828074400d5001c005c140c1e40e070306681c2c8919100b0082603854141d5100400c00041c0000645400c2d520168101014000703c95415412203d007240100c5000b81c0c0c0e0591494aa03081541e0b90f81300400f922424199104e070b40c1d0b08040100807a80d40300a003000120344854005003161a00d21140c0e00503030014040b1207141d40c3e154002c21 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 506755926 1250 506754676 506754679
    0x501030b011e05030a060b03070e100201060803040f03120203071115070206070c03150b090a200403030909050a0908070327080a020906030309221104060203070c0807080a11 76
    0x991158500412103102c07054481d406000640000402400c442c4501c150000f510300030010324a5410041002031024003520340c1d0724400c81c1400f0341c4a07003540c000d6000034014a012400d9a4803590395180c241c41035605444141c40400042c02c3c00c8003124804011150302c2c69000b48420340340d06180b4244818008004403694030000100622809039854401038501e4030300ca4400d04498078198036140300c8c2c040202000a41c4507041148005480da105050150700c80c00c00c58001035089207000360584107107804915510540000034010051541c0b10071068165079034214140615168101c14404440c0a45d00c050041035003400000300003440345010b04015221003032850400000750511140300a510b40c0a000b00307603c464042800c606213081480e500503422400741d400c00b4a41d40c0030480b1018101082213495141c0f0407045c0b0509010750180134022032842210340c913184c9410300607680c0d42c0b00340070a41c0d4840b0030381c800180da104001011425601082e000d46041219035480c06800d100241001c0d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 506757176 1250 506755926 506755937
    0x110102160e0c040b0f1c0203071b020301021e03010f05090c1801140a1107090506030a1211010c0c0b0609040c15050d0e16090c022107020d05072d0501030b01 69
    0x441061000290482c005d0042400e03980d40351425070300100d26030a94442100c50b00600802000d1038000c0202d102190002010400000d001d2002a00a104104c0741c0244c402c060b01d40b140010780c41070065416079031000003100e990750f220401c000180a00322107019000a040000c0d40c450400a0010716074a10107040c145c248080d509203c01032038001e00840307800208402441054140b0401c1404010602e81604002a0401c2c50209460b941c2a0780094441040c0c010a201d00700e110300e0b4000d0002030020020054010180b030014050440110141e03501c80804010501c0ca2238001c083d68040c03a400f0b0b0441030200d00d0204280049054290b09205002003400f506002c1c01041c02000241d50000b03000e0043e0840d1049984c103a4407140d044000e12070b20348030700c50800c6500000c3c0c03040030341403e90400c681c032204040091458031030290029004040380f0390f01c1c0c0070800001440d07002c0d41e10b000381103100fa640d030480c250440701d40d460300c001c030240c20b410b400c010b194060341c4111501c45062520 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 506758426 1250 506757176 506757179
    0x20f062202090405160519030b10030b0a0b010807080f16020c0d060f11071106030a0b030d02010605040c030228090312020c0312071a060406091404110102160e0c04 72
    0x280b50064211002d0307605030081c10190044400e48004040946400c45016103c024038008420344110079010040032001d1a4011910705150220b0400095900070b4403a222031405030303094006001000c109601081340440415102070090b010140b01c1c140c0c1d1a16114a540c580d5580240300081c1c21140095001340302d00400300e0340341c07030b8452001680a0352010481e007000740880011504200c4017640181c02c01c3c824800026400f21403000d550780115043c90702c030384800040d03000514942600d61381c10300c2441400e01d40c003501908035804980007103504003c801041c00041d41a0310070300500500c40c2d28219921145020032070100409204685400c50526842c0d5940e520f501c1840300b000409644400c0d00f2090525080102c0f50003210321400366030034540b0715501e0001c00b4181a40604c2c00400f4500000d00d292600d501032001401031034814032002d40300440a0104006c01d44090701d4120074410103c4c00f81d40005060110203807140386002d00c031842e040368000741d80d0f805003041102c103104000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 506759676 1250 506758426 506758429
    0x6071b05060a03090b010e0c0307050906130909060501171e0102160c0311011d06030703110f070303110405090c0d0902031203011509080c27010f0302030607020f062202 74
    0x1e80212006500c00281c0c2c04c41e541071042500e00144c1c400c440d56101320081240c1c001414064a8100c9010704001d9180c007a6800091322502031341100c030389041030b040d01c0002e042d0080e800c03020034140110f0080141c0c3c1d80304d0b05100c19130600c2c041d00070800c0d800f0340d15600a80815044c41240c87c074101d0001400c00720380c43c012030070300040402c054440703290707400d0300f803080c002006c8131020705d00301c24240714a90361012100c82d2900041c0307503506c6206080200004003c0ca019800111440201c1c210903a40c4070310303844040c080761300801c80c141c1c0040c0c40e00414800d008403410880301a11030040018600340c2d652821312160b0f0380121020080a52200056401a10200b0907140041d4011066030348940c140061074800503807075001c00381004007042c5d081000c01000716001d4214107094810304041da50488080caa01c401d07108900c070b10849541d0001880ea1075268101044e240300300c054030f109807200401240c0e100c3c080140c41c04c41d0b4108001103a400c0d00101e401010290045200500802c401d40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 506760926 1250 506759676 506759689
    0x21020409080702011b02010f03090302191b09020405090c0703090f090501051503061e060f0d0e0d05030c0901030510030204020c010b0f2209080910030f0609060506071b05 75
    0x1608072070344580480c00300119a00a00703515503001100c003400d031040701241c00003442001c807210a00300741079440401c842418801d200d50280724440d40303425035003e4018070300701900740c1409040341141607951802061807803c40c003c4408803040200325030180c1d01d070725030218141c1c0e000001c103c1c14000d26980010382030703c0f24901c034001445079041c000382c4e540c074203000c0c000c1d00c2580b51740d4610714400800400000381c2e80c50010342a00004e8011360715005000c200490201d00c81c5640d00c0354445000304446200c002290800b0340d42000302001c0e0f0b4091070130b2407401d403600e0000b555603018140303040c04070784615440383d4460360340400a015080402c55aa8002c50100e83c40740039080c08031f9448407869041400c02da00c0c2032072900c1041d220303242d211080010610078400303c0181179800c0c5890384c00e00c8050010354016611075000051481d96001c100c120080c0c003c0460310010a0715504049001032602101d1080340d0403142d0150000d0714000c240e40d80c2c44242d01260300c4158800c00315500200706916100c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 506762176 1250 506760926 506760941
    0x60d0c210c0e010503100e1b04021c0e071e290307020615120703080903240108010c050405090c2817010f0803070f030201090503120a0c18210204 64
    0x10500e0b0055040600b410704103e81e041d00c00880500f0000811540200003400e0004500521001000d6081c4000014060303c00c40300790000c05901e200740302c541048207a0002c010f40c0034820444d6130380c554460001c5402000700c039070400c160344400010401103003200c42000c2d92400c07908104040c80e0180070025880d41003581c0500050b4420300400013400c43c68005614903020449400c40f8440030804210356810321760000601c02100851900078030346040203203904c9a55003190800c0084e1410f1002610040248a0900c3d035608000e1102c5240f80144100c41c26982d0142c40c251083d030745d00240d04121b500060720102d0001d4510300c4540c4800380c2090042caa03072001c2c2c0d50701090354800d0444011089040c1c0280035000c4070b18104101c024000400c030f030038280d0710800c00c5080304202d040980c0184000321014205020015030408030003144280c262245c0c400410030440321407030140468500ba403030802c1401c00d0045042c2402280719070000006c00044110880c2c260141d942d003c00c0644040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 506763426 1250 506762176 506762189
    0x818030708090f0111071514161514040209130510050a060e01082d031908090606010f050f0d0f06090b06070803060d38060d0c210c 58
    0x8500180503203003918520038590f4091822200d002c1d8004030194031135901d8465041020b03501021000002d02600e912000b0407542140691a50014554800700c4000c2003800c507203500b1902882c00c0031810900c6440041038045003c3e01243c0e4855003848100b40010b800300c07940404000c98400042c0d8100b0100c2c00c060b030110008680c601302803045c20309030f5007540c01000c981d5810034014440b005d00029072400c40040314503515410480e00c82c2503500303d204285515a50301000621406030146288181026201035551003003558481c1d400f907031582c034291129070000f541802441c2120740310340d01601d18402d46a03c4030749400c3c00187c0c100e040714903072905404d4044c4c55030400c1000c0a61840303800310b0404c094903854501841981d9140d0301d84001000d442c0f00d83c60080340a0203000305114004a84590001d045c092160b0000346d00d000010300d0890300512140c14800160141000d00039900002c0d13001400d081d0a5080412403400300018900c1d401001000d22492808650081c1c8420000c001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 506764676 1250 506763426 506763443
    0x5030a1d04230105060c030f0a0306080a08070c0e061305100914010513050705030c0a02010603150203040c061133010b0304060b010504030f1b18020406170c070308180307 75
    0x1030144001240c210b05078070242c856038040c001901d0441021044408180c580b0070110703034070a154031060303000f020603800058161280c0c5a600742004150360083c071410380038020b091140c03582d903402e40c510104204e07590b64002200b562200048620303900040d400540805404280b161141410b004440e010703401000031107440300040003203080c0314203403440480c50b40700b05101030303d4200005402440050580c0900300030001e070000b070340b51003980060701a5500000401100c400e0a0b6440065001580d00b80d504511480c000150b4600501c4901c031381005040c0070707104640044080c1c0407200f008d0010b03100d404140c04204211180e440007118040c044021104d6200d05142c146801103e07602c842d00313418000c0410062010508a04860140992180d810b50000e0180f2500c500000010350180c126105101d03910345411900e50090400e81e00103a58168500d104030a0602c08004240c52021a4034004c214210100e4481d8101aa1081e81e08004010040d40001a10b00e07580c40340409a40521 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 506765926 1250 506764676 506764721
    0x13080c011a030a033c0801030201120501060807120f050403030203072003070210110109080406020f060402130e190302030409140720120d050702120705030a1d04 71
    0x84030071540300d80724100368000d003048401980c0207045100381c200c000a50550420001381c00354140b4070801d502001c035400700741502d604100c0180c0760210030301049001c03c02d9540f018a048140384102412100940c2d5200026107401400780c07240f4000342803503900c16403035061302499507100d4041c603270149100350740041c0e81c0d22b000c2d2001885007042c1d40b002140180c18035140c45581c40000180c034032550b01110481c1d80031300c0208040d507500250b4550403007076500304080c5038240050103003e841141d2943d003d0b01c40c0001d01400460b00c40000700c400a500500e900c041007203810b2070358001c1d014100480212401040c41e00c0ca8003155915114044005034000101845038440d64001c405d81900c0322010500c031401d00340c10140c81e0209a03450300c145031034841000401284100035001e0f00261a03d40b1542d1002d8044000001c1d0400702ca50f140944201c0b0604100508010700b1078001ca9041406541008040302c0111030200030100207601940c48801150304075903541c41200c0780c10f00e07455110340004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 506767176 1250 506765926 506765951
    0x1b0a02011808030319020909090d0305011e09090201110712021f080a2f0403050c03160b09040212090307060c08070e012d39020913080c01 61
    0x40d01020003010900260740007000411000030940e6000000305040300e000b10118480040240140c0b40c0056000c1c0b4642c0c148560a000400c5030100248560380a00003030380ca44900011110100720f18281840410404000c100030340d41c0a501003038814504600d040401e4292685000c410390040c5c10314400b0f4654007c01c40c50100082d910b010020000703019034852081028145000041031000c4141c1c803902c600f02c00c0d0440341d00f0014111050f000c402e0994614400ea030010ba0414081100d86200e41c2c3c409042c5803400207400c2034203030f40c80700051034814200401b15405410040c007107500142c0034456100c048400c0c1c030b02540300d056680c0c011500c42500d41009401c1d680c075440070100307000000051201e03450307009025000c0d10307c082c00c0c807503092030340c02d800320141094104070450388002800302018020303071050042410b42c0d040c0c000f00261014645440e0b034015a89012002001c51308281240141041c1d04081c3c1d00010001041029600a403242a074650200c1040307402c5955500864110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 506768426 1250 506767176 506767187
    0xd110a0f02010e0105071704020d020a09020a1803082208010518160b041502070302090717091203040b090c1f14130303140705070f0f050103020c0c011101021b0a0201 73
    0x903001034002d200905102d40050300d44d0f1490207c0040a070b0f9604006002e5455244000b80c426a0281111141950307403041c1200940288180ca80010003070318249407201c04034240a01030741d40201500785000c221800c0d4018886004224507105007140c1c00009001c032081c41182d100350811142040880f100000c064200f0701d6101d030580c03039903a0019080c082d10b1034110965040e10503800101141001d00c02c000e03490b048160f03000951201c0b0764001c110341c0580c00312004504642c0941004040d031940b170191501c600303203407040700c418440c00d2001401107082030805ea6007000c104000d8a16600b8950045126203d1074a402d00c0c0407038002c100d20030010790240003801c08614400c2039a041c250000d504030001c1c0c5040c03002404010b42c0382c0c0090641085a0201d43e4510ba00400701c03560300ea0b903542c4d80050142e0501c03920101d180304a200050a500a00844000f00052000380161105074001540d10042064001b0140c0d91b082c80b803005580f0041d002c603282c4100440040a00c5492803000504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 506769676 1250 506768426 506768441
    0xa0803010609151409010324030215120f061206071d1909151e0614090916232701050703050a0507020a14130b030d050d110a0f0201 58
    0x891000243c6442c02140d032001c0940b040340c0d022501c441d40d488079080101c0c0030b0f1101200031819460040340c000e0b90110041c002d982180c3c070a0301c1104520b03041c40e8844800c0d02420501401451400c00028031400c04042040d6004400604544000c044918080c2c5402800c0710414007180c82c0c0030360742605618440c5500401d54080301c0013401d4480400007401809003520a00001984a040c014084180b00e5030306005002405220903000038004e140062030050303485158040385003d0740008071807a0900889406943c0644241c1035a03c51079054059a08041c4400342000070103100c000e4446092506400f20100c2d80c014162220369204400c29038150340ea0820031880381c0b00e40071011598214056880301e5406041154075140340444c10b855500c1184402540400c2c00d01010881803800c01510103c040140c400c54140c0c1148011441200d01c10201e2580c0741e8002d1a4900065214030300034030407222507070350108441d810f51f2060502d642208030310b400400c07490025000010f509109404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 506770926 1250 506769676 506769689
    0x80f010e011505090c04050405130b060405010506030412021f09062426030a092102061b030702090a050417130504050411090106081005120606060c0f0a0803010609 72
    0x7000e2200b03900007840312a80c0744180d90140c0d2000002440069460058070010f1001400c144403130700e0040304602089509000895a480f0b140022803007a060501c03a42d4165103019150034590388407034480240c6008105d1565085109101d030b0440c1030b1907114100c00c420aa07030000460082001d2508200381c650b0720624488002c0480c1d40c0790070005040000c070b000c88144459080301c091f05130100c00e00d502402440743c03005200006884441c07507480101a4100d03040c2d204c008101800740350f40e000701282c02c803501a500c80e40520a50303c0741690080051068104c10045130310305001c0c0e0f0702240f0305910803100700d07509c2d07942c4504010034402d10100c0e8180001c203008581e803410325840c04d07500e80010b00b40900b41c0165614400141007250203a1400001c0b000181b1700038041da51043c2c01044c41804461044030080c0c03820740020f16080100403d0b020038480406004155a0803040c020325402001e810742e040d10030f07a011265030040a1042030140d43c002c04c15590389605012018024420651000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 506772176 1250 506770926 506770931
    0x905160c0506040204020c0703080c07170c0f22050a05060a080a0b0109090c1d100512070b13030f08040303031506081503030d110d06090903021002070602070c080f010e01 75
    0x300065001c550035a0090b411039005803150016000c1500d46803d40e00001c1c44200d0001d0b280c40000000241d0000300e0b06414400540c0b4588000c0060301c0c1c1d62010300994002950069808a40c50089440741c811040010885040040045240b003552415034400904582d104117205441c101144130f200036041c124000c02030a88a9950303601152414850911007a80e02d20402c01000301840e83c0300700030070036680401d000c20030041d040340c620141a00d24034200070a0150020316400c005804107a0010160003078038081c7c2c606444e480707a0b45e226070f1014800c0e0003007140210004034100928241c1c64061410691034506501e0007404a420200c0c0f007071508030010700100a4585e0150109a12026084199002c0d40700100400d00c1d40c00b5001c60079503c581043ea078103ca401c40c400251194020340c0b1801d000d559a280080412159071000180050300055008501014103400070a696445284010715100198480900414968026004981046454038680c0c01d0034041e1000d4010640000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 506773426 1250 506772176 506772197
    0xa030e0105070806130c0c0b04050303090c0f06180a08030406050a03060501091a070302150a0911100503130f060f0c031a060a030b010302040e0f040b090105091f0b0a090516 76
    0x40180d02d1100581e145c00f5142c8041e404035610841c104000c46078031800c640700c24100b07847c0858807508111448000352140d2003040e09680340042d180718400002a24445c64203c0004144d4550078035a02c989400811440300090007541c2000148014840c41c0d0fa03690700d6403081080201902c000368451070411403501c00c240040d0310240201c8800805c0300746c0050f40c0f29a246000c0e030401c500441c2c0b10f1920741d422801c011001415410800c04c0d00e02c6014aa8480000300c000c124100098040540c0003c40c1400004e0016088111a81c070181c0110175600201599070780f04402e41e40391800b003294094071042c03d0110250580540038682c1c0340b0b0304000b5221b1000c0c40c0400d0700c50003800045c3c4101611509040a16402030707045a024040f0000b00550340c0c07421801105d80150140c074215404103031a0006050440107100c1d141c05054100c001d404000c0545141d181885c66034000d88043c550744030f110b841c031680c40c0104500100134100d008202031801c0d400da0744094501c0c85141091000307503e503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 506774676 1250 506773426 506773429
    0x10060608090705031b0f090a020d0f090b070e130e0304090c020a201201050a06170f060103080702060415020708010605030a0c050909030708040332030904090312020a030e0105070806 80
    0x40040c201c800306207504502512100004520f11b0154010b5900040c101040c4a5039820a40082c60711200d031307490600014140b1b400c641c049880d9900082c149400d40d0001c94071451045c00ca180403458010491604490ba0840c04001c4403c0d803460080b0543c00020b041100515901811817170f0700450029054105841d00c400030f03c003000120200580c1d001480c0800259913250040c4501d00d6010000c120f40c0c54488821402071009024076408101e004030642c080c07000004002042054081c040d04581c1d1943d95454441d41002d44120391104041c4804180c42601540c02c0b07643c140141d000701a0b59260201042c00c545a0f60812802038002c1c2d020303100420801d51001044070070a0b40c450180e40d643c25011070640c0140c1c00001e00c09000002c0000030b0107002e2501c0c2c0b189803c61824546031000510410b600081100d5004000343c0090020b00400d1502e035212120050080c1410401151145000012a401041b05201003a0354107646041d0341c109108803948110903007880c41c0076082580 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 506775926 1250 506774676 506774683
    0xf06150f010f0815120d020609190c150c0807060507140a09050f04060306020403200307060912110411041703030c030121020a0f0801230a1d1006060809070503 70
    0x1403500040c42205000410107417901601c0c07030300103030304181569019414581e00079290070b41541d00031030718411580b032402d007154280c660300b0115034004078009445107840700b1001c2611083c070700c91040c0031140205c1004103035000300500c5000d11501d0005101c0c40c0250300609109000d012500028105120703449045e50480c1041060302c0040340d81c0000c54003410002130103000f090304010010350001c600007040041041e00451402c0403081200035401c00702040c945e035044a4030458000840e4443c08000c1c490b645004200300501840d8400c1d034440f1580c001c9800d54199400b4929100c200240030000c02c90402101c840310f212070380c0914a5410200029501c5000c103002e8070540a0603460341c14006030b01805290100342e8082d182d112241d54400a460109085218039142542000c0b1100303640e0405040007000c07103031100307000d026940755117000b600240503603c0c801070a1204140c0030824000100200c1d146030083c00c1001c82d0850a2881c0200040006030144081e07500c001000e00040c0c0e07010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 506777176 1250 506775926 506775931
    0x10806070e1c05070b0a0206010e010b0a0909050c090d0804061107152f010605120d02070311060c0f01020a020c09132409050a03030e0304050a0302040e0f06150f010f08 74
    0x7021080d20b07200c960a0103400e01025503c4850300340301c001409417020303402045250486108214680031aa03030f40b44206000c2c0f084404c8540040c1043c0410700c0051a5684815000000c070f407405811301076402c0105003008080c9100b0303505c03086c002c03d003003041562060400c08400600000307050114034140a5124890846103480103004401036543c48400503564128940c1e6001c03403003c002060240f509900038800c6004141c02505d400c81c0741c04a420000402001c2806280d004104403460b54944803081c040340b42101c0c5d4860010004118882010444070320304460500006988008150010b0b1900c40c0d200d403101c1c01b031801c4a04210f40c04d903105001c035940c66080080550042c01040c18251981d01d4150380031245440c24032a4400e20000080c9201e6207846a18200010860032411a54a000314800d940c2e2203100b1810910042c01c0580214038a8000c040888440171440030388103080510884240842c0c040d0401005079510b400b50b1048064042802c00400c01d2000365070041491030300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 506778426 1250 506777176 506777209
    0x12090803091c02090f151f031121150405010e181c0816050306060f0c011407120606030b010c031d060c010905010f020309070312021014010806070e 65
    0x1040715035a00155980d582e6400c02d82c001c01551144c58510141044004141d94014070103070400130707144c11818119444c503000c6410301c50640b4091300309881100603002c28a03076075018440c10310040010312044215810500036490100c20a40380070144400c40da0010303e40f2071301c50340c1404010040da24414003441c1d00322494501046045503089207203854145a504002000700c00f0308460041c10f5440b0340780c0360081903c66400e041540c0702400855050009840150380004108810080c0c00061001800b04680302c1d4008034580c440040e039803440000403070b103140c00b00b08620000e649040f950f2003100007602d010b08007005400480e20000f0b0084525002c01000c1c45450b0b8150480b070b1824001401c40b0044c003c14256590000f4540b43c3d010f018414411261907080c0803003c80080201d0081c0d0788039032902da000b403441c3d9103151100044400389420210550281e02500202450706004166021409042041072545048407a600c0c10000804681c1048100840904a6551100140c088012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 506779676 1250 506778426 506778439
    0x40b030f07090b0a03090b0a0c0219060f050c0c2127040c03150e060f21070914010519050603061503100807080601081213050d0c031209080309 63
    0xc501c101a1094005900039610040020a40410040c1d02d60800b28090b41b040b502d152aa440c1e0410140aa81040d881c1c0005a0401075107000300003000343d245034081e40640d074081580c04005c0000001c0780e000340e0700c0d1010344000003072140c20b180c2c0411640758111804085445005a407180c16402030041150000b0f04040900742007001c03512032141c3d00c1040000420030801c4c01e01007803002d0006c0a50500020140300f46881c0011031454001d007c034841c1780040c02c40284440098200b002855603564804e070b030b04d16008240d1140110400c0800050810200c0014804841c03112141c241c02c0c050380480d1048400e52031862006920007000d01c101c810641d0010b4591300c0700380008201004d0160141caa0740804000c10003045240c1c0703c500100e44603482034030b0003251911032107505d0310001d019021a82c0d001d00c01c400b10340d041c56001888180101030860341540d441c4c2000684d1b0007000003083c0c460710b118010600c14031001140142e5000f0710b60901c0680300785094210341c2c0303c1c00f60161280c450302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 506780926 1250 506779676 506779681
    0x3120f020303090718020d0c030518070506160201050424080f011203031d010c0503150d03140a0915020322060e0d08070209130b09030a1b050c100210050a02040b030f 73
    0x1629a0180e40050106081c2442238002004008000f807008940c54041031002c4040d120003038502180d002c0c2920f9024000f5071401d041106c0d07406c00703224040012410403404110004100d0035490030007240303202d000c2c141070303a01122000007050000050000d4800071800c900401c400c420361880720400941c9410045040041a0100d0804840c9244410299401c0c040c41e088070303e50020056101d6904040041440082e4509000c500140b40c0030050204002049092502c2241e00190003003070003916002c0d034415140c0d05114044509280078102584c00810041045c2c01d88842c0f4003807560f140c6005520399480e0000c01402d0080003603100b406204035002c03920611140c1801c0311601c2d500a81469918140700d404000e0b04c800c03600d000d40300c43c4070b000b000c903083e510084100d889030500360ba19100c018401021044104c0000c0c80c0c120b0306403107111005100b9449120000380c03510810380250040c0071840d082e200980d40c00504c08030100348104018040c4400c41d0341542d42001c40f0188118190303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 506782176 1250 506780926 506780969
    0x812011d161809180311061b0c070302130f1a0102030a21020316020706020c0d0b0a140708011d01030b0a0c090819122c040b0a03120f0203030907 64
    0x14102d03600f1041ca05802c1c90940020041c803034006000e10340c401c2e070380c54150240c1010966101c22080d00e85d19003902031a80d10703140340b00c0c0100190590440e0081590309840e078941c0000d89030255012a0802180c603414041000d102a20130104203200c1e064100503c1780c07820700001d4480c8944994031051003506515813800e0140c02c994880e020030f102800315034031b003440c0b50b01c09114040c0509c8400140f140c030302c000c28207500c049921078009a02030308045840b5807075519520110720043c10a441540da80b11201e140d1507412034054020610b946452043d5410419000d100300301e00324200210041d1403004000040d000821941d10001e10300c40090440114101241c1c1101c107035200350400d2082c0138480f80304801c4258903440c0036100360314080000c580c9080503680703604910f41c4007a84007045508032045c030551128100d07400714001c1c00003c20140b214001800c40d000c5030000d032010710410741522056038000202c0c400d00d8100d03000840c03c40c502420010b41d00c02d00342c041c003030700c0c0c550489002008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 506783426 1250 506782176 506782217
    0x50a0612050a021518010e01141317210307020118050102041805010323070504020417060a0e061303020705090106030209010905100e090408070812011d16 68
    0x605240d500500c030608840c207056640c0c412101c010391140301c41c9203e100c0f400b0b240740b00b12202110703041190100e5810407001901c84580031002c0505010047c20a00c01542d6400c00421401c0c03140e101d0560709600f04101c2c0f1402c0c0f92511040100d50f03000841c21581c4e043c40d00181e00c510718803203028a5030799480b00c01c01c0307025190100002079a002072441d00010040c0c1900900141e60200c02035500740a1420160015610288005052907480140038000e11b8050520400e812011034111080c45e5584c0300881c1c103e0b4880d40c40100c3e00005001d20408485080c0041604084100810300c0030400400c040d5865100190800c0302040401c0c501d881014001d105107c000d2400501070521980e581d0b070090040d500070740d280b600040009a0106403450b100d0740694105425a5448031405a40003d2000c0a5000380041e00c00e03003014070820000824101c02000c1d44402c4c01c14032121545801c10280000e001035902079410110842040160382c0c0d4000d060381d98095610300581104155149000c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 506784676 1250 506783426 506783429
    0xc0c0c091112090c100804050c30120a050c070905040804150306050d0f060c0f2a051b240a0f030f06090c02070501020a1106070503120103060603020906060c07030204050a06 76
    0x100845c18150b00000d840d0405169886140204151440000030b00d00b0412215810088040b1071107880040d40c024542c448296541d4601c03042c1259442070035005070000603001341c0c2c04000014800200c9150328001408046c008225648044c4010309251350b503000076008a00440c800110300e40a010100e52281e08144000c2030064000c0400c00f00364200b24040000405096030035034244103a01d0481403040040d4034480d1401e60383c44011043d204ca5510f1000c4482d698460f0a02001042c1c8000c100e09208408507580c9012050f1203502d220010712103c0300300c6200ca200300c10300c0507803107036081c228000444801282900e82103000000401e0291700070903503400d100e0211340c94544003203981c001039800110308001c580c0895450b40e0f0341e00012079071030400c60001850040c2c4c04601d6601c0f8101000034000c6e103840b039000c1d00d0400c3e900d4410144070000236482958015224242002941445905240c1000701039407251300d043c0c5040101e540d00c8501e0302c0700034011681d81d000603002036810784c403000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 506785926 1250 506784676 506784679
    0x1e0d2019020114030f04170c0d0810030212070306061a0a03020306040f02030f04020a0512251a03012105061513021308190b010b070201120c0c0c091112090c 69
    0x60b03c03820700d860b104000400454003110621f540190500c2e14008083c16141950025801801d000c049030004640004000d04080d00004032410080016914515803002c80205040201521791440c07e0800c240e0b1101d5018070342064211091214a00c111421100c0c9601c8a00340540d483d2203c3c40814014440d04001109032440803060001030822003043e54095402240e103134000c581c560f0304010103040c0c260100315085d0300a02c5c134001c481e0305110411043c4e807100d252429203169119114442030f1911310840f111440004014818413032200c40c0011b0713514894010501d03100003030745c0b4030b0354030040a0302070145168130741d90102c8295241003000701d126a0040c007d54882803c000310713021100c5140035020060080c590080105244031031245a00d540012001040e6440c00c50000500d03886820b0a904022030000018801101402058468000c07503840b0402e12485080c4100b1070840b039044406060700f00442600000b4406007603420305d41d403050111400c1c1d03d60702c9a00c1e1402c80c1d4141c005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 506787176 1250 506785926 506785967
    0x904050a09020f030c0a17150f040507060203070c0902090409060f0e07091125080406110c092a160c1a040506040b09031e0d20190201 59
    0x200d00420140c0101055a2081d02c11599064096042646400556482c503400003d40282040b10300c03846108040d403220b410b0195001940c003110712010b4182304071590340505444806000403c102004808002c0080e840a5030400c80701d81d0740e021105800d845040006034010881e82030995540d84140315903a40a07408200f4074100000c5440640300d41210310885d4080c0140c0040c60700120301808500da989100382074913008180d4450101807400d40c540814906500a1010014260300300400c054401500d030801c607204000350716482c2c140100c0c041402118924103102c80b5400e00c0c01d0f49884124150700d25081303152003850342481c82c0034050103040d2a0080c40031040c142f003c0d10a01c07105840048605203130b0044918200c001d2403182d4801c02d0341001d400c21040140607064006030002c45401800e4a1230701850400c07040c00701e4440c07000d095142d00a0b09650590b65048505109504280b0401c070041c1d800701e10002d0345820503000c0200c0d0f071600382683c1408582c0300303145003e0a0702040c02031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 506788426 1250 506787176 506787181
    0x6020702210115060201150e043311070201091406130e0a0b01180b0307030e01140f060102150408070222060f120803060d050304170f010c11150903090405 68
    0x3242c082c1051a0024441408800002c0344580c418001c14100e4820554075005c45440c000c0391b56100c5100030001d88422101d20356600c170b10690004280e070008100c0510300d00080c21081100100d400710180f001030303074004000b5940180d0300061010105e8a00c00c0d2034200001c01600455124861406d001c20005e503844000708a96103440341d424009d08003107004118200b0110019900c030444140500c501360480d41c002c0042440400c011035004429150104d01c00045501072401c1d11011805850048420020031042d030004800e45584140c00740b0041a1003032710240d521050300c0001c0c00107000d4100000c3c200d07056458603c03152002e16480b400800306407100440c0c01c0300425150040c0b00654280704000101144841d010410302c0d6000072040d451600c1e5842000340e0742c161703818226590b0005110001d801524050306142e41a07600d40540008108440c0450840d400800882c060040c0150340008991000039107180001c00380001003059144c5458162840c0518481d041c1d00500f407804 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 506789676 1250 506788426 506788489
    0x203010b0616060c020606032a060a080402010e04061a0c031b0607090902030106082214150603010603031b0503190f02101b23210901090f06020702 65
    0x3000d26860080d04104141e40113001d04a07221101a580c1551592045154020000b5100c0819143c41c40501039069114034a00c0070650a805c0060f0800100d50f0000400041d960850281030f000c04040700d003005817505021740215402d641d0456120341c441c01180400002000308222491000680d02c40401c00e4669525183c1e5010119030f11380000c0c1c1003910004210700c0d6402502c0c180c407810345450050342d5403501c9280100c2007600505118082c483c6200022404400d0624000c0c03801601400191419400d011541800644058001d81c504038003000231941c0300b000c03c04003501600d16504035444a0820310300c1d40c0101c15400d03075100d03107260f40203d600e504544458500002a001d1314030440340d00301c0c1401100c2406404084104c8142d0903001c107684120401761440301c0080d001c150703280e03030102d60408542204008400c4001da4044501d81480305644d1198000c20840007809010780541c0d40c031007060302c80c440080105802092200c11550744a0b02c54405490700a410720f6808480344 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 506790926 1250 506789676 506789707
    0x40b0d110d020a02071a04060e03100c11010c090b22090e0106060f0f08010b13080708030306210a11040e030307020606190522140106050a09060512060d0203010b06 72
    0x10810161040e07179800030b0140e84c40101480260106e264007401c092078210306442c03044000d09400e80c14011075044003000c10042c0300d20701c100c15095075426441c01144035024216007041c240c0c03105024900f0401c0012000310380403503808070701ea01c409248a48020644403919641600300069040c109071401c0d400d404154000d00071240d4966031880c0e02c01c1107000a42d14600c0c902503403000106003800520a00c001400240b16071440c0c05100c1d90ba007a92a43d01600f41902900015100e820001c2401410319100c0080c00e6100510382d12006d034817140328a03003603441003440001030040f4100c0401022a544680c0700e034002007915800c0c3c9036249001e9600a4840104407034041c4507030f0640101e024800c036901d00040070f0360005852800007418945681d0544190990503a0850361a01d0001c4e048803000724403d130007000562202a1500142403000d481d6420326000b00081180a200300721041c204050040d8014100b6101904403e04500201340584010041c171074020300005441408940741c0e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 506792176 1250 506790926 506790937
    0x18050c04050a0506030a120219050c0307091401090c05041d07090b090d0807060608011103160216060309150c090806060a080a0b09160f060e03010c05040b0d110d02 72
    0x110340c01c205a079501680d0000301c40e0150780a80d0581d1080c4003143c0083c17001004e28050744c0d80ca00450352001040842c100c45050b0400781210a80c0007403001c0200341c00c0030450701c409000b0b101c2007403006004800e940c0300e100c88144120b503503c903183c1c40405129401442110007402440b0317900e12003060004880080c0d403100740c0c0c040d000100490400901e101910081e00e02010300180401900d100c513440360b480c02d8102d01e200340c0343c0030f503200e4000610010074460f02d07030883d0041c0c408903264900103a11170015101c2602c09410b640200071808a032500e1411a87c003036803101e0900190441e02c505001c5c4682c10300c0b0310899141071030004180c4206030800101012650700781e0071103145982e02801d0100a001c123205600c12071748081820400504000d80d40d907804000c000440382d5920300607800d604520b2841e07000482e0514010400e11031103a01c4092908040003d03002407041058138000200315208038803d1405118010510051007101c54100c0d2000d5000c4206a545581d54425050020741c000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 506793426 1250 506792176 506792179
    0xd0905130606090b0a110a031e0201060303090302091801110c0706021c030908070501110702010e241b070306020406080f01030803060d020f060a080a1a0d110418050c 73
    0x300d0118a50880d414040c1000342c0300142e80d1040500c1c50903d0b00d084130f4001d81e8882c0c1c00d0000041405504410800032080b00501955401444108540047c040c408000141c10116410410240080381e005200c84003101d40c19609090260344144144003072010f040f030312800650030030040380d401f8401d00018250860342d84080d00e4000703a40d00c00a99690b80200540c800044a00c45810141070113580000d4600c0d002c2d0140601e06201684e8090031503844150031801c1c000c000c1605419540d10a031030114648043d1540d841c5444011401111102042200c07401c5801c0020540140200442174140c0030130081c00b15079403903850380f400b0400703500070f402841b00142d507690000703403d0003421f40c1580c1240e0300302c074540d85140c80d50414803c0d664075030308090303800511240c3c0b04130b000e40310a0014a40c00410b030791898050704180040303106441501055190541e070f98240010f13640d40344800070031b50f00d510101c104505d09541700410040d000d00c0b070801d1041d40c0480022401d010000c40c0d4481c06510 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 506794676 1250 506793426 506793439
    0x4030e090901090209160e1002030906070602030709090203040b0f100807030804090f06050a061227060e0c0f04020903010e0f0601150c0c0905070e0402041e0b190c0c03050d0905 78
    0x2201316448080c5d0b13994151000020b8aa0001c42c071240c20055888c01e00134086105583c544041c40d40071801ca03030310030401280c4c4544e00201b00181c056108800c400a0207480e5019455420151115080308902910761101c0000c0100424110110f003d01c0310003e2032580255039110740e40e401c3c0002e0580151155000c220704214024041c2d400d0341c4a00d000b0307100000c0c000200d940c00c00c4001ca41d0030400e08000c682e4155586030020814282d900d0f405039480c901e10510f40d08503c103180040035114501010800d90380038801e9a422584c0782c0000c03040c2c0403010390b40162110701c01c600080c05400040a1000c50b80601982d1010008002c20341c07505949c4c0614580f8a0745034808001c80c5d10f1100b802c00030344490502e000c03d03c010001c50701300301c3c2c001c0c40a2400500d11354680300001d04a82c440d602604070300f440e4403c1420100794904503580107041c4104a5810407071101e40c1e02a10b00e50105804042250b40c0b08032800300003c4c20b4032400910b4010049030148400d2100103842c4049501440d0322500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 506795926 1250 506794676 506794681
    0x11205010e0102070c180f050f061008040b0a021c02041202180609040b1e0711010b0105090a031e06020706050106030e21030a0e10020415090f030b04030e090901090209 74
    0x905000300e40c21517903c951480105464041400150514006c0845030306032030b08007240c00940c5c01e0048a0003001008415401070500104014180d001c01c662002031000c258100b1020035144403030154404018070025070303500c01e288a11258030f0724507c0c110302030620101300800c592034540c50f064009803003618048119100614510f10500040328026404000d0400040014010003501900814804601600103a440c2004d004209040301c144e00022192005031411103800d0007942d01d8040c3c02c0c03d20300e02c0c1688120219459421a00018001c80b04900031108610b0354003072038004a0707070450340454130b640062910901401c0700b071140d8000241003000500c200d41380485c0d484103c0ca41d4481ca000e850301e58241891064100500c0b40c3d1040355180f2044201c070505004050012007201401030740c0c0ea0030705013106c0c10000b406180320204201c14905100600c04500044141e03030b004120908296940c2c0b0301140c0c031101c406500d503003290546091202e1800150082074009100301e40c00522503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 506797176 1250 506795926 506795951
    0x303070611031012050703060f090f1202060115140901140a080402040b0402091806151b070e09030d0906020f0f030612030906070605060604090203010b03011502120405040b040b030601120501 84
    0x103400c13000026040307420414080001580982c031000414407010808038031405070b9110b20b4030764a0b09240550721700071190000f03001d8603410701c00103002d00108a001405644120401464403072070b100304459461000443c1c2901d603001d40f90784030224001c103860b950765080d410001003148100781c1c0c049000320b041404034419480c06000b51a88610007404002c01450301e81e445034403042020344801e4029001d10060b0f507004c03020b64001c25a047c800194020040410310390301d0302d08502d03544024200340c405024041ca11b0030120445065182811000c90600e0b247c0c2407400c000d126107560b041e40c6030300c0020607a10210300c441c040e600c205800c540c00c003100641406000d46170b101d000045507010800f003100500052180d030110350801c0000d0100341c1001e0f1140000f008030392080e00116481a008001009814000004120800b010f440640004003420340348030400d002d6400b880703214584908a4001c1500c0700d51000a841400404517032103540d41c1d040e06940810204001c2ea055401d050419201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 506798426 1250 506797176 506797199
    0x20c100b0612061e09090a05160b07020618040603030905030d0c0b06151210170f0318041808030702010627021b030c010c08070c030f0e03030706110310 67
    0x10705a00041000e05640f0401080801802c10100d6141100003a07200c004680311644003512405071540180041011400c22a00e080f40c2030071002216030102d4800d1280000c0c0a042c0da07103e544c10744a09490b610340c0a00c07500c84140410000341c2081c5480c00010615900400304030441b001a02500c200707401a42c811240008010700103048201c00401003583c9080070106208546001e084050400c00c00d6003c2c8940b682094070000558003000d00280040303928031603181c5d40c2c00c0f0007030014200192400d442a417640101c015284100e81501c20300030300b5485940041a682d045c0c80365562000502745080c1241d500191400c10040d80380180c0030030a8001042c0c060744051341d108034400d400e04c0d04009403001c0c1d03002049003c6c1690f8002c08107569024100060114509540008540c0310a80f0b40d00500c540b0000b0855020001e83c101642c0c0481c0d00300c0f0059841d080c00e0b04c0c02401d15000c07040464070350b02c00c140d0300030100e9107801503206d1940f0242000c4c500500781c0303002040505580701000c0a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 506799676 1250 506798426 506798437
    0x6050c120a1a1005120a0218030307030c0618080d0e010b030304050a030b06030c0a080c011d010c0f0c0f180e03090907030b040902060a0806031005160c02060409020c100b06 76
    0x2107400507201c00c080301e1814400c1d94801000030314095162004035940d000140ca0146d41103940290040313030040510329596144003202d54243c0045041025a480041890300034143c0548542e40c0c070407164807002c1200c035a81754000e0308a151641d071400712190751002006003241d00d2040e54a402c90804003460040100d030100c0700300030142c24150f030441e02c0d0440365800107450305130f15102d1040d282d45d0607240d1741d00e440c004140c05400390461810b0b038070000d84040c800d80e0402c406002022044092680c00000c074040340354020711080d4030000c261415080365091034100e1400c403402ca400000e005e9000707a180f10760401c5206d809102d14000341c04040c1ea40e0040c0840030764003d0384040007840c4644241d10001400c00000c1000c140301c43c0d01d0700800c0c0303140d01a601c0038000543c0319080010741d05041103094480e0a0114042206140811032030030b039010f00c0f0318800100100c08020b481590354600949024082c060421513a0711650300c00b16680b0b8008201ea02c0c040e60604c04e00d040386241c000c0070b0341e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 506800926 1250 506799676 506799701
    0x503030709050f0a0501110c090106050c0606040207080d0207030905031609140601020d0f02070909060f0b010e0901141504120203150103031e170c0307090b041511030706050c120a 79
    0x44c14941007800654103000c40000201940c424403061415594628804074004d164a8445960b1507407000741d07041c20100014199805580100213940019400d50101c40f48003580523401a1100700a280441b100041940040e0703041c030035608814400f250002000084445522042020310002400521201c004507180b50141e04014441c480c024000c29503500280d00310b1040c1c954560700d90100c5021181c0c110410340c0c9140d503420540740241103602c00c9011070f08007402c04807000842c0e80000351480805004015a07401c0c92030345105562220510a5a5515600000c644460f01c682158a441d030181030309900ca07105004060801184540720203040e00d4069407210a4410b24140c0700791410241c54016040056100103404240d442000c0c5500074800519080d54909081d0300041640e0a00c0c0c000300e42d840340400040204c03c80b84442c07600300c0741090030a03d604400d281000c1d800c7d802404c00280141d4100820042c0d400c14950003003407501108440a801610303502c45140407112040b0300003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 506802176 1250 506800926 506800939
    0x311010606031e020306030f0304030303090b090a050d0302091302040e07080f040b270a050d0e06040f05090403260a180b18121303060b010521090313030503030709050f 74
    0x40100303c0c5150011a480036010f01203611a04800c5029482c2d80d010341d000750002592850b01200700300c0b9035040c030750300150100000d00744030b041d07500e03031986030708016840c4020f050b40000e4074995600c4040e148051041c1c042411521540da0718101507004c40c0488006001914280005181c0b8640c3d9070076500030740e007241d900c01640c0d855504e82d41c40c60710a6408154206510126242d01140800640c0a154421b40203410302c2e080c00e540242000b203112404a11901081c0410700480c0c803824003000445001711210030b5251100c6c00c0a98166909000002c030440c450380c00f60a4a903510ac1c0468015030641804010441c00c044035800b1401002600420a40495010400b0b007a000b0303054005c4400320a0546103500c51040d003010165200101480060384406020410f2004078480c50002c28001e00300b282c03800e60040340c1c00c552519030944010031044058046070240c0d40c200181d42c528641c000c4040c580580381c0c10110360700c1c0c0003100e5010009107441008122030030854030090900348082c061 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 506803426 1250 506802176 506802221
    0x1404050f0a0b0d06020315040e060106020a1509080a020a0b0604021c051b160b0a020f040e07030e160302130605031b0316030b0612060906060f04090609031101060603 73
    0x5a809800741002550388248010083c0b00400c00302c0c4000c42c052a0880070b08440658080180020b0340c20980d09002c56400442c0108451600400c09648007540a0401e144a50001c0002c00007000390040190a80c0c4000c00d14070441034001402580300741c083d1038403410070350fa24410001684903a00e1501c81041c0c0c0a003c3c25001d40103500210307003043c3d1001d4032451044610202d103506810444001c2d20004c4002d140782c007485100070116400030f0f40e0840c10f614142801d890000540301c1e030312801c4841c601010000341f0217440b0b075101d0307844440da400503100b04444460510403510a94001070384a400304125a14994225100e0325080b2280a0060800703529001e6155032250080d0034003d40501a8442e40f85400c003c00000d20302540c0b00303008413a40d030f09040c8180a049c0f4810400356109901c100c05000d4913140000314158802000c440c21007a02d0550408540038204414000b4005400c05c5442020580c000070701d0342c4810604070007001070541d81d5900310705031199104116039010003010b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 506804676 1250 506803426 506803441
    0x3010f15050d1814061e10030f02060c0d1205180a170d050901020309060c030405073f02030d030c1d060909090c040c0e010806010c1502040b041404050f 67
    0x140600241e0f05010031201c80403611181503044404009074010303005401080103010700c0c40c131042041032560405040d1490214600384a00c41070340409014105508100b204646e152821140c0e0400c40034140c070450b0200395800707484a80c0715000440c5450800740012519401c010403981e0880c6000c00508501c405034803404910f240f5100345003c203030b41c10454554035401501549004a070074100059903480c01c5074400d410000c01400005415004209020100700c0000f549400d41e96100002d41d64180d03c0240652801292011110103070f00000a200c80d00b5280c200172090f980c029010b076940074048110840455130491123407404a0b0020381d881006140103030303118808103030180c074080c40d1591080c0018003080d4104c83e0710310194844180302030141401d005098004050382082c04400d10100b001801c5040000d000c0c50410410341f29180901c1a2140e0030343d07201d02480d00465407a07450f403135051095842405040242003100f010306009061910545100d201ca031448036000f500d4140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 506805926 1250 506804676 506804681
    0x314061e030f031308070b211e0702010912021f0b310605060306150304150c0903020102120310050d081e0405120a02010818010908030a0203010f15050d 67
    0x39456070184603030488946030507030400c010310116048442030f0382258079018100d840c043c45a004107006800a1100c81e00039481d4800c183d0405002410390000343d0740e0104400f102404a9500d245403445030000e011807143c0644c0007802d414050740c54203400c210007e1040e42d031030840d4440034405129a1040286e125015030180014400080540710b01b10b02d90740c5030f840300c100e1400059042d03026142400310010054400e1400030401503494500b94030b400b4001941300b12083c80002d082503000130000382000010403003441e4840d64004c0c02c00a1110030b920003040181ca501040f8054031880080c5400c440b2140e040d03d10a010300c01031801200d00344030602006045c2840c084804030402c0c028072058495504107010300701c4040071000d403107901c1e0104100c6200c103031034020007080d00882e102d81d0243c2d034440a0143d10600280624903034034264031043d80103150700d0a0180c010407010040c407026465580045040300e0580840f0014103850711441269801c0e004a0403010403010001c0310600d81d0141c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 506807176 1250 506805926 506805979
    0x2090604090f02040507020303100801060806220507032906091b040b030a23070c030809071206020a0314161d03030a020115090605060409020904092001031406 70
    0xd030940c80540b4240e5000c5400d540c0240e91144c05608040100070541c1314400084009207034010003402000c1c079089000b0388842024050f2801401e1941029800d883c410710034042d42a4040c04441d007c1e543c0e03007040e036440104000f440151800c4074a00611001161100a02980b0020134401c8a038444110040d24040d418008107403c0d1024040040d101401c03d0142d841403402c10b9002c1100508504d00130782d9444080c4c50a68107640c12401c0c8145c2c82e50201070580c0599150070500d01a485443d500351414420f0f0b80b01078044402101410108000340d0007808803003603280c0302440781101803080c45d802040200c03440400341c0794081421206610030080161600c0001300304c0003c480c111800302e400c43d4002e61640001d40e44401e408018000082c6108004200204080081d40e0904000030702d60b209901c9102200c54010a80b01c545649036132098605551140b90752040f03080f010a010110071402c42c0060101e0b142071200d00402d040b80d640315101b0340d0b008000710345c0201d000950541c2282c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 506808426 1250 506807176 506807183
    0x30414031f0504150c080f06040e07080106051206040206030a020703051218060c13060c060605030a14060a090201140c01060515070c08030901141c020d09020f01020a0209060409 78
    0x8400800799141d50200348a48480c10000c00402d05141c00e043c84101c2c4c1420b0f00500d0440b84c90800c8040800b54002c5110350040308200031200395403512070008000d017525080c4446c0b2030045100c00a1020750540c4280f0031a0300c2030f0351843c0d01040750641c2c0ca0306c400d8100c8011350018810000070309608441d900809070380d80b0a04106040c100900803040031503004a03681008078007200504a11928100680c641c0712088890b0303140b80c02405c07040f46c448003003244070701028014075000200030000942c0200001d45000350803100359000f107050140240c80350b0080307031040d80501c20106107500034078000e02c50542d80684030710842d00f0007250254441c3d4400080d810542d542c50201180d01e9444610241e2001c0d030101010f03490f6412414000a045541e42c044c0480368010071641300b03180d030080c042c1c407031280502802a85a070344080c40010022500c1c4003d80c1c0862002461b4a05140e0a520a41010707000384d580401103040d101c0166582d9205001c041d6005a00310001006807a00390002c0e880e0710721 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 506809676 1250 506808426 506808433
    0x31507050c0d03050108100b0f0d0f05120403020a0b040b1c0e2b110c0904080f0408070e0a0c090306020c030c10020702010228111c05011e0e03041403 66
    0x203664007420714104004202c0043c0d02c0720010040030408005d041c2861000c0c074800c1181d0b920b01c000042c564040c0441845c0101c500302d20304001c3c000203002903072103917070808180c403219884403828203010780c000d00040b4841c2000350303000326403940d480c425101601c42c08801149040501d11004407005009030b0074019207905d41111940f109001d0200300015000308042c00d032034000c2106000c204040180c000760402200142030050140c0010b201c41075540241c41d128415280e5040c00c5009101d21000b03102c1403440000e0019103240b002a01500702c622000c24151152aa44d09050544034801800000940c582c00e040c400710f1030340d6005200812240b01140e01c1c150722824081d0505803a42e207a100c695074041030400665806008001400743c5005990800b804441c400401d2512240005020030070040a103014030b46588100440803540c11210107100a0585006406800c143da807031001d1080c8481e1f400806001806020060291080958246818200812501c09005a21551510 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 506810926 1250 506809676 506809687
    0x5060a08030f041809020d05071a09180c1207020d1205010e0a1104091514011106040807020f0913060c02030903030a080c0409021914090a05010315050909010e0f070503150705 77
    0x1d652400307d010992203103014010003840c0002d00c0c10a481c1c500c4110404842c10055003d032950303040c03240e05400c100300c1108000b076120850240e580703000d004040c5101d2002182480400f0b46c00168000c50010f02742d40309411060303010081c3d010b0712000c0c46102030381c4600c400810814a10341d040320907090074482c00345007000d90b2206484140d40805500b2540c5854101080c86040510008442d682c030007820058016030a0480300747e55003000a0018180b0314021420208554540381002428807005010080c54200381050410b003040313003001200c0320307840e000c0e44412090021080c0c03005038000801442c24401403a405540d48903009085050a017003c02c00450040c040c0c1c4081e05c016400e50082c1c9100d801c0444019108a281600c400031250052000c05203035505c44140301c050300e00a18001c81d00d40010380c500401e400040c1c01c0b80d54031980c01030805c1201401540a13030401c2c0d0400040710008810151502d481b50141c0c0186034054100700d0500c00c050310000c84a54221010707180c002d1504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 506812176 1250 506810926 506810929
    0x181d0a0302070858120e060402061b010b04110c0d090b0307050a090e070201020a1d130b0607060f200301050607110d06150513020c0a1509140105060a08030f04180902 73
    0x30711102422034081401041380e40c090000f6032260070307130b0440400003d0547c4d003055000030712079005040504400121948026010040a4200115440e000b906c00d01104000d04004491a04160b0b0b0580b0395108880300f110201b072051121a0498031840c69080c610b881e503040484296101d04696000c3c8884034800044510944102a10511003030b07000580701e00c4c448000508640200400548101001c5032440d5241d4a11101e00450030002031700003804001000814058002c02d180580307200d15000d154000d848080d00a5080380c4c42c01c0c030385842c91040040340501c45000a004541e00181c090086400148864424220b00310b0000d0100f18400425036411081e03030141c001c9050f8a80c2004000c010606124010107210446003c055061403603542060b541c40c1c03255607016281300303428001407249030030507400302c0e081c1d54008400c00003da01d4003e0060207030609803001c07070140021050005811101200751a80b401d5186603441c5454902882500e00b105a840d02e10145640c0f010320f00d005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 506813426 1250 506812176 506812333
    0x30b06280201060302120d030507050415030228080a1b051b0715051210050f0d11060f130e06030a0b19050f0a06050406181d0a03020708 60
    0x40400301030003007c0f036120090340101516800707889101801406d02050001022103404c030ba940e03440c03134a001600e51910700000f44044000003030307154444405a40096410754040c9685202d880304000c14044070708208010081c14540c04226400180e0500652480e200410307191003c04200600701da9042d0784413040c0340100014400c11001150b80040c005a00507030307055602e944944100d00034610640b030440030030112011102084d120300310000000003040900292100d01c980040c28403603ca0b0341000304004c080d8400d0091681420003884009040b042040806100c1c8a011700034080801c000c0d5641504c905002e00101800c054808070000410300702d1080c0342c80354490310740b60880346c10000040c004a0310150451405141003080038032240704d110300918020200d1007070024081454021f0139039180185d00c1040003900905100760141a0b0016040c0e0640394848140c4040346800e240c580312000a0103092209520044103204000726402902c0d1010400c483c00f0038202c2d200c05a9078200c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 506814676 1250 506813426 506813449
    0x60905071508070206130602071a09031806040f05060a0201090516090b0916050c030408030d0501060807030b090408070f06050f0106091e090e0f0a03020d030b06280201060302 77
    0x14140311501c028948a611400c800d811801034000fa10541c10419541d8521241c4000041c0c070b03d9030006040c204010003540c500c403440c50801c007043d10500380701b1034070342c1c0702d512812284166404804204009142100841c1c040320035030000602100d15250520189401c132180314020f40d56100400c801080301404518040480c001c0000c040c1802c1004c800101d584020015001d584044104040c3c55848980c280b85444d1500b06691554148038006256201d1030308903040600010940b5844840349411050603148551610741482d80c5e88141141200c2d100312001d075015100d40041004200008010f00072140aa014140007040940303d44003542d406441c0507508601750001003200742c0d844408800030382402c2000d01110005601c4c0390308407401c40c0c0200600c140d80d0301c0742d60b150060308003d4000030200c200103607a02201203050203521100a01032040201c0d003030844901140c40d01c1070441d40260f5684807852a000691a8140701e1404a050300109541d038881c0f000c40580e5800100c0700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 506815926 1250 506814676 506814689
    0x80c0f04110f2a0a030f18030510020705060903070c060c0f0204051003050d020a081b0f0f0115140d0f140307050a021c050d0503090715110114060f010c06090507 71
    0x240d000407a5212407030712400c240103c2e00c107404c62454500000e40c00f2100d6035a0050600d40300f0341103210200b15404940d40d55100401620910040e21180d0380c994001d013010074040d00554080384e40d002c03081c689034403a507040180f807142004014043c0078080c80641c44814082d201c560342d610b0003a0b0100303003140c80581d41e0140003800c3c00400c100b0000304010b02902120b00d0310140c1011082030303441d01541d008841d030001100c0443d600082980008000f202c03106030741d0b11308a44240500c03151180c000c00002d800c80e110038050f044040b0b10600350700b101500d4004050a00491042952220f90140004501c00c85810302c3d10640505404010405440202d000d0303000307400004941c0c810028640d07200458180f83c0c0d008a171320903000c100040340c0d08034200c643c0c1c24501e40d25980d81c14401d04010141c1c00c46800c64044800c9014404d5104001c030540c410188000c00808410140092011004440351580b0000d5540c00c83d0241d4451b00013000014400d01000c08e000c102c950f2080e040001641064 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 506817176 1250 506815926 506815957
    0x5131a0109211e0302030d05010902040f09021602030a08041a03011d18161404050f0103080a0c060612140f03040b07022202070209130b07030504081204030206060406080c0f04110f 79
    0x1404d1004079108140c01462b00550441ca0700349010308083e080744c01e0344142242030340e010429405104056143c2440b00d580102900c0d124926850040d6841e0000d000300c8100f4907a4248407003c00780100e04413410b952600c0000e802d05403066550030340c040d00c010081524544180250728122408203d0b42c0c0d81401d80d15860003c0ca401c1130480c40800624081151040b41404288200c03100c0c6ca120080c1540d401160f11669142276600503151403003145001040b4030310708900058a44040b99010880c03911544076242203442204a07941c0e03d0700100c0c08400380d504100420006d0280d10001070002c280701601d0000e610740340503400c1d04c03445120201e0f0b500311500050004210324010849990041c0e0f80e90401e008c4035220780b00c01507581001407640051594070400302e001e2000c51001d540e00c9072940d0240020038a05450000d48400301a41d8950046080c141c0c0800c961030301007688424004050920404680b0700d40400001d40400003e41c5203403181000710240422103000144042008803054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 506818426 1250 506817176 506817187
    0x30c0c030b07020f0703080a1803150203060f03160e10051806041b120504080403120f0815030613030c05030c070302010e15091905131a0109211e030203 67
    0x70b82092803000303c134049900454014000609800c0640f200800a0303d000240161200b0340f04036888800d810103403915500180101c0c001c00190000d6210b24020703911860321035000030a240d50b8440c0400e039140c1c0c50302a080c050026504220b00701360b1140c0740b440c0c907800340707982c801c04074034031480199491960340801c00800c2030508041c058070038240c1103910700032042d4080442c0200701c0b4030a088003490190300d0302c004c20188011102501c0c055900f2441c10319990f1810f035000780920b50b401c100f41000c540020005520b03c1718120845002210140103030920356500490360264495200044007848980c91000c800306204201030899404101c000340300103800c3d80000b42016400030301943c4200c008a035580c0200000780c06464003503409442483d003105280c80348284101180d00050b0300100484803030414000d20b40c0000881301c62848001d801800c0c1d8030011190b0311510b003d825080f0460510080c507140481c058502c0650291400821040541e01041c2c0c84081c0c1140940060344003180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 506819676 1250 506818426 506818441
    0x5040506010b0403030f0e0f0418020910140f03100c0f1106041a060f091302011b0b0f0a0623030d03140a0209030f121c05070e0409030c0c030b 63
    0x2030301e0141160000541c03c1a282d550000c2c10800001440c10422011021a9806480c0c03009851400d1000034030a000c0c560340750380c207520f10060805060717120754604004a0900c140c003070b4002c025541070721241200034010405004c450810900520780510030880c8140842c0e41911418243c82c0c4540c0d582e03103903070055040040c00c8400f0845441020740118062100051070058a00a0415100400c032142d540e100c0002e000345210014540d0040c1e040c00400c0070b0268444102001540b01b602e0f1079101854085e034076103205c200103400500d042502808035490502c003400ca1075101003e008003040558541000158401c4c4a103158036102c1050380024074903190a00603444007101c0c0780740402909021132520550b0900140c8404441d86d40024800d5582e2802c2c054107041a560341c04075091002c005988101070f5000c00800c00e1099441144006034a00302c1c020719005d441c8982c0d0b101c0b02c6218440030030008020141e000c4080c01919948140050b44c0e8494072030086008010b00d44591501c002d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 506820926 1250 506819676 506819683
    0x3020a15200a02090c0c06041209090219030518070b0a0e042904290f01020307030c1b080607030b01122d18050d03060f1d0603010f0f050405 62
    0x384114034558401d01590100d0000701103180b01d404540400d01501d40808507600c03885a04181d4031180602e41c2000207000e40f042c449042a07031280d0395550069980c248490890051280300000c2000c000e100050b82e520a801140d04a0740051081800507101c2c136507140307002130950040b01c440c1c0c400b02d04582c3c520f4000d040e1b100c12103402d43e802d02c030a0700003032030500c0e8207080b0300641d400001c0741440490031510345500c40d0041c1012843e60688114009206540c1500681d0304144a00c02c02c40c000c840079403000c0f003507030f90856141e08da01d550100c503a520075031070b407003c1103c01d000031652030400078030600e040045038020036a0751030000d16040030000040181c450341c2c1051010608110540410b0400003002c01c0386546030811130a01c0c45507046100c0c0c00b40411100c065500c0044c0701c041020700a001c034a15800c1c80140e20101b10070740c1e882c0344010076541c06104208894058002520b40401c00000c400d500c6035004000145111401000303004030354940054640040d901c0042200b080007c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 506822176 1250 506820926 506820947
    0x6090f0314031303140d0806030d031a120c12070305060c0307020c04050106030518070503191505190c0206010501210608030a0c02040f0509030f07030c08071a0708010501050f07030903020a15 84
    0xe01d0500d04920f44a0003080cac1d5561402900800c05940c0c00c44904030b001c48595031440c92000405c422000380100e00529540d8078085500c2e4442c101d00ca03a100149180000c200c0112076116019204980d0703226000d02668100902201c1580101d5108440540d80c600c00c02d4041c2c031ba81c2e100024181058851081d0347c22496030302c9106640104010300c400e03500060103100050031030b1f4160a50480d149440100304092101e0304240f40c3c01d0905110001c0d6200d844598034000d1f002041042ca515648101e07580d0304284a500d0120302c100c51040308245e104030f04c0300000c205101d00803070420350b04c0a000b0300d551710a0454030002501d24654000710318081c0640380807142002001d10960074813681030354a0b407042002840c0310b4440040c0420405009001032050381d60852200e81d1146100d042020b84c030300d4200c0d1114062103800303000034906401000d13098140d641c1a540c0c1401c2c0009802c0c1400f1a5100181c158284140d1a0001005a868009207401380980065070341420301b60120250590310070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 506823426 1250 506822176 506822203
    0x408100e1b03070b0f07050102070804170102070c0303110a150218090c0301062a0f020f04050417031e090c04050105031504081606050711060106090f031403130314 72
    0x10034054074016076000541c4416602c06082050f610500d00300807002e94483e030080101294004180e1400748498200a0012541340b040c506414014140d030703031400c030700c22604018500c000f000d4040c40071a1041003204841d040e910101d500d0010640c0300c0440c4040d410841650150f00050b500c03001084048010070710200c29615401217082c861481d0300c060005005d83c008000f124074500c00703100040c03811000400c404038a04042200c20381405003402c0b5403203500b039003e0385c0700341da0004c1079050511605111304d40000060400c044401507194080e8400741202d5810318111030059012203001c404240104841c00003401807050b60030500c0260340b4140c2c0064443d4100c0b04041c40362801038151260b1140c2d00c481301503500c21081403000c450501019001e020306280004108010703070060003445004017014101c52090b83c0e140d008a0307642c0001e00032008100b000903000c100268280c10010140d00050054a0a280103c0d101082551b9168801c0d40e00d40c0003c0c580c0340d4072503018440700e07400601 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 506824676 1250 506823426 506823463
    0x10051e031e0406051602070819020105070c12030813030509010e0103270b0106050c0a03050915031801050907060f050c0114090a0c050118172a09010902190809030408100e 75
    0x107030007241601c0e2001803015071100c40c09d0b200b4007006c580c4100111440c5030b41c829041c0040e84d8880c000c041c2c000ca10008200c0110b07006002050361884440c5886564030703410369504c0c4c601072180c030044401741c0301401d03164141516102c090600114a2030002c103107100c81f102c10300d0a02e545082c20441604180d000409222081001200034400415600052901814001e94a490401c049501d08604458050000e1404010302040c4800203588088041920000b4459512400011a240d14440c0300321404a100403d50b20810b500070005032006907650400059902c2e41c1c030400e0016681c040f1224138032078204075211010041e610304107002500081c41e29002c8507006104200a039030301801084902c0e1090716060030703200001c0001800001d090603904030381550248140d1a00942c00010b5480350203c0e50004c559214a44242c3d480d05040510000520804c0c12080c1c8544c0070190071300c45180000c110121344050700f009041002030f03504034001001da210135000345c24600794456040c102c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 506825926 1250 506824676 506824679
    0x220c03061e29040507021c05190309120f020606040b030a0230010e030304140c040c11010b090c040504090f0f03081503161e030c0803040510051e031e040605160207 72
    0x2640007400481f05001e450a804440020820aa42d54020b0f0310b02d070211054464400814160705030081c451107403181d80003070010490007005594450038014000d0040e481000040c010f480e090300031612030040a825034058907a181c0100d403003011203042440071107860070400c20742900d6540c05404042e0700d11008010394140101c6094892001070800381c910000303c201e92090703120511000e02003800c0100104074503400c1e01809480200d4078081070a640d442c1c00001c00c41414003941c1e00d44152205200c02d4a81410711041100a0001030380985403108204054400220481e0001090500903150304601e450454007200c0344003102956240203401c0513501c086072000a0800c40143c0d82042007140c3d101b48503401d0100e55410950001d40b0f003400b000d000081d040070100090040e81d009883c60b080e13424602005807264444c44680001d000c81c95200c0803007110456003e541c010102c4035100d004503800180c40c0340f007010150340942c1d2859540e81880b040f03459203540000c01c41c0550002c0c04009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 506827176 1250 506825926 506825941
    0x12907050d08071106070207030b090d02060c0a0302070206130e060a031101032f13050901030302190206070b040b1e150f030304030b040803220c03061e290405 70
    0x46a08015403020301c1081004183c42c180079095000314880304400701e80c150724281790001c0d510072071071205030750404018004c80c101c4400819a00c003003080304d0300141069101d050b010030459000450280805509001031801030780c13080010502c45c0e035000901d03264542000760300715208201401d041e20461140310f080000580741c801c643c1c1d00f4002420002420841d40101420b1b034130045819491610040844940705064000a07103042c009a000181a103510384c406c0c800307045020300001d030150340500e44071003aa440c0901182e1045101034101030802c0c103a079582d9503030340000ba502100c110a1000030009c1140d82c14052010b1890b01282840c00c604044400c01e2132008000181c03402125640440c3d040354030200220f40056500a0301d0110900c2c0030f00b051055600140e0780740c079501c102c20700c1e01e407042c0000c11003400c02039410100510840380340d503441e50024800507a0005521882040d0050540124803882c014240428440c0d4151132003902e2601700c01032400b128a04c118940720901409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 506828426 1250 506827176 506827183
    0x3020123040615050301050915090604050303012304050c0a0809120d11040b131e05060d0c02160b0d0c08130b0c120a06050a0501170a1d01020301290705 67
    0xd42c100c600058444140d0241242409058100e50740641c04d000a1041e11a030000303080e04003c0e18a80050700715280d86ea091031715803009440103003841c1c0c0240014410441c0240c45540e080300203003180a080c031000c0d40407800360748089a544010f5030001c1203054420341c11854407a403000c50840985a0300803400d68407086405185aa81000c5a80740130769004100d0901c1120040e00703030440c07441e440318104040c041c840c00c020700590380032118a6110307107000e800104981040e03800040803281014094010b40d801803010f1100001140700301c4030485620a004030a0310081c0c100070f100b079659040303030850440984003100020785c108003441c0304005eaa01807000404640640c45080589280c035a07130b414002078041d1260030b412501019085c41510780440d406641200d405481040b0001d41d101c0044d512280102010903042d19008005131400d092a4403401503503100c458004009400032030780d0350890708240c000310201c14450b81c01039200225940501270700c01494500500e403900315628640c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 506829676 1250 506828426 506828431
    0x8030c07031106040906030609050d11060a0b1c03020f0715020a060c02030714030301080d08060108060f1311031005030a02240f030f041106030702071a0f0a02070303020123 76
    0x4080070311803150682e595084100d40c02861a81001e000094803401c0c0303030000f40700f000310444103403180300070b565102809441000f4a4114110180c4010794400b40c25602a110002c9096400006080b0340c0144400c0c078020250018080e900403c0320b41c0c00d141c031075403074400250002c80070400054144003070142d0004414002d1648140040781420101b8410fa20b14080c6e2003005003401d80e040d84480004c04d001000c0c50485652004032940031300d40d40c030f05407540d003016074040d070000350741d180040d50904100d11010201000508405200c503c152001c0c02124810358010404c21000000d001c075281d070b001d8008014117811800b61004d80c0403070380020038002100080881094a14002c000e101d04804192000603451140d0b0a941c0d103000c00b0316201d5a03004036400c035140040c0f0400c140701f41c10500c09aa03c5600245c0003080c01a04000b5201c0e40f0042c030200700d100e42d1008202c200c0c0c140d8052400340c0300301c206076001000304500350319000c2c2c20b4418512070b6111908800000012250b80b41c0c1442c1d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 506830926 1250 506829676 506829683
    0xf0304030311011103041209050406050f1e150703030b0f01021c020109060f02210c0a050711041d0d050a051b030d1e1401030512030c07060c0504090608030c0703 71
    0x4402482481810f02420700d4107a04095008048100010710202e0142a44192590380d5107230007003605d503001c100440e0014012660409400074600041d42098500d80e10600e000100c0f807524155210300141c1c0491084071804111180801c04104040c0c1601401ea500c0d10122240041c1806d5070000030b40d0f440b890010b050b070404030304156400d024000c3d445203016a4021400b071110800054090300650312903459440803041803000c1c08445040da004480c022081921818940b811517001110250025101510b00e0181400001d07541d40d41c3d40300701542142074038040104c100035120110304141090205070700740039082000701f030b4a40d070060480b6510074802a681c1100c00039001c0540ca18020349406060592500140d844160b882c00d50880303624980713900901000907100888010210700703100080243c4d1000800c04180740a10010b5503006081284490821007261514815070380400d000d200030800024042c09944002d0041da0040c1035410000c45c5030840c121412a038420040c0b1016 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 506832176 1250 506830926 506830937
    0x81801110d05031e0721091205031906090510120c05190302090a052409130201170703020304050c060306030c2107090e0f01050c160f081207110f03040303 68
    0xa00780d03462220042e82c0114020046040c0d40c80c0448002d401e0844200040b000e0091908240c0b0701500b1b03d0080e030462983c0f011401c3c903c030205480c10f5800d034002415031003416940341305041500440f403040c1c500601c800380006c18181050b801c460086042134201601031100f207540c02e800b00c2c400c020114101c2d1425a04001c0107018250340305c80c2c0c04002c0d00b000754841401002d0000348042904114001c0040141101c801c0d00901103045140b00c5039024140c000d4101c000040f1010550742080c8035a50040c141442007512a98244c1d400f0300c2e007114044042a030100274030007404010401a00702400035a011031441c240880000c0d40e444010b0211482040070103203510380c03400150508204908840b0803075810070b888850300c1000e8480c91b224001181b040381d00300045e060b414060b250084600740f002e945081c2c95404040a454005a800e8a40c8400d00f00d031030000403501c000a01d41c4003c3d05280d01071a00307007920000c0ca00c5847d640741c1034080d449400c1581c05141c0104c01c90701103c2c0e160504 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 506833426 1250 506832176 506832181
    0x60918090206030c030405010c05132702040308190c0809130b030d0914310b09010b0a1803050717070503060c0901110118121704081801110d0503 64
    0x8540504116000250404004000d011103909108051401030344600001d1262011409088500d0f02a6501070502072100c1d800c20011000c04910406048081da801441c00c1c404140c00c4e031060307a12540c405c0322540000076401d4061070380e615601d000261140b07044510440551504500380c01110806442211860340d5490303d050190b220002004006d82038425803180d46c140a03003c00300503c619500703481c0303c802c40c45161030660085a000f003440d140140d800386100d540e0408001408001c11401980e403160100c496459159160003400480b600b6642d400c06224001c0c4191054800d2440308074103084107200041c800300d044410390b800c01c0800c2c458400396100f07240c0341508070761100383c0602420050201c440c0d403143c02040e20300002c1c0c03144152034102c1c0c1012800c80c2c400780d0710380c206941080b07901c3e0300081c41c038001c2548a41480c17a00d0313510010084424040d80405a40445200710001080340c507403c1000c110401c00442400c2044000300150940760f11400090070201c00c20400000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 506834532 1106 506833426 506833469
    0x9010f060e030111070f0c030c090c0e0103200f091302030f06030307050a021311030f01061409060409020c24040605010f080a02040c09080d02070302190609 69
    0x1a058541740b203a8070742d50004040c0000c1201d84d80340074007001000c6160540d0607400b401d0500000190038240c3c2c80003421020a44000da418142810100c070710325409000c54032060000c001403183c3e00c0c0b41c1c496004402d44190409154000000122100c0240980c1e000d18403030320200c004a005911101c003015901e000f8128020801d0340300045203001410040000c1410300c00d40d6601003a01800ba04404140c0e030400c4901c51301104c0c076580104102e5501181c0c10840c10b0b6180b07100d51500e140c0c0000301d03140e44183e0103600c40303403a0001102e507a0004100040c8030f10110240780b150b4100d80c41c259407004400c007500c00341c400c0c03410107001080c014902d21402049403106c00080c8180c2c44070703a00307000c0901948842a01840046000016129401d2100100d107008943c00fa09189040d44100a0584176007071400c000c5083c4940f00b805099040313546201500c6552500d0001c1030003103030 = true := by decide +kernel

theorem cover : BRFrame.Cov 506654676 506834532 := by
  have h0 := BRFrame.cov_init 506654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 506654676 ≤ n) (h2 : n < 506834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
