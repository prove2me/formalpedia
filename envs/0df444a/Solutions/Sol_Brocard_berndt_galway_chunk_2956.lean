-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2956
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:14:53.051607+00:00
-- url     : https://prove2.me/submissions/a35aadea-838b-4fc1-9010-e81becac5e97

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 531474820 ≤ n < 531654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 531476070 1250 531474820 531474829
    0x2120c0904090b0a0603050106050f0108130f02090f040311012702010e040e01140c3f090303010f090b06090405190e030a12020c070b0a02030c01060906090e03031311 73
    0x110382c81c1d10200e080901c1c2030400c0410b020308031600003201d407542400c10104803030810071054118854140d40b540c5207620741ca00c103000c2d0440d4800e01501c409180d0103605025071240c1540711f00840744080c104070b0074642810b00034200010f0b455082030390303410211103c40303a2400c041c08240d0003484148042454000e48010307030316202c00750050343d0001c1c20708107080d08081043d84450b402402810b00c580c2c10350f603501141840b034070410110007460070007408403905046030042000005031841700d9071003002010900070000003404543c0039000358800801403051484080110740109402d810a1001c0c14126000030654041c061480d4060b179660800251401076504106e042d100079150300300300e2050050005034407903000c088910049000c4807a4240c103042c10303200300c0d180c15041c03070007a049103030a10700c00e49216400a507982e002c47c803040c0310100e042c08082c42254001c10035008005002c6281108203000d0701c2481c1d00045590f041802013212010303080c0c0808100d0b550000c20410f40c00030200004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 531477320 1250 531476070 531476081
    0x9040b06040e031c020717030705120c090904120f050c03040e130c0e07081b0702012d08090c091006080406020d0f0f050c0a020d12061d0a0f02120c0904 67
    0x100b1030345030302044400001355000b03241c00c0b401b8101c0f4842030740304100745070010b1000b0380b0a200080c10030805544411020310660307402001400c00903140c2040b600008043d10019142540e1340301004d1b4045051340c0c1c101041044100d60390401c01d05108003481d0f83d98480c0034512030074104800040000d100001d41003130f07030311142d0380c131007400e902250f1641900454450101e44607408911580041503c00c48417a07164030340d0b00e070407491303140c5000080d40c011217010350354054480e0316014014005141034202490788010346070f1039503207121b18034080000c03510342000000d440c0d00960103601070092003940c0840504c280d88050901400c0c0e07844615007240240b080c210040f20040c98031180c1c4142088a8000d0581541b40c6407041c03100b40c4401048009a103d10410b003005640036000e46c00e502e602440b00e0b8515048507c00014155680f1221509200096041c4080038400242040341d9036049200d0b58001d201d00c45000c40c108001e01030000c1403008090a101c0c1c100c82c010034005515510354001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 531478570 1250 531477320 531477337
    0x30c030303010609090e0c10050706060b04081f090b0619050a0e3321060109200a0f0c0602130b0c07050312070b090709020c150609040b06040e03 64
    0x8407a40c039a903a80c801016400e06020f603601c3d0743e041000c50300300c0f8000020040c00c0070f03c004003420340202c8008000d0b503d65110060442e075203a104c0a00003031552526000e08014051032014143c410818100011052501030074924847e2900044002050712a0304c0b45501c6082034810541c001ea04800360720340f0f88420307400343ea0700191105010402d0307550342e021140140e049003c4284046070401100c00c0240c0e40c0300b01910340c80703194000e1100701d24204184203110088178070b030481071103074041000382420426008620781c00e86581408a80c80d8018280100d4015130f8038080d4102400000000d2000a011003060708001440480300c050100c2c580c1200c00b10f8505040c0c6154051b9903882d04000da030004405103c8274021807500084c2400d010070040116140030002514250240d41ca620b04030354040e190880760310512501042e440e519200030f25001e0000e40040c80d01c04442440c0300c00081000302014002d400402c140000103145102c1c903900000200c402091050b580c40d540c07403035406202030703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 531479820 1250 531478570 531478573
    0xc050d021516171620060d06050f090907060302071a130507051005030a1109030708060a050604020403111e0a0b07062a0c020d0204050a0b0901092009030c03 69
    0x803079400002c1003800300d200d894450b00e800c031030741c0c081d203c048045400340c019250301c03400000404100161070f5240c2d10b0746407403142e5004010b0541d41400300d1030341d42180408810b420785d112000d0115182c0224100c410900440b5006070030301d8410600f1f501d40b1084d00c034102c1450740104540c001c00550711445003203240c41204a00301403030002c006240654a40c6426580790084c8400460b40d402e003804216151400b6448a80c0b868403140d090b180104680303050104055024005658180c0d000e12201d00204100c0004040a0030700d90001b200320380018000d140315600c10401040000c1135040103208038501143e10b0309000c0404150015010401c080455102c002d030709020484d178600350702070311406008407020442c403444100c00703000003041e000703060300c0b00340d0802580c03443c00e07100d2545407116920240616011048650100301540d5003952650aa00c0c0c40f5030b0400e03c5414258005801042003510600401c0207400c1103403c506050a256601440009212100b42d2400c2044500c4e5100140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 531481070 1250 531479820 531479827
    0x3070504031e0201030b04020c030a18050a0605180a151d060d14130b2d0a0207120c0c090b0d0b01030f020907030614011d0415061b0c050d0215 63
    0x42e011086901200101d02107032600d0501515030400b442654403080b0048019842c2c82000d9206542920141c3c020b002180c840a0b03001c00c3c107455540c81c445c02042e40da158940c54030f0b0303031000701060304d0a0b207a1a50701406404000300080c3d50b080a01700903510369030901001d0644090400110404000045034110200213440c80e09128103510607811440d800301d00c0c4c0c030180c440041001024400000240002c0303001d4000c10858082c0031020a80c002d444103e04003034400c44407009011440407900e40c0d001d90350100b410700034005201140c038641c031040e142012075054141d84141100709140901c10407140d82d6903884000307072944180000d0442e04034203074180d29a504d1034850b41e84039410703500724001e020800206a2050180c0104000d5500e0700001d072240e42c0141c401100c2c049810070a00d4113402032464110455100d5224400091110482da100754604100010300150000c1d529050340900d107084940100355079526000a0302e0080754049035110150000403501038007a881d0079102c49001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 531482320 1250 531481070 531481103
    0x3010e060603010f0908180607050105010801140a1b0305090109020d05060a06080613030e28030311030f040323030315041508150403030e1515030309060d020307050403 74
    0x1a00e5100c0c0c00304400a0041d02482800d071800d4444088004024400602010411020024580540a04c080d1105091000a441c3da0382540d0702a800f08543e42d545a0181d00c0d81e210b8004c1d03079540031030704083c18401080315649101205081e4004002007580d40d1000c20002642900315003a05a00208030721084d542c5410180d80721442628040d00d40c0345001380026407640d01042e2140301d13a49400d84103d0b44091900c00b42c031940c103400e0486900820341c0c03043c044030091030301c20030300300b401401152080d15081d49005000740310802840c1c101603000342301e1444200d030000f088905030380d0711490380314981e1030b680c00c0b01e2403000c0d40700724807519404042700300b00d641000c61000c0e01070350383c0460701440a213041d0052280007140300c1c0100328064110040c40003503481410455908644203160005450090050441c00d02406e2b002e03416a040a00c002c2c031100800c03d115200501c00c04401441c0303031181c5030000407203a22031140302d415141d401000003016580110700703407002150030400740c40101d00c40d07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 531483570 1250 531482320 531482323
    0x31c08061927060905010e06090709080a080904021902030a030f06032f030102041202040f0c02032d04090204030201170403090504020f041e0f06080f0114060903010e 73
    0xc842460140240303141014107080c0e40c84048080354000442c40c030030b400154030701140694018942075440c40d02c2c3d0a001402c20941d1282a0082c5400072001030a820120b04011001c1c9010380282c00f042108038042c030400c1000b28420700c229511203040d81c1d40e207030f2400102e07000c0e01480d85880300a9415801a0031f02980100c010081118155270401000110a007034504031400c1c2d0001404c44075418124000071000039070f040c500c40508100d450299800000020b003607034015084a03920313042ca804484214105802807410000395404240510301100000a40d20b000349800410524ce03108810141462508407255002c104081038582c1e40d900c0709140b8010798030510041380020b2801d0f5041415030b04801d080c90050354550348010341b0902e8401000301a4104143d032203600305080000140220304000300354481c20a6988901c403652915000d0309030032903580e00c4802407000020802a54050743c0d04414151200c2920300006c018010001c516680115170f4811f4040d880c011811140140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 531484820 1250 531483570 531483587
    0xe04020c07030c1508070c0201180609170105010806150a1d0118020c0d0e031612052a2e020105010e060a0b09060a030b06070605060307150f030b031c 66
    0x1818210f0340c95550f520031104c003401c07040d08407000030b0000010500f145c0c4070710030214901e40145487ca4450143d01181d01c449c01c495401440071a192140030880340d90400b51142a10032124001c000d950701d8000329540310000104404010340030800c00130f109684031005040130700032a000c20390b214540007a480035103110078020035907aa4034092001002004900841e134039007648102804002d480040d0641c0c401044459040c2d160080910400c0d0862041441c14020718440c20030a4440180b420550f04001c840c05140f911408140114610f03288100701c40340d403441040e15110300d2080703900d1280700152101c018400c1d1019100300b03185102c5038150001c0d0b060740c140c81141003190f11000c08206c01c00e034041c883e0b80c40590b800e0180c2203d52400a000c2c2020b107125040c0400e43c240741800040c4c45500015046440070f6680d009c0c05110f040401c5034901409a1211310307186040c1d84100074101410302000344007010784030070480c0007648061204500900000102c088040442ca602038203400c2c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 531486070 1250 531484820 531484823
    0x3040f0305060c041d04060204080d050304020a0807050a030305030405030d0f02120f09100f0e190c09050709090c0309170d200a140c030706090b1302130c0e04020c0703 74
    0x10507000411406995070f02224100c40303842001d00608405210b4408501d8002002541c2c8140c2c01c2c8030000728400140010128085265215a1b0720b281c18410411507202a030008500340c1e122207028041078503890032000580e030301802d0403900c1c0e175074618260b460352190341402072100d410840d140201c0c05140d0054031a43c941c45106001aa07550143d19816060403652801c7c6903000ca14400074140145d03100c102541811800811008d0031100c80d9440c1007843c0941090020a08010070300740407644603c00701800035110240701e1030401f03800c000d06040070b0340200840981c0d909003c418140c000e501c0100300503804003450f1815440a5000c03074641d0003500f88500d2540c1031965500c10318030000407004040c85174504e128140403102c00c003201e50010300801c02001c008200240424000204060001c0500c604004601808589803000c1c80600241400c040818010100c400690303843c035112036042100803002a01c64a81c800450741e9141c0000810b8100340300080d200d4100b0408100350b800c0da07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 531487320 1250 531486070 531486073
    0x3301b011e14060a05060f0702030717070b0405030c060a1b14070504090510150b040807030312020c0c06181206060f01050a120b220507090b122703040f0305 69
    0x800562180020710b011100750b90301c041c03013050a016a10f00540030b00052400f03003401c0c03428200d465012915004442d00010003400344ca00c0e190000c01c01c20807501014221400407141860300e0800403940e2881007611040c8034120210301403034100c2c440d401c011011a000d00d41206084c0c01801d0503403107407640d000c08141d640102c1002160500b420f0160034506688500240a2541c000d1524401484030300191508841030880004460007510058006000800003501c12a46180b9010300380075044200b510700d0b10300602640740a000045071680c0c0c8000b0654842c2d944141550f440c0d03018840c6251143e50000c141036030503e41003c002481841000242c9520080d10b80600c0152100c1c099510100000380c0b455410802e902c40a411052080c00040d00c46003502040400300f840c403100201008000640c2d80b07041010080e44504800d00030710005859615101c03010307460b0102c11400900014810001c00058a1700e29460000d41d900c80c08103106503500c075600c801401a00034101d01c01030f2680e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 531488570 1250 531487320 531487331
    0x41502181c0c0e06030f0607020303060307050d12080c1b0106090e150c0f12040501020304031e02030403031b020406030b0106180510120f1a03301b011e 67
    0xa0406540c44158581d080034521000500d040750381503001100800300c54041c0203d442450301c01c01c0407c00c140c000c540c2900a1900c2c3d1503c0c1d028186000880d60200748955a1070b060040444d4815661100410444c5400c2010f540d8800c01403405200300700004c07903400c40000342e0340c3c0544819444131041e2500322005111145010f040306035280780340300c001e01c81c40c0c02800105030350304103400003054824030001e0b1460030111410420601c05504071740c03d8541e41d4001042100b01b6900100c19000680740c1c18044800c101070a0000351781c0d000d41c0c0001000e00c04140d0900c5000c0700214050044264000c1c4240521a140c4c0342038421400700f88030744004140c80707101d14406560191195415107202a00f91084500340d400d0880b18000d0983c0305601da241c0e5141070309918450b034001d01030b11282b01d010114540e0150340030315180c41c08040b034105540e04020b103459011010401040100c3c0303c18850281c941c3c118480c2a06810200c0d484107009600e08610000411030703640c0d140300810b00c2440c04003c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 531489820 1250 531488570 531488599
    0xe0a0c1508010b040b03131103070f150201091212060512010608070828030e04050103050d0f020f060a110f1314040e0706030f090c14040b0a031a04150218 68
    0x43c01e01540c003c80440700c43c2440018051300c20000c911170001e0044d03140351581080038020a0429005401020074910809014441d0300e103c151048500b241520003007000010607292100b587c004643c1e503004002d00c042a0780d04c540b600390008009064014071182200c96030445141c020203913072003000814040e6000006111002240501317040132070040000000650251900300140041c10403414001c00c5000c141c3c441c3c545200e0140a9445200140502020448098904a080c06500c81154880514588415004a0490b0b0001c0756140b0210300f4152a4452202900030350b51101c550a1011071200704602400c2038590440d038850002941542c0d06009000030350354481e00340150b0368080380c4104201c5200307910420786840342690008455203155500e00b140c0c00c2561003500a0649404640d10524251141c030300024801c841c0424907503d1555443c400c2e04a0804d03000c040c140080008050012042d03080598174124202150368070030b03101610040e4907a0100c02070182d43c16002c0e064 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 531491070 1250 531489820 531489839
    0x91801020d020d050711071d07110d120609090213020901090b0a181401021c0e0604060c0501050f0f010b0901030207060207050a050d090605041e050301060b0a0e03010903050d0e0a0c150801 83
    0x181a5145031140034000a040500500b140714003a003030741d0820ac0514803036111800244529403142c0c016554400e00140103404a03020b488007500581c58052a000e01170006944002040d48100f18240c009611000840e00580b12100309a00c080a02000054000707690b9521003e0140d80403085040301c0705990701c0c0c0c0d0001000030003d80c0762601680c04402c0802400003032a80c0380300304142c145046003c1400d41804166550810751107400480c551041d4178041010038081c4c1036100003c41103003096450508d0007400342034010f100e90001c52400144c65a81079100303404541c1600d0b00000d0656450000e460650758038001c281040e545406003602185034644250405070486569544103824982000840202e881d2009001c04c40e0044220001074513407030a0140e51300400c030304402140c031902d4891002d885e4503017950ba650f100fa45803803a180002908030081d5240c030304d00c1040018100400800740f501d09450044064402c01f140f200c00034070100109203502c503c652503910500b859a8905e0441e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 531492320 1250 531491070 531491083
    0x9140609031e030619150806030d1e03150b121506190c0f05030319020a0c031b020d0501050702010b0406030c03020108100e1003061a091801020d020d050711 69
    0x300c08860340d0724418604079940720003540d0081c3c002803881d0740d40308403034405c20b90321002940110400f04103410040b104136007042c15580c0c46041034000e0301c1e40d281300e82d1000b0f00305954408041900a1010026080c0714030036800701069100951078034159a448080c5c0102941003850301903521400790f0001600c5516404642200c0c0d0380142c42c0604000011200031445141e00b105641000380c41101200443c07960744804035001d0103a40035540e40d0601c00904201d403c1220080190b0a004009001c0c1e01030344600d40f40901034151a00d14030740d907907158a10100f1a156000030394130009444156042c0141944064020b54044d002000340700907070800d000039142c081c030020300007282200042000d54000c200f0160b02811440d5600d00042d01c440d104100c42c003064030320700380d0400988000e1040280501c60f112450700c12101d00f075a440b511400040c20b80b1001402002c0c02d8840098121a044094040d030300043c940314410364440c180803001200030041142c421000612650503044005004a41c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 531493570 1250 531492320 531492337
    0x1506010c0b15060909041b0503151902070210031a010c050601120812130203061308030a0e0c03030408010f0b0a0b2709040308040c150921060914060903 67
    0x301c1d190740da21510b10302c2509142070b00098000004001c1c5455640e41c40068501c900c0c0700e10b500450030700c481c078010040c02c209500701c00d002c0ea1002d4a4400c42d5a91280217541c001d205048103c901c210401c82070b0041e0040c050000d410440c081602c015003601034011031411602030440c1a43c5d48000001110080110744000e44150040750046c412005585105441c090050b11402d1030304414002d8541c102004640c06d00005583c0e0704404210700d414404103030440807800740071020400681b214a0f062101400f10305e462941d580b200d0504540c244107010144100030203481e210f0750f0703d0392002d01074004000a100054907105444032240782c4403142d10183c0d08107030100341c240408403140806404604014100c080c1c0d04080c54040340e80c507180801d124601c0703940c80c000182000c0c941000031012030380002e200c80d000d5041d1705040300c0c0c4c00800307e0301b21546e4481f02281c03e4030414035241450010700d0040d0000e401c2030304410910880300c01c010051801c0c0400c0f40c48507a1042103440c0c40b1301a0803107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 531494820 1250 531493570 531493583
    0x9020a0303171b0a05091804050f1c0509210709140c0703050405090a0b0901030c05011b02100507021207090506120705030705090606120a050702010b042a09090603051506010c 77
    0x151305281c41a0084c003003001000d461421100c4800c18102003007641260110388550000c0700c0800c4460041c04942002d1441c1a81c0308803c180114010b0300e9805130803112802108144403e505050701700c40382100010000b03080d82c00060721003922101604150701800d58405152700401c1c6400322001c00c40f030780c40c0c6e010368809003801c3c03c00d820400a4040908030804003500c0e1103550741942c4c1d818480710b000307500ca003c1214865150100240c504503446000c0b101040e9005002c60243e01d07040240c00d0402d00c545006a07943c040c600c005910203104000029092007280f001203100c00007a8400e0b030040f00308441316000108070200403036844103240900ea400d50000300c0104100d01789004080e42000e0010702090078840c907800503880c8001c003198003003861601c403014400015020301c5003465520003a02c040c42001c20050124520b52143c00114152640e050410540544164689005072100481c00e002542d030f40e040181ea2a000c0c9002948425022000b0524541c0100d101c5814241e1294 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 531496070 1250 531494820 531494827
    0xa03291c0f140708010f060e060108130b07050c0a0c0501020705060a120518160504111303020d0219030f02030d030225050f0726010203010302030a0f050109020a0303171b 75
    0xb900d4400070a060348004100380709014000c1608802805482c0204400300301c009119881c20300c55800c0d81c1c00185c141c40c14012040180990b00000340326440d101600003144410a4a681004590902c11441482910300807030ba846d108200c40000914201c603000da0031294110380f640c00300701091003034098a00c00720310300a60394422908580c1003c0e502c1085c0540001c40c060580c08410308101011a01e03a503480d94808060103145018418070540c2010941058208a40c00001d103405148501000c2e20445011251204566841d0348400d006130b054031030031480965030f150142051080340e10480c807d00910003c92190351080c426140700340f1021180603146080a0f41d202060040140b054550340a0302680040d000e0742001a24014440b007c4542c0d0220032044030b8441d03071300e410134019006034010001007003d60350003d0110051500459a444c900903103141c400c6c01001c0d0a94005d4000148a0001041c5030708003e0f1840c43c034a90220080703103540d500300159030414050010000c00386060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 531497320 1250 531496070 531496073
    0xd0f0203070f111516110c13050a20030a1a0a120521040807090608061f090504080306030c0103090b1b0408010603061b080106140a03291c0f 62
    0x600045072802c06403020389003114290300c025420404c007203402103880308041c0401d03600d043e0700030102e03c1075003882e80c0a040801c0324500007946d020243c070050090313503880d10302140c0140481d80c030645500c5c0303496081c00c20382103c1c1e089005254100310ba200740b02c0b615001c06550313006c401170034011461000600000503241401c6480c24554451482502c0b18840e15000b0303c11a43c20b0346141c4c0101c0c0314007080d40e0700c5500d4644040d20b0075002d42c1040311070b01d00700b1004001c0b0f00000260642c109011400701e50747c210045055031030608042e4004038071141400140300c1400f810000444c0903490a900341e0b20001032322001035050300e014400003080c0c903110300c00007038541c20111111007101206040340d528281e40ca2001c1401d507415508180c0350969244441c078040340c05041170101e858050300b0f01c00d00b95850030401a2007080008030491240d1400100a034805102c0e034080012590900301c2c40d110644602081c505004e02c050b035041c00303030082085440d094810340210f043c00361b41c481040b4822030b00a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 531498570 1250 531497320 531497327
    0xd2a05060403052109160902070c091805060a020304150c0e0402160f380604020a0c0210030b100504120219050306010608043e150408030d0f0203070f 66
    0x2c00c1440c2c0105065030346000c0100e0780c09010750300030405c0e0340c004c0000d40215a0300c60014000f0b40d000c950854410801c01c8009149021008101c44174110005484e002c44c0c0752802c26407150341e000a0450140710100555011681c1c061070040b0301803500d62a50715001c05415081322108014500030841c0500c4076280c2d45070940080285150720030289109004c6603036240c41400c004402114a407406c2001055200044001040407140044103480d80010b4107145030991540a0714050056800041c010301c0607000c0c1101e40c0c0140e42c09403c4000c00380201034024002c00ca68414203215283c0c180004079404c0c4513070241c0d0182c800c41942c0074035020b074a500300712005045600780d4009260700d840004003603505000442c002d210544980105107031034600310340b810700002820b0005103142030f0003070141e80305441040340c509550110036141c44907010015210400001e82d80740c01c3c620024021034000d5001c8094180c000c3d9030807083c0b01104900d94281d040e4001111901d00040402000407400ea10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 531499820 1250 531498570 531498577
    0x20604060c050f0a0e10030b0d08030703061a0307020c04060501050d090204060e090f062220100e0102010e06151009031b0e10080304060f02030c0d2a0506040305 71
    0x70356082580c41c1c40740038100f1a00a070841e03c2c8010104070b0b03072810b4042e2414801e9155055400c84e140800c01d15203201e00140000d00c0c4210040c0014030044005141c0601a601480c0a048140d108010b0b0f94000f0781550f0060344222010310040c000c000101c80142402c3c001c0748240e95058448500704a0f002c50b9010061034a450166843761702c462001807075011912426010f01c1c01700e40540703800c00d880080a0302e018006090628010203003410f01004801c4030440780348007940004d82500d100c81c0d509005500c06907000c0010b42c800d08021800c0e09413034102054403e0340000b0380003801141d10079010740c0d07210700048803420f0b5942e0b0084013444c1c0c0c07490300f5007248a550b4054180840c041e92240c03904207120300c01d021a40301c903500304a001c0c0b003903141c00400a0303440750076844036400d440e0810a0051701c0c0e020343d101d102c007400401c061400e0310078024810384051012103c201c1e982040b1a00000701031012440043c0e1030204e80c0b00101c20440c1e68501c070381c03e401d604032005184030b0303d0315981282d143c2e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 531501070 1250 531499820 531499841
    0xf0a060c0f030c051606090f0b1b0c0d03020304111207080f01060b09010e13020f07150912050a020109020303030915070206090d080a1806050703270b13050f0d08011502060406 77
    0x3d548400e00d00c001441c80155239502809061200f00a2800b54101c820b02191104090f08010007400101c80040c0c002a004a003c0110324025031252942d2910800700d0050321080c0d81c0c4954030340060501080c0016031207044800c5501201d8099801000190885049001e50311103842c0800200310b01e0350040e40070281440d009852815008140307401c11080703821820307404041500004204092060001c010010f0346544403007088940340f560b61300c1c00105048882c61007405000306420745814000c0d40003141c010340240039217649180040c00d40e503c2d291044a444070040802c400b00708501d10000b0f106100303811000047c04100e02d40340303007510350500050035104000d40310711954007110914031401c29021720480011940b8100480060b060390f541417003510300c0d400800a041900f11041d08803c080d26004003e500341a21456480c0080e25104680a8528403403030340704804034000003079411103000f566a5a022a40d0700c90301c0c2c80c910300464800f840b005920070000b15000c216a83d00080089 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 531502320 1250 531501070 531501083
    0x911102703051b031506010e15040f0909050601060306050901271802120c06071b0306050408030412090303300609140f01080706110f0a060c0f030c0516 67
    0x155900d42d100d6203010036800c805401203080c1040b2480314101042800090388282c51490402e25100000030803500130070340098828004044810764440070902102d010300815265500401e450b80c030107001500401c42d08844c41d1040c180000341c441e10911172107040d070700000c12800e0207034a0607140c4100d110f0590010003205205c039900c4425107901d0310035082d43c210700d20340050b80a03055004004135001d1405000000d0f0304011008902559030078111202268483c0202c5038088401c1040da50110310742d00003c03d103074901801c0c402442008405140700f18420005000314001c4640c08507150701ca2848014089000c071042c000441c10460705000c44000c030428074903030044182d031848080d5a0310340e100940041e56514110755481c070316110b265000450300041039065252140317007582d60032180309190800c030b5000e4034043c00d490140054a15440341400b00e40314452242030120080101040c1c88003c90703900d2180d02d06180c0030740a000c4031010301743c6407281010043c10b04281100001003046030309 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 531503570 1250 531502320 531502397
    0x40201080a060e040c180e0d0302070c15080609130506060d140d0305010f0519030314041208040609120506071b05120441040608010c03091110 63
    0x20700e5102801c0e2845103020f0300e040ca414906c1c09010a50140020003c6548141011803005a07440d0000c0c129802101d00d140060340c400181c20410f010218a80041c0d407a82414103038481c181ea030020740c031805144103d4026545484c0c0d881500118440460000c0c034135044400000c4480c9459183c4e00900e6004049125001256180b810704000d000210b02011076612001805103103c045c2c5a41c015240559810900690400c900b4484a086110040070081840600310018541c48242c90043c28a040d8000c900c2c4101d10303003044e41f6000750007070b0000542e07090700005803640022014040c0d0394204002c4c2c1165190004c0454032040310354001240003040810302c0c40050000c000c184904030150140b5a00d50341403145000c0032034030308032050b00e1040704181501c50302c0328042c505c00910307918281c0e07078862035008001080141a2760b5100003102c1d460842d00c03440194043c1c000040340780c81243d80d00c0d00c83c10b03044100b200b65004070014100140c002c0ba20303144001e40c460702c41004510310480c0c02c2c19 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 531504820 1250 531503570 531503579
    0x61803060c120b0a03020d020415150302070224030f1506180a060c02130b1518040c050f09010c061409070314030f1204020a0308030a021309050f040201080a06 70
    0x19160004514400641120001c0110140b68460155030341c808403460040c00e40346400241c1c11104154029128550b030300c4018203a0b0410103480710003822401c1d40102c00c0c3c0c0c400407019009400011040e0301039000e81d41d40d2038440022240d00100d0b251880703500340c295112603e45003000b80009200001c0d0050742c950249190b680d038005441d0080700c05103003860040304107080c0040c5503035982c0f2110074041018854001692100c90880c0341c94803081001a4118103180003544000080c448201403c0d4002107460034010880700c00c4501040c242d80a00114603118000ca501e84641c80031100b12020522200e003140d03200750030056441d03028200c041184034500d04e414240e204203907003012155206c10001c200b04008403e1040c88a50040040e40c209418070020034810302c1900305550088450750002011075a46010300c501a542051942d5207901d00307291400001d50101c00821400d140300340340061003184034082c0754402c032100103240803aa00d0355801902c10800140003030b0085502d9000114 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 531506070 1250 531504820 531504833
    0xd090f021302041a120f04110907081509040c060e03070513050105100f02030a0e03030d0e010b0f03280320011a010806030a0803070311040b0405010f020601080601061803 75
    0x10007a944800d80160b44602d03122209462605000b03440790000002d00c500c0032140103a6000c56800000030034044032035540d61505501e8100c1840010350721680a03010711030240da02c524450710506000b03801e02c0d0108421000c000b000001114000e000c2c4400c14001e1280500c1003030f51802d1000701404032260140c4a100140641d24114000c101103030b40d0744010403951405030107601e03e8440b5414100c3c1c0410182500035200c0c0b0540050400b404581a012a01a20100110381907583c0d014800c100c1e00e13440c2c3c2c0f81c4034080e042141d0042d11814800c1d0504820740350209084810038000706658080c200001d00801030320094500a0342440012224074001c41409140c03100d00c0c06c1c450303000040d030901a4009443c80f4202e03a50071030400803c0000c01c50706032000605000c0c01ea4005002949a541d98201240500a940050b248164010500055410040b0041c0068403426224042d2510304a80c007283d0301c990074070403030b201580403400400019008103142d046502408000d00c052a032030342c8902 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 531507320 1250 531506070 531506089
    0xa0b030607390203010605090f0103110d0f120305060f090411030a020a0e0a060b0f07030815030106141305090d0e18010308090109080c031002030c0d050702060a1a01050d090f02 78
    0x1000509040c2c014086150030312603200503120841e890b80c40380c10400340400134003005010081160500381265a0715640c0c01c440b403940c070b0b90301c001004941889441c015080c1c016112903c0033213414140410403e28102405620341040a41816015a42d60f16001500c41c484104240c142c001c980101016888800000028200c512412008c0381050240c440481d5916809000a050203204496411020b10304890f8420f400d403502442e00e4903815826021002180506503142d0f1902070006414050494602548001114125003002d0030954041c25150202c5001000d40c1100b6401100c0a000f904a040041c1c805082508080850542040c0c0c101c020b80055481010200721001c40f5070740036031180c01925202c07029000001c400800700303075a1030013105042c1c46031390044001a8a1800c4c04152090058244004d010500f0300d40d0001c1d4807402d05440c59103c4da4204040b00c1c0c046c07a00400030703801c101d01c103030340711850030314000e091000500343c1030021615104103107031400141e511513468 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 531508570 1250 531507320 531507407
    0xd030503040c030f0318080303010614090f09090f010b03060402012307080d06090b03010e030d180507030c0e151e030f01050a05010f08070b0906070c15170a0b030607 73
    0x20104520f42e480081c1b00605c409030320044041d4800c00052201550216886074003424000b40c0a4880d041c4000064410396045206600b2840d4802040030784000062030a00703d0320034400030880f03800200e0a00da11410b02702e8000c0d021405101c01100c15484802044500c803c0c41c0c40d1190404d00a030350746000c0e030761205000d2809a500c4910600404400b0301c100040084118004c0100c060600c011940700e004080d04908035643e5000c4048502c105540243d00059101050342c00361038480c90074426030905d5000e8203c00092080010724815440d030502c1c06c00b00380003820300481c0200840c1e040301444001000e0358250241a078000d41c00a024003803140159130038200400d1940c10808040a0b8001c00e9104148540c0308210422410841904882400310156042c0b07036580c1c1c0d6810645004105a480040021180302120002540c0640c01c1c0d00c0e8518544039004460315100741407410340c3c803140c0c070065041c0c20440110391058029a4146544540d40c0585079030149000b14184901c0c0040fa00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 531509820 1250 531508570 531508577
    0x9210a1703040309140d03030e070f080d090b070b0a020708070209090f1c1b1b0602070603050a02070b06042f090901091404110103020f2110050d030503040c030f03 72
    0x180402c05401c1100000031340015810400e985c02000002110403071071340c4028062540e110b03004150044203100c0200034040010103a0b017071a981d00c3d006a03561109201c124001410848042001c0314031600311900c04c2d8002c00c440c2e480d5100c0c0400d080003540f04910440341d245080140d82d0046c0c0307076412420310403440d0780050180c0107000d03620303c0d007800d201c408000390703480184442515458116000e880002500c25a403400b00800c1c0c42c10800d01c03601c045200c01c000788032040c0059115400a004001d68082d90740a115545443e407a94081e4010424014480883d10000490300e09083d84031002d5000e003a099801490b011608201348411500306091543c2000100600740f030030850312550040c03c1d03182041003821150498004105809040205072440c4590b011000368442d80684196003805210507035952007540700c9401e040000390f18000701d080950b002400001e020f013428821030b41d01914001e078503101076030704550f150f00082040791401026040880840d5110030750314540e0784a600c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 531511070 1250 531509820 531509827
    0xc0221031806060109030f05120304080a020c0d080304030c0f02060408030c0105060a050a1e18091e1e060f021605100c051215030604050706030b0609210a17 69
    0x4000c000c18580d81c0c40c0c8411164854414000d00d40d0303201842ca0201c1c2e80185002c041d4490070302e80701d820321094441403c121100070061109000e242da0050020040325001c4910b444042810312200403800140600280010b10000340880c5c00742c600d8900d514887c1134211480c030042e40c000780311a00a82c02c2002d883d030000c40e0595024400f489603640042c0e04a4031002014500340002d14240030901511083d44902d01c240c42c511002c003078122010700311000c0300e90152144449003034000d10560b0300944041c400c01c4042c04883c40003046044410b60031511000301403e25090618040c4689241101e00c5aa5003040d90f8401e0030341e102811000107030030443c0300d0351030b0703d400d010389040c4110034440009442c2030307a5580c00a800208440141d25210020b804940c0e800d03007085028145d0341c00c55600744c010b0f03404210800c50045103040641c2e0468400b044a041028203119150040c41440c9400c2580c03000100102003880498040c440c0060b41182c0e5104003a0782c426084401200880c5180407012 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 531512320 1250 531511070 531511081
    0x309060c03020d271112030304032a1a060a080133140405060a120b06130213090906110a0c06140702031204020120060a0608010501180c022103 63
    0x50044c0c1e100440d001e030030140c2e240c1c03c40340c503490b1204d50341000a00d5480000e07034000083e240c000a2581e9021500142e949900d42410040c1c40320f1484140307480c40c00c0704e9818000c6443c4280740e40828003900201c100582c2d405205026484c200054104e80e800b401c541d2000601043c01d02a1460300c0c0c120020794a10741d0401c20302d516803548480d49001030003041c80c10070701c44807042c201c940000200448000c1388a4483e00041400214160899401026440382410600c02c806880e02d002d800c05031240001e50b210754400c0b0b4200d02844a01c65844020020b0800909425030007203c8154060100000c90a5081d40c0e5030210780d110701144000b103011030b04444140403142c4a0140b400820700720040d4186001e402c02900d80c81611707140a50341090501180540e4030811801c2e8844644103c1c240304c0300310450510303984010464035504003504215003c5407448040c02014100c8035031651090301d4200c80309a0348040c04014030380c0c90451254900c0010101d003540b03041e00c40d038584040c0941d03907070510 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 531513570 1250 531512320 531512347
    0x60a1b14090a032f030a0b060d020a03050f060f070f11100e061807062016080a02030105101d1b030c04030201031a090c090102030d5006010309060c0302 67
    0x10130a880d0f48811142458103e8401041c2034411070752102c551801c0d0f541d00f1000840c0c100c0c10060194200c040114040104400040e0607040d420080085641d03a0b6510004111078074400c859000001d072120743c480104c5d41c024943c0d0411040e60703809440c03260f0440d41c0001c04455000c01c1e000704581c4040140140042822401b051200602c0c0140c000c00d420b05101404079400b038004042c240d105c0c0301c05c08000c1101400002000d420040300e000380b1030313a6484610b54848540304207031310951904012032640032030100c11404480382055044d103110401c030403c07004403500800c0400d0450320700c0445030604032100300442c0b10300c0814242c10b03211411400018101c4059400c0c00c00d20045500c51301d4201d50b50007070785039400030400c01500c3e95000c15070f004034294003a80c0b0104049505062040441d02080068030000004034150143d00c040010b94074400f104801d50b00380501c0c0c1d80c02120a081c2100c080c1d5aa078044c4060402060344400d555030613045900e401a89000070f503021940441d04c0c5071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 531514820 1250 531513570 531513623
    0x51e010f0e01061d10080709091505040c1b030c03090914040204020f0c07030f1a01180c0306050303070605160c03050d0203060d15050603060a1b14090a03 68
    0xd0911881440c0d08001e01105000d1041c0901c0b000d01c5820b42c166101842c00b020484d864890103014011401c0c3e0b00704018003007883c02d45440d00442d04400c804034903a51a4070034412070400c403012007450140707014284001024044a1034042044c0304040444000f4003104015429101781e130362100710403003030034000e143c103225410072000c2d582011180b15100f0b5241d604142c0103501210700596501007034008800c588104040c40000b070164100c00818440d504200c032001c42d00031000f1105000803c00010f0890300300340591400341c00038030194400301c43c45511903880851241070000b042510b4000003491034100d06405c484580d103603002c10620900c0580c040103450424207003c21155103543d4007400f9030044030355904200f0f90100000740d0310f94610242500194003c0e420700e2400c07100e03484400c082e25080f51000d01902ca0070020540120903442165034110403041c180200c3d000202c0101e484c1514103140c1c0256800a01c51041d440d6104c501610046101d8102e440000135802d803070021840c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 531516070 1250 531514820 531514829
    0x20622080f0c0d2a0f060503101a070f051f020d0f180b090705040e1501050f0604120323250803010b0a031503110301052404090f0204051e01 62
    0x5090302020001030f00383e200389084980c48101a0344c2281c0100071081c40c100554880c03165401d10000001b03440340c101000318050401e841d00703005101e07101d90400c00324031410b801b045400071040004401080040402000c0d25100310213490484881283c1d00c9401d030303442e4155038442c540c001440340315843e09108039494040003107424004a04071416142205089500c0503210001c0d0b80f0002c0c2440400f888120f018140c010030801c1900ca0910b046680c0b04c444548282400c00000d001003510700d804200c20312001d400508061415040070080f15071210306020480038496421440c4001000702e50404840c0281c0070805070300e0340b100b030284001120300d41180d50012102c030440c2c4004031307140e0805c503410f40d8500140c4650384d00141074210700800103480c90340500341846402108100c075500d0900000c201c201c00070b01c001e80704c6070310b90103012150b00100010a50011058400703410203230015592240a64610074100c419500031500b9942c1c220b9885404035680e03031040c0c3c4000082080c7c9030240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 531517320 1250 531516070 531516079
    0x1f2322090e01110901030f020d0501030f0b010e090a0303020c0a020d0b0a1a1804031404060810150f0f0207050d08030a0e0303040c030f08040909030210050702010c0507020622080f0c 80
    0x40c5503110700e060b8940300e01300b14981016220382d0342c00032014841d01207408040e000801008290396a062044808489540844e01303003500100001e8407840f01810b150080e1184409800e541c1da8690b0164020762000110100d28081d6030013400159a440c00f2a00600307000d982d00268505c0e26490800848110300240c8030000c00c0b37a00d250100792170300c088001314032545982075042919035080a030b50340a51080c411703030b9614001402080450b0b10100c0c0c140122000003a040a9548404e400c3d00300c11400300d4070100007a80c010030300341c985210323400c000c030f100310036006071905182c4541c00f00321340c414541d1040e24056000403d20600601078400c43e40059001c501941c1113050642d29903444055034840503015045005060080c0402c1c20100e800038a0844800c204054691501030344401086d40c0c8812110b1900000600d41030040c011208486055038510340b1300865503003003055a8010401d0740080c4140741034a03c500c9520008e400002d0302d02c42c4010101440c995070f0003450002c0d07001c50380f03004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 531518570 1250 531517320 531517331
    0x120a140331050a0204090204020c06090a03080a050402090a0c0917011409010504020a0909030e09091c0e06041e17100b01091a07050c19051f2322090e01 67
    0xb1600104030a074010354129130103e07030500540001000b0b80505070191000c0c1c080c110074412034400004030403101921a84402983e691608551000c0b6902150b001c0e41044d00480010400d01d001ea124165114203410f04048040d00c138543c09805a13007540c0901410313036580103101c01d002510883c2030f40c0030130081c00a00c5280f809a010604446440c4180100c4a071030350401420035000f5030f100818070901410040e15407a00340c0a0941d40c07600401301c0888000400c500d03103041c0b80b01e500c02c0121110060611440c261400c180f15000620284030300d10b020310360040208d000b0110014424020812b103006040124040c1a4a011290a500e803d030511414120403c0042101e1505400028900d0100b40d102c0880e410204e08100c81d03001d107a07902134446003507201000e4040c18000309682d001d0364441401c03408845114100c034001203103030f0041192086200310051100c100716120052902c111410048410310300c00400c2040488030030210590107040c0005121440341d52645520388001703100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 531519820 1250 531518570 531518573
    0x3040602120a170a020715060b09011b0f0807050d080601120f090c08060a060605132607180b01020d1d1504090606020c060705120a140331 61
    0x1a01c481080c800795221030082a0444618095660301c0365401c50300c65000b90b1403801c048003038000c0d84901812150400e90100340103220401d8400c0009941c80c5840041c42d0907080c42c019204020304000000c0000c038800b40810010b90000d00101c1c81501c501652a141d050f00d15219040c00d149500c10420041c070f40d4100a440d07a4003401d00348603050007490004183c00c600d078649000d4428003202800e40c0b8184240040c040c079000a00a209500c203000421019845400c101c2d0184140300e070901183c040140e050103494521000326004003040200d03541c07078600c10122142000b5482c1d10500300c151407810055120f4a0502a0300c0031200248060101461020400341466500c48400e5040e562001d1000d030294540491f0b5107050000844001d0325a41d9035600758001e00410300ad54070050060740900005814044140e654095002018020781050544d9205040d001a101c17041000204200f059850110b0070045000380641c1c4910f0b22081e0b070403540c1030902d00c424100d50b8000d102c144102c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 531521070 1250 531519820 531519823
    0x1a010509040c052b0c05010f140414010e090a021213050a0b0601031e02071a1b0a050f04060e0f0a0803040e0c0c07060918050106050a050c0106030c08070608010803040602 75
    0x800d482044801d10241c504d164241c0200301075040b00c460414118903003410074411802640b43c1101d4090340c44003107000418400b1251000c1d800c0322480d1640041c0f0080c03110560080e42031021582c10f2500100e000c00120024054038401d07200f03d8491680011520303040100d00d6840c2c1d6101040442102940510b42c0d01c49a0320300c82c5082c0038101145250121303295a203e5002403802074124a60380401c0140b1241c0c00d4000d5015480c21107080c3c0c18845440e248441d445116449450200d0468240304621603002c4210752050a02c1c4080100c200405600c54240308045c002802155a40200c016404414025482d6980d01103508c2040b00903400c205e242c000004483c00c3c0c500d94035038503210380c4801c0402c0750307203020303045142c4214000c020020480c1c56209a10340e0031507101c00c01248000b0340c000801c90442c0d40030302412000a004000003d54540107900030400342c88034000000d012365613034541164414490b0861146504040c3c4100504c681c05400c8070b003d044488040c43c9401e00e481e002a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 531522320 1250 531521070 531521093
    0x110c04050f072607020d1206082a0d08040302010305060301090519020a030b0108011b030b0904020405180d02030405130218010c1401180303061e0317070503071a01050904 75
    0x720208640c4004400f500040e019144100a01c41e0740301c1c1c445410441c601a46039000a0610000200301c501a0820110580100c000b102c42c02c078003070401408025429980002e8404100000c1c00c840c401d92103054980c0c0520b81c40050140310f18036116030661000505560001c2e161303510036030401080e0000b0a001159510f500d0000714032a022501240c400b20b07008110311750000e49122a03200000a034010306410608804042e032344010150344c40b82d2025000c45400c488044e030000125000a401420954001307604149290080904080340ca104240380032500144040141c00124013045141400311906021001d00d07181075003440c041d140342c11020102002c2503410042141100b1052124010014042c598000b00030f106881c400c84812140d905485811070001c0e07c4c0c100c0000d40400c031000011445900f0300b640703228061440d10f5941c074106403580142c070600420001e21001440820040600c10301c500c4809095150b508001b180c03c1c10140c1c4000d016a6040c420840000c0420f03959 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 531523570 1250 531522320 531522331
    0xf0b030c0120010b1806030c060c0d050a05070f0c06120902060706090609020a170c010906080a0906060503010c0801180c0206130c050d1a0a06080309040f140106110c04050f 76
    0x801c02418082c41c05016201e1a18040d030800c0203000d015070405041442d0740e12488099040700c03d000c0072042880243d04c03400400c541c040d00200c1409201e0f610a0300202900360052500605000f000e40302c04010008005003103d80d500030030401c01c0100d8001381d443c010010400c0042100c1d84107900811400d02c140d020003465103688010880c08c0042d01d03445410100c0d006024660500d0702d5006030321462048038458007841c801c002003070441d503101d4030b0800140c030501d0b62007a5094982c0c5a5050180902220884e88107480302d0011a40da2000d1092055501203076580400b0341d49000d0003803c03004c0c900d65a00030b19034213207030301800c20980004825404c074088658621030041141040300d010341e602d400c90b550142a452244013400103980f111480301c01d07180c040715415254460010211000c910074040a0381040c003076000d00346040da105200e50590b918000c41d81c80c04035904815061400d810203404150506074084c82e10004002c000010f4a090314200010304000200c20501d00c1c00900 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 531524820 1250 531523570 531523607
    0x1051308090303070c1203030501050306040f0605040c1a0d0612050d0528090302120d090b0901020307060c020601170109020f041a0312180904080706090305040f08010f0b030c01 78
    0x540220310b03182001120300d22034025140e0400e403902d03141d60380000e42c1d80e0395056000908050010401707180104c2d00c0d600444c1d0200c140941030b10b40d503031982d0240500501c00c0d1018500c6003c00240310b1006800000c10302d010045032996108a0350044003164142d81244600c070155410b0003000450000ea800100c8009042868542c06981c3c09682e00324040c0205c01d00da402079042c04001d141d00040701c60281ca1080314040b280c403081d211141e90f070300c80b0301d000c000001d121590301300302c0d0341034260003440c0e03103001032045d00c0c0b5003d05501c0d5901552000e4003028016846040100400000c2118405401050400074840000350340c0000c0d4110f26040507007031096543d0481d003401a0048030030b1a403c6500641941e2283c0d94902405031160444142e081744000500c9014039035140000c40ca9110343d500a100c2803e09010743c0300d060080c030001c0c0c012070034800d00704004280b2951030040d0070300a00c080340001c00c00f0625041c000c420303a4400b80c107280c000d034001c3c10407450aa81104d4810354107060541e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 531526070 1250 531524820 531524827
    0x603010b13080a0b011505090a0b030a02090405040b060f01050708030708070e040e0105011811040b370201060609080a061a060708030a0e0a050607260a02070605010801051308 77
    0x850140c20310005900552540c802d0a42a00c2007000c240413082c100e5400181010b5441d00c841402d84483c4644040c01d07a00c100301c0002030043c036010a002d980c100c10194401810b10741c280002c101201c030141c0301694441088000c0121521301003112907aa00030a103000d50030541d150b13a07a00303418000500248280901c480004143e60b01c074000065407540010011b000c0250807500d203500a010a0041c8207400c59442c0121301c0301c403210b025010700c6450005081d441c00780380032264019034100340e081203102403255442c2182015640e403d032424420180d0b50f510611030100c000f0382182d0166006c072040c000c40500030801c1c8100030804035102500608082000c0209150010381c8100501009500410105148042c4614940510710a0080010030440340780741c617011650f50104100020400d500080005000300d12401281fa0301032007100080e00000e60140146241000494500b0040c1e0780c0820032109008150140c24010900a0b008005c0350400001c106100403040030050315011002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 531527320 1250 531526070 531526087
    0xc020a12050d1d010e0d09030206070206070606030309090f06030209011707030506160e0a032f0d030302030405150f0a0c1704030e18130f030e090c0a0f020a020603010b 74
    0x26000c881107498800c004028014440c88000038843c18003000d00d01e990718004130600c00e05000250320203180c3c420b07228854102e140d5402c000c0c103a480f008049130010010310800001420a0050202962298403071200341d03418504008100c036034400046110604004042016884050030a4107542d042408000c41901c0d0140651a0400d581d0004000f84982401c00030118241c11011400e445039a0f1490302c002006402c00040d03049a00002c4d01e0036940d044421001070340710a0b10f8442141d5181c2601c800107040c030024100e10700c4460240c000c00d8001040008008060040c0e518007800107400c0980c4d8203041754007000b84100101080030190762141c1c0645500c0c011541c5075104001c25038054070030b103017030714000301244d08100100340034021880b01454082c8205454501c41c003407100340020013890a490f01e00b00c8515100c020790a00ca280340c1440f04944818460305d106090071144c186d61900c0303843c401020020828001c1003150016001580141d4904c0112411a612102003035221281c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 531528570 1250 531527320 531527327
    0x8030f0702160303030c090e0c041401090b0301060801031104091a09010e0105010f081e0a06091a0f150f011b02120307150b0604140409110402210a0c020a12 69
    0x2420202c8885000c0320700200b007651642105c0c44128050ba83c1020055603441da50444000503918640115010b0100748001400c145808101801c14074041114940c5d400030388203c1c5d4006e0300b000d070000325000018410312000c9020f00480d10400d0307508001542c603503100c6001c030752141503000c0c400b001800b0220721010000d400a0380307214940002000380d941e5036020031a01c884180300d41103142c055003d4089000e07071640040400b44090398054032958103a40d6810008001c001c80c21211140310340280c01600070740c880d40c7c0e446280c0a1a088000c1e00700103840f401c2803e000d40e6003910841e0101c151804690384542c079000200b5426070704007000d592502c0005d0700445031941c0c0101d14440481c01005000c2e0504040d050180741000420142d900c02e414000c0a101d980105000351008100e03011290038564040d08815000b0105207210984070000030b0300360381c494068981c115180340b0040d02c10500d199442c540002c0a070008100b00740c240000691600b28a00020f003001c0c02c1e80d40a980005d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 531529820 1250 531528570 531528583
    0x40606092307080708040b0a0f0606050304110f0a090e0f034608090f03040902120a09032a0203031920031b03040317030702150408030f0702 62
    0x25a0388180200c6040e141201e0212800c2210800001e0710301c0c0100e05841d00441c0998010191a035a1555503601c07a00c0b401c0d10580041c200d50082513440c001070110003c41c2c400c0030080c3c05d8030307542e81c0d075030341410704001040003003030042c0500c47c03054600b00110310707aa626212422928001e10201c2d810842855440c146800f051394010240000034170804211400c0f08800091000b07a112042c54860380000075504400c1d919045c0030b1461207501d513a0146003c3c910040e48514000c04031981c206a00c00c0c4542150050740c00054001e03000718050800c0740041c00e4295001e20308020070004100b81e070314020010754291003540c03412451004000104000b1078100058580c000c0c00320fa03524040e094030380021031a070102801c00590382060b2181e0203940034100c0340b0b00d11002001542001c40d000b202540b05881c0c0800541c051104100000003d04940a40d03601e603040c200340c1c5a1245800b078006030800c00b4294120042c19422810030001920031001d880d040f03c040b920001031661070f04020391901c130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 531531070 1250 531529820 531529829
    0xf100b031311191a03010303090303050309030d09031e030b0a06140d090809270402040b010306081e070e040f1e14010f06060e030a0b0903040302180108160b030708040606 75
    0x250020326442c12441a180d41d641111603912a2204d40c09805800c418640802c0c00000e00181ea03c030070800c0400d21440c0503641018413002a6850198104a00f00031a07001c1c0404902041e00c021110768003070100f200d072400000b02130506212524000c400503a00d485503004040c140801a5440300d84d03c582042603d81e00b04004c1010008410182030122950300815105c600ca40e04400118090104a0402101c094040c0b01d00c03030030903122130742080060014208914109591108002031035141000000300c240640740414020f100082160760400e001d64001d50402d00c1c2032014400000e007140c01414940e50400c00740c010030b0010a4254408080d83c01014104404c440c0401c00c0030103040d41f011072130301c9040100700407943d92968155000b01e000001e4a5264009129220202d441403090682c0b00d9021400e4030b140640fa40c0c00500c103040566807201d405006e8100504c14404204034111000584044240402c2c0c501900c4210390312000b4603c0c0e08000c002c1010400b08052070b000b910290 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 531532320 1250 531531070 531531079
    0x1110a120201110315031b0d03140f071401051005060301300614072a050106030602070b041b260c031e010b09010302030616020a06020301030b0f100b031311 69
    0x203041142080d603a03170156401c140d20a010700d900724040040c0c10903804800002c0039002d4540000551820f071b6514018520205200340100100c014450044001f40340052040040d10380c1c00502134409400c55800501202d203034007408106000680e203c200350383c11030741c0f1003680151a9405108404103c100d20419001401c030500000c810455180c001c0c0107240b0900c0d5900c0d02a6451590031152040107050048286074040100d03034070408840f01207007400f030142002041050307503030390340204a9001203800da420ba440744040c80100400842c0c1c02d84041c0800c01410602ca0420030741c540100051007854a08840b0f811040038050300a00080b25851002400d0303880fa07500810400d03007003081c03400d98006a94644902100c0b14a06000050706a82d000360081c255542c40e0003001d0341e80703600da0540346c0c154491804848000364440c00114041d6120361403210312800c0a88d00e00c01c292102a012001e0140f80b12014080307a440c002c15030b544180101d007029148511424240c4610f0181610107400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 531533570 1250 531532320 531532327
    0x90301090809100810120f121107090606020c210a120e0108010807150212040315060603021801031a031b09010812030c0703050415020106030b0601110a12020111 71
    0x500076584094040080141c6192850700340609003110500411180300c403244d49160010b020b4086050401780744c1c140b1a529900c81e10015480302d071081c0040c1c881c4000000d4014076120310400040c4560802800015400d02c00c240c1480320180d25018003504940c0591243d802d8041e1006001b03021908001d40d0300706840c180940781c01c00a0304040d0220050303010810400c5051459413084009504070740034940600951401d040c2079840582c044a02481144105209901c0284000d00144021481502c001c101600c030003110001b0b4868581c0000c0034584117100c0860981d0780214912178800c0c0c246800500e910304103120a500c02404078400740c251040e04211103040001490145071100116512819607a0f9088429901c1620b9540c120000320248045418100610702402e40700d442420054105512030380582a403401142c01c040050307448200c20014030003000c00b11a0010803e01c1c2280d014903812895a540d0016640001e04110112401d021031034800c1d440030000c140f041556654 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 531534820 1250 531533570 531533573
    0x8070b0411030a1a0c04081209030601090c0e1909090b15090601020304030314041d040303051f0302060306060f0c0d0e01021c030b0a0807120b0f04170307020309030109 74
    0x2610041100c04585511003008800058a00002c50201d40c0382d02c01c003010420707014007402000754030000e0a0424489000e01c00420300e4181480500d81d81d118000001c0d840d40391600806141110690050f40018900b444003485075620101074145c101056507a10b034102c400002d403000391a0340e5800903940518064aa1040203101c0d41c403240582d41180b44404150203040400081c01000d6a0440c0560720802081001900555440300d42003a1008030b1400d056132102e06410f03280100000101080c0050b081004040d018030803603410494a8000d001440004002c1d070580c0d4109002c042e21940c1d0110000b00160f07105400c82e20260783c158541c3e510b03250340c0312502d0b80e10008400c0440100d00380340480340655100007414501c410b00d00301003000b60403840d0025401407084904140d0001c8071440c01150760b4008112001c0104400d010b20300001000c1e082000030007802402d010b030480f0314242840017040c003042e50841036180d61143d042d52a1540181645584504511544c243d403c100c0c1920 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 531536070 1250 531534820 531534833
    0xb09010e0418060e0303060108073905151014040209150c1005090d080421020f0705010e0a0b13090507080403110309030a110103021308010b030c12280807 68
    0x1081c030701c5100144032913a1020503054aa0004454050000340003400040e0202c2c80740c0c92030043c003010990b84582c10944a600e415440e4110064420f100805001142c2000340801619524044c00814408241007107070740640c2e0311041e4404e4101d0015040c1c0076182070707074a59040301d602758002030176000c004030345114400c15034101001035a0380d8054603c008a58101030b0007458030844840024001000d08540d00340c90300503014100380c4041441240040103040c0b0b1907200a0101055001011000b000f84802d42c9030542e15081141042240d080301021502c0307802f4000c00b604c201c100d41c162241345c2d0810f200d403102403d41c007880d1940c0c24001801003a44c1c00c0700c00d40380654040c5d41c90303c00e81061040203d60b00e1260308280740c0c060740b10814500200b4820a00038004050500d0050f10340300791030036041c0008185030000c00e00b40c1d5441d050010035280800c883e4008500955604004200d6800721a40f209908081c991845102280900c03c0b404000305911205500c0340752103444810904100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 531537320 1250 531536070 531536111
    0x6070c031103121f050603040312111b011410051f020a150e010b0a03210e131b02150f0c04050d050c0f03011b0509040209360c040b09010e04 62
    0x5616130303580c203803000c111402d242045a04c07a54040e150200d400801e038409800a200c1907458040b05141400f4014a040b00802c02840042c912000450703038511826241c0701d0814041e121038a1803c000b48100003607180c881d0f04208010301e10b01d517211207200425069041c20b45880004048104c00072040d0083c0ba01940402140555072008019105811060001c4034116001c003410100018107052403005800070120080806490032580c1c0b00c2c4c030302d80880c444085608026141c0c43e03e03100409050b40c008140104491442d200500a4000382200c1b42d200c00409440714203003285107800a51400e584004846c02410007a100780c2031001c00741010741e100d00b1842d0702c107482000b105080c010701b46414081e1821800c412003c1200140c1c0c080415292940300c103498a420540900c200718a175a680880c04a0041c081c2d1002c151351006c2e00e82c203c5410102e45001b240e00202c1c80f00744a00e03083d00c4402e48080d1010404513076a104440310042e0f4030000c0b00981aa401030034078000400d60309404044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 531538570 1250 531537320 531537361
    0x30803040615050a090e0c0a0b040311031204030f0314040b0405030610030b07030225050601150f140d091203020d060602011b2f010903080105010206070c03110312 72
    0xc0001c464204070b01030481d0314901c00c0702c1d4441003100051000d0042607000d0140200e81200312950030f001000070034407a2045070b10240b012000410200240950074000c22000d000403009403000080c83c50540e40c80340039601016080c800407104810400d805200301844000c0c49440058441c3c1d03590000910a900c2400b805019005071000315201416510f1a001075980c00304100b0115640c444086009410044203128010354030118000300f40690944008168042c2024100c0b660405004103040380443c100a8100440a0400310303610380e1040100c0042c5101032441d541d52012502000c01410030550090109912071850901154255000344a0110388075004c5c01015600d18090f800c86000700964850014440d00c0c203403040d0322650307202403080d50a03403500706c41c41200c20041303000702282401d50000b40e6682030f10310305264204d5201d90041c80c0c00d200411682c504110024049540094020b09016600381d043c242003a051040d27032003030724402203041102d00c1d240034561104842e2494 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 531539820 1250 531538570 531538583
    0x61602120f07060906020d0917030702060d06060e180106030b0414150a0902071a1f0b040e0604020a051602040e0a0b0a050702030a0804081606050717060a150503060a0f03080304 78
    0x2000202c040c0081031f440002c03030f000e0711a40c181c18501145031350030428400e01040e0a01081000f0001607540c2005840c100a13000400540703c4c0c01c0074400b5184001890300c85e40704076954a00480c1902051021034150352584c900403c0c40701191000c030303014228010030b021041d65641c0400042042c4c0d014548440d60301103035407810160755803194408910904d080900901c00100b4000b0f906000c1c40c2c902c41d009402014511f0031110841c0049280c3d40c0940c00602251000060421003107100c0d0f80c8280e08044212001c62405030074002c0030f440341c0b040c00a03000d003540010070100103650792680207800f601c0801040d81c0d1100020700d802805524126035a940d024544404680300c60b100000783c800d10b51098a0b9809191030703a460707444407a00f0100c0c0710005035213220b00b410001801da0159502400b6139455003800c1d403200c1480c004019500501042c0a030104500c100044c944480c1a809200114207049550380c9a14001c10f5490704103410484c808503160000008200c030490003035109501602e03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 531541070 1250 531539820 531539837
    0x30d0e390103050c12131a15010e0901050409030c06021c0e0705211606050306120d090b0d09020306090f0d02010c020c040e0114071d03030306061602120f0706 70
    0x340103504841044e01c084031103090610002d1008969549070340e4100d0f050066202e80320b0015980c0c00b65482c002103407104828048818080300e2608061040c00c00341c02400c0c00300450080300040780070910144034540c4540c1e2034996036028140662400c2c421940c02c90070640d5203200c00070020060054841401c007443d86070410030f01c03000b4004948001a00d800500c4e2803801b5140802d103114030f0349500e9648100d4000c070365000180001f41240400101880d4403521340740d1410f28100251046011844206900140c40841860745d101800000755443c0c1c0c1441511407a032810100020551b014000f0340510524060043d0b8040c0096010542e2400d0f204880b443c40000300c0c22030a07a820450000c0142c0d0022441d01000d280c160064108502c104000150308030101516452401095850301d01003140c5034030481501c04542005540000b0030b500940c51820448007058542c4a5032419070348040c44401c04004564540b0780707a00320420224200e4042e0000000c400c1d0300c4500e00d00c5840c02181010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 531542320 1250 531541070 531541183
    0xd1224050112090203070603050402180702010b180f011a0d0603152906030712090f06060914010909080c0709060e0a090506070804061b02010905011d030d0e 69
    0x1400f0b016801c40c0c0c00317805403201c1881c24a055000d0800600300300e034400c1d91080500652080100114802c100c80c0d400851440c4c03440c000c1c48000c000c1007000720550000801040300311070043c0388103811614440c1c40b51503040821440c04a8900401469079040c40c10240000140401002180005045031400704540e2005d00e440d034025020480050008124078150105203142c0100034686c80600c40c2064044c403802e13078a4501c200e548244045aa4200d1854407409101c1a489a00301500c1450b00070040002c0072101c1c90002c1d601449844074130b50711242a0010001b0700415a034001d400b00c0219072585480d503000b1006000f8600441c60b050002c030000510b411020b00a2018060b04400540804c0c1c454910448601c200100141d03880e54543d0701030640780b00c5110b10078903045510b5000180c00c1c4601d00c2e1203800d40b0100220b954041200000c10781c0d4689002c41103850390700e100f580028903240c0d1000503070704044285c13a001d1113401c1100c5209140800c034203c8030707906288800d004096503030702 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 531543570 1250 531542320 531542357
    0x303080603240426030925140f0a030803010e01090b151204020409050d03020a1706090c0a0201141305062a0a1413060813050d12240501 60
    0x41501c02c010822280340428080f900000e0360000c0b00e41c02c81d80400c569948040703c0b10300390303000f40c421203025031101020044a031801c1c01c0030001911101c1c003000000b490504e03218040321001900a104031790900c03002601d5039902e2811802194450710f040d03140d60752800c688103000c03002d2069218550920241c010b0700c0c60f100c210305441c140c040c0001c81c10510342060042c03015200070801c0b40c010b0750f16000e41010480810500080003a035075009039848400e904000c02810b0381c0382c2100e40404102040c0140c643d5030200c01030b4484042c0095580f42c1448a008a003d070054409180e01e54040000f84450344405000c21003172107000f64112070650301d84032408400c0a44514412202c12100209070b6136490018005280714426882c0c08400c04030102c2c401407242d8855039120b0740090700800100940c1c0d070000c0308140d201000040034054240151a0552961b0010301d90380200700040d0188a00c0200503071007a07440c00021420346200740c0c0e081310441c1c1c00040320b000d000d0104003404c001c4400081c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 531544820 1250 531543570 531543613
    0x6020601092c0a05060c09120f030304060c0c0f03021c0f0c12090b0d0f050c0a050711040e060a05180703050a0b0c0702060c010204150503070f0c17040303080603 71
    0x500351030036800d8400040150074041d0052400b510140a0301030200081142000300e01d0040c05140f074215a9129080e0811417240c08010348004c054020f031044a010190210a490340701303400401c0443c503840c861004135031402c80c004000304800e070040380030828164000f03248030400e4038805011300460030181c0185c45104201c128880081c900980031030018881d4142c1401c0ba1415060800b880c0340c451f000d01c025500710340788400031540c0e501000383e031883c0305000301c94000c01c501c0b400611700080c050000300103102c1c0c0c2d50040d110080220005555403103a40c40744003c4000e40d01540c0040c180b00d03038504060030b0161445203060200d2290403a2000001c50010101ca078444d0050521004030b58507400007640003801e40c46601e409100020150700c41200600c044032104000581c0c81e42010b803101180d0407507400d60070400400344100001681c2104800400d880c10b428510b201401625144101350070b206510448d400c40820f0000800d6008000303e402100110146d480350198070340301e12895403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 531546070 1250 531544820 531544841
    0x20a0f030b221103070902040e10050109060203040639050d0e0f041109060a170907050d0807021f0e0906060c0303040b07120c0f0f0801050303030604020c031303030206010602060109 80
    0x140e07240d0180300043c107000703001c4a4400c3c014064905866449800e00200d80181d84281803c103500c4041054031a41802e2300005020700742031482980b400d0040c001d41e2400b540c0903038400e100d0781454101c18003010f802c60221009104140b4980101c0c61009001a0300c0b0900d0300311158802c044c2c3e544c180c640600c00303907111104041d02508400090b85c1c2040f014212081c0c42010760313030b0304104201e0581c507003d004200c2d0304800d850340c4c404072040c46c0300031114480040000002e90000c1d04280180c1c0e9445054000b00d0f90400038960726a249800000c10785405c0d1100c151070071150175541c04082d80c004180d90004801219002e581c0e64400c1d00380610f62051101c0007006800400c00900007900170714000d5044016440c181d082e007490380c0c1c840b400b2a46800d00d1440420038144a010a86500c80700c0f172548980700d440c08805651410b4042039503400044d0802e417040d900801c40808030101081130318840d80a01e0000008a50360781806501c5503020b02411005018010000c181c0d03907081d014402108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 531547320 1250 531546070 531546121
    0x80703030b0a06020d032309071502010209010c080c190b0a0c05030f0c0c0a050d051207020c01120507021f0c2c04150909061406010f0801090c0903020a0f030b 70
    0x105001000720300410031582d46d0304070755243d10104007051f680b26641e1449030f40d0303400040c4a0b03941010203290141802c0e0319190110b80c0100812201030b41d0140480c3d000c6940202c045890b0020702121034200b40d92484014a05600c3d2460003003401305881c6690b0154020b070a0810000c0d4150208032902c1c0300c00c07a81016003140101c04103510700403040c000c10400d0307a400f0550300c074001665901814910b0941e4618001640030800d10b0580c00300b09400d68000841d40014240180000000380007124001503006031103035200c00241c0e440340203124403421200d107a1f070500380303d00f6410911170051244076406400203001d013804403e02c00d13001c0314607a070304140c150810a03044140420800944220a00d06001c500510310008451505000d40c0b4125480f4a801140410302010780065691004080301e0410400603000c103c855041a03500f8195100c40314042520310002c0000d5404210562000f1342004400800140c150081c21001003641d104407280c00540d140c807040da40504010481c0861003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 531548570 1250 531547320 531547333
    0x91b1209051905010204050a0312020d091419090c090807060f14090103020421020405070816050d060b0a0906090e1512010905060711150f0609180a080703030b0a0602 73
    0x4015400010402d05104900140c60702d0b4450000c80c400c80030300d500880c3c050194820705070829070140614850001e00e81f50a14080d8903200d20b240c01000940070345400381c80041090134400c0c0304601400050001d401040c80b10407103030040107116240364031400c502400380c0480420b50900c0f030b90322507158118684e01c4030342c00c240049019040380d00901100741810b41c02c100c001400c00344c4009800d0008503403000c84441024078018802640e8000380000d0401c140c0703008000c07992103d4100701c46940620b1500580f1604140c81d058010700d116001180201c20101d00300b00301075801814001628010350714031817100d0b690004440c00300415102d0361400780d050301e0300410b142001e010110709c4202032400030500b04d1aa80320f01d414140103842d45000a503060005540c49942080028016540c03200f1a0501d850f10001a902c582005444075101701d1950b804581103910103884224005205422f0710b440401c103140500c11940800350403030120f41805500c410724607006190000b205c00c10f40180c10ae = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 531549820 1250 531548570 531548593
    0x705060a050a090e1905090d1e03062d0807030c0501211b0908150402010e011701081b030a031e050c15060102010e1b060304030504091b120905 63
    0x10150071020b200d208204042500140030412140c0a600403580041900d10924090f040302003683c0000300034440641c00145960350a961001207012105081410341c01201c1c54900c04402800d050362010444005092003c40d20302a8410040c3d00c0c010514a01e80c000ba43c4d4034440350310340c00035200140c620500300e0f81c2040594002c601c0004401880510740c0c1201000d400e0f10000c8039508601e154003440003412a450301608003103020060040b840c020b00001e41001c101d60030714000104003c1c1001203825442005034001c40000710900c3d00c41781c1145041da19002e03059540c1a8140540380401c10700c1c40341c440340381004901c0e040c00907003541c0c4070030082c03881c21240c8425030850541d40d801c0040410010385508018050b00350070700c1e20401d00b5041400d10800090a60320400341d0540d141c0c0025000c01006401c0b440c0b0516820801d60f80240c0b2036890741012f640b076001d90303805510b050341030403840d41e42e01402c040f5603485200c041e03c0b03003a030002c040c40320304085030481ca9009080307501032180403d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 531551070 1250 531549820 531549827
    0x16030b0d03090b0f0904090312060f030b13030903020d150b090f0403080601050d0e06040218160c02060f041502060a020a0509041a191d040b040305030702071e0609080705060a 77
    0x9030310165016214a0519864045411247d1249040d00000d5016058904c80c007420b003e014014480c51140510060070f5850702070510201400c0745415201c8010b00808050240341c9040041d90005c0010b0518907490900d40d501e540c0780103041c4003040c03800c003840c4018580710f5a03a5000307003174605074810140e5403650183c41c10030300509404d040c4031041c00044c00010241c09003160125a00001d814070b42864410700c02030001c104a0f00102824000800a0302c068540e425003440e0981e2609623050400e6001203106071103072240c6044038010000700414007058155050a11b4081d42d8200c030380507078800076404201e01a5403000c100003030040001114510b03160b080240c2804c110200317456058101c1e40010b1288a10203040e0041d1a00c0c160b082089450805101c04109042c0101800c5441c050380d90400b00900200000c061090100c00300340414420050180504540740c41141e14814240030301c0f4603103d403441414000f41c40c000c1d01041050000c40c051003101e4003d070030a42000401c0900340d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 531552320 1250 531551070 531551077
    0x6040e01150309033608030438030c040308030a062309070e0114030a0c1b02010c0f030509090403091505090a150c05030f0406030c03151e03060516030b0d03090b 71
    0x100c0400d4040d07480d540110b8012060b1000800b040d5004556562916006800050400c080481c1271401d10303c030580b022110106e84004400d20301c200e6270b920b648d11b00c0540c080c7d0149400c00760004d000441000020704296210806a59484220b40c801c600c812000034590703444400c1840d040312001011030021800342c01c01040000f814180081042e101120045103900304541c42c0010039190039208000c03030782000c280e4030f10301440c84405520400c1a0006400c0b401000c40007131280d68010240c1c0f084c140310710291104158010b1110040b82000d08004064101900410084900e008400004203000b00c0484001c0100540080c00c03040c50b06090400d40981f1090480901280407681c0c0d00299043c00100806070400c1000e9407124200385000302140c01380901c0b0800e142c41c0180b106213801d2060290310444d036803003502c200586100f00381080501c2031580000e042604113814801d81007001c285451a101030747c0e60420091410b0400c0002000e1401006030108607403c1c014002c2502d1070005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 531553570 1250 531552320 531552377
    0x8270a03061a03100b0916050f031302030a05070302030709020c0a06050702030906030406050f0a06081c030204080a050a111c0602070821181b060c010b06040e0115030903 75
    0x709001030b40c242c07011904114200c2907a1010540e100d01680c402c0c41e0480d101d9402080c15008a60f02803c40b00b009005441a600d40c003e61000200008a8200001100d074240c1c079805015a0058201403400583e2040640000c910900881c80003191000c0c0a100781e5800c03480490041000c2c1800340c41e580001c00000d4003440450000301311000960b181c0d00c008500880c03050a001525107060300032629828005444441d8450070301008006042001a06150354031003400009010418418168020311030b661000300b0078042c4040c0310342400000f06003050b81c107005500401c0d848064004200c1e0500c1035049101c0c6145400c00342c040440da0302e9025100bd0341c4100c04035450080088822403402c86040d22070310210400e0301c2008040d4210f4480c0f00c5201e440403004040803112200602e045e01031003914280074420100314009509402d4121480e081c0c0040c180a503125103e09190310046024082e03400880520904010340622134441c08000316015075601c040030784003260741340c0b041840040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 531554820 1250 531553570 531553601
    0x9010c08090705280b0a09150c11130c050c0f010b0a3b06120606010806060a03020d020c01051b03060d02061c112d0d110c0a08270a0306 60
    0x3546aa03d14134801008043c00000349401d481d408580801041c0720290742280c0c0348c00710040350850300b858118009021044c0c1c840d032000102007002000c24000d80001d54000b04e81030070502862081a003020003000545a0441540e56088186294509881c9155929500b2080b4448100310a0041a99554040150781d00500150b800400c43c0b46084e0008210040c900d030041007484811324204180c14500102c06001e400185400400640b03490303c010001030041000152541150f4401d0303040b10100d806c1418119150019010000e000f40412034070360400d00400054040420b039400305491240340000d0040307031056404d5007400b030036420840750018000400e025405000007070b0301411407158945000300740c9810b041015501d03d082c01b1410500d028585001001c100030748134007100c100284d40c40012544e106410403100061080c41009906801100055000c101c11000240384150f001c02064000345401d1960301081121540303e550311402c1c001c4100000fa040da040403142d24081103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 531556070 1250 531554820 531554869
    0x304180b0a081b2b02010503151807080f01081f0b3f07091503050d11060703060503030313052107060606110303191805030309010c08090705 62
    0x10301c440d1810780001d2943c010508620b8082c0c01a0901c14903800c903840c1600ca00c2c4100805900072201050040364000c4d0410400000040d500e0388000c4020b00451303000b60807400000703426400c6460001082c0c4030380d000100b510010409c0140310418050503245882c1c044d06201709c29018a001064a81c0050815151a00c9401d0002c3d502c81d2008a01080507408a250460b0540f090b483c80c48102540300c00610102c0c0d554044070030303002500000b46c80c034030000040d10b11604559028084140d0384002d00600c9058071104013150701c070840c2201002d400c0704441454803202c0098041d1a07150044030b415a00c2840081c003000d2070040940c45080c05a0250350050510031501d03228910204100c07408040002600c00c100425449200000c0502d864403420310b0308440c040503241c1c03001810107190358041c0481d2034420350080e44a058040c10f041c0b840412030805142060700ca400884280c107071940791003407018005001d546a14854100030002c0c01d400d41c10075042266414110b00010342030046207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 531557320 1250 531556070 531556079
    0x608060a090e1006050103110d050a0b06030c07060c0302041a0703110d03090c0b030c1e040905071d03060615070305120103080c0706050703170601020f01050a0b030705030304180b0a 80
    0x2e2080103280c06503107001c1d01c9400c194801c0c00043e5400d1368451410540f40a01810703080e0344040581d0010311109a005c40c141c2c9840ca600300142c4000c07808194407903400000d01c603500d1402401054038034856181404492010714041d0200c0c0143d1180d00080c01c021404070410943c00030080291a02c0380c2400348030489a240c800d4980070700c1611060100f69514034920138410410012002002240660f13865480c018850011901501000d60003c8466421403c2520310003810b56001d400c40c02c80420051619080061445002445110307200306048202003103400c012425500c140c0c40989050b8052244d60b540b240c1a601c45401901088001c0c4170865001c0b810000060082d13010342c150030748501e0145112070420722923a2282090080410140740000d0b00400308246207060303044444035030b54400c00140e04190398251000c50365480c220805c45404400e5220703410500059013100c043c02d494009142c2d0324400c81c005c500c0111445007690b41041d9080e00f03c00304034100501a0b50b0543e90700e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 531558570 1250 531557320 531557339
    0xd0b06120d08060a121e0512030a02120901090209010e130c0e0405120a0e0d03050c01090c0f050105090906040e01091e03030b09040201120c020c0a12050709020c0303010608060a 78
    0xe08084000502c15005201c441d00d4001224409001c050104c005221010f40d604000d0719a40c4e42181c000242c401050420f00c003040c000b0b06a801d8020300d000d0764034500080321600039880718030340748180c00820022403058041481014411540900b00c01904c0e42480041001094000c0c496210031040d880707000001004420100001c10240700f8120302801c1c81d190203404c1054010009440580c140310b41d03041998050040c2d4440942607c0583e400c0b036171800e00701c444d40300300f4000340b01c95800d01414104010301d10026208680200d4030600400741c0f517000469046c860354565a900020400205070503142c10762024010410500002840c440c15a48010035248540c008505122100c104a001d0580500072404290740449051000b490b1a80c0080c0c211206506002101c039a40c00154000500821902c0d102c0c50000b012201010b54a00d0b8501c0f41400c6030004a40c00d005410300002c50810500035116948100c5000c0c0d0300f180e00742031040b201c082d0300a00c0294071956035400080c90414 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 531559820 1250 531558570 531558583
    0x6030302010623010c0b0621030304020a05030106080703020603060d050a0302060403030b011b06020705071e0501020f01020909040b0907031505010501080609010f090f0902031207120309020d0b0612 87
    0x200340c0000c0340003803504403e1000100c0002c0c84409401081e041035240b40c2c0d110031030300960307640555111400c2e10b0368400300d074902c0c200d400751070080741034207061b5a4401030010245100300d2088883c48030860b100c800f41170a8500382d116040d25a44400d00c20300061401c0360186611010150403446117a0203512005e26280b1141810b60258211605000034954103014007a1032803020b08012400c001c034840ba086010b81d0306e0101400301035002c00c0440421005000c19401468034801840001445064048003a400340c0714050152040c8440c01000785010b00940700c800b80010071424140c0c5d40c5444035040900014514003441c09900c0700400010511303a804604405880c00000c0d4941c14400050b14040000c0c007080c0c42842110010003074001908002001e03a10612004a100402c14030200c000c0c180c0d491009516014120714403c4174000070025004c501d001c1d0383c0000d540a24150f054084034190280650044106003404010036552800ea642000b40034108408004204200900301034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 531561070 1250 531559820 531559823
    0xe0d020d0b01060c031d06030a09082107180e1302030f0d0306090e060f0411041112040c17030702010e060d050f06041d07030227070905030105130b0a050c09040603 72
    0x1079401034100103055014410100000c484a000b0000c9041e5800081e090301004122108071746c0c2b0b031100e020401c07078644180c892003002d00c40d0540380703954001c01c104a0710f0404c50710100058130129001401c0b005249030902202d19001a0803c141c8840e402c4d989a07150424060307815108030481e0b024171600800041c1c414001554001822900703200c0a502035071f02e490802d84544c1c5c044414000c00700401040582c00603440150150824548000301d800b0b44409032191741071490105400712920303000400d40c1c0c4500d1240300d11200c9a61104400500d05e080394074440340a60091040c18019409404160040d8800820305420169011001815500d0844002e05080c50050a00005041c980501e006500104028001740701c2000340341603940543d4400680300305100c1c543c421501440455105606078094598001e80c0b6002e000503109105031b00c030f158041e601e04000520418840c1403107200d1150300c4115a50191107640859003d400e002c5c107000c2600008012625542e0317903503c2200000d5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 531562320 1250 531561070 531561077
    0xa181e0203060a061d010c06150608060909150c0c010f020706020c01050637150c05070f0303090b181f0207051804030503130b1e160e0d020d0b0106 65
    0x340340c07071010322034452542c1d07028206105e49101070030350083e0a500e50100584082c41c02e954100c0640c2415030282c41005e42204022158a4010501c0c50f405030600b442503d040c1c44120203034a8031801c00b41c3e10704200300c2c00c8041c1040310300459101d04488009108400c2150004551102d140900340201e0b8840c0c0d500701c07a0141d0010b10403a04060a015003035100e581120501c0e40a40d100070380401000c40c1840386000c0190802140d40d035070400000800192601b203200d041d400c030182001030000b041c00c00d81910305116110001540c85030185941e010789616a540900161400c1d6186400360400902c01d1011071000003006410b032034011160344080f4164450101710500c82d04081e040152035007280f0701450f00550b400c003007000c1e6200c603240c0040e03062401035526601c042120200b4104224010300c402c2480e0140215810000030900000f080d200c0010402c1e26480103211540c14002c0b0184082800301c11300b00101d00e4100a61190f041c00074001510000043d41d4400035580240c2140c40030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 531563570 1250 531562320 531562327
    0x40c0c02180f01090b151201030507090605151612020d0f030e03070b070504120503030a1406030c0118050409060606110d0915110f010b030f07050a181e02 68
    0x2507207000c10781d4804a5000d00e02503800d6040c5600404807442d014020110640d4480c06040d0454450a21514202d10410082c4d40c41d04584050141484804e1006a41500c2994000b04005071140700c0d80f0704855000f02809000342248210045507003066042075451108280f200300070a40e00d0f100526020b4555024042d16800d0340001307000307900d850044108152900d680e543c60045c0000c2102e42d4a90000f90301c0959545030381048550f4410358001954406070110141d040000000180d40104400d4a0038880f07071a107030700391640c642011900749505038444648034040394001c11202c50420040288140c4090b280e0010909494039040d086415030703940d00003044155030010010440a070b0f035201408000c989040020032200d054001e00e100100720050010109000e405403988001c5400251080c244a048e130b06d5000300790031041280a4002c84d010300e241690701156480580780010407402d241c50902c40720301046007403044040403542e55103421211601c401c207003800403044000d50140c2e8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 531564820 1250 531563570 531563573
    0x1c0303051008070302060c0f1204030309050114030613021603051803031222020d0f05060106050c030406030b0f03070806090c0102030703120b311b021507030b040c0c 73
    0x112030000381084400800d400701403080540105441045a40446070240c80c3d07100e11180c0380c10401041081c0c1c126104107020b0000554000028108690107031312140509031750350700155902c441688603441c0c401e8003000052042e1030584508070b0207a1075440700604000070905560141c90400005402007032020484865140c0c00d10345424500c40203401550400082c0396500042020180001041040102e014100001d0785035283c0c3d04a600284000c1040100c1d042400b509542c45a058030380c0d0203400c0010805501541c1180c900a24013070003145001d2505200324001d02c80c03240c120b54090b40b0380254003e15134040004001400030030700030b80002d00345100c41c1d52509003180b14035810340d001804001b012a030880490341c0c0ea00d07580c00002c1000c8071207000040c5c42c0d10282000304032035030b20b01003100011580f10004107980001424100084414403a400700820110780c911401644142d603c500040001006a900002e40d07040200f58200030100090964500340f100c100090700001c2410b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 531566070 1250 531564820 531564827
    0x519031e021306140d0501110324010306050303190e04090b0601020d0e06040e060d02031c0e190306020f04081c0314060a2105030309030d0c080f04020d0804051c03 72
    0x880c410610701c200283c516241c4e40380c10070890030300d2a41c032400c0e541d0042c40c244402034100c510400000325160f652850144180039454501c030f85012007200e11522400c80550007841540c042c1c1d40010025420030081055521030050340795404010802404071181d166240c07801400c01a500c0f40705401d0403442c00d00002890810351160075010040c1c020b554442c00d0300d80304222307002d1340c40103804054160f403203501098084411240c001e4040c0305101c9440b05c1d840c640800003164224035035404d46000000002c001000d5000051000e51103810082080001d1081d4000c004540d02007031241e0806075a1080a41007120303184800031180d5030b0244a000195041c0700b581c030316034114010802141403c070046a0344006501422448502c07964041003000341a0040e0440740780d003c4101c81c1c0d00c0c80d02c0c2b0002034071380d0040001d07185030b42e0410038240c50031401481600d20951540c610300c00c040d0b486408011000f85000401d4032420400c2102040c2a140e0064044d004032402c107400e8452039036490001c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 531567320 1250 531566070 531566089
    0x4050c03010b040504090206040e0f0f090304030302100c030e0a1103102a0e060d140603060712021612020d1403130206180a1d070e0a0519031e02 64
    0x80906110410041c400c608a00003650240c030303802c0d035001440c0800c6102045442c82607402c500448002042081007240c04150780c9840303002c40c0c010326681500c170011896074900440c080140540c1241140c1649028694041541d122207403a01090301d5040d100c02e5030502c644060140c035500107408a074282418100580110b81410305001c00010000e0303442c41700c1d99a4100c90700c00c2010381c12030054943d94400e008059141c000100000d9903601e80030380e08030081000703000e428000c40080d000106545804280248184001d03210b0440070311400002000940c40300c4034202c0e18a14921504020406255007020300c052660020013029004030070241410750103000580241e0400c10030000c2030021202501c002c01e9058a21589459101b5500d0707030070242088419401140040340040c01c00b0b0844002d40080c2c6900e00c484003151502d0354200c903410041c0c005a500443c0c030202c104041d05100300d010502584843c6284500d80d101d83d40c48452446284840c2c0700d00d04016810360541c6448030700e1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 531568570 1250 531567320 531567331
    0x803101706130201050901030605120c0406050301090c121401110c0613110118030516060f0903020312031e101a12011a040e1906080610090c02010b06070f020405 71
    0x14100342c50400854074621821040003410450041208646a4065086800070700001440c030756071f0300a0701c446250307201c00c1603500505c2242001e000040608061007100b204580105030b1040040c00d007055a03100c4c070610001114a10a02c58045814001c02e2140030008040c0c0c4000c40ea07a65100c5429600d001030141100c03032130004c14032440f00001d016012a4240c01001e0a00349020a202160101d25003080d80c005412401201d405c9280d410480b0400020799503e62960390012078000c03c101c03200b1040740030094065005582d200c4c2c030403d600018543c440700c015900081c1003030852070310750140d00c00e45110320708407042c00d01030241c0511800700500007898076403802d0a2061150340c0305508001031080c02144201c00000192007801a403c58001d030100c81d00250950504d8160351080c0191a0320480071240341c00400304460401051890086901c40d000c004040d082c080b01d1401001c0700401441590342ea0b2450b048541c680c013000d096280d01403402c40380140510b00502c010788800814 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 531569820 1250 531568570 531568573
    0x807020a050f1f0203042102010215010e0a0b0f0315221109090a05070b041d071709010e010c0c0b0108030c0601090c03020702060324031b01030906060308031017 71
    0x58440c59103444056181c00d100d2840c600d42030b0003c140303090f0304522494120f0680c04400c1a0300c43d041002c1400310f110050710070380c00c90f0441c1c420806098100e40c0280910301d0f0710b610031b2010881214040d00041c4604000924011464403144000384c50b00c45000c8001c01c0b03800114040100903141c0320004215403032040741426941c1c0c0700d6941c428401c4441c8c0b040c6172251244c0380100d1113041d002c100340c2c000194010308403101c50b516480001035a030014444c10fa425400c001c03041e690074418200d040d01608143d00e0303540d1052401c5400d801542c00c000c0641c40c0c075660342d14500001010900078008020140c6e103031040074403060300340941080e005030002c1e1240d5000b08060007041800281c4a41150051007000178a01c1c84004210003a2142004c06540480040240900380b501e6603158040221000380840c40800300400340354803003214911101149498803000c41c40c1c0d5009810400f0381901c0752000203815516907036250120380013521910703c46881408180060381c90290074080c0e03c01c0050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 531571070 1250 531569820 531569839
    0x19050f06160e09090313030308091002041802030411130b030609060106093c05040b181308090d030203070b0f04080409020703170a0e0111161712040807020a05 70
    0x4201426403030390140440c0c01240303810002010720b0000d1082c2c1d0200b641b0b0146c0b0000706036580c100144000c0040d5041e0319580540c0040381200b18031403080354100c031800d94003e00b6a0800020344402504010015280311449202000040c4d8030544581c00c001c00301c50740024640250028543b809a0050407a03c440d80000010f002e226000119034040702c180c01e40484c905d041c070b0814074803d802c11400300440e00c2404003119000f0942c02c5841d000381d600550b000c020350701c40c10082144154a0301034443e011801301d80452104054000352843c0f07240142e070084d251052500106005107240d120950051b08081181c07c20041000303100c07070f04000ca00311030900c9410281c60307440c1c080c4a64862000041d0b80010340300d0406001d0310420104800701c4100e01c0003442c104101c0c801801108003102e49a501c1d200b102c0c1c2c6c03c00351090a540d800d1416524096030018580c0c0c405408129401c0328412214003840040221340e800c0b44008c3c880ca12448101d61a090a81306110001006400051181d00a80b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 531572320 1250 531571070 531571111
    0x50a140919051c1707020616050d0204080a0b07080f041203021303020414091606020703060b12030706240806060f01110a14060703180809010219050f06 67
    0x540500d50822003541c9494000c107403034201c0c07510103c886a4290740103c010382d641d6054000f402c0b00c1e500d5480d1a1100c0441c1d50300b403400c03070b00c40e80e04840d034440303440818110348896485003001e4041c5040024005144c0780c0c864241c80e2034014040011285580c0010400c42c5107079202d070040c0e42004984651111905155503901d5920900c04002c5040590100f00703070418031100380d0305200968020f08100490301c400201c5080082d02265102c510340308008110b1040d00011844030304413085607024008407825540c0d00340c0640080614598482c0c6058000721488105000030403880d4030880b00020b9400c0900c080c100108100c0190301032500813190300300701d10003012842d998000c50484400100e103608400580f241c80110000c0c440900c686528003040080c40c421080070801e42004855540d681d010040b0f050f2010000408088980d200400780050300e0132010b40510b50050041d40c030315104064080909901c0502d096410f03910011400105400070300501e9000b12490944d0019105d80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 531573570 1250 531572320 531572323
    0x906080319050405060d09110a0b0c12270307081617120703120e0d030f0f0908040e10050d1a0f0c16061e051e0403080a0218040e01050a1409 62
    0x40c3c3c6040a08a91607041210230000c1108030107095280043c0a24a82602c03161440419007061050100703d10980801d103240d070301050103448a2103244802c800d103007146d800e80c84550503140c0c2c4400b50588a284000b00304068203000800b4012070701803801c10414074145008604803e501c0e041d500c19000303019502c6100b051701c012a41c602e80c01d4180b451801c141c0e140743c18002d2211003101c0c3c0490041c604d22140300c55140d00611a2705070f0100051041941031401d00080f1800382e60002c0404104000405c1155104010141d20101c01e400200c2c4a541e1640454445440031a04590792120440c140d4034143c0c0d02d410641e000145480001068513091944034410300c650031215003081101583d1804000e12070b0401845440301002520740c1000c444030640c040e1906865410390089501202a243e801c2036102e5489950543e0342c01c802d9031506060302e0300a42c0300000103440c0c03030380c2ca12080388103464a010300b503a8083c4000c00091946080000d0404481c0a01c03074900b4264483c80502000750300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 531574820 1250 531573570 531573577
    0xe01080109020406140c160306051e0907062007060503040c0e06010e0f0a0b041712071a0a0e030703020a03081609030611070221010606030e03030708060a090608031905040506 77
    0x8003c010b85d952214800a805d1510aa42c0c000c4031842d1403440000c000c000058000500484404411080d415581c5102704a2000100d42290880d07121590030829039115032190100d041568003c600030410ba4203e0500342000c9400c2000410b400000780400c108101c82d102d801021009071481282c100036000800c14100d1000d158400c1c1547d00300880d040c1d0b030312540700c4001c00d4840040c030f90b11360361600340340083c400e80c800100f414000c400b480f8030340b0040c1c0d208890a240c0e0240a00c002d40010790003610a0001c0070f410128481e03614121000c0c038110400c0103041d0356020f500100059a06490000c1c14a10014402003203010300011907070401c0c1c0c00040b0481600c0d403041020401c14103251f00f172100c0d8002e42c034010b0741c404465203413601e001101040c080c2c044203030a002803210540703504055054507200c1460340002e0b442000018840c52013100300c1500420018140b03030015684000c1c1000b0f5580076081a9000e801c00102072800c100380c0001001c40007290300740582417034a000c0004480b0302 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 531576070 1250 531574820 531574847
    0x60c0304020f040b03210c030a0c02040f020703200c0402030903120709050f01230403081c020306010c021905040203070207081c050a110a0614011d040507090b0102010f09030e01080109020406 84
    0x108003e482c5410f040c20540707d02e615810f00710b039141c548a1a00400360b0607184400e0f4000c80c0348c8614060105014001c40e000150141c981c03200c4040c1580d1098502022880d0003483e070f016680d4030707c0f03043d82e46000231401425604000c603142d00600c07102c3c1411981c003034500e80c01d00140340000c0096440d9000c504100e0042401c0090f840590700f000c000c54610740003040991380d0400280801084568030140a003003d0308002542c0e59116036124804a20080e642c142c00305249074007510051806c0c0c1200907403000c0800d00c00520340d54520200b4243d070000d403840000341e0000c20040c0100c4008100300c0034070031810344c000c2103075082041000c0d00070700c0f83c4032412040109541c500340c4204403c001d01e00b511a0700200400601d11801e10b0043c0d422002c0c05101456140100c0300e00c0700562200c98207000d190088007410006240000d000000c003809401b035030542d502c2d80700d503581610f00c510566138206d00a4544601d155010000141842c0301604080740040c410300c018424158009807003c5402c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 531577320 1250 531576070 531576103
    0x309051f080f100b0f16080a1e05041403011e02091c122006010602160503010509070e060a0513060510140a030506060706051f0801020a05090f010e03060c0304020f040b03 75
    0x149240240402c1703078070690341003039101c00d0401100310070440160010241481c3c0703035651549621222040010342a5200300c40000100d05100030302ca020b01090341c58036006001030000480100da07060208011034542000ea801c0ca030701150345042402d004411010204100c0e45182d0800210340e01c041445076810b1480b0100b201030700000440d1803a544100c0d0005000804440716503a45100c000d5446c0090001c03110f0010b80d0183c0020242014003846025543ca500a000b0f1030b400e0180c40500c40c0d50040100b907016854600008194403920404066a2882500400c0a0b402c2000f4088000030311a502003c001e800414401c40c40303115810341d0340210140c40c020540c4d07100d5100090050149000241066241c28140403013500c0103501071042e000100450220705503502c034032500704d00840d14040c0c0460010080c8003054600032000c5c0d11401c00504152109040410101e403410701d007220b0040c0c20304d600209000552502e030340300c0e000c50041114140004212400800c0d00c8402903035082005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 531578570 1250 531577320 531577327
    0x312090319020f130c12050f19020f0417010b0f091b09060a0c0302010501060504050315060a12050f0601120c0e0a0905010c020a0b0604020703090506070309051f080f100b 75
    0x840d52800034801d00d03118000e00c0302118650f144d035284d00800c4074101d12400b02d804152400c41030241da000302c134403132100c0728180c800945e10740100283c06c0c81480c007090895642004088103080f80c800c051302c0544092484d4a00d980f03826007002d402c403540e41c214548034000da0a0100515034601c10aa41d005511060500c050801e80c4000340550040d442d02035885200404c19160f0a0b901042c4586c00d039010760300038007481c1d03a10355054449201d030340109a0141c102038910320385000c605040b150001c4003d81021040b80d0780d413128200f060b0383d60030100c0e0760750407018070503007500307002c0101901400b41d604411000c00c685d983c40688805041c810120000032103000282440c65541c040320b243c0e900880280413040e5101300082d191706e2040750884001045101144c40d60500c0e00c00d5586455154891084550400e0200420b43c0c03c40003044040000c100320110311900c0305002040149000030328950001c000420142001c1d10051145c0345d0000101c04201040b11280c3c041e20440e0300140c142070386c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 531579820 1250 531578570 531578573
    0x1e0303160f03110a05030a200d200c0d090f0513050a09020414060307090203091b060705010e100605030a2109081c030507020a0b0402091003200312090319 68
    0x16101c502c0c0701800705000414030004c0c20750440021440360064840801c0790402400380c1c4520342544042c0007591340400d00c40038101131195441185c0c541d01d040039003156261407460640c85d66010400300034a076003040381d84103039030390f004951070001c2e14030840722000041c100004a2040040000d10381d1500b515000459010011765202c0e039042d9070050014040304001c003c0d648545402070354514007a2040f00000140d548803842501c0c06203c850b0081d05012180f1900c00381c0700041000307512b82c000400c022281c0040c0007403040500040910018080102a200b0340c481182c00319840b46000b500801c98450008000c001400384080704000c0f240020070032a02d04440d0f034611900078081612030781500c5586000c41c0c03500d8644d107030b407290b4081c8a10b5442c80005c0340c44800e04800144518031a0010400500c5c22200d8a58040040000041100d80c0c80e2500001d000a00c85442141221103051200780d0400f84a0b2085030300c410302034246802401c2010035510143e0015444046190000c00340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 531581070 1250 531579820 531579827
    0x4030807031a04090606051c0c031b080a06050a0515030d1d120c031926070606091406040c0e06070501180302101b0f080601030b030f1e0303160f 64
    0x41030100c00381c0100814130382c0345800e8004100070300950b4172035000345000f90480b6080c0b40c40c0d5551154040e4910100c81d1556485001141c108101e45d10380480c9000d01044030181007041c55115801a08082042c0c24000c07021021981c001e400b026100c82c058962050030345001440c0e09402413a03240120610142c001d24442d07a000da10100340d032002000140e00c1026200040460307024808505a68401d08801a819980e01e00030000500c5182d101d6895809425a06080340602e00c4c5000e48030700c2d204995841004840880d00502055030780d51211480c18400100d506038041d000380c42c10821240003e0014040b65484480c15118030000101a0100b16003074000d80900000c0d0150018a41201d20f4040d4803512108588100149014000704102d003050314030502030106501c8101c0e402d01b0300340c0200c50b0b94200802e02c505141c4c891000c01800e84082102c05c24032000d000142c80a0b041001d00880741070240700813680386520034000d000c501140c25000e031180700542d04055004050000302038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 531582320 1250 531581070 531581111
    0xb060d020f090a06060815030d0c1104090c0303020f010507021c090e011d0a0b0114071b06050d0c030209151c0c0c0c06020615040b040b030111070501140403080703 72
    0x40380c00140c24401c0c0403103510160800000c0d10441d845035a81d0780e8a00c404408030030300f8020b0441c8d042d40320301000400c450203441f150807400d004032524026110000c000c5806d80d44401001c8548054560b000c00c01d159040c00602d0040303030404005d203e01d0804ca03038020765a80c1c1c11881c1c1c038080b15181e54500c40340d41c080c2c2410001020041c07071400280d0382d2000e41e03001601e155200c0074200d0000740c001461004035482051842e0405031180c410340807034401e01c00019040780700120340c4280e80c84000c401802c9030f1942d4500800b40c659900e566003200003070f42c0c0306485d8de410400040c1401485520400d5440c0301103e51000c00064003545c4030300040750310070145c44440181c1d040141c80c000f1600303002540452045000c40c0034042032203d26a40b20012a903e18080b24040c1e10014000b0703040c0528541504205075800000f07001040c2606507400007400c40b4003480136500400000907000c4100b01082c01030088048400042c03940b10b02e0720f610003600c200d000901400c205aa0348014002d1241640f00d0b2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 531583570 1250 531582320 531582349
    0x70e0d08032802030901061a04030b0a090501090605150612010e042307080c0901031505040303110c1005010e0105100302030403170112020108280207020d02040507090906050d0b060d02 81
    0x2050502e40c03580d5810002540199030620030b035401c002020a08800f000038220744501103d8060f480e081ca5500c0300c402c908009040c1c03180041d1a80e40d2400410402d018034500d8601039100020a801e00b41e100c482000c0c19444030350301034034082c0074000840f211980c6031030440340702142c400c0b0203a41d030b480c18840510560455141d07006070500c00601380400014108140d50300d003012a0300e1b2111000400088000901c4000c14020b00900180c02e03504c010f40040740c22900c00c0c2408608200711020160780c9402c4141c0f5a0f05030b0b0712101071074040c01e83c2c0740191030042401004110a43d41808003180102440c0b502e0030091580001c082402c0611511212082640500861581d07507102ca2544181c10300441050740000e40d8640803d480301125051110403000343c15020b03021100344d81070b45005c0d420004c0141d0b4030043ca0072200d005601c0e140101441040e4913031b41c0140780c1d030502d10280110b443e030390001c5010754081811040020405000c1940010044424801e4040e003880080c0820108020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 531584820 1250 531583570 531583621
    0x1080703260318010e03090904030309140f0c0102070906080a02090c0d050106030b011808192303130f030203121b0a12230403020405040302100204060c0b070e0d0803 73
    0x401c004070b444000341826801d4428005d0140103001524540d5a0140042d1982d0200e0007002040019009a001c851254411180790500a200f101a60704140c0410782c0d480c00f03900b00c8000400c20303681c1441000060038400008101050501c002d0070783d0795280c840000e00415190020910741c83c0740205807103068840703c3c0c0c10300566849445c001c002d00b075000903003400b00c1c1c401d04a00640c0144502070000742c41200c0010b00341555022102a808040c4000c01c0e11022190407003180d40f8202d9103420021078410b0401103030350f0340303401c0c1c03034200c1c03040c042e611400950207420421710041e034005ca0710b10ba0801543e540c040d103410718000c691506942503140300c442403154400d8142040240915400d440341d16448204030741c40c042c1000d070901002c01c02e0084101720100401d200600e070075401150841d01920480d00103c4407402c802049a10540256000c140313081c6a40e400c10105803481c5500c9500c901d802c0c6005400540891345070074210000800710000840010107841d0300b41802410543c0072113 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 531586070 1250 531584820 531584827
    0x3090703171b070e0c12040204051905090a030f020a171b010912030b041107060e0c0d0506040213021c0b0402130f081c020a030c0201210f05010503060108070326 71
    0xb40440d58900a601c00c2d1000820740e400007981c0c030342d1400159008011451010700140e50340d6402c110083c14024070350250310140c0d03003100050380b01d0741c401c2602c20348000005090400d8113040141c0240d14200d0340e81c08640c085130b181d6001030013003001c2c0011a600080e50300e440f440b881c0028001d0207941421404558a001313140d200380b040ca070a0b08020300d01161410028200000180403d035064500005040f5000300f010000254040e4416410200140241d079600d00c01c01e80068002e550a0105940c10741c89441404154a400c009010802d407035031004504d01140c185502c00c4c8080ca00348001015580c0c2e601115194686404503288990075110b280101600c40002010f04015406401201d2082c08001e952344a1020319119140c03401d07070010018203c1c0c0390b07001c5842540f0310808904001190780341441c54000185801107a2020800c081441240b01c600700c03003107500580c0103501c41e500c60b1004100411000c40d2030800e59407c50404141e10980007080c0251901e0300355a140c0304103000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 531587320 1250 531586070 531586117
    0x8041104020703020624010f0c060219051b01090c030f1506080d1209020904150f02040e060f030610060c03091509050a0e0f16200c0a0b0309070317 65
    0x404c0c803900c06c4814403900c1440c80110724481c840021100b28490209848808200440e03014100c803490740c80c81400094a0006034864480140903591261b03000b20f0008039030030700d2500b4000d84515409203220000c2190b060140c481e0380d402081c5210151240d00c1c20303c1440180203011004140b1200e030328500b4030040d40d8517a291540e4038500160a40060004254003a4030f10590180c010169001005031000340c5540d15901011000a4902020150703681d80c071004e103401500291004200c803100c55a040e1400340e0034880620803400030b061280e0040300c100160100e141482c4020380b901440c2c40602d00c1d42c1450140c5400c0d42c940c1261003e4080d10180607101c5a0280c505c005542c0152228016a0364429074800810b0042e1140500d015041000030f040c035044c00024a0700141d0b515103032842c80c50260b90702d000fa8904140c0d01200d1342140c1da1051980c140746e400b8031b0003404080301240c9546062190316031a0f075800c2c00010041e021204150041e605841c0a50701242c146800340803611140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 531588570 1250 531587320 531587323
    0xf090915011b0b070e03031204060902010e040203101e2616180c050d1a0306060109180b03070b0408030307030506010f050a0e06130e01081513030804110402070302 72
    0x21a461800942140d610b03100803218044640c21007075101100c0360751510340003000e4980313008142c1d072550107120512458a0000807411042d02960040500049041e000d00004040701c1032809054001d0b0f004006001c450846c03416900c04a0752440c000d006035840380341c005200417445a1005950306890120040d02000c0182001500f401020480e041c0040030000b490815400d84034880e000d8042d0180760313440490980105a02e0301e03492400b1841d2012298200c404c5441c440d040e5003110300281c200c0001030504000d41c64000d282401c0090b200d5242c0042e0b10007009a81c09000b10b01d648410f00c006081d1420850711011b042d40d400010307282d0751a02e00c41e0f980d030707001150000300003070a04001c94a154003920329445408559501c1d00d150007401c040641c1c40781d03090302c4495003060b41005198145041001e100000d4112040e00e0340b525454054641c0c6442c2007159100c851031001c00c203000001d510003a03841807081d07160078990303115921401d0142d040b400d4400040d0300240002004000c0560 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 531589820 1250 531588570 531588601
    0x301020c0c0906030c01020d0e0109030c17010f0b060d1e020a022a060d0e0f0f010204030b16091214100501061e02100f110a030b010818030703050f0909 67
    0x1c00b81ca240714580e41e02d42c10960f681c081c1c481c645003d40c200e10181400b56210300c10000350f620040c1000c0d001c0c2c5a407030341c400e1400d0b4030302e80c0208010303070b200b80410208000a000d10700e41d001c1c90603001e00c441c140319400107145100b04031141c144141d035803c2021541d5103400669210543c00c43c421915a1680c80001c2e48a906481540c01404029130030703000c0482103070b070b916500c0740e1303026084030304160681545ca0010012161101d025114517400c20385181004c000c55094036820034009601c40e4a10300c4e0680814501800032002700c0c0d99200c03900750b1554800c008004644460009003140c401604000004002c180c548400c20300030140b010041100f20780216049480e90f81c1c0c0c9000107905418044203100c640013941c6c0c016000f00141440c101e10b5500003801d40c4048070070000301080741d82d440344040e500030031096020a4403150759000a40e000781c21160300125601e00e500c10002d44400311030716031040c02001010b00c03a001c9240003c001c04882a0355081c10702404080310342c2045500c0245400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 531591070 1250 531589820 531589843
    0x60801060809010c0c020405070c051b0a09021207140c0a0c1a0a1425050f15040507030f0c090203040b010f0b36150c060703020c0a06050c090301020c 66
    0x20080381c0030520ba072005118804503072400b640d4807840000381d9800c20016000c0070b8050b008004001da42e500c007140050044480e100c01c50424420b24124450900800380030f5a03004030b40651041c40030700c400902425501d9030240407441d1018120f42144100034060085000070006441b41c0c030a0300080101101c1040f0a88030156072404943ca4180c005952074421592681d0001b40c054005403185c032801c40240000f9080909801040601c0454151224148120540b00b80d8032840401c080c03014203000641d90100304080b1100d0310325250320f40c540d90b8811440001c040d00b504010f500284004507100390068074001c90195506d0a0604001c21180000c1c0240c0c1c0b0012140b420010303c030742403601151230341c8481c02c0012030040100104401021760482d90748c951144043c1d0700d815181e540c1e403a4622000600204261561503050100c1d152180080c030321028944100911490904005031280318142e10600c003140503030740e0406103040b40c00780c094440c0c0c0540c004558031001042c0070407a0100c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 531592320 1250 531591070 531591077
    0x17100503011b05070213020f07050a02040506010206251404090c110c0d080d021e0a030b09040b04060b010e120304060201110405090106120902130b1c320706080106 72
    0x2200b000d500700320b810b2041514200031030b00811161006080030b120712007203d001d01400500301842c00381d0660f015440b00704110380d543c01800c10002185054400c4a0300900c00784020446840d225001c0c400b801d1030503991101900410700803071082441510b5285a04101c49841d40d10303587e4030b81201002e40382611041001c41d07484005c0d1481403400062100d0145030080c261b0b012105281ca4520301343d80251403403100310b9000c0040c0311161180c403074140b00c03452101031003650f0b41300610001011601e0f102c3c50740348941c102034140400700f1030800c031300f0b07412941000e000030707001e4000001a0760305c091603000207070401d101d40c2042080314404405017080b1140fa030000d010480c0b002d211041c0510031801203d5000384504c0040c446c00e0302c5491000c000e0840c00300d0014a0000603000900e451409442c0380c1314250310703030019020078100142041603844c120210500c1c8000d0300d85d00d041c00d0806c0cc146250f580c0e81c20070310040b806001c004108585422a000340c40303600d92a280001c001110034007034100403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 531593570 1250 531592320 531592331
    0x1506050a021b0906010c05070e01030c150203070807032f1b0103020310030f021809060417091305100513060503010b030f0709020a0e0310050103060c0c03080c0a1710050301 76
    0x40c0000340c203591a00c0014880216561210019104140207001c00c7d00c0c1c07841101408101c881002100b07078040d40c007070000c04218071310f008002040030701ca01c05184210341041c07003d00000350304c86e401d681205615060003041e407080440204142020381d0807812880d080003c0c0540903da01080b86002500321b4084880c0300c010000042d02688400c0d140c5030566203140b2002c00c04204465135084180f84018035402c140610302c0c0000c0a041c1c004d450b0224141c00510901c81000a2507036280c034000984d040c01340c1843c06400c000f88044c01c4481003914196150700019081c002c8641140c000340100828000f00840c10650050040015000301c038041c1d1b19200e8401c4036441c0009081c5480101007006000560400402d030300a500181080400e111079000400c4283c0d6080c4810108150484000241c0d580740d410a042641c001d00c481c24140112440c140c40420f60154549078025007001105a07104075a0108540007807100d0310038402d1860001c02d2020900c44030070340c00201e90741117000b03018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 531594820 1250 531593570 531593593
    0x20f100207030b34262707230d0201081b1903050a180503030106120b060403150f0e0d050322050a1703310501020310031506050603010e0a1506050a02 66
    0x220b208903001611840c01805c80000c640307001c180013200400c40f00f442294071030011034030a0740c0340006a400280308503075a0b420017452039807031140b0342528441c00c0300d0203d001e80454002900c82100a4a21171060000c071074140742d40342c400800c5038401c50150300d52900c581d01c203540050003401c3c1525440c4010b030404100e500d010190000011003107804c800558a5a4039155040d03482c40283c0b00c140403200d480c1e88183c02076648210242000f0343c062551520072003a49044601110324078130f0048d018601c2c000d98828048000516030000c4105810403e60340c4c0c4502d1804505401e0542c8945008031103060098104100070404605544c810460222070314284040010a800b08548510240282102e00510007021440d000142c0c03040408068044070140c84aa099030b004462483e01c1d0b02070341004004014000ca0114003850b0080d40c03c00c402820000000c3c110311040c46440f8110715840040b4281c2c1445500c0a65156070500041610300e40d1a000606190000d40440001d0b0040c1528981e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 531596070 1250 531594820 531594857
    0x30d09110f0612070e090703091104060303050417070504020f0a020607210504020607050a050c13020909070507150f051e090c0603071101060803030103020f100207030b34 75
    0x12100740c0003850380341801c403010007960014038001e040303c04200c0f00e988501c4658680d1618203010700f5041d078000c107040300142441003910040c06600381c0030f43c0c40d000c02000441e901c54180c4094410454034803646c8070007805418a8200240c00c241d40c03041c4002120306071309840e64003c001d001d14540a841c0e17076a94180e81900c0a090240420031fa00e41005515054500c0542c0700b50b902510040c02c40d030401550741c80721403800b491840e007114180c0c40200c1c02d452900c0c000b0041450603107843c00c198036210035540840d2001b035024090105014021602d02d0801152100a482d03101412a082100301c40e2810003101416090b11601400119065484061280c92160320b21514514000300308e00291241485803582c00104003604001c01000d203840070031000e0040d10001c1c07040754000d40d01c0c0d50560040200342500308520900c20301c15001584070a580116070320b000c99402008114840e5114070703602c000721a904001260348000c1c24006602e480d440b1816510503000c1b41e403842e480d42da080201030b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 531597320 1250 531596070 531596089
    0x90c031204031509080c031b190201201e2508030304030c21031a12060f090c040e0d030506030c0d060f02040306060b0705011b080c09030f030d0911 65
    0x40c000c0015070301074440f400890b4101c084614420507281d8a440d500039030035800d54002d40c02021040c4689000c1550700d9000300003200d0310070820940800b4080407940081c01c03000700b0519202c1a244903e00d0308031241d10a00140401020070720b490304142d5410402541c842044248100000c0509400b011505015038152030646c1d43d6000114a503848546065405900d01d40003101c1d030000d2214000c0c081d002c05620000350352080d031400b042103070480c07003107407150098040c0c0d0b0341c0500d421050120300a080004c402d44c100301070094031020364850003403450502499081203a001402e01600d80e2814400044ac0701c40c00215035800c200e00d0b2101020142c03103003001810240d01005500359100811802c0d403001e40c00c440310304001444d080d641c3e520306c802d4500941c40340c51818404119131003449800e00a43c170000d481e21052004425060074050040000601540d50040010960b04241e8404021500c0081545001c03079031180f4030400742402420030b071502200c6d15100c1e04584d561508024010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 531598570 1250 531597320 531597323
    0xd05030a0e01110d0203060d08130503011808040302150d060e090d02120418060e0708011503020a0207060c032106050102121e0903072d12020a090c05040b03090c03120403 75
    0x243ea2821a0804402000e500068050b0b6404840c1c0301110000030240ca004007480001c0c0f52211994514000800d400c44521410800040b8400804680054100812074040e658129825045e41d00e00c191100900c2c081d032400c01503003d01e001d0010450441c607201e010710425407030040703407540340f03001d18201e0302e8070516030210300c400c4018841071003030119080300f210356a011031364001340729680c2c0c43c00800601c00580d5000042000a001070080c201c1c201c40344111003042e030030103501e04110500d00075940c1c0c900b403044008010000040000301403086010415200700101c182c00414003450620004100c2440340328058852280415076070b1122030192400280c0351103004000407141400220b03e40e0041103195494003071a4008515102c803500005c40d0034220f0000d03c0e1070402069080343c8000f81a401c2850707860768088038603006983c1c140c0c600c8146c0f040e1080102d1a1342c0c940f002134506000ea0340000301ca00c40080104407040400040d9014907403007c8003240c40c0c4044240760125244141d000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 531599820 1250 531598570 531598601
    0x140309010801150302070503120a0b120d1b1a070207050102120909040303060510020a0b01140d1103010e011a09010e250203040f0b03090106060801180b120d05030a0e01 74
    0x403c4510318056a6000b002894140949844400c0c0e036032500f5503100c4103543c038081c10301c1802e1100d02d510f00c6c40f6207003284800340e4030034103003480000d1440d07a200c1c0444903400400c21040044001c0c41518114060340a501c6078a400780c15050b4a185202e00000b00c6045006100e01c0800044640c400204540310221800e58603242030461030074010a400d00810075424143c03904030000c0c2c0d94654100e03150700f42c4a02e501034a112151880e000c01500d006911003006006582a085001c1e52800540e40c07002d80e1140180b00d200c1d082d07101180c05400600c000b9405940303805585170844c0300d41e00c10b103176404004548110090303880320a0044188010740311840e519004445140500594151000040c03025004403400c0c00e948101c81c82d05941c1d281c00455420700d011050003107010090013544c01a00c91030810400b551304101003400700341d01c0e14a4104692341c59241d107090940703c06484030342181c2443c0550390f01c1c10310311001400c2940b05407105440180740c0780c50104440e0061058100d03203001c410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 531601070 1250 531599820 531599837
    0x308120603190620070803070e060a080106081e01150206060d0b07051308010612110904020105300a0203040320070e0405010e1609270605090f0f0a14030901 69
    0x3c450b00c0082031207020610401401c500c0412102034008043e00d074681c4120082a600d20b08801c00401d40003a00d04410f00414003032084a0b40d040c2c00241240c15a992032421345515510840314070010407150a4120304110740000210310b0746d0a410b02e005100803c2c1d0212813007130701d4007820302c085d43c2669403025001c600c91001017050248107038000c0610611002c06412055100c1c0181400c48101e544038007541c20030b282c034100421141024001c07095404943c03041207480c042d00040d0107441030b0402510a09410001c01d03130b55400c020340e200d03642c180400341c0000350b1504204c0407001b98070588098000c50081c0c24901c8400034101c4c0c614410020807400380811034031b0706403c40c20060000e0300494455407104006003078200200f1070310202c130603114030881650340741070b5030784040354010980c010040c0020b0301c035850703920342c0c100a00c50020f91180b40081e8030303510707046528209500c449900c0010b000710820922202c01c005420481180900505001d16000580b441d689220322880d15000c680041c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 531602320 1250 531601070 531601073
    0x11070c050f0303191e0309050c010521010906051c03020d0e0d0b0f060901060e0906060903150f040c091b0c060b061b06090a020d08070507050901030812060319 70
    0x1211544201e4409000c0301d003440c000180051003051800009000250044030382a6405115007481048104604080106850301d03110540c407900c240c10080e05003c00020007495003101c2254a00700340f07811016584040d40c455000304003a140740c2c0b00d458420314145980001d00c0d0b01505081d05800da047c1c0040c954580c04200c1900d00e04544426583c0c80f00d015020780c4040388407880d04600c954902c2016555a2400c84200240400182c20800802c2403202c0c1c0a501d5880c0c13100d030701e178002ca011038105846241540010b407424070401c000a064001c1c0d4014441c144c605030580c14007030751103481c0f01c08a82d40c8480700d2000b01d6910701c004030605c10b0082500408203003e6801152142d02600c0302203030714808003011440d41c1d8400c0222a246421200116804c114240403560308101c54102a054030003198001468201900304060301d0b07841c0002e00d24041200030008070000304009442440990f81d02c1c1041c41198000615884107101180c000810514010607007007080140c0d04654802100315 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 531603570 1250 531602320 531602329
    0xe070519060c020f060f0a030e03190c14030a0807091208030601080414191506050a0e07121a01020c0a2702120a05060312040e0117160801020a020111070c05 69
    0x5411080c2c0c1c0100c01310030940c0c503644681c002424410000506e603581d581c68110000d08541102c04442c425810a015421742421401101d0440340c2d6a480c1c40240300c0c1d164100880741c4444203c4141c0d06110008071035803d40d800100c4244240e03003e44507030032040c0d50b428a000c040c00500000400480742000064039070342c0235090880d0018090118003a0b4002800801c0340303040c00714601541103a081101e01002c100011a038101070022140090103407910b04004510200164054180c20721982c10018008501c40c1c10f54020342c401400040c01160140c005104e100014083d606005000303e2181c00e5150a01d9801942218015211003882c5140116181003050030101040300e2036030200243c1ca00003901e04c10301405545512070014150400c04101443c00d40d8105a46490210501c0104503404c07400d0100c2d81102c0f040400c2000720417009040c242819845000208404481100803561aa0550250100d800c40e45c008105c4c0005045840243c1d028400c030040c5000140396040c80300e07050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 531604820 1250 531603570 531603587
    0x61a070b010b031f030503030a0e070e0a0228090501091d07110109060603150605010f08070f0c05031201031101030b0307170a29060402090d0f02030708010f0e07051906 74
    0x20040f984c0711041d260f8251000145600581d01c0d0351010040c803090850f14440c01e900400b02000034170109103081c40382c0e0f44603080107100010304c507800325844040c14500400007114002d401d41162100840300700103040360119014590004082c0507005c516803560040c10849020048505080d4ae615584103d5026032401d18070103035075481d0b036180e4001880320f0060034095807140c032100812103206002d0000302d44090f44410304111030740c030000080541000030550840024601004a4500420306464100b10329070000d1062200040c0f07221022801c2a486051301d00c55514a102034006400440a8900c01d20000c0e03415003080504100d01c1d490111488072000070340007917030b245038080d4803500700c440800c0c0e07849074009c1c04003503450044102584000b58421001c03a400c506141503200401c140c3c1644000082400c2c4681041c48155541002148020092000240a0100c004481401800d42000c103135441d48074246001c2102c1ca0b00c102c1d40b4005014120a05400d149861021100040e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 531606070 1250 531604820 531604831
    0x40303150b030919030c06111201090c030506010e132a020307030201050903041d090f06090f070806010b0f0d020403062313020604051002011104030501061a070b010b03 74
    0x595030032040300305903119420a00148810721165480c3c2c0303054400503041c105040200c4500c00349010f10f4000180d004044004d032190412800541400c012882078803a1149450b059141140d2000008a54506800c200d0117800240c0c2c081c40962640401582c00817055003a1039441440300c445c16100184a5000b001c81c3e40c9403500c1502d44c41c5803440300048081d08004200e00580000561a090540900800d50000300c0180294605841c140b001e52651402400440c3c0d41404c2030b0100d52440b2040101d6144044144240c691074100078003011394518825441180764001d1036000510311502140490484108503069860030f00302d083d02800030381c04103607040d14080e428400403012400d03502c05c1c1c040542d0041e00344112405030030004541410000e20710318942c1141b0440c4001070b03d0311400ea90803600c00b510422080c001900c41079000d8010001e244400d0040420000700707000054000d18111000901564440289001e03015520310580304007038031012085004202c070807100d000555200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 531607320 1250 531606070 531606077
    0x304031d06090118171617060408090d0b101818110a0807060909051501021023100524180f060c060901060f060e06071a070932090403 59
    0x141c4500c06420350113540d04804405e54007032030303410b108642c260001c070018107401001091420103590410f50780325001400200076007808942101c00d41c440004014640d40e001042c0d540d2403820310002d052410851084592041084240f0780ca40718051081400706036081c180341c6d46602843e1151140c0c0703c889040d00e174210b0300c064400107100c038045c0808406030000c1e43d1985149494224040240c42001d041d500040c0580c140d40d200c0d50780c0010384011140b0300030707402042c80540151080c248054131822450032500d24030800c410b80072071480110589008a0b105104044000c400c1000074040742040001464104850908200d01c1c10810b491803000501200007007541402003005604212000c04140c0d0010003409615002030181e0f5000e0f100e07118804500d6860400014072400d00c20000d0741c01541c0001345003003440044107201c4060351507604046034034101040d004228160500c070b0fa0f0320321501c00050b51504180641040c81103006440d107469241b4640c010885500b00242040b41403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 531608570 1250 531607320 531607367
    0xc0c05041a100201050618071b051e010e070f060923061204020f031f050c0d090b011a03010b07060203070c151a09090d1818020304031d060901 63
    0x1542e403262841c14444425038004102410000103000c4501e09400a107a8000007900400016035801068140c0050008044144240c1103003401c60034803450303400140c145003100b04d0610aa0205400021408141000715400e80f5a03400b000c06108807507003c0e80740000c2d08407104101c0c41d000714a40101070084d40700d240001a80000015559030320110000494148070001c00040d860007001d440131241e0140c000d466a850720061071001c5281a242d409402682c800126407a00390101c20744520010000080000ba140c070f0a04c402c03252024803842c02d0758141c21204969845052055904985c41c1c48081401d00c840f80d17948102131340005080d0700800520310041d80c00f01d18000001c01d43c2204961001507070502025107403000c1142414180c5c01103140c0c80600180000014680c0000d951914208180020404049000e60f40651100007400c81c064041282e140c4030340c0c000c50050348a52110b00007200d07125075800403030b440c03120a071307a215000340202800e0f54020030008803000700c05c810703d580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 531609820 1250 531608570 531608621
    0x607140c060406050114030705010e130e0a030201020c06100609060f0c06050115020f0f250905070306051e130b13020301080d0e0102060f0c0f040b0c06160c0c0504 72
    0x380050884090703c0d11030700c03900100103111440c900301100b0f60003a0302401105040c0700000e031806003c0c89805024086282c40c641d020181036100100c20784154007581c00c00034407801c0080c042d40060384040c641e40209404900c800502d40c20410840b074098483c0040315140c55010340d41d01400b82400c0701130015102a00303000601d9886800c1c00703048008100b0030102c0c040b90b002807500b81300408410322513001e0490061145000500c802114141c44003027800e507180310082d8034040ba0715034001036009040005000c42280c058000d90255401a81c40e004198241c07492140148524015180c1140c01310302ca1403071241480d04480d5088a01a011340e810700000c11911b4202d9209a02c04044c075007242c00307101142580142c966042800902c0141490f041c140074020800c0e60107441031024401c00100903000815a505940081c0002c1c02095100c090030f10034283c488000f100e02041c140c50b49644000058000d0100c0c5500c44d801c210b250400505103000d0200400303415689c040b000300320844160307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 531611070 1250 531609820 531609823
    0x903030e010203071706010912120c1a090d050301050904110406080d03020702030d0519050c1c0c0209010b1903020c01020d051609081b0904031107080f1e0607140c 72
    0x5000d121580e41705503031400c40400e4800940740c058285410001c0f480b604000c1d5541510703500d03017039640012030f6040c4074402441c00d4400e01500207008007514030900340111011421070020348210f801c10183c0c0c1c1103c035036102c08c54451109000d110751005201000c50081040350450305c216480240001801036112a0903610300003600800300c0000340c00140d148218101440f90603070016182c280181042d8034030380b2100046086801c00d104200000c00c9a1500c4001040012078400c1c6012002c2c1c0500d4483c1c0e030080c010880b0240c103074050700c1000c00005400388884100c4850455031104801e070303070200a0089011358040300496100759002c3c483c240443e002c601c02c2c180126110b400b005081d2030900303c0548205550b074441803440c0c00c042d20900006468603500c02c2c0242c000c59000c04036a640c1d103010b0302e04400d1411012181d02c03076014081071800700010070a08502702c01046582c00c0d5280c250002580314209610a03641d00800c01086005000e0510f45082401c0b10601d03d041944a08049 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 531612320 1250 531611070 531611077
    0x5070509010b18120c09040303090807080309011d0c100c0b1e07020309030c090402040906090302011a121914032205040c170a0f090f02011b0b01090903030e0102 71
    0x2101c2410005003000c5030001c1044400f41149058400400242ca6140030540740c5981c0e03489140600070315400501058417a500c003017040350707101c99515281d401904040307249403c1100c00001c203610f00000840c01550003004000e1a03c840e9000f480701c2080d44090009030381c4041c8199041c001440141c0c000900f9400045105141129065450184020701c52903c050007800c04400c0d90001c00001603140c6003c1003140d0112010345020703810792102e01c040b07030080c0202213019160f14034103681a010582c0c1900076482040701200768032a941840401c00043c6000d000d2018070541c001155003402002040140c45428020755100010394914003c1034210340c44001c02901800c40810010500120441003002401e0142c60403c805d0b018520050484404210421505101080002d55400d0716801c051188241403106004816035860440c0c81c40707403090802ca004c55091080703d00301c8040f80c0c00c400540358100d80300d04121791a0107405ca008100803a0305500b051b0311480b8103000440c00340000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 531613570 1250 531612320 531612329
    0xf0913090b07050a0c0b0c0714060106080a0b090a090203010b030706170705070809010806191202150702031011120c03090d020309030c01051c1503110d020d0b040507050901 76
    0x8269a040c0d880c011103000c0008144074203004051000041007540181c407040540d5105801c02c542d52140d0300d140d9418050107c0c01007401500c408007080003800840d580341294810b40b240800c54440380d012030300307803000c2041c425003212038039000511100306d640002a10394006000042e4020390780010078284003080d00007501080003140c402c0210030b1b14481e02903102595141a41c2803142941e9500c5181c4a0559907904110082d03000c01e09640d075241d001141c880c0b80302c2c0703810034041d6142203074240310217004c200b40d100b01c40d500c47d4403902c0311040c4125040d0990050207030240482d8244a14005c0c0205000080004002d10040c0d100d0294840d1942c0604030981c2815103a240200b60949480e2081140c1821034000388041c2c140f580380054405a0b900e402d00b0640d8490007982c0c80441000851101034500e5810001c10031041c5a0498402040d24001d00d560303491040c01c2700c00d00c0b09044034010025041400500c2e40008241403100300b6410521510540382519078400006031100d0081c1c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 531614820 1250 531613570 531613609
    0x1c02041401061202090a031202070519080106081219090909061d01060f05062b060302150906031512060f0723120c0f0301090906061e0b0f09 62
    0x511819400c98110031072610710800661a0403240305c045001c5418074030000300300207015017a03424400e000b07009440180601074413614400c9504100c4803140800c40c483c0303900075440d24502141100300403450f40701140140d5541450021103007404440600000d503101c0400425200100d46a201402007081e00c0740584c801003900760603100c610702c4550101080000c03a0b80340c03940411100000e000d0340c80c00c44030200d074865111b50200501b180c5070000c80d46a081010340c10401c8102d02c8101d64894070a03280251003409144c1a200c17001c005034031075001100e0b4040c0301400080c45421009480140c030240180046185e0811100d4880c584034069410b02002c49044081100f61580403441c50040740110481c441e5440c44400103803003921802a03100300c00c43c0e1140000e8030405075001200c3ca40b00d0301074801662580c1d00d044880051805403070480b406070070004c001940f00318440c604e29480941903d4422070b189868100c0302035900100e807a1070b6108061200010f02d0740d450400c05810380c0a0341 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 531616070 1250 531614820 531614861
    0xb130c030812010e191121040b07050a2a0b07080f1506030f040309030b01031103120a08130c0b070f0210031e090501060f06020d0e0307050303091c0204 67
    0x4648002d4400507003050104014400412500b59400e0340890500781c20341c0000071340821130f8070030124103200390b03902c0c1980c01c40003021640c80c14150309583c0d44650700443c4103020703c2e191844210303030354490301000c00b00145029100d0722880c400f01d100c07181c0c00c0c80300101284d054419a41d0307000a4032800c27a06170300443c10140411414008295a4951104000c0c105036418421403002507440d000c054420203201c1d44a0300020300f050b0107001c04070f0246400500741c803030701c1d03949141c0000524498908a8000d000c2c540809441d0040a025035000d5001910b0307215150f030303458080e800b40c0c4002101c1540c03c403101d0030000800d614180000c06059002d00410a001105801071104501d440b0100004240c5020201c4200b8901c0c0040c6184110044401044146450400c0c50141c5204e0704007039004445c00c07000013078030390300050280100d100c0c41e01c40080d0a1001e000705921003826105d4590143c004200d550b059140800e0000c44100001c00c4031903400150b6004101224070807101d0951303902030748 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 531617320 1250 531616070 531616087
    0x8090a0b0a0e0d050c1b060c07030f03020d050313121806030f060803090604030206031803040e061002070305030f0708040e0a02071e20030a150b040b06040803070b130c0308 76
    0x1888003100c1000f01d818003502d40000810429580e40d244c0210301c002040c0f4800c1030442e035580d8011601240403400807035025a407203090040c1c080c449130301c04038054440c206032004441d0040007520311551a640c208503455100741c9030211101c41a40e080410011046020311030100b5104c5504042c00550b50002241404c1c0c2e440941110816080f0f076003580e000b44180011a640c945c2241c05580d4182e0380c0507101e0f120710740d0400380c007505442081803501011801003078030840500203500c2410100e0b0303008800d81200b1000d0f038450203035000282854004200003c142c211020052003820300c5490380f02c0c83c280d40c41a0010b1100010340d0a80c603407940028408003030001c8030b00980c1c0000c200211049241d0126501c6003c081401e0084030304108020a98400a079000d000210503c0c1d0400f0001027413600f01c058040060004200c920f21691412001c02a58100703079081d50143c401701002140340c0046500c8610a0200c000d250300c07285a000201103002921302e500c118019403060046544441e2070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 531618570 1250 531617320 531617323
    0x2070203011d0c0603250c06060e0a051f05120c04060e040605070516020f0406090f0b10020c090402090603070b0705010603121e031a0a0e1812030708090a0b0a0e 71
    0x2611031684100d03024418071005003081b42440e1100c1032030400a942070075980c07200b5500c0320000b01020309982d241c40000240d41210140c46441100500410030507665a40f80405854018003205d0b028400c5604050149041a1031001071503440141180c20242d5481d00040941e140c81d0080300850001d50148020844203004451b00410380d070a0590500340c0002c2201d8a001a655019202d2384220f1030700c0005071681c0c2e201602601c030550090015940004210002c2c0c18100e0300305000741801080780180d24070214402c031400c4801051340c0c035503446940070403c0d10396001d000c403541070062450000700308040c0383c02409a0792081c00081040b51541c14410851030f070380c000b40303004e00c04030340c000782102d034161400a41320307030401d04000480212260800b40045201c10300c1503040f00b0040f001141498541d2545881507200b41840c0441118075218640c49154034101e108070810140041646075000e110702c030740c1c0b0400d110201c540303a411545940044402c1036940301e107480c0d030340c500c8210203650 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 531619820 1250 531618570 531618583
    0x9090620090114090103020421210507060e01060806010635010b0a031b030212010b180603190207080a1107030c1a07020a090203071b0c0501050d02070203011d 70
    0x5218065401e0850001c0041c140e04402902040303000c5000500740350b030f82e000ba41070320f0180000c0c4000c51040805c6000c01859080c801d20213035808411128078100e8070038882c6103422a000699240d81c01c242840c0d4496000d032103040101d800d55500e07048040b85122080180500074072036660307030034a0110b20410502c00540c805e54400020408075801d00c0d40288030b10b03038490442d85d200c605640c3c0c0d5080c6031000c600030b0920322000c404921051041d843c8980d4150013908405107485050001e030390b603550000d6101d00c02e1400040c00b424a4000c420b03a01e00e040f901031680aa040f6014540090b00000c004040b64804481200c0309000800c0c0380c40d5990384800ca11041c00e1543c1300a00407281941c64540b90070442d03200b0112072900014903031040240d80300139115034a80c050a4400c5040d101c6110401940088032004001080c2c100c0c2d42800c20b1081942c00020307604894072388191410040112850340c00941200c0d5165020040000180c03000d125070300340340351003160b0b00075005106981c140c14283c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 531621070 1250 531619820 531619871
    0xe100b030a0b090d1d06030411010203070f0c06090f3b0408070c0608040209060609180f151c030f03110c0a061d07210b070305060f06071119090906 65
    0x31142c0f8195155600c1b80c404a03600b107904480d500240c5601c08004038a144582d81e00100000c890b040c800040003900011202910303403d41b06c0f00090b9440c0c031104410902c06209220340c0c1c8038481c4038020115814142204202c0e03540740c01d0009100448104041d0220584049402080014000c2c041c041d010656a000e803030f840c5040031840c100b540004060b580041d060510030030b00010700000c1940c403081000040340e6075080d0000389181c840465610a00110380102208400504442c0c06141086280380c21484a1030720550703102040d1421078110090f0241c1000f45076032011905001d41e0180041e160355028800200210003171841e000d0b043c3d90b076010b40685000c00400c03011010102c0822a082070740c0500b0000524060000700c14070035170400c820b01621511a1406000c8803942c1500880d12408003610fa08003c1c0181c0024045c07184180c1e0400b03426607000316125011840c01003c5518180d1144100b110f0194490300e00d081140c20080085079103664031080c0b04a503984142c644034140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 531622320 1250 531621070 531621107
    0x20d030b0d0b24030f160e06030d080c2b0e0105010f03110607021903030e102001090204110c010b04090b22080304030e0f040e100b030a0b090d 63
    0x1c84807566800030200010708104015600b81030900310014480c0e400c1902c05000404461041d402a0403041d103844d134164041500c001d00b40004111441241c1145010741800390007480c005100e140c080300c0080000d48005846e440403c4030600d004c0113414500500c11030502e107541100f0280f2031801c12561018806002641014010054000c403a161001200d422041d50b0000207100c9000503c01e04c83c2e000000d46c0080003103c90350510701c3c0507503401c00380c1c3c0c460349880e004180740e1010041c030600700c58961320000d070034079040010b07941074407442c3c8800321540400441c800c501a40007e05444242c030112400f11000f00d84880c40d49401d0245000309a010303541004004c0b05a00c6000604000a10b2007520b40036251b044818000d40500111500341c0050f81ca0342ca03070400d440c0041814801103101449505042050500d80c501480b504005c020ad0800030034460342e1003240760300901005050107515001d000c2c1998003003802109071790f101d612100b0103031a2154030100042e21f100726503038690440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 531623570 1250 531622320 531622339
    0x70e1807050906010c0501020403151b09142b1b090b0a0605030405070b040803070c270e070302030115050118030309030b040f050d0c0b07170c03041b06020d030b 71
    0x107940b9148070b0190070032400c0ca4a2604803480f418110701a210355400100441031040281c0341d005029402511003504d282850741c810208902c0485410a4901075040c881c4004000c985092604007854004d041c804098049015889000302020700c00480064443d48054800121400d1040d05d80c10081c00003407404010702030014001c2906800e050241a007880f1001001c0703001e001003004040000c104490344503540702d8881e4812500d07071700445812a41844941e0300031441c450391010950480da1076070b1310050007034040000440030f051070b10328590060050041c0480941c03400c0c000c0d80c007110504c15264001515040004050301414401c0481c400010501800001d5000c140303081107031740080c40e41c0801c0d1100c0c20300b58070110142030000c0c400d10a0301c3d000321429401400794604c040c0a04c0b11040b20340c5d68003030107641c01c00e42c0d040c92100130520711002030404d9900303101440d0814050444034880010b041c500004041643c1c2001c00507071300c0078808004017a4103001d24400004281c54200c0d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 531624820 1250 531623570 531623579
    0x1a01030509010c05030c070c0e0a0c031404020f040902010e04140105030705090106020a0b090c1c0b060a14060c0109020d0c0e091c081f0f030b0a020a1e090305070e1807 74
    0x1350002425010300d2110002c1c840301440a031103a00c2000c1c100b40e030700d2a510781c14441070610040c0800e1507004042030901d014014440041d41d0413038455900904080f1086211004001c000e0500c06002c038140300b500201c140c040e45852082038000d803c10351180c035065051408252601c2070382e1748198841c01410b0b0062180341d40c0454ac90804a42c042e0001d44035450304800325041940101030f564111204040d01802018501800da848a002d014001300688401c1e0620250680d503016681181380e40120790303081170400030020070b10350482c507000240c1046280d000400b109105c0800f43c0f0840103108003840122030070548140c0042440e40240007072020f60720044003c6c1402e00381e440c2404084c034000341141400c6281209c0e40a40b564054a080d074440c41c4100c40344c01c40d40000d4075001d01200000744542c0b8144200d41c9101655200d040c3c440d1403114000703843e80c441e612490200a40b0020010000700204801d401400f04403000445915040c41501c90b610102c0207611140c0d80160000c02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 531626070 1250 531624820 531624827
    0x30708030a14130810021c061505070804030c030c03020306070201091505040320160909080304061121040b0702030723032803110f0d0b0f041a01030509010c 69
    0x442c11040719850546400300402416070128250f40086081e018082c8202c500701516801402c0d9400010000d603045017881d010b850480d1018010098000d100300c0d0b100300c91500810240131901d20070060549415101e5680c00608503080c1d00c01c0341c0035090341c84280114907041c08682c1e03100c00184000c00000000b0b40721a060200b5a1170610701d026a0b88020505140c030505298207610103068031490264021007203a5914111010409102c8003c541d0218040450340164061203170000110303070854441c2d4171090028200c072043c90644d2501040f00f070055074403000c1226a1482d138040c03c00d00a00d0542459030a00310000d02c030000719081004008002000e6151411600b031000400e160741709810708410b40703103116001c040c150072481e403581c0e01209091050341082c0f88400380d606115040c0c28181c088164000e0103400c007600d00302400500010136040e07000e224100c4005000040140300180410101c4942d041c405503d400c070a514041256018000c050300800b00d42c008000c100c1483c07800a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 531627320 1250 531626070 531626087
    0x803250e060c031c020c0d180902090a030b091506010903050325170c06060604050904060f0f06080c0f0d1208040203030d0204030f060501050a061b020613060f03050a0204051005092d030708030a 85
    0x409c0869808078203081a07885020442e8003035170340201144030908000d05e03910790303a01d88002241d075119460303000200c2c2940310380c0c0b141c0c003102c0d4880d00560409620695050b06183d201d11003d007a00078400383c0001040101509240400504022603a2001081c0216060040092902d805104104420000340c0c0340c4028240e8041d03001800014448200700d0402d000d400140e034010703055400e0030000b2a81b01c10119000b0702190048030303081c500541101c1405240c800843c0003a0400100200c4194842c0c003459845503c288000c06803071070841a9108802242c02a03003043e41c0301400711303250408004032445440c3c050201201c0c00c442d8549491801846130808180d81d0b294550004004407c549410040c9d845401c00b1104003000c40f5220792000f00749102d01c04c0400002410000840c80e50b450034401c44d4144d40c2c7c0645000862080c45109560561101c1d00c1e840d00600d88800907442d00f5600300d52800881c4280145454554610301010b00d00a1b107500309104540007009076007079654101080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 531628570 1250 531627320 531627329
    0x1090b0418030c030e040204140306060f01053117010f1103010b07082a1b0d11012714061606051905040803250e060c031c020c0d18 58
    0x4240c91040c914046400c0384105c20700307981103400410003044410f18070030046401d0304141c04a51169560b9001c01c0071074014000d4a50100c2d000700710a40040510a00b0448103400440c0c1e0100c0d003001030700e404231866800c1d900103100810320b210009442c1c00e00b070282ca1840c03da003900c1803200c0e0700100038410281c8018480c8113424080010308000b00049142611101c016440055007020780003001071010300c011044145e85405143d80240c0e440c03200e25000e80b1484d1010708000c110011035030310408150744a04126041c00541e604c140c004414407035030b2400200700030098030355880c41d20400356074802d4012500ca10495003403088191074600c9004014030250843c0b07011482d41c48806401c18080c000c0551800160705210820060100140041d409150510100804000313481000d8801c95410b410440014010000410252a094006c0e1181c81243e0302074925200c1500520b1010700b210194601c3c81d103030003080744c10031010240b00c00610f085050603c010f0002c82e201404c02c00c486140038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 531629820 1250 531628570 531628577
    0x70e010206160c1e050c060f04090902060c0a051c230307090e04113604060f0911090a06050303070f050c100c0c0807050303091c0b070801090b041803 66
    0x680600300e92203002607a42c01508101424014550300013007082c921000130701a215031150b040103e420b07052550496041a4034010f4150410f030400d211040941103202099a0003101800f01500c056410b10107002c11600c66001044400220303d000c0103101c8550501c4000d1001482c00401c0244010b0708021001c031501e0115581ca84d254076050720343c005141c10200110b44c0041c1008100000701d01d0101c100b22045401d014452407070211425440c031602010341d10400480c0040a0302c106110b00c0c5a0454403890340032400c890740803101c1c0c01302e4110035810346802c01403451075a05414020401034211032103803c140a00350605020a540b4803540da00140300d800c40030540340a02005110310b10007150002c144000050380c0c144010880445038000f550506245400010703060360010703c2030100c541c06409941004180030401c01d00c03411403030300620b00f00c005503141c00000d4560703400e10780b060607551581202c55040c000c00d4021074004101c4180200d1801840401210341a03054116450b403614 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 531631070 1250 531629820 531629851
    0x42f090a1b030504170703020615030a0c140a031202010204061106070221070602030705180d050601210503031303020601150905060d02120c091003051509071e0207050405070e010206 80
    0x143c1007110020001c03000c5c075180da000c94042c08050780410306038003e030000a548019a05400c0030980c507804401c00041c41413070201010880c03002d2081d100c04031443c00620158034581d503a29050301e0201032108210050754000303814848540c1281c2c842e45c00c640c04400520300d5140061010b540c030808820a0101036038540892100058000e045035400c0364401c0042d5100c0c00c141d00081e10b250400d43d084201c0f110038000d20642401d00229503e00c2c190894020076840e4070f0030200d041001b0805a00e00741000341c0c40102408120100001d5000d965400301c0100c45400030b0800a080c2441a001800c00204607690400c42907403140100d03007520011503103296500d0440c0e0a0390000e01ca00c03444c017486c00040c1420044500403a1000c2d0208242c05d607140b0021901c101011000c0380d50464400e8404600745001c1d14550805420b415440040b80c00d00c4141030340c460351190120202d21100c0390040e07011a1083c0041e007802e0052540050190801d404910400f400107034840300c0003031001c1da0342070000c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 531632320 1250 531631070 531631073
    0xa0305091009060519200d06030501020c071d070c110a0e040c080f0f0703060207050c0a120501140601050912010605061218070518042f090a1b030504 66
    0x80c030030541440000107080160704441d01e000400f802e03088890701280f040c012010507050415015014401400b4940d00081d4020b03071480c0c5031150481c00c0c00500a6a583c074000c80020700034401405680c541c0001081d01d28645070f510700501e81d0720310018900b83d20320800d0100b0b80f9082000c028003e41c3c088908818030480d0000320341030341825880098a82c2101c0c050106010f00403c0240a80701201c0944d1030b0746801841240ea2a030b0400c034001e800da8018041000800c8a0f03501400e2040e00c41d8013a14184035012000074485192a002041c5240e040400602000424481c4590722010901c40b000a8034141e00060514001d10340d03240c1c05074a03240034580b81030400390300c00000f41200030017954443e0287c08184602c180110303080b45070800074a4040307450400005141046a00091982c0800b070310141c2d07030813000315010b80100d41f00307881217001c03000c4030000150b01409507445a81d0724892f00d20610801c042c402015000c480120303e030204134803045071102d050501e02d1800d401d000c00caa4503903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 531633570 1250 531632320 531632323
    0xf08030409021602040c051e0301120b040606170d0e0103050c03040206130f0b0702031905190302030d020f1903270c030215070b0c090901031202010e0d050c01060e04080a030509 78
    0x6543c4001d500c14500a14500540e420401505400d101c80312010202e050b460800d04452000b8041c160900768624030038000102040141c6910a10801c07010541b142d6951864000141d0f0100041d1076410406001c04a19445212180512001d2030244032500308000310740b20760311003d48080e0240d680095508038009a00c6000e40c01001c008a01e6005943e81d101c030500d0580250004a200c6d001c1c1c0c0515444031000880c5040351541c0286c003914030507540100300d40780c56401c2c01d4101e00350b00003801600401c040790b2024001141c440e5002d81d0362100000558440461041d6004080c140b0b07200d140d01102046551007460700600d07440d40d10724484282000c443d1000f16500096100511506003084415140050802a445201d10140c0c60f04c80c101a810070f4018141d030742c3d82005542c0d004001050700006044c181c00307645d00000951090144c02c0b07034100a1000840c0c2c011600008500d02c01450904c1448011314240205007618145545c3e100c0c01e51040000403002c0507220000b04002e440d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 531634820 1250 531633570 531633607
    0x40506010e0d05060a1416030507090915061101050f07030e16030804080f0d0518041803081009020a050d020f04120b010f140105072a1d010f0803040902 67
    0x244800e903200407902e000f0780d0b03d2104940748a1014240000d0b04003000200c0715990180c04019001205a0040c003011401424010b00150402c40009000a940e481a00c0303507000d0000d104542000103404d09002078108141d808001071280e25240030032000080358440d040c0c2051080c82c011410b00c91182c5100c2c0b40443d5102c640711000308440740001001400c40041013210000800d88091410000c1215100c00207560403001144081001522040340b0752080e409005008100080c045201110413000c0d84014000f1004130b0407180502200710801c050400081400039402d602e44a6015401845809000f4100b4202c0d030300420800301c01c07070500042d18041c0141c0b038540d0040c40400d08105800f042d0038469010110f030303c504007282c401110708500002c00410384a45280c40425074400f05048400d4443c0709040b14209010710088014544080091142ea200d11003804260015010b4112060b444484a10701050b0704000c80040071082d24101c55480500584030b01c044411200c0f40072 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 531636070 1250 531634820 531634847
    0xd030212120a0b01050f07030e0a0b18121b040203040c080f0709061d01030b0907050306090109030311130312020106030204020a030219030506031c02100e07080f030301030c0504050601 81
    0x1280e00d01c4031054071070794107208651880003071001d0051400152558030034548810864041004507201107805034804e407001f0000680320380402c41d6070f00300e03050007a04810020480404c00305a200454071301b81c0300404e00c90080601402e5140d0040c484140c2e200c101e600b1282c01185c01000140602400d911400b008002141c00d541690900b022002e840785028001c400b0382d10328010700491084505000000d5025010001840d80e90031034650350740381d04e4004c110311107921440030046002d8906201e03050050008400200d1001c46515024080d0b42e5481c841545100041c0801c0142e084c03800c8888040b20703044040340b100341c80e0060003203000d04207a40010350002d000182040c1c606074103500408400e0301402e009101d08401040440944e01b00340c81c41c035410b0b4040f080030043c0300080c041121001a441c0101c3d59640c80400b4520161076030245001a40e8101c1385040044500a01050a102a0b010043c40c910760440ea2183c00000c0ca90081d039000d60b0355880018200d9000b05028400135 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 531637320 1250 531636070 531636103
    0x10609090f0e0d0215070306050109060e0316090e2416020a291303020709050a0603140303040303111207140702220608010605030c040b04021b0c01080c04140d0302 72
    0xf40311500071759690300c0401c0b0048460760740320000384150b20031312801080c0c0e0b905a413000400d9160603401c87c1c85000803003450394140a4640c0d151541c105650082c001800f03032040c045130400c4020b0b2010700385080306500040d03806442049000550b00310300301c1a408210405052200117846408034036003424450010643c96440c0b4041010084030070340085400c0309801c05440e81d55501403003401031144914010b0150344807540500006040ea0826a030040c89627900065265407a04c1d4142544c9107040c150103160800010302041c150305000341d690383c51420341080d1a10300740445040f003484004003a04100a210760010174400d00b058121505150000d02c0e1820182000d10900380c030002200c0304801c11441e14030005401a018003d010031180028050006084d1900a01024041a80b400c95010358204141c01c003030b038102051099121410001030130288145800541003c4001e448200500410701c01006045c481000d0004d41d05000c0c0e131810100c82407407030240e10300006182085181c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 531638570 1250 531637320 531637333
    0x1908030406080f06010f08340306050a0806101202040f0c02010c02060916030b10050a0f060f140924032811040b0307020f0d0806090a05010609090f0e 66
    0x1ca039201020364010f401060b42010705485100065526008003842d000c0880e4032000082e400151480c440b00f2880001521945150000848030000f8120050041d0100e9a51602400203080c2818000041d1071400014015400d00740c0d00740012156500c507104610280d10048001c648aa070007100c40724a03a658180101400114040e020b000100400c0c1c00602c117040009094881c0020700c1500030000f48400c22015065440d540e2000030020401d880060f41c121000515444100b01040148840c2c003090210f10309041c0010030a050702110311003045450741c0601e01c0c0c03e261004407480e40754120b80070001c906403007003108201c3e101c06003803000a03100401001600910084845001c1c0c00b10b05105020b420b04511820840d204070554580195080c081070042e119110000d5400038071030300407034800c2c1031410b91940c50701140108004c00201034100344100c07418050119500054480c030240b12540c100700c0001c00d0722031913202d85119580c407a0b001c3e445500941d40104500c10b02001601c60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 531639820 1250 531638570 531638579
    0x32703010204090b091e0c0c010b100305070f09050f121e0705010215130b0402210709110c0a080d14100302090705120103242a0309020a0519080304 65
    0x401300022214056680c03c00005c0f81701c044c030040400e05540c080d40c03540041d00e54032002c2c401c1c0c0d001840e154036290350b5101800c4569071421f24244a94070540d402003807900c1d1000004042140d964020801e00c2100316007807000d80d03520124406000307029913021008004a09845181c0b0711011194141c07600c000e42102c0d0503400114900c01070794000c0c0c0071611002100c0c403a00900d110102e80d04424808100c40d103900062100c50b82c5900140018030413540c2002a4010b4009280e50440f03118055100c0c2c0300c104008001401a488619644005542810248941551941c00c04d000081034504009145041d00d800c5910480e43e50180d2554032003549004906072126003034038001070748110f21000c001070100740b15000b142e1007909540482c0c999a441d581d50350540c0c140041401170300c81030303280550340c40030220300c60704403082e1008480318201c8070000640c1e489000c01c074040008240c01c00311f1031409601c403456000e0850344259403c0101c080041c1070700800c00041d800c040800e0000240029 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 531641070 1250 531639820 531639839
    0x110606040f11181207061209080f13141c03082802132907030e090a14070305010602031c060518101e120f02100918020c032703010204 59
    0x4080f50240c40a1001d0000582c209a0750750180c4038010004410141300080302060b030b001081494071a503811401d240c8400a1440c082d00280b80d48620191804810040007005820b00c00c500a01613808800d010100200803e00401c4090003400b1302605030045260060f1003c10b04028066000715122900e01724050203000c0d5100981c40002c40fa0101e90106485150076088440710703074041c50320709174817500c900740002c0d9800903201601802580314001c038180e00c80c00c180600c00e407460800040d056001211181e04090040d104204040c5801c0061094680001c100c4500464045001d074075007000d07031400c0f0041c04103a01301c1d42d0001030012003041e1f0706082145982c00b07401c14802c204551600c0e05110302d0f04024001b01d401d00424500c00c1001625600a0464002e41c020003403030581006903004155603980c0000c0040c002030010508014000d101d034402a02c0742520075041d40b0706001903142d280d0f0307805850300252440c00400591103400c440e0396181110740c50090700075911155180d0b102c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 531642320 1250 531641070 531641107
    0x120916090e0c06092805040501031a090f07140d060207060e071202010f0309030c060608060601020f1518100501080a02040c02010915050c09040204030f020a06110606040f11 76
    0x218920b1007000210005868000107842d80c2c60381c064150803500300300a20420084c43e2030707026840200420600400c2585507402240c0c042c40c0240c0003007055040442504201a0000b0400166900440100341101c00040b4268007100d04400c4210048140c0d000003030407540000c00010140b0f480065407104019041d00f00f141d6216528054445036595281a25040c1c0d80a920090004502041d0444454002d51103030308503602a00e80422458859618007048455941001340c1a074810403c0009544c1e0400a45800c02040005004050900d15000c0314501011b80843e00c1030307000296050b6003060401c00c0200b00d4842c01814011965101c40490301c0762103000f000d0b4040c0c2d04204042800d40e0050195004060b0f100803c8008003141c000c81c10300508001d021040f12202c1000074210607580c07400a80003035400f42494100301c48061040000703100036503000c10244885080160321217100810034580c4400244d50200703081c01140c846200802024996503640100801c18404500d0310b04040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 531643570 1250 531642320 531642341
    0xd020a0b0d0e03130e01270515040e071a0414060a11060f0403020601060503040308130201020708012301080c09010308090a0909140714030d233c12091609 68
    0x42101c0341d0302ea1f000389154100e030340380000d4000014034613030464482c82e51106e41d000e000003540405048507800020195494800340b0160769000341002c5c80100307040390380e4141900c0841e0500b860503140042104020344c00701c54452241401041400102d030044c541b0300030301480c040039582c640c40c0080345c0305010701303050701d00b680144a00c100101c0c4540c05101101d01407901906c0301c0009a0f1245403880d1940141d0303030100e04601541c0d10004103000b090290544a9401c01d03240d0b19551500c198090301c07900142e125190341c1c1e002d04949003064807003080c10b81c1501d0b004600550368142160200740201440e5211511962900c040802030001540104e86c1913409031058868003550359204080c09500c00c155283e046e004960504105801508000080440550000300d9141c0900c01c3d0140ba803c064505080310303080c0f0059070100d0032158081c060386801003614240104080d01224058014500c02c0c010304141c410202e1035412040010804002c40c407104044001d0b1100322080141c600d0701c81 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 531644820 1250 531643570 531643589
    0xb04020304150b0121050721140a0603023607030902040c03060303140d0609061509080d050a0c0f020907031d07030206070210120c021b0d020a0b0d0e0313 68
    0x14411041d032180766480014106002c0b4540684400c045d0100280710140c5040103100c5036114180c403000e05260080c001890b8440c00142008803141c0409500400510707111000c1d1070300c07105100503944d18000d0090400c180080f05034102c0341d02c0c9603503002014080782d05208101c0d20b040000d4a645038000800091094070184a4000c502100350161000350000174007144c1d20541d0011041161009001d034145021400304a01c2ea8810700042161039a4000b0385251f081d801040030060303000f0400000034288540184009166494014800e0103550564070400111240e280306110241081a2440d038000b008103c5908000d90050000c0100129601e070180d4151102c03070107011301080860890f40c024140d02e2400c2e20545c200700031440003064590a12801e08601009131406104a0724154050b800902d00e49040c1c014044d540008400705520030030341c000d00075006890300c068040450754078400031500c5400072000300c2c02a2100509040035403001084141d2031a40004043c01141c40455 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 531646070 1250 531644820 531644831
    0x170f191209050a080904151403070e010b0a0309060b0405270c0a090507050c1903140a0e0d05030f0a030b10030615260414010b0303090a0512010b0402030415 69
    0x900314401d441080402a180783c024150301c2c00491082c0009080040340284000340040d078030f41d010902c3d604c5580180d064030104102d40202e5040400c00c01c0c02502c0710103080e026030745c5040f180048500c941e119840825883c0e00c040000c10107240c2082c00ba20348010b005219510f04203000201e00f070101e5041009141095032010900760012503d4009088060590a00e550034084c1540241c00d024080c141002010004440b09201c2400580901c40c01030004184a143c141001003200c00195548880158101f064826140e04512000318900081d2600d1850b00103500300a400d600600704640780461300000d0071904168903a2060030142401c407040d503103109a1b10021400c03500c640c05004841e540010b080c2071510b02500300c65001800065280e191b102210b61032120b0341900f41c038101ca01480528002002200a0064210300901940150304000131800020884030040c8240381c002c00090002001e103110030b40120a45d520301810035540c07400c1a1415500c094101d4003442c121500c0c15 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 531647320 1250 531646070 531646097
    0xd0e060910060612090f0602070b01030b061804030e0301201309020310170111040e190b010905010f020309040203130c08010203060a0312020c0909030405010e0a080307170f19 77
    0x1d215600c290b501136034443c888886400042002400300e0b000c01d80d0329407000181c4000242041c001080030520411081d03e071540340d4600b0f108441009444c01d071181110700c90440c0c8405840c0916680190076240690f0781041c40000b10780108602203031a035000c641110408c1040160900415001c0042c0c1c07050640d5076581d0810310120b01059400d529109000c480400c061540d91108104442c0e9410000488040d048034a2501c0c8d0b10607401800700301040010415107600512000d800713145004002d01081741703001c00003012800c1ca4003980341404480b1b100003034403070f1007041550031421002d001196282011000c0d45134042c2c0b407600807249a550703407102085464040c02070340d001d80c10241c000c2e8409402c6644010501005c001d41004500c5251140d1685545455443e400b81c4100d00142d41e0715410304000521803103501c101a8040c55800c071040180540000440e03800903041a848000c49004c01c03c0924144101c00f1041c24580c00411030344090044032000700709035410b58440501142c00c6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 531648570 1250 531647320 531647353
    0x130b01081b090f071103041d0a050612060403050f0d061707150206040f0317040309050907090b0d020c0703020918011503020607020f030106050d050f1b06030a0b01050d0e0609 77
    0x11250350341581c10f2580030130040e902a4000c0980000600d091701d04003501d4a04903070080118004006c82070070304005020500c83c40f841030a0300108262007503405107250001141c6d803010003031720040c204040040c81102a1880800707584615800000600c21559146040701000c20000f800c80200d00440c00001442c8288403180d00401540e5000741070a640d03503440f0254141912b14096060080310481c08070014400310603207100b03901c0713900c40d144e0403814603042c000c00d4074006003c8018488a500c09120301c1e600c00041c0c2d040c1c640300c00c4026039100300001e0074900300303802540700a422075440c0040c00300c1c2038441301d03d11000b140c1c454000c00c0066a84c1d10780c0350200c01d41c2d11011b501304c1010480134026041007100210460000360021544656801c04200980004e140070703a41d40e0415040418010818001c9000d01800c4285174021a0440c800003040b40c0b001501e1031070305540e1184110b000380d0059013985c8405511040070044030a540d8030301a1107200880d95124a402948032590301140c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 531649820 1250 531648570 531648589
    0xc03010515100c05070315090312020c120309191a060d030e060d0e030a02030a270513091502070605370b0a030f021c0f02010305130b01081b 62
    0x1005106441c5101d035036500365503c040ca81c005607014001c0000200100c0c01010b00c4484d1443c1c110742c0000c046c3c290307080041c88140101c0d01c48070072600400800c088130f41c00080400458200040c07140c3d0b6503c541c08210310304400e4100886041a44120500c00c1c000d99111115107070720b01403030450541d074400c0704120182c0801000100841c011000307007d920b0030b0071000303000d1054a03070400160124035003450602e10f030020a090001a03000107139001447d503120350700c0308403e503841d202118000f100d41c0240107000400c0c080c1c3c500440030700b07040304491034454101034000c540000c8012041520000c80102035800408169486170608011074110052542ca42007010203e4101f03940c03c003160007040d165030158030343c5803001a407902c203510100d989480d1a10025803044680311102c0b4801d01c107019000c0e10030107058a1025642e44c0d55004503181d40c0480443d182d091030009101e03940e60f148618944008030001d00001d89060020480401c00a0010344a0045114240c001c8070b4490420401c0c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 531651070 1250 531649820 531649861
    0x6040b1602100b1918061406041a070c06051b0f1002030601180f060e010804080f070c0918032a0f02011110060501080703020c030a080403140c0c030105 67
    0xd01c00c1005001c0d49480f42d00210400c40e008144004155081a459621901a4215220008002414041c01c0c05684a0307036000313000000d12920925144d01c0001d269001e588240300b40500946c065001c81136241081b2101c2e036a220b03a11001d81c54603030600034425001311424500c66888200b040300301c0304000400343d1072014058001e0a030700c03070b4130540500a07400141840381800314010780a01d00e05044400c0001610705003010301681468201d00401544001889a052012640070b02010503041c42c11500b01843e0090340035904c1d00d00b450710790003c08450b808500414600790b0b01d001240d21010600420900990303805110f0b1902c941440035000c052050b401d200040c0c0f00b5240006400e07290032020141c0141007070044244043e180030704010004100c02c54950340d03144140145c0d80c0041410390084800d107801c5003845008090706907248104280c0b5800c2c00100d00008040600c10a0800154402c0030017041c6c85400200006039a80603402020f8429400c0800098480e030300042e00c03040341d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 531652320 1250 531651070 531651073
    0xc0803030103121b030c020a050a06170a050c0f03041112030d06050301060f031e06050f160e01080a180204180b06060309280b0708094b010e06040b1602 67
    0x460717981c1a101d20280c07540881e00300e1a4610001070300e0303071845400c1008000030303211204e4005800319100000c110040c1050b03805c524200034002050b251100381c1c0c901c1ea5101805035501c0d00e4508143d890045540000ca51050b401e4081c18424000400901039114440760f081c04102c1d21041014240d4215018040040108000420104e1448070301c0004c2041c54032a0200c24810030303111441920001c0310f0241c00d14806c50107008941c030810304440e0000d91689840c0d0000044c001c002060704030041c1020042607114400154640b05107560072416544c0140301f006401e100050703c02440241d500b081c2c031510070f92070003e1f2203402d104085034400c8440d034014000f54900e400c0c1c003004500c12034140d20001c001c02400b400000d110090001d01903601a06c070303640b0724580060040c3c580040510b000c5a0801804e10004000000064441003200d5141c031101c07804011894500c0820205004a403c0b5801c09200800d08000461071038003131030040100300d680c1d44c1c0c1c1080c040903013442c020945006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 531653570 1250 531652320 531652367
    0x50915030c040b0d060c0c051c050711030c0306010e1006020316081303061802040506011b0b1503120d05102111090a06050913020a0e040206070c080303010312 70
    0x10310b0a68856006260002d080e5095090252500012136200e0b01c00030700490b441000d4203052100411001d01800d2034803116042c282c51203071000b0480e0092031001480704801082900d0242d50600c16100d40301c90240481e01d1a6958000110410805594800c0e91654003c800701d04203101000312000010051480d803801c1800c0e5032000401e074020908051250030494000c0f0001d0a01e001d082d030440c900407040310380342d41d1a00400c03048132405454141480817420902c0d52082c680c00d000c80c44550003150364003043d13894904659141c05c42d000d040e685802681200e100c8000100003512281d030f40ea4204002958411140951800c200d009191a95800d40c01920700c0107100b003441c500151040c0d40c0301c0e00210280002c01c1000d001502c02d0150a81c0b40c12040c03000341000c1c0c2c4900d521040e4120f0200c45001e5070340115031540024000c03440c10800110029095480d0f50048506180d4003540b441c42603691810300301e40365002030004484c0c1100d84044004c40b603101d180040c000300040f445160a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 531654676 1106 531653570 531653593
    0x60603060e0a0c050d09030801080f032115150304051516030f020906121006140a0318050102040902040611060c1903020405091005091503 61
    0x815103020010025002001d558980107184088000b881c1e161403041290644240740c0072110403420310740034a04060340800c0c024100d540d4482a16110510801000d4483c49800d0b02003001d50020107d0b104a0840d0754202c0b904541c0d070baa1035519244103800800c820080440154820200c0802000240b10081c071820240083c410380380402450034003301d0040d410388501c1003080580d6199504440c00417a4103c0b80b50090041134162940603041e00184c18984c01c440b03001c5403901c6c040d070008103640183d040a400440d0042003909010100c403045006003012808510b1411144a401010400c01c2c4010700242ca08004056642c600742000030b09607002001c1d0f50301560f80b0040c1040340c108409002d45140b000c05440300a250a14100100c0107400350340c010a81c0a2540000c3c052030281048401c0102c0703030f00707442e08092a030702c0c20054000c0c00407115245416400040741c0c5074 = true := by decide +kernel

theorem cover : BRFrame.Cov 531474820 531654676 := by
  have h0 := BRFrame.cov_init 531474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 531474820 ≤ n) (h2 : n < 531654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
