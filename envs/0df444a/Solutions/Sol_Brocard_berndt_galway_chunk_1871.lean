-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1871
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:58:48.990319+00:00
-- url     : https://prove2.me/submissions/48314adf-73fd-4058-9854-f8c6dc37dcb0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 336330935 ≤ n < 336510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 336332185 1250 336330935 336330961
    0x60e01051602010c020a11060403050d09210f0f0320010902040f0204150c150c031a040c0203042d0f0302010207120209010b030a0e120a031a06040608060307210b 71
    0x38100c0f540140c86c01c0040c5484984551580ca8a140c1e003000c0e04120010014408104c0401075020990343c2c11403c505140104c041a4002042d94103c06650040c60010609500403900380652021f5000c420f040302d40340955100794860540c0b1502030041c1034903002e202040d0020f0491600c2111b040120003e45d503000f0b0200c2c0607a00500440001c3c7e400710f2a007140c060402d440703050b400b801c220340741104003c183c002a16410803540d40040e85950450f40a00300d10100d02421003412070302408a92041d2000035501d024a21070304c00c001030071201c800c103060f0040c00061070307a624044a28042e141c5882600405c040184812401449104000200700d0030849440c01d003039a000b071407441980d01c2c00300000b5064101600440140742c0d134a154051400b401c020b010240506201c1060300c2c0e00500030090700312401240726162141151000d0800c1d50b070380d0400c64054400c18180003c0a859880c040303481c251940c2c10078018810711811060040c411040d421040900c650952031003030b0f0f1003016410384 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 336333435 1250 336332185 336332201
    0x5070f050909030f03100b13090b04021c0b0f030f06012612090a0905071d0a0b030a020a090b0f040305010b060c1c14070b0405010506040905030304120c060e0105160201 74
    0x410340080c42004d00d1004141c0085400480b0150310318009031301d4500b2030350349030302180d03c1040304412110108070b003e000b400b411050f41c074115421410200910407400203003d5030314180100715601c085202050b501d09040194802e0054121145000c0040415607a10002c0c0100c04080b05401d05440c06407004012814010198001410350603190750100c0409030403149440351300821541c8081384c405982c0c810148210200d54401500d0039900e00300160041a02801d58000c151102040c01402003072000c49422100740f103801661010301c907108485c0003240b0780040000e01000640040001d50074006041506e0107403000304541b0b00c10208000144c86840da85011540242a800136040850116143c0d014a01e08000c0d880e22100c410149540d48103100848072846d184080c0014030100748034141d0701030f006450800408a068a03003a40e88d01008000908106d80c015541c203083c2c2c03280c900d00707a10a621038400c0c40b2100c50400c840f80a040c044a030318022030130540c4141100307407050080c0c0034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 336334685 1250 336333435 336333451
    0x614030f0703050d1202270a08030a0e0f040e01060e070801050405010f23030715020c03010203040b06060a090e0a060e090a020108072f0c090c07080f0c0a05060405070f0509 76
    0x991403c01c444141d0b05420511000f17000c2a9003404201800c10306c002e45244801d0018060f801114090410480d66103a150005c1c1c83c203030b10500640340801e03000385086150700812946501101c0302c0300c2c00a4080c04c40e03031603507c10390350a0110004c1e040041c92001d5004021035210021144e0703c40c424841181d00920660484007405001086504104e01c0c9141d1041ca5908500f00101d41050100303143c00e80c164040307042e44441c2110354850755414001007241e980c044000750300e18203080d2118511070002601c028492803000403081c1880303002c1d0790550001d01c11034548811a10300b0890201c02842e091055014244036100042c2144002241c3c0380800755050b11001000c0c0c543c010115005642e45a40d40900c0b03c0c6101c0b446640403c5805021041454100500041c0b91110a0211045018145c0b0000c2c0c04140704600002c0c16203015601a0522030302601c0d21f4100c021002e519180c484900600300d80280400c1c0400d000c0d0200e100001c1e100e17840d80e00710155a03190240010a8421180c0c40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 336335935 1250 336334685 336334693
    0x120307031806092a080318011101050c03010e07020a03120f0e120a0207060c08070206030c09060310050a1703030a0902030724020606010507020f010c14010614030f070305 75
    0x846450003640840c03031040c407015103590001065603820003100d080882c2903034843c00c0d4041c04201c08192640100120f01501d0001401c40d1030a0400ba50324043c107066000e81450005540750341d83d1061810955146a0340c00a00c058104204500c025910a010703010422036910005034445000148000ca069410740e2400c0c1c8407a11030403508014000718a0081c0b0540e10f903030080a100074104103c03030004541076251a81c0d210408800f901d491182d038030210510800c107040b200410303041c5040d1610990140c0e412950381d902c00400410340d21803403d10940c0038401005004201c00340038007036400d03644252501d2261076201d0300091092103141c0c1c54081180c2c8200000382040005401031178440b48041c00312072025484940e02103a44564006071801b01012076806000240d040040ba0340100080c2406403801c4226000300d0304058404e820319040c0600d8401c00310810480c181800401c000090003089111f03202c101841d450410b480150307100e8820404a00806200802e66008481e0b00100074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 336337185 1250 336335935 336335941
    0x2100507050a110a0b0a03050f060a05091801020f070602070c090510031506050907111c0c030f020a06110901020705060903030304170904060608070f0c0c090e0a0c030804030b091203 80
    0x440da2110341c3c0c0e2011904401c0388507000501000c0700015008074138a40e20040f441c1e2403e00b0121036000c2c2c005040d1841145010410007140d100c80705050340000e040d00916120040e11402540680b0a80510814411002400b403080c802a07078040c02030113100c1e03190440515540c0f41ca0b00d080d9001603031a400c002c8200b00b8100005035160b1007800024121250200300c041e65100003034547c030022641b16001c14503c2002c1c0041600c28426200580c10301140e1200c01102c14100034170328900110000e09000d40c4120806445000b080021109a0301c08801e0240b41242040d8141c1c1c1d070040c0f0380150240c45501e00102e00391915034146c80920b24040e000354155940d03620790031035042a01010b9004800304001c0003602ea02c1e1401020043c1080d80c445c2d04807030400300001809042070002c20720410016002d03900008443e4040c071411180700d200b012a0348465500c4103410305201000041102042400010070414070b0f0000d0001ca900905071904607559850341d01e03440d600c6803031901940b80700070000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 336338435 1250 336337185 336337193
    0xc021b040c020109060f05100e160f0e0d06020c01060509011206020306060714070501120c0804061a22110705030405100905041d0c031603021309120c02100507050a 72
    0x4400d500954800401d03113280310703100c000440b201da042140200d5200c1c41000070708400c4c0706000c4020b01030030800203258548450300d426005c21800c070034020010382c0c950078103019208903054103480c1d03c000c020071520321040c0340c450b000394040807507507100b5400c02c0c40000d02c81c900f241000d0304861804103a42481c1c0c5041d9100c0d402584020445940b01805010130408140440030f03c0a4a0450f200200003460410001400314081907288c2c1040074140601c03490ba41d940f00d200182c0083c1c0c00340000c07030f0521703040c01800c10707154078200440e0f04400700343c40500741c0345040001854007000d801010031061603501c174a03c88034400da01024080e41c1c8200020440c600304540100040c078058500040203a80b10000242a90400700c03203507101c0e240c02185440c440d40d0502070a0024142140180a8110011b0074010240c10074400648070b1400c40c02c070110740c0c40081e0041d80105500000110012030401ca000d081944404000d84c0111000340c0b00042c8280114100c940c0940c0101c010160031456543d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 336339685 1250 336338435 336338441
    0x10f120b0604150c060e2e02040e0106021005060603060f1e1309061401051e0a0f080a0c0902090f0f0303070f050607020f1204180f0c02031804150e040804030209190c021b04 76
    0x9050400d5820000000c5c0ae0105d01503260107003640741e010744100700c881000503041d990060f001034031446003002030006076941c41a5440106c241031310701d1450300c50000305000c0f0150b03090b04400c1d00001d0010310011000c5041d44011000c2d8810349040000c40300721008010a8507090050b650843c060355103801424040d00d01040301458002c10074100191130706020b11400d081c1e5800b001c1c4580c40401082d040107030001900c0301034800c0c6401107090418180010b0307228910024042c0c0110030b0b03415250741c180c0341401140d4a8503008258060703010785600d040707030f56580201ca220340140110b1180d81a47c40000ca064400310189044103403c00e800c0050315140c400c50303031203200491070740c5001080d956880750060700702441c5150082e42e02d030740c4404a0590551400884244281d1030142204c1154003201e10700425900c5600180c5071030360795403404103414460b030380000c0d6001d0340c0c0c4030802c07500140001e81d000e0840c003d0101400b21924182e0141e0f614404c0e54504403800451254000700c50500303038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 336340935 1250 336339685 336339763
    0x40c2303091509010603020a0e181c0302090a0b0f09031e07031e060c090f0b07020312032205100f09030c1b21050c010f120b0604150c060e 61
    0xf0700002445903a0303900164640700705034041074000c41030100f0002d0505c907103c101e090550f0304c0006054000821268031240050fa91078040500d40d01080c486100d4482100c4030b005801c8030f1151954440c503085114029070040001d691007481b9485038a0480c1c0150b440c0b00510900c5500203001c1103080d82c0e80d00d00884401e140750441201b1904020000c035844d4001d11090a0083d01c441c8c582d1400c012a04241e0b4115811241c4400c40c2044400c006841c00504411090101074505403a81c50301581d45e0b2a41180c00d010020300820a02c101d401d0004c041a0403020140c052010822403000e40c5164041c1c0e000008040c020682007408000400e0011b0f0703410202802c01400c0780001d940314101c41c0040003c1b00115501080907290381c900700501009a9203c1c0c0c0402d00f0030f54014000c45030020722004c0010104803156880752400c6880f070316002c0a03200a0284540000c660b00b035019802000013080310819200c2c0b505040394418181d00114200c21101740c0d0340203070400320a82400e00c1d0901ca03a60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 336342185 1250 336340935 336340951
    0x1704080a1106040605040b06180c09060c0d0e0907080108031605011b030603140703210e090a090204110301050d0803150d0b091507050412050c040c23030915 69
    0xe107481c1e10300c08800b4802e2500c143c1c400c00c000030755070606040849040030010450b90051060781402c49282c1d0031040389550000000240c15610410382d030115034903006089210402d8801c4014221045030002c001a00c9500c00fa40e15646a5440c508101c801d103c083c40f40e040550000c1010703000c5007202010100055000c0c0c0008111500d10700200407120060040a1001941d92081841040400060400c9a8009000800c502419a00c2e042c01e488150f41c802c1c420600d119030070360f082c81c0c022000d036103690fa0004c001d4803d030328000f0442000351100060480c4a9440c08003108680c4100700b0549040c1c5802510585580415545c0c000e45640050801c00150700c0d49040a100780d500c4020152030180301e00038850b41c508102c0002c84c5414108506801c44800ca5000c21901350380c000252800c45884002c0d028901c407407800d183d410601550b904a070464240203c0d600ca41ea005207119460056610b0001046031041d01012070a00083d01c2202c0640c0202040fa5580000d103c0c40c40c1d003000300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 336343435 1250 336342185 336342197
    0xc0807140a0e09090123090d08041b14100c03020d0516050105040501290906130e01050f100902070b1b04080102070f03030c1b20040203100311011704080a 68
    0x2d4000011441d480c1100e242070160b44500c40051410300000c4164801c4042c10740003820390800480043e200c2000602c0706041000110006003842a28035008000304100140410540d1b2210000c41b400890014042d01425070110f00d5960f007031045442c0d5039200d4050780541042d444500e002c4840341d005402428806078045410000f0030400e00c200fa00581c4a070000243c0420040c00008440c0c04081d0180060365001030703110003540750440110740c400021141f2305000e0a08000810003480e600401d008150328240c108408600f040f444140171b0342e01d00ca80e9012140d965484101a031040060080820b0340d02e6002c1100c0d1041c00401070305115a07850400c0c10281c8518282d42240c101d2681a00d54000040c0084240360301031080d900d14804c20300d000100926400600ca407441031600008191040341e03800c44001c03c1c044c0c242c20750020402081950389080044031035803440824042602c1e07102d003204e80114150302440b01000780d14581840d01d01c03075603600c0d2140d1809030040d024200602031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 336344685 1250 336343435 336343457
    0x10312050c0d030b011211090405061203030f0a0f0c20030703050d0c02030717090a1202180c0c01150305010c0f080103080a021006090f0e2d0f0601060f030c0807140a 73
    0x103180c1c0120358440c0c0b4000e0b10175464001c0c0804210907074401402f418013401900e840c500d00114003004690344500030001111454440300c0c0c598000300201c00d440c1485a00d040007401c00e95521020a0f400da48138003c03101038006c055a8020f0312407003040002000303d0740c100f0400d50000c840c0d13007103600600141d0042e0713428002252038800c0c2e00c0003140796207640710a00041410141c07600501d540d014000c1c1b100c500d003000701140d012440315982001049201e418040004189000200c01c841c00142d01d00c00074804016210f008011800302030004a80703d508011050880d0342c442c45a2520b560f40c15030754041103034a99120011a640301d03486200843c040d005214468804500400c802485001000540e10800790540011245160307190b04071a0050007024141014042c1070100481042d90244600204900b42902d40081591b0600b940e006e0303030000040540d0000e0410001001d603441c144864000074001f2100d601080720500003007583e5580c46c162400c0042d01400c40c43d0094100442501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 336345935 1250 336344685 336344717
    0xf0206030108030409061a120a060b0406030609180b010303080405030c0d05180103050403210e0d2607020703030f1b1203060807030b010512071203020105010312050c0d030b01 77
    0x15009800c00ca201c1c0c1d10016003040080841d101b03840080086c01e0719404440d2507004070300151312400010071a030003c0c00d80071a00454051744888010001c086006e9540c40e035610024010385030501c00c0d030300d420389417040c0120350f0458841c036544113a50201115080303a003560350507540c2403000750003521144070078003d82a0040040100000c10070359516426190101c50808515800d41d107600036040504100038040040d411441c50610300e11101c0140b02c03003c0b00c420140008101d500c403132000d18800d000d558000035400905502d118414044410401c00700407521017408035040e80c403000140d0100604102281c480c1d0000d1200c1000f920342003030145c1c1400110140700000e1981600c40c0c12034040c290300c0c51601031090000401614015122182c6940c5032030344501d10512aa40c000c0700c0c204074020701210140450b002802004001e507401e9020703401c0c024024003090100f02c07150b00200c9058482030780141d050315004034180c0010965400c500d002100a00382c004055818020720080b83d00c030503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 336347185 1250 336345935 336345937
    0x91508040512071b0801230a0f051519030308060603180109030e03070f0e1504020c030d020d0f020f1602031c03090b0a020f0d1a0904080304050d05160b040f0206 71
    0x1007401010f0300818032032403440c0301d044c444085e848159640e140c42441886001c0107245100b89000c0740300304807036596030f010303c0320003074843c1c03140002941d0326000c100200e42c1320000d001d21715102c00ba10390f40c46032300840d510441c0b15401d034000907001c500d80000013941480d00300011580b028800303e0054444a141041d142074410b0740208034040346040880a0f243d00342001014000d002042d122040d03140f9000c00146c0f00c3c1400740c444031800c031490210418a4541c2d030121034410010801702e036503c00c8007042000080d0130102d4003030b012500b0000c4405042d0040c1c02511041c0301d020315518501160640c4954003c1c00b000822a05070007110700d0441c68012158244c032200d5015100811038160700e2815048907840101903102591040c4001506036003c0b009a41031495005030000702c1c1d15102d008911411600101300d035015804c039003044200403843c4042c6020741d210b102100c500000c901815515401294001d82e040c044103805080445d0455100d0b9810500070060180092000d8002c90740e2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 336348435 1250 336347185 336347197
    0x2907120203031e070c0206030c0403050706021f050103170c01060902040b0a020609160608220f02030c150d0c140f040503150601020307060f0f0603031806091508040512 74
    0xd07810101c2000081ca0742c18071804441000c045100c107907440c14610140c6210f58015020340a50004170008141d035840104540c0070f1a040310490340805e54442c0d00a586005100c44d14010403204020849081c0c00c078002c0ca410381c1e506c0003595010741403584400f2860b82010840c078241d036407203800c0012050340a10003407015203084042d05a84d00842c100180c5000d201800b0038501d5808040c2a520b10542c4005041c260b0740c26123007040403516a0030b11500481e403c02c0b0347d0740c040e034540c010a2007001000c1c01000902842074007a5149000d00348200810008945140b00c0501001c02c2480d0b00e01da250fa204070700c110380c5824440143e02c1c5128102c01c2503086681000e440c0c82c40001c040c080c43c44c08001c80c01c0030100300008041541b62400000703480307006035100140b0711510b410720b8182c0d013090f0307801034244100301c0d210410606549003001801c5c0e410009101c04600714803070b00815031350707c40d2010030141c1e480205c2285207100112012180b4003002001941e59000d0002d03e6410840d08000402e8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 336349685 1250 336348435 336348437
    0x3031707050a12091a0106030b0909070506090333010618061103041814060904080d0c030e0a120806063c1308120909063610050406290712 61
    0x5621b41c14104c016048a80c0321080714801e40c203a070108503840c4000180c0d41d05840341681c0b26925000d020300480d207070904511003550300390440113460360701422000462000c15801c181e074207110b90703850805480c448a407403100801814651b900344012400382c04440c1554030b00d8400c9030b00d01075803404509441800b1744081c214881c1c03a40300c842900c0c490607000c940c0155044230b00b50643e007010740d10101c151181b4030401c50705688950900038024003a600609000350103c064075030aa605140c032058520b00d4074072a4000c101200c001c20858182207043d1261a00c8000044404c802c00010461000035544900e5000014203101000c1c40201ca0000c1e00780080715115041c2e555061294890400100c9400845000c00510079608181d07100d10490740c11034015030350b604017060480400c0c0088505414007078450252706107421807201e20320380c81e10312980590501c4480203455108100685800c0d20030911100c00091140381003a45912440c220a00d51042d00c48c0340206954841d1014a50032038808 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 336350935 1250 336349685 336349733
    0x207261903020c0d0302030c070b09150108010b01092106020d021b1c1706120f1207020f1005190903050a080a030b04050108070b0d0f06090603031707050a1209 70
    0xc00c0c1640208800341c8090011704080d81146003440c9218102d0040d0003019107401ca1480c0852200710f070a0000700e5480080221406403913840e94105806071101000c0300e40021610040080c41d540780c03480003005011108144205403001c0e032560400b940000d01c01c40201542000300000301c105659007005030302c40c0f08015002840100c08501c0c4e403014020b014106000038000000c0d207544464140c0c03940076404880250034080b4502d81e0318a4440b01d4a0309030380500c1788004503906101002c1c00781c640c16208558014181c20ba0380288441e40d15502130700004504207015030400b4141c0d100103030307004400c41c0c1344c087e008170b549440700344c42c280c00704ca01503e0013600010740302c500325810301030b415000ba02a5010300640d49002c203002c0da18980c80c82065481500800d01c80c0b00c0c501c0300d410400038401e05003030900003680c45400c1c0030010f040138402140403950600045984050425a16110310599180c007030a12a200b82c0c00d990043d0a401c404505075601c40c10540094818082e01458800040d841 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 336352185 1250 336350935 336350947
    0x1f14030f010e0c1512040f0813090e011503050a03050307021603060f05060301090c0303052a0f010b030a050604020910080a050706110a170708090a080102030402040f020726190302 79
    0x1c005a400c0b13002d92003c0d03004040100300c65225041c60380d00e4115030b000402101c2400d29042c0944203014455250700b6240d404000000c071003809400c10518030080704020406d0700b92079a40c20502c2d801510006013a80c01038802e21020074000e0300130355032040305401910500c0380c1440514a04002c0c6810803506155600190b400808962281c640e0001d000c0c0d000b040340382003584840214400e184030080030810002130311540d90103d54820889a01022040e1564010100426440d814000c00c40034803076203410035040e0545400038980403200c4d013002c0982000e0b1a60340074000c01b001e00420020101e060301000080c1c8540800514010b14002d40250142c0b03402c1540040000c01689040b2641e544001e40b0440800c090b0180c6400302502c54049694451241c54142e1460150241c401e510005911000540c483c064000710301c114403c4600b00301c0c2010305c4081b54200c0c0200302d13011744107524124000c2840d01c590328040307045e011b145207181e06140101d84030100b45403541016034002500403503e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 336353435 1250 336352185 336352189
    0x80604050c0409080919081b0f1c080c15040f060c050301060512060f0a031410020f0301030803042f091003122006010308070b1f14030f010e0c 63
    0xc10340307500112400d01c507400c510744503042c440c000c4049940c401c1c50710300c101c080109050400c580042840c00251400b1030760440a00e146075003c114890300980c0034800410705403403c0484040e0080400a2030409080310b510f074941c0c80e42120580030114032905041249201e080843d9500c91440381c401c00100c15414541a025a1603a180820a00c081880140000d58105040d191103800d085440d200582d108000100400c0c001e0740c0e2150031080d202e401209000b41d88984045640d016401c40d61241400800082240b003210100620520280011f00000c0e02c50001140c00c50b02603018419000d1140c0e180d00310a14545e1401912031078608607030380560070080c000d250700c200641c0c103442c043c80c51030f11401510114070991703404008000c0c0c50f0f600f100c40440034654034400c52a080707522541c0c5900d03003500b0356400b5040685012411500161480002004044034041050841003260f454501c910740590080441035505010300114802d145d02e00740304080f0041d440100800c006850141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 336354685 1250 336353435 336353443
    0x302070206180316150c11120304061805010c020f0f0a090c030608010e0303130305120f0a181101030f020708030c0316020d0e010f0c060509070603150326040f08060405 74
    0x442061140100d01c20071914a417243c0700c0300030700214203290b200c2c2503040c9451030010120064203a84500954003075442d00800001070030175142d664aa035602c00782c0c0310070124082c4045109490018003074900c05001402d1500d40180301020140414209254560020f0b45801458121071000d680d81c0002c009816814004c0d4401810304400070072601ca0b206811588903c801044a14817003a03002c0c495041600c12803c039035510a201d0301046107420b100e4111840c00c0001d40e1410310241c00e0038401c6480583c5100c614000701c0e4001904420b074400c00c030041d405843d451411b250000d6090108001081142000751320a9150345510359407490b000d86201d0071300000090404c215070080c0c540c80f4055402005080c0880001d0902148902220100f01c2d404296194018201c6007403030f0603c112240d001880074103803204c40e01e0070f0000e82d03012528810100601c3c4005032070451114241c2a00300c80301104a0f46290008101d24603007903d485001c030850003164420000f560140e810001031090500c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 336355935 1250 336354685 336354703
    0xc0a141204050a230909010e01050f240406170616030e120711040603031106070206070f1215080d0e060f0306040f06170a050f071a0a03020702061803 66
    0x551003504150400c804180d148402e4040e66102012455010710b5000c42c003501030000107030040c0400010b00d0300748083e031b01a01001d03c03a0451503003014003141b92038203000c0b900c520a00c1811440c240030044d1400440c03d400100c10030b00d0b0006e98490000c0389000e01c0c8610903225a06110042201e81054403065000c2d04071900c0210425241182810109502140103103500604201c07941d11011681440e03000c40c01c00c0b48106a000d071814000004040c0c2010012001c1c8413060309407407441d659100306980f100d0b4200c61640000c0d9000000e6400d50f4055280c03001001c4020600099841403114100948600c5410a007615400301d408030035050790100c5c400c20440c0e025242c1a05048100580e54024003003e443e16110715121800c5c0d03000d4100c50340c085402041004904100c8400ca00d21540c2c0301c0d02c2d89201642d45004403504c0c0c0c005040001429000c071085042e90100340c940c00c0f81c142c02907420126104007019003c100040240e941c24025100c06003841c1c80c0144480805020103244c00400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 336357185 1250 336355935 336355963
    0x140d080a111905040e1006020d0c020901060f0c12080612030f0403110d050a030e10050310030311070e010f0501090905100902131206020d050609010f09020d020c0a14 73
    0x1451100078912a505961050181c1114100d0400321150300f69681c0c007030307900708a14a001c0c0c8000c0002c04900c00e940070b012100e4a4007900c15481811804880d50b00c04854040c0d00300d00c1081c0100070b00344c811a01c0600c2c00328180703860200c1c0c0800380d4410307a03000300306249800000c0c600303c10b00083e4542042c6018151846000842c501b001c40f5201402602076031101030001c900c0c800d054074a81c1c960801c9084c015a1010564910b0086c0307245c054641c0c483c018005004901c04080c0e2a506030062040700d002c1e04400c1a694081855039a08440c01a010b02c0444024000c0d0f00c0c000038022040d20895029010804081c034155007000001003482d01c896208400c5642024244803048403003d08542c183d950948025030340724640900c429442c008dd901c145140c280c412405420b00066501900c64000714030f03828002070f00da5004100c1c000c902800b5010301c00441036401c10241a0590080c02c20b01d51404001d070400c46140013a070f00303007401c280056a90005283d02c1c001d4000c024860780340d0000178 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 336358435 1250 336357185 336357191
    0x5062d090907090807061b050a1a0a02071a0408070c060207211a1b0a0e0901080c2214040503030a0e030a0e1c0507030c031502181903140d080a 63
    0x54413401543c1c620702c1b4400c400c1441808075205d20300d4442e0183e00c40d0059002411901d01070050310340302c001141880741c18060b414003040070803d00c007406d00030bd42c034154204102c1c0e42c034125010300d042000100900b003100c45600410400000800e4400224010f040350380103040c40600d42100152000c0040d1402032519864803407203000a06007940e03130401c402200756900c50070f030344440001502c8840c0c45ca001092000115044161550201c940351502d2800d0704c54030b1560f40c0e5003024035034624032800600d0b03006010001c0c1c154034005c1410b400156048114000c66a414a00c0700420f0f000d10a8405031610303000017040004d0382805000f00006c140c4450b0080d13192141c0303190014108641001064420804102414140d00c4220145140141c208040d584c43d59138034980788441d030343c580c4000c8404107210304c1101a40032141c400c0e6410042c00b45c042421302160201040500c0c03510510b072590340303081001b0203c0400c0040a0101c000074410707005001c220319912003c0c0100384002e2080e400141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 336359685 1250 336358435 336358439
    0xe010f120201090303030b0307090f06051e01020a1203020904060603020c06400507080109050717030a0e0d0c172e15090515090703020a080105062d09090709 69
    0x10344643d03064101c0360589000290140720310002400c104055221401090614201c000c4000e600c4c0e1050048800c101c0f0440d0121415076413070b24a0403520003806000d038004801c15000304602d0159444601e41c54600107142c6000c280c001804c4481703075084a4002a404a06114800b108101854001e812070035101104203008008001141c800c200700c6003500c040c02c80d003202d04425292580c0307950f41c2c01012f90309050388607407800f8000c0c08072003400d0312903200340c2000260302e5000c00403a01601d41100041e519040d56800e06540241c1110740090700400842d03048030100e04980f103a0f2014202e03200360103e040c0020311050b464440c803100861a440781e0402401c00c00d6000740e112001a942c064400715031aa840058440c007089642c1c0601000d6040c5001c00002c4010003a506040b45e204880c8980281c0340ca0404608900464407194080b0701c0707000051056160101c0505140d0b80025150464002c0001602801c040d4259108100507000320300360880d46056900280e00c242e9500d04001554 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 336360935 1250 336359685 336359687
    0x709050c0315040b030a0602160c0e0906010b1c0c080a1523030102041205061b16020f040e010204030309050f0609100c0201170106080411010807050f03090a020a0e010f120201 77
    0x40700450b5003500c165a1202145019202070056000742c80e00000304540700c03074602c44003400d00c0a80b403408440000c44c20801250140e034100306203016001050041040b0380c2041d04011403640481104d4020148040c61406200799500503950104040d5960074000d080110345d5000351007003e002150400d00201c0c00340a503001c60b14103071a07801969068408500100d101081c0240700d80d81000501501a48801e0244a00025082e02440e43d030100d1002d802861850003403c2d00070080f040c90f02003211200704016143c40350400810003c0100001284c0318041201d50072a4415070085001c58807608003046907281c20302d035080e901c8200340c4806140008800002d1425045440a40103000d8080c04040969118081c000070407441b0226500165071200e01c044e01d03001d011030b01252041800c4071040c880d54810101103014005d1070701d900c0d05141e000d02c005021604010030f0640c0512a0f0390034070740503981e018000d100800c00111041d00e29418010184d002d014185c100c8060500d540802c1c000503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 336362185 1250 336360935 336360961
    0x8010f05090c030c13060b04030308070e03060610081b0406090302031501030b040b090109020a091d01090c0522020304030507050d020304180b010c05011b030b0d0503030703150801020c0709050c03 86
    0x210000c07500c1c02e80341c51700e2200c000c0083c542d87e004a94410b102080120805801c9034116000301d21503221549500d100904141e90b44c0d008440c003503089081480710703650085c028040b058002010001880d988401e8507805070711034005610100c0003d1118008109600702800203d1b4070500012040d40b0350b40c10340d220007034003000c0640b00030002c20a100000b907802c3d02c290702901c80b1560080c81a034482c1c1da40c02410f000303020803812012781c405801c51144400b03001481401c5601d0791000c02c400c080c038646010040e0001c005508822059075021602e0354140c4944015071199110b0340301c070b6440e00c3c85414514a4000303804515004d42d442040140700356004910880036480589001041c091003400040302c07030400c00303d0020400d40c2445110030000308017004c040d1609155540030800c8144240402030a0188000c010703105410403c00300301324074401e400400100c0208a0612101c5a0b50400c00d400c990002c40100c03c1030b000218180041c18550141c181c210481c84601421810201500b00780 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 336363435 1250 336362185 336362203
    0x9061403010509040804120317221203020c06010312032301050409290a0e07060e04020304020a1d010609301b0f0e090102070f140a0c08010f05090c03 66
    0x810386803400051304124002044501600c81e1a51403841c00b0701600d00a451418505140e0088540f0700001035082d00d0645c0004145c0c070240c18440d180e848160b101c3c4060b49450903000350405400f000300500042d070401c403442c002c510400e414420b42ea5008002004c03a00028100079911132990341e80c0c208901101101d90545004550000d0042c40c180b8202c144040f41030701d0a00b01199601d80103004074900940e0500c2004030050500949070010007864039034015005000205540c00850580303820580d01442d40540b01130300c1b0401c855141c20b0000c1c0c0004043c080340800094500061060303951001c0180010800641014a404407101c0244e100840410801c041c80e14400920002c0c49100e0b07800354401d509001c1109a05a10703040806401c2d00c09004401e03011507a0004588204414400c8890003908a868290502d9440d5500b5a81049021200c100c0b0712944007a2000b044608410400034503540000213890701e10140c14805556004110f041640c0143c070f5040c180d6107010a140300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 336364685 1250 336363435 336363439
    0xf10060e0c0a0314070c030f08010b0d15030605010305060709091a0409060f240e07090e15040c03020306011701050306010b0a050c0d0201060f0b040b0703030e0309030d0807090614030105 82
    0xd02c039000403408030024401401240745104c101010b01210980002000862030b019558412140540b01d02c207030b489101c207208101c030703080041018111010442d400301860841100340d03d41040d0340c0c0d48038a000d0f94020303017041c3c46a400070418440915001030348d0702c0c001d2010310000d1226860001d0321500724006202c00a0041c4e440300d00940c10030030903500852941d5402c000030485994101c0d00c01483d1041041c800340c030050304840204010b02c05006052059000343d54601600b8105120310390041405444014800c1000004044664503400f42e196518a10f6070016103034944070000504080901c0d090b002042d44480050040e500e010481c107064410103425a42e030b0351454903003100c0e18829959641036901402d500034610603410740140e403c0742c820301c640c1e003601030322680c0c402841c0c440c038071462303400c040c1c100481d00000340030381c000551001180c0b0079a0308001200c40460b00700282e000102001445003010881026000402d220280c2464546001941d034400050455884103000e031034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 336365935 1250 336364685 336364687
    0x31101030509030d0e100c0318032a0b060a060f1d030f030706021e03010605040509130807050c03010507050a080f13141506060c061b040b04080f10060e0c 68
    0x1094450100121251185500c40c20000c11101074007154840760501602e074110f42c1052071540900303100e4012715641c4070301100035407100d9482d5030742924643e000c3c2100038031054081520314038211908100f010380600900100505142c10820040351440c650003203c1072000585d0340100e1a81d01c1800552401181074105115050400c0003c0ca00303443c83c0c0c409110340c40700040c18000c00c00700b6006007084081080c880c078a1038658101c0114075000074000c00000440500c0104800d243ca0226030b50496041540e00b400000c0c1a00d40310740d15400b40b4410741d2130783d01188440b601424244a225800040ca04e03101d8100b80c0b0344440100f030218054043c200c824a480003160703021145103454248150710000c05160581500380321a02c40c03461a8500307500c07041410015900d400c1c83c07404c88e030041820b200600b06aa8a0091304039003c1410f030b4480f50101414800410350b1000c913001080a01200001450120912181c4d1031800451880c0041094104041000b0103500300c2d40c0d840e04002e0080740c0c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 336367185 1250 336365935 336365941
    0x70c0501020405030f010b030f0c09070c0303020405090103080a0207050a0b0417030f0c15010503150f25030209130207020619030e0304090614010c0b1f051305010e0a060311010305 79
    0x1800390086401041d13150083c0c0711010304150055102c030040707036416810780e840b1184004096403601d095444468016a50400007602c0c0c500c40e00100100314803d080040c101034482010030000c01098100726540300380041d0000040c2d0b0104031107401068206c2c0c00060080c02c1082007c1c03e0300491113000640300144401d500f840c6000d1060780d0044200c00d412548490110010b160b80710000c28038402080b01e50000030071107003000729a0041c196001c12280d212500c0b0070280d5104140c0041c10442c44142c01513511b11410b9000a4558082d145503070b026881e20181c130104082c40208403442620184108000001070b01e07020f0580340da43d003c585402001c1300200000360080d00b1288200c01c2c46000c0000c000c1080545a4000400d862100485510341c009150040d990b45010b018054004480900080c035041c191a600046881e401101c4001841e951000300d415000002030104410b40c0b0b810040c444078012403d5140d206a02d440d05001c1360b0302d151a04040c0c07070400e10100303040507296000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 336368435 1250 336367185 336367193
    0x703120e0c04020f0409020f03060a06080c093318060301080a030c0f060501090504030305090f0a060b010507021503011a0406050d0b06040e0f0103050d0509090f10030804090c0f030e06070c 83
    0xa40317000f0210440250340e07411810404034042c1d4003c4401901c210074511020402600c26007196124400d00704482d4508050942000703062240124854034840c50040c01c3e0a003140f091000903032070305000640689458069400d481007020004007280240310500040000e440300082d1015040d800d0f003004c07500d200c0c0743d041000461582c190041c0c40c160820000054058165200c1031060740240e030200306503120003101d25140c05e40030034502813540c0810041400b080240d0700130a540101414114a01503581c1d01090103008001500043c03182c01000402444480c0700e201d10426a03030b0500145847d045c01c06c054000e020b0800d86d054159030710030306621152205821600609620f001c40c0c02a45003500078620305603400d0000711158080e100e108024580102e040d104ca00c0c000400445039035680c480000d0440600800562810728452000030110f40e0400c0144042d1422000100319200300b0718020745183d01d00340150342094901029010048404202d0756040040361410414264480c18 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 336369685 1250 336368435 336368437
    0x3050906032214060a140f0c1e0d06120804170313080c1915030e0114040506090d051207030504020102011d0c011409011b0c080604080703120e0c04020f 67
    0x18012a4141020002c203110f041d10b002d0700c4592500080b220140d4408900300141c0781e40410400f220414007011914940c1c40078a056840414a21070382e041240d01c0310303051820204065410038150380000c1003081e9117041e014050291480401c100410401035840e0840d0b0300c40d40c400c903201c0c0070003001d5042403140d0a10480744000790b059912441d8645901c406900c407000750200c07074402c00310714042034100c07081c00095000715600f0500d9025560300c02c0400f603000d0b000505e41803010707542c0c43c00080600b80031115014055401203004002c079181130844140380c2194440c0074014001d090210425400500059a6201b14107180102d00c6071980d10050b03000d4042080c0d43c0e0340c0c100d04040201200400010840383c001c1091b65100303940443c10314102610300c2210310503030000c0c1000105407040310500a000e04d000d44a07500701e918503aa40d448031410440103403821141c0b44400103040080c1035000f030040c2d01101e03c000c0300304240e50b50640307000d90300c800d0381d202d0a0003103401107081448060030360 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 336370935 1250 336369685 336369721
    0x1060b120411131a0405072a02060301090b0108070203070b07031d010c030f2403060c050c0709050421020d0f11070f09061d0705030612100504021201090305090603 72
    0x14000442c0c581c450109080035266000f8210312003a694030700c802151031305005a030702a44250329070320702041182401803130f040e242103003248c06c045800c1409001626a00300030340c020803400d080042d01c24000d400041080c0e0002d00000115030060100c100401c0d03525500720f42103105424000785400f00100002258461580c9484184d4644403040c15096010303000141702d5907a0703410400409807941c103040400307803071003059501d241c003401028000901241d004640490090401c14108031408070041d2801c83c076034002c4410f140e124020310042024240d000780d4404440e4851090051560400959409550520b1400c01c03003100d600030101d60042000641544841e0b060f1840780e900c60080345280c0d40c41b4441c100c801031030014002801c0300f00240700480c0e06002c41e10301c882925044000c5a60390005441b8a40c000b00c2c148883c00804402c200e00702210b4103144020880740b0b004c0c0108000303220034110203003550b410980050002940541207540401e0219151500d07604c901c01d0000c49035420b6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 336372185 1250 336370935 336370939
    0x40804180b100806090606070b010311040603150608070e0105030d14090406030c0513140705070203010b0d051b04020a0e040f2c070f060801050d140618010e01060b120411 75
    0x1542e101c0b110382d035208030460720a84040d529800f4644a5405120040c45808405407140d480c1000510006900c40c02444e40c1e0701c80180082282501c903160100500071042000c2e0360b559840104025a100601a4000410103425041165894075020039210010000742104200791070b200070200c10300c0b00040d5208034001500401c40242c0340d203400207040407180900c1d846440c00d9010450b403030318270b4091400c4800300c41141c562151540002918581c103c1d060499055403a00d00307013002d50b1908519002014000c400818090105003400d80c019482d10001502803401003044804058020308041d074800e00584000400c0d60b1650485001003400c201e1103444c40184d00002444070407114480340c06601c83c20150346070030395500200d1900b11458418000400c0701c01004108504c1e0042c48608040d00420380c0c030745030414a025140c01c040080300c3e116244010b074a003504218a091213008089131804c0e000300901c07804e110903080030340584002c404009810400080401403100d24090080d82c5c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 336373435 1250 336372185 336372199
    0xf0a0903080d0608060105190512071503050109050a14011a0403080a020601080d09060c0201050309010e2a0915061c02070b0a05071d101b08090108010e040804180b 72
    0x2c1046640c003030301c0188102c40841c401c160020500d8540611402c0c800940104014465440c2005008005030f04280f03500d5207005400c00001c568034200006a4505801d035070004583d814240820704030f61000d044000c405260200c00d032510400e0f51412815100b4640c1c05100044420f40d12100f18070884e08014120341020034a0107203940c0004641c0d060b540030000341d614100c1c403244203c0701400c0d0391107000000380480120b080594047d00040d80c0000211002141c1003814030f10f078510f4070340343d1315a000885011b6007075800081114007c11311002821141c5001906000c0340c1c01801408000c4101d101e20400038000d010310907013640c07080107600541d00642d101c01c49070800c0c0722030501c100c0c1d8820f17446081500052105110300000e480314041d03101c6080d841d4aa1070b050080340d51140c3c2140080c03152402e100c51040d0584c0704219041d6204003480d40e51400c0840005050b5039040e808000300c00c0c008030522000901c00c409440030b441c0510300202070b2860182180000e0300c102150250440c4d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 336374685 1250 336373435 336373447
    0x140609030a0c1d0c030a1e09110901050111031206030109021210051b0703080921041503110417331005181b0c030c160b0f0a090308 58
    0x8428500754110341d20000300510241c8001c94400f0144812590034403003000030000100c4400710b0780c0c000c2001100c00d00980c0603c01e02d68603035608843c04483d0940300400320381103000140c5002480c2c7c502414080ca040000000101c01a1b5900d00555a610030b00c0d580c20f5001072542d0300e00b540018583c54005001c060404261038100344c0f2401d400003c0c0d41e01904100019041c448802c9050440354040d4150615043c140e890465028030b02514403e62401203032090500e4540070000081301140084000c0d030340300d10741030400b1000c3c01d55a903c5014581401c201d840c00784c400c0d2040d202100d40700905890240304150b92175041041c032a060000b40c1c00f8000264202001c00c400070b044100f01c0c64540c8500d6115440b59559004262044651100790380f80b8038001603282140a54100c01e2a50b19021540545420722406811021134040682e101098042801804001a4a0410708481c1005985003403195042c0c5512a81304101255240001c80c12000c0d48680d04110081d90821a40b6888071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 336375935 1250 336374685 336374693
    0xa020729070c08100b0a0e130c090b040e060f060607032309010e19120602040306090317010f08120c030903010f150503031215030a3008040c140609030a 67
    0xc000b50007110124811020700c081c0c8210b0510031114000030041c1103540c03403890085000c80e0100010407980c86040c50703102d80c1c0300244c0e0030710000c4082d0144002c041102050701c2c05210845030301c0c0c24885041d90002c0103004d9004102c9170716542210081c0d4001c0e0340c4403c28141030341c03015001c1400c00340d204c03985134902c04412580340151202e100240d9401401d0605c2d442040449280b007481c200718803600e45810440c085d0070301680124a489200c000d07013007e907682c90705400c4440c40003040e4042007107000003000d00e800001c2094050030390045c0d50030300310b404e0800c150742c0d9881c24148a0402d240021328612542010030540340103c0b0f00800a10000c0503000201001e855040d01003044182d41147c0810305140200c2520002c8140707031404503155841c4204c5a00da40041c454054050040f0200c3d00e02042103c2152407043c0742c580a034041110002050b20701c4d182c5102100f01c108040748041c4800285054103d404845d140d000758401c6141e80d20000b030780c034414907a080b60715100d1901e040d0100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 336377185 1250 336375935 336375953
    0x11103040305011e0c17070909020c0307060615020a0605150306040323040803030a0b0f09181603020607060c0306080706020703050f0c031504031b0503090a0b0a02072907 75
    0x18243d00d500400c8840740ba800790100b17940201d80c1c914046400c051008803e01000006140c0c040b4051a080b0300e1142e952054408030380c4009042100c9402c009058024080e040c00ba003c024200085040f21400084600070f40352155044000c0c0f5007501c480210306c0b00c0324546001c6003e0440101590340360306251602034a1703242c080800c500024013001682d1200303414101a03500b00d80da1040074610310743d2201958002070001c0e41c10b05522010800c2c0603080398407146540782c807d100b00081d8881c105004031115241c070160010500003810041d9003440161959020789004a512040104250819520940c098020368204d81a14407030204000391480d4006120b03411680200195020006003050035619028100000f5400d6400020301002c0d845071040100d81c0b03d070091074000302240c961800c1b0001001c080800b91010350001c5117890480c5000c2d0b84d254014000361941c103140c4541660082d403130304058412809252240d84081403000001700c030031440c0076122108650340702400c0c5409100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 336378435 1250 336377185 336377201
    0xd0509030d0506010516030c02060d1514091003060f060305031603200d23040603060914061f1209030c05060c211909030e041406150901110304030501 66
    0x1941d0b00340342c0411400e5000c1d03000c41e1151180030110b030365206816103065a00000760a0100d03000031040005100722a0380d4820000c0d400c4800c14070720001890105080c081c01139020100b84101c201106010103410840c54000c2101d074408001b04003451032100290080c42a0303030003e007041c040012400c0c0e1007524241811041403098440c0742d0480b40c86101c056103900400a201041c0c1c2c09220340407a0140a040040e50050f50a11440052018500180e459800c83d40c00440440e880e42018044140716024807034520000c0f2044074814500540050080c10340502001da2040c800841c0710341c4e0034480c03640c2100e01001100705105130800f924004200030a01c8805645500804002c00c50501840e001c5070f48a201c880c0181500c049145404211142c02822103041c410381d89901f03000105175805003410480c02602c80854a20031003040c001078508582c0c1480c1140310030700c00c00005a8881c070010803c1c42150500c50340711103550300180c50040f90750b100c0b020580b00108000080142c15044260 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 336379685 1250 336378435 336378457
    0xe01082a03100f020919050604141c050607140307090302061309090f0209010e0114271003050c01030606090b0a0315030b101d180c060403050303060f0d030c03050f0d050903 76
    0x295041c45807050843e0340d0b201f03004490340a1410007041000e0829503e0903a07161600034443d000300c00b40a4010348000e6042142260560804010030024903040400791018a51840c016881c616251000505040450000074845d000110701d4071403800000701e00c0c6015240b1400c0070003e60145007003621000c244214200e20417100c0c0070021400d26000c3c0501c030b0498a2208803140c05c20303611400c2100303450a15441800a17240c0100b81f4419128140f0b180b40554142c2000800403411800c00c0c604002c600100107041c0340c00c00c902086101d51008041d000c4640c0c130b0410b13641f1454040000c42c05400c1360b64440a0780c6000083c080188507100c42e409004450018007105025038980100810703000b00c04082d182c07031814800090f14081c0d042448410a1502402d40c0e01c0c4010910016409410903001a02d0a40c404000c202050070030700198403441004035002c2d0f9090740300303a070003c0c50319090032401000c1010110321000f8405415040c1d60b00d082c1d200b1014055454034440070303550ba03000b50507511 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 336380935 1250 336379685 336379699
    0x15090106080c01021b06091e03010e0106051804150e03040905011d060621090703140a0c0b0c10020a05090423220503030406060e01082a03100f0209 65
    0x201e407940000c0000c1900c1042e001382400c441054050600c1ca02104680ca0b040002001220520f503203048405c0c0f2140b000c2138040c40304541a02c03c2c103003159086160040c17284e01d0030905004a58940380d10540030b032009501c080ca603684038500301d00c0742640700a41c40046800c01c2c14060038103201101400684074443d41c20071041e0b80c0d410b221052820301d41d01001c012101359000c0f90080c149240141a420104201a108054002680c0c6c200310003c4803a0310151700000d00c02c1c42080b005008880012010304002c000b501c01c00c0d111030f03500d00128862034400090016070410701c1803007884440c403052420b540864035514400809405030744410180d62040d40b43c11208618903000c000000b418004901c3e02c0e103400e540312000094110200c400e03089012095240031000194200011486030b03118040200d0034901e045e6140d0181d07003043c0c001003d00c0d00840c80040d154200390000840710342c55980d40c024520061804a4141740300103000b40007081c01c20998100d0301009030010410303100169080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 336382185 1250 336380935 336380939
    0x40b0f090304050907050d091205030912091c020a0803030703060f060c11010810050a170c1215150303031f050d0312050c0c0a030f0810120b07030e15090106 69
    0x5803240b14074010b0315400000304000c9081701d17104901420303a451440000007401c103407607124007d8200840444800152000042000c2001c040c41000c558500005185040040c03420019800c01c0c1c100e0500b10408445194030070a6503100780141000b007092100303036039a0341480304e0300030041d00e11409509820b6030780d0310001501a20884108203a583c0000e001000e8403000c0004603072003070001d461880701182403d00481c0c03d581c0e01c481c2d10000c001c83c18aa04621481c40c20007810b00030b0010740c0c603218502c2c92481e0000001c3c00f00e181d0b070701268400000c02c3e8a64609000700941c6407203840950f05448080200300c000390002d61400d0700030840c140030380d064a84e0f41c4100301c00801c64980003400a03110b0f84c01e504145205410450704101403c48031803c00d01e400140d60b01e03014124a007640010064401c20764043c0c1c0009246801504008000e0341240c1403807128692008040c81c0101000e03c00c40025041901c01c0d448145268036000c1540e0103034510000166004005442e5a14103500c0d03c0c0300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 336383435 1250 336382185 336382201
    0x30b0f01150e0411090406060507290a0b03010906051608010b0c031206030a0512120703090b040f03030b04050a1e020328060b030103200a0302061b01090b040b0f 71
    0x1030000e4040782c0c0d0740d000c07200c040c1e4014000504074508000ba065501800070303e00310b50f650702403240600900e6441c20b80302c000354200842091501200002490b55200202e442d5035209003030f450b07101940c80c00200d54a2101000302c0d00402061502500302c0340b42c0ba040c8602c0c040c0007103003c080c1d020541d0703a554050362070740204150362042c10300720040c5500800007400b4182140303d1325907102c070b0010151b4407045042d46602d824803001d00c0890b56101d00019584002d00324444000350850f0b26443c00300312803091562030501d508405000a00705420301074005c0304041c46a044110f80d40740150084c840d504005c2540c0d80580080c00c81e00300d5a035481a86190500082e10079280300d125481c4004d4030044003200c0446034200b02252000c4095120b62001c14400b00c0d60000314021841003001040d140c2c8001041301c40190154412441060510000c10142c4d0711034094030440365403020f03081c00354003024071004d0041665040050104004600b00814003440d40170103440b6000c0c014200c5140d9554081c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 336384685 1250 336383435 336383459
    0xd091502010507020d0e0406080a0302070303021605030d0c150e06010f1a041a07061401050a090207030c1101110601030b04110d0c030b0c0f0c07050a090b031b0316030b0f01 76
    0xa03e500103a100c1c40d4007000c11803081201c191521070242c800162a81c90b1450b0b01d05100000909601690007418100209541040070381001408400805c00c0c1c141400002034490034840a5034082051030b400c14010f002400003034840d0040398000c1080505100e5400c039072202404d1080000032044420001449010b80c4a0768072b0b0000b49850161819003407072111001c04d0001c0113940301c51001841140000344403441814640e40c180750202c0071941c54402041000c107038035006070760103e006000d101c0000340c01519091105a1005c58011851800c100486001c44854400e209c01d1090600010910160300c0e0102d004070f020351503030306041d11100240a60464145002070085108000810108425a40264004c00d001c1002480d10014100c00c4000b0341010240c4429034100150400c898500115000c00400384280248240e8416400003500d4690b080117919910955008078070890f5000e0003981d000d0f48119102d09411600d80c10710004002044543d40500b54040d000030902c1d9169007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 336385935 1250 336384685 336384691
    0xa020a0512071e051c1a0303030906012c070e2b0c0618140103110d0b0f03060115110712030c0605150a03121701150305150105070210110d0915020105 66
    0x26510b2101100040302c030500802e00717a01c2ca43c00300181046c4808080c2d6041c0011801055640000c00c40755042444502440c080c1c0c1c1150512400074040c00700410710081030312584100300f8103144811410160200da103440c020140d051400d00c0308050080054000800f0f60300242c000d020301c03c40c807619013005a860750308144912521010042040101158240240f52010010714022644840c203150b0f44003281c0041c130641a001d07880750440200d5050100c03040c42c54100880c01020326500d001500c0c1e9850500085040c10452054508501480108402360050054201440d984102420010801801440c0850b40d1a0a21001c140403d8150004a41c2000001e0194a5040c610b5a41840b40c1c48071012280c10f0200c40b1030301842e84162481114003d003800c546101d00300c1d1848400600300d9000030140030036440d9501e420701c0d072a68400162185140e066411398001c0076642015154042c605500149500c00d9100e03450340203074494041822241c030f00203500c0e08466803070f2003a400d0f14011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 336387185 1250 336385935 336385957
    0x207020303040b0c031c050402131509090201050702090c12150f060714010606080711030301151803060f0b040c03051504180b010305030306010e0d08030a020a0512071e05 75
    0xb400144003003030502e0018441182c903142101d10b06908541a040c44d00b41144890002e070340d4900800c0309500700305145110040380904104524400000d0045948a90f8090660300740d5a503000b410031039000d031040b140140d03002080f00400e1b1818078000512948511324403030900000e6408a003a0701e01221000325013a50003000b00d0b80c1540750206000503500320710001e035901c407804496409400000c3c4540b90150030310b551000e000c2e02e03000e00043d00f10403a103500d4010a520400c010400403103683c540c00030000c1d992038181201c441404000ca03030300b10990405000c252030715a01d413500782c080740d001001c00c00068806004c100c41054003641165000c032204030000c0403003401541c05242580c17012001c182c0c10301c46000503003015214a1000442600204c900b6880001444055a0040030b800c00962041781ca0980e2410b59649245540c00040c06903039217542c0100350202d04902600c103480c0140310ba116004801c2c030b400600102036028415100c0d04020a56002c00e800502c580110f49801c018 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 336388435 1250 336387185 336387187
    0x6040c08190c063509010501120203030412060b060d0608070506030f07030e010213060306090b030a0218060307090903021f0515190801051312052b14070309060e010207020303 77
    0x180c54001d4551840c400603886400714030b4065011540b1240c030355460381481d15264a01c051034080c0b1061b0840350181c0048102c1c525880c0070302c0041c0c2e8000300b04e4065483c4c540c08002ca0314440e00e00000501180b00c44030740d02c1200803c062010100d15401401151136072000c441d012540c460909c03000780300a80c0e0300e001e20001900000c60290007604241c200182e150001498081035400002071507182d90040780010380c44100810622903940150100c00703604901405203060b042d80050401c0b4540c4c820368000082103c005040c1e50740c1403058500510440009104c0005680750003034495414001449400c201c02038204034900b841e200b40c601c01c2c1c5c0e041c0c603090441414001008522103c105034550b145544500105d0789460070300485015a10103810403091142d40d14140707000418824541040280030b00c2080310b2204501402e15450100780150743c0308070700e00300320107010b4841c10040003d041914400d0015036a07266000220f441e00031070301000014001c3d8061800d0380f00b8600c000ccc0d803540c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 336389685 1250 336388435 336388439
    0x906030902010e011805061c060b0406051e0904020414090718270c0201052e05011d040e1c090e0117160b0a0f031e05061206040c08190c 60
    0x400303a800340e400700c040c140b1720403140e540d6107000401590002145800c090344080c080c1407140d449028030b0000c2c1c90788010707603400c05040090040c0f0902960700021a41841d071081010f1280100c0b08551031040090004d40d540d80d11020042060a21080481d01500380000001c4a50b032140b0b840003002c0000c49191640d451409a113100d84a0014030b65611032841c0d02c3e13441d038160b003203803144483d00c8000f43c00200c3c080c0ba00804442d1224a498500700340181e06100d0000014516903a000c140c0d802401c0c0301c40d0b0660181c80039045548940d9065402521b484101451024000380a0703001e100300e070180b03034200e10b0144021502c18060388102503c10b82500018801403003010300320319010701c8650442e00010f48940f48100c4903180c039071004104100003d4103081c0103920100c0c158040d02a41414003149511810100094404210382c0401c6a621f0000c281c0780d5a824412501200d080030858820f41003605180c6400a00b44c886c00300f5510801051840d0000006007041e0b03c0740e0044400c000180c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 336390935 1250 336389685 336389687
    0x11010c0b011a16061a0a0605030c0f04080a0308040b0105120c040908090a030305090901060912020d020111070b1b06090604080c01110a110d050310050d0c09020c0d0906030902010e01 80
    0x540d0201c1d280103007441c28084158a00880540103018a0144c134012404040c0396620000d03150a0034076940c06588400d0051012940100460b0740119850b0107184e42c5664541c60360002c0d01070ba40005a05000301c91400090580c230202140c0120302031603184409903620070400032060840b920a50a44e00000d003010820325280d801205858000c221340d500d4003144100103801d0022642049000c14000b02d88000380d401e020b00d05501400080c14201c0855080011a003012040c14100901c0740401c00d140604591090380742d011521070072011110f40ca0346441c66581c09402403541d405051101040300905014000380c10f40c011125503020340819111a1100d0391144c2c054013000c1c41075900ca0030701489200c51030004003102007040ea0b075800d80075581512036080c01c001c0f800c8881041000d10611441c4101c281c03001c401c9682c1250400c1c03404200f480c5c0b00d028044c980c2c1c40486010f00c0030910300280d20001ca80000b260103a42c0d9501800c82d200c9400380c080383e0b01c100300a0300151660392201065 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 336392185 1250 336390935 336390959
    0x60611100b040603120807140a090b070203070f06090303030b15040b18031207062405060a1103031003050f0105100e04030c24062403020901050409110711010c0b01 72
    0x401c1d0181000c10526101c0d281c0da103003440c1d09681031000076101030130884001d520041c40c0e500203082d03010a61400981d500d00400301d0507140208590000001001c40455070100031900c0148200c0c6080038000f555440040e02c10981488141c0c04030342003035940c000500d080c21700b2040441111180c181018240b01c41c145203500009070004240d030240300c4c414180d583c200001c01c1720003804406199250070710b00c1c0000541e005181601c000c41c40f0715503038010000c01101d0800541d1010799149450704002c040840380501e403403103103007160f020010500454904006004c4280ca005a00300c984000e50706038106e0895900702e4640c0784843c18200180a1802100503107038100f8003038584002500303242d8503100e004283c00c184611a4000c01011002098410b014000c01089110051000341219200b402002504002180100341d400519100f8a0707003c2c00a440240c910020108400e00302c0300728505e02503200754070aa84001441080030141e41c4281e25403221243e21400b20f1f41c4a918009103c004c1e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 336393435 1250 336392185 336392201
    0x281515090b031908120c04090e06180c0102070b21010f080f03030f060607021813060b0109120f02040905030408030c011407120c0207090f0504021003020f0403030f0c0c03140106061110 81
    0x1b000020000055488801e0084200310b2030340b907000d4051410300c0061400e9440001c0041051900107164403410340c0c1c0c02013410003c40d000070b00c100ba03480364141c06418080359604089041c0842450000c210000c801200405403018281107441350b0b42c050044a5036404119548000c20401d200060480e04184014012162003c0c0000c003407071802104040941c3e20071a50640301c00350b000c40100601220b030065988940c82800c2c0422018140251442511031400002e407096840000640454a50398001d100e540e0b084407d60741ca4079100c12100c0d440b907001801c500f035a5070030065806d0f0502c10784003c0c94090622910755114010001ca0000094100d000e11082507020f80c280000701d0300d4440c01205614504040300040524142c41003000010002035007808061040c000880c003449034004450580e074140c02e00c1a101181e20300c04850045810030010500b00d4594800020000178114094009140f0402408100d480d510120b4601e00d042c0300c590a0390b8002240075101101584c00044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 336394685 1250 336393435 336393451
    0x11120c190f120f1e020903070603110d0203070f020d091202040507030e06090d121a0d06020c0307030e0f0f060a0f2003030702281515090b03190812 65
    0x22a06040110308491440c001d0803c150f4464040c080c150110643e810701420391140300310305215002c2c0102e60b032400c040c0107003400c0c959140328001e03001c9004d00c144c07000b80b4450a000d643c0c81c544060700510120f41ca00b00280944110203030548803501400240c8143c0b00c4a25060700319908507001c02c000b408010b0165020305541c0e40c003a5501d04814480c41e441900920014204500c880398000c240c5002c002c0d0007016189408142c00031300f8000c4031050104901203075241c0c50300c0da8608080c002441410b03101c41c214803000800e8801c164019000c401da01e00c0484038800080e40b030f417003407080709a1420300301c650040c0c2c1000500b405c030b40503d9a030481c0120381d20b0a44c1c3d18884500f049541c220328100f2011450b1b002108006545a040010b1010014000b0141ca4807469581c09034803800c1c400c0d40010708042c15580398402c1c60096074849405c040195031442c1619954407005002030030300020f00d80c000d000303000c1c5042400d0034108200c1d040c135501c11881803801140500e0302007104400340801e5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 336395935 1250 336394685 336394697
    0xa09060917040501020f0106050303030c0a0207080d170603030c0c120118080c0f0d020c09060f0613210308040b09030708030c0d3903060911120c190f 66
    0xa0042207240305181410740141e41e00301d0381c5034104800645490414014031005038104a024485518048141d0350080c410140540e01d0700c03507100080c0c0c1003a400f50401c2415105154104001d80e45c0055031a05810000b42600059120070090548a110ba201ca10005520a00d5145240c3c2440f040d03a40184c2030650000600361014080c01341c503980320880558802201054504401c10b040c0504c91400a41c0002070031111714a26000e915aa60303000100d110300c0164001420a841341207a44020f4640100400c1d5184003400382184240071900500c0c01d00440010030500c1c1a881284070b00c040341d0940c4a620040c2c1e5030381d5800c0720900000b028681a404207000f51400030b5402409940513400c075201382a2514401c0003841c0403150b804a1545400f4101049406011212a4011949020681029803298400b10190040d0072103920540955181ca010070704080030080203403250701140d4003400e074a07443d40c41c0e00c44541d0044a029076a0510b01d00d40e0782101500038003203003198080c01c0c1090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 336397185 1250 336395935 336395951
    0xf02210a11070b040b06030c0a030b0c1207031505100509040504060b090c0c0f151f0803160c0f03170703032a08090a03020712050f0a0303060612090203060a0906 71
    0x2400b0342128508407031081c6031805100070812401e503500c1c0c0c861000c0d0000c1420801540000e800f0681d14032010b040324110380040f5503a0702d07032082215601205c170104100c184c14100401001040703e0030203440c403c034040c03001080c41d01d04440c0701c0000c40700b41e40d00d03541050320140800005000c0680200c603915034036214141c3d40d031120764460f40b04492040b0038546520080c030440f802c048039466030610503000040750f84025680d401501760800b8080204101a104420f4014207111880d040203803948008600c40c0d0645039010304072002d19124140283d503240c1e9921f40745484880078000142105004003a115041898601400600c2e0281c50045401c0c12204040300f005034421490000c0184015010100250440440c94026041d840140988200c076280291115001d01036410800ca00380707107480911a0800a26807900401070645d1341d414498079020f030091103076100d0803011844a2100c00e010034818400c4184c0a45c0180c041e1072582e4911002c40c004140315141162120345d6008030f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 336398435 1250 336397185 336397211
    0x180f06140c01060308070b13050d030911030609010204090c030902061608070c03050d0e0f0306070818030c1629090105070609030905030105100f0b0a0314090705040f02210a 76
    0x240400550080c0d10641d654400c13414210071011004025088d554103a02c1758a0004000182420b24400545000204500940350044903818400da040c3d505108101c14010b03645c406600500454070b071181300300002c03084c0b04000d50544404500c080e510131400e110f110b2403a56010718101c3d519214a40d00b071702e40b07911962007003141d020b1a0000d94240e030080d0f440d124001d41000a0350652032048403200803503d500e00c0065900c080040003101003100543c007140420301c24544000d1050052000d0725109c0000d4a20346540f035070011a001d81d4105046000584040c2400b20307480d9001c01c588401002007280d16624129030700010000307041041c2048504041600da01c02d90100c944640d03551010149858109429140045d00802d103110002c601081140000c440f00401c55511014072612250425429002044001740501f00d500c0a1410444929404200203003940c80840e020441c0c0c0c03844007032a0080b8050542e190203ca65940041010000400300301580f015203400c003c81d1880364854 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 336399685 1250 336398435 336398441
    0x23030a03020304030302150f060f04020c0a05030909070f02101104031e0204051b0d090503160f03080a02071e1506060315140108160309050111030403180f06140c01 72
    0x2025801604085420320030581c0c10b025a0341c140c0c0c400d640c407504504120ba042e41e080c0794064010b51044103c210840c2e03058555030107075042030198006440d440642c50416980b81d502076041d1074850003100700026034003802102d0746d0401000c158001c219658150002200400d4041c030700400c100790070710000001601c4c07400352031180d00303001e01c0c4501050a03920500050b22006080407001e521100e40c0c041810380308405452491004a0f00440c202000e806c0090540c4190308240b40d5500d56680750009226020000b51105842030b540c908207503803495851030480c002d4180052001c280a07006001d11401003030705004060282140308509001030910701d0450310301e1350140c4003180d1503c842d07003a004101007a18005141140708400c0044159000920600700141070500302d082034149a00014400e03842000c42c1a4004005c0042070000b0415030000c0e0001c8804400103258240385c3c400c514200c0c1000c00807180b000d407200c2e005c0780c10420305585100d0010003135400004140040004810240 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 336400935 1250 336399685 336399703
    0x7150b1003060603050f0403050a1b0209130507140a090b1c03020c10051309091403032505090330040e0601090803040e13020d02090f15010e0603012303 67
    0x901c0005042c0d207001805025940300506071510001c095007040702098111003110900f10a40c03804071a411b0401c180040d58455600d0040d40202c010402c124140503051064903041d400b8508462249941d02d2040c890008001070385a007090324080e00b00035852a40d04041240c0f2030050684040b90100190a42030b49a4040c061380140e03c0a0645002402d1098516881041c640741541c60207401c409208000d0f5060b11a540c40d9982c5d27030643c41700303002e003000c1c0c80d04c01c1082400a9075500d040a0b0880121420008140044005101c044600301c40c080d10841d0103903100640a000b480b41c0712681403104808203810000600c0b00303403903011504041180108040c0100000e17844090a010000415a6195800c040100e5000308030a1100c00380c0c2c110056840b044102c0000300441d044c0c800b140304103a4445009400c140c215042c4040d8a20808002f481601282d00c00c485509248004640e180c0c0b15500c2da54100008000512101400980008040c0c01c42c5001c10701c00b550010100340b07811001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 336402185 1250 336400935 336400937
    0x21041104050702010c03050c0406050708030901090c090b0102010b09041101030c021606020a1b03051207150c020307060e01020412080c0f060c071208100605090102010b060a091409040807150b10 85
    0xd0074071541d01c46e41511031650094042c040881c01e01c1d05004002c2c00901c40ca02e0041c04100e0007000040300c11009400510502c4d40c80003800c481a503030303010741c02c0c0900a2458128090b5003814055900d50804072013151240c4e4001c45803c0f06842c1983c0154000d1840c03030140310440c0215203041180200041240004000ba64000c05104110342403200c80c1e07107801d2485002070088020100089480055031208030384da07880d04955906c840c0c0c038003c61a880c100f00c1c110702850800d100500043d8020024204541c040d82c02402100103020105080744240d000d02c00092220107169000310341d004000d050711803003160444406005641c1c0c007900d0b002e01103600e187e03003100c0000d2a208004040d012680a644c0070300300038000d410015000142544107025000400c20b0100d41e1240e04d82c030035040316a10312030150110342d5807510040700810440790380c012140400d207072030910162420000c5013188140c1d0058445414909140e550060401060030080581c54035480d0030400c994444603804e0802c0230b9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 336403435 1250 336402185 336402191
    0x11d0307050114070c031b0203010f050106030510030209190204050303030c04030212070e1816150e030604110d05070b21060d32010f1409032104110405070201 70
    0xc40c50300900b507460406860b150b00740514140154150007a141185456150510885980c00c0111141e000d220041d40030750706600b00200502d00c411031b548201c1c10b881e800c2d5001d0141d0f0307482c0c01c0c8454850215210094004c0c84410000381100b4507000300f032004d00032454000d032500c2d69400c0081c0ca1504190381211113200009010011460031210031802c035819100a8242035140c07800c005410a00102243c0e00c0e20b03d40401c040c000340c0280314030000300104d80090106240c0f9000003010306122440c40001041c510080400c40e45000190548070301e034483c0c90b07120741c07a9802003800544402c0e688115014412000040f614201190242180301903000305108118003507404406e418101070b004500070743d54441320b4804541c4a01c41c400784000444c070248010541d820290f0901410b2203840344940d403030b040c0c005807002400e80180c0d0404c2ca845001c16902d40b5601074044c2c40b4843c0c0c07a00c4000c0d03081e00703000c407448008107130102580c131a00540394003142c0124840490166102140d1030070050759 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 336404685 1250 336403435 336403447
    0x3060207062c0309061b0312222003120414010305010b07030804060b19060206090d0201060501020607030905010603060c0c02150f0723030f03040b010819020111011d03 74
    0x10784482070385540c041c01c0c03008451074442c0c802d541d124895591624022500040c05044c6078421942200a80000034120b03660785010030904085104140c81c0341d032021340a01c0b00144d11400444c0f4620310340360050b0801448480c1c604003810352000d01500160940900f1890500f01d04500001d0030003424800c83c85000003000a0004003100c41c143c21210380100d0078410640800e90000441d5032050b4403420002d013070b42c0800c0c00a020a4001000902c0b120500000840d00981c00b2405a000d02005412101410a0340200381e003602c10074011280160f2000d000130700c003680b082d004052080e009500020f1400d0726a2109030941e6a12070612000c5591600f80350114100402d5550940340ba03d840d49041c882c0000d50140d251007040f00160403840c501c2c1c0301545e16942114240040105d80c800c490f0790721860300c04001660800c40c0d040d0356a1f44024000110724030040b82c04030142d1162000c00300d0940050380151006000140703041d00c150340c1d0f400c0040704100104014401d01035800e000b152101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 336405935 1250 336404685 336404711
    0xc050a1509080312070c23010c0201050a0501050d0b0c0409060e150a14120f060429010302030c01050f2205131826032410080705030901060306020706 66
    0x1440350741c42010301e54400c119040401240a55480e0000388900d0130380182a090b04151807c0d0006030f51213503120720751220b85d481004055021001404194000344100d544d01007880080f41c01c00d00c24150000b00309007803900020b948064590303004c840030b512981010340340c0c0e281c0e60444c0c6140c0c00241740010110248104000811001001070108403800160715003404500d02c250f54180505c58082e90f8614103c04d120300742400070074002a00310301101e001e880e0509003403510b94102003564114400c071440c0c00e07400341703205154030707050707d4007e0f0040004080044c011a115408070340c028480b103100380315104030900d03c0701500c4420a44050500078060803d4100710034010040c01c003500c044c0c5041da001071403008681c111070106070009682c41140449541a010084040e06507815211000040004080c038204100b0a601d9400ca81c5904810f154014441104404003c9901044028000543c0303d8403900085501c468100004140e0540e40e9550303005980081004507001a00d41c40540050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 336407185 1250 336405935 336405947
    0xc14010603062a09050423091510030308011401090e090619140a0c030204050928110706050411220c020604020d0b0601050f1c0c0807020c0d0c050a15 66
    0x1102907900d009041ca03c050101a021224920455000c0c5407101a59800350007100100010184084c000c3d00341b614040c0c08081c1c84102075820909404410b0020440369000c0f00d0440c0706880e89509c03148c21507402c00309008100c0810710041c9042050400c400305803090713250300c0940144081e030020001400c0c14a0a034218090100c01c205072a4902558002610122405035810859041c0002000d400c6a40210040c0c4505e4100580111200003885a00d43c620340c91804e4007121440781000364510b0b0324101007030f02d82100d42402c221000380800c101056042c0d2156030014451101068142020f0020031042d0000e401c0c241c1900305030351503040300d22299004844a00f20244050007080c038160340001d14626403c00b01401034504080058403690007081201e415206d0200c40c191100c01c042c0c04910052402052940c08605101040010760b0082c14201d00a18868014224042c44803090100035232590074250b42154850000107895142c00c1c680f44081c004002c0c0295084040510180c19 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 336408435 1250 336407185 336407231
    0x150b0f0309100b1011030c0d0c0618020a031e05010606051218190501180f02040b0d030813020604030206220b07050d030c0210060e0a06050d0809010c1401060306 71
    0x414208000020aa51038510b0610705249604041800140d0850406e1460140540221452143d00d06051841360002d219100715032054006000240408003210801060940c0c020b41040d440241400001d050555072000110303042032922054505440341820759181d070340007602080c070004100180102443d100341d4440c0e08402034030040c058a68403250f8681714604001c07101c6000c03400c8002000700070740001c0e103000b0030016042c0800000d414200002407001c41c00b2881070346081310810540c18140711848009400d91a641259070300d810042141042d0b40204030390044007044040016aa0079026004a40f41248000301d10720703442200224000f9960415210000c003401080c0c00200b0004c1d4089960310303686004100000b1100c0d080c0d1400c07100380c0e400b426060a001021420340c107814074003841030060f8801030050130b640314140021035150041c0504030103010840c541580d4040c58003075415034441c0a0b40421030000032045800c6034101e4104840083d103403115022501d6140c101820 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 336409685 1250 336408435 336408463
    0xa03090b07030f181703100e01080312010e070e1002240411090c0910030902030a05011b030c0507061a0a083009040b0f0a38040306150b0f0309 63
    0x400000680c540845c4400c1c9950302144c0014004002411400803d0903600288004600300816507100c160581e05c94022021403d40e40d8628400040ca10f1404000f03030307009500d84d859070000381d16031005002030300d615003910000f50f00c280f40204900110f0b1034441148000c0c02200756038203003032900c0d200c001040d042070600c3c882c0c04403030140110340f05030508070341068030210303034485010340895002d401034807079007101031740c0340c06445080001d115040d0481411200c80342403241c201e070407a0070160101d9200d4680c5400069042c0541c0001841035448481009201800920381b0740107240019402d4901c3c0d00318407000e40014008890f0a4150f402400701034410002090801c00041c80c0b4202e603014042e08144250384030b0000c1d1400f43c0b21050301c4500c492011b4510502e46494045603102064400c030070481c4461808102640051294028104214060040c601d01851910703a5400380400e00321031003048040020004088104600806600d00c003415440e403640350500b00b4505101c10282029 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 336410935 1250 336409685 336409721
    0x15060405030d08220809010f0f0e12070905010f080c030a1119080f0304030b061807121127010e0307061b0503040602060118020f0a03020a03090b07030f 67
    0x20203169000300300b1644440072803800e800301d5907811042030001341042c180c401442d0107604800701400800c0000f410020020f0700c69030301c001e40c100e00813181c200c0e9000c0c03402d0014404018a070014500400c10308400d0034031004a44056484400c0581250702c00e03400540140c40d006001c00c4803000c00e11580c0b100000c118007801e5403014603150802710384040c0c03e01501c80c0344401c02599030511801c0522014050140c1101d0b4045580b01e60315a89034000d00081d201c00316003d0008140b4540070a2402c0a00c03120b0403898426110240140c80c442001e0542180d045c0d240c1c01c021800650345da0140115941281004a01c917a042003200b6104071a242034904001d00b083e4034000c0b035100040e03c0d60885e040c92030304050014001855114960820b24000c000b03000000d40000c081d0350000d49036040c0e8426a40c00e003410085440308008a00c40e020340009500b82c203008235140b00b030099001d0032000145045c0411b400080b540c0c0c40000c01c1080341e500022907590a2107501c0d00d039091281000800c030b807005075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 336412185 1250 336410935 336410939
    0xb0f06012007033905030c0409050a080a0903050303040b011a031006050a0e1806030106120c05210f06150103110f03041703070503010501180302011e021212150604 72
    0x2240c80320300e60301014001d202c50780b00a0782d0401d1042462104130800c000c44a00d40640d0b1850301c120000d80e071144074400e1007981c2030903d00d03280600c501072425038013134002c109103c141ea861103003a8010111010034070440c0403000001c61070510045100c0ca22a0f80000341545c1000c40303441e5030200b030f004c031496928418420071a40e00124080407069500600740103448802d0340a0403281603400d00420750700b001100c50311a08891140c00c6250141c80100c000788138007a207a00c4c0c011a40b20348403c003e810550444020480781c2010120f425084084800012810038010310359450003040c0307190b0803115880801003040c024008130313840700411000d207000c0c00809a422800d48050103890001d549040c1d0010100d401c004070300803007034644803140c07a1003500c0b07141c980800b8000ba0001d2040a000c103800d55161001c05d00c0200700d040079280d05840b65070381000300700e0030301448403c0c24681ea025481011455900c12000401503c1d00d0000300f081c0a5081c60b0146540380c0c0011518511030081c038042c002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 336413435 1250 336412185 336412247
    0x20303040311101503060606030b01090e07020c120d0e0a15140c120c19020604060509220b030f030f0307050711090a0507180e0703090f0b0f0601 64
    0x1140e400507014901030356401450906035041c0900c0c109910381d00d82c906a2038240b000c3c04180628100ca00884d420400300707958001c01c0e02a90380342410980040c800c00018017583e0410111241c010480e8411112100c00010104000224800c10807905500680a015140d644090420312041d016120145620300d402c080615145221600b201400000582d1140882d40041580c114542c400201c0c4c80d481c1141c0ca0816150744034a001603101c2c05042c0c0030403955a1002118060158084d150320700e0a031520a045610360000120198481021490301c84592005c034544443c0c038000d82c2c0c00080152081d4101468042c0411401c1c0e120b03081400210540401d03001529030021a505227a50740300080c2c5003050010f5241c81c9125403042009051150614041e072050748148072a807540f1070040c10503c2c201c003100c041072080c0300c10320a240000480240c401d4014040b524420503404107105400d580750300448404413020a000c9a8000410140c0e40e0b1180b0b1203502030311004000800c081c0c80d084 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 336414685 1250 336413435 336413437
    0x1090203092a01120e061608090316030309060b13020a0f080f1503030f0418050c0c071e0302090a090512070506011509030b071d0102070b0313020a150c03080a0c0203 73
    0x100e0502c61300d24107a60980c15550400c2d14004075103030680e00f181c82d01809510080091110740d4000401070710001301c81e0600017040310781c40300d03144a403503541c10190f9404030090b000318101215402e44a4100c0b0b0354075207483d00703a041254000b000c05a21040050340040600c84000408001c114105003440920310b60400029009010b282468400c03149400110b440c5106041942c007001d440040c1c000380c110060b1a50004460006030140301c00d03201e0048082c07003030013003000030760340394003c1d14041100c02810021800d0f4a42d241c00d00d138040039600e800165a4420480d20203000f180c130360200b0002c1001c00d1007424030003100464158100311181d02c9030b540d5070700140149068440d00c0070b0103d40300c6000f208044010741d406414104146011a0000e018200c900c002d942003d4812030051590741c00460b500c0280d030b00e070030861070a55954407607140340315240c0c20003a42c11040112007c41e50344861210b4035898000c85d21041507408251038002c040410080002d0f6140d45055002c1c1d56481c1d000c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 336415935 1250 336414685 336414763
    0x5091906020f0405060f04030c120210030c1107081b04270203030f041d0c0c0c0103020906130b1e030103020607020108042310110a021c030e060109020309 68
    0x1480140c8920b0700d240c08070b4051046410040d0301801c080350000381c1100030700040c010b4902ca886480f40a82d611000c4007d0a460f00c0340082d4482003508411003a14801d0f80003001021413842c140048103c6c04044d18244a42c64000c1642d40c0c02052200e08040e04800350030310310400546040043c826005000e901c94240001c03020761030b00058442c0c000b50340e410425500e22400d1100103540d15070751602154921000554030300d149003c40e60000f1428078202c81614580d189d008054074820040e000110300a501c01c0c00d0740c961104091000c1d456080d00390b0f030b44e10083d0000181c11070f07a8007412880700000c00303400c112100f60070344200300600041c0c030342c6800d0700c41a55080c01c002c501ca03190b03450254046050b0521401c3c0e0303045c15851190300e5400c0002c5001100307094060800c2491080c4081d60f041c7d225580c030082c0583d011100841c5030b84c15603000c402c03498019160000c0e01388440410365040183c203a1000d00707010b4020091007441c110500c04465410781c0131388021b81ca0044800078140f540f00d49 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 336417185 1250 336415935 336415943
    0x9030c03070b0a060b031602010e120301090b031005010303200309010203090f01170403020705040c020f0a021011060a050a0f150317210403020609120904021c1509050919 75
    0x518089900c0043c590000340280002c070301901c0c0c80c0d18010524a2080d4400c820303100040d0b0030480c0080301c15001069070041644048202403450f03007440a000080c009004441d038061007183d04805d107038111849840d01031803080d91003084095142c010400c4030036045480c030f00150400c010864003a1380001c11680215410345a00380854070394001a52100d022415880070100c41c4020802095070101700f820a44104a45c208948600503204a0f40d841d80c4901540d510b41c4000e202c000585032040042c810608a85001500d0400700f840c480c1c01c1100a948c0384141544860510940c0040c41c0140b4003802104a0100401c1c02040100034070160340e80720260400131315070340e0a41c4401451084980003c00500000342d81c100c06902242440400c4406600500800303005c80d10f0807001041a403d0341c6100310741c150070000d51404100c0251b012032a03900c0300040c000c1840107a241c0501900245d48240346a003038416103001113410540318003c14481c000c0e04411a10001141d030700003060065600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 336418435 1250 336417185 336417203
    0x20d09080a1104060302060d0c03110c0718021603080601090e160c14120301030204060504092d24050a0c0f0c020a09090b100801140402011b020a0b0403060509030c0307 74
    0x341008540100a01d0b000a50404000514080108401d07042761209051581c3d04110305000c0020740001c60040c2e42203c641130700302120801c6481a00e20f5800c003900c0154000618005c2c1481542d002504209802c03004100302c4000c0003d2580c0100b6114010b04218880301041c0c80c0140b8404888401006d40344284800034130303d842400b91500030b0f0320352000c3c1c01007100c0aa2084e6544000517810900c0101d2103a401d00d00041003a08040c003c0391001d55020310b00ca4000307182c6035a420540300b01d0309220a0003002e980e043c40c010400d50141c1c202c032002001c0c18a44060401440302d07007a200d000b07001a0f109800c1054000c2440e50050501000b28030500d81503001c0d003610b02c001a454482c03031f40400c8156041c90300140c1408583c0240901a40e901c01c040c02d4800c1d9138482081c00d0b100141c1c4007031030f420940c5000034095406210680001c0c12002d8154040184950024400001c04d1b041040c15a40c0880c0c240204000c7c0c0c820b1542181a0724002c50404641410542e43c9115608004200d552 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 336419685 1250 336418435 336418463
    0x30f080414060106031d0309010801270c03020a1b03020c01050a0c0501060e09070905070507080f12011e0f150f090801110d3206010e060c0607020d09080a 68
    0x7051201e805049425500369101569a104002c001e81030301d8580007020403071451b4004060300000f0803038074000c80684418200b6880d001103100381c00b00050000e01d07030f40061205112031220324071555201e03040c59100142c5600800d140140313264414005000340c034503400010f4002c41e800085880d2400340c2444e00565412000e03100700d40801a400740280b00f9030911202255883c120361030300d072007112001c0882d0b43e5a503a0717469200c10345a040c1d0710000410300400407540880c444000030156034242c554524500041995009119142680401100c1440007405485500b00e00e01442c020000c0301d00707210080f820040e60100c501480d881070410702c80401410000a4044c2011000a0805c0c00c000c00070410401e03103244c01c603803100108803075003498a94075107821031426481041003c0b62544124510040c0c070000c1c80341640140010b030510903041c80c0d16410350f075103600a05203950800040c181ca424090400780c40d0a21040c408024800010021701ca00c0400203040d1150607007050000034469 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 336420935 1250 336419685 336419693
    0xc010507270e090f030d0c0f02060f070509010c150c1d210c090f0403080c04060c11120706050403060c0804051009020d150c020610061b02040f0624020307030f0804 72
    0x141024462099010105800c15044610b61003a05031f00300c1c6894076401e000741c0540403a20769208a42695000c001d22021880315881070001d032002d2401810600706c001d140da11041c40b8021003210b060000da0b155548103100f140e01c01902000d0750185d81e006840f42c40b003400080c11080b02c05003030350755264807a410310024076000c010b180900c140150200310340b820a0960050703400c004440550102e03040a0119003401c00c1d01040342c1c01c5466903a00c0c90328503110380e52203d10001603461215481071000b1b100c48031007401031229400071720040d254550b41e1441e5180c003a044c2e50035008140f051104010802c40890300211b40b042441d4103122000030704002d240b00203542d6130050740c406030654814069120f00ea0042d9400b41e500d0021640803035100d0341e03039005042e610036540e000d143d00084101c0c083e032000039842402c2103070340740c8000c10105e140c440506541d411642d55a20200962282c006004502d010300b10891032001c403688081c5241a25a17100a4034035129100340504000d901c50024040c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 336422185 1250 336420935 336420943
    0x818040f0c0906210507021b031b1908070f050301110903151902190e0919020a0201021225090f0312050712030e0c030a02130509030403080c010507270e09 68
    0x100311304090400003800c100c10000e44e40c1c10742100e00a07000b15001d1825060b8034000440714460040d0800300d0070300d9190103083c44800c403100d409489142c024803002007511581401001e0180c40103048004003503280c1020103095a50000095200c110b003008141000c0d01d000c074007600540310120412809072a0548910441d01c20f0346022480700e80702240601c009200a100104492840e80e0354220018904080080103082924003e02c081c4480d402c00c00010400e402410f190302e0f00f0b000060905440514a0000d1441240c8144030880342c0b05544021105003086030b420b61115140c02c2800a042298039401044c281c0809040301c0d0860001124051290080b642d80e903502201c4420302d6805e9010140c0503000039803844105004441606c040c80c2000280750002c550010101c0e5012101100c00c4001800c4c09407020700980002c02020000c036800711f0003000c180c0c240c500000707150f280010001307010800a91001880320a610380d000d020301c00c4842c1400540b010305c141c042030798490b04c1c555894 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 336423435 1250 336422185 336422237
    0xf18010210020403030806040b12071419080a0209070809030403020d02060904090b01081b130209011b03170f010501050a0e03010605130203010e010e10030605060d0818040f0c0906 79
    0x1c1240006004010142d00108042c0141d0083e00d041c0f1000d01a60204030400300111400031040c3d00c000c408000000000c20200f2895001401c0e401004e401c51030068042d60a9800110030381e40904030070011810100403140e406422441e1040302428000105922031056110207032007424444001010b40d80c4001c2120b071002c4005200f005401c0d4949800c41940200748202003c13030040d900c80742c1009880180c402040c0d00d004021504c00c1290030034140080d001803040e2410003554000210f001c0d042c1e4001c506c000c501a44842c8d051744402d00100e0400c2400610a038003481d06200100f1043c0d0f002b0040e1268840c103030418048080c842c2e0040383c0140aaa40280d80c456604294400400703442d0740114140c9894140e1032046a03290440b808075040151101103130f00c080e91804101040080e4006500103000070403039200901340e0303280c0c02d010b42c0000810040c20030116500d6129450319128000300c07901200b20034400d4210030f4001902c2000381c0d2040070140f0280101c500e280c0f04100401c0d0032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 336424685 1250 336423435 336423463
    0x1e040506011401021518011d07030602030405010b0607050a0c1505030408030a150621050f010b070507051e0405090a030906121107110306010b07020307150507050a03020d0e060f180102 81
    0x85280b40000d180b290481b01c0c806021841e52812881410b204100c03034024966000c0c1d10014001d01e891036aa100c000d61008206032030a543c0d4101303d0301256914402000035074003440040020010a080c8010b1020701c0c0da020348801c103009202002d080e504030064a0b4455041403400d038032661041d070100050103580d10503121200303503444085500c5800000c40038452440d42c4109919122840d070600c200d5506554802000c4448030040084800d644010003200303204005588540c1c0e614004500030400d150501c0c18410390085030040a4100341c820941d0008440000f40b816280c240c6000d440410b407400384400b0000078074651404620305030410b08088411b10401941c41b451801d10400b0309d0104804039100740111000010360182007401e4031011031300240030b4021035140240000d0090010314200c1c2c1071210030b00420703021440a00203002d03418000c0d000b03040419401c03000208404080c1c05000d104a50601009482807104416100f912001c07003403001459002d000141c0c0340030210300c00c480b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 336425935 1250 336424685 336424723
    0x7021908030108010e0115290d0b0f040b0d0b070309020d0c080c01050a05270d050601320f06120a0c140f030a1e0c02061e04050601140102 61
    0x6040200d854000c6048400c000005c00803002c0074600c0320709903131a90130b0582d440d00c2d0149050006021003020101c0705150080080b04200e031865a10060740c00040e0803640d20fa9851100d181e0900b0810381c00103103111300711020000c0440700d4002681c20503500c14050250460040040e0321107001c0c0c2d1251101a40080148100c0ca2261608688280060040b0703041c1c0e02a810039640c0c69401641994070400702900d0b1241881d624140c41c080e03008414000c0c1419802c9014907606070b46803840149030190048018006540c18007201140c80300c030310000c044500403407075000a00064010a0508041030842e01c045410f0314001c00652240100c520b585080c040b0700c0c1c18000398441640c04030143c8075035074440c00041c01181510700454090076450320190541080061084083c81d440039145003400c55441d01c054086008800c211000700403100c0160388110144600c402da840b41004007861150004100d40c502130340c6041c0c4500043c03080c00c5035055009a848d43c1030b8001e100e0410102c0ca115480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 336427185 1250 336425935 336425983
    0x30708070c06020f12181603030c1104090f021f17040507030b0f04060e0c09010b280f020c0f031509031903090b0603070b0301061101090f0503071703060a0504050702 73
    0x481d0a4001501c441070117003480c1c1b103038000401020400c0042c954040851600fa1455a1407da61844000d50220380640c4072240c100070350b80d11807080038070142c0500b29203c1c0c894000e00c14460b1807006550540925421418820300e415402141080700c086030780c100280c0c41d159440e101d860302170140c000134500380300041080b02d01000545000e10441c000d010034001d10480782e96850b1268000480070343c01490301e00c010302c40c00c1e00e07100c0284031007000c42006e41510580006410320703541d0f50740801c0b00003070310303c0321300c40116070b030402020303a40310300490301100341c241c5100c0040ea440d003401000e8080c07818401d0000740751070824015681d54051580402503c1c0d49400b5000b0005d080c1110111071404180b40400c1407401e00003107407010b485142c1416480c690a0000c207079130401a00c000c90645640320b1900c40001800c0e0034000448502c01d100441d2260701a14158815030040100904400b809004101d40d5944601c0c02d50202d1f801510005080d0725540402c81c2080c0c1c40603450904242441d0003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 336428435 1250 336427185 336427207
    0xc080105150c330f09101d0a0c0f060e2413180509011b03110423010206010b190302031509040c080c030304080a020f030708190215030708070c06020f 66
    0xa00b00201c02e0103c05201c0c01e03a52074072100c01030b01040e107080580d0303403043d40b00340c55502c0e640d440400101404128102a294603066561410000d0401280c0d4400b44030020040c40c1810341031400030740315508144007210341c59401b00d402455440c0c444102e01c04d49580801e101510383c0c0864900b0400d140a51006584805103120204000a41b481b1030b40d16000c002000c000c411300c120b41e10b50700600c1e000040e02100034000c5000e0003404446603080b2408200002c0ca001c1d40e40d0300c0390000c42102d904500200c080364000390825505034004841a602041506001e11090707002c00c0d41202503050058a83d182d05100b211804801c42d01c180e04000040144401e011310f0403401400c46031100211103424001c5001c2c540c5038060b6200f60b8905501c211050001403411389030080100c100501200d03075140c2d071045010302c0c200e5074803440442800c2c102160001c0d4100381040946001c02c03840c10a1942c18114802001400c000309444104041480104204502030b01110101070011202c261242c6100ea1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 336429685 1250 336428435 336428503
    0x6030c0c030a0504150801060c170904020711090708040807080307030912050904050a0e0714040902040204030b0103030f0507030e0405090c0303031006031404030503070c0309030c030c06030c080105150c 89
    0xa000d00f5000c00c0c5c42101c031014481c60030b0fa8103039042c9070795114a04d081c0e540c0d43c504105003088000b00940091146065688840c4080c0070564080c0454520000c01c0c80203000e40d80f84007400702410448035002b00000b04265400702d5540a80c0000040e07038a035529036084005180700f401c010114030041001e04004c0754020050082d66800704c80801c6a9200c001a00044428942002540750041038003005030b001030154200c68079002130000b0440d1803496000030220391290704100c80004c1020018014140d000182000024480c10400e20380b202d10785015010701d40015803a4807440d1a400000c5191406102a0002d0740d800750890780c403401c00318807102c0c41c1d05960150321b00217440c00300098228840038000c2401181c0680300c0c1465034131450412102d00d480e4500a805002042100100180030b0402c490011801603010baa152802c2006c028152986402e107201005880700c014800c0795540c02d8a8591901e81901056039072664078030046c20426156002c1c240e10300c00b080301c9000241da00c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 336430935 1250 336429685 336429689
    0x60a0c030c091a0d231b090a050d0201110a0b1603090b060d0813030804090b09090607390c0f03030c020108180f01150609030f0206030c0c030a0504 65
    0x9101481016032003482102c0c0110b6a1142d4503031007803c1075101d103001c0314510060120b00c1d079518002ca546041a85140c2000900c0214076080c80700380020000d00e4190101c00c800203501d082060f610380016400000e15031403c0c0e0044a10640454100d5811603001c0c04002c0713401302c407050035980324101a0926a103109001c0750a000c080240809041c0460b1103480b508030756903800820071810b6200e2405105203110251001c8810100070001d1900854070180d00f400154072480d41c850392103080c070342414140c0e2000d03030031180200a5078042c00b0040101003070690b401902ea00d450b1001011811080c072800381c0400c020014018400c0042003000440c41111180c03a000f12001c51000e95607555a02540ba258400a40000d62424080300150b00c500b0451b03822041450558203004024000b83c0c1c10311414624080c2030b03a40d203440c19a840110004050000d101e94107041e4002c0e451a00d402c1098040010024468500000041e40c518990b4082d00c0103110f150040366141c002090300030340300b58058 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 336432185 1250 336430935 336430937
    0x6040f18120e0a03020618030309060409050a0b0909060a050415020d05011721070312050703022109030403060222060206070305090d09091805010c05040911070201051902010608060a0c 81
    0x70008442c5041c0840140122130f0b02070800f034a0217404200c0513140c860000b060384e0b03150104000184c80c6070703200000f03000078142892001409090603110300d000c6980b07004a240c06450300d1820024103150206600307610010b500f00210740c50f503503854000c0c0690700490f80f101c2090b02c0410700001d2240c00784d0016059400101011021000303201c4690354030301d440008601121a90101c038070500110b040981046440b034241041405205203012068030002c4a4010000e0b90100e80110204c0d03621005840308002460820500e08045800d5a140d1196001c00b40940350002801d24103112000d0b59181c1d251000ca54901c0504c2e11808002d49070b64094504c000000e007864042904601c0c003082154400da80c03a00c0340000c05191829101c01740082c91125101c038100c0300a06004644280209112140103586d0240d880e07003006a41c0c2e0407a01c00c003c4240e03086109120800050360004c0848641c00300080f04103000e40007620089014158941200c030281c01158188071011506400446144607a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 336433435 1250 336432185 336432197
    0x121315060303200d0c0804030b18061807061803060204060e010f0305070e120a0c08030d11090d2301020408030a030606080f06041e090503041509030b06040f1812 71
    0x4000e0070011030312003032030030f03801030740c00120500b02014054614890014818042c80b41059603d840c2c800c425141126041d84500424000440d800e41c1804042e40c0081c500b08042c0703031b42030080c0c1090b54428140c000c032010700c40132603440c50342003c940108000442e440320046d590389031222001800c01c1d01000b001408038003603000c03e0270000c0c000c0c0a4684203001c56550300c806154100f0070068140c0d04020b400c000c50042c800080046290004d803036000e0302411005654510a0741025002c0341c814000d0421404c000b0b2003515096a00c8400c1d50144a4100990441a289000d844040c403044005419003135031000500052030407000c80903103100f03081038070200002660742c00e05032004041100d108024055000c002429442d040d80000f480e00c01840d007103c5001c040300122401c807000c045099407240e01c045010012014083c00d0040145d07054030b003540ea40e51450b5115040c40001802262186031030b00c81000d104881c84c0d01480ba030460760104070b0181c0c545800c1c42404440d60b02d01003000030b42 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 336434685 1250 336433435 336433457
    0x1d0415090f11042909090405010e06011211040b0301112b02030708060111010209030106061e0203120115020c0907170c09030c1905060a020d020709090206121315060303 74
    0x8602d0603503045030841c980002c00c5000d0001c41030f11004680d05104a004001c0c41141c5454483c1040c1d1440b8a01c524000642c2e440804885403800074168402c1d4007400c1c403481d003080081c10034101851000e03000e03500400d04403100d50009000d41ba00b8200c4003805240894100780350151032aa440e003000b445100e1103da05402100c035010f0f0300c012281c00011800010100350395520540d51a03c44655440c001030628182e040004d080d180c0035401b180014588650859001c43d900030903c0f00030465000951400700030384c01d22442408144600080d00160303c8011807030900030302501818030310060840c0c0b4546071001c40602104003401c5001100281000042c0300f41080320708680c80008001c0017020500801401c1100c511101d58842410080351007000604ad1244805041c0c41c0ca00d0350007808c0304150080000b840c0540d40d46c04500541d0900c0150340c0503841e01c40446680c40340e004000c0241c1e6840349020b0005010050006192005d11020009441815402030080d0307803080d40c40544001e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 336435935 1250 336434685 336434711
    0x40908090303190f020c1e0d0b010b0406030e03031308220e19050103051902060412030f080708061f17090d030c0201060b0f13080a060c030506030d1d0415090f 70
    0xa0842240940005541d000d15004c59510011fa15640300018204100f5034207a548000c910300007a84420104103001c5014001039805026074100c00b402880203608519140300741c2406c070b03401000054400720340090040e95024840018188811007071040c0c142043c3c2d1802400c06001d0304440f0400f028510250011000180f8019a03040381d402000800340115000104411241221800c0fa40800700b00400a4030303410b00c0811072074403802a1600e110340e0b480c480e000350010000500c01e00400403250100880d6540e0042040c3d403002d10030f401007803010fa58034030541d0045a40040105581103400030003030f0b804030000751480e00750310955080c0410481514184e00340c500d5405176981c590340034400503408070362030301c0036113104110355a00203160707a580c521041c00c0031404035040d01d4250b15a1520b06140f038260160642200c821380c001c100d842e90040b001060500302c00e040c500e90b054041100ca80070368a54114032140d40c060907070044429070302c0c07080400602e815131051100c1424030258003114 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 336437185 1250 336435935 336435943
    0x501050f0d05010e010f1e06081f14090f090a030c03050403020405190c110c130603080301090b031605030303063f01050703050907030803070c21022109040908090303190f02 76
    0x4414101612621981002070541b881600107000c2b050080e5007010202d00d200c3e19465220007071640344940404050201e082c40070300340c401044403104441c920240598400700191810780e507501450550822400c520f81180c6910443c0d00c040d5020341040144803282e00c01c412080812840c203402001044102201958a642d1080c00115560014200c840481c1051100410342d850401d00008170319031203544520943d0020b810025101d0b607039aa0031211810200700d09001c52403a140400703004c0d0300e804000782c0e90b4840100114090904a1054160041d0080c4107641400100e129200031070200341c82e0304400c0c119211022032940c01c20000c01c2020703009201e01343c02000ca01003d000303c242191540e4000d0760000d0002c40800c004080c2220210300c108032001c1c0c1080079414850740c0c541c403655000746064100e02d03444640d18418810320001002c03070ba00320381c11410306450100c0c004131641051612409019180c0d40c06020004800105d40c6021103900060000340e1144941000542030883e60b07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 336438435 1250 336437185 336437219
    0x14091e0f1c0206030a09050303070c1707080d1a040c030228020c01081e070f021501050a05120a14070303020d0c031d060d090302030c010c080408040501050f0d05010e010f 75
    0x10110604071540c094180440195845030017000042000086a56007030314551044817850002280c802141c1e082000303800090101c034000700c40307150401c48107490b00e120030322903900c4040080d5504c200d044000303448945a021290401041000741c085400030180c040c0d80709190694004041c1d5403240c0325a1609180c0080001072940180121200d000040d910210054010030700a240c14104405540b031145800d841100d1603510190300006c1c0d007002900d80400c114244848100e018018422619403421080841c0c6046402c01d122a4401442900300008503101500340c0c1ea103903042303200c201400200c142c1100d00c21342c22500214404a802c0310000c0001a0080008041000039803a6076800b040c02c22140c40010601450180c40380c0d0302400301e84d9002c13811000b503000403a41d070340c0a18083c81011031211080c00c00700075602d4540d85144052042d806440e0500001046000e020310540707040e50301e400d40c0305001308025611900c15480c030380024820007404036542e010119080c0d06643c15032003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 336439685 1250 336438435 336438469
    0x60e0406080706111606020d090902160206090117010f030b010b0a0c03030902040b0910061202040b120c160b012111090606090a26010204120314091e0f 67
    0xb0180341040e908440100d040c0d04030818a1048002e0140c04c080300c0e46100c1c00400180d00102011100050090403200c0160320904102c6d1060040303402180d1040000400e050b41141c0c2c1035a50f240c040c00503075a100c2c94403034030352101c0380d144008100044040c8055040d6400754480c040705071b0341c03400e0071001d5100d00d042d070700005a4400904000640a50070100e8201e100900101e080f500c0000070800c11802200c1800c400c07958400104102908044000c03a00c00140c0780c15803516091400c80340c1e051059410192846043c000060741c2d180f050000c1e204418003156100c40501130b82e0606c0150f110082c0511201812024039955440d82006145001240d000403040ca5481c080d40400c080140d0003407001b0380042d0200070000daa541c0710300740762001c0c00c03c0c2441540c0e11004045403000a184908080000f03a00c10801403080880c00c514424955515180c00002110030f0102c3c05410b01650825940180070441000e0ac3e0080940c0340100010003503813808400f0310b94100300440207400d4140c0003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 336440935 1250 336439685 336439693
    0x50c040303030f110304030305070306060f0c02120304120c031b0e060405040c090509011a090705030c0c010608032113170d090203150601021e100506040f0501030606060e040608 78
    0x30020b4020340040c64182000b040001c0c4151824940c41400e0380115000c400081e030765810080300c542c062080101810251511742c001345d46d8040e0160900d140b190300a8850004128550a00c440400c00c9401500700c040100080781110300c1c1450030008540811150b4024441a02c40032a00307480780c0208941015200c002c4903284c84007031100400006e0410b0305c0f59017011001080d482100d010b07041c00394120b400000342105039100c00d5100d02d07111403812413241c0d8a0200f07010165500100350b0350451000381340b00b80d8816040740c05c907005100c1a0302402c10340c000411480c00100e1113071510007801c010221440301a03540c100c8007140306140b0000090103040341d0401c11501c1c02c010800303840041c00c03410001404051b1500001c0c0f07003496070007005007840035a0b402c11005507418441d26485580c0780100303901250100241c4e6480c2c1124036001030101d640d490010b011559039402625068004020400003941c5030708107080030b00014080e41001c208580d40862142c03e15110781701c120ba03a884050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 336442185 1250 336440935 336440939
    0x90102030403140f060411040606230a11070605030f0f06100809070506031602150f0402040b1c060f050606040f0308181e0916020c19090f05150301050c04 68
    0x1100f81c9482d0400c100d48030321007800c914010104410360055000d400080c4258401c10200001d0750351030381107134007004840310100310200c1c8480c1c41300b41c00f86500c1c0700083d109c05011008a40b40408140b914020744213282c000030380581c1210080d4094103200c4c40403102652070454215031540d0a40c0ca00781c10901c1a0040c40703a1a10943c3d2680c2c00030010381c151003200c2c0d500c0f800a08903030020340342c20402440c643c03d40c401c0300d1b4040103103405040d009183c002242c07038860341c1003800403401040640030316128203c804941e603840d001e481070b400c909104034008c2d00f01c0f420828010036801080b544910b00e000c0200b142442c060085d601218182c101402c2c00900356580d0343c01d550441c900e101d41c0b030140041400c5041da500c20710107410f01016413040c24542c040004014003201d01030595108481d003030b010940071030341c003042401e502c0340c0035036650103404505610070841005542c00301007054030300380402010580c5508050300500040360210302d0006204101402c039034054401e130002100400003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 336443435 1250 336442185 336442193
    0x1f0903180303410408010e010504021f140a12110903030706020f07050f10060b04030206030c09010c02030d020a0b09010c05160503040504052d010803090103020d0e0d090302100302090102030403 85
    0x1030040c1156004103000c810051425942c5040c2c01c0e180b004210b043c0d01090501c0f0803502441240003024513000240010300b01a0041100d22503680894941e20180b203607039101c120f000740700300e940712035030000603030b40d0744001180c018000344029815825071420101034200341130502060340c0750100028051807070034882e956000000d51120044502d180e505012600115005000c0400100c1150000d0702000a404145104982940c0c118840d13010060000788007580b01d490a4a238400a450720305a50f80180e5030040e00c02c9810f40d00029814820301000c04202d43c2d0201e1001a154401c402c0c0030318948410720304d98280c500034184d0314002103081c000c500900c1003900000c010507009006581ca020b80351800b2030262441190481070b000039408001e9000c010b903085940c1c0380f070b42c3d030250741340d0301d504000700d081e03c0f4803c0031401c81c101900030030001c0c01e1401950100040c46040002c13512100d003a00c00140c000806071000f03078420000b000c1c0c1c0a00e000d0180c02120b0038114140d0107145042d0844c2c1d0b03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 336444685 1250 336443435 336443477
    0x11406180d0b1e010f05011d04091b060c05030316090305030307020303010e06030d091505210628030320030a030b0a060e0102030f0c1f0903180303 65
    0x601a40542014008503686541d03803000c6030240120300e00344040c0b40446040001c6001610b0340302064001c0c4004200081c081c204070003d40300300b440d042c4c3c40c0d0428030030165160a81340d0105a0301c2840c003c4004d08000d030340d1444080d0b0700c5050b600305071240d41e50340c0190341038850000301070f00f950000c20006150b00b02410804e250042d43c1d0074510300b520348a44602c0e1850b0000c4030030f4800750b400040188002000700d4801d50307010030110000d01d40c2d08003010000385a01c6952088102c5102c1c3c04040880035070080040d00d90740c20b00031100b43c0000c159005070494544090b2100d502400d21002c482024180e400791490304e207020050740020052459508982c400c3c445445901c41c5048055070900c604000d000a19600400390341c08500300c800b8a080080f41940385e4061018080d54258240e003e98010095600140c080030f00e00d40c85034504d189450600010a1040e84440244120b2542803640c1e9840804070034041d607980301c400c40d0242c06002841307001c3d00000d4049034440b140b204400900c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 336445935 1250 336444685 336444697
    0x30702070b0c0102130b0301243507080402101b02040903081f060207050d080c01092906010c410f030a05040302060a020f070b07050c0306011406 64
    0x12044400281c0e564040c0a03041d081007407403005603500000c1c11182c20102003248409001c49494084c6154588016809502500e00c070038854004070790034205926004030100d02d58a00d0781c5100744080c0801c043c00c5031010715260300b641c09a40114000c1a041842403112a01c01d5901900b1058030404842f41920581482c42c40c59241e4041840303c0c40043c3c42d6400380d1682d4920a032100c84250404480c0d03005015025583c4955800c140c000800c0010390000c0c158040380d1041d1030160b4410158200340940d031059116840140d82007805c0c10341041981403c08800b1880348005000203043c400f24207503003070340036120b00c0e0000d0000c14400c3c0c04100c0400a803400005003902d440c1085500300340131070420081c544629000c00e41006a43c0c0c03c418148500010401070402443c900104444050700500031400080e00442c004900390042074002c000b5801d000740c01ca41250030303060791200c1080e0281d10200049507203010b429004e1045040024029040e58800300e448600e943c004018446650005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 336447185 1250 336445935 336445937
    0x207020a06080a0f1e0507030b0102101a06070b060109060207030201050d021b010603123b0627010e030c0901050f0a210c060f0206010608151e04060506120103080307 73
    0x180f589455504c02d91054007401c61018102d1700103105581e1700601203d00c020b01e06170a06090482800d680c5c0e034041901d20700c0e03011043d03002070302000c8180320340b8611380c1d08104079070055000a083c070148800c030b002203407082109076585401c40d602e88078101d855045d5803000a02144092119210000d5550080c0c260011114030031914600100389107800c0d00c00b07a61040d640d4000d85040905074950102803031002d91a0300203141e4003084050022180001210860558403108150740c21483d81d03007604450000d81410300c4141c0e1950000703001c8000001800005000ca01600348002c490306010078640900e080040000c0301c543e107001d0a110343c86008669181d07011314240d60101d403600d455101c7c00305040461240180a140a203000042000542c000105020700003000c1801c040d4001441419143c203407a244c40c4503241c1c80742e000481028880b1032580030158907400300d01c10980c1482d000040c00122400c0c45115550b4051000710b1203503c0d044023802000d1801440401c0c6184010b40d00000f071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 336448435 1250 336447185 336447191
    0xf040312030b0612100b04141018030b15010f050d050c160302062403060a1e06030326190216080304080d1b05031302030c060a03060e0a0207020a06080a 67
    0x100b0310000d00180d2014555409030a000c1c014444a00c83e40a030301030143c5454005980342c00d09242c40002c0d50203003901e850703200c1e2800d03d2503005000e106424a01c10041900801500e2607120310705180002d07000c480d002c1e0a141a428241074030f610030300710030300c0c6004183c494070720b0000b03004a020090100140713a1755203000c003042000500c3c220f200140308d940707002e58058207842c2068000c44890114100304405c00320481240d1290550700481d0203034120101d0308002540070f23040329510751070910280d054031364540351440001c14150061000c2c06030001b034202c0034000d00c400a005000e0f990042c1c0d606905491742c0104181034141c10350086c01e001c051840428000a07841e56165219070044508480c802d03008034180003410b03024000c41e0821000c0301c00d000040c2c070703059074010320f5400010400140092151030400c1036480910507055031300006000c0d29503449030040080c002d00780d00c0c400d541d2800805070005040d20440d01c00e50300e48903030060411071028581041228041005404800e207580e17 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 336449685 1250 336448435 336448451
    0x60f040c0915030b1309050303060d1505100302190f0b070201050f04080705030f030a0e01030b0409050615010f0201050c0417030f030a091101020c0906090a09020607150e030f04031203 81
    0x11000114112039000c954000c00c1301c1080c00b0510000314500e00c007050760350341090600e80000d4008001c0d02d40c410000d55031118000011f0810003403080b100c00419034050b01d45024000640d0b0208006010307280250307071070300d540c0410040d80c202481c260710503080841968a02881080303103a000801c02e050052400c1c90524030190444810341e80a540f0102940d40107800070841404c091020284101789400a0340c10001c40c4400900b40800c010803041c1019641c0310000e40c3ea5860f940000c880075003080c101d0b9540c3c07900c10041440501140d641c6800304189004c40c034040c3d441401074070f104042004a05003094506541c001c8121140140d18182d4002403100003001c00864000d148901c40c1c0c03020115145d6510304118202c0138620703038201d0440d040300e00469401d469000086802c95001d807802c1c034041d81d0b0500650700600602000940c0a14006800c2090002803420001c0221441d801080100704605c101da54901c900808410591018801003001c9440d22180c040703070446a080c0410300c81 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 336450935 1250 336449685 336449699
    0xf01030b06030a0b10050a0806060a09080a120305010816030210112506080702032209090f0209010518070c0303090206030f07080903030106020a020409060b3006060f040c09 76
    0x241088500c1c01000c2c4c1d80320301d0b00001d0314000c5501a0407500b28144689840c035005c000030b01014005050074020f417800511182c1d410310580e8124000c1c07207404140c03009441c00c0c0c60807600c504000140340c0c00080c20280082441c0c01d02085a003038045030541c81c8032015107558203010b01d0000d54000403060000070348039070740c0700102486661444041040b960a84070040a50781c421001c0c180c10940400c0490820000b0494002049a9141c007508205840300381c001e9400190342401f54202d903800c10b0408250400308501c2071440c00d01d06200710790b1011141c0c0c0782d40610a070790688030032900d81d00b40808042241075000c1d11100451500900d000300e001d54454010810701c1c1c0c0252501403007008000304200c0e0321644440002e4026400c40701840c235552400170000d503110140c0b04082c3c450f0741c0e200309140400a49a0102c15114400382204070740e40322481140041b01740035180d60301600d0340d130911100b55900214909203d07031801080d003005400220280002841c410f4056800e00c106c01c24042000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 336452185 1250 336450935 336450937
    0xf0e06070f0326040201140705120415030e0604031403091515040f0903120e1608070501020f03040506071514040c14031203010e07050708040b040e180a020f01030b06 73
    0x15010f5200c1007555505000004030144640f0400d040d1400002d090000603a44000310059964429020b55290038290601e617040a41401c214030141e01c1c00240000d4081c0c1c1c2e10034140c280d1210391400c0050131119000c854a640c0f084400600180200603074001c0c0c07850b200003554201140d1002c0b03903814a94000e550201e203100342c51380b00680d02c100e2000b00080c501030080481c0d481b29000144036810301a50f015007481f956601206000c0c0c5c90b05640c041030301d400c102031000d0020034120750300d41c1c0d9075501c00981c561406000d59801402000084808000c000040b07034101c0c1e80144c00309180070b600c2d480308a030400c452504411190f40b00c01c030503a5200c0c51046031600860103a400c0c3c020051404414800d006007240c0403e0190b00031a02103043d0300110810f5030f04407050307110b54210344c1e038440b50101c0f49071081403002050044003140100381021004040c00941300d030306840a007940c584540e050b1a59815040b82c804650103080c0480060030410724885500906050100324541c00c80006112 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 336453435 1250 336452185 336452213
    0x150610021c05071103030a0f08060102010b04150e0f0c0f09040207050604031716020a08070f0c09060305010c0c02060d0c03020d1109040c0302030606070f020102120a030e0c01050405010f0e0607 85
    0x1540071898400340702c2142507130b424500f001c50056240004000c000b40054140c0c8108005201e034910004245074002e4100010840c40144100b045040404102e03d5503042e07030143c00a1380e00d50f103002447d13546e404040310740101a00f030184c6040c40a01807544010f6400001c5079a0001d409000610010b01c1c00c02c91640241c3c426129901262080760105841400c0113000c40d051640c0c0301004030303410b60003140c96078400342c00c003003525590401420402c600d0300c8003400c001c20300c0c207032441c000560004035801a01540e10910080c07040740480d88044070f00120308000650b02c20420400c2d201c0060140d072000780c8500b1a402d0250504209404010071908840c42e42e00c07610900084101442c030300703841207a00c0b50820341811805d41c04c1990103d030305401510002804090240356181c29a80200401880d04a030040c0306661a049504002c1c05089102070200c0c1070b00c260440029190300030001e480c240d89041c0e49525110800b25070465800c0d2400b030300d490304514108003c0300403880c2000070230780c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 336454685 1250 336453435 336453437
    0x6061511100204051003020c01090c0305060702160b030f10050405010602010b0f060a17180a11010e100f3209010f05070209040f0201110106091508150610021c 70
    0x202040380c0104560400c0682040428034601c10841800aa81c5050f01250000010325005880300c81c40d06006005241000000d802007280e45000070400074001758052082c1c41c0d980c01c0d251001c880da840f8042c0d040d45030080c520796070700600010b85040f048500c1160300c6884d802103070b15156076880210f001c448084e0003110050751219502d0006080442e180141c40805031045445c01c04542c0b0020302c1d19900c80344080d807100249002c03074410010510030b08101450340090b140c0744503061030412031002010b996070b80811050074020300d2500c1e040130700c5254901079884081c001d45412200302e403582c4000b0f50440d810030f65a0480701410062044050341010024803140d650100b039800580100f5406c2003503c108001044080d006807250000c6680090340032144078600b003643d10040c0c484080e11075040c5807940c40d1020018000301035030090324a81002121660800b9103404c039194840b03000ca01d50b0300440360401c000c91803c0c00c05c1603415540c0203580c4155000d0340551002d07480d15544082480c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 336455935 1250 336454685 336454697
    0x1e0c030f2414030c040903050d1a0a080c10030b01231305030706050409020a0509040e0615060a091406071a010503010c03091a070339020a020319060615 67
    0x14881d0001d9410010142c041007921101100400c000241c1d18602a00c0003405a901c03074001e081014001c40c01e42d10b0740200c1c000140b0a4810010404007049178809445110315201070f00041c03031300408280b03000344010140c094441d000144000b64003a1590389601030401c181d1110b10154058090012510b114520b0710255030340346d4441c0c29003444211078001c14400d41104508001302030700b2008a5007190707400c1d5400b5803142c144a90968803070203500003140d0007904064031504405000300304507202d4000420001c221200b1501030112602400c06c040c0b000c141052010b10030f450520186050b001001001145803d5265480c1000700003008a106245d0070994018403252800b801a0300b00e42e202032500700700c1c5505d0790702e4014049501491001c41c44945201040503d4030a400131101c11503420a146201c0000114144108901c0110319800b4850b09a00b10b07440352001c10500300300354005001b89414104007030350300c01c5024178110443d0969554000080c079541e2992a09419403510340b584 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 336457185 1250 336455935 336455981
    0x1008070e0f0d05060a0c0f091a0d020c15090601060e1203040504110406090b03040f0b090715020c15030903040b03071e030614090415020901050706110304151e0c030f 73
    0xc401540c03506c1c1420030611105200c2010b482d54044840c0044070501c3c40d4030949250a0702441d41240700780d8840c1c4031658000110711000140001e081204c200416145c01d034240d549441d003540b640340c21b0207000e00060301c00300420300c545841d1a1002ca641c81e000c0580385403654420024080f942c400c40c43c040c14803800320301000321603006404440101130700310740c076891450281c0c0d404a10400c0b400c40180510720b541c002c11150302d0100002c20140280c0381d02d84e207a01000102c00b0b5511211902800d02ca840f5200204009a1280d0301f07590040303500c40001c60a007400d1503071081c03298200400400403c10800c40e10490b400c000c10412082d4116510300045042c100050120b5840a124120b4082e1a100707040c0400241c400080d00c416001d05280181c894903078800484e514406c1c03d601414050078082c1084d003032500d80d0002c6010381e2191803002140e82c0300b80080000c1e02c581205801c2e13060442c4120034201d2455400001090100b13140028840600303d441c5c1c400c55584186045030ba200040034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 336458435 1250 336457185 336457201
    0x3070c030203072907061418010609020f0d0903050d050406021902061e090f060f0702060919060902010c0b15120703050606120109081b0c1008070e0f0d0506 69
    0x20007009400b007108201c08410110880c4211a000b681040d400c2044c00940141800780c1c5602208108451400014036810f0403645100007031b501c0c00c0e501e5030a518000c0c000966400c0c0c0e200b02e4582c40d0544100c141025482c420b95001420503420540130b2244c01c024010030301183d0310507039108906c107900040e1220081802c1c07091000b4094107a109651202d0b003800103102c0110001c100c02d00302c64000020b0f6a68400c151410f003100001e022049101e403c05210004170302184051003011030f6400c0b2525540c07504d901540c0e580306c0315030403c00395400c840c000c40410141d03005810b00da80181000c030140c03015a51040d5100804440f0b446041505002110041c60324088800c0000c001c0c1c00140300083c15501c5280d00c030b00000e03009600c20304545000c01340014080d006440202d800507a0540c664034450f21800014500300380404250040744050070b114a402c4030f00307514001035981d400704580d8403200309444520341c1c100f82d9944541c040d4440030450b0b83c0c100100d5845885200a05194180480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 336459685 1250 336458435 336458443
    0x60e06070f080c031e07050c0d0c0b0c0a120b21010b01121505040216080703170f0708130c0302130b0906040b0102122214090a0c080109020f040803070c030203 70
    0x30240482c1e180800511074080703a100e003411130307001741d00e18001281c1e103581c0c8042c1c6041c41901c4a03007882d03009000c642c14506030000f40c081c0c901405102901815a40c881c02c000c0b15104038200e04000c9a8101800c807000520f9078041c900741c4001400006004419070700884210b00e101360014200e0391660aa00180c0d42c2c80a0305840c00301d0080c0b010301401000110100d1481d0716809294000c9a022404000c041014800340c14072a4110010903610029410010f0803a0400e40c043e0b0500005000480e00c00300030405072901c10b800d256284029615801c81805c003086030000b00f9514803030792100c0400543d64800c202449190b42c1c1d040040c85407007900c248500e00c00f00500c814441c0d490050489490798012a4100c8158a4841480d036602c0e800d107064820034406481c12010051074800c003159001c280d080c00c00c0c0381101121040713070a0355102140c1d02500c030b6484410000a0205004002509098014001103002d215645041c19200d108003460f5400001c0241c038140d503c00c0040042d070900f44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 336460935 1250 336459685 336459691
    0x2010c0306050f010e01020111040816120804170c090a051006020c0901060c0215070302010f0f0911120307080c031e1213020f130b0f030127060e06070f08 68
    0xc102400702a10b00800200110b880c842000c1c148104464001d200340e10139404050002408000541ca854841d03a90f1540c4042a0414210305100b69401003203026055000074034495100300748515241c01c0600c4809a1941c01d110342c5030718403400540348125a81c91460505c108a01c1d48009918a00510701c6181c445041e4024070640d00403203403500e01600e0b00214981507619500b010301000450384049002e4000496102101e242d020504c1820150b06402200c018040840c083c0002040c5011010446039071340c000070034054420f0002680c50034a516070032501c0205009503424031150351162006680321200950b2250030005018140c54085691400d840c1c02181f032950404001561501c078a0700080c066190540b5131011040865a49420000301070502403c00620600e52443c903c0c060700c02103072400c0c0300f6114a4000c24681c241445801032120100c1d04a228500e00154002d1034240b0114007500e8084e2907a910f03c2d4465410801e03107000e4072484d56002e102244d402c0000b46075141c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 336462185 1250 336460935 336460937
    0x603061e110708030a0513080a0201060303080a0e0a0b04050313030c0e010603060305032d1c0f0c020a110310050106050d0e0d0c11010903150905070503010507021e010905070e0702010c 81
    0x24044200458243c2c016603900c50359003440080c45884000385446049040d042c0140885800140e8003030a9506402100c01c607442a1544902c5480b04058002a140701e052180c43c5079000881000c0840c54010401e90070500800a80f03140604805100c02220b2103900292440400b0120400c021202e2607142801068145420440d1a04581c0e6981c1c8900c40d441c280e061211311000d020b00240c8440002d40b459401c0328081541d2290b6058007180043e40601007202528541441b04114021300d00451000d4041d42e4041c0460326040c1d580c0d9582c060604001641510403000741c041c001c40741e482868060002034840c1500d0383c400041d028140d0366014550130702030b00208581390445401c4140c01c51407030342c004035111082e0a503400403242200700b548054800b01403020841400d03c51a8410755415001d04280c82c001600c1d6024182a50001d03240b40f001a8007080b400e10381c003103407800641c412015090001c6200c011070b0725000e01c0c064280e0003241c01542d4400034400d6094091041e01940003031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 336463435 1250 336462185 336462187
    0x80c0a08010519050316080d0c11010f0909060e040524070503061315050109050d02130216050f010209010912030e0411040906030807140a080315040603061e11 70
    0x21510000341140c0040c0b15980c092609118080e8a02c4407102c00c00001d040060308484215964000d2001c486901d403103188254060703407040f134040300e115400200c4003507044000c00007070b105400011a4100210192082017000000f004211107025024100c01440140c0780c40305942460f061442c10545400d60402c7c9283d000d428581e1110840c0f0f4005a1080311401d00036220ba407000e000c562800d03101821107a0710351400403405c8144549101e03c10031f590080c0d885490b01900e07041806400303031824001952042e9114451103540e12150020141c41707803503011a24551545540351448e202606030311a07400c2e500800c1442080d68840c0030a002031001e480b00310501581901c000d0880c1e080a520140516100e400c010905800764003158020919544200300c1643e0340e05003c803c981010008843c044a008040f900500f4002401859142c12061240c5075480300712101001a00302040650020707191900080400e5881c07007802403800301c07020050381241d0070b0400d00701115483e40307015041c0c3c10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 336464685 1250 336463435 336463447
    0xe0901060b361207080c0307061e2604021f080a320108150601051b01060506070602030f0108011a1309020d0309030c05040501060c0f02010905061603080c 68
    0x840e200180420b0181c030000500a03520840744074240c010414105030004100000b0300c802d01c9001601200f01d8140000383e60400c0e0407802016119500c5100349400108220449a80c0318041055028440c80506103560b850701c4c405610604046100740d01c0d480341c40080208015424040e00023800105803c100705519028000003030000b201c045c2c400400103540e801c2d81070f8049500c3d85d40c0102c0296144003051150501c1040c07403260303c001d00a0442d107010b820354820148042c150081d00804051711610700b00240b1098503010841250101e02e021364841200003215141c0300c0040c074816000380c03005170b901e243c4074070900790401d01030340a000790742c0c50982124040d20b226a0038403c0b592003286e0500240c000510224054a0580006507100d00110008002c258022840d68222841038001040c03141d580c2080000b118800d1080340c01040310344007500700054450a4299039140b05061800c41d098540740458a190400320040d1000400c50328140141074002c0429548291044480c6181203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 336465935 1250 336464685 336464707
    0x50604030824090c0d0914011e0209030a03050f04030c06030902011b0809060c010902040e061e0108120304031e03060f080601030f020919020703120507020a020315061201060e0901060b 81
    0xc000e044e40029140410000d0300c60714282c1100030203507001a0301280007001c01803c1402012012041e030010648600c5080c500d8020707000b82c6000000003405045d80c010540c13416665503004402c01c3d403015000304001710004143e90000c101a102c141d5000414440c1c03880003400c0e00d801a4980501014007040311070001d0500e1003101c03004d84055a105d915081c030074801901618880d40001d50250038a01c0581c90003038000b8845c0e125184040a40b40001143c54801c1c254030020301500000340c00c000302842030701c10103000641c2c21611a180c501d001c070a500445028000300c0c8100440080e450301d8040143c2c1e588a81d517035002d081d600000e01010b500d103540340a105100c2c0c5800030300070890803000134621429010460441241000c01355502c012501e001400c070309191020a0b040c501e0440031544607480007036611096507000e130050002840b8055081200c071030046c945070f0300c403046500000ca000e40c2030007000000d0003507807503840c820b0500c06401c90a41e0701c07940245400b03110901c044a420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 336467185 1250 336465935 336465949
    0xd05150a05040516050f07020612041e0302071e031e02103b030a0b0f010f05010c0b04050f0304030503180619030234030e010302030907050108090a050604030824 71
    0x4e415418261395401a140282c5005e00078940003079403242c0c010944c0805070520b510540e10403031086260f103003131a806401c24424a01140c4019005a108134000c2c00500c034881c51580e01540480c503000c50ba9592a5129a5103d059000409404458582410071401e22141d082070107451420f2511181e0b9140c1c0101c00021485410302d42d02220400084084681c00901d10480d2a4040c0a4030481030250524058149043d00d89400c1021440b00003e2240d2000b0084c1080d07400c160b4a4541c02c000075102c5a0302c40c407010b042901e0703078002c1c1d001681090104100400046200f48060342d185d0110700e641416076440c05600d940214010000d204511042000d40f407410b981c9403e0042c5c5403125400e158065021303040503010180001141003060f03000c031900b01d00c41103103e59600120100058011003d80c0001e82c0c1e071105a5001c0e00c400c0c421036005050a40e48580b141c412103003007048940710307640f90810a0341d00354041a11082403019038096695020410140d5440003143c40c040d6001007100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 336468435 1250 336467185 336467221
    0x20f060a020a0f260414090606090909120a0e0102070f1d0a020c0a15180201230c0d090609080a0804090506010e030d05180420090102030d05150a050405 67
    0xb0f00b8a00c41034400b0000c0026031507a080441c0c089595040540301590245a400360144c2d80e070380d00c80092410b50b20301e0700c240d913079100e141d0161105082803103040600c850102c01520030217490217944408907142c030031403015200000640e80c400b40110740705000a41071110f2500710380c4101c201e03503000b03101c003640d01c9110318203515611401c04071a80d50420740030003e010b8a001c010550149820003001e00066004c13200b80114446400c00c500c062048000d1560030403500020302040ca14420007000c012603600003c1d007004840d4a50f840c040c142c07820036062100710054940801c8200c141402000d9000304141c028042c0300c030060003102510749a000785801144100c002c0142c4402c00660039902c920101000b010001d411905145035400002e8044c0c1c004d4400d105420f03220081140c0a4038250081180c2c03501c00708100c41d8402c1d02c0e904204030562104804506510007042040313000d402a00c0380c1449180304101e00001200756000700f000f140e5003a400300703200d24145001e01802000120700482 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 336469685 1250 336468435 336468443
    0x16140c0f2103040f020f0a030b0c07020909010c0e011202070804030f140d02062a0c070e06010c15020c070b040909020915010e0d0c0f03030504080715050406080a0605040203010b07020f060a020a 85
    0xf800e15800000400ca0000c64000509c49e0300004140180702c12044d02400ca124804c490584131603440f091040c0c00ca8030032640000006400c413640f51601d500458011150038060720303000d07250846548502600c0c1d03100d54001c5900c0c1652840540c248a8000032441e4a065900702a20401d202810000e5a81d00041c2c0403100340e11000e9407011705031070b960000300108510407480588602c4400c144c1d0341ca52181c3e21812780805081c0c2c0011703070309600c9001008080b039440a184466145608079042c000d40000042c00620307ca03001020541d05109070180004100e071010115851a0902c10b00c40950130243c9a0020508003130b03080041b582c0c006a8211030071105458a000c203c42500700b20301c0140182c0c1c014000c0700266900802810390080041003901c0041080b40d0940da560340100072000c01d19615000095801e0105108480c4507074880e641001d8000e8000c113403140c490700010200d80c8280d00c800705415002541d5402c50506010410003104112440c038103240d8400006512141d442000030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 336470935 1250 336469685 336469699
    0x70807180b04060e0901020703021b010909150e160210021608030403030906021303050c0a08031c2d05070c052e0c03060302150316140c0f2103040f02 66
    0x688540b5240d22500c01080d290000e80500e0030325841150003540440e0095006006510100e0280405000040400c3d0f4040c0e41e8004030515002c6440000d00c05001a5846008140700000c2c21040070756171140165a4452004282410481c0291401448170703600c040d8280140060241c1d0380c1c070400381100c1590482056036482d80e036442c00b10008c0102c450300404891001c50360101c40110340c054201501c1c411021144030413440390801ca4454880d00c01c050f042e9004000e01102c5202e25282035035a46414000428544a00c80d02000d08452600c005210420f040c000e074008811240501600480d807030508540080107610f4181d1502c68800d2540e407000800c0406482d040da01c1514801400d03034544041142d204d82c4034004029140302d12059100351201102d00c07400b9184001180d008000401750f225000614010a56081c00000390b001d00601003403100c007009110500980400e40d40a4001d411080b03042040e80ca015082c0d80c01c0028010400d10410002401c1e5103203208007030b50125024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 336472185 1250 336470935 336470951
    0x42d03032105041b08070b030c0703261e060109380304030e01021c1805030a0507061b0302030304060f0605180115030c020c0904140118020307080718 66
    0x700007402000a03082124600003c03c41031001c04410104d0100305032401d042620b075202c108969609960288180d0030008001041441c002d00c03006120061081c24050251000102d40755444206101e9205260344a030781001004041c0000c4500003101c1c0e107940b031805007040400245000310354000d10424854000c802008080b240305680c070349074200c2c08140300503d000206a2082d030016601100403954150306000158004201a8130700044500c20f500c070300f0001c50b021108040c1c616024000b244029030082480d4405100812085020b44000c0c00d032076140c5003004210007050301c2c6144591004218101c0066070100480742c0254100e007020070b0491900ca602002071209501c05a8442c618101c04003411220107a00b6040f60075800481140d011180c4050f401d076210360000c3c10050f00f1458200026151844980c0e4010b402140c442c0d09000700400941d0848000b4074104080c07401729000e1104600c2c0403c0340c207000d090042d01400070745150203a15081350350750440c4050034035118541 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 336473435 1250 336472185 336472217
    0x3060112080715110a020a0203070902070f0f15050703050906100503070608090c1206191a060a021c0207320111010b040609020315180c0a090306090503042d0303 71
    0x40000c142400c130342c0340c80c2d85400040d0040c1d81c1f40380c4100200d019001e1644005400c0e2524426a207100d500105480407039141942c0342240d601030309808845442c80c04443e00c80c0d82e400351003070510841140d20000b846041210300315140413801440340c035800801c240140515100841e02c2002c60f0070714240180c1c00c0d1640210107007001010314060f0b40000141c0c0548150000009055004020031491010308411807110031094407408007103c440041c080c00c8110650070010002c211140007441900c030110b404003d00310360000c011007400c0041c1d010304401d00c0106110703040e42d00700b50000c0490f0444400180c285c1d48449880e42c00050501a14000080005100390450081c141000b8002c21285031651a401c0003900b003541e0507100342e01950900c102d107080030004101e41c00c002003000c1c865550703612065800d039130286881e0070800110000010006ea224010b692030b032441800519119404c000100780e02940040b0350340306c03031405110102d03c1d4007003101540c0156a014941191030300d40e100c134 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 336474685 1250 336473435 336473441
    0xf130b03011803051308070b0f030405011d1c110d0e03030f04080106090b0f010207180902031207060506011b03180e070801140a0810090f0203120903060112080715 72
    0x1840320b0300c0d801e0003007000301095031000090207000390b013031550001c25441d140031941c2c2c3c00b003d00541c106980d0800c80d183c091a02c1d40c0c06540d02900c02c100100d0000c1d840010512403044000b501601c5074818020482031120012144140d1003c2e841d1440c1d2510518074142d03a212003043c424814440c60660060050301c00b402102c1442d5902c410040e9560307500d03005a030090226109446c0310b50300d00300000c281d52038079400c1c03e0510307a016802040340b0f03824143c502400c041409405543c0d20741d500400b0700140c9051000440c9202201c0d1841d032152094280300c0141e0320020b12150400140659070320768051017002c86241d058040c941913400c00205498004040026040400201c0111082050b09544106200d040c2c0304402d003800e100d040d0880078400711400701d0040c125942c1010904c071403100e182d03070b12000e005801590400c2645440ba004070381440307228005491280c1001030300b48402c1c14108542c0d40182540c3d80a20070600c06900c0d000d102e8001d8101c000d0140d42c0f202c50840c1a42e001d50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 336475935 1250 336474685 336474701
    0x9060f0712030501170604110102010f0603080705060c07080403060902010c0804090519020c07060302070602091f0806030a02010c1209030c1401090e07020c101211040905060f130b0301 81
    0x29520503035400441c101180142807031901e40c0000381c141000450100011407941151642000040a96441c1e40e82e9015032150400c2d48141159610b02d1141c940c10440d000740402140610030440c2e82c2c800320300b090340c18400c0090a2560070941008050001200c0c0421079045942004000542e100984012941090600c0000d46200c5c008140401c280030f0545c407540c0203803a034590450188038401d40240c242d0050b0301d005d038401d8100380c030104146030080e001042c40c20310807840145407294000c00501d10181c0c202c1c40c41001c1100403c401580d5030001d940c25007042d001ca000307040f10f0900d0380c0000d00380c898200008003503011040e8000c0e09035000b03070401c00184cc1c4c002d00d010703c2e46403940841c1555160f05100c00d0f00040300102c0025a46000401c19400780c1026805130100e0f480401c1800403254001760098100714101915003161100c0c1d1240b100d100c4828101d040c0e07503038582642102a180c02034a864403542c01c0c035040006503a5038488000a05060b448049044509c030f400082c0113101031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 336477185 1250 336475935 336475957
    0x1b071109010311030c040504030f20010606031b020316080726031501090e040807150c09050424061803080c010c08010609060807140d02070c03050105060103021e0906 73
    0x820000b1003048080502d1074550780c0140e08440c102c1d1545c408100581e40156400750203e09041101041a032050b542003100d40c0c0c21000c07015000c0c40303042d5150b08580e9994044400280e448d222175010b07840750015061888507500c000d50030098560f201d08400406140002c114500000395101006904a020141c0a03d28480c0000480401d0f62104040c8e00488207080900011040208158012040c110035103c001118403a5542c455840140c250b0151070261007404043d8601e0036880a10302800a1062055136400821454482400241c403001070708100c00c0382100004031407144140ca200403c8400720b1078030038030419142001e9801c6104581015004000004107800030f02415000203500c81001d41c1d400307040c1e80c0daa00c0c04807000c0059008100000d110040894020f80c440d00c0b44030b41c81c0000d0103c4500c0c110501c0301500881e4030001040f01c480c2e241403020400d0003030a201e1030750300c0325007800c0c103520300b41d10204c9184502c814204108190000800c1c0d01150352941c0702036500c54001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 336478435 1250 336477185 336477199
    0x40f06030c09031401050426030114181003020306010b031909021203040f050a0503010507090303110106050a0602241314071d01030b090705010507030f020c0a2c1b0711 74
    0xd004c0c0c0d024082c000c11142070741c40e4100c7c100d0100c400c00e009034198550314108101e450440e401c0c4400008041103038442e01c7e5110034203074040340148040800c2c06000e1280c1d050840f10705841c0d803040c1803c00c0d205a202002410f014010460015542581445c549034016000500340c2e400744001034980007042100035140c400400c011544110b40d0030118161581141d40e10307941d542c1c840070142aa0811158a80050200031080000078015080ca04000040344008589a92613a01254000c031a030383c801001680301c80c0408203090085e020607415150031140d111240d01c0c2410310b5040309640508001c3c03140d40803600364010743c030040c00984003905440c004011100858071140000b40800e010507510750640c1404601204800a49481110b2040c0c46031401e0807c16107007a615500444503200940c007544c0016001035440e01143d1340644641c1102081d4607075444021119094900480c00d60034481009100e04c203013094401d070044804c00c4070041c1d80c442c003910b0030084820700e042441d500041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 336479685 1250 336478435 336478463
    0x10915080709020d0510060c031407150606031802030d0e1522080123041a0703050a15080c09310303050702210a020f0a05030307030506010203040f06030c0903 70
    0xc2d50341c000340504a407010040c8000c1c1c0398030b10101a80b120300c1c0700704008528070000c40c80c00280100c07003039103880310f1002040d41020485e03110b0f83d0903804031030041440642d8a240c140500c41d0035208905d0340c010070710800580351110ba80403a07651480200304000344440c01c1501d00301c91b600c0e40200308440f08000f288035101d401064004414110700c5000e86000c082e08030021904e42e0052040402c0084902c1071203000c810400281481610060300580d0000080c2d4100c00a0010b2804014010302e41a03a00241c54942884001e0813146003020080d90b80035080d4040108020014002c00b443d03408480d66070580d2119411071139601e8004a0071140d46c01400a407a01040451481d81c0301d050181d2424041517403507072402ca80390780401e0356041745032880845452211443c1ca014091840c0c0c14011184003100da81c070800d01d0310b03901c8041200d46074000410003d10b1581030080d541c000c6001e0004504140c20319001400110440c0190002c165545e185c0181003407203904280020f40d040701024040b46 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 336480935 1250 336479685 336479699
    0x90f06020c0c041416051c0c030905030304050a11150d1109100221040b030406092a1802030103020108130c030f1a010605040503030403060209061b0718050f0109150807 74
    0x101200c0184140081400c0c904051b409003086803100d0045090a484182903203a10744000d0940b0f1408204150303485440000041d0200021406a0b00400040c06a81c88902d059105008424515402060180f0400c9400412142580c4a0b02030145011500800c885191402e60007a607289690200d41045c1e0441c49a80118094003100188803040c480806110f20009080c890751149508241c810400100450301662207583c40f5071040100001c400b800342c0a602e484285507426800d180f80d0000200100d40500600c441c01103811002507046603d56000039000305001049080f80f40b100e010150304200030903603481c0280d903214400c5071680d0554101410110f503034001840c0b98103001000440c0703082c0590162021500020011840c1a045548900c00794010f420f170203400440034000c24001c82e08550010104c0b10064004000d0301e07190074070710340c1d1109c2024180100305280209000c00314608011150540d00b50100c08504c0b40ca1a07640da00700080264003082c000d0241034008030780c0c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 336482185 1250 336480935 336480971
    0x20306060f0f0a1103040e0601200d12060503010501050906090a0b03150403230405101103161505070c0807051906050106170903120910020d0b0a0603090f06020c0c04 73
    0x58203095407090608000d113442c981d56072050b409440c0c2005140d07000503455600c00c04500b403160b1006010307041050130b00c8580394138002944001001081c7c0304034882c40c0d0341e541407207140001d1204400030301c0b0303551620010070480300c000b130540c6000b801200d001030b00d100183d030021101d41d00060100e82114210896070b4505840603642140043c4240103100c1d0a201010b041e41c0c00c3c0a85258602d1a0600e080c081000da01c20008410003400707400100090002402d002409186c03941c0c80000f00000c126203042c4402030000307811015102d14040038040c0740c60703008101803169a0301c411100d59848550901d280f9011b130780540d03012403400d61940c140c104140f58018604803030940d200c0c00d80014501c0044086048115600304460380144803413284414590000358000f803000d815600c0104241c000d8005a0780000440c1c2803154a0300d00801c1642031003102c4a00500c442c0c40e041050440990b142c5103003010f070400150136540c007c42d049146c054144404852010000d00410214005c080f6810310 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 336483435 1250 336482185 336482197
    0x3040305010c080f040506070e041d030301030c27201b0f030a0c020d020a03050a05010e0c1e100306050a3b010608100306020301080f060604020c0d03020306060f0f 72
    0x70f00c6800460412407591601502507940240600202d0b07685103000c40310101c2c52045030741d0258603601007540504041000c05420810700c00515602c8d030450070040010f80031540041c00c10910400185048041381462401141003988040341018080c4001d05003101c80c10070760401600c000610f000c6d1410b8003036152585466602c103032046403801084e00ca40306c1c02040e03155400f00d41071050810051070100b42e0003003142d03c000e0540c0715054890b240d051501d09015402c441c5607541d038290319030501c01041080a1800103c800c2c8400d50030280a00007103900500506028122440c001c0b624a1b0094101da4090b11000e094940d01c2940d8403c5d8042d4805000720010a4a4910000000c0301400d1903c0400441d20360030346581503403800c4800c940b415001400d4419000e1034420100002d070440c00250300130132680005001043d480d5400740c0c10a82c0180045111f14410494620f01d42c9000c5000d503003000b21030400681300d58858000c150184120300e9001c542003000550007190340010710240a07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 336484685 1250 336483435 336483437
    0xc0604110301021c0e0c1504060e0a0b030106020607092301080915070306030201090b03060105030c0a02010912172a090a03050a080c1e0c0609030c040510140102011509050601090803040305010c 85
    0x516801b80c442440b994140100070100f203000f00300002d2007003d00596200390500c1020b000120165034400750300b06d040c0c20a0300010010780040c82030204140d401300d01c1c0c10107801030002c03154420a8080c1445c0485000409490603c45001c0003d00c3c0c200b014040c80b1911500440c049100e440c01c0c0038024014880f500081380814211140418200045016a8811701043e11070a00c5d5488000e500c0101342c05c0905180210742d07c41e079142c03000400014909004840340d80320b801c4c500626121100118600500c902710340100c032101c0c00240c2c109004404a90351401c8903117982c402c040000702c0c0044506800141103171051440e0f01040000c214010704180840f101900c4408a103849464043d0355900001d102c0780e4803804403c41c585c42d282d00103001402c8000c00301c80005400001003410740758110307807044c44003040c610708120f40382d007091104c066880248005c115148a10142c00c88941c41401030640d074690341d400240407070b4050410000070f84014000c0320b88607a924541741d8080c2186e207400f28 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 336485935 1250 336484685 336484693
    0x180601060f030f201303050307080301090b090f0a0b03120f0307020f0706050d0506130e010507030509011104030b0903161b090e030d0507090b0d09060b0102030c0604110301021c0e 79
    0x140441c211846148040c0c0d40280442450030640003040286030450003d0100301c0c17128040000000e42c0420061040b917104000740c58403580b5103142c2d5004c498a60140038041c0c884601000401c510500c9202c2e0711108815000600c085443d012a181500403900d20381c0003940041c001c2010342d000700c017452190345c09500311840490385071110390300c4450134800c401c0850824007402c004114142c20042d840303000901411802c12590044000b41c03124000c480d00e86954a005115249515006446d40600c201740280003a01c8428888140c2d8800c2d4400a0321000380a0040f0304c00d0301090040b40c5c4d416a56180141004d401410040800c88442c00303030700c048021030301c0002480300490007222140703046003000c0c5042582454040c400350100502c2c0301d0400000c01808210315411101401c058404800d000403200d6507450100119410708003403c0c107660090002d40c15005000901070b03030051344848a15058450f807800309019000342c0d92009120311608440181c013200c582e122501c4101494116 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 336487185 1250 336485935 336485951
    0x918060c0f080c0a030f0204060e1f05040308030907030b0c03010905011a0d020c0c0301060b12101a0d091e1a10140a120f0c1d060405180601060f03 65
    0x25150300e008031040c400803401e0030340061003207080280138000540c5030b401c010444002400000d0101d84c002d4000c00701055526802ca0001c2c1440d43d01d402d0440d80c1002d041c075446c0c3c0f07100400f419a0256210003070080c000000052107510083c00440c00459000d580d0341000d0400d060741c810b61350400d000c0d09164501e013030000201c80803205002083c940c14034040906d04240d2071440d8010307504c11084890341d480741c920410f909480c24400c11004040f0807100c10388410b40008038941580024007a0b480c40d004505051004120010442d54a407441c1214180e8546403903804401810243e20090710b9030b0b8002e0182c00c5444941000a040d5512900180480040442074592003690035140c2d4202040407403000d100800e42a60800c0859500034102c01c0a10340c3d54412559000c4402022241136520458110400c00100141800342c080401410201c5407465007266a040b0010038841c40380341c580d8041000c0d42c805424000035002c1d0a01520308568548402400e20014030400c840001d10f01065 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 336488435 1250 336487185 336487187
    0x15031c090312050906070633140a081507090909050303041a07090905090316050d020708031903051003021f020607020f070308090a080f07140603070206060d0c0918060c 74
    0x111118013400400d542d0a0400989440e070042840070700950850020308140300035101c2c642142c201070700e603d41350030390082e09162a241c40e00d040078503a10702803400540c00344039814003c604010b0000c003820304001305544111085a8085003a8401c4000c3c502e402c0e00c0764144400480110300c41e90250b201c031003c40b5202a035030b104182040301c041d000122651414081a4907a801040d0440c400b0760807603090810382202c1804201c54254121219070042604414417501804a41c0082200f60041c0d400e1580700c81554104400c0520b40c4010590b854000074603a403203008070321010b150083c1141207070841c58140604c180f402441c403580036106000000b007442d4400207a4030030302500e2a015081542c03459849a039141c200302c816a512400c4400301152582040042442c4440e00c03600801d0040e1030903034011035030041d107803a1500aa4081080200c040e800040694001c3d10030345200c00c1000d600e003410000100c0503000a01464280250084941c0030390b4850580326010390701c100000505240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 336489685 1250 336488435 336488437
    0x10c030b010929041d0406051608040312061206091b0b04061202090301020c1b0102010908040611070302120705010e0414040b041a2508010b0315031c09031205 70
    0x4a8107810f40c4040b0207180403000c400c4050039800e4440105181050785980c4030b1010070580c15018034038a5001010002440124080c0300d4100c900b1001691740c00080280092100000074400707010b200110700840351961541d440100200346605030342141c00c080d8940030000d03040101c2c080e180c031254400392500c001580b140c07400486d14200d802a14281c6804815a8107040d8441c801d03c41d55801c1c42012032986081c001404a940d806000e00680007988c1e108a80070207590000078116850503290000040b0814101d030b0554229003403051000c4242d9040600c0e250441c0c0000b9004081c412454010a10016115055070403d8a8030004411801c0920080712401300404c48911072000c085004500342c3e204103a0800d02034541e90020301200e01140e1107058087c0c68484c444400c2e0100d00c20409290f441e400d03482c408928040c0002e52400510fa1494003020308101e0000c0480010304680340d4080018442c01030002c0a40040c59521460107040e0b8403c1d8442a9200c3c1c0c544110240507600c908 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 336490935 1250 336489685 336489689
    0xd0c03050a14161404090507050604090506010f140a0809030d060305010509071409070507080408070f03020f04022a010f050a0608070b040f06120b0301090b15011803020d170309010c030b0109 84
    0x1c613003903003072100c2d14100405400f40010039a81c5004041003c034203512000e00500103007800407000708143c100400010300c1044820301c107008005000c1840c4101445810803241140035501c1c110b0000d03112410924114803602d0b03820075071306103408400030800c0f806401c0948110110000d98500680c2c0e0b40a15201c51000c2e180240d0040c24080002c19a0707000300003800381c140c0a48581c0c1e0a2503100c0d07290741e25018131504000c02064600e1010070840c80d1288900120660a03241541850902641d0120310070202480404141081a00050641c003d40c001c040300fc43c1d03154144182d0401c40e0400c1c00a151328059841e4a00400002064860708941120b04031a1f00741001c91081d442c00504580001c200c408030040740303882d2901e403070140d42e0034010301001a0140c2c00c60802c0d4140351001e080940012000281070007034450544003080e000c802950100c1c2d40540f126142c3c4c92a43c54084840314a550001e840d06001000b0700148007815440315004004d075880410001c40510b0065606c3d007545c1c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 336492185 1250 336490935 336490949
    0x6100303020c010e0619090f03030804020a140d060e0f160f08070819020a05040f150806060a0303050306030c09010f0816051c0c090f020c01050a0908090d0c03050a1416 74
    0x204919030386c1d000c1c50708141d0f03105549442c0641000b03499100d685e1081080d5801507001410410a102c25841c0c001009001401c035a00b4540d84140c15601148010968400c00b400403a550440e03400081d0040c40003004c00081704040c0c0d000f1240050302c0403000304443c0100000342803512004030311104006569002d0715074940092204241034003020100c0c2e8807a40d82260802130495000500d500c1b43d014035490b1190854010401d2040062143e0b00c00c107996000104a60188003407000700c0c0c907608407410540b034052400c55903c1d80d5190200f40340c02c0101c50030720303080b0340240c000243c00d143c0c141d000400e5600060641c0e02407440180142070201290080c2580080f0000200800e0020902e00c3c090301403082c11100302543c1d130b901c0b40e4400c440d070900440c00c5458000810f800c10210030f10031603512a0b00582e040062166a8540b00014052003a07424041c0801101e5102402042014a00103561240884103541d10304c2c940f4100101c4c180481e02070521070304c8034200b481030986d1068000d231000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 336493435 1250 336492185 336492187
    0x90303050f071b0804030206040b090102161401121118030f030301061409030a0c2402030c2503060e1018150c05091504080d02060c090d0201030e06100303020c010e06 73
    0x2843d55555511500c2c18011100300301c08210001c0182c503460054801400500082d40d210b180b00c00003e800c0070ba501350305504d541c0800750300707024000c011440c1180000c42840c01c048040789000d890310040a030340040141c811400329801c0c000a00141410020107070036410f48008941c0403485552f00d00081c028400803520010304002d00d104840c01500070071600404a0300e06803040d03200d02003680401d0b0031201141141a4582c003030010b20001c1c50381744407400d10080d464040b004000d1516180c944c06c0d10508070344d030390310b0100000d19499040b030007035904004200940e0785540c2c02d250f619050030080b4000c403400d100c0018021861444901101a004040c00c0791092164105200900701c055105083c40000d10448080f45c030f60501c0020018038070050340d41c1d01c90502e0902c51414603100b003118215800082005444400201500e00402c0f003034940391031030b503403d100507006080c403c1101000c030303c548000c01010564044e61102100e0283d001e031111121840011541000d40c0d03080207411003c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 336494685 1250 336493435 336493457
    0x1e03012105100b060702042f0a17130209070302030103020126040308090106150903051b010518010c0b040605150405060f060c150108060906010e04110d0c0f09090303050f07 76
    0x3100e8000d0300f9420b0005109515120056001a0440d103a040100354461120740b0040f03e1003c2214554460008130b2040390700f4059008001402c1c00911864104880301000100f461400702100d00c0d004c10703500601c012024541640002c000f90424402607000030301c01c88600f2101200300c0c0321004170108610504c00d8035a0f440d101504c0903640585582041e66849400043c080441c440c07211450a185d0f40300069240b4500f801880c0860792414500300c01d40403112030b01c40ba0b8000c011a400c0d82540004000c0d14005400140c03400550003c000d0315040240c0104002c0008a0307029038403403911481c0800f114281d6206000845000322031440d0080b4a40008a42d9468030174090304a0710001c0b0112003c4411143d81c0d8803c065007072f44203c23100d60002c424001c0040c0103000c50b82c0505860880360030546400d45a856140d118403c0c0180a104070b54018018081000011009802004bc00c02c54807680c9007107400040c0540e502c180c0010346030401150003103140c1c6078030b140505155590141000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 336495935 1250 336494685 336494713
    0x1207171f0506090d0c0602010b03160e01060807110d0804061a06220306090f0b010e07120903030b100203180303030402090a02090d120504051e100e061e03012105 71
    0x688440516580503890700310b1a8001100d51711144090701d8030351300200319034a0000c1854605a00201088202c0707100200134803007031980300ca01c14111210303454186041c1e2a1860180e40c00f60003c5480d031228000c0c5400025150b410004040c0201d1103030400700504506650542c1031907120485040d84000c08004070031000090003170b058425090010001d000750f942e56603520495441c000c003240c68042e03136800c450511002059440c0100000c9039843c12a01d00090010240e4209411400c446951851810305151180d0b1100c056140c008d455030702807266807600030b9034030b03041080060044080000b5504c0c1d28280802500d02036540600140015154200d0fa00040e400c042d80301a000348041100d4070104244654548075544540ca981341d4681c00c2c81c0a10800c450411100500080011001104c1d5124034568a100e41303064509006080034240000f04244100c4000c0f011500c24840d82204031401c0000442c101c5082040c140c1c030440c083c24442d5111010b08201034020341010300c40507004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 336497185 1250 336495935 336495937
    0xd11060f07051b0f0a021f0c060c0e0306041103011d100905031317070b09010c26041e050102010b0307090f060b0d0509060105010302190c02061207171f0506 69
    0x1160f500f030402002a00c000e030031924010096240128a90000170300f83c083d400e081c901514005c40c0c662113524422a0181c014055500721400101002d07551400d8100c1240301d0600620304420080545d4042c3c20142400e18008104c071700e0036803003940390400c1d20303a40401d403a5002440700c44640141910324602000c00340208030090b4151440c0c00b00700b1950b580004682c1e2000b024010110010020251003004103140072603503005407094410400400c04141e8101000c1c0200550110300c1d0180b1607807550210141c0945400c040c00200c2d004100410022036400440352881981c001e14071443d40c0c0c41c0d004a00b642d1018441c250940c101c0344040c05415000d80100401d070401c0c06011582c5561540e104459030b01070151030604554900601c99070813000e00c801801800246003c0d810a100700100c890a12440c080718028020300560890840d120001a154010041c110403d12490700890192100740507807411840500000001400c05082c20303141c403030203c0c2d0fa040442c1c41c01c1c01c01d4184201 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 336498435 1250 336497185 336497197
    0x11406010e09130606150e090c03010b160c0801020901020c03010b01080106080411090a060513090b1f1701020309070e01030b0103080f0922150509040b071b050d11060f0705 76
    0x160f4011035140344080f64040c028100144003008503d1918807000384010001810000914812401d43c2c0070311841d01200015241950200000c440c1c0d1030b00128120510641d040c000180754107140d500c0000d1181c0190301415001c002a0240d4072040740300710805080b1400c25072424007040280c0018407260b803240300411760040c4201007a00450581030001400100c045945840d85515280c0500260500402d101c400d000e000100b1b1202c109a69198402458000d00c00c00c500c4031000c0740401c1040f0050202d0009100094840030303014041440310b4040e5204035000750b128441d0540004400e41080302d09030403290440c03400c2e1116400c0d5a101e0030747e54494007034095000020320102c00d207a900c80b40c050006100c10144a03884211030560704041d500c41e540680000b880c1410b082000b0740b40c0c00d032b40320b504c15440f141c4500386a0310900c0a075950602c1c2d00c842134003170300091140420000c3c000344104185c030f400c3d141d4101c103052500d049a40c590702240d003d6400c00b4144003003441580681e0117805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 336499685 1250 336498435 336498451
    0xb070218072304030c080309090103030f02070b0409020403020a0b0a080a230703090506061e090a15091e1b080402211e0a050601180f0501120203011406010e09 70
    0x40710303005001050129a0090b200b9000d022000030b000c20030482d600301c400000300f440e4800381d0b0a180b100c00000351904014807002c0e042c41491b90030349608a209200910181c41401d450f80e031995224090400250007a0008900450b1400e10200f09105e819013070700c0042d02c0c0c1e640c80741019500c100b01c1901900f022032010b0aaa1602580501d102d501c000821748600c14540e00000c0e17154403420400e1802c103014203c40e020702039207230000702c0b1a00344070b00664103200b05954089681d25040310701001402d00c4110481e09616503880400c214010390080001d048200c0e50740c00142e0313000100c0c241101d030300925000003034551030910b1550a01842015501500003030000342d11030002c0407020f0410b922000301e0801c0c1d401c500a90040024004003031500000708500030b06802d6055502c41d07542d4201801030544580100460000c40c45240d009420b100c00c1e00396040c010f55a440010601e003d08030481240310354204035803410142e84400c10180305800594510f4082c40c03250341800700444015000d15 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 336500935 1250 336499685 336499697
    0x3a05010f1403030f0301080609010c0e0303040e1005030303010303050d0c080c09041508030a030b2106071d040213050906010806030309100539010507090b0c0a02040e01060f0b07021807 81
    0x300c259588103011718020b05044015026625003204240e0031220a18509014003055007850101381e1400070646040e25140c442e41c891f5a00c4502a40366000c0c1a41e0206a044c403000001104059109018210b01c02c1e54580600c441041d80030140c5000c1c01c2200c0510607210140310412071841c01c0d0704035295542c00a030303075121010784031041c240c110382c09030010030041b0762100c4d512403141c242000700014104100102031a0b050080c001c05031110406800701c81000003040139a81541604680c80b0b2030790b18010011560380d2030294081c0c2040381c4038402d02e48500c440da0b0024090394080d8505e02e21403c0010050742c0340500102c1041800216281c95408010341405007600b9201b000401d08100b008040702c3d1001d4400c4048041104000c2c071807010081c0e41480140301e056504a0321030001d55225840c0720313072034900b00c08509141405204d0f010354424201050110b01d28810343c0300c00c040d21513209000c03101c00d8441008451074805c1d820f00030f41040c0418000324580c140d1100d600d802040601d008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 336502185 1250 336500935 336500947
    0x102280807090e2d040c080c04060b1801110d030906050604200a05070b090c0906010203070b2d15040506031b1003090803010e060f040e1c03023a05010f140303 70
    0x41c8101c0030701110211006c000b804414807031407104025102d504401154140601410402800f43c540034101804011810455584001d82e0051083d241c0d000c11041c00c68440c0941c03900024060101c4480544c0d0652500001c61010b0410340190042c49210203189441841c20050b64060366100012200400005001e06d100240c40409078a0140c1150001400007840203400c120000d01d015012505641c01048a40005000c5003482948141d5104882d40000300c1c441600e52540307a0300294041102541c01000f080900c0d40780082050102907400300225a203000034550391f0303810162060b85000820001348102d140c0704961200e82c10710303841c010403022200c1d078450f42d2641081e0043c007a0340e0b0f003c0d030400c03c10b810000c18109125204403070520640c10404042e6440380800c5071078407035107244059003120941c0250121a281d10402c1000004060f45818030045600c030391a0481d01c0344900b1620b00211009030180c50705036003116100f0900c481c40e00e2004406c0c040c0000120760140024015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 336503435 1250 336502185 336502261
    0xf0306070f050f1c051509040f050304210b010501021908031504020a0c060507031103011502013308030a05092e03020919260102280807090e 62
    0x180004d107459031040c1070013081c203081400907a00020840c4501c08007544034210300d0f039120200c0c141c005812180701040f4a5260410b5421482103820043d0050103408004104d0740903c5140707020f25001b0390401002d643c03210012a03c0350b16241141e4a5820100044c201240100009541022440c812400c5040c070010110b816030f004141c0c20b2001ca00302c144c040d03007448003038024164050010b240c10849074500341400005400103000d1004540e1607000d40c030b9000c078004d40c440c140c0c80080c409950b400b140135400e0508986841614030303010300d0304c0c03c0d0300040d0b00b01e0000a88404044584a00f82080781000a0002060075000c031a1407400501a100d01d07403003a441100c500c01000da650160b50384086009000c80b46003039942c0c8c981c400301e10020400408405100b414902c07050300380e026841c603a000400601900500c1e13004032500300112582d20203105201e40b0f031541c404480e141c01080f9511320382d00356003050061040c001d80e02c070071000240c1c000c4001040b200c0f680043c921815a0030a80d065 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 336504685 1250 336503435 336503437
    0x402090f03071205190507030609080706060b0c07140915130c0201020a14070327080114060315010e06060d1d1e0106031703060a1d0a06050f0306070f050f 68
    0x1000240550403c01a503043c41420310208565503142805022500c03050380d2030a039910030318400030700850f965440e44c00401500e941111855a00b141c414400991218801841640071640c0c1e580988181640000c8812042e84c04c164101c40c0104019030302d40c0c4150400d0014400103c1240d40400d41c03001d95415007080e8454102d10301c010342d00050310b44a14500186c05607000311203170103805030107000400010340c0c003040301880c612003c21141d0b942d201030803883c51001d002c0d400c00841c650800403a80c015607000100c2d103110b12412000c5808244103e40b101030650400e024081400807078400183d40d80c10940f000f0070f0040c000e58000550045200c1110b038510651407040b00c0c0941109035681626038041082a140000400082000c00d196070780720036000b002c0391100351040001100081540d075070303540254000c210f421020300f00e0712000d281588080c0d0044031600c54080ca00f01000c1458241a16603d4034070344041c00411907911101010b5a82c542200700d00c04c108882006202c5075200b00d50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 336505935 1250 336504685 336504689
    0x50702190807030807110d030e0f0706081506130308030402010e040f09050706021c0c0c050d05030703030e03120f0925082803050c01020d2a1103090402090f0307 71
    0x12001c9612903400d403070000c101e50400fa18400c03c00845001e0b1640309500856000d4445d01c0d9070800080e81c0e10500c035500d051484084180040f07000d51a80001c20540182040e441050201c4c01c400401c1080303010803542c1d01603030f21708a03090407450b0340910000c0c100340000d5030420700505091510081484c002825184801c12011005443e2010002040b03420850700d4003402d04d030300161440d441964801444024104003920400014040d0041446940c0041740d0180401424405916101e4148984d90b5403041344105c0019203480c004122101700070098030b03140000e50740c2e07a10903610b0300f03a5500c00559020344042c0036402001e001107a0b0540142411007800d10060003024001e00e0801032509206e0080345074800841c10a2041d0b0581c5400f01c000b1b1605541400c0082e20f45e001005640e00901a1038868141e65260522122140c00408403450401302c039084003410b0070203610021035101100d40b5550a190780309000b590360600e07041c0c0190500c4640030b441d10b694001c03034200280c81c1c40340036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 336507185 1250 336505935 336505943
    0x1050603251704060f3e04030203030415080c04030f0314121006020d0302090a1502161202041b080c030c120f06010e090c0301030201080c0c031909090b0f0405070219 73
    0x18603200d0380080501d001e10503400703400422800030a07140c11504081c05009a44242d401c2d500410a115001c2c1c6c01402d0794080c58015044035103440c0c40e0041c02a00241c1141c07820042000b420024090384114000c41e02540e43c046000d000c5480141d80c15101442c45d00d013200c00d0180140b200401d0515155040e51064040c49001c4100701d24125020303090901440d0314030200360040042d90701c0b0352903860040040707403410b1101c170b50b0354440e00714124145030400ca041c008201c00510005407591401030400d074154001c6408010001c00d070030050a0603032040d00c4040c08078001600141c40c2100010140d5840f0300d038420100e1905440e61800a00d1034401c941d00c1e084004400c0c14009156031040c07480c42cac8158196400760550030318102500e00c90005100c0241000320303890001e40040040d501f40d58400c10640c044a881e019000304030001041903000210000d045040c0010300900f6034050048241c1c0041e20320180401c8020600001c2d10700105040194411010840315030010039403074042c0c450007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 336508435 1250 336507185 336507191
    0x21f0615090302010e0f03030711040908031302032b0e01030f092f0a140120030a0f020706091206140f04050d0906050d0c17100306050105060325170406 67
    0x390310016150300040440680114890210110a0b480000841e8401900306400b0510ae8005000140240541c600000c2c11850301005219804e0b04001d602017010b8405c40694210041c120b0303007403051982d04004061000280070940c0d4100d0701500518402e1801850042000049680044140d40100c0011507180a0116240c0503046200701d078540e0070242c00341409504403151000540c1e00016018259800c550110b40314490b81c0107191000a92070701d040025000d01070302030040d07181d0704006c0d24880492400189904103900c040340362026528103498211119040a0f02c0058041014504446460f9075888010055a0555405100e05034061200440745024079005007419600c0100b0004d02c03100314400c2c81102d81190070745000294100d0300040246d40054211240d041c0090501749000740714040c00101e0004003680c8090b030f40280810b120590341c503420f1000f5848100c1300e0001040d50b242140ca450522000044280e5295140c60001e00c1c04c0380c018400908402c1c1c0f02103400547d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 336509685 1250 336508435 336508439
    0x206030709050901050303160222050a0506040b0108040215070602071505011d0c0405010503150d0b1005150a081e01060f14131a070b0c04080c0a06021f061509 70
    0x140c103e070300ba405420141c004d1820300348e817500d02410324074000c00001d02c1000400210400782c101e40f03040350b06c00311250000384078504000103080000d020079134161340514180107a822055018000c82401154007818000c0805800403121203d500030080480e840f94082102002140025103103a500402e070301c40c00181d0394980070700044201da801810b007030006120b40c1000000a0318009540498800b030030059030f40d90742d824410a00ca070320307559101d038403c44202c2c0307680610100510131440703042120a81c1e00420b403075070100010303240c1d440b480001070301007003168074500c074810401345412600151040500c1c8800d04559000d02e18260081000078101c00c01d02d5560541c030041520780950b0200c8d1103441d1000080480640d14014042da951003500c9150307610501c480142102d1540c1c2c5c00c0811b142c09428201e586400660051143c000b00c3d01c01c030060711001d49400b519550465840307800804940c1444c1e001c40c009090141e8690f943c6c19035070b4500080c0c0d9072090b0008261034040759502c041440c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 336510791 1106 336509685 336509689
    0x609030f1e0d0606090920131a28082a071b0807051c0c17030a0306080d0207031e0f0b04030e0405060f0108070c020603070905 56
    0xc0700000da220390402007540080140c403010340e9502403080e40c6040000554094a1506410609908400d035400e0240c0004080080c00c001182d916a591000440d40100c41c0204000d00e21800040080100528040000704214402c07520000f0311900e80000b000381c58024411010860070303003990409403241440c41640d891300c1d911003e568142c9450022644004002003030000c0340c40790004242068041041000d070b50000e414040c5001000300f1020300c8811030038054450740040b2001140f070404011b0101840a2040015a41c6400074107000301113903155801441d42790000010644847d80c0401c20a00301e070b810440200013030203108104010b04e066407100401c01c10b00110980100b1121240c45403107540245c507180480c81010701403001350b46080b075038142d00a01318607521403258000e00c0c210b900400585000980c2c11015808203000da402a81c90b07401050300380741b00300124 = true := by decide +kernel

theorem cover : BRFrame.Cov 336330935 336510791 := by
  have h0 := BRFrame.cov_init 336330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 336330935 ≤ n) (h2 : n < 336510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
