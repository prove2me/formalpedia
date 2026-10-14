-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2703
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:29:26.091764+00:00
-- url     : https://prove2.me/submissions/77181a93-9a38-4fb5-8450-3aa4b9cb5044

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 485971223 ≤ n < 486151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 485972473 1250 485971223 485971229
    0x61303030b1210090b160203070f0302070e100303080601050703050909040c1206020d0f150e04030c0b010b13050303040b0d02160f0f030206070302030402010c020108040f150209011407020109 84
    0x105940d12010209a02c80c68003000341100d140c1d04564080140c15040b60061803c20020360b00c000c40f500125014035900050700b500d100e001d5005606215460b260040135483c1c01001710154813800e0400500411410b809038804c21040008a80c030380d01d103050180140c04001c013004e041040c10400c25001a800400f5204100820b0722100103554a9107041180e40506401851030380040200100400034150020031846100c0302c0305100454200388810150703041c10704444030900900500348580722542108603030141c0245840108484e168403100c003900004c0c1c00001c100080045c0600b5414422150000101030030740c000c501e06450500d03c541c050151440c40e41141c0c0e00001c0c0c2407020602c00c5840c07100745400004800300c400051510b940d0654103c2c50840240c00f60030005100580248240c034810b58040c1c41c5c2000c1c0304125401110a450001c200711030b50f40c0f02c86405800700c0c09030305400e1a5400c91900069403440b4a03000500a545d00f03070802d1840041c204400c0c00180d07848042c402c00c0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 485973723 1250 485972473 485972477
    0x20106141f0207091107031805060405120106150507021801061409030304050a080c090f10060c02030a120e0a3201170c03040218070816020f070305060f0702061303 72
    0xc500c1c8600c8128100703010b03644420070003414819442160701d041c50091464910a49841040c00e0300040140c00510552240650020040c8010002410140c50320f0016078059000018a5a1038400030142e100450820b900021408164801103082c100c040c4807000484207000720a6614126004091042e01d0003000007c2002180c07034401a00c041042d580603120040c2501c0c4c0c03058407640b11a946031f0780c00d10540c0c880d071121404030b800710705500300180c0201c50209040404904264040d5902e61722240c0c1240c0600c0f90302d0884005c00c0e419407030480c2c09030b800d0341d4560301c0300a41010002080c05035003100e819001a0418494080d0843c481020412540714045404543c140e0060762040e1a484009004004080c00c12490408160046214500c22a0b10b07640314141e08400038403003441100c07070401054401c40821480b42d84005070480000d01441264075203144075004a00701074095004445940c484401e224500d120760300c02581c001500d2004001e503140040f03404180c40d89144020301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 485974973 1250 485973723 485973769
    0x5060603041112210d0b0a030807030e0f220b010512010e0c0c0a030e03100204050609041508072c090d0507052407022e15050904050d02010614 63
    0x8281070b050000007000006413103030840c00309250194181650040c070212034440e02d130004a000f1458003100010075240c00c588407e04001e03190750705452042101c072030b00c1d510402e800780d9501d10707544c0e003601c1c80350505000224484409030b89211506441003a42c4550520000344090b5202121582000341150b41d0080808140d03100c12006000b14401c100821103203004003140c032401e0580282c1a4501e284081e0b044400c83c03180140c2080c200d0055008665100c003082000146915058100c1410b11160140109496503154101e510301f4045500c41c02040010010820018840a103114000c03006081a4039032841c01204144c0c80305041c0c1c88070003c1c45000f1030031364184501080800d8800c081c18200b50010501c0d003500141c0580200d81150051140c2c030044840941032030502010074402202c0c040494004022800103400c020030700031103015a4505c00141503036500f40c2c440c02a8040c002030030003000c00304402030964045400016208a10300c00209283d01c074903000480041002d20454 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 485976223 1250 485974973 485974999
    0x6180311162108091801030308070207050117090c0a151202040e040f0501090b100806070309080301061407050d23031e04030c0b010b0405041a03060a02071b0306050406050606030411 80
    0x80303c1401115041500510340c101c21184d102e52524640d810307a80652501c111030742c0c0f0f514040f84c1d290100d00900d8002002540010341340ca0b601422540c004050f0b2050b45e001c9001c6201160414505074403001c000050a20151503c85c1c206000c440c0700310014205526050074146241503080002c0c1009110600e00359508060040030340c051a42240e0014240e65581001c640c07044600c8032500502d04107008010101c1c00080c000c2c401c0320700c0e00d90302507101804c43e17181c10300a540e040e240481510402004009500014505206281c0c5040381c584482c5038440107014801000e44440001c5001020308100740140705010805800c91610800d662050940d164070b4200d45109030b0610040000242c07034004200c080d4030301d0103070090390000e4074200002003004c0d099071017800714072032129010b401040200d0b030440b03ca030b0000c0c03040600800000c00d20b0000e14840f080c0c059010380c001c0d03450aa8880600c0100002e5028003504444103c901da0f08605281d2a60a2040c1004510911030105c0420302 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 485977473 1250 485976223 485976233
    0x906070b04080d060e01060306090c02210c03040b040806011707090b0d06020a0806090c0a090308030603150a0204061d1c140a150b18040807061803111621 68
    0x9031940f800e480d03400d2080659501c3c1455540f1000e008003408a401e1450100e00c98203d4411503000c4402c907802040504c0e000d02242d0140e5680c032030300c1080c10004000c007a862035003c0004000500340000d1481e507461910003035900340300c0184c100303050800701c500200c160040b0004400e0f00344c50300c0060014224991100041060811000007000c190000c5034504000790040401c03481100252101c02c441e41e40e5012051407440b40404200220300e0a00b0f081c40440d4028002d075a004402504075803a1100849255010320302c1110001c0303900f50001b405112880d80068001040c1801500e5400c43c5804500040c03110460302c60401004c814031110441480004607243e07170342c4403405040d591801440e060103005040082030f003914003820481000e0391030800064501c82c4203074208a404082e21140d450b22029844038000340d40460b1600a40c41c980540b600800b02006d109440c3c40b03280c1c003020940517050200c0800c2550426054040c100012203000001000710b4031140b403d140e14016920349 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 485978723 1250 485977473 485977477
    0x4060c052205120d050a0e0a21030206070315060e0d0f0c210c0b0306031002031314060601090b0705030d110408011b0e040c0203190503041506060e2e12110906070b0408 74
    0x1101c0c050090300e164a0440b01ca0148900919000b2f5003550142e96411038240d0030f54501850141c0c228442d400b08000c0c0610500ba0a501050b00900483e9641915190300c9095945500143e030020541c100030030003032540315484018851014143e01e1103070300303944440040c0c85040c4580507101100000103100355800740501a50010303003680441d10b07810021415800a0f0844000325030a0400c2402e003170f20600006406482103c05030340345000e20707052035800c000c1c0d07420140b004c8450b44001e0240a84951040c005d0400150084140d07131b450b11310b041e40c0c007800d5601c0c400c84a00110032021251040550240c65800c81c00019140031070000e4034030200302d1861040c00214081d0040cc3c1040342c402c00d80c0800154040d90003280808001c0101d00d1801007161414800c0c071020840580c44102c060034551070410329000c4c0c1c2158400c0c102010041962410003031b900c2600016a17182c04000201d01d04c0c403401c0c00c1c500c00030304040d051945210100e0807a1250b6100640a0002e03180010200210502 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 485979973 1250 485978723 485978729
    0x809100807020c0103061802070c0b04121205090d0813030605010801152103140708120f0106030903020c090411030a08070c091404060c052205120d050a0e0a 69
    0x41a41012121044020040d032016580003005010310012050150b1083c0280d0007510403003d4445042031105c1c04102c020b500c210001c1300c0b516016a00000c40301000000740c0020510801c0100d42000d8034036040581e642203402850522105104116481e101c0008001020b0742c13000c00240e82d0000d550640064100641c4005c0c0441d0030480041845070303042d0000c905c0400c0b8584025441038803014848008a42110301840c00419603c0b1074000ca0300c500e080038510141002d4444ca00b0110382c403410b070350b988031003019480d44044e0300500049891410035540100010f10301041090300c01e98000352a0f0001e0500a0311a20b41c800120b0140b00c4010031848240341d009084805544503841d1652140d000348200b5541c04690000000301903c0c5401141c4601502c03802101c2c09913150740c0ca42008000400310700c02084000d000c189900d141b121000d810088a94800b00c0750a0b1900d020800808411030f800300064101e04440c0f00303640e8104003134070088c0c48107042000d040a29600400d00144140d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 485981223 1250 485979973 485979979
    0x15070611091e0306070f0f08041a072c10080603240403080108011a040905010609110405090112080f1b060c0d0c03090c14030a080301090b0112090302060109090809 72
    0x5488080e440381c01c0b1001d100c040c4041c2c066851a640c0d212094680001860b5550082a501c0c00c072561103a100307014940d0700500c00c1202e0500e51140840000441000311458004039030400700006d100280c4450404000da400c445c4825060144004a03824603003085a16090240401c081107840d07500b1301652a640405411500015008007514100d007042950283c0c04211040008034558906004001540c0300c000000e0003d021103106001c003d21080c02c0c1035070725558956007c01d440704d090141d00d1500c0181100b031620746007400208185038206901c42107044000b080a5800148803c0c240c4203081e428a030200d844038212201c4000c0c030454242c080920740145400c110101c0c1100000e000821014a020402c00d540000194111096000d01134201a00710b241004038001036180e154071024050240c2e20000459076843c54140c00a0b0407450510362540348c0020355580c0b00f1751201c0800200001407115001c81c0e200a9161441030240c14031407925184041c090120880890b48000805 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 485982473 1250 485981223 485981239
    0xc2d01090b0a02010605130b1f031d010b01030b0303090f0409050703080a050a110c0f06030a0b1e10020d0e0f0d050a0303050703060b040f0b03060406080d0206070206061507061109 79
    0xa00b80240240024051705200305100c48000c0d8486800744105654014003602c00400e5110550fa001c04c0b419034000840304040d12425620101800188012003e10070300c0004614001c1403000075050b04c610705c15040c040d40c0280b01701c07030345550348400c41001c1190907500040c5125007400c0482c20441190405081408000361340311000750304c0001007600d0682581e81850340c80e008010140c4850001d07100582c05403060707440403502c0c94070200968000d41910000101500880c0115031100b80940c2d201c080100342081c201c4c13070f5040c01d044d00d82454415101401003408007078406401c4820b0441994040d90f10000010b140d034580310241960141c1020440b00c113000546001809460b00b02d5034000028208a400907000b60382e00150b07000c2e19841414903040d541003000c100b1540d000140f050794000d844400000b4002d8023030001c0392030b14481c1d40c00f0302000c1c540128003902e0101c01400700f500034024901401c8811900c0010380d032103550b0141c00440d801305000040e4800d0300400300025803100b06 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 485983723 1250 485982473 485982487
    0xd02030a090e04050307060b12010c092d29070807150e1906090c0b0d0b06030c04120c0302041805011805030912190606080c2d01090b 59
    0x504400c111507510440340315201d91142ca60340e4001d5400500381c2d401405181d0001b40d42d81c011103446d8501900f02c501420070040c42500b510311400120011038060b000621010380d2450b80c50301c403020b403407041d41c450030087c07000400804040d00c2120211442c80d490b110b00c0f1410680c0312030200031084080c944511290405203900d600003001202c804818030350500c9000011b000302082000d810025141d0b540001d00c0103081042c04540480309296034015440c00250207420745405030800100f2140c441900000c800e0448031140c800f90b2140702e0034001c01241e0000182104c083c1d541c001d48002d2140080d140c00044411180c0009600c1810004c8820142c69004884104140034500030b0189100d10070401c02c603420000c8019010360010040b014260405c56032404242a98504807801c200760600c00301001520100c00b1134402d41c07542010401c1e0401000440404c6a0403294141c1c0100d100030315044c0f201800c62090080c444201001c241e5a016a0b1a40010f022084000c2c2e03035018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 485984973 1250 485983723 485983727
    0x51608040e06010210061a0c0f0706020606120c030712050316080c010f090218060109030f05010b180601080103110301020f070507080618030301060e040f1406030f160e0403030b030d 80
    0x10040324034078014811011105c4904d0b5080c01100226991081403034424900032018400355445000069060f11641c5146104d44104204d4840200056405006a800c0a00401071070340885080f00c0c8032907000c2014170720155400300d00c0d082102c2003840700c0400075405142031400d6000740c0c14081c0c020312442e2950028010080c004002c4a59600000c000b0406090860b604403251084041e400004192940010004000300c0540162050600c04a0030390b90b907450b076680c4030ae6040101d0701a5101c0700c920105041c00200351100005031a0340d085503140090008054035014070014000707081000c1c1e6082c0a441c20750480d42c1155540101d9070f910700480c1069680c03181144500700407449068002034980950080c84005150000050f500e542d20700b00c2e00300c9020030000c0200e82d102da80c0d8a0b100c01f2010381803060f120b0100d12141c104543e45482003c1504158404e0000f401c0390300f240c00c91031610200400d403039095400046070f018040d05c41d410218000c0c0f01c0c005a072a01481050214000d480d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 485986223 1250 485984973 485984999
    0xd0c03030e070806040f020f09192703080a1e1a030f0312060117040614010504111b030c01050f0108060105010c02010e0405280c1e0f05160804 63
    0x58000d460a01007074007580555540c0d84000d02c1a560300c3c0e0040400b060004000e0850070440d01d00041151110b5652000001e126880c152021071010380302003c00090398116000e452403000e2005c4400c440e006500d811020fa09070390140090030084c0000010303034141d600380d2090007106601e251a440d43d8165000903001410704600c02c0e505a01d542c240c50740240740c00600e82c0010a8924042c2d401d0085000130900003050241c1214140700001c03003503a8403c01ca11000c0391240d4003660001c54040784d00761100c010400180c000030b0040d4184883e030140d068001040b50086600c039000c882040c03030b2010b040c40c1180205600c04c41d2950810ac01d20043d507990001c224181c40024064031a203998034001507940704000d244c000c2c04075030290320107401480c099002540c800c0b801100303c1074034181a201e200f40c210707042c0b46940d211552a0024420182d120140208900907261840c643c2040240007904002c0490220300c2008400665440b1422032211035a445079840035001c0d44840c0c450811000d04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 485987473 1250 485986223 485986247
    0x1801080c01080f0705040302130b03011118032121090304050a0602060105031c05070c06020d1b0b041103101a12210a020f07380a0f0c050d 61
    0x15420b030340801c844160005006000b2101c03615040c1ca80b034034503824046d40c010707041c00c0d40c5181030355882d520400342c5080c007821079002041e074130760390361814024990701854912402907030080e80301070740210309603541078030500900742c40d640487d4844d280740080d20b1005101c9076181641e19044418004c202078000040c0c07064441c201c1c1c07040c1225454800403a030703078582445543e0740760348415034002d0303180c4406032a2464580d0a2400340c1c9071191548510040511550006c00142e10030070380c9210888d4490010740c8400100c1d0380d0200c01150a8592441804001c0c2c000b40c42c0c0b0442090035200c6a50403c01c1d0346241c0450071080c0220010b551584490000710f998544c050709007001d1020309480041072003005411003403440e40c45030b00e20003036080701034111030f100a06512494040009a504c10480340009125502850315001d02d901c10b0f07d10060344490724101d5000200d151711001103108800c0e02c803038400e076140500341180080e0b8101e4080855800c00b40c0380c2d0044c0425401c209a1002089a80d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 485988723 1250 485987473 485987477
    0x1b0a060504051c0c150b0d050a0b010603090c03080a090e0108060a0513031d0a051815180106030b061309050414061005060c10020406050c070b0702010507111801080c01 74
    0x1043d0740350449150807581c803061000103024034007900006103e42c4204510324107410001a4001161000c00d0446402c40740503140381d80b200c490300c1d04100e0300700803d6000d01401e00e0700b4040000c007035440782044911401300914041020901030720080c45010103a00802e10703154071240d956911062152140c0c400d403100c59509080c080000e00042d12805041041c41c0c3c10380d00c4858040c80c03613030320361510150082c1e000d030302402c06e080008076507444504582040158010807a884d0524040e030b0b00a0220456130b5074041c08800c0007000440820301d09860441d040d03414042a100040e44c002842441240869010b0078424000810f000301540e00c0346202e10320448041c0c200b048605e54055944c10300b2151451000075000042c0014141240a800c50314440000c0343d05100c6113040c0784003039821940001000410100b012090b081081101d48010000624038a00e458501c0d00000d0040c8124040a0407440e482404503102c0c1e241d00007070805081201400018650312504d2092b00c5607134904071180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 485989973 1250 485988723 485988733
    0xc0118050c0901050109090f140a2c0303040b0a0b100302040302010315050a151701030506070210020f0d021c09060f0b190e0907080105041b14010909021b0a06050405 73
    0x1603414503900030b03410b840e016114034501c10711b4904510041c000c3d01c001076031081d4031180020700a1041c00026070103403501003c0410808110784c100300b001030100c0820170300d1700c0c40000103184003c80441100e811580050541511b40d959a100c40098583c0300009a004a56001e074205019070603400303007060324401d0703a007803000442440c03800c00201c07224001c659014808400030481d007020308901400040b00c500340850720b4544046230300c2070580300368002d8415070001d0302040b03182981403000e24000d084104046040000c01d1520062034040c009100d022641d00151600c140006640c40c2824115000300030b12485015142c03402c040c0240c0c1040c02080f40c10803050440a00c0c01c200400381084031510701d0468a8a401c0e01002c000c038015280003242d01a04c2c4020070b03480403e0144510030760060202c41c480f000850049107451510b94081150b401004044098603a80710100d0360464030042400750300d90041a8100e0f221b05440a2002e0321442907483d1081003040312b1704030030303c59401a004e442e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 485991223 1250 485989973 485989993
    0x803040f09150b13030212010c0207060203031e061815030606030a030e100c0807030903172b0609180501060e090307060515090f0402040c020f03090112020c011805 72
    0x40c00d5805040401200c1d0b19042030511a4850311000303044801602000300850320394030340106e10602c50341d503c0c1d400240d4441c0300b400352842d01080440c000300282c1c40254910300d00307184030750365014080881c0700c800300c00c0c078001c81d072150f82d034550007000c4150201c0101d0346428403001c0040301e500083c0c0424028001c200000c0d88920380441c2d03904032285c150301c9251013141d20b203040003165500241c898082c040440451008140f5590252101c5c41c841c0c3c540400341c500f581050080d1414607042c0d40f040040c100b02c0e400d41c45030904052a2010303203e0304013107280c0b81c109040c5c0018001d15000205140d151409510309035000707441e620306507405100200a000d4880085080041003110304102a80c0300300400380001d0003560200340e020b030111050544030fa0841c0b0005000810540e060b20080c12030310280025880c1600c500301c221105400201480280300900544074026204010306000325010514008100d580440f0310145d460002040380301c0344551415900c0c14200010303103061080c0c450307035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 485992473 1250 485991223 485991239
    0xe100f050f0603060622020f0705030705100504020f010806030a050f0d0e0a0608062106130b130209060f04020d090c0f0906080604080c01090506100824070806120303010803040f 78
    0x410b020303845c00b4010503e1002c00704080355941e91041940c1403660740c01c2002d41d600c41d03415800380223050b11034005599244803d007000b0345000500340c0707042002880c05051100591301c800c14a84114000e0038041c840795110000603040002076a0007074050300400d50020301072580403900010241098030784102c040162000c0c003c0303583c0d0f5030044201180450010a0b51854507071000c840c5042c510482c840208146213440c1e00f0403005880b21a007004d03905102c2801c01c5840950389601c02071a4a038034404000b01d400042017954003400450162a1444034404903844d5901102c1a9030426401071090041c0c81c034021000b41141e108403550f40b20141e0000c990a105805610102d4910710020038040d110381d121090180d000d40701c03045156594042150004000340300c15031180b000c4a82c4205110300c0c00048904000b103581001d0a1640b03030b607452051075003801d00343d40d800c4000e5140500d11950341c1408995007205006140c64144804000096044400401441500d0395551a1410940e90b0441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 485993723 1250 485992473 485992483
    0x61d060a030c05070c1e09052e18140a1b03111209070504050606041406090109090e01061401090608040605040f050613020418080a141312050f06010609090e100f050f0603 75
    0x8940c1440076908904141002c8407188041000501c5182700030444e81d60000c1800c4c044000505001c03281c88034121104518210310700b9038051003007242401400a0b0030a2048a92020740c0706805042d07031006960f845000c0d0b80c080d20983c3d01041c0301117841b81804681150364440511030385224600700750024a46040c0300007920201c8003441c2c40350000000050400819030030214509041003219240052804410701540e085024003800014a580c03c110661142c1e000e0032007054140506000200411940100840e502a421001c001040e40396840d00865a02c1903031005810f600c1a1000d1101294025003810001842142d00300b00d5180625484071120000c0320002c0c0c00000103001c0030107002c4c022001c1080480c50020114030b010301e01644401801603a4001d1285904500c0c005001c0107400c03c00d0510107000c04004042d10341c50400014445034090080d004499192508003211070705c1000800240560104140021407802e5040c1c0000e03c011640c0f03195080980d40412014140428 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 485994973 1250 485993723 485993731
    0x3020415020705100908100207030c08180a0906061d04141914010b0405120f010501290f09101101020d0e0c010e0f04090c0e0907061d060a030c05070c1e0905 69
    0x8094038600b60b031f000c5580025000480203409110404682d00300040d03900000b0940e041d000c00018203c0b070003c0090006801c85504020310b21803901034207001540d00301404002c1040c0c00300104510504e001d01260280c0600c0261901ea070320810180002d48004042c418494044140e04000f6892401c1140314241028441e503008030340c0400043c01182440003880c094441c900040700c200a0f030420820f421500300341d01c03048940b40791030140ca200c00050704500d03c280c41521600c2e03041c0340400c01d10404074491440d00c1889950b0300c544254115010b60f82c809021940d0308003c5442e5001e4100c1d9001400d800190391003580541111400c81d0741c0200680f407403481c805411444814006001d0000801512030305030361240403018001988013141d180070707200307800c541d02800090346801e5000d840e0030014104a048401d40015050468030b0310001d0f5a0001c2d517510300031400d03c207441c009498600c10300002400d847d40140c0701040d4640c10b91081040d040710951402002c99035140e45c08111201a2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 485996223 1250 485994973 485994989
    0xa02070305070204020901030b180106030c020f0d0c150c03090212011505010e03010902120f0f060103030c200d1416050d0f080f0d0b09010b04030201020a060c030204150207051009 79
    0x202c11080581410f0b03028003e510b01c1810000750358581c66000504030588001c1c400c03100441080184483c9a04d40102c052140c0365000030811041140503940d1070341140c0e440c14041003540c9810304240f150314068800c4c2d20025001c10024074041a60040c0030f4804071505a000304090040b40521280500c80c0150348030510075000011414000111130300d00112051030341c1592181d28010150340c54030a5004850042c800411040004020603824414980d842c0b1100e600000010030110b50410b281006e580d41c021600301c1d0898810103804130001c800c0c81d110b60080503200c458420070104403240110031402408a90f05451020023840390b2068a0040a4100e0111020300c2c00140c000802100914400e1005504107605401c0603100b680080c030075081c640d0b44804007042c1c28100701480c24098000e42003c146094110740000c1d6075245840c00007000c03142c0d036806040b200c62003607040d1000740c0742003814503442d00703060f42000390303140264011540300b03900072004c0300d820b54041c00319542181c04075 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 485997473 1250 485996223 485996227
    0x280b0c03072007080102040b03010515040f03080702060d1d011109010c060f0f0213090b041119140d0c0e030f0715020c06040e04060b1503062202030a0209090a02070305 74
    0x401c038462a214003403028034140f090f5040032415010a0010780f01600ca03103401140c0b00d42c0752004200013031140941c60380b0300020820003031120a006039095000c0d80d401042c429524047c0384081581445003840310040c0e1440d107440200309458008504c11400d840b64000d006540c140c0794044080d100d03810516004c141141c41c00e00000301c1030340100104120710140010201818a00c410680c0d01c4400c00d01042c01280c80700b8400c40c405480f4480c070700340043ea000c00c511b65a8498030035062060001e80d030f0000021000c2c100701036110380000064121007440e80c1d030311514410b4803800540720700c40702030021480c90200340d200c40c10005043c18200700414001c02c1280d14180707000c0940c103010f029890442c060040401015101c0200a100034105089400c4142c0342030b0070917100b110403248540e4810541d04154030502e44000e400d884e00400f0403121084108605100140c80001c0880102c0310f2900100c01c104220300d40d540070702080b440648011004c1d0390307144103200484c85941c2005001c5981 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 485998723 1250 485997473 485997497
    0x30112021e0f10030603151b0201050705030c070f0f081c05090a030f1403011d0a051003020609030109021f0f050c070b030705090409060c0207061d060c280b0c0307 72
    0x71440100360f14140038280043c0594a945034140c4841c803541487c0d21035900d64000307004040014005d21590000d0388020025814220001000351101420f400c0b604800410342100f8070258507d2250701603800050304200c08664036260101740c0008950740543c2c2c100e401410f090a8250151038412003902c8041e1000c552107983c295000c881d0130149600300401c00d841c0c0d4082a1a0700011400780c1440000394655075a002c5518032800402048200c0c6103040505000481414041d1401941d5045507465180c22620000c00d00400f0004406948202421014030480c1c1c03ca140a401a54203607a5401003480d01c0340068402d071017800d0b03040105500048040180b200004003664114541e0b180043c90164450300040545400c4c60050310307401e03500d640040226404205190041c103a5080105500c1c84c1a540781105002c420b015901460000495100c1a08140309158404145d10120b41d404080314200284514085500b181c01c8500d0001080340b01d803a404c142ca2282c2071301d80d215030003081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 485999973 1250 485998723 485998729
    0x30f040e07050909041109070302040506070f05100f0e06160804060b03010908040b1803070b09040e0a06110a080702060c0301060c14060a0f0f09020306010e100308030112021e0f 78
    0x1001001c64040100c00e2000c031420b540d941d00620b00807030148208075111520700081207440c8070041e00c580103061041004000340c0e2281000e881072079401c0041d0303010001243c1019403d221000c030464044928005408075040340301d0744012824040c2004507641c5648589100d070f07815424a140401003003c460004000070542d401403a6100c002800101d80d0000550700e003a200c1c2c0081d00020311400c000f10f603e414090f8000c40c4c2c410011803c900034030f8541d1802032a0721b080d22919510301e025640300e0652407c4c0c0713903081000d0482650703c25010094410528031103c19500194180d100140710314012504043c80040c0c900d00402149102601d0342e440d01509940340000300348103d4080344184003043c490001400444c0c459080503101045440f03801005000b00c07045415900c0d0001d1030000c1c2d000150302c0024040341518444500803087d03803243c0c0d092480c4445580d20007418000e00000105040c41c0f104040c44841780709455030304140108001c034007680c221103040303503401540c00308200003a89 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 486001223 1250 485999973 485999999
    0x3030c0d0209040c050c010b01080402011407060b060d06031e170703021c0801060306081504231009030e040e0a0204050c07050703320d0309080f120402040b03030f04 73
    0x40c151000524151282010405513280b450004001c62800304400031044020f02962031410004d00e440040303444c003640080c0801000800c014034103240856000204480380d4061100c5440041c5510b80b5010280040e50180c074441c00116080c801d9009a0b001669110f181c084000f40c0c80b11400302c001c2c4000306914201c1d009101d0590441c8282001d0421030708400c2d841103d00c034102e0351050311030f604101000e403d540c410743c481751456114007040040304000d4200960000d500c20402c049564402e00c0d0314141c10512100e01c410790058854500b600f043d80c1d401b10040c18440d4641010300064001000202d030031000c945100c0340c1080c24034000614141d8441a4040d80011083d8242100f68503a9440c11410b5001160300b07a0500c441c00b1002803400c80410900789401101c6210315400000c1503445a490380c03400000d044c0c407480d004c001c0000c01e02c00d488800f074080a480751100c40030490881003000641d4164081c070700c1e1000c04250307418003000302c4c2c00070384203500614941490041094148 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 486002473 1250 486001223 486001237
    0x60e1e1b010c060204120b01090b0a180b040603081902061303020a02090406020f0d0f050f0915070e2211040506091314130308061c080a030608010203090d0e1203030c 73
    0x3da80c02c01c00803070b050050046060441e4080d54140d0001e40c10301e185a0f0803646905461351041240410404c00c0346a6a02d0050300880d050101240301e00525010502411044c0c00090121401149290710790780c50381c00040319000c1581c02c940c0c00d40c84229845803404aa4038014006030070180100002d42007201c10160032501c034100052901d95400b00d1842c0c0340d0403090f030303c82003261141160b035030301e1110b8051035030084003240030051507040100981e9562080e0102000300c0b1042600000c1403940296040c02040c40080c00c00001c01c59503100056191010205500c100c07880e20781e00c41800c00030042994203580f40a0181c40c9440d442e0740030031120418158814410030707110710041a201824800950003000180034000b119501c901e806000310400914440c09051445c0703000c3c040c204c68604500409401110f0580c0e51094800214040d04c682e411072021580000144a811030000840f20240784690382e80ea03442032001c4d0200a030400c0802d4003c0110b60050012501c00c0410400810302 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 486003723 1250 486002473 486002483
    0x30503180303070315050402030c16060b0301020a1106070f050a120b190609060518210d08061512010e0c0c070602010204094203060e1e1b010c 63
    0x525101800c41d203580d10480d807501c0040c0c0c0380c05800c0c540300d2101802e84084c06080354158103614001010400c41d001340c0303d40c500b0048082c0c0a50b82482055440303d0300d010b4010f0029943c034180018054054000d004003100fa038400c0200090f0352902c59080c20301c4081703c61ba219031500c0a11401210f0807100003148003499a51442c04004980d20201c80444000412070b81031045490540041c0c0085082e42c0f00c00d06004040284020b0089600c02c4010b0444e822110921000c14803180a540055540300040c25403041c40a4007001079040f010f00c502c1480101c41940300380310b0540840c40140640240d0b036488103d80c1c0018442240d040880302da00003042c40059041180816000303240c1030781ca6000f1b00140c0d5001905004012082c01140d071b1081c0000c4100070340308100c0c07403010030740d500b0300b00d01000d07210030748001c0348202020101e600d00868000304188040c10000c1c00540d03e603040804103603070616131206d03012405d44c0081450720305045c84140c00070b204a500350040d07a410900c1d46080b03034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 486004973 1250 486003723 486003751
    0x90203180f06150406050d0f06110304120309030509061201050f040e0a060b0621010906060314070c020f04020a02030c010507180e040303021c020a110102090a06050d020408011b0909050f04030503 86
    0x3030592500c140c00010b00c0e0123802c0300d6448202605103031007100c1508940c10140740f010410030002c80c440d188145004021881c0002e072480040c00c08903001e01600d404603600c4280011401d4403040310402203070588000301c400d40020412131041200316820204c0342d030860f400c155900c5011943c1c50380a200c03280da014211915003c4890001d50104040342c0d40e080d60030320880e0051060b090740344946400b601e05410100f021001031440f8029005004055404105c4446440000c545a072000d404603540054000d6413128224240a5140d8000d02c2d50200e456282030000340c01c0e180308100d406011100240da40a00b942403212491100c40d0041096040c50f400704500c01106c030084601031030880707060300c0041c1c981440c00710047c6070480540461440b40c3c01400700346407540da180080401c903251070800d596150f1403c01000082d0185502100d529460214425000c2110b01e42422920b0b00558821441ca0784400c07049003201d400b900c18010310750102d000a4002805000110f0300030200500d03141d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 486006223 1250 486004973 486004979
    0x30c0c0118091d0a03020a060b0a03020a09022b0903020c0f060f03070315060f02100e0705010c020102010f09050a021809030a0e0117040507051003050903160318090203180f06150406 80
    0x130f1800b6100d881c100d0060b406403643e041400703400c1c402d02003118021954100c45601d1600095814911030260200c0640e0001c0d00440150601e11180720400001540303405013407042c86180001c0291500a41c0540102c981c014002e241c81d4031481340441c001003100342020f01181c0f41c101c40c0e420050105051550703402c1c00342c80300500401c21030010240c0366034540460905031002820044460600f030a064203140403e6a848000304000d000d4400a00e8502d40d11207490004038054842106903064070f6103480300850901c00c0125407007811a0007599084500c00c02c40c00c2c0310100b5901120429045d41091001d6424144074400b0041c400405142001c14040c0701c1c200400c0344141030764119105d41c4422030400c01402e2840e1403c035030713040e541820003076494651611070300c9100b00c449054002c2e4001c0e02600806000704100b120f2008400760034107180e910f0750004002907200781c9003c0c915a41002c078461101c00f000030104c080e42d00d60805030990b07461f041d03403441885006071059644280c0b980004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 486007473 1250 486006223 486006281
    0x1080705120d081314010609060905060901141810050f06070c0905040305071209050907030612020f011e0203090a0e130312021c0203061201090c0308070813030302030c0c011809 78
    0x240317401244440001513a514002080b03045444c194032283c00f090811042050310754601094078115810b00d01c1d1025210800c000250600c41454008000341d2519400c1c0040390680b0040c42040d43d0301581e00d030889803100005c201c003e000310b41c4000c0203400303040c030144410b02903500000c0e0000c0c03190910904007121030351100c444114945071000059214081003041d440c0c400d00302500110a81801c12002c1d050a0300079038000c800c040301038080c01c00780c03808441d0360348100c06c40e4107840900c0340d1b01c80c42d80c01c004200035103952000d05184c0c4140c41000c0041481a40c10700054080c0d403d8075480182c07410716541c1138079135505103d00104d1081d800d005061140c1c6500c074200c40e20b509812801aa20b1074504100328079100404203440b8103a2505011400040a0b500c0240030340380c01c0603080d0348541d4a860103a035507104e5111920445070300750100000301900000a00b03070509040d4140c5142050320ba0045604072a00c85807201c045075414010010b04134298004012064406101040d2021407800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 486008723 1250 486007473 486007493
    0xf06061e0a12110405100f1215060303020616021209011809060b040302041404050309011d030a0f0b07032a030e1e060a02120a0525030501080705120d0813 68
    0x80d560f141e224040d501d00d91810707114241e44654000300d40c004142c14100300c2c084000c42402030100380389105800f1030601c4503c5004c15402400a20709010150b00e03403a0003034036004261031038001322000507a5038991034000300321040c119402042843c1092003007001100c1420070b8942c506c2c504000000041101400d40c002d040282c030307540c4420759840f03240d0300c1800100c1e0a89803a10380803a00000030702000510200846102107003d00c1c0c403084d103610940076401c2580c07a041456500d4070464600500b0400c8407a40c0c41c150f0781c080e040c03100303003903480301401d500340ca070080410040c5054000c551500f80700c3c113034000228036980c1c0c030340010700c0a40c41d0000c91402134040c01c152111210302c0d001ca081d0403402c10202d0341c003001c001402e504200102d009400006000f9103010030032034807200010703541c10f000d0880e540c20100c400321403c0300210040d0094010a000e0041c40741d180101c90020840c2e0800c404a03e075a030007034000415012030684012624410040c00b0150074200303a0301c1074008121034500e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 486009973 1250 486008723 486008759
    0x10f1d12061b0c030a030c1205040609060b03010b0d03230c031e07080f0d020d090f03111207060203100f080c10090e0a050901021909080f06061e0a 65
    0x1005140d2818110582000d00c0b1002104400301d07031040000d8682c400340801030f1031071806581408198854514004ea88804128103444101c03031a1104110910442c2d4220191140c0282c1341000592404000c0c1801d0b1154210800e80041d1081d600c800080d00c100d1020720400c203030b00480004602505035405031a1b200c2000344204d5400803481003182c48240481c4841400ba0f80080c506c1c105040c0c0c0e80e452140908840001d207800c0208001034048950340480c0c21120040400700300c0b4600d140b900740c0810420740070903800203007801113040c0e030407c00140e00d52138030b40105691420611240d1314400607500042c890102c24501000010f048103003e9000d8000e00030b8100038002ca4242002400744044070308680d1000c101030114100808941d5142d2244c10051585010444d5a91100c1040c0a4811001446020f900716001030204d140e0009015050342c2d8441c050300d08642900c140c2590f180800e0750303002c3d4041a0032038a0700078045460640c60200e1000341218603a6a030b035401040f1000c6440c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 486011223 1250 486009973 486010009
    0x209060a08040b090a170c0c100c06060905101802090a080609060703050c03041401060f1404050109020a02190525030614010f0b250f051209010f1d 65
    0x1d0184401c00c0034a05060780d10015600c02426030b04e5680e1210b000d0b108425800c030103811030000d01810090707400d003e01d1000b1000941071040b4043d022800405184040100740c03071440c41c00d100440c07258410301449000312811011403101d5030034404900c0156a81c540e982000079030030004422141c5812004600a22080001d4142850400080c80c1410700042c030040815141c601005211090501a0307900503030460050750504505105150050505400684840c141100001a034600c00c603000c01500b64240c80a0200d030342c1e600031480980c0075107540c54025070802010504403e599000381c0701013602810850700e11411048103500d003400080361006410043c0841071050002a00410030000c030310076940704296140007203484070394a10b0b000382c1d86002c2001070351410b00b1501d20702010300c1c3c07404582e1410070b89680b8513268201214503030b0116028080c04404240740c244001c1940c810340b4040e1200740c001d541614040310140102a18105113101d1898101c2e00c0b0b07203603001000e8076a5850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 486012473 1250 486011223 486011237
    0xd0605030f030306130e06070e120f160b1c110708030114040b030a03210f0e030c06090316060902040f020c0105040b0c07020109171c0504030c050406030209040b04060209060a 77
    0x131106200c80d900d00007926050050602c80b2403816060000345035a40402946004c01c5545c0f04500024540c40589001d002c15100740e98184030440303004142040601d4a0710350035518659a070200c003a0030f0107460000f20206810b5078080405103100d8000d4150b10b058885114a03061413651840d10a0b0001e03042014214507040380d03420075080031301c1030481a0108070010300c0962101e94008010540301d10356003c1000843c2410880c04580d50010503030445e0546041c4078032000c0c0e070a0240c1e203420a42820700d02d4071401e030208500e034070040102c0d0032010364030420000422440d110703000603080b414012038005a03610320740c88400c8190300c040c00303510030b1100c00404d003070411741807000e582e0740c002c0c1030703080c038640304004500041c0c0e0064450b100302c401914801d918180445115400d1005141800010300d445116440b64298414001c2c01501c3c418401003d94544403c18041251803d010080d0080034400125000c0b451840e286036101c0d100d0400903240c9441c450200c0c3c480e0300510302802c041015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 486013723 1250 486012473 486012481
    0x110a030c090b030112120e10022d0604031119030503060f0102060118090203011119080112170c070f0902090a051512040302070302030102030c04180605030d050d0605030f0303 77
    0x700a41410003004100700807801e5504001406203450039100c0c0080c5103a9000c00c40b6800355000705050013140e44003c020f240d548414600c082e4803000c2040c032840c4955020b00d442004202e031948444070030344118000f02000d03510360b40c0a840e00140488200c800748150400c030300f0340315200001d20619622a50b5059140e0800e03000b48458400c0c1208040e0541d00310400510814004212044002c010180302083c4510580003080c0144403401d20001040f10000e9903140000b00d90035070810002c0e00740d440340341036079960340700380c1c181d050b02c2a0003000890380d03880515031000104050444280840142c442d61a03a400000a10700160380c070080b013458000c43e06520510307044140340000c0000b99404203000a10800034603007031080c10300c509500b4800b0008101494070070045480034503400303002159030b802c00e024810581d8000d0b224000e03a0709071034074820403583d1183c0960070480f000580200002044a1404c1e01c0642000345148000c50b92000d000440d6034040240105031409400176641c1c03418 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 486014973 1250 486013723 486013727
    0x1a07050307170a2c1c051903110606030606060c1e100605042c070b030f10150903060f0216140c01140901030c031b030c020f0a05060c030a110a030c 65
    0x85000218980c07860403000100d400039004600511000101c880c00c2e8000a10000350005d060360f2130001c0c01604c10000b1b43d2201c1900755900040d814001d844510030001c81c99072640d075030002100e806815030094004a01e190a01402810030540000e0654090401280d5030746400c3c6101104000b003030380000d108941988203407240e100070b130009840a002c0201c881840001c08550103103c104401000c0f0500d10718108180045009441c060210365582e0401040581c440d200035580020341c04025500080c03c400c046101051003002619905002072a5441e800001c11a07006035600c0103400300a09031800c500a40b1400c41c161050020003155240c5146161424180007241d9050000c0c0003910301c05a1a580103945032101d091a01081800c00300108501408034480030004c40741d02c98460014954042d000702c50901c220740c0c2180c00e00c500c140112503407101654400b82c02902300b1004a50300c40c0c80d020085900020410f0042146840c003442998143d100030790b1078001998808003034000d19 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 486016223 1250 486014973 486014987
    0x19272303190605100f051309050604060b04110c0606090a0618090b0901020424030b1c1505060a050d0f0503070c0f0b04050f012f15060306011a07050307170a 69
    0x300000044d491072800c00a140c0054045030252510500c003407000c0ba40d024005400c4645056480401d545040c207040c0360010141a0110000744102c1c10000c034a459510244140d8251040b4900101442d85421050120384034000e80704005c0da0f0345581001c643d041c124540e03055142401800040c00070050f0a21040c6114054080b10780c59004210812074404a03e220f0072070b09818010402400720f10503010307001888003044890f0070807100d8981240514949002c401c0c0640101c11a1074403803469420301c4221002128010b902c4500c00d6024440d5040c071403005512144500d4041403c0407040c0c0307880d031450700010030850b0100301d620340612140d110307400701100519100b0017041c00c03e41403034001100980d0007080700f8100300c0c000030815090b81c400590003454210105440c404210f0125000c5c0c0c030740003002ca02004408144000c1030142c2400501281219205103610880202184881c0955070003041c1c1030b6440c0c441031000801168501e11049900441007540399030758601e03014080c0050b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 486017473 1250 486016223 486016231
    0x507050904030c030f1b0312140f0a0e030408010f1b021507080601020328020c0d0210031808180a050301022b06090219272303190605 59
    0x940d940200388000290450080d4404542c90b0170039030700365043e80340101c50b450322926018811070750040c513020500d0740042c080d101f8140110300a00400c5118613010010000070788240c1100070301c0c84000b0f8801243d81ccc0c0014503100f4408240e80c542541c40c45001d081d2811030601c80d04c3c20f5510300d50445075050b041070002c100c103036030f0000d0403440092284429110600800078002d101b0b41500040d401c0c1e100b4000c45080341450300180aa01c6841c003074000c0d04803504010311000d03104103008100640380004000742c5040c1d000b4a03c42410000000c01c801501ca228031294410b140e69075094005980c40d40a020b0050704907884143d00080031003000188042640814081d901c10442c445c0e000100700160f03100d041c00c90700003102d100c00085030140102456405000d01c1480440d03103c8003903555125440c00410150740304080208000c00e40c1866181c0c280010750040b14800c020060184222140000715480383c00781c1603c0c284540101c1c5c100042c100081200c46451072034241006001e00c1441c1d04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 486018723 1250 486017473 486017479
    0x23010807060503060105070c0b030f0405060a021317070b0d05090606060c03090f011b030e040e010608060a0c030204030b07080912160201050d020d2f030712020702150a0c050705 78
    0x10146480c8002c0c01e03c0c03001034501410010001544000d221010a58800030a0001445035503403405d007080d2048075a083d10101c1c1c1c0b034021000815070b1194580292001400318105080712949000303001d103500c0110300302281030b500075204005115500305002c3c001c113038002400452107182c2121182c2c2030003c021710780d0380f00710b03000d10548414540000c00d0307980d00300042e80e0000302e40f85102c2c0180d85641031942c82c416280c425094100400d50700007a680d900e2036040d50140040c1014500035404d85032a8010080113500280000e001c22943e40c00030061006030b8100185800d0b203030784070041d044004584a8020401201c24040c1c2d186003082030318420345210801606000914110b00380d5079000241c0030341045004280480c80351401d904840030114001020041c0c0c600141c0d442d0940701a81c0c04c412703010780315403400110095056007103e01c2203100f40d0314180c42c44201c41410000390400c1c001603800c01184000c0200c1c0396000e000401762828261116005202d26181561410200d6001140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 486019973 1250 486018723 486018733
    0x503090f06010834260d050d0b0a03020d0b0a0e1b010f08010302031902040f020a031d01090c150e0301063c060c2105030412031e0c0207030204230108 66
    0x381250005184d0151580d1000f13040c560004207048101652007402c0e400c0041c003071080c0c001c0b01c242d048001040403203400d90f000c0c0003089441c010060908070b2840003a4101c080b0b04c00000001d83c500074825444041d08a000403c640f440d0707419890441e0502001d84192a92540c9610960b00092a4400c06030a4075100076107604690100b0780742c4150052105003100b80c921440210354642c0c100c8999449a01030464440710643c2005019100d034102d10303a00c11025440c60046d0003011302820a140760001090284a4a08601680d01200024078001003052401c0d1000d03882d40c081c05940000c00c0c01e41c981d8a801aa5440d009411042c003003422000880c000d448030540501c0d014034141203a4141c10b05210510603400d1449000040554114482c00c136181d09129064001c0301860003a806410342000400061005600321506400c2c001842c0c040804611142600f9070001c0e2509030b02c40c41501c1500b6501c0d80820262407038085001100714507000348801103000324640d24010b101100c0100b03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 486021223 1250 486019973 486020053
    0x10326031b0d02090d0501051501020d0804230102030403030b120d1202030408040803040902031f06021b031c09180510090504060b090c0c071e060503090f060108 71
    0x600c5000400d04016078400e030125804a1446040d4140d84007510060a60804043d913460014000c0104030340d1101003100c02d00e1078080310751000400e4800c180b4943c44040b51503c0d01c0d100c40b00031848150420103410318601004900800a0005d58080c503c41e4030007088444480d02042014460b080701840658050382511840982c000c0366100844081b0034016520703191410900024030444d002105036120001d0009120300d03070b690055214981d00d152880d2001c089845400d82102d03a4440d00005074043d81907080131080703540e0300c60841c030002400c8074094020f0b082940c0c18001c0320040400458600301080145d4407140c040d255041d01390364800c00c02c515080d01c920143c00d40c1d0303001e480000d550300c1000508008071544103620011004040e03030328034540240150340c2688081c000c0f41e80c43c0a2160000713203e00c6040c400b20041c0e04581c002c1800c0e02e04204044409400080034035400340721303400350f03001c0d45c41c07051102c54041d02d032000140075100914914040052100e854804c0d400307140c82215 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 486022473 1250 486021223 486021241
    0xc0d030c110a14070902121605090619180f03030e042703020102040b030f0a0b0f03070909080403021504080f120412060902090a0f1404050a060e1501032603 69
    0x208074100d90218030410b8400e500c10f0b40d01d28000c0c040d00034406083c4006a03185003014100d001c0d0348241c03140708807180c2050440208940c5070044101d06070700f040040c002d40701148008002010510003601d085c94054040c0c0545621054040d030110400d00c3d400c1c2d80030300506612609450902500350740a1062684403680c42d0010803058207030080050882508a0030103200390101c1e8010001c1000103504d03401e042429503034845c02540c0002c68107103080c52801560828407aa60b1080c2d80c020054080d003403400448130050080700314101c8604c5420000032005030364800c2e02d01c0d164113600c0300d1580ca4a003050400b13460164122410311082e400152081c020b460108129025a81460344100c50302c822854030002400e00110000d42c01210390081000c0d201031540b1a886c00004d000d8140207079040c030b1840341c01307241c800e07a03001d4516000320301c0d81408507000c0e40000c004002032a0482e00c1c07040c2070051001c92a85c003030300101d07903203102080003082503d140c04441d801101c40640c0c55107181402098 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 486023723 1250 486022473 486022483
    0x3070e0102190b070207080f03040608011203140f0c030301090204140a0806011a07080a02100f020405060f070f0b0c0c013611040f0f06060305190e0a06020c0d030c11 73
    0x7000e0084200004040c2c910a01402001f820031408446031034200b18041622a00180281c000041c4580c000103284c410b0030b8003820003550107072950700c0e80c0e200c1c402170301c0f1b2a58050710303030048800c50402080e07010703481c200300850092010707400043c0c0319070400d07124603000010000410b05c01d03500b02c00c041c40200310126902c1d04541e42d40c04603c03980c528002c4024514001c1d0384024001c0707800454400c06441e000b01c2c0207101d59200901c00c01c04d070300c20b00c1c0116040740550b0043c030382c1000003030001c440c0710204203005114203400350030300c07080103c900c0e561aa03e9400c2103c4006010502082c420200b40c0700340a202c0855440d600d800c00d41003850019404407a0b17001c40c4041894104030340d0041403001c18000c980407640c014005102c0f449070009808042d00c0d0141081c11070614149000440d0351080c400c0030f0003050030f101c20459204044001070040c003007581c8c080c0420f0048108400000304248010542c85400002a0030018120781001c0c1c200c0c0c0c2c451001c24280480d00303108103010000420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 486024973 1250 486023723 486023773
    0x5060c1005061f03051506160506090f3f070303060f03120309021315030209010e0606030c0a090513060510030e030d0e0f07030501092001020c090402040f0f0203070e0102 75
    0x50001031075541c4255041e5501c0c6d502c0b5480350090400035050804e0b44a5000804105005404903030182d1100c1480c281c1d6174a400e0a031203a150007806441201c1e80c4000300600e00700000f880c00a01c0011030403070a0a000800844100c44488006050010540c01d40640002407115a8504500510f19100c00f9004118400c119082566807003d002c11940c0701340c03a20b2402c00d0254020031041d500000c00f84400510340c04141d21800d041e6000141c840c8089500b980704d4603026202e10706584075900c03c1c0101e608140e0030170061109078a40441d01e40c0715000041c83c4418100c0021448a141c501071008074400d01c00e140b400c00d8100392420300010400400c803281c0d08202c18000941c1000303840c0c980d08181c1510140c1405024050000003400300c1500408003090203200d4245181c05c0e00011503407007030601c04400d405a007081c5280d9a49161088006a21500180001c940c00910140c90ba00721036040e010343c80484e60101c1840385043d8080e0038025071040138001012a02644103101c1c0180781140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 486026223 1250 486024973 486024977
    0xc0706110c0103020f070c060818012007080c010203160e0303070b0106110309120303070e2707120213060201200d090f0506070c02041109011706010201020405060c1005061f 76
    0xd5841c0d001c460345d412074100716000618404000c4d280c04006241d07910643d5002101500e243c0c1980c0180010301c40d25010b01d540d00c1038520460301a40c52142241c01c082000d6135045c10074031009803640400e000451250818103080c8629080b40303d8040c1200700200d900340d000343c1c014031030300c00000c810303c0f00c0905455890502015584125407514914031030340e24280c0e00188a04c2c0d80c1c202c2407000001031070041c0c40705d03100c6e85810071181052101c81700341240c4800411041c0b003040d100c00c90314081c41d20b4101109181c0111030311002c42c2c641050341e1000c805a68a0a03001e403003040002c2d820301ca00394200488500d00d0742c0300301100082a00600980408a1035241c2c0c3d4501d4a0030820b400c42e11090103940303c001d4504c1c5191880d006031212030804400e03800b6a040c055030440214001040300c580d800140c407000c9a01e5100003185c0350340200280782c10f043d1342d42080007103450703524040603050011146000704007418248005d00c0a403400900000c0c01141140c41001e62001d08003900101203c01d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 486027473 1250 486026223 486026227
    0xd0807081302061606020d0f110a0e011214060a060807050d02220e011a0415080406060506030133020307020904060902090c1207080f01150c06050a020c0706110c010302 74
    0x107400007070202c0c071400480c03013104c0c890207074940c0420040b900a0000c182d1040b1003000b8455800d0170141c02c5c1c6041160620807501d08000c0840303e24061021164070f82c0042c541041c45244583e1490100c420304401000d5a141c80070405c0110324002030414064055860314107a0390a164801511901805800101c01600072690610b10765110300e000c00e502c0d58407208041c0850756107007402c142c0c1d4000c2c0504001c8407554440310400c0c20346041103400b00c500d55401955911480c840072191600c000d001102d12641b140c01c001013580d9140041e60203800d8861411600c0566059582e240d00700e031024824003c00c84801000c52182c000c0152200280c041c1c50250080d522442e00000904070440001e501c004000c01380010645844082e0a200c00d071003030321018580760040107030744245045404201c85182c0384014040400c400e618444804443d003005200c1d180350365607003c2a1801103079481c084550105810700c0d0440308105090003005d0a0908500e61415245426201e102c0306003001c0c145900 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 486028723 1250 486027473 486027511
    0x9050901060807141801060903150209060f0705030c100c0201060501140706020a090801020c010c1409220b0409060e190804060810051f020c0103060b0702040506011709060106020d080708 82
    0x291550203114100c18140345515984c40e07d10103081c3c542c075800150784043c60b1851903d40481e00d03108480c0c00c108001c00040c01c229080724007601750b500c00101202c0c1400284404c0d005040b00f0040c4c4600c96840c80d0001c03640c8081c0c2d94000707084070a10303032052f4104052401c85448800f0f610048408103a0051030159541c181d18800b9a554100d940c84090158400100020950410f61002c0c031407480340e81d200c0f0024402c00858441c40d018443c072540d4040f0000622450b005603c001446482d1020303035022030b4584e60040000c0031101440015520700d43c903001c03a40200d21051101c144c3e480c0400585070202d055940310240140a40c0c0121000d010701d007004141400030008500c0c0c01418000c5c0b01004400c030004014010a0382c00444030302512407044440003035070007030240200752507980500030704040d416001c002c040c0201629150501a00c91421001e10002012981c400c500f583c004041951501e48002e2515030210080f1041115500511100c0342c0d20010b840e40240c46c1c142c1a05051903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 486029973 1250 486028723 486028729
    0x30f0228090e01031412030c0a180b0703080114100f0503040c0b0c100b0906030c0d02060d060e091218041d01020c010b0102060108031204030f110d090905090106080714 74
    0x41c9540103030400891150002081203001d110034400d20004000f910804464000218005d01096410303148002041c010518030070300c038101e420103941d44100c00c045450340c0d034004405e00d0340c040a401e038000b500c1000184502030b0404000c1880c0002a102c4034108412150010315000c0c520440c4410020004007050602520141400162400442c01030361555032f9202e441d9194500710b10f400d01281407500c14a00b6203403c04030a44a8030020300604030302d08018041001c0c2d42c400e10000c981c0f004050080c00c10340041445044043c252508007081341e410524245480c1c10103030380e01540c0c41d810410031010080c44901407514440002d540c0428548051020f500001e90303a0441c10782a580301141036025039034150480c1c60320071803e80950b0302d140d1300d4500441d1039208003c10000fa174000103000c03a000900c1003d203c05d11911f1443c15940700d0190180060524803054907450000d030440c001803003440810720030107400c0043d480003040315524020803243c869140384a031491050710081c1100b1151 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 486031223 1250 486029973 486029987
    0x90c0207050a080a2010050307081b030a270302010b030f0106030812070512070e0a1208220b0c0303010312180303111f0501260705060d090b090c01030f0228 69
    0x1500007071030030341b225683c03280040440c0c200302c82000003d80e204012400304100480301d500034400240942d880e61351101d000c500545400540c0b004407541c004820b10000c1000c440040400c2e1003607001152002c5048205440e2410b40103000d245640362460800008103e40d0840d0400d9000300b00058143d5101181640c060241310b85100b4294401010044516440f55500c0c1850400f2100402401e85440c5060864590300034000c02200b410060700300c034801002ea290b22078125995440340c105480702245840358200100c3c8503480d60000c80140204070f0802065a2248203038a88a0390720002c40040c000140c2e0544000350500082c41042d0620380001e212070844d0401c100303901d00024002034140001800c00b4070480c4104142d803d5a400d81d401d0106100301c03504482002003028505060401c4030b0b50b440b28440c60081591f5890f904005003100011a105400c140064425844442c0003d0207962a00d1001180144104001001580c241402010250f0100c1c0f100a0300c0661078401c2d5412 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 486032473 1250 486031223 486031283
    0x100903050c06040609120e090c1b070303030501030b3d050612150f1003150e040302010510060905100503041e05030c0c0901030c0611100204090c0207050a080a 70
    0x68014038007000207000403174100b0003100d8865185856514071500c800c41c0d00c20503016645600c06650004101188400405012616001c84a0700581d1102c049070f14070b400c3c00c5078411000320342c0302d0f0010400c1c03100540301c0326448042a01021031009400414483c080100c100241140c1d549441c1c0b650004000316541001d007802170308095541e4105404081002011101d087c01d07040e42c904518140c0c1810500c1d1420309001403e2b02c00304d040718035400c2d405805590700726081038840c110000741250b04202c0503801503000381c0001509081c402c0c0310301d0a0070041c0d004a002d20000410401668032540c0c40c010b021f07121458601d84030303116480c1c401c0c45142142c00c00800b00358540006010b0000100040c40c4078000c0f5070407186031201900038450004400d10026020014207282008000d0041803510302e1001c1c0e010030783d4103034107034401558201c0c0c00c00d82110f800e00307a0328580c3c1c40115804100c513801404084541c80b10b4136103000071466030b803e50014011f00803d0680511500010180001850 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 486033723 1250 486032473 486032497
    0x30608030408010e0106081209060d0e010906050406150503061605040305152211130e01140610020a150c02030d02040b0d32070c06110705160810090305 67
    0x19650351560041d0284c10002c41600c100c5d403a2450004040c40c0000d0b0700001188000c0c5c0d0203007071a034a8020440b10780c02101e4265405500c0b0410840003500078414040501c0c4910800905410142400c0b01214007045a581c502954000144032580e000111294401d24100d03001c0107983c001e550480702402075500041c40f031f02c00c0b224441340c00703880c030400310703208a03800085440d00a0703840941050500c0e00e0035014005032a0b070001d460351030070320440c08030354818031131804600301d809850a14211b902d002c130004421441d03503040c82914500240440113000180c4020800114561130301060000d848401415203940c03030785200d1107940280305603082000f030a14110345440d0740d85c2c8a004542e0142e40040c030360b1440d00a907100c101120300250703018501c04581d40140820b446400c0c608810005c1d00b0b80341885840340e82040043c0f0303980600d00807889020a601d456044130324010385091102000c40884615000d03040c000c015000403202d28418080001048010560509490910582c01d4420b5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 486034973 1250 486033723 486033727
    0x130503030d0c030c051603030209060405120d030c0e01080609060a0e010b19090b03270f070519050d11010306170a051c0f1d060408061807051f03060803 67
    0x1520421079024000c2d00981d80c078148090121048100c60510641c25000f80d018030b52648800424030985c05441121005018145015103403800198440754461204001d0780c00080740c2c41c866a49402a41c02c80e03122030600c4c0805104007000a484420010b000360b018a802200098050743d0341d05604004022010615405584681103900d0f039500c07101c1080203194090040d0308e41e4520400c60402203400491076a42180c0b540725596a18083c207000a513501061781040c00000c840c14040443c0d103540c0300b001415611720745010301c000e940510404200900b03015400b00415154040382c800c40310340c8491a101c4440d050b000582c000c0056030046c0008001c000c0c595034142000103001c8a00746e001e401281c0b40d000c003221130007129214680d400b6000851014144595034000e413980c0c10040b00c0c02c40c800405000080215003660003e601442065100b032051040e0800b20010ba20740099008025000403802c03c40402e8260000740002d05103400e07000d294046091080e071101014101080c06c1c1c83d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 486036223 1250 486034973 486034987
    0xa05120604061a0c0d080c0d0c0e0a0803040501270e040305070b0a05060f040c050d0e01180b0f0109150509061804110411180d050a050607080414030304021513050303 73
    0x10140c029903d200320358454800d40e01e41007070003400c031b4074810300e81030f200c840c0f03852000c24038600580380b50048801442841e00c51104070390f4410349403401401400b40207644852400b00010015462841c07052071030070300c1000f0304124800c0501c403d000c0e22a1030551500588a514084030144501800900041101e109010010070b0f82d8000e540541c2c0708603651850741c6a00300c02c201c2111464001c54001c603d04000c50140e81c80160421507a006164000040c0800160210024103c101c81d08448043e0140104803a140d948000d160241c800f80740308106800c040b06851301c84503864003800e84145843c8000850590b01e0103e00000700160300c24020050515203086400c00c40250310301445242884020744d0040c04241c15201e1168000c1183e074954164402800002803180c241682e042c001c415191000c14410000300e40030f40701603aa0002c1500d050b08101c0b0051902c1c0d03590a100b03410420a2201694403840030407400462089440d41d01e41c0280100100c940c071070f50209400d804049410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 486037473 1250 486036223 486036269
    0x8070302060c2e0c050c060403181205030d050c070c0506031b070b0108010b0f0f090406092a06030605011709190f020a050301050403050403080f09061611060a0512060406 75
    0x800f00c40c01d0b080205201103c0c44190030780d52406070f03a220b450554003120004021a100b4544480c40c0c65410711003c5806860304103100035415426010313507440c0d10015a001c1041000e2081951140921100350f0514a00340d0f6000c203504810320520b885800f0100110780700801002c0c540d4070307200915805d80d955504914014032a100244141e103c2c2e940b80c42d1030303038000b4101842d03285092800201809401524881004071411002d001540c01603a038035200d03000206000d684031401040074081d2210302c00301c950b0140441b003040c0c00401c209420840200700d2a41c1041c8880001d806200c8900d81a517500300307103c2d2408200302c5080b095610304030382e04410300210843c0c010060740280e441c20382c49a107900c00c0c5400d0390004e0310028000b440802040000c82c0c11400036110b40c1d030f82c802c0c3d074520b0001d00400154241c0c01aa0800c00c1401d03c0c0714001c810032207a511a030310303039400c1a10590300701a003450000e0700c01d01031007000900300c00c1220000360040c2d03195400305001d0081b10b600d207003000c06980b41d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 486038723 1250 486037473 486037543
    0x8150c090316090c0210060b0a05030912070f140312060607050a020301050109140a050c04061b120807030515220603120504080d0e0d0201030b01020a0b04031d090108070302060c 78
    0x481310140c02440502c9444072614045c9000b92040445101d14155a980c0120740a40c40100781c00c40902035403030a000c1c64a100e1b4010a010cd01a80002c82407840380e0038481050411381040c1c2107190f008000400c83d0417140102980e019008607900740d101c6069040090508000d400000d506518007030020440303030720503405111f480c01511040d006681c4c440000c8000c0b42e40136102c00ca14074000340820402036224494411000c1a00b02034583c20346c0160303461032440105002010041414242004031a96161090300d84c07041c000320054001e6540c40300440c0f0244000780c01042315441a0441200003401508544015540000440c18582c003100005000fa085030151100c94060309680c51640e51040b20794000c0d400004141c0380c0c0020081c1d00640050a40f0004281907008100c000380c080b40002d01402d10440c00303034480c041d000b0190300542140715a2102420700c42c20030180140103000300064110143c6c3e5050301c403241d441002030a9640f03400c850150301154144020040c030f28429100c20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 486039973 1250 486038723 486038741
    0x20703201e0610090908031b0d0f020717070f080a170903190207063c0c0210030e0606130e0706050909071b12091a031008150c09031609 60
    0x4056059104c400035800c0d02c910318409001400140041440841c00c0d0029100c0c0b511400d180914208250405038241c0d204885207074002540401c80d8402d02840031000039504440e0102c0a142448550700c920010b08107030380241800070f01103a0343c40d901c0e00030031001d82a41c8100c0c02c1c2421510b86404455601c2d401680e05051004000359280c0d91103000080100c143c800549809202c004118074644150b2200c0000c620340c4900002803050200b250301d060f0880f4411551388807090221401807084114078580a0000c0500d8807103228140301020952a42010003180c2c2c0f20a036148210040018000c1440004084d0090410000d2440c0e0840d0084c0140c104c10380e0402290780d1030142c10360300050014040701405000d08610000980140c48004511045d13003000e0b01551303114400013080104520f101d13260307544000180000000e09001ca00c0c0100808c034020f060000c40000f0452000b4000b0b841800075070b00108001d00c46540c00e2040c03641c0680e4000300c881e04241c0d9040c4240280896003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 486041223 1250 486039973 486039991
    0xe1021081b1b01050a050d090201090308040603050a0501080d090b030405010e0106150906140d0207031107090e070e041725030804060c0c03140a03020904050f1009020703201e06 78
    0x1a403000302c99406501591800803840e2641802c00325031803c0f1101030144148200d0420041400100c0040c040001400241c83c26903000140380c03401611000c121001a088424964066825440c200398442004c0301520700940500c3d869444a00d0301c3ca004d0b040b0f100c0c507154a542441e0010a2000014925200c4411280c1d20f00e9240d50307594000340d4882c0b0310088000511103040007100c20646c1527400411001d0711034503182c0e441c03644221041e401c1100c15080260100d80b100d00301c4604403410005100a040506600c4615091598540030f401404040401c0095404260107400b000b2420780051a2030500724480400d0075103240041a00404071002c4500398540042c907110503210340c007030103201e40d0f054841e040d00c000113514640ca0ba411102c00c450400d502080200e0113502c41e80501d03800349069821403801410700340b00c0401c401005030083e600c000d1040c4201000300b68808020125405000244200019848690341c10b141112824605a0310a000040d071081c10014903144104d04031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 486042473 1250 486041223 486041263
    0x160c05180f0f0906010e25080108010605040b06041403030c03121e100501271d070c031403100302060a0c020f180a0209040e0d08010e1021081b 63
    0x754581e54081c0d00756080f031481d902500c01030184000d89580c9507000502c14400e60040807030500c406800c40020480d400c00074442200401c84188240107880c05048112020300c1442c00810104003503005038403a00d402d070402828000020b890610855200c2d00e080d8080d01c0d81c4002000046c514040c05441c3c1030038541e2400b070701006c52210190494042e00c607041410140f507142200466400c202095010079003980c4482c0e901c00021246e1880e002001141d03800041e000c0c51036040690901c0040a000a1249008840001035030052111a030100d9044401d030710b80c2ca90204103040c2d20001e410094104c0800584103c10540101803e0701152003110400c1114100d202404241d90700380c403404818407035000211300c091000f0740141443d44405000080d40c1c0c0d481200080c0750030000d0a042022030310700001444411044491564444402c0312540642440d2030303400e50741c941d558140c1024403001009020200484101280c08081c02d41d002164191407110303006448100507880c1104107104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 486043723 1250 486042473 486042481
    0x504110310270305031b0405030f0703051c021f0b0402030a0b0312040b09041802030a0309181b0804061409010f0e0a050d0f090305070b18011103160c05180f 69
    0x2240c10502440e8990746984c2075803a405071404010700d013240e480d0815a000d0001013940d0b2020050250a115900022f00e03800345503003800c07400c000b0034041008112010049401e1042d800043d122480da404c110a03a04c0c131060032400e00000d1400100144d40240000180b010a001c070340c205041084044003503c0c21400f151104480e540304512841841c44d00074002c1d03407401c1c9040d80c040003d1201c490408094041140e0010b82003942031403048003c500440b0050040e02840004c030000c0307907d4001b007002107507103110703401a4500c0c42c2c040e05020801800e000808005050700140103042541e0100842c2d410680ca0842c042d10301002000350451609446100000c4000703481d211943c0c0200103441c040400d01001c4074407008442e0a0000c0c0708044c84000001002006030320028988031088540300c81a1181b442c0b1400c1408900c141081a44a81d28a0500b0088112044640a0010315001c00807624101c80c2c1c03088154410f43d07215828810f1402c0a00d00c2004152003a184580340211580d2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 486044973 1250 486043723 486043781
    0x3120105031c081f0905011e0e1003081c060329060904021009120f020a0611070e0601110307060f060b03010b0a03020f0702040e160501050a020c040504110310 70
    0xa001603004009590350703011440e0200e811004203c140c40124030b014485440361170260540318280c0c86a2240038030156042d4180740230a4500015002c6a100c0c02c0044c20f20301000b48100c02c16000c054000c0c14001001c6d520525480c6040100c0c1d0340e044024000c0643d6404c00102e04103040d418051005c1c5056a24000c00c0004140385100c1d5100508140d2130b5180c0350240146605416514820710041080c0852102c0c42320ba900031b0a1072007442d01d1001140d040c41031080c900c1c803690109052100782074201d5160301c8040707441026034040c0c03d240b244659801c4012210664191417092490200103186020b100ba1900580041155a00700f4461141e0f50103420845100034801e100e0900310912120481a101c1e030018000d646110440b1341c10a15070790000b504640015446450710361102d19901c0e01c180b100c4a000c401403100342031140c03e281c0038000207501d40113100080340c80b4584c0c40340094204090b47c1543c001440c8050700700d509400090710b04e10001d0120940d46005909102c600b010090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 486046223 1250 486044973 486045013
    0x10312050903100b0a08161e03030c0b151503100e01061e030605040e0c0f010809030a0c0c09141b040f05042003070c060b030a0308041202030403050312010503 70
    0x420060020180384603c4a034580c0242040c241c4540c1c0144540c00002c1c04460801c20b000e40d03004a98040c1140b18580748921a250341c2614810b100c0d100d20107020000310382c0014074882c5103500a0100055640c4160340706ea4286130140100341e0241070424155503808445015510610036025141880358807102c0111803403400b4402c580018454090191082c80d04081c800303880211400d01080f100e4444000806a918544445401740c1c0300050301d04240c5440c0c0240401d1030360a0a000c12103060004a076500da1290f008000e05211010f20a94204100e0301c1c903010080084000400c852417038106009901c0c181900c541100d6004010200101900707502128100c8190000d10380e803c910f0842440042d04ca803828010042c141c001000070035282036401140b18081d00e0b51f03044c010203068a001c1c003c858050460394001c0d0320850010000135041080d0a4000e030300040514100c10440e20300701d16501c101d403c010b0044c00040b42141090005030400c605a64044040e100300c45a91003405105c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 486047473 1250 486046223 486046237
    0x40501030506060613090921030b30030d02041d0f01060f020c0d0302031e090a0e040512040f1401020f0d030e072403060b160b1306050f01031205 64
    0x81d00b0200100c0c10919128004008880381181800c081e10756590700f01d41104c1c101e40c0207403403800300b404008804000c64894a0244600307800c2c200122480c01d800f0501d80f408460790041c4021489200300c400307242c0e50407940303a0501420110f1f81d851803072070107800194000d0f2140040c84600007201081c082c07110407544c0e2064200c034903402080ea1805104650350404c8c411050300b54014100d0b1807506440d0305541c8010140290025540c44e50020381842d0089656200800800c10901407101c203580c030079052804a03038000d00c0d203030400c2e21681869420400a1241a84071000c0060300140318001d41c1c2585003120404000311400d100140c0042e40c6507541c1c11010611a0803a80403050790b14043c0d84500c80510040d002c840340d41c1d4541007142c07152403028000d8002c00010030100c2180541c180900406402c40c4041107040c0140031a6a00d00e00e808044001c049841c0768001498103d40d203000242c0b80d5820000c180505e040100648007800420f000580c2d40100035000d19a46034056800c803041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 486048723 1250 486047473 486047483
    0x4290307080a111206280b03070506090616050f01050109230709080a061d072715170c01030b01090506030a0603050f030d0b010305010e0711010905011b0e04050103 72
    0x5142400e0380d800360211115000207501c00850742104041d070904004a92045002010014040c06101411008401c2843c0c03080b06c00303414281d02a40700c0e02c0103d003980c01c94009031401502c1303a906500143c00c0340900003030b44c40f99801100484051100c0010301042c0d48100714020400740c3d8031020410300f80d51552000c020000100c06800c0d00032052295002d80c060b5003850018005501ea100d018200307020721106451982c3c48070544030f10241c00b01030782c0700780d80d00940c011b10145140c40201c4600d41c508194001d210401d007a0705801d01000d03074010520405007140d075101070907240d240503080104959824403d0f48941018a012075020380f14111150005840351a03405180c0350420555500c01004143c040352184e000000182041208010b2802c00d00c000d541c45400007090032048130b40070080c1904041c2060300402150400005082e0403d000c0d1424100d003443c00c264480c09445d405000a0241d0302e88100c0211900401c4c081001c071001907640c00c0500c2502030700304411f83ea820301020b00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 486049973 1250 486048723 486048733
    0x10c201c170f25031b180503030c0a120302040f0909060b121b010e1c0213091707030c14030414030114060607140714100516021207050429030708 64
    0x140849003220000c1e543d0348a240114a2510b42c40c0500c070303500c1c0c02c1c9a5090104604007000d50004041c0190980502405d03401141095460140240da42110010141011201080b141c007254829011a030290610281d00f030a85552040b00a004128000e019038159181c501303144e00515207811300344221103590340204a0040b082c0c036041c51820100e6442c60500041a40540094407084001035a0944484920041d0442401406407a0005901d061180c0340b61050400020b4160101c0314020044912115140c0302e0b18601a9400b000c80000640107021141c89154000e500100074001d560006100f40d15180c1500149820b98594290700d2201c43c501c10300254543c142400501450b03400b9070301c84426080e041c21b40f20300b410303490b801c007000b160440f96000e10181028406404c00c0d0100e0702c0d01b01d260140f020000c40700b038524650005e05c100081424100b030004200030000207403100500402c404e284a0550384c01f500840d441e1448180100c030301441031840d010468008507040714020380 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 486051223 1250 486049973 486050011
    0x30307120e06070f12090b040f0b06030a03020319051c05060f0607080301050607060902120d030c0c11010f0915021c1e050d0f050a09020a0503010c201c170f 69
    0x3603a10300e444452000c3c0155104046c00108280f03092450207140941d40041d41b89601d81022010464000c200e5406a4442e01f5440000780c3d000040b184003a031818101d105600c07000c83c0c00c44042c81816001c84140e0f00402150031020340e950310440c0586030844101089242c46414014140030b00d140240c40402c05000400081c20700304002c09103e40705d00c600045850060380000e105410101200f5101c3e4018420207508a402d48602540486c9908000f41d00c22511383c0c0f15035186084620403170401000a12520741a4084c0c3c8410002d40407034500401c03040500640203603a244109a80218502c0d24580d50312018000c0c81120000100b03112540a190008601611581e0142c0b4008108555031100e84601c02c2c0103100f021301078803240f100494582c0c00d900400c101603907240c0040c0d1199150580d016002038210207104440891500c1c94495145480300060a00880061043d0b486100d07401ca8010309500030050303d800100784400e0a04c80c0c542d09824070141e1003c8030000e602c40c1d0814546 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 486052473 1250 486051223 486051227
    0x30c0607031215030f03021209090402100c0b0901231b070503040504060311090a0b06090f030712080a17010b04051e10030e0717030706051008030307120e06070f 71
    0x70040c41c1280d0703001c50751640e00f060080d40c04450764030980b182000041410101907061080704007103030142c078400d8207001c0814000743c10008050002803060031499080c004080c0a002e090950355001100001d0520304204005c2c0030f04001807030410079110901e0440540c1c100403622034060001c3e018078507102001c03409424040c0c1e02084e019151440288000543c50755030303008100c00341d1322886003c4010b891041c01c1c4001c440c0081c0c00b400140342082d5540305682c4544007562100f4400326240c0c880d2441c01d0020071305105054000301100d052401d850800c1c0440b90004104401940c4c2d10b000c2c0c800440410b00b400c41c1405e025800f02c01074100010400780c0b42900d80c59113201504040301c1b5007845040c0000304440282100340e00800c0e00c8241c904000c80d030621518004106d00e2100d80806030036007041c40e41381d102e4900e0062104e1398035004150011100c4030f000002e0a12882102e80c7e9082040e4003421012080e058000c0b001d082130070580c0710500c0845d540d8001d00d415113406400396006881 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 486053723 1250 486052473 486052487
    0x18051b120312041403072103021806090a09090602030601020c06070309140a080610080d05070302100905030f040e150a0e0f09250f0b0a170c0715020306010e030c060703 74
    0x20a031071403601c4201ca800303048030520003031034501e02c00c3e10301e40c1080b401c140742541581c41c0b107d0b10f030040c18814401502009070b284192001c1800c01c031402c40e42e4001c044000fa40c0302c0b003c1e40151102c189001c2c5100c0412007194000c5000b10000d80840c0c11034828141041030078800c0f02c0c0c00a000600d00642003040c440d9600b00c401d06140b0082c80182c40d1512100c21a10700141141c00f0024004800010030103030794140481c80c071030161481c22600e0001d01b81c4000e5507130f03801c5c09900c3d07500590390303160030060050600c00d95901582920f281581c0f035644040345002c00798107544c1280300e0903807503104003960b1804000c3c0400302d64241c135101000b942d6440394007801c0000204004441d000340007912a6520203145e81104941e040042c80c01e076541442005c25203c690798002a420a404000c40303030011303800518131400101360303450b0f105040e511200c0c03484150041003402810800289500b10700d43c481c030740180d8031400c03003071703865040715003aa000300b681c0d41c0304103180b0a8000380b04001010120344a4030f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 486054973 1250 486053723 486053731
    0x6022208030720091f060908070b070c050a0e071805010c0f0218010807090f05010602070312180e04060e06250201110c150a1506030c020118051b120312 67
    0xb0b00b81e99003480350008203124010403a241e17403c29001d003c1e401482800382412402a108038a010b40c01242003407002035071040c45015070041e1400200c6c802c410030128480c40d1028160240240201550300c400012030000103031690004a41c492600301d41001c01c2ca0301820817240144c6d6030085480c4543c641300002507807840c003a604100b24041c18003225807a0081710f0300900042004108091404002c0c0302201c05c1c1030f8040ea1150f041c075004211b015400100c0b1300c144d0390451602c0000c440c6208003030b5104288071000c124519131035040050001104030649215600410050201400440c02c481c0c4560080300c1e40c08042074045d1500b1a60201041d118242061074000001c202040038082101c42e004203c0405265021410701c68841500c003699542120b2885010300020910b2a9842c04d140164043c0004060f51550140d00c400d00c00d4001c90b0307800c0c050102c0d0401c2c40c0b41c5410642c0c0c45008591400708040c450810b200c10508060160a555410010155083ca042c1d40f0300103a034554090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 486056223 1250 486054973 486055013
    0x70302280609030906030c1701050909031b07090b06070203120c0a0c080f0c030703080f030c0405060a0c02100e1c060905030d0209040c080c0703111009060222080307 73
    0x108060015880b8440e90001a000380c0f00c0e40c40326840c4c114004d09030f86e42c0515030740c00c0008044000724010f440c00e08941c15500c0c11290080702d5601e4403000c2e480c5020b80290064008188940c1c00c051040c0410a0010b80722440320500900000d48248940f503c50b55000a4041c2d11040c0341c00381c5008204050515400d0800603220554800d0f11040044201900010586d8014203503560000c0c000f0080c10845610540103004024a1500c030705002d8040e10316000c845881c000009400280104111800703000010061900d41441240040551000010403401480100310794404503000d008905241c01c0d009283c0d0440b0036404410a5941600340c3c0c0859100e40c80c0d042c0040003e10601c00361012000340b1000584484201d42000180c035000c0704d85030103100301c41060081c80c19006040700c20742e50b01820000001c1d405030804600d0150307003141d00c0e400303549000d80c18000c0018039002006040385070300d210f9410140b040c00301d0058803682e104001417503004100380b60014035a002c802400352010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 486057473 1250 486056223 486056293
    0xc1509040c030f022215020604080702030a121101050c03130204020c0a050129041a04020c1606030c02072408040f020d060c0318031d0a0f0b0915070302 67
    0x4000708242d170044542c001d880e000c14040100c01411030000c16005200310ba000001e50b0a172804007039281c40d405080078013605030008615040d508c08010103440e01d944180600c1010441a0000f0040c008200c800e00107542003401007a030b10101002541d0051004240940c3c0b144815803c00c0000d500040c2041d001c1d019980090000c180d0070710540038001c0241540440c042820f017070861a5030551800c2611952404c801046c120026038181d400d4a8015100140c0c0d8540b1607080750301e444110010750710328186100c40412041d0b4190030020700740c0a90f800315442962504202c082090040541070b01e482c2242d454003100a00c505010f503002030040f400c0000c00c40e0950045001541e603546c1c1901c02a443d01001203003113a06101e06074850704140c101c00b0b0101e01c643d8000701003250074503942c145551a480713541c8560fa03078048120010b0903440e211901c03003036640300d003059503410207100648a6004d4454042420b1080002c6900c05030f0700d030b07006d01940310003021003000f400001c40d0004500010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 486058723 1250 486057473 486057491
    0x70f020a05010e0f0f06010b18130524030105360105010602070e0105010242040501060603140f16090503010f060806071d0f03030702061207020c1509040c03 69
    0x8288204241001140d004d414401c6141400c9441e0844000517962690b0121004100c000058001c1d180d030603408000c8040160481400036401e60f5516005401a40c40c2c1418840c001c141403895102601c45d14a0f46805226000100b508071141200c0c15a4441c95120b07240300507404003c1582c1d0703001d0341501062022182c015486003198800d03000341c000340e407020360248090344e80b210301203004000910042c120048130585a0000030711001c81d40321010313028000d940140280d031590140407000d400c0011007074a45404c00358041c0c0420310070b03070703000ca89000700607544025a0a40640b107895043e1809226440d2310581144100c2a04a100d0400070003510220b520f5801380207242028035540350229100c3d040c1000c4030305107500174000d542440b402003002c9203500e240c004481089102212020040064000132a05600c20000000d501141c0064210300ba001034418490103818280d0850f070b05c500c40c0700103014106400c01a1000200744c14408101e8519241d00100d1140b4050301e004204069 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 486059973 1250 486058723 486058733
    0xb0a0b16050f0d2c010c02131112070c080a050309070b0c0d121e0f090f12020f0c09010905040302160605091c0305070312090b0f07030e06040b070f020a 67
    0x2240c05200554002c4060f504599600021101d20f106406003002450320314546544503480034061080d051000c620144810b66840703e1108498501641c01030000e22280500030a103a0b22641050b058082c06001060040d0300c525500710f50141c0c000103140c5801820340040d00e00c6e0b000104410303890311681001080031030361000942030603003008000305050441100041c01d2100c890341c1080480e0b14003030202c1540c60a1850584aa580014000074981104503c45002d00362404003e0140c510100d0880e080180c0120902840d0b54160f0076520580354540c000d54032a40c418031401e9004289200601060000e43e0046030441d110780101c03010001e5110300040390320b5540d4030490100340c021500c0219800c04501030307103030a0340080700e20102d41d003143c1c0c0181a40c01401400740401210600c1104085499488410199000025030a062034101845074066001320f4100002a080800d800c00c85403000079028000c1da8800343ca03020303c1ea148402110b0003482a101181148158401500851 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 486061223 1250 486059973 486059983
    0x7020d0606150e040b010309050c0d0c0f0303020c01170f0411011b1101020c01051c020a11011e0b1c06110906270d0309060302030705070206030703060906090b0a0b1605 74
    0x1200b207031582e420890511041008440d5590314040c141400e1400900004002140800f11080121201c411922443c02e04101d83d800542041044c251220717004000e01d13400068510800340e090ba40c403980d024201410995640d819981100741064220114002030aa4030f4260742c581c42c10701d0555030703a40814090400381131560b0700a481c02c54403803490403200d580c1444008420780c000c5c01c04030304d082000424041010040305455100039070228600c0c160510034000101600c0200c0c00078017400710042207071862640c400c4884140689020408100303070400000c80d420103070700701444414003d50364a816000e0700302c0d98004040c180c42003100782020b540341005231820041003511110328201801c10b00502501c1890010710a1711000c00343e10029a00202100540c1d00510740940c890311824015105030140001c0258441004020031940e81e40c140e1008003280c225000c144425a41d03800d014040b41c07181030b039040d00039030085014080c0000e81c10040c000701703c2c100d110500010729512424204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 486062473 1250 486061223 486061259
    0x60a020906072a08030703020615010306080d110105100302060d11160b040203010c051201060c1502121b090303090f060706050103050604030e0108131211060702030a170601020307020d0606 83
    0x200e040e40403c1c11001000c010900d019101c03003070040d46030200644000c2c0d030710a80180401e02543cad1000700c2e01c03402d0b403007070300440000e15511040740c1c031019403040e018007100b18881a0800f00d40c81c01000514060001038400105d80d006800717039140c003a517824030001920000703502108612080001d00782c1024400850002c29006000f1361a42c2d00f058030400d400c0d180c00704107440410009203c0c1041c808800b10030681118590f041a56225606241c003070700c0c2403410b065640301d243c404180601040500400180315030005c24501160120115181c0c00c603000341c1c415550582c3c4184546941c40c180440c040500c050000c14050411800345d550100790381d0300341c00032205900040180000c164100041c3c240d500000d0030030034503074030340090069030843e41c180d009047c40107080000030101e4000e1403540144054a800d41c2c449141c0b03200c01955941c880e02c031000000e84082080e070300300d500c400e8010b0b001c0d110590280d45010f04503001c00080300c2ca03824007682c21907504d003400181040f50072882000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 486063723 1250 486062473 486062513
    0x3030b03100212090c0f06180303280801060503270118171204030e060d0507031b031140141f080a06081b03071502060a02090607 57
    0xa24102e800107400b03c02c6010740840d0240d07000190304410f66684050707401c20140280c03000c540711003043c03090010b0b4240140070b0795003500000404801c880c58000001514402c3c10080c01060260400c046440d0f550074892000001c00a1011a01c0e00250403010999001030040c5845010310100d0401d003121868000384040c3e4842003200010130009070000780400400910710ba04100c00c2401094103100020001010800003102a1080f641c902080e40d0b424002c031541000103161041002e40208050700303e881c5803607143d00f0b80c94500c920034008c0c1a041c2182c05200360405094100e03400c031200106192080c102c0003d044035101e071307503041c80000b81c01c420041001c005a240503d5001c25203c040c1c4618012151029a030300342045807602003003607285ea4508031000b952240d405000030074154208090300c0c049e1018811150b51122940c15220000302e007500c1d40d550751410040001c07600c00341503002503001140002d4000009502609415030040d000307500d0645140e03540d031200c611111414030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 486064973 1250 486063723 486063727
    0x9020a0b1305010203030403231c0c020c030a0f060b0a030b100504150501050a0e0103020c1920010c03050d200c0f0f0304050d1707050307030f18090903030b031002 72
    0x1003001c0507407034601c00900007800554918241910014050540c8400071100d080003c48030300c2ca004815412134080c3e89440640d11501c0031900d4210010300301c01002030740140310f80ca02d0b51000e440c01044403450954003018100c1c03030020a40d11940039081c07000d0720030741c0209840000070102b0519400d0501c9424903510310004503040204000484415501111000c80e0b60348050242c3c0c1d800002b10b40d460b034003904103002124178182c0100c0c080c0c4a940c01803040d900070742a86800ea41c10400340d05c650184942400398450340c101000b40c0110501c0c01005000034407174480c410200f0b00500040400d074110400115101c40c0c50721420b40802003030004900c04540020b00c00030610310900840028288800251800719030302034910760350b07000d2170007524481d9020102c460100081c0515034450b80e006d5103011900d0300441e040054032a049100203402050241d114041304a1081880c0d007980f0050a400944d82c9040c840d40c0002001200e6086040c19500e141c2540e4950701044403a66801214601603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 486066223 1250 486064973 486064987
    0x20904050f0303070230120a09050304090c080c09150d0f021b06060d08030a0c09030b010602031c15210b0c0d1d06060f13050c272209020a0b 62
    0x30507442400301b200310102c0c01d0028440080003030401212205210082c0a42c655101c408014000b840344c080c00030894480010b00040481c01c6801002003070341d090303c54540326070b04c000c80f0000341d01c9000407055008001c540c0003103006465601605070707140481d0f0002026a40c90b03600f07070200d912041d8400164001960915100181009800d41c840c0040d00c1000003a0b44c0f40c1d483c18040e0002070f00e24048161035084104021f4881e00248000315044900000c182d6551040a5125807181c8164045d0705140501203111510078022911001070280040440b00d2800d85544820107400e01e19066055440409001207201224403a00071601a0016030f5111341c0c46001c082125264050402d00724006503141c101042c02156482d8448410341717030701408404c4038002810240e0070704039400c21145401d051240d90150352020303012000141d41c8030403000c901108101290041581141c1d80f0140020303079255a011100c2489080415200020420700e17a641c0c00284040c03100d40250030340c524041203907 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 486067473 1250 486066223 486066253
    0x60a06020a0b070305090f0102190e0604030309140103181a09070f030f03090810050403030b0906030a11031c02030316030b01020d11030d050106020a030e01020712020904050f03030702 81
    0x52140380014900110a6a0b860304a07503002007181c1c00741a55240040c207a2817060001c0003104440300002c5580300070440403007822440000120b000aa00c2c2404c200c1942401000c0f40c0a49406449810409140041e02c00021820303a00305030405441c2e416140320281d403221001d088038826a148911082c043c0045220480024507500f0198045882040707200603210059050ba40c00005e207600000d52401c0503103199840d680320205610a68820548892190b88540e002d00d100f07a41c203020210301e030000c00c00c03803107015100c00e9032680240c1410f400042c501c101d161207054018051700d10b41042c41400c84150030340e046041026030000400c1002c1b4149441c10719008a0f2641410814103540740d000030b40d40c500c05d2590005115020880c0c0740540c004200360381d200c0302c0c4200184440d40c2c54460094545a0740d4100720003049a810401c0718540c0041480015600b1500000003e110700d6001c121200e500030300182c407580140500d499102c48180000c1d0b04c9140190010300c005a444210 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 486068723 1250 486067473 486067489
    0xb03040210080c040303030b06091002060403020c10051b010f110406080603032104110d0c0602011d0615060f0d0603020312120606090f0916110c060d020c032106 71
    0x404100b22404040002010b1200266020389800d40303000904484004040303401845184901750780700408801c0d0528843c0d0024107140308a00c2035081c2c546500e00311052240440e81082180041a0144140c0464514514060982d586008004a00c079049a413a03401120300050307288020070000a000d1100b207410030030868210b20305034000c61070301c5a103110080c03000300103444110b00842140e01080038050341c0f55600c0da000c030b00101021514111441e027540754502e40e106110155080a98041c0e101041d001e01c20030303c4103100d02414040d601c0020713005030b0518410916511180510828500b00d10540103891310b200480030000d00b00e82140100741c0341440076180c11402c04010811050982c01303048040c0d03000007082d0ba240f9140ca68140000d82906661100d00c0c2d000f0040102304141001d0b4080e000f0300b1600c80307441c4c514002da5041007041c1c89074079020b05181c0003001008050700c00412039000b420481d0341d80c03003500d04040c001c20745d003407420301e02c041c0c10380350b45c198001402003d16140c0d072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 486069973 1250 486068723 486068749
    0x906030c1205182107023001091e050d08131703010501090b16150906020309100b0d0c030b04080c0f03040302030d0f0e040c1b080c0606010f0206040b0705130b030402 73
    0x303200c00d40019007000340c1e9062143d044003c0c000c005010300345401241120803030581c590840d88412504201187e42402099400d4050b248001c400d80380c5010700ca4030a0005070003a402c000a40314556030705109481100000c1c11301e01040141065220108289000e11400200c0c0703280380550300c2d4500000103044594030340094003d00d8041100442100444c0d41800c00d49900c180c003400d8440380c0e40051401031207031601c084c06650000041000d404e40c00708604041c040e040608000d084400d80038000a155104c1004103000c25840040c404103a00e0740100f540b1178480e04001b031402c00c56031b00184c18040040d602800543c008101070085150a0003104028402032900c111021104540100210040c070950b500403070361101c2a1985502c00d0161040500c84001c43c1c3c004101c0d980b4000d87c041d07000b00041d285900640020039210341c441c99241c2c0d180035403640104003070b403a0303500c580300024800b800c02400c0c09810006d0300b03803502c450b0320100014418002d1807626450315006001e10401119 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 486071223 1250 486069973 486070003
    0x112a0705010908071202060f0309012412031407021012050c090f060c1018022d011812140d2c040f02040906030210020c010906030c120518 61
    0x8144446400080c61104917900c000c49455038000038000b00d06c861240740d03040c04800000100300b25030403c054001c0d035407104204800000c6410024000041e05225000d804402d0b5120304130314010034840ca51031080d0b0031043c2c0e03240e440d00c06a6400101d070144d1908458000c109010b80d08a00c200103407040c41c3d8070080b0942094074080f1410000341c42640108041407090002243c2c141c808502007002680c00081907800f003008140d022400078081801010481c0300341d5111800d0700a40c407003400c05003007507203016981550003d4410f005440c13000d0170309021ba61100d152300c0300180b60086003030103a41050042000c00040041c11500d0b0703082800031001131087c8030707644034408403030343c0c03e0b21800110484002d000c0c90380c04180c40000b170141610b8000701000c00d001040c04200004a5400001220710032030f6039420340e00c010078040c0d8407070340c109481b84e0208214410400c0031601a40024184001900c2d0625103220102d140100302e4a040c4c4210b4910019070381082c8070b100b410099001c2095944e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 486072473 1250 486071223 486071237
    0xc05060a06081908130e150312030a0b2e03061e0303080a021c0c0801082a0604180b03060603150c0f070f0501052409040303112a070501 60
    0x102c400160380d000c10b030080d50004a00150078800740400002941c5d16a550700900c4050b05a80e40f2509003045410b0721401400507100c480584c507482e001901802081501c07000e035040d90b1b603102948000345a0300c040380341c2040e25512120f00244c01e071030301c0b819035070303014811404240300202008086a890341c100301e05811040b000049420b5442100000302c0368149401c1880d641c83c0c02c04800039001e1440e60000803442c501c041c500d01104c0e600143c2060015581e100500d80e60784011540d98500080c0200300c941d0030825140b003201d80700103d14140d28000d0645807400d50780303010070311038170100600d00003017142c2e1200403e00516040c13040581084d411401080b8442000c140300d400a03c000e00981c000040004981d114030b5a010180c0d0100307900882d080020703c107030b0308095000e001c003102c00c4104883e281c0c0066604020308181a24410740c007601940103640c40d45d5081c1d005008080001c11121001d00c40e000340503071030040141040c10800080500000b21130045460800c0c0c0c0c1e088603041c0022 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 486073723 1250 486072473 486072479
    0x406231306170c0f07170c0a05300a0c051f0f05070e030c01030504140304150306060306061b150f0c02010501080312040b100906060305090c0a060f0311040e0103030c05060a06 77
    0x4a481a502c0158100701d10064002400c4400301c25171145c03910101160254800900900c2004507801142c003030ac411901180010700a04e0f00300c078004030041441400380c24810741d02420b00c80d91000302800d03c00d0003160100c004c050940c03403140482e115045c101c0341d00c842450038021060b0042c0d80e08080709003004400003407500b0019850300c4140c1411410107a40e8400a01032014091500c42080c2465060700d580d1500e43d102c0106044c440201a400b090400f000020312a05c40d01ca034100700c511603999111910340c10064040c0781d000c5ca001c00c1da40210342c8001c10000d07441703521540e120200c1c84400020f03840260b201c00f038290343d4140e211509641040c400b90212501c200c030070b81d902642c0b12299441c269070f0781e4a098060300180d080800c01514048000c900d00e07416900c00d90141142da000c94004081a83c204003001840b4007401e00052001217050703880718000e401c0341403a9480c2e8280b060505440703482090a82d24240c2c015400949240b12075010703c2410300c089504014508000d00a45003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 486074973 1250 486073723 486073747
    0x3040f140d022d0a06030b1903050d03020d140c0d1a0916050d0c03020406090b033304141005010810150c05010c08010501020607050406231306170c 65
    0x1450f0000f64104220703042c0e90020340c4125441c1203005050007070500348580d4886100400404543c80800d003c2c2d180201005004004503c01d10200c82e4800c000f45100c1000b44003c9010b0741003030400c209040e840c0c8000f00c4650725090301052040342003091031601c07149200c0b03e000a4030040c0d0f07a10702d0544000701200c000c64403100d0031181d1042401c1600003005990560850301e52140f14901600245019141ea8000768590000d100701c03030842c0d98000d01144c50b080e0307242451105913a8850001500c980c454030400e48001ea0116203180d40d050707055146090f00201b03003580c0c80a4a07100070415134000300025101c81c00034400c0a080c003860b140d01d10345010820003400e04a140a003034065942640803c40f000e100304840210298044020700c800016030101500804003230003024054010000000e425611500030b5038112107075560360a6081c50224001900010200d50b80407203c00c00700025180307000110001c500600c820350b2440340030b272611508428841405030003000b0212080140c980566 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 486076223 1250 486074973 486074989
    0x91206160311030a0207170a090305100c0c020d0302160308040e0907080d1803290c13030f0c03080f0301080601080a0f020402031f140909010c0807140c03040f140d02 73
    0x13280e1002c00683d02d00050030b01c00c4148140240310100020001100d480309070344066400100e074815812200c40c1285410030b041520403d400c444001040140704002500e03120540217030380d0f8000c0c015551560b8810300d40700e00020780741d081501d562130001800c000c12010120310561060000000d000300382d04200b8140c0d1644078240c410410070100c000301142000001800c68000d5502c132a80d00b50729030707201481c001840c441c0385c41820842441e0340040c00031059402110f03084040084c1d4035a0305410b50b40c52070090a1809019952184207100200010b62688010405a0306004100341c07290f1401d1005403504005030003c4003240c00c60809840002c07040a03441690945c11135015880e65901c00180e8266060503113900700e080894440021001d40c0080000300b824402d6440012555901902a00f624031424042000501c104001404144980e520a605200d41254140361602c1c00703c08501e90307006600011110140c60301304206004400014141c15a41a620400101595000a4004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 486077473 1250 486076223 486076231
    0xf09180308062106431110020711010e1905040f091b030b15030a15150308030108120c060a051f0f1d090d180801020f07020901120804030f060209120616031103 70
    0x4019404121b070811041030040501c6a10700080440d1030b00c10605040701c0f84004149143e000c00e04205294101e810178541503444002e91003000044503151900744401810305403601c40103a555501c4800003c1d404061202c5440340d45034005040c9401d50908140014005c0d121941c40d8800411440881d00e000c0707109c2403803d030442c041e0400c00c8200c1141c030001e801088810415514038000c04010060305d000654143c800800448806c00282c140f201c02e0b92150800940d8154007520001c1d520304002d400c4243c0c415203011845800c2424184040d21801040d00410220240c40c6000d003c0080d000c6289049204500841041814800d00158441c07900d0403480b010071400304801d040100350100d000001385040002150f407801c8000a1180030380008004a1140d0316032000020000100e4941090150b0485801880c062031076880c501411030b110f82c100c1c4c0f0180c083c804000140d54410500c241d01d10305801425407482d01c50201e000312251031f02007005140c0b0b84421030303e0510008045c1ea0388 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 486078723 1250 486077473 486077477
    0x6160b13021921140f06010305010b042313020a090b2b30020c040605030307050706030203061c05010e151b03100b040f0918030806210643 61
    0x1060f805040c4166102d04010041010f44645041101d00c08070005003a0304a03400f0340d00820004080a0800064a404183c0c0e5a88440388401e500901e40109518981140c0405081c0c01d039000e8950218015640a40c00b6843d2310381e584890441904241c00007107040c000044001c4c00150050f02811f840c180b040d84050150011849a40d1410303000c180394600800001489084d89440e04c84000e41d1404904041703401517040c408009414100042904d041540c4040507046060030140202c009400c02082c0030b80c400e10a0020247c0521200c5202000c035005000210b40c49250883c524a0140007a08442c4903882500410a000101010f214050101c51188503030700c0e22032103295011045990858038550000080c0000c0c2119110f240710106c50f8021b9050203c020320406400002c804a02c020300030840c010000b820f245024026403c581c0f428a201d66144010540b80c2d616005040b554003400d0781c45101031409201548506042210216101080c09081d215030020340d03a0304101c3e1501 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 486079973 1250 486078723 486078779
    0x120305030f102d08030408030a1404031a07030c0804120e03120d0b0907050403150908132601020304020604050d02120105190608030306030c06160b130219 68
    0x500403050241d20000c00491601d86605203030400021040094072006460303c1c58205000a1014404004d035421112040099400c0c40e44065040d21440004030b0407281a4204020102c0040d030301c1000c00c220040010003400c0503142c4800c0140403203c1c1811400d082c0035800d0200320001300d0581246841d01010b1074407000701480300e40400c0c6400002d510746054a440802c00d9024910586d2000b031400b50110350b01e5499899092041d0742901c181d0001400442c2c81180c03a440b000700c243c101d44281845940910300d44440c415152510000c2d50300710072414100b0019003400c0c010561804409442c580008602e1401c0503070000342a0f224510403503010314070290704c640542d40d508210361081121003000f44240e1414248640c40003021080040c021494007402049494001003030340d101d8400940100740404147c0104140e6070401071060441a100450280000d0795202e5118007074000860244600040c81c41041140c504414440d21400080c14041200403205007010350040e220701c000c41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 486081223 1250 486079973 486079981
    0x40b041119211b030510150c140d030507080c18060702100816030b030601090b010302190302030609130209040f02031c110c0609010903030c05190305031611030a0819050718120305030f 81
    0x9030706042d9060002c0c0204c806510542760071030300414100301c0300d816540c00b01b001782da40a1058407005400d481500f02440203000500c49420354584100f0528002081d89052186039030001c4c00c3c1c0400d00c2e1501000600c09000c0c058908078983e0f0040a01c045070030b003405940000c102103a074a0405110301c204040d128220049107034001d6048802101e1443c02c560981c850440f0050301a601c140c540d00d00502a080010304240c203024418190b0643c02801040319403116150100e080c00802c5060780e00d8010140d4120060460303008460744880f094490030240300e0030b00d290f142018044a9454021581044070450350b07a8050000c4054951500f4144041c03222410041d10f42644c1c03810301480403900301ca170301c4280340c1c10a014500c05c8400c60365080032002d01c41011078200034000c001910a500900c00219414041c43e0080d81c00480840c06409246040d09561b0540d041500e00d440810500c4412481601c0c1d00d9501c500034001400c0500e080301110b40d001081e40c40300404460f054003002000c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 486082473 1250 486081223 486081227
    0xa080a0605060f0705060708010b0304030815060a031a0402030727050d03030603020415030305090d020102160f080d050301080d030f0902030a030905040b041119211b03051015 77
    0x1500203818003520498032050542920075061340500d00654440c440e58002640300392160440a05a40202c5652030840d00d03070342d8040d0750b010400f03400300302462880e01e8148042e40320800a0040200907a60209145002c00c030254a42c03020702088a0080c1e00400c10043c020390400740da08450210f910050f05182a00c201260301020b031500190707404451504118241a07041d04800141c0b4000c58080040c5404a40460148202d03844000c0c01b04805000c07a078400d10303000f114001c41ca801030044e00c10030050290010321065494000072403c4500002c20b0008042c2013054069007556400d12030f1940d4100b900b1165510b01e17400525080603218441c076080d2080e40d030820510a540a800c80f40710740158a80034040d50014003415000e9481c2050451152419008a801c183c021040c10742c50441c0101e812071003098079130464018005002c080128019071a100b484140c10b00040009102c0c200c19035404010041e8030304902010304000600000d40741300d0b4065021507030152210b0042490000341 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 486083723 1250 486082473 486082481
    0xa17071401120c02060a050109150e060a05040204081b09070206010e041a07110c01020a02090402150c03070b040201080106030e060604150b040f150c08070b060a0504020a05070203071a0a080a 84
    0x82c400018104055028069000145980126952001403009a0326440f0507007c441040035204c0050001c800304102244010611540021000e404003500a1301d6001003410381e0300c07642c0041d400307070310080d40142e52a0313490b90401c01d008000c40d41700300c250804039002962040d041c00b80311840c101e84000700c2d040240c06044401da4041c65507a011040c64400703400b5090419038844400e150203003210811056101140c1e07810f02603401031501d8215211a000d20010401004042c0742848041210860302e00d0704102034003000b0310420f5491150300d064070004000c8001039220005143c146010b010441801107540c42d4005c0d0180c0740000ca0340740078015028444000d92003103030301c0100000c002c8ec0304c030300c020480c200b55410f1088040c64103650400031190b0240f011400341491030144019000500f2195401e83c02481c000c110340000c986801c005030803a0b1014a8030008983c3c0081c580c0c0850070184060030041c561155261524095400714441612504100508104405c00000d24002179648 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 486084973 1250 486083723 486083747
    0xc040e01141909140f0108070e090709060b04090f0b010c03030e150c0d0e1b101e0e0f09093c012004060e060d021c0b0a17071401 57
    0x82c2c41d0700903d80d603001c12001094403107136880c1c66003084000510481824801c0c0350498034171000500714146800610b024441000d000110503000f81c800005038030b0200d004a0000d08010800300d170b9240d1808101d0000c0340e6103010020880c50501c0881415070ba0002e02d10000c031a0181408510300ea0300080940c10a0b4003600c00e0380c074200b110713014030400141e088090071640c0400c0b4400c00410325a81e00695807020209007500200d4074122014450381441c1d502601c01180d031b402c11007055503004902e00ba404a0240e01f5500203642c034048402d15103407200f6000013002095642c00550f051480324180c6030440002805010500001c0b031404c80425a065401040307414030b2002d0210581c181c011740030302401ca903c03041c80942e00700000701403615030081750708517811501c50a040f10001e501b4408903030024480d000b4003542c2404010f505907400100c10107824032142002515103030a8003084031000d125001b00c0520b500c2848440f0031032000003145000c2d5080480b800b0401005400101c8400034621 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 486086223 1250 486084973 486085009
    0x7080a090f0c18150b0f040e07030b01030b0105360303030103060e060115080a05250f02010606051e030921030103060c050313110321030901050c040e0114 68
    0x66407001071014100034401600e280760398000c0c40c050700440031010b48690750400f039800b54000b04100010f010701d10041444116000d48681011356841c20007214400840780030001c2921803010780c4c030540e41480380d03114500702400e00328248070756a40170942040200321304280040004d061000c1c00748026428000a681c020201c07640d03503846e45003210141640171a4104140b240300e0020441a58442c1000a00441e5903a0f8180c00da4900700500054207002c0c240100d411304d00751070000070710000d01c5440c1d0b581007640c075062511816003400034210742d81a880b4404101c0309001200ca0303900440207841a0084440e5280e80380d4446003107141c102902107080c4c109101c01c421a5183e00e100060185041341d000d035104002000784280182c0d440d1104a5450310a81c40f2454a01c0008803112004d040d00070000e000c68001c610720321012103140c0c000c0e45000c51021300200030001454400d000301f42e4001040c0c0d00700c50a0501e0207481c01500c00040c0141d01c090356000542800c2078554079502001c80c600381e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 486087473 1250 486086223 486086243
    0xa2405090411040f0b030603031c0b0d030c03110327120a0312060902030402010e130e1207060e011b120f020316030c080702030a110a150509100c020607080a09 70
    0x6012a94140c1e400f038440e240b040118020002005000c000a80b4407552001d03000e5464200d80c03c3c03034500d0f9000110480d1444035039600103403106407500c68094980905c06d07201c200442407142005401c000850314801200d51040000040c040070307240c1407540360b041c1c40c481450868800750000380b001449045d47d40182c802d05400b0f005140e0302607010540c1c000f03184c804012040d101c40101050f031104550207400300e401e500c040e0030349080044045c601440d00500000d24900c5040405003051140007202d80300b502c0114041c010b005081c030403a0000344000d4002c001c030340405040061004148000003007800340c04c020800e455480d036080724101c4c600d6100119070382d02d004580300017100c144044c4400007900d801008c0c0c007502c1c0107000741c074000c01c0b180e0021410650b8030354044400f0306081480328000c0c0291542a000101c4020145002500005000c6020700d000c3c0303402c0f49440c0328031480303400d0300b414030040460441c0c000c00c4880d00110b440c0341c01446a920030345600003400040400501003461 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 486088723 1250 486087473 486087491
    0x130201091725030c140a03030c11031b0310060807050103090309120620030609151c2102070b07230a0506091b0f040b010e032a0a24050904 61
    0x32504610050304d218040c1d0040b51500c4d405910b02c1d00051854054011070304030350501c00301b40a8a0b80320888d51240c80d00840740130b0b0f2480402d04000c0000100e0031000c0f1418580502e07031509200452446214440400a040c5010166640c03160240b08440c1450340d510003000034144111001c50151174540240c0801012070b24180e0300800700d092a06100c1d010303006540a254002004490080000030111401b039212210700d02c182040b80529554000011110342500962005240740c0d80d1740606c3c00a40c0320011260f41201040d1280e86e03010441d000000c0501220985e4030a60300125080328103585001c0d90150580e16a00c40409010407520401c680c1c4030401ca40043c41074801c2d9106815510180c041a0082485030510051550f01c48508554112030341069405031a202105250004800c00003d001c00d00b00703032505200c075954206442c448481121412840b0100720010b40d000708041d45400d0400c030348914005180c101c00c500403071510192074421003e840c1c107003034024410010100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 486089973 1250 486088723 486088783
    0x209010c120f080a020901020a0201200a060504050d020303060907050702042a0906080601020703060e012406031107030504061107030501020a1205060604290426061302010917 77
    0x124104082d0003c0c0c3e071031000502115039030081d2000c05606170001c0141d141541e005441366625503003280d000050f40412000010b40801c80c40000728043c90002400e405d050500c00d0402011240d000c065500030028050b103500e07042415030307024003d0700c0c05036281d050350310005d00503000121548400705103007817180d0f200ca80c040500b144d0b41c41c003d40b200c15655685003030696000790202c0c1c1d5540540c1160408001044850b0800c03416004031000014443c400146a02e0345007080021004054841c024180642c61f09403144004461180001c242000969a402080342c8514014101003100710740900100c018104907100245074800020364840000e0b00c0d0040014105403a80707400342c0e00740300c081080b13420080212070554503440320b0103421703001014070716250703003141a2003414100c410040015890501c05544019441c3d542a0398100c1d00241c0206151100203070001148001d481c402c0f00c0180c0c0c000711908111410f02e4081031102400b0300c0103a04090340e000384682140c80400803004441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 486091223 1250 486089973 486089987
    0x503030301140f0901060801290d020405010f02011a0607111806010e01140d051801140a061d16020102070b0f1006020304060203091c020402160c12030509040209010c12 74
    0x1400c241c8030912400b81210070131400713000030b00c69540410840f400600c01e524003040c02d42d0784075440e04041d102c92a80843e910300b1952040c1d01c60040f507940400c040c40b456a0003841d11241c080b80d40700a0040c01840d000714103800e844030a0041c03181100003444010401c02b401c148140c0c5e0350080100b41035441c00d076041550001c0441e00c072400118bd41040003620340c00703030511141c03042c00c0783c8480341000e010a1f850b6005002c050840811020100800413040100b40903c40104007000c0c203500e00c5082c40850340e000d0395020340080070f01405054101d0408031461000c107502c501c1c0e060002c0a0302d0203614083e07009204560003d84004004001c10900c02c1c484050340d402900700d400e69905082c1c0e184070480e00c0b801940110320040c0c100b0022200b191078a50402c80b0740e812521102507004c07244d80e000070100d03844219841c99000c001e00010040c850f5105001c00100403034602102d9000c91036074024050702c180f055a600c210390104044440b03911030440e8100c0030303030f00c0600810700c15440c003c050210 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 486092473 1250 486091223 486091259
    0x8010b031b0711030a0b013f050f06071205010911120a0f02040e0405060106050304120f2c010201050c180d06060f06170a06030b0402010e03160b0c0c04060305070e040503040503030301 81
    0x42c0200100c8e85040d1240240034140b4601c241500308030350b001030701c0d101c2450404400180c60340d1044845000070b55500307102c00d5003d030b0b9480d120b0005180913041c201050300d03416404070700d1491400001c0c280d41e04107501100c40c10710304560307091032030b5407454140c00c000c00c02e4064001d4050f1021030003280c110f560200082c000c03800340d011924143e07a20542156644800c41e0000d04ac4508803048c0d5240600802c4280e006400d541850062504000e03007a41d074043c4903400f04003803443c01c80ba51080c1940c0a2045139000303206070115a203081c00240c0c1b01c0c0e24480001044500074521240d40764103005032540030401401401502c030780800c2d80c801c0001c103001100b11140d02c0d0300c861800440e040041500c41c403800c9036400030428100d0355036134005698440c441400c040d0140200810000d606041004580291150281894403456849442403801e40708080590003249031040600c08942c4c00100c5000b00c850915525840d540e40c0d1409508600891384401d82611003c00080350216031400d80e2004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 486093723 1250 486092473 486092489
    0x606170709050c07031b08070203151f0807140f030a08120c1810050c0a0c1802030108031603213e0a02070509010e0708010b031b0711030a0b01 63
    0xa0b0b42c8a42001d0841c5214012005022034403005820b0300288402c4403e01ca1745010b001281e04104d9185c02182c100710640314540300445084c0c00300407140c5020f9402c00d003c86804400c00140d203003001c3c0d015903100104d0050741c284040701810300c002d641c1d8070200300742c201c28091300303446800020f031410344429003202801032400401c00c000110722200074424ad40c13140b94072504006002c4000001d02030500c0704180040e0800504100c01c1080da2403c01003a0380c0d55200305c640d0a03502c3c0c9011074030304032602e074102c4169041e801080100440800003050b2070045c100044a000a0b440354039098401120a07499048450f44c1c41c05074042410641c0d01c04050404500315100388044c002c02c0d07000e240c0d40501c150024400070003219145010000c409050303003404c98011200c5450300c5000103070300038209902034450080200304000481d940310702420b006200940c9a5400c40c2070110f05003030340070840210304a400c80007049800074041c0e650001c9041c4907014098480a4a40e0300f07048400590074020030b80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 486094973 1250 486093723 486093731
    0xf01091202061e071b050703150908031b040e0f070201050109090816240f0b04150b0702041112060a0501050405060a050c0c030102122a0304020603040606170709 71
    0x4a03001182c11845000611030000401d00444103041030400007809090401040b03581d00c3c0c64201d40410816061801800180025450340c5484030580550f00d030101c401d24244100000010614000d981c5c2080b6120100025079401d402450a203000c1e941c01225034401d540c003400450419904503600075a2a5402400982e8030b070452201941c110506c000c2008508204001c2d034072024117030105904e841880355000140c00341100b100d484024911041100c0d5441403110345003036091140e03039243c0d24151400c4c014150024004001c0740e015100c2d5004400c0001005802c554455100f65035114085649036181d4201e5480e4014003007084400a0080b82a080045099801401524216880104a1450140584011142c13904041080d81c0b0520520b00884541c2d034080c0041e02c2e0071f1000741411800c62500c81d0959000c0880991b044c511a10241c444840c00d46490040f43d40c020313015200381e40d5a4440e071400e10b009041e190b00030404040c0e800040740c900d0b040803d07680121042070340140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 486096223 1250 486094973 486095003
    0xf0b06010507080a1805040c032304020d03050f0c0a060504141f0b0a050a15090b03012412060e09160e01060315090204030318080c012109050f0109 65
    0x24640b403149440c00740c05481c05004da6450280b00303503c0002400c3e60b010020b4080e682c1c1710082401c1c0da403a143c030324010079180c0d41d40b50708013044800c0e0741e01d11742c0360250303983c555007001d40104000c1640c195026080040008044c0601071140044429070507120040310740d108c1c00c0d401c2101c0240381c01c2c0c500f2501d81c2c40da0280003c044000207410350400d171081410b20381c500304e015151030041170903042d000d0b044480d941000074140c0c1d40410220040c10410714103614640c05040081c80c166041d0483e10b00d140040c001403060000d4401807060111410f041c26000191240040e142d084400707404034081810160046103180e40041080d0060381054201c0300740345454011000e404601c1d000e90341e08104800010009680300360021000121000300900c1c1c8079440c1e0030b4501c107076805a04250040740181c10104445240102808010b003640806015481003030000245880601800c000080d449010304214041c3c056101900c100c1c2e10108440a903400d540109010700312906040d6a4025549491 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 486097473 1250 486096223 486096227
    0x9190b04110618010e12160f050a080a060207031202031303030e0304060816030207080a020601080d050301080a02010c0203030d1e15050d0314040e090c0f040b060d09061103040f0b0601 81
    0x50b8481d40c0c03480309084054100720300111900f40d94210401d1380700a540011901c4c102c4207001c07c03001540c0030072850100b541080c40d00c042c0303a040c5502c540e000c1c0d4188902080f20700380c0455680c6500b60b00103405640d03200c15003801c81e80001400301c02c41c0707041d100000717001c61849510107410081e8800d07101800002c50440025459000c1ca100d1300001c50041000201c00007890704084100015600300141822580d85415005402500c0040090383c4450014001f52104010040c007400407450603515641c1481d5000f03440d8200d4070300090500013101d49040c119034003401511800d900c500400c0091000e820a842c41c0403c800714011070706850b01401007042040c00000e802501d41c040d0a800107264a1b690490b07034040a00e011000d8800103100104041c2e10310b0304014001c00c1c040e03004050031a12041000b40c0e0681056400d40314030305d4017041105c01e031102c0c4290f4103103c2c0b202c1d40014812045003004006882d48443c400c1003114000100800c01081c281c100c601c181c019005001a03076641801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 486098723 1250 486097473 486097477
    0x2060a02041a09030307050f0d090e04080a0c050114070c0c0e010f05090702010f09030e0907112d0304170d090608150d020a29041d09190b041106 64
    0x1d414150400c0d040c42c0706258459002401c620b07102800300c900e885420f0712640d040644100424006800100d440700d003a80c1c1c40010407000d41203c900f01103040c1840e0b500c1c40000d110b01074200081c481e443c2031140c184402903001c1580901c2010b0000c966242480c130017010200c410904840002000394003140c0740340c03000b81c164185d0711059140d5205a041034100241011300400701e00456403038003440e17459442c4500509580c90310a803210007036080180100f04110100405020030000151802100c009000807503100c01c80307503040401c40701003c910131460081450703900d494151100180009041000308560a145502e503401c0c3c80d03125442102c211008075141c81110006208000410f000916820250302e4401c0010a50001e0803251750101e0b1440701c542e070100d4043d902020300d510060031a0801e50780b0039480d90101c545800d041000860030b101c0c0d201140b402d003c6820f00013800c4e0302403c110150ac140c1d06100050405004c602e0300040405007110102e0b200d40c6450403c203841d0500c582 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 486099973 1250 486098723 486098729
    0x1006080f030301030803041b030602040e0603030c0706080717010e060f100f140c0a053304080d0e0a0c030318030f020d15150e0603030a02030715020f040603020a02060a0204 76
    0x10146107542d1131521500c07280e42029000f43da4210500303461124520382121680025446800e015859519040f0092241c03103004250a000c1d410400030301030020404030380c10040d241c0d90b0820290725220704c142100d03071142500408089942580020440000100d00907110301403c03100c8000000700750082c1b081d213030702a40b1150089427084c0340100020780104810704058030b089444a0501240800349031900d58200c0b0127603855000940300d00c884074281941c0c40100411650544901c14080e80d5110a09200138000317000307040003090301720000750143c1040f80300c4843c1c40121240100c040c141540981c1d5544400c030040780c810b04510100041e032071070380811207400c0000e1444540d9140c003480001424260121921241e91682c0b07141047c032446484c541d9140421540001c1e424842c11505594015142a109a005000303007030086600104459030710b680f010641d030f50780104540030401ba028002c3c0264502d83d0218000c1034999142e4054038039004075608644081e00d40c24810412482540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 486101223 1250 486099973 486100003
    0x6010f0f06080a24030f150506060d0e0304080f03040f060201050112030e0111060a090510020408030304140c03030d09030201050f01032a050d08070b01080607092312100608 76
    0x800600700000d01da10401c07030000040040540c03c0201c2d07080d2807130a00c0300e40088464003021400702c1c00f03200d402e8071000d28050318035400300454280b40c03000402500618004058054030340c001d0707468481040c425103005082c55400c0fa810040d00b80f018a840303400070b0095507480c2c0c0c260f20000034464814040d8504903241d8503003d00901205c0c1d2030480750f103280c192016040c0001b204d00c0d49511031040000611440d0348140004620074545840c505118040309004c0038540140400d1101250110803250441d920030800510b40c40f418a54509013400d02e04802e42c10b01001c01c1c0c00c1e0b148a0a034000da600310744241d000308690760700d00003c282104420b0002900c00124041070040700b540004414290083c81405250142c3c3c0d42e0002641021b0914000c0700c001001151842c104840e0f1441c0b1030140c000040917100c1460840c1c00140700300294480d00300c2002d0f602403100ca007003810350300705001d000002d4841039030100c8449400b42ea900715040001c041e9032811000261000012800f50300012001c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 486102473 1250 486101223 486101237
    0x190201050402100509061306020609070506120105090907181512050d180902040f0302030c0108040b160512161407030203040e1b1615020c0c10030e010c0206010f0f06 73
    0x4420700301c4139070300f2500e0081e801a0342004003248030305104603420300506542d401840c01349840b0002c613052810075071002d40218814000c00c1d120304a03141c40181580e2080c0c8040501d55036148201e403404216901a01c00c60005250b42d101182081e0000d29400b961f910004a5459580c081c0c014420b100c03603009046030b0480010b034500984201d00d101075034000c18014070001c0341c540030745604a9001d40c1c08a00034842d00c1100704214101031142510144007400c0400d510703d0301d03071545580600c0c0202508411a9845241800180102c0a0301c90744031405626401501c0c0c5400d4020050010045000c0840c600e401e130401d0f8006180201e8070807550560165080915000305102d007958050001000094040304d44a0310500c140041c1800d80f1540c20f243d003800340b0b5402d040da545641301003650744448c01003040c201d01c140c0007e5039a20340d002c1500d0702c0103c5501001c3c12401070100700d80440155090200c00d1540d80d500203811410380302c4412a524070241da0702040510030003948034180c0841c00e2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 486103723 1250 486102473 486102499
    0x7172205130c05040807080a0204060806070c110105070605150a080304060e120120040e0603030901170601020a020418110d0f032d030c030507020a0b0105040209010e15190201050402 80
    0x80e038000b240e4540d01c608000b41031948903c40e090411180e0b03000300059600490558040d072600b03020b20001405c03000c011b400c0504060500030400c4401c480064940243d18617a1506a480340086400c0b80d41c009004201c10304220308101a07070202101120300c262103000011031072250120480c0d00301e8043c0d03224501402c2048052208032a031310241e03034440d95655014a0a0b1403910340400c9030069003480c255a07514100341d038681100704081c0c08075010342e00920210300c169820890040001741100c90162040c1e44690040345801011003000f5000340c2032040841301000000e2084494500c64140d40140300f800b4000e0011020040a000d0450b0600602e5200840c0c081c0140c0b9241b002e00703400c121070340c0202612154840c215584008002075549082081d103990522030143c00100500c00b501a615072510380494a00042c041c0921495001591544d240c0c0128141100178401900803960030310115000011a00041080c018120540711308104940c41071003810721595008154000d280e013 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 486104973 1250 486103723 486103759
    0x70311060622021309050907081c0309050c0d11030c0103050f160207030605090a0605090606090c0a03200703030605060c03030a0c0c0609060b030d03090b180307172205 74
    0x200c0004142c2d2696404c0007200200e52206140402400310800c0c04030340360801840035480c2001c1036110120030b070010728008003611015480b0424000c5603290100b40703200741e410f1030350400a0f00c4c01c80f55404400d61640c10200b141c15412014180380840036129a4403c0000540981e0380c04c944510100c3d80d0080064070f0810700404107a0080450f104403400c0075143c0c2d4458080b07074415034801105070f205c41c01800030803119002e11540982c1c440080d00c0d550503c400030403240280036010700699080401c40c0c03841e030b51103540400624210004456000f003220304110703401d9801500242d000904042004c545802c203d0200c426150000c1f00841c90b5660b0711071058000e040c3d08200504100d6860a20400305045008440c0710600500700000c0f03005032942018034000038455442c0605080c0f128020100300341d803d0040d800f4401413564410804821422800e61241d004014141101d51517001000034992018091007078021608021407a009091007040400b2403080c0303540b0403079404400407000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 486106223 1250 486104973 486105019
    0x151b09060a0e1801150504030f0b1b040f03060513080403030f14040801050f07020c01020a0204180f151104050d020d0317190f09440703110606 63
    0x2910710b01c1e06005059022000a01070000d0780030030042e02001038014007189442410b40c508241150801074581480c40c0d507004031280306003401074a0b09041c14005400c10758000c3c4243d0b20310442c80a031517900d94032514170300b42c44400d90000313031146454000014200c08502e41110102c9070032004040c00d1a203140c0d401c4542c0d07107141c0c0c004020451403014140c812000c60b0060805860300900121744d624207800720588000004001c9021503000c0c0c002054981d8010680340b40e0700d60162408107500c042c0c0790784400c01c0c5d0241d25000f07014140b42003540003030261340700381032000c0e0f45449011b102c10304080386828014003440c0901c50f40030308400703100d40051515007403c12400c0d02c2403c1c004510540c0102c541c03420407048402e1460b0f4805620022102078051103420004401a442041041901c0d22050b4000c070380310390f2008091610302d1074500401c442e0b0030020709440004d01d250035110801c0c018041c45400c50301048000c04c02019080164940109259101c2c40b0040e2501e9a4486407907030822142c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 486107473 1250 486106223 486106237
    0x1e0c180702120f0c10060b16020301180c030507271e090c05240702042003130308010b0c0c06180301060e1e0f0c0304061d151b0906 58
    0x26210303445111203140b10304000360240400303200200b03407590241c0e050541800b1050503c66011840d00600340700650310755003500c0701c1e051444002995110188082070060182c400c1c60503842d061100328004102c840c3c1021002e4901c43c00c1524900c5599902d8940d0700060b00400039460100250100795100c2c895000b80c21500c090042c42c0014041051914100e5000b0401582d6400011405114500303003101d5840d0f02c46501c41d50003072489040d8050844a0142080c0240300ba900e0b21100040141031090729003880c0340e0b444000e5502e040c07003045d0503121549a2000c03408039000e40000203c1070b124038103540d212441c000c0032704400307204030042050550003000e026901110203a07450156403800d2180b1400343c04030380c1d071008080c1030401104041038100f410000000b2403800c100040310b0340e000718594000c1136000030342d510b0b40c88910b0b108026060050310140322109404c1507840c0014000344d0102d000d94480d04441454841030469034000520602c45a0b204c10104202c80300d6062140c020146 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 486108723 1250 486107473 486107477
    0x9021b0d0f12110a08070e150708130e0901020903010f0b01020c0d03230903010b030a0f031206030b0a020702100503010501090501050c0a05014101090f06050306091e0c1807 76
    0x2c101c1e500c0c0708083e9941c00c0781e1058000150020304010314940c0204442551090480d99444200e0b58181300c04106e100350b54004007800404124560540700b04940e480103443c03055604450b07454480d00e858002d42156000f24030940c02d004102c90f83c00b44034403e400e510641030380901507154001c024001070119049049007004440300146030301443e03180403030021000ea80109a41d502c0c600c1e04060a40319841c0c4428803c0c1c1240a036800000c807e040341f880300380d07418180712207064405860b0500800c083d0380301400d90080d03241040140b0702d40e5402800b10714400c03264213000600751401210b17140424041d99000c100100c1d030030f1240e503004801626240d42904220750140d61345660b02c0c2d0940301040d04420810410f00c410451108034640e40b92131004115036100c2c1020032260041704203030818881e8000c0a60fa0b0951184100c10b01c0d0014400740c60068200d910714101122403aa40e602d4a2010390341c142d44116007d02c03241800b0695448140c00203020000003481c00d0300007641500d0160030101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 486109973 1250 486108723 486108731
    0xf052a091302091f0309050c0307080a140708010603030302120f040809060c030f1201180e030906090d0f0c050a05040e031905070f08030f0718030813090609021b0d0f12 74
    0x81c00a02d62003480300130101c140c0d40440d01d41c89602c4c10f10701d0440c00100c502c1c4280c00903c01440394000009150100170313004a02c0c0d601408107010fa071428000d594012010300e509292002c014550580c000f00031040112100c0c0a682e80d900c800c940c102d000544005000e02c6040001c50024941280908a10610202600c4c03402d903110040b4400d036404140c003100503418074030040180d4004e0842d10a007100b40b4404c140301d18030b0100c40c440d80320702ca40381a981c803485000c2030400d4a0f844050401003010340c801200842941a420b24801080c501c0c4202446402d5040300820301d03042034066600c40300c1c1031200960404520307844100c0282080b400c01b004002d81480000c000c41d0b4103c0c03140803010b0003100110340ea410402c1c0092084c040050001c810b229540365204a80c84810046104070390b080000c0c66182c0b0101c140c44151403034645d00143c82c0600b030640205035485154010040f9450b080c005040714405c61292540391100b80c6012000b04039100c1600c0c400c14000c0030000d03046021808001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 486111223 1250 486109973 486109999
    0x1080307032304090f1d0f0d1b0609061b0512130f050d08160c0b0f0709090204090b0315041e020f0901030302010f050709140d060f052a09130209 64
    0xb0045a12003005a0425a00c0300d107404240c6c04400c416284246045000d40101c80e0b1451100b03507601c0720143c0715410004910031903014051616103000c0c4076503205505018144040c00c01501405480b941d505202d10b0340d80c4c507403500c1c1e40076070112440b62070525200720310340d5980b091a21145420100688030010807043d024005082400029150310458582b02d500f800e003940f0100c1c006460003800320a102440c1010400310360f4408001d1340c825080c000c0d45465640b001d0301110340d0016a440903c80b24008140071038051110b82002d6a91801a0100c0d9000d50100341041195102510301400c0c0006031714038100000d1a041010340014006821180010b00c003e02241e48504243c3c0180c005075034401d0403059080d454001c45401a8071450030b13181641c1403c858601182d0f0304d00080f842800360340107080070009590090725845080040030806032600c01d0400050380a0300c000518a48040c902c0c40c0c032050008019100325070000740000420000714031821000703502143d0000c0c1d20400d901100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 486112473 1250 486111223 486111239
    0x2d100f03050c04090618050a09020f0d020114042c0708160c02060f04170f12070c03050105010803120106091a07060f0f020d140412030b0111070b07030801080307032304 74
    0x4580201010060030100d40748540c1000107c1e00090300b1925000c0c14071240c400580d0f95404412100030080303071084070380c40c52840180d400c4143c81d402011803203004030300001ca500380d510081c411216010350440341011254030200d6110703022180310f0003144210300440d0418102c1010b4456178442424412503203103080d000103403650441c510980c528031001606000201000e00d01b070340100e0080c00103002a942d9112030729100c0e56104400c0441c0e100215081051000c2d002d5440001d40d04107000b081156110707819035480b540b0030502e407880308900c440006030305445551040116000b00d034990504000301c4030002d620303901800080c0c4031140c030340746000e0044040344101041458018001640d034808050b4542c01d84580c0d925201440451400b0040420384068001e5171810841c038000a5020503000142d82c07080c1203001c21600b43c420f4a02c04a88100c501c001404001d0007a00d404105a0341d81e40c40c1ea43c0c0f486031000040004015002c0ca0801a080c112222050020160035500702900c84403030b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 486113723 1250 486112473 486112481
    0x603050d0306120f020609040204091404020315132924061c0e07170610050d150c121112070201060614070804052d100f03050c0409 58
    0x94405811100019418075018402e0030003c02841c0034414814480362100c00c0c400401c0300d0701902403107000402c0a000e64490f812580035110945040080050755505d4103d80c102c00c079012402403264500c2c4e40343c501e0000200303a202d00804100c080600031555a0403001801541c0d19201c00712007100b5400341d002c407004403a88500e8041c803d640e40038944125030090b042c0b1480e0150301030001003120748006411a1a5454908507104000c1244c00f08104150b1030490346030311200f608040d900000300d8049022513814041c0c126540f4040c00b0f42d80720b0041003912101147c00401d40070840c2c2c200301c60700e44645c0000f20307812014180f030741e00309100901403002d554a0701c4600503696400030f00e2182e03405041d00c0702a000b0446c0d200030000030b410b000010703200030881181d17030b00003040c04100300c0e08012841341114050500070f03003214225010520b1800480c0400d02c0b10f4207102c0f144a84007801810600018032801c0c026998032002c00c041614264014180501114010a0100001b180454150007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 486114973 1250 486113723 486113729
    0x50f0a03150f0b040501081005060708070b010503010506090406050a06090c090801140105061b0703080d0501051002060903031311101e080601020a03211a030c01052703030d06 77
    0xc01103080314603200960848405600680407460704603409000c8001d110381500c00380c400c20309000050b42c5400940d1a44041d0550103503510040015542080190000141940b544136494002e000d980300c0c410182030325802c030303400c0350026002c07000180810703415000142c00004a080c001070441d00c0b4000d40081d1a803001c0300b2004038803c41000c120702042489880c10700492803950304029414080081c440344620032405003040101040359640c41001c2c04014011b50344844290b5541e4030305a01c03080a0202445818410b4800349510904140003180c120b21459000740031b9031940d0340c0c0302c8815a04c403459280a80700d01c4041e070780407011354403240c002c001f01403503d49904441d0f405158644661071a00e0903a01701f00408042400141d0340c0004e180c0e980310342d16040100d09101c41d25800d13000140b45240403050242000045141100004110b00d036561054040d02d90701c521180041d82c0600c91002ca100d200304030440c0e50350311101540f161060848004040d2440c4c161030250402c15100590 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 486116223 1250 486114973 486114977
    0x507081204030905032a0d080d14060114090901050616050316020a0f2412091101030c0207061b050102040e070e0102070515031b0d060810050705190f050f0a 69
    0x80424400351030304010070280e15a407601c082e840c03001c4110140082c0b8010f046002e001c1c00daa81f107418208003a00040e10343c000040b1008020400550359180a6084141c848034085007504607003050440c40d0104a0300248005066000280d20340340c02d1080384e9204003c4c1c8840301480170801c000090042c40182250125184a2864040ca900400030580b0903944100740112111104002a001154403a604010840c00780340107101c407000d0542c0e8901c5072005140110b03180418035402c000c4200d8401400c22400e0380c2c100507420b0108016a503410b0140540804161546a034902c07448603805c51040c00303841540003500302540c0c1c00507034111007415507049010946002180d009035904118001c001c0c03004680801b034080c00e88032408005e20000c2d101e225104686042046a284620200c4620000079581002225500c000c8a0740391048060f1204d95103040c07101080010f4410030a6503024042c82c403031224101d0790117506541e81007090348900284041844501c41031240b03d0b010b0408021a5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 486117473 1250 486116223 486116237
    0x110d0e03161e0e010602190f02090c03091002040b0d09060e01060303080a0c0903081801090302030f0d0e0301050105030717150124171605070b0403051209071401050708120403 77
    0x7215203600400c0858118003e02e0801e140100551a0300107002e0840865900886114803400d00f00a603210b0f81d6480041d400a450100740611010f0140c004c0d841120814280c403c41c0c510150510300743d201d240300e040c00f895000d00a0410315181540581200e5109580006a03589075a40c0a03080d501c1c1940181e0125000038200041d0307100f580504a81c0d10480d10703280c0742d154203507921241d641c0500c001c4004402c489003c00b0f83c0741d90040740c0d41005550010211030721200002c2a29540d0181080b03080d0024804100600f558101406030506845e001000382c01c00508001c501114001c80201d0410303684500d03018250070900c1000d0181c061f0140c0410040300d140300280d9108510342c105014400c0121152280404002040441da0000c0011614100e0100c185c80100c43e980940c1c00080c2c59465554140b00030580c10000500c80c1c80c24038244245684d07500e00b8102c0d00c0340700c14400c98484401c0000c260b100b940c4610010700009100e400c00a0070440960040c0c02c803010104c0b0201e0215641d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 486118723 1250 486117473 486117509
    0x111b13060311130e120403140316030507060f06090c090501030b03030d090510090606210b0609060111030309010212060a080706122406081305030f030601030b0907170601110d0e0316 80
    0x950813042340f02041c2070020b6203484c0138515444230703080c1c1c41c0501a0070044041040710400c030540c2c000c01450340401c10280005610f0300c041e000140851308802c004500c45010001e925402401801d000c404020b016505150080079450064003841000712201d0007440c08a00007034105105641c0c0040c020b40d40000c185003885111010081800300b0804110109207a950005880890250380000c0070f443c502c0440d161407005a036200b01d01d0380c000324540000710410000c0302d415406080459004000320300140c03907882c2403090094460044c0d4030a0b420541050008900074046000d10f0081280001204020321101b80300e03822860480030012801d183d01009800d03480515503800c4201d81090800950451341c2e81d5076284900001c0c0206004080000340302c9a000b940110070202d03000d007a4090601e0114402043e014035441c0032020468a40f0100d445940718031041d08400305400018072144008100030707594400d0301c034900e50f03140c4509111801000d042035001703401010700390001206200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 486119973 1250 486118723 486118733
    0x8010302102a03030204050402120a11040303020622150e0d020123090c060c0f1b06070209060a0305070f0501020c0d120c03111b13060311130e120403 66
    0x8550749008202c0c0285412800041c151000c00e010b6080e0101c0c0840c1c040b02e0f203000d6001c0c3c0160303441503510500c00f184580d2000f0b074001e221352040304112010840e40e020301200c81010b0090f4003001d00160712400020303078403d50a010b458000380030b8003001482c0c0d001035560700010620f110340c40c4099907103c40c200e41c5012005c0001d0141d60155000070f010007140305980002c2002840d001080414084022840c038a00901030245940b0001e006143d55001c0d200d065580c805240e644102e1b41d105102c0c44420f00840503800d25601c1400600340d0745084095001c006d680700016004952100c4030400000000300c00304001c2c2e00030f0490b003681040391441c0c0000a400c3c55000c1e00c00e00e004aa80440d16030000f0a031031a034580300149820241440000c82c2000c03122040c0190351303032085104005900d1641604405100e240d82012146415000102c1c4040000e0399071900c402841c411084407010200d24003240140c0e005401c0720000144450300011840c0b60035407503040a020380600041c2841404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 486121223 1250 486119973 486119989
    0x3030209090708060112110d0606050a0207060207180e031603180b03010e0106081f0b04030b131a1f0e040218070203041a1c060906092307110d08010302 67
    0xb500b40391805180010020708000d9008605402950b540c03902c00d0b40c101d070344406950914030807402c00c2040c16240c00b0f01410540c00b00c0c01e070300007503c251a00050341038070001d08881507420200030141411401c0c1a03440151440040c0c01c2c0b041d004c2400301c0304003d035541003440c1e01c8074003d41d02e010b4483c00741c070f10070300d04c40240d500004044042040180420070705c1c0c1c48207a045404501c0e20742d0386542d441e5100244403900144003800344111420015110741c060300948203a034010198142251121069070b0790f50788128500801c0d643d404003a5540340c4041841c86684403174064420100140c40c102c3e09a41e04910381c00020700c0d407004c60240020b42c10304449086000003224202d02d0182031183c00039540b03003d14800c2051002d040d0508240104009058035181c101440381074031a05e48409070f010103400640103000c6198606400081e00581324007801544219a07204800d02d9070741d0303402030084103400400301d0341407000040703400e00e20110410101522100a075118481e95045104006030341c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 486122473 1250 486121223 486121231
    0x15031112060a0501170c0d14040b010f091802010e040b1503040b070f0c14070b0a0201050609060103060b070b0402060702030303040804081605181f080a0c170a0206160f0303020909 79
    0xc000040700017134941800008a800102000503140c82e0110041d00c04040d007150300c48103204003119030a003c01c015141d95110706840c954103002c1c00340c0303480f29924400c50300d12462905400b840540f0b40c1000d5406072040c03619003600548003245000c0c0c0c03603000c01e5030314010440414610000104003c00c4c08124000503420151a2815018401102ea0020301400c0a5070b400ba251000d900d0842d81070500c204132450040010388500e98446501300400b9000b480304603203150080385080c0020f0050b6120344500300a0350041c200c2181482c600351900b015410340248120380055040000310007580d0100003442c0300310707c24900c0301d50703a038200740708513007004646400e4450125402c0700c00d0000d80da0300d0091200c01d1208201c40001d45c1d8031103490344200088050542a4519002c1001c100d1003408101406200d00400920018a43e1121a01c9603940d50507048600313904402da4103801850101c006010220200d2600c40d50310906403924000740c446200201d001ca07a0014889100c0e0400f240e07803940c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 486123723 1250 486122473 486122477
    0x10e060d330812040b0307050403061802030c010905060d2408071d04020d0b04050307020d060c1412071b170702040b09070206010302040203070315080c032515031112060a0501 77
    0x4598003c090140d55019600071007288a90200c00105e4030381c801c0c03003500c000b182c008100380052564440419140781c1034101c280e000c1c2c0038015140c0c5555028601e01d00031200090700d52880d0003881100c5c50001c092126400b10f025502c4584c448a04694000c8400600407900c040c029171440e00c1074140801c0c0c2004111015900d0035820800942e0f144000018065000130403c0c0f4695582c0c54140d0031480b07080c400a511101c40d032911001e0004550207001c1e00491500d52180b81c4882d07010010780f600403074a813a0504514000001c08a0344542d2003041907490781c01c20030700c41c8a082e03500d1451341c2d1840c41c2c818800400c0840e0b00300c203529140c000c2c000744e2942540d21070201c3c104810000c0d1100341c14000680283d030000080ba00d41e80c07003940000180d800502815004a0710f485c3c000743c40d03258281c0a03510070300c0f82d000d144c546942c901615203883d010f8040a054800d00c1d04891444551560281fa024142d40c1c40502180c082490020140000d040000c008141380c174004000b060101600f010381 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 486124973 1250 486123723 486123733
    0x708070c11041e140105040506012a0201020309030304030b07020105220609030e041a090f060d030e0613060203070501060b0a0c0605100306181203050402010e060d3308 74
    0x404903140e60840021481c0540340410a0450790010900f03050000c10900790180c0340402c0f50060811054150741070b11b0045400b4003079519540300440d40103540d2508407501150200419100c03a01151550100c1441030041d44d08002003800003d0039904290f10a441c21404c3c002045429039082c0300300d40e070100030b14000c2c105042c2c1100076214907500a000040a080c0d03160282003c5c5400f44020450481004000340495050450040003880d040c0e0011f03401141644042030b02003982000040c45600041d10886180070360fa101290001c081c804000e800c032000b00419022040e50340340704005030070290015a42c03402d0304c1ca001d5003150714036440790100210900c0070541082e400949240243d81141002c034454454480015451407140e1009044601c0c01c800002500502003403044c0450140000406204060b00150192401224024001410300b000100d0a207401000760584e0a54074400041001c4000c01e41d11031743c485110310071003da10709001c4104001e550848200a001c01c240a02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 486126223 1250 486124973 486124997
    0x31d010f090e07090308040f0e0a09050a03051b0a12180e071206080f01150b030105060322021908010608120a0f0c0510092904031101060e0f070807 65
    0x51290720180a001c0030340d4208030109124074802e00d01500503681001a040e07460f50b550404491032906441141c44004003d400104000704621031030f82c2c4950014040d10f030300101590100e0300c035482000d0309001c0010609244042010410068022910a205801c62940090340c0585013042c400041820000c8500d014800c5204074031545030820500e0605d01400a00425a03070041c0540d5040b00c0c14906c500c0c1343c2c500c0ca910054128400580a250700d140b51a80c031011011590300c024050990808410004a401002c0100300d040029031100001c0c0c42100b102d6000940030b511242c0c4140301150940000d205d50042072080c2d80052071501c00816441c940c1d054a166640102c045600c1489811824000c029000e000f480000710b502c4010b503408091400460030007802d0705101601c02810780c803d00111801030446000341816007020300c0d16155070701e64007101c4a084d0400030840b15501c51000191001c03102c2900ba004440641c002d170360303e2410300001031000000600d440104406180c4d45 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 486127473 1250 486126223 486126227
    0xc0606080312160f081902030c1206010219021c060207050703020306070c1a1e0108010911060405370b19020105010e070f170901022107050d0b0409060504031d010f 72
    0xc502c10502ca0503d8402c1c3e650714000d0402e0903469101b19403456000204121514580344010a0030510241210100b40c403aa8012a0b43d140b24100300601c03481000000d40240c900303c0e1962942c0e040d03141800310508016a503180503378104007000c481d81e50001d9803e00031450300b4000c0702d51120491420190300107107038a82d1440c5c4000d104013072304040d0003030003c81c10b143c11070a0340b0400c10701c10b00350b203031a15651020414000e01d060a0203880c000406841d0455074a090011181211801011042c44d44401c10400004051040602141c41c81d000c10110000701d1026031040289510442c064550100ca5913031a0201034420814046902d400014880020700c08420303a00f1042c54908142c07141042a0203403407100d10b20a09003030460304001000b029800540060050040e1510405010004c002c02040981401c0e5901c1021620034440080c0c1001580d00c80e05a207200100007090790062900d400080b500709aa00b600020000c60101c8800e200b40488411801400e10340885614040c1ca00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 486128723 1250 486127473 486127487
    0xa1b0323100b09030a020603130c0b120708070e19030b0108010501151404080105040f2108010b0706020f0a08061c5f030f090f010c060608031216 64
    0x2c51001c03400204007104991810400e031044a54058080c039501c0c1410403400058050f400e00c116410503402e0408a40010f640d015101c00b4018003070340c07081031384405209030389038407009018004000a100100c07011340d43c0e0110283d00204040013282019080d070130006c6100308160003047e66030b81820010007092030481000c10501ca001c1c904040341c1c00ca210185c1140d449a90301c11107240d801c110074031040c042c1143d8664a924031032181008043d404040b0307154548084621100841e00c40001080407a010400410035948219001858010f41c0d2030420565000341d50294005801041040403d0a190307204000c0c1500d01022068a010503583d507029507040c0f61546941b4050348000e80810403a007100d4821403140d042c4039542001c810300280c0464254250880c0c480c0388104241032207400004c011030710310b40110b0403102d15150200040c0803580c201e00740d0103410410864200b50104400307108040150070804041c550b500307140c800b80b05800f0342c05070481c06a9012050b46402140d00b080f0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 486129973 1250 486128723 486128729
    0x1f0e1b060901180303030605011b030f052d0714030412082b050a1d030412030e0306090708060c0a1d0604092a0801050d08030a1b032310 60
    0xc1a95a034441d06004072684034112640070640c107102e41c008010160580c00c080c05403a0287d85a005690205000a141500e030a40c0507001c1060301c5649035040d8890401040c0100040808440090030385030040e90411601070b500001603000b0480004200001c00c04406e0343c0901402107040509002140e01c03118680341c401402031300300050016031518814100301c1d26214184100c090b5030044407450700a05403c44480f20404d00c1c0c03401002c003607000d410307854180300d00c0c131001141414100410740286005041c01036092081140600216641c104401c0f44602d1484014001072490010709500d0104040d02c0c80102400a000300803c0544c4050794220102d10384c41d415206240c010041001445290018001541031000340540104d0080c80d016401c00342c00101c882904506000700c1c0c1c200800e004081e40240100d004601007448070001e141c221050a40002b50052241401107421000240342030202e61244001d002000c000700411031010040c2d00484464030300041c2c8009003c103640 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 486131223 1250 486129973 486129979
    0xb0a050313020a031a0f01260102090a0b04061d01080601032d0603050c0406030b07050705010e1e061501050d09030302040b0309010209030f030a0504060c020f031f0e1b 74
    0x300000d0385800d0540a41850282c0240640900c01d4403030600346281544070200ca1108650840412901d00000a0f168101c4d581828110140f51f00e41d03c504480184d01d4145190035902402002d803140e846981003801016541039030795855151003405440223110034104166039002021020440c0d800c0307140d80e0f80c400024a80002c908802a580e00c41104c02c044800d0171040c0511a48603d0345165440201a207004400b02c03910021800f0800c010f4400500005120034103840c0801c500030f000720040c01d04184290004646403a1900c2c01c1c82c0b60041a180c181d400d4540005041055402031000680221124400441c0d0455a00c0003a06038400d21858000321591081c09205040c403036415900034000d2007030f03900d58904090112901030b4100c81e000c0c9129001e003400e5503541150000403102d0004003503c0c1d00c1d040c1032034480280c9460401d0324040e40c02c61180c10351146540d03024031a540d40175158003482858465031549800480c2c805000780b248560120041d591101800c1c00c008291034811 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 486132473 1250 486131223 486131227
    0x518160b0901020f0708010218030c03070b0c070b0c0606011e1e030608030409060e010e01060903020f060408030c1501080a0302060a0c0c150b090a140601030c03020f04060201061802040b0a05 84
    0x782004070316140301c0b4610000c590241d00401300c0c8020f030640090041c8516181003010046180e030800d91507a0a18503081d81c5a480114200103204070440079050440000007622042a038135080c1a030340740d0100c000030859402c294100880303903801400300c5d401e0a000464214500d603450402074100c0030042800c03c001d84c6403403092840b542c401d42000d0064a590000d8985070341e034600b5080c000c0d2030b00d07004103090718496000110b1400c03a903e024504962103a90341d018241e26607001c1c441054820710003650091000c00022452160800081c142c030400107005000c2c4203448001c1c000e01002c1078020301c189800c188412004030f0750000300681c0240721008002281c1c400e40b201500c0c078032007822000f0716002401201400801c42e40d4810f000743ca0003614080000c0c4d507001401400c031141c03404944400116a004150035521944c0443c1d152890380c01c00502e0504031110164854000e90f11800060791900c03018800078440d64284401014401029030505040214040070360207107004000405c600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 486133723 1250 486132473 486132487
    0x2030316021c0b0a0e0607091202010e040501140f0306060102030f160b041a0a0603081b15010f060914030a260d060905070f020c0f040605030607030518160b 69
    0x6007074510407241c040d50580202c00c1e00c02d450030014007082158a0603100e032500030320396416000071413024421005070b9511408541081c1700078070200e81c00c820903030400120301507047d842e0700c0d1440360601828007c034541c495040c5180410041c0d0140c2c840c400c0c000c0c2c120000384072260b6000016650100d446810190f100e4102c0c1c000c44c040c1d840c44c80300213000524004144002e12400084404400303405841404190369803099010070760f0341a00c03005102001c100062044045070604000b0a80218420f50384891007101c54000c07412001e0b000410101203003d070404c5000d80200055000300011000e8109504160b40041d858070111700000d42440402d902209842140351041000c00e40c4610100340c8501340359543d8401030000c0e020f80004285000017045001e801100414441e4082e070b03004000f0885504280146c0594103e2115006522850007045a40d001c0c800548601020f58000071285002401c4a603444d4400030724070300310703000380712081d551400680c025000c1d41d06d02d0120b2780c4d0750300c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 486134973 1250 486133723 486133729
    0x40b04060e01050d02130204030f0209070305090c33041e050f0d0c0314100507021f18080c0a020306060d05070303050906090904030908060a020c0309040e0a0804030c18090203031602 80
    0x3506241101b028800240482000340544205606900a031200781d00c650320032005608842d025140b01107198800d91100c0725614191410721810207108034a101440030251000c034180c410014000e00c848000b01d418014206003485698a228826588855181c078000100e03107944030200545000320321019410b0284214554074000441d4842c2c1c01d05880458171828548130380001950074161401c160202c0e02840c80011031910f85a00c02104003401d807800b500000091180c0c07038103200083c0c9043c03410070100e54060080e01960200401401140481e481010b003090b100901061040490442c0da00c08280c0c0000c030501521f03418201660740703c62013800510107000e03103030718181d0005e00e64042000300740d030145c42c0a0444049030201c2c0d046454280c0d00070240d01810703a80580543c01444290103601d01350700414840700e03606003520b200c008103403a0790b48a6446508241d401798200c01003003104080006803a10000481c1e80308108507501c0781c0c000b989030b218402009900f020403404000c1555 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 486136223 1250 486134973 486134989
    0x5030a0b041407050306181e0406110a031506030c020a0605040302150a0c0809030901021009020a0306050c0a12021c0c1101050907170a030e01140f0a030b040b04060e01050d02 77
    0xb10301020708031620300d071490005100d5402242c040d40501d506a008645404130103130340d0f0380651010860045200404083c00c503e07400300502c00d840460f151070707240c601560301038024a10490140d8001c508045134034229480c108131640803c080515010201040b65030205003000c040ea0301102c040342c0e0780c80700d0400b01c1c034203000f4800c81100c0c0030b4030100744107151620b644000b484e00702e10746804106617200c1d00c00d00e85078015412050301503006840107920b142010343c0003180c0c1c54070080c080403044d5140d40b00d20b01218012590031000c0c04002aa011906401ca0701c00c5c0900504414250706d881d0300d45640c200c10700c41c250103000b8020340300c81c2e0f11012680200504c0b148551030400030081842c1c10300244c0d0340e0f0203041c40b641c691341681506d0320303d20b080081100c0c503419406803692a03500750740100440d844000742c1183c1644c1c60040c0450034011080c0d42c000c4c460b000caa6600803980641982c108800c50707021030719142c03156107420020012030303500d001700301d0442c2c1e42259040c0b00107503580082a149 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 486137473 1250 486136223 486136241
    0x10f020c0618011e1b05010609050c0a090f032001110a050303102c0408070503210702061b09030123041b0e0c1315020601030b09070605030a0b04 64
    0x38008140201c1d901c000d200300e80002142640c8000c200031004000d050308910b04d004440002d41000711412011440000b101c1c2c0300f030b1061000041b82d5a90341c1e4140c040b00d109485000303070705000041003501a9408039948000c1c01c00b6a00c808952440c0d9940c2c0c100000c0c0440c8207580c008070007481284a170303010308103080d01400004140c5010080504d0302c55100e52048645900c0c91f002642d0100d04401e03071080f10402ca110340c49600745000104002c5200301c00bc01003048424010802c00c2200181c03040c006400c003c95001500803900c1da801c4d10f20201200000c081c84215030103e0100000c420300d16054107599800103007078644d140402d1380480c3c090018200c0d20344405013030700c001200784040b001819202d0307401400074090900318030002110302c100e140300341018128000701043c00180b03460007d003140100c04601c00c14407603030303013900c075808510b00107540000d83c0088004100b480300d6040126480102400940344260a2000281a9000c050080c004050756503903403d10075150380d4480703d41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 486138723 1250 486137473 486137479
    0x601230309060f010801091104241d0f070e0103110415020709230408130f06020a0501050601090f291201060f02010501060e040228020312180705010f020c 68
    0x149207007400c1c070180d03034810a90f600032807000e601c1c000241d014010300ca0001090b03440500d440360364504000b040050b040d00d0707241e441600c250019071b41401c4c2c640c0011800901c801c55040c0c1000b0120041e0f144042c0700140408a0418944108a64540e000001a0281c0c0c02428002111a628030303206ca030328000d0707030480310a241003031201c850b80c80c0c0c00042d01000c55601031400e0100744000c2031400d4013a074800a0110310700d0404408240060501c1010b8003a08100100d886403060f41d6600c285040c005a07400240036810600310300045c04402c0c02070680c040028205038074405c0c5050104141d0317036001d00c6002c0c4401d10004490301281e441032014050f12043c80002e984401045c201c1e20410f8800b889038601040704500c20b454014018058903041301d40c15191010709248040500c4003941c40001e01010f10344401407500c9008441000d8443c6024880e401161a10510340d8516420500a401c640720b8011004109005c0d860010349501910028a8038105403044c85009a24243c801403185034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 486139973 1250 486138723 486138727
    0x301090201122013091a01090e1315050601021605091602030d0c02013c0209040213080705010e09090a060e0307050a0317010b0c0d11100f0614010f08060123 69
    0x30110801058440640760340701c004200a104503c044c106d00c0b05281c2d0164041848101c04001e5000003528159201c0151940c11034031f03074056a00e40f001e41a20132000d0f062740380e40b801400b03143c6d6410030171400035403d9218080c900c28206400680740f940c0081521110302e04010714503919603c01e0090741c00c2c00d9054181442034071541d01e0301034040c0c207450042101c492148000c0c094541d0143d8159075414140c40032924981c20140b1103c0040d51040f040b064009408000d8900d4406021442100524201001d4030045040034001051012500201440b410302038043c0400030901050342440c49910020002c1c486100c0652982140139004018085c2d000b0740506005041e00005ca280b0100550b01c49005907a0729201400518000d0b10010744141e030010404003501402009040304190040c0d048801c0002a041c81c9010344006220b180d04070785c0c0b01c0904110074402c4011f8030103c22800d0030107a400c80742c4400c00800c1024010440303030412402040380703404052800c5602d43c00c00c0741216055 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 486141223 1250 486139973 486139987
    0x209030a06021c0b0114030105010f1b03020d11070308190e15090102010f02070506060d170d0209040f060b0a081e0103050309191206020f0408010204030c03030e03010902011220 78
    0x154400700e41c1d03180740f24503420840c1d4255250b208242120b401968a130704142540d0800c0f004503240040c5e20009030a0010030401110300d03900c003901c0310700c1d500d10070ba0051a03404110303c0020642c009503480548682e04c10601840000d04240035512600303803030201006101d1100308200c1d44c0070720400710260031481800c0c03d0010a5210401040e01000a8000348100b00807151010124410000042d10f00c0d000440804c10034548002920000d9001e21800001d0a0000da07222003181d22880c9880006540013072401d40318101802045d842c03031940e03071080100c00c0c036195055000307108940d00d810800c45000001035000c0b6040c400b84400002003024040c440d0307180d207402c0d5542d40c00340001910440716180c031003c14146e102d40d0b84040d200c80224509150350180d44400107900400c20080850340284004181104248040d1009500401103000a01c0ca9402c0107071804141c0c2e0715140c0030781d04100c003990260741c0001183c034030701060200010356801d11440340c5d4040c1166104000c00000005141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 486142473 1250 486141223 486141247
    0x10e12070803091c080a0b180a02030405010f0c020c090f07090b0a120906140f0108070501110a0204051003021813030c0f0609060204081b1807090f030b1608090a060209030a0602 78
    0x5c2480f50503200020440011080c040143c6410311110400b941104800000e516014039006181c002c2d01c21000401c02600c410141401d50781e8507001c100041c1e0103010755900780c0c41d04046198001c445c2000361081030400300c800a0003500b950052000b030b10000a03403c0601c43c45044041e003244601c250070403c1440600e0100060318030202d0404200150380c0c04160440ca03018442c0741214884001000f80c10b01e02001541c04c68211103401105024030251140076072900e00480740305004028121110700d06610400c040340da08030f0701001c620ba00d01e100f0080c1103000840c01c01031060705030801c62401c58481c03401441b4007940040c02031150b81481c039007901b0041550050300a0302d04240c2a214400104080072240d0706058065992142001c0526410382c0c5c45500410341100300c91030620300280e01d44400c42940081c5501c115003c85040c0c080110090094203001d0747c12005141402042c284003291903a01c0758050009085550f001941e80c07100e5504014051b1a590f0041c010754650002c0c1c030765 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 486143723 1250 486142473 486142487
    0x4020105120412031a030d0e04060801050c03090d09030b130609061401050319020a03080d020c0d050a09050a0b0706050c09030f010902090a090201080f09072303010e12070803091c 79
    0x90b041c0480d017040710240001c40000180c07024280c01030014005d4502d020001c6500c00e0442c031070a034006a542e007021400207020b001d40c2c0d1144039100c071040c0e66810038804140ca40342c000c4250000b08036510006200143c2c580c180f031600055045040f442d01103403424640000c04441c0c0004002500c0c2c440e420200011541d0540d040f94003c03811303075032084440fa1039a148100d5005000b0351000040760701344005010300001d80b07c1500548801402c0c01c82c0f00700361501d4150485016808074102140081000b0381c0502c0901c050b1030250740603203110389031411929640c020031074000c0c0070913212000109800360281c1900c0b180c0c40300508540b2401c0940607100d000b080a06820b90140040c0710004038000074a000e400c0c80c1560680d9810f8850741e511a6000e01042d0180c0603a0690045d1080010110f418242000d00c0d48040c10200c02070210b00400c01d800c41b01d40885514a0381c000b210740041d0803288000741d8030920307040700c0215a640e80e030718901400d000001580e681d41041010042003880c0c1e024070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 486144973 1250 486143723 486143753
    0x1e0309100501032003011a0d0c120302060f0c180103180c140103060906080a2a1710091e020f18070207060302070c230d080c19020f09040201051204 65
    0xb50000b01382966400345400e980e41ca5140b1140d0780e01d91101405c641c00c110b1030f5030b90001e0140c07440641c96074540549103584502c0c1d102c01d800507480b079020321480c82800b00b2015000090256528a051901680c0c80c9541e5110394046041c5660f810008034094088118852556805589490740d103890301130742d04041010705070041c0007a14189021600d2500c0d48034031001d4480010041c40365021a5a030300c03624021001e50100082010311a131078a81109011b201e001d480350800c04518440924951403421041c50f401020560800c00c1640c040750350941d035040c0002c030300354000703584801d0344c004600040340e10f1102c550400103003072906134441c0d11102428000d400d180d00b61586a41c1d81c44045060303004034100034020b5440c40c0701c00c0200802e50341c080843c86480040d40321804640c80009078044100e810203840600c40090101248101404014400f020100210382071142540100300c0a4038001c403400c0c010401d60703000c00e0a40e1302483c00d944080c131107103080300514030b0145000907030444962 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 486146223 1250 486144973 486145013
    0xc071208070201112805040b040608061206060a0306020d09050a0501090b0f0f01050915100c062004030807020a03051614090702300a0201021c021e030910050103 71
    0x4d0320a8030301400d5101283d00f20500d120b80880403400f04804030080342e00d118041020711800f00f1000803486105800f600c010619030300c400029103803103010700c1280341200c1c80c4030055820910800809603986c910740310940342c01041c01070b268544140100300078880780d21301614521410302c6020402c64150045a11707144900603822007a03c1e01800540b00030000e482c04035007084010018000c50070f00f0481d0690000652640c03861480c49503022407440d40043c1d40b6040050311081d02030090211034090800e0140320301c1c1d9207620403004043c0d0300906002e00d001c0149500000a50a019980c82044090156400c074054032101e030705900416803101c549124000005039a00106d04440c43c101d401c16100d1136036900600342c0e43c00904844a1803041000001c040c0b600004400d826a10015014280311700c07150f000183e5032a0b960722004c0202104400a600540c01000040640e1001e0784100011104800a894994032100d0419003425042d00d03100d03521502d490700002c1441600505140c03414002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 486147473 1250 486146223 486146231
    0xf0a0605120c0a0807051302030426090a0e071209052d0c04050c03040209090a1401090606050a050f060d18080405090702060603030a0c0305090603150109080f0a06050c071208070201 80
    0x5945051720781c504c52041550011071755480e04101071840e00115842807290a000f840042410340f100c00e5034955a5501c81c810310302241591031424a4a8044064802c5410785e0f1883d04c0c000070010801084006000d4040b900c0754945400c2190401131240f02c00700d90000c0c034584503035180504003544100c0210149074403e140c0408030601303051180c42d00aa55a02c4480d1840d0380395024014400700c050b00b6804144505413590000c152841084450a4844070000c181d040043c03c0420a880041d041140300c0d201522040113596100c6070390040c0c0100c1620714540320082a8210401130034520040074584203e090740c0c90030403111900900944004441e0000c860301c0e12603040b83e0f904000c56100e501544104514485180145a010205031083c5800e500d050801004074409410a54040e102906e003401d07030040540e0055a0304016201c55001051209404800c05a84282044020301000c0e40c580100d5485071441086407409a000034104a1103903080c0c00c002c0c00244216880383c010b510f4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 486148723 1250 486147473 486147479
    0x708010f0b0c16060e0102070f030f030e060d050f06030d080903121b041202040501272007060c020706020f0304060f121a0901060302120f0a0b120c010e06040e0f0a0605120c0a 77
    0x21728412707090369081802d4101c80791640d5020346d1001c1c451554181d00180c00c0c8a0180d1450780f43c01118070500c2d83c0c03605c10b0740f5820441e00b0b2510780000000c0943c140306003482002040316000050311240300c0180c0c0c900000c6c2c7c9500c03404c01700044404a0026040400007030208102d000800c040c5000c03403098401b04010380e629044034040344000079180b841036a05d9000d60007145d2a6801000c812000c14401180c5940f9090707040c55181e114040407681c1070b032a40310010b80c90b0340510051000340014005072801c0f402d0240559100c3c07046000f01c80500000c1700b80c2c180818410000f8030140002e08104020380c940c40403051440c9a81601c400d4032903502603001040b550b119000740c0d0400c61040e40380703449a80f40d008031018800001840f14403200d03503800001380e0a0707450301030b95040c2c0c01e400005402407144100c0010941c00d002441607020341020003041040d0441c40b00d09039880b030403000c034101c040d8640880300c2c000381c003950380025880160301c400280c00401c0400c441c2440d510881c1c0c0c0d03542c0160303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 486149973 1250 486148723 486148739
    0x90a02030616020a03030c14040608041e03120e160e090f0c15160204050c0d0f150e04050f16141503040b0414071403060708010f0b0c16060e010207 65
    0x19000e0400b40181c0240d880440028043c2c0c010303030511125424804100c456152078032419401ca50321400004420302c0071311040c05021510b288140c5901402001508681d407000382c51024a04610034071242e1b251202c01e1410028020f4a20104601050610143c0d03601100031040340182c03120650303400740e60165014013500003004c40c60350308090104250040d0307078426851540c10441441e04800340103000540183e40394422284120384000302c02c2e468102c60007a00381111071401000014030702d04162414001e411950440032102e80b20000c0c100703941c0360f103407031418030701c00d00844600742c0306100c0c10340321030100c940c034800944201840510b695803811003041020540e00040c4414190200007080218580030b00e06a8031500440300c0c0c03111085072032004c52a1506e43da1005900307030101c150f6401d5a20b02446000c2d004081c81c5031020181d410580c6844052502c4d1181041039400014031000c9460148103071004462200040c004469030740c0c1018045244c3c1e4040180180120304d0003003201c030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 486151079 1106 486149973 486150001
    0x100501060c0c06050a170606090306040c0501030b030c10051608040621020306030d030b0f180426090108061c030f03150806150604030b090a020306 65
    0x80340c1401c1c01506901e558101908004c001c000c007101c03c69000440303405000c82c420b02c0401e02d880d0300380000d1403482075039107658042c002c0300704100c1030005400c248000c983c000e0302e0611041c103120080507241c0d4010780310280d101300b241c40e0a2852a1044003c3e052041d00c00802ca0751400f081c4d190b0708c689401c00d512000000c0e203012038038501083c0740d1070702c0d0f0700e42c1510000170742c00d42c05c1c0680065210f58201c401034040603568004589680e5602c51061410100502084400080010240c00700c0501b12401d692036407846203d1907400c04000c0020111015404100781014521001120781d1000580200d0340300400c0c40c1c04e100111984440c0454a510035150406403656412014044e18030b00d80c0c01800c0003071f130031008010024020030704641c4010741c1114103084549401c00030b41e15000d03940005d800580083e0402100c00030001d0900042402101102d10958828031503940301 = true := by decide +kernel

theorem cover : BRFrame.Cov 485971223 486151079 := by
  have h0 := BRFrame.cov_init 485971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 485971223 ≤ n) (h2 : n < 486151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
