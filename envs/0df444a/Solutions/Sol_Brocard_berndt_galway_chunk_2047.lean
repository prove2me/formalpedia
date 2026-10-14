-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2047
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:31:42.490989+00:00
-- url     : https://prove2.me/submissions/d359a58c-4c81-43d1-9421-99fb776a93d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 367985611 ≤ n < 368165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 367986861 1250 367985611 367985617
    0x1e021803281a10060806180a0b01020f060108100c0c0b150a0b04030605042a0605071b060c05150105030a081602040203011511061521010c05250807080c03 68
    0xc2c1c544007450403400d02e900c00000007200c030303c074150018525000064540c18040340c01c0020142c5c0c1e24140c1400c0c2c07510041a800b81249801440c1144602e0007120708100080201d58001c26010303002e0000c04908501c89802c6e500c0e028501e1080c0130300d6031b08030400074507400d05003036211090f100c0245040c1d59900c0090022002c0b52f022611185011401005003c0310b58043c40c00f9522400b8410300c0e8030085a502d001102880980d4207002080040404c15503008400500400348645600c0211002a648003200075031590040400135810580c19420004104000d4040c40d805c22603100700c5614100000380e030340c1c0712134000030803038000070405510551440707165205169000b4425501c9607118040c0408500c0c0d0510394500194081c002810003220200341c240c0201071008014402014000900440c1c5c20b0b0003080002840d03007601c0c0511924820b103d0f42140c2210350750385990300c504002030082c0100704c000c80000c03043c074019640c90010344040121200386501c8ac000d1500da507842003c40d41140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 367988111 1250 367986861 367986893
    0xd140d05270d020303211803030402150702040f06080c2b080705190b010f0e07050c0a0501052d09030d09020307082b030b0f12011e02180328 62
    0x2c0b1012840b01b00d200307661480070841c0101da5012840301d5881c07044c02c6902e0051003800d050190820404500517051014186000b0071421000710328000301e980c0400c0c101c90704055040740c482c0da076680a024071241449042560300b0121030580130101040460548440908280364082d0107061040c0b00300b010391425601d090381c00c8801c0d102d40404843d0005c100f41d44070b2800304d801060107400400c20061004400040d1040b001c0c1815180d512100300b0b890640c0882134001d0a44100e00c51040080d20034003400f8440e21010b02c202d1004803c1e10303030098546036407614001e10b040c1b8523002c10907400d90000035200d2130020454040303640b03541800800d007408840d03000103489020350308004c50704c0b83d6200f0034000452491b03207491451001e140c400320b04035031042c0c0c12a0b5000e010002100c80c00e00c0c0540710444010080000000d000c804014001d07000c010910b072650480e07401064120480740583e0041d091000190090b00580f44280d540d1030141310101034584840c800c442c0044288401c0c11810400c107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 367989361 1250 367988111 367988113
    0x3130e060a1e050a0f0602030f030402010c0f030f0e04091e240608100903020c01110102210f060a03020d030305190f09020a0902090d080705010b0d140d05270d0203 72
    0x20103001200d804815101d400741c5030262401d4440040c8030741d42e51740010110b900c158051400d011801c0409201c80d4400782060741003040e0301c080f00003c602103503d0450040d100b070320b510b010300e207003010042c005040c0b40d5040d61065113499500c00116400c50404510032041005c4540403800601d071100d400d4520304013081d96140000c802c100b00d900668041425100d4a07030444a030704000042190546801c8000200160460f451083d4194007070030340e1a4440c94950005400d2000103c007450a1031100e030b60700112090030000b48030000b0304200f050b503040501500c0e1000d5082c11500411134013034100300300400f0160fa07400014a18442a50304032908080c050043c481c003a0b41d4502d6401800071060140d116499074500000e0310900c40c0300306c88140d40d020306070702004000754541d520303550440c0009071207a540f544482c00d111b03a2a82c1c45911628421482c4102c040e104420300d41c0307496107014142c02448000c12103e040456010441d00610303c0d03911103030400c02402400319500c040f45040003501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 367990611 1250 367989361 367989389
    0x9010309020301320f010b0a0302030417030c0d050f010b031f0509070c150b0f0f03030f04030f051204060e270f07020f0610090b01050715091403130e060a 68
    0x40c6184c02035140d4010074641d0415541500d6421550b02c5101080c85003d8100d4410810b45039994065000703160710500951500e200c086841000c0c2c511513000b15884d010488002070b160354881c0c140e04c12a6046030044d00c4814407981080150300301c40c8400340012150301c01c0d103804c001c00802402e5102c03001d03120251800341c40c1c1c00d00d08005003890010b0340c0100d48801c480a01e0502c0c801681c07181251041e070041515500504480501c21303030816074a440c94060000304507d09005610310000c000662103060040403c0314181000380c1010413200420f505101c0070002001030550207505900f081d035045900301c0039040c104e0400010060301036401c0c0c40b81c01001c0b003040403494490301d50394801c440640035141204041e8119548035401150000b24683e0450341c04e10448049500040220406041103032924405031120205421036080a07405180c079140113008018400301c00d050100b440800850400307000009103049800540600035910440d440028115a1004541c60061442d42c06000c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 367991861 1250 367990611 367990661
    0x20d02090108090114070e0d1403030402010905010c0b04150b0301050f040309050a3803010b04050315060d15110c10050f04020d03050c120f0a14030c09010309020301 73
    0xa50409104180811080c01c0001c0c941c02e030602600c2e00e00d1401c3c00c0501600c2d5128001500c0303162111460326040030306403541800180384200700c00841d02c51000110b450b40380038800106200320540001c1d04100c150400000010450f00303085402c242e0128160621543c4694098000d0005001a03603240d801c000501485001d008200b40c0603500030342c0c032268030a480b082404404012441041eaa02d103000f0458622002030410713007a1454143c0105050311009008040c09940080c1c20081c980c90000802700594038080000340c00c1c0443d420340c0e6106510340032000440c40d0f00d1154015007540c25048106404068070f80c00303807400d8071800d500980c4842d070300710143e582c80c918000e00c800500e10300000b01d000c03001a106034500c184c0e4000c0c40507541d1b04140d80c04681700c0e000103801c4d000d140318041d4503000c640c00100140060403280300120741c803240c81205c002d200b21001c06544410b4034040003032000d00d40c600d03422a0070924080c200410308244501c0801e00402143d40c2c0310b6050314600449003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 367993111 1250 367991861 367991887
    0x18040803060a0806010605070602070c03050a140601090c080a0902030c0306010605090f030102070203030f1e0406080a0506040c020c0114040b03041a0a050f160c0c240309020603040602160602 84
    0x500910050341d03042d450b50f40303481546940744c40a00900000c150140580000102981c004015a40c450024036005c29543d940341ea141002030603088500d04204c5000016440c010007003103004207201a070521041c00d00c40e4014000350006004541550f80750000e00041d51010014111030700c0340602114100c2d030b510000104035070000c911841c0720b00041d0784d0141c0740c3d103414000e82e00b12513001406141360803401a9501156800385402164000f41d00e918900d44410010191009085d551580c206a1a00002d5481102c8009000512481c42e0030b6861b85926030001e859160070400782803ea1984050241d0030b08a03000d164044540603200004100401c0008000f00d18924041d41158583da110050b9000a55008940140d2180c5034100040d41511907070a1105031031040f0701b040c41401c1c800391203038841c0c0b0005030010340058240003030b0703510310100c049032035101c1c0252843c04200d0801e040e0b00046e01880050000307070200b5004100750034070075441003002118a80c010700455444100c03649032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 367994361 1250 367993111 367993117
    0x180201260f1515031815190e06040f061d0105010909020102061612050c19020703050708030a09140312181003050c070605090c10030e1c0f0c02180408 66
    0x311241480301c00c6070010703403e00e00f4403803074000030001461341942d507455124001c6003656216064140308401000c1210000712800390301489200d80000c8415001e183d01d50185c441030100c9540d194041c100308408120030245203028187d0080002c213048000082003100880400c00740c0541303500c1c017400010540c40e0343d07010914051003a0280d400d60b0b665001c48001400c0116031b107401107500010341000450313441d44183d62100324590f030319007404d11400c00b41407840ca0051480005d42d0052900f030050110030000b42c0014011880294070741203001c4c0005180e15490320651080000c1105503082c0d03a80e00344040058091940384680d00c0d8038a001c0c0e03000b540200401614060818060000c5440d4070034040d032441407260364500361800b00e0b1b1741d860500800004100c190035000b0301203140c90b65990b000050000c0c28041d070340481c0c1d002912400d241003401c0940c9010340041c001030700c007182c40e8000d441680c40030003500b020700c4034610f94004a011001d5401c1d14200b03000c5080c1c00c00003005458009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 367995611 1250 367994361 367994371
    0x1e020609010525050904020f0d0203090f060601050901080a0b28050f0f0d0f0b01180f0509070510020a0b18010b030703150207080f0408010618180201260f 68
    0x303100d242c482e03c43d0b2501450b00c0714a454441c9068005580146000758014491800040c000502e000001d0300817088a80101d810006025000002e0140304034003041942c02d4040b001000e49a941003020020303010303200c0e2203c0a0705014200d000112020700c1d80e441214240c2000c1c041406201c032000680007041c040550309940d040f10f0950214090800e002e02030214400a420806030404007002c100801030304000490710003454080d003130000b60740d0700b50440c004c103200c1c01405981b44c4280e4401c2c0640302c0c0b0800c1342d00b4107442c000401c2280e02000030320740202c0d00c040e2404800e1068642c1c2c01c174200302044001034007000f500d400344020100c01450200d00740714054000c00c000c0b80303110201603c070409840003911154408507490410000d56000700304440c49202840e240a24810003501181c005910410b41030b5900e41041000d0840314003001c0043d0604602088000380e07284c903850300c0d2950400701070304001c0d054170045030003c03c10b4032003668052050045200da00d800c00048818640c1104d0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 367996861 1250 367995611 367995613
    0x2010b0a0608010302030705130f09030504050102010e0c0a030f23061e04030903140f07080604050d050c0a150f0203091c0f12180b0a06060e0a0e161e020609 69
    0x2400600184190b4010b810799600a014002c403a2501041102c601014904044035641d03852404100405500c61865158840d40718a501c8500c0c103000603084840d07200301070341030380c000300044140c1d80d0381c002d54001a65448000000300d000075040402c00103004540901260303040d0682c0f0440040d001501c0c40c0f044101f885401081240384401e801313100b0065800801141e0000c4c1c0500010b013083c3d54042042c0d2007441181c103142e8150700c1c800c0c5085580e52141140b504403005000c01d000c1c05000e00e04240005040c01481c28100031920742c1c0e01d0383c2840010708007100910f0300d581c103480f0680010b6616080b4040940d22401c1c01c10300a911440b20a0040707540050801405003610b000b4004256540c810b5110180380b9840c0844000181403c118080c200f405404135603000101c0e2482d003d4002da10303044000a13020b040a1014012181200e01d042c8900c0d5482d40400910083c40102988507a191b003000d0001c0c2951441682c000381c1d4142555041d0360105a4100e0069000800c244101c0d5900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 367998111 1250 367996861 367996879
    0x61d01030c06050a02030a1d100915050c030d05040501060302040e03030a0614030c1203040905010b1306140301030609060e030d0c03180f12021002040b0a020c040608070924030302010b 81
    0x31000d443c5131040e0881503015820610041111034090900031410000081c00d203540511003000103951544000a4000030030018141405140e100c844107034051a25400c207039151120300890655617000d580c82050000d61990001001c101d401c0d0061030046078090402d100c080403079440c0725100d42085070049203c6192200014585940315404480400060040c0c01112580c005000c0b0300303581d00102082600c020000002e2540f600d100b400d000b0207800101a4480c00010021480400643e001c1c0c0c0422640c1744218100d50b5103101103d044a07031000c1c0010300a2504d141c01d10107011200c1c0203143d00d00000c140441c055020342c0004504080950302004071401d544105060354a4a40d00a06482c0390760a2940c00503175401d0420721a4480e070b004032200079030502c080744180d074403940264000d51001f044041c0101d804001e04135182408a0302440300d1401d01441c2996a542e40c840e22200c41c0e01d07061107442c960f484000b6403030340054070481140a217849080181c080c000d840921030242c0049 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 367999361 1250 367998111 367998119
    0x5040806070f08191808130e0103050d080a0e12030a0c030218060a17010603150905091c050d0e06040c050a18020d0b040c020c041b0203190201061d01030c 68
    0x215000302c8101c500c0c2d1a20f600d20b848803042d076820b1850070003108100a50b0707810005610110b0040c45030396148500105079030b50395101941a020740341035020000b4256000e0040c80041d00c00300d00801c540d4280c0c500264075954403082940036007010301d0801c00d01d0090080039500b0b8010400154415000002c00740442004038804030300320311a6200910401d4071a500c518643d16082005180b00b240503e0031404030800c040010b2034000003a07000c1008240d403041040c0181d4a06000e4400912024004002c1440c002000f9611000c10148200c0d60039556080d0075403141c000c80c01d540401c21108400c0040171a4a55030301c2e95140c0641d419645014105000141490f00850090554030403100340d0882e00d0314181d143c4003a40240001c4a80c41d502d4044103201030f00e461140d422103620341c0d4000c14500d4010360a00c02161031485c10003610300300c035011490800c1c0c0c002013114031000c0d044542c40c65480158201728010701a81d007190303541c594411203600c02100f803081d03aa4142c0c0d0040622071034403995 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 368000611 1250 367999361 367999367
    0x309050a030206190509060d020a0e1804062f090f040209060409090201050f0a0c03030f02160206030405030d1d010e0c011d04150b12090a021f021005070504080607 72
    0x3103200081d40444100181442c029400009510760a40b90600900f003d0720b010002d4825003100300c205074180ea02042c0111510303030000007440c5a1109407002c0602c41d02c540342c1014005c100a102420080c3c40301c01c0d0344e81c401201c000340f220012544640280710052058a85441ea02c5401d0091240e0015500542d075440d181c800c54143e90b8005000364542407520140d000a003504c9607003170303040c031000f400b460034181c160800804840c1001c4e03441c062841400d18000e4120350070740754200240f920600280c20411040f42000702c9007034040304c030152247c0d03440c640176181d4441c020000c041c043c14141c1149203079020103040850b408001c40240011980e03d08002d0350b0303030322240b0a5400900300827911b0a0140e450780604001043c06040400d40600b810300701c1b86130100a40c4298811400014024050225036000582140014014100207030641e00003802c40100d15104100d050f120403460000036000300840d840c107105014061083d8605110080d0641d001441640c81c14003482d0700080313407584 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 368001861 1250 368000611 368000629
    0x2040302010e060a2010051806070807030e01110406170105031e0c0301020408010501180c021e24060109050402030613020f0c0610050a060e010903080904021c0605031203090d03050403090509070c030905 89
    0x2003d00003c09455444ac04c04448203180603000b0b00500d69a00041c42040a0070f018012181c0144080e55603200d1810000415010b0b101c400405c0d69203004005020564011609181010b0640c841032000c062080d0a181040511110b8940c1580b002500044201064202c5412150059484012484444442c805660402d08020b0058000c9050550304414688440100702c0942c0120f90648108400c051052a00c001000c922002c458040004569000d00d030803028090544065085051842c0400d0010050b030302c10f60310282d004602429410582d900391000140140200c2c2e146080c04100700c514200c641c006c082c00f400b12858089912805044014407040e0103a4071040b07002d1070341c0c0320364580360004015142d000350208840800c05500f00034203909100c9081001035202d183c0000c0503d842d0803500c480070b40c0c0e54140300304009007070003040c2c0c40043c0c010b83c00c000c68107955501e000c640b11101500059840b1803d4828011a9640440c03112031032031003a1508036030f4586030170400201c45 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 368003111 1250 368001861 368001901
    0x7090b060703020309090c0705030d060509010618090203070c0b07030b0405220b0a1104080606120a05031b070b0c0a0317011a07170a020a0606050402040302010e060a201005 76
    0x780c030170054075140b404d11700006940403d52504040c10400c03d80d0b82d513411030348100a1040350b15141d000c24481c900c0c0c142d042030300405050510013455001d20551009081e158030a0f04038955000c00095101e034003031521210348940c0b0040c41d2050b4038000798090010030010343c03090b025034904000941110140c84051071a80150940480e041615070b84600c46000e0060038406a81d80360004010b22140b018080c2000d0090000989164500740d000c1c0302402c00c04891090701e5030301102d030b110080350700801214641060f0400184400580c2c0100c0c901c3d21595610680c0000c000003002c0105090104808050b035202e540c0318141240c0c5146420041c16080c000c400c20070344200d403450803100c88032004111151155803131424441d4003180c4800250050088070000da004288000e04204a500c2031a0203820102c904606143c00c1d80c000070410350215408500130b07040000c3c5140c0c0c49000310392008801d20b507480400050b041400b40c01d40c4a0b28170000c20080306c1c0c10007000c14801d0052082d02c41e280b0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 368004361 1250 368003111 368003113
    0xd05060403270933061e050415140307120e06010e070509010201090b09150c0f0a0c06020d06090b0f090c031519090537021804090507090b06070302 65
    0x9420010003a0060050180c244a03001d001d07440710304208807440a154404080502066105252820203016481400409901c0c145450b1100712140c0d00700043c1d6058075010381400246501ca0203090701e02580b402c45502102b031021041260466200d14040b44890700075001b445020f0b41400d0a0b50394030400e000f6070a00140750400142e0061049001e858603210520011036007401c5a201c0b849130b8101542e178004540c1260b40c1c00c0c003c505607204000c0d086850107652524110046203030086500400c1440010083e4034609801070100d41c2d016150041c50b03041c030401c00c0c107035106103000082c036400008038041d00900c482540685805615144584143c1800601e99075440c11900403102540e5061640102d070000031b2504018000380b00d034040e0442010000302d505050301e82d40f08080130311420722601c90620303031980503011040d601050014150b8101584408003412a040701c0c03403211851a0304907242c01081e6082c428006081c404a9600d90b00800000c4c11260500606205080001e009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 368005611 1250 368004361 368004437
    0x306141b09010e040c0315030c050f0a080a030507020a030b161202160813030b0115020c040501031a070e0d050c0a05030309090c070204090b070e04050106020c0a03110f0d05060403 79
    0x224113242c1c00407110b4462620700000c180c00c00318440b80440d00590026914a8003104e070500480c1082201e4034401c5400310384198a15140c2490031b90760702c428644c01010404040740240031912030030b189501960f400b407204d500c1c500d0f0107594112508401c401210000b0b00718003840020f88807500c01c40304c4079540a285007440ea181034a46041550140c0b9145020121050001002c0340071054168061301c0010b400d5141407002c40340080c5401d61100080b40b2403071501c00101700081201c000818040f921885404c407654503000143c07400c1a0300b40d03000d80c0043c80700c0c2c1d0312810000082044070707101c3c104030389040300c5984a070281036580c059421615041074200010400c481400e002a001040c8002d101141e1040541d5880000c580c0944d1003801245001703003018114039183c00b0311809011300d4801010039041100001d0708603410303880090001000200050b0403a11510301c0e00d80c0c0c0c610007810810031240545800c03a41c80900710f03002c3c1d000507000a08100d0b0203003040c251246e94070a0018400d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 368006861 1250 368005611 368005637
    0x10f0909050312041b08030f041403010906060b0903071a030c0f0403021011010c03051b09030a0506040c08060f07090b25060c0f110304030f0201090306141b0901 71
    0x1005108084041d68103110a11a0100e000c903440811441140302c2d01000d01c98101c218410040b82083d50404c4405400a01108420000110a036001c5806038454400190200c0d00860b00400e440d88010300391505040c07000c00c201940b88000d024141d410740464803010307626100600101161503254401c410700308082003202e209070b4054140d410440c1441481d00b50350394001090900c02c5e00b5690301042d0004040b501e04982841181e281300200d042c240941d1418050200c681c10400100e40e5035008040b40103c42600c04100d070000041d03205048803614282402d03c1e14040785580f003894401e10514001411040f9075a000d64041c4040c0d0303d6100a09081c102c405d06a5040245410712219601610388951408020302d1804240180b40c000781c51680c143d002459030320b103c0104014002c6195a580e825140001250110ba800151030380b609141d0344012250b16000b80c1c005003400b400c15030f102c46c040e056500d074640507032060300c0e640c3c00192191014070395034003510100720b0104440c1d1050903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 368008111 1250 368006861 368006879
    0x20303060d0f2d030f05070c050402031008030f030919051f021c0e0f0a0b0a05090307050d0503011d0105061c020418090501050c0f03070c020117040f110603010f 71
    0x9440034400c5961401643c440081d0010043d000145032a074065619180d0003031541240c0011441c0324107240151600020703440304c0003011041d103e102e01031580000000d64803000540c2c0007010f04041400d9a584911181c403c1c9056001903910b00c4460080350340141c0c0901c0012041c92125900c40040c040c80150100c0f6450101012645401000d408010176209010100c2e00030140b0303111203000007040303442c51950902e0b040714024a403202d6846134010401003058292199441121444042081d560b5a05007600314024880020510b104a01c0d80803201c03500000914140d070401b200c2d80d1100c40c0c450340851400e031001c0c0f1034181c002030b00300110508082422140c1c05032403104c180c003619041d40c503411442035144402003080d01d5551500510104682030141039008100c62012504142065000c8500c6220142c90901804058039400c0308690207106181401500030519502c10715003402c0180c4020b1040e8800c4864035844180b03903009207016000c3c4ca059500013071010fa00242007020340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 368009361 1250 368008111 368008133
    0x60e011a1c090b0709171213090c05070506070206040b040b04170c0312010503061005060c01061d090d020f06180c12010204081902030303060409060209100201021801020303060d 78
    0xe201e0310000c0c0c6036030340c40035840340c09150011441540f00760000e03d0425401000011641c00182d00b500e8204a649000400012550300d159188801c8070f50358040c2d8040071070000d9075503005040d0242040c48543d4143e41100c007030b0040d14015019034270130390746500c4100d071a144100d41c005c003c100f19601003000324003503a0007294014405d44410b807000701d8165201c1c4941d04038004030640e40c0d0000501d2814510502011801400d09078000c01e010b0600c1075005441c004980140c82c000d18000c02e0311008043c09401c088018503c401021550034007000f00c0030100c01088501300c146124a6400904a40c80045c4401e4000e0080c40605000d45034079500b5140281c03054201d00e410f10411000ca19103595080b195020005420300040c2c0d910318102c01d91f401c5c020f1203140860b5030803107211102c2c0580c8020003141e900c0300040310b0000c2d24080c0d0780b9000b8028000c9010640d0400c2d6500d05510300c840c0c055008180001c1d6a48915014a15640c012a641d1004440c40354024848003001c0c2c2c0010101405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 368010611 1250 368009361 368009377
    0x106080c0903011d012a0819090615060c03080117030403060212060f0108040512030604020d020705010501081603020a030f0201031d1c1e0c02011803080904060e011a 73
    0x1441c00441500080c20b440822210b03140d403560070711222006940c00d118081005085120f10030b0943d8202c9442d00d2002480d524100038455200002615242042140c5204048401e03041100c9001801d0400c0184500140038000026101021880324054101005404d506a40d002041c0e820640d040201d1026000403050a200c288004800541c050000c4e000002d814001c00300517180c050b0400c01654844000c4d40e041c0320040c13040c807000c0f41c000315900390742d182843c018503680e449030008030700244a5076903c08074591001c1611401c205040d000035048400c10400c50b00d00c40c161020340305003150580300c001d62240d401b030f104000007800081e0101c243d5005040000302c007508050841c40314081c921100706a5005080810281c14056109442c90724592900901008222040221900c1502c09060a024925102804580c42044415055801d00380008541036503480c00b044690400c4d852903110324140700c0040b440b41d40d400d94050407940d100441c00e0208800d2864034142e40c0c04404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 368011861 1250 368010611 368010631
    0x9050f040903020c030709090221030a0f0e101806020c0d0312060b1216030203040f02042a020c030f03070507060807050d020a0f11060708013501061a12010608 70
    0x1400c003130542c2c00340300307000007040315080c0402d440c00c040c410000000240d164030340190180d0715130079049050000a481181030030f0308000d43c03024102d2405546c410404440d69a00008121000143c141c3c050f200071001251510b94001250b101d50090784c503800300303211a50704541c102c1c8484011910800c9070440c442c00410300000c82e00d490310300119103584401180743c566400102403010301030100130b4410000140f40350444c21030034140d5420401300a04071001e03118640700c90003200905080e54403801500981030103401000d14030b0001a40312a600303034034640320340107030720a9442c4102c012045420b41a403100c0a00949818240d0580310b50718040c01071b0080100034800c400c1c04120740e10040c10840b425440304081501d481030024080054091142c0c2903420130310910420135040303140e40381034412000d00c1032000203042d208421101c00243c504411007032650b40020320030300c040d406902a03c14030134440304140800640310324288194603451081102d114010850140709114940c2c018142a03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 368013111 1250 368011861 368011873
    0xf0507170a110d170f04060b030115050a060e10210612171e03150604030b040308010e090706030b01050408010c08190b0105030a0f06120c0509010609050f04090302 72
    0x42041990381c0224030a60041000d10303811905140d03081240e502c90700d459260503086121040c8030300151504c09413007468080100004941003007101d801101c29490054020089602c0a0000c1a0400c50380d10886010f000ea000010030854480c01d250300c25481c015154000b00c07014210f04988a4081080d10071302010608840425000f150056000901c3c1c0c1c0c42034034668440c00d04241400c0d410301d00400c200308904009013540b06d03080000c04001a80211025512036a403400c071800d00e2600380703403a641d02c904000f5001c41003000c0c580e00a4092030281c1c1c0d4800d041ea80b5001c1c5205010340c00d451541150380058820060700780b090300b01580e101c40614029081a607601200c2c0d00755102c00084e100894245801c0207018803a007504414110b2103000c00748400920f07a00080c0c030511004d0031103018030b41ca0320110031000360260049001450100c060002445803420300c024581c1c040e00450340724001841c00018090b00c115000d07001c0d40c200a02c40402c2d10400010000140610700045003980100e03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 368014361 1250 368013111 368013143
    0x904020f010e060a0c0506010b0313110109090906020315010c080403110604120302010b030f120d020904090b090303010618030b0f0402011103030a091b08070315090209041101080709060f0507 84
    0x285024200003203039a15a4003444645e80341540c180841604500c01400c824401c01015404898094844d590001c2c0104455942c0030b00488100000350480c082140c100204c10040080750b500541c42080400e040004810310a0011203002552060143c1134010511051000c100c00203907040c02c2e20401028180341c40e9446140c00801c2014500907130160f55102121480c0d42818020780d6640920100034200f9001c0d0241000003d020300c02e500c59800c1e60104d030300001170300d030759024088564201c840f50409107440c8080c3c0750760340d00074052440066007403c00c091044069007052400e880d402500c3ca6420350720201c040050b43d9005200764104511207000f04100ca4013030000b5030190300c0a250108100c941400d144240d0703181000000c0d502100410104180c00011a074507090700d0340030001c0300804000083c2007010309010400607600c800c2c81c00600003009034024168020030001e0301e8031141c40c6d50758403003500c8880c01c9200d03100200d002c8078084004648103078000d14000d4880d50142041801d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 368015611 1250 368014361 368014369
    0x30105090a060905040609020907080408030a11091509100504050a120203011b090f0b0c030405090405100606050406030516020715020312090f0f0f0a120c05100501230904020f010e 79
    0x2c02d42d806d54070299a0382031541076007071030900194000141e0400446078101980e036004117110040829090a98540340122882d2a010031102c240500030220700f00048030100b07400a5a02810000d44202e0b80e99181c00c1d2460701030416103046500c020800c6091903c0c100032480440c1901c581283c2c19565403c0040011442c074903081040041991280160b50400f0341140920040f1781016080c00d600340051070380c49000204641c191001643c2030800c58070b40386409072a0614540120000d14182a404204968000d000d4001c07142142d40c20711080c3c841c40001e00f4030b0a4411131130740040e0401d103801d0003a440c10032104403240c210b5204803842c0282101c1d004641080039115800b0b5034110000104188174204a0508894039100242602c0d480300300400d652000000002401d41c40a02040c0d10300c00d001e4242d5001c0c864205080e01c0601d80000c58080040000740100b05101004032031a1603010640010441c220001805103422038403035400b04007108803a840e440f4104541c0c0703070f011007072a11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 368016861 1250 368015611 368015621
    0x1e0702120c031212150102120f0901020c0109051309080c0709090611030609011811120402040c080903120402040e03040e0708070e0a030221011803110a0305030105090a0609 76
    0x14808050860521040105401c0a0940c11890751607101444180001941e0200545d0005890f50406017500c1e88040140d0504500110f290340c07101d00445c0032025120600b006001c054026400c4d11405a184801551400800d010f420340209801415120500980e40f06071a1240144101402d00552420041c5031203201c3e040f45044a0b1a0000e800c100111809800e448405545959045d851300b9004258040d10500c20060206070804070f42070408060747c0003514103410010b1103580d401c01d01916401d8408181c50403030082c0d2a06410b0a415403203103510600035807100c0095807811562044014800802900c241d074059560b446040f07402c0300800085c0300401e801c039000c02c02403070011000790055500420070b0b81405081c42e14584140c0e6040e00b240c054950403101c488200f14000c2d04495400071030520068558079140540c00700c071520b034060f90f489501c0f1b90b80e070900307070a15046103588800c0c5105004010450920051116280045805134080e0419000285240da20908071781650 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 368018111 1250 368016861 368016889
    0x1f0b0901031e0e0c0f0d12030b0a031a0f0411210a350301030b0405010b0904080405130204080c0103020915070309030c060c1130060f0601141e0702 65
    0x182d891500c500c0d54141445442413040080b03411800d81d05200c8007284030000eaa0034002c3c0340c0144c80c0720914525000740c0c06201307020005801d1a030041d45a240c940e880c0e00c003800000410050800003d0080000380c0349041c49035911003004446840603070107101815402c690311907801c80761440064110b000401040117503030700444e202003e56805805d11021000220000c280110711070401c00c004d116101c080700d04584d071011300c8281d6662107041803401007001e0011294090800000d105c1889028000741040d81e500300c0300b8010982660701804102c0c451885910900d42007060005120743c040da0240180c0d40340604000078800d101c025080403640f00d004110f01059205005100b03100c5240c2090f40074183d6410a58000f1420340c03615141500111107081c0b06000840010026a84011b14100700350030314682e0104182e420322995840704402c03142c0740701c12104403000440715072148030b64515242c0c490707103034600d461481e45401c45081c200580c601c3d0501020026400141c507030074841001e503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 368019361 1250 368018111 368018171
    0x306070e01181e060906020703080418111902100603020a0e040317012706050105071713030b0402031b10030222140f03120d021c231f0b090103 63
    0x3c6414a00090015100d5402c0442154883d41702400001c003a54222000c4d100d241d0481c8800003940b101410107010302c05504035a5290108000c2c0f034114950303c200c03c0c1d40a407502990700e00c0030031070703000811542117200c06540020a09800c1065110741c42d0700c580c22034080e1400c03031003010007041040c01c1c1309820307440503039241804c00d1074200c41c4840c00c2c020b4145c000d000da0288001d51030440000d0550040380000b408900300c01840307000c0000c440003283c24250350800c4c014a00b50f50f80c1030240c10440100d8099009004105060080701e0100245400e403040040107040a0f0b107007503908138004d40001c900800c6020542090503005e245485604c0d00170421810320350040f000c03c4090100384041050454001e0380006520b141c0c000040080d106130b6500a580140c40307421004103407150903184416404802c1c54420511140704800c0c221056080740261451100e0f00c1c2e60007621a0040c0c10011100343d0107014034103000b500400700040c0100b420516022039025030303400700d440005490f800d0030900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 368020611 1250 368019361 368019419
    0x102040e0f06010302041a092d0103110a0504060f111e1b06041a0706020a03020405120a0203060703020a020a020a0806010906080a05030f03040305040911030402040b0306070e0118 79
    0x10140c4400780341d9500150a03e004d60800780750041071415074040034103180c000b0402080e01c802c9502e804000c2d41e200c0700d0018000b000c2c4550183c0980107465415040c2d8006801c00150405103118501260212142a614185414900704003100c20318121119141003041c0702d070b0020b00603002048a03e0b0f2202d071840384603102c51042a540c52400b5240c40c50000070a0048000001640c0c564060700c040350381180e600440a40181d14209440c807403d100201898400300c0d05000c8283c1c0744e405002642c80988080000d01c0100c0300740b40c0d0390064201c000f541a070000d800140818401d40252001240c0380c0100c420150700c0740e0000303800380c0031604501c00b07540c01240100404245801a240102160f801419070502c568590a03100c0c0b00d903145182006078000301080c20107114000b03c40080040080030003032240071140c0904198401c0e00d060340300700d04001070b01145203170104626006815a841d600c00783d480b01c0c4015a42c0740060741c011810016201000032312440402c180c000000c0b80300540c1380c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 368021861 1250 368020611 368020621
    0x906061308070e090a0b0c1b010e0106030519150f0b041409010c09080316051c09091b05070b04060f02130807080a0c030602091f021507030e1e030c0102040e 69
    0x442c0a0004061813074030f500801445002c1002c150450b6000103102d46d20580d00d0182c2c0200c281c0c150101c500e076000d99864030301c20521403181944180c05680c40b45058030070705071540480300302c5410440005030242017041b000000e1412640d00420821200314400301341c02c900b400004d000c45030342d96038415a800070401045904542071082d908100c0d224201884118103003a07040366070307000d80307183c80400c80d46000f680002c1c00700410582c0883c43c000d101c00384009100b800010039400702c505c200303000b25041000110b6030460000200d047c11a15580d1603003401480c0d10340c40d0410b800030740b06072951581c4090110400ca414001012000e0401c41102540c44c5410b054610b00641c40e480024581c0208050303000045888014108594106070056151102413001507801606210600c002040640031846607036000305011004000d84104000c0742d5603403050950550344001888080341d0469195440703544207019000320381180d10b40440781000c40c10055542244e005801c02d28121000d501000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 368023111 1250 368021861 368021879
    0x4080a0c09020309030a0e18011805010603020306100c031718060a05010302100c03090810090302060603060603031c0b091e090a0f02010e06070204110c071211090606130807 76
    0x480148400380701140743d441c1a02450f5240e00511240c1000c00c600c1b104c01e07402980c1e03074240041400c0b54144c1d4007000ca59490398000c800896200d00e40740c0e02400c000000600a000c0c0c400e60b40b1840c800350000610254200c4200d90000802500310309001342d120031034000700c90200480d4070a09490340c0124072070924418652416600801901609042000610041e2109035062201c00020b04082009001500d421b40d1040141c0d0022041d44c0300d55000b179148040f0036080900c0342c50103602501c5007505d6400500d616020200c840f990503a004200e5030310358031880700e8041e245d1400d0800004542c40c022001808481c000d442c0200f00540403520100c0b1411200745103034102000d680141040242660350003618602414040d0600080010b840040d40f07502c412075000b91f03401130080083d41c07036094a044143d0031844c070781d2980b40302c1c8900100c1c03003d855841074060940c1204041084490358810469040710050071030b90804401d01807406004101406800645204005006901d00f407901076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 368024361 1250 368023111 368023133
    0x60f080105060d08070203100e061914280f060503060f1012230a0b060a0b0f1303020a14011719110f0705150702060906070e130204080a 60
    0x401003a490301061110079900d0065001c03c035a8030041040d1124500c1c00003d05000c1c0c00c00c001503005080400c03849045401040203486840300c0000c184012008407828001c4500144643d4448040840424049203055807860360a4032007000000054490000750410784110585540244e0b031550302c140040c1c941802215401503003954114004d2400d50280d08540700a48500380380c44400503000c4003030003038000090b0000f0210a9a2180d2030021007003103682c82145420595610300c0c8400422030030320b040d05016007200e41c41e80307071181000c01a040101303440e4001c0f08030b4049032540540020050325418510002001c0c0d40c0012081001224005071902c00104141c0440d00e8016080206160300c40c40d00c00c01460880746c0001e0104082c1118000301c8c41014800445003c02207981d030200301000441241c8590a804031420a481d0f40c039080c0c5e5548410b0350b00c452590485000140010300c00c84408083d100000d010080887c94030414500f02e80c0a1b40006030640c00c01d0300440180840b070109 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 368025611 1250 368024361 368024369
    0x301090606050f0f0a0e0a060804110f010e060c0c1908070f030218270703020406080d0206220f030824100e06040e0703050403110a0b040b061f03060f 66
    0x24034110050008401903c0f5480c54103068400114441c00158401c21b41250584000b514032500030743c4910303000c2c040c0c8030300315030840e00312100506460305824200e0840982443c103865061030301d10081d00708981c60300719203030030030f224802d4020455459843c4811001c00081c1da21059502d503007014206400e0041903040f141481c441c803242040181c4030f07265000084101c0d00e42c1c6c201c59848408002c141b403030700a20324580605108000843c0c0e4540418001e040f0b80c401c03141000b010759142c428030740b1040d0f80f916400160b0004d4000888403103d48a42c11004984600000d40281c056a03854114001012040e4002912001004688008024000e00990314103007142000c6000e0000200180d8a030f141800c1000049001e000840e2030b500c040da009000047c0c1050183c0c0342c00740000380202400c440c141c001030040f540200c085e0001085040006801170904800c5586640f00c034080c000014003aa034001c192405030544c0858500c801041041c2c0d107640208002e0320341b8044c14084240c07604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 368026861 1250 368025611 368025617
    0x12020c0102040b21041203020d02090a0906150206040206070215190c030914100311071e03020105012117120703150f1d09030f0c070936050c150301090606 68
    0x303100104003104051b0500c0e0000345000760b554a28003005201030f000b01c07080a9003121140c98041a01c40481c3c100c4010f4403a08510050b10000d11142240d135900d05490103500004208203000160402c0703003d080d40c0c00c1104c0ea0711490403401d8540701d112483c42000380000904551046d00426078403088400051401c07122085030f04284000003005600404c1c00002403641d203006c01136041c5400d000344c948580d00b110520150703107652120011440c0600200720015480d1200101d00400d00903000484a0b001000c0d40030302c480c0503036a00504c0a45006c0500d810007082c4401c1c1e81c4140304c5424240b00395113139600411800a403c20901c04603015400c80958a45a44c0b02401800d00710310418200141c41281034206482e24940281141300f451035032421540c6c0003440c142114000076000013181d034044403c021034a42000001c0c50752079a0400d81550f240b501d002c3e80b4030a505401d1100c00c4502038000d5510b001040c0e40052499905d036001c000300c03400c01100421500403144107000081080d41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 368028111 1250 368026861 368026927
    0x6050c0a0203030703050601090f030302010e15010b0f0c0705040914060a0b010f031a030a08030907060306060915201b0a05031510030b07030e0d0f090612020c0102040b 74
    0x11006912404002c284d0700030141d0f100000307440e9a1003004000020108445101a41d5450341002400b821801c414081d42d4420b142c0c85072500300c0990f11040c121000400554141506103032280c1d02c0d82d00a96034a141c038494618040383d0343d91a4843c2c44d2000c1c2c49110182c0c1c40c040b44422356414000c2c000c0048480e2803a12091030401d1340c0221040751310340003e14000070481c410100030440d003840109070340e40510402154008120035000110f00400100e030032940c440d95600c20850980f000ca02400e00000c210400400c0b0b5030303c503807034480701d05501818050381c0c5480c4903d51145410740d0000c05485540004000b20a09220032041401994241c4419118500340400701c0c3e40d444040728604480d480f88000a2140c2d510640540b0145511441400310380c2840303078005001c0e204c50402c002150140c00992603849008842c0c8d414500742c01e4952425203490030078150f49000d10104541e184580030464071024200c01e10041024148404003681c4403150b4002501110300003005d01c05001d03a00e6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 368029361 1250 368028111 368028127
    0x40e060606190909020a05030105181312200c011b020f09040f0c0e0f010506070b22050a0606170f0601031101271a1602060d15060c06050c 61
    0x4642103840254201d40c14034080540700b80300302d41030740346070f80038a18540c40464445001580880194100e40c0221400d0202e04045400e00303200240655021441c1100007844400244941e1807940890041742801050516000f11101c5800b036026035621700380e00b0a4150300c100d503800034102d20750994043c00f1000100403d90106001009568805100e420301c40002070412486c1d262803201d43d6400400c03116081e5444c0902016504243c2e05102c1d050002c10000c112400c2940c20384d0741480c3c0042da41600c9880e200400f0310841c0b0b8260180303c6000c0081021400307e28200003890b4114030500c0000f985928018200d140050401c0710b81d81107400c0110403c115040c0061661305594101280001c1e140708000140c03807c00c1c0d0307050032110410f1000014540052a086e00608803010344520500c1c00403412512a401c2c494040d007101009201d0945e0805410040302038002e4801c4d900300010402e40f001c1e4000e01d4142650302c010005040c1030903c00c10806240116500b20b200240303114200400c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 368030611 1250 368029361 368029369
    0x201020f04050603040503130f090f05040503090405060622090c0f0203030c2101170d050a09030b060a0306051008011406060d0203060f100201151406040b07140d0e040e0606 76
    0x8902c1900d2280b00c010000c102172000900450704881d900e105201c1f4129a5001c1040d078280c054499030b1615498108010780e02101c034040c05120b01c1e030120141d0f00e0311340402c00300030041034003410164200200380150401d07200310114002a00c601031000503c0d00d0701e0140c0f054160307003200700602d0401404a804081e10b58000058075040b4810281e49a01c0b801d0a6648280da4101c03084447d18891680e0000540300c50101d001d1048070b5107081c15130300c0c0c541d036214081e201442284008400150a1401000403413900302e04590001d1000f800c40c00c07600c3d034940b18201525025910341000342e00c0c01408000700b1f1024414960b08080c810348045c0107107041c0c0c2c0020b01d1030003840203203500990000300145032540d81054040c0c1031407000b80310000c4410040380003402000038400d100340400c040040810f40e24281d00341104080b40c004e01c1a807515042441c0c1d00500d8000030811644e20a0080004582c034000340451100460656903511100001e10204006c1d64042294104660030102c01c0c060b042d00c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 368031861 1250 368030611 368030617
    0x42733050d031b08070804140a030210030e0a0c0e07090e0708010e0703090606032f030a170d050103050d080f061f0e060f0316050f1c2403120201020f 66
    0x81c15007003c3c4150f4140c03100700b00041107040c000a141000000318001040381c0c800c060015101c8020703111212902080034024921203d01020394050203c1034041c080500c00c3d000000c450003200262404145503941d002d2501426411070540a4107860400152951116004004000c01c84820510303080c0040c01414011040c060580c1c2d585d55400040c080f42d010b50005140d59501c03210803c40c071607990400d4070f010488660141c0121481010746040b1502c03000850686040003000340c00d440c5443d640709014928080294941105d05204d40c10720660035200d014020b42c060720262404003800603000305646801088046450680014411107484a03094010301c581003c14507078916090201c1584c2580d502e440165005000165040030410140042c2d07000d005074a08410442207000d50a9490780039503280301ca10b028090101d465200b424101c1000e5070751510354001000f00203109a00d800000c3e10203680030040c0c0c405e40810812203c00d0103070a50001c1c0344021400c05a07601d815000c0b0f0b03c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 368033111 1250 368031861 368031863
    0x122303040f020d08132903060904060912080a0c1e0f030e030d020c0f0601051c08070c060203030f0108010b01050409110d1508010b0303030705042733050d 68
    0x540c800000215100d042201c001d491300a03c5240c3c48203105000148503048034019443c82c02d62089071402174400e8400314a243c80f103403088442c19a541d9200f0700461030f00042064401c1070311a83c042000c01c80b0f01084030182400c40e92040141d19014102c0f80940380b40040384410054000550007941c0c50590b201c080080d907500d01801d0100c1940403c038040d0159a1008210f07000004070030f010364102c0d500809840c200c11301506c42a4000716403841d100ca000748501500f00c100c031049103403459950108004510301c135500302e81c00c1c0722140c0c0304d85c200000140c10003c096400081032042401c0c00886450040100b84001e1000400030300000307156004510400b0a91a120260080154118803d4410841e00e02000f04010180c8240b0928214a144030707075a119464041c0500c05810040100c2c1c0c03064055403100340c80e051038848810b000c2d0380245440b0b90500898131902c902c81c1454003d041030f000107040407505001c18420502d09106140c6400012444420001c000707035101c1100d6903001d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 368034361 1250 368033111 368033123
    0x8061e0c070609020f19080705042703030e0601032003011a13061205150c030108060c0702010320040807050307030f021924030f0e0c04050a061212230304 68
    0x141c4501c0030551071038410b000c0c0d951000c49105010001300030318006d2001c465441c02250300c81030f40c030f406100840359800c0e54400301d059140300141a14104000344803c2503ca40b40004074201e010061a040078400e8001f01c81000d006851a42c40100352521081400022002000b034242c085628141c02604042500d0050603010004181c001036a4001001400d079000c100402c50701b0391400c5c070b494003015011f154403103241c00f011428040a60040e070707041e501c0d580b000b0030b1540c88928142102c0e8200c100d0403030405407a030400c0700100149440c60704802c4c82c4807401d0340d2a1401c15000d1804c0c1200c070b0308210300960040d20208042100e41100c1022660151400c3c0310340001c4200d650f10703180403a040001c6240b66040e800f1019251000c0c4a403154040d65004c00c51075860000c100b0079500752020306a500e0b800180f0740785840c50164051900b0042d54200040c14660315911900c00a00005095a008070502d8501e118180c0040780000008101184c005000791015802511800050006445c3e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 368035611 1250 368034361 368034371
    0x1150608060a0515030a1b09050f22060305100e120d090b090f0601090903020a061a030f03090405070804030804060207050304120b100e01120b190608061e0c0706 71
    0x1034642c00304032406004060b0081e1032503111001040d4a55009540b024a964039081203002900c80300e15034454541c42a03914103813524980002c114020140e1000103038088814620300051000c0c541d0705040280350000007240b0b40f451420054203041d00c41d089100310a09003c0b1a8105078004203110b0810106c0808094444030030203107840051180010040c1076016150a011076100001407170140302500c1c1040340c0d00c03aa2100d80c00406da0b020808003c02591149030084006001030300580e48140c01141510b8014150b00c0000f03241c403c0d0200c00ca5800c0d00b00103a90035082c202030113595845000c90902034050f060542d402000c3c26001003001c1d1005a0114103541000014002c0300d00418007040700d038002418504000c184040140e8800300f0764060000000382242d0725012040c12207140c6036a4080041c0641c0722101550070003030258042900400300600c1030303a01031080c1c401030000d200003400c580c50601d90344540b82441001032210042018104541d01003d40c0c100c50f162540800c010070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 368036861 1250 368035611 368035621
    0x5120a020402070503040e010b160b07020a29090d08040f050a05011d0f01110d0f0b10030903110613020103020708120a0f1a0604030b04030c1b060e0301150608 70
    0x104010004900a5100b80000341c6802800000400340c01074a0494100c04510b980e10390804640d071042103202055901850300b0600400c0241e01d0159108c44a4015284120010341c0d660100148941e2680068085c1da01600020b0898040d40369000403c078004040e0040303941405014540010300051480200001c90000c00c2401c1c05440011350f03102e40203000c0c0503028140d20300103584a51002e545071240c2072182050000c14015050112510301c0000e140a29100108000c0e0000b108580103ca884561240c0241c94410034402c1c8003c480e40c00044111702480c00400301c00c00303103e5440c4113601000034058024a222840c10160380d0909005075124414134103280709000700c0c00c00d0000003040004121125003560004042045d88030740c2042003500e8000411484109943c4c1d680e0000c00504c424000108500c510b96041402410328103c0c585140d580e12600c00c01d069185111803c0e075620030068160009400026201c084009200d0440b48020b44820071859202d070400304141c01d030101e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 368038111 1250 368036861 368036863
    0xf3f03020a05030a021c02030307091404060308120603150c030606030703180c080d1b0b090c190312110307120306171b0906031b01021c020a030801050303040f0512 72
    0x100155031150550b526a81020800394842e640c0a80c0113006d07903c403851520340b40d803010040340c1c410036554698524150030700d940c49001401c040b07152034100d03aa4a6012011890300e80240c4003c250030b40450249140c400281401c020214a404800b85004030a1080058034001278903413000003502c10640303a5907890302c00c4001c0d041041c481500c0d03041001030380040c40410040c000685604c00c1c11a142100111b030120380d00c0c0d9600c5000800903040e540100c00207103d81c40c0391500001d00d030048500280d0000005550803014401300780420000075002c000f001401c040c0000f505295040c440c80300c91403e45055100d105090000f00312107003a40c0340480c0c045c06640000c000d00050155520b0920100310780380e58400201a1011040005400b042001d251618600348294405000752080207040401c0b5860341e00100031441c1540030306620496040b4141c1715040c14800c46500806101e0480d041c050322545060b000507002c1e800c20402800120400c0c03040c18100c2e8410750701000ba64031503000c04e0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 368039361 1250 368038111 368038123
    0x12020307050a06050910091802070507030204330303080f0a1d01020703110c01050a1209150204050f1e0d020d120305100f0302010c03050a0314010f3f0302 68
    0x25581c0011154404506294000017030031800d10142c40c20103080d003c0b28420b4650805511078800e0820048190411301da840350082e1820500c51422a41d80c41d440b6030016041e02c18400001000d60348520380e041d000a8000d05180702c0d441019800b004050840d10018501603004180341c0029401c0e101160303006c07200380c0c4015680300341340d0b81a901e10801c280c0030b107000c1d610000d4242c0c0081e148a1081064240204030200e070039034143c551928090f10b103481942e2442c00c00ca401140943e60300c0342d140101d0b5510154061181e5460801641e0b5420001000034581d6044140c9d0300413000344060322004a4420b8160003005001c071102e8148003594800100902c2101400401d0a030502428401054250700158090300c1c403a600794a580d500d0380700720132403200d40e0302c0064009a0307044a078a01003801b8000402c04041e840c0ba010901c500d4a0003402e001120a9001e161070007240c100401c4102201103c618150740c141d214950040a040e95003501599515210b1006040d50004c2d00c1c1018000c001d6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 368040611 1250 368039361 368039369
    0x1020c1c02150a0e04140403030c17150405010e07120b22090302071203140f090612040204150305030f09030313080607020d1e03090302030904060e100509010f12020307 74
    0xc42d100c00b501e50200c00c10781d030001c183c410301103031800c000004c49140500070301880c048140c8014405585984086012308058a6540e040c00030f001041403400060b01c1c07051b449100c104c5089060401d039603080c00b040307030340507400491500685070502240b507900c20700124407998400c0c00860b80300c440c5800550b00340400c00c2c2e00c550048451403002003240301500140b5409000e0780070b42d0382d611350741d51403000036088001005000903052200c44841000c0c4c0f0700070303040c40624100c485090980c01c00c04145240c0c810640e201032041d800d01040304515103030007400c42d6460000d480c00c0050386559142ca680c0e00851010182a0f000420440c64944003042601e0070740030700d03984043e00706544100944e141c1381d00342c030f0038001130007400c080540766406030248556048071000701d11140a44505c086006000c0550214118001080780104603559402814040c0011402d504400e0400300e014007490300e8140d000c1d40c0a849900010801e290010a00394115031086480c00824540d910000b8102000c03504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 368041861 1250 368040611 368040619
    0xa0e0108030d0b031f0f1d0322030803041a0108030901170a0b04060b0703030c14090d0317100519051c060f02040e06040b010305010509060d020a0305070b030702190201020c1c02 78
    0x4240e0503100d4041d040340c452a0440c006c100813610102c04000e18144117500040c4041c2d10402ca07040c0c8a124040d25800c1c074910902809003032584943e00d40c03445070f200b038500f9034103580c0482c84002586030141c80c4c40d0040c40701d000158544041d10b000030340196000c08044a0190440c00058181c1209421059801c0d000600800003d5281c0c100a5019002010250000703031030640f80522583c0a040350f1344003812942c000034140704c0b4100800119130f0404400720104030090944162100b0b0a00c605800f6852000108003d0790528060100150820719200c42d0181995030400c056168489064a81d03014070f031a107030082a00342042d001600d480c3c0c1d84d4454040c130015000130440c550072403907070249501b1141881151500700044064640038002d1540c0660890302041c0380340b40800201c55030341c2c4040c0200ca0750aa07691a014244031407a8090071500b18000104100140d0611803100b4100b102410041c5204140d00002d544181072248035005100a0030a10510854040303020500342d4018 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 368043111 1250 368041861 368041903
    0x20c0f03120907060503180f0a03051e1317190c05040f14010902160b130b01050a0b03072d020c0906041109130902100804020a0e0108030d0b03 63
    0x801255a0391003407092030801c000150218500c51008643c079000c41ea0302c1d40d1030307600f161515220b80c8803668078414101c03d140301312a480018600c046c850708503024042d803922920b60000342103d80709032102e05210b03603251808005040c81150181119000c3e61080c00f0002c0d006805140c0c06480c0010a0100d00c80c090000007451041264207507001e4142c48095400344024000e8000745000c0c4e0781c00d41902c40e007a03c00300005028030706081e400b810f41107805005d10b1a01c0d2401342c488140503041902c60801c414107184003907050110701711500340100b4055500c00c0c0c0700c0b481e00800d04c0d618007020f0042000c0199455681e110580b01e124001c07145100c580a011102003004d202070355480c107140e92503000c1c010303101c0055001d103804c0c0320b0655159030142c5151b1600e4440410011102400140904c80640d2500105c3c01350700c4013003504c032003500c4d941ca0701141c5061a00412403a0b0149034400107940290f9401800f9844021099454214a01ba00400c500e03e0910000e414102441d400a03c1b0003030340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 368044361 1250 368043111 368043133
    0x30507080105070e06070203100902030102090d06020c06060d051504230f011d0d0e0406080a0c06020105060607020a05090a1b0c0c05030102040b07150b03010212090c0d1113020c 78
    0x10b41c40103000d000140c5860b041079440400703200075802581e40c00707076141d00f05680d03800240440d5049031442c81c0c03000f070005103002c45400016502000c2807d09445195001c42c8000c2207007010045030b500100d044070710356208002030307441d16a41e240f0003014082c16032062011504111340080703030044031300804200a06d41501207003007541e240702c002e584803420b40c00d15940041c1410b00309840d02c031000041d0003a01c0c49818203207003511040c809940007604281d03200341c000303181c200610144480798407405501028501c1c0820003030940d44003521503482014100225801031796040c03011002c0b200e00f0381310041306541c0c0b868210010006000c03243c4503a81c0404032002803c0d8005400111907106040c4e40440d01d84590a2500701d003e1402403100c0302d041000541c1c0482c69504c08081089000380c0f011a10807810b502290a86e00b00f9040600d40c400c060060010300e11051004601d180010360b01d04900b401035448000102407034000c541d028041140032204058481e40465406160312000c5440d020b0321 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 368045611 1250 368044361 368044363
    0x102105010603080a11011404030207061805030708010606090f0e0f04031e031e060b03010905130501140a06080a0c0b1b01090c08070e0f040206130e0a06090605040c0c0807030903050708 81
    0x5d0905200c07020f500e8840303c0842c035020984890300031074050b80246941800e0040a0388c403020350041c2400c02c0101204002030795501081a10040c0491100100346145021f5010b0705655040c0c100034a030144203001800941a01b010702540704102c107505038016165802c4c01c3d1000c504465104040714440b440c40301c00960140c2000c403e15014080d440f40c80c0f551905194221403079401521640c40e41000108400d4143d45c022541050303152160300c0c00c11090f56116400c441e051404020a001d0f600100800d891032807040e03100030000d11001c0e10f0380e05440d94641903c5126070213084841207010401e19401080c2c80e101c0013082807908000c2054401d07a080c001c202c49014419120705124861000c65113103982e0f511903010346080f101010090322140d080004a801a00c040d800c500c60801c0009942da00810140b8080d0440c000c0001d507013428800a0816030700301e83c1010b80124100384500380480c0e441881c3e50030321500700224680702c006502d4100c41a0550b6030001d4040d11400e1804038811790 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 368046861 1250 368045611 368045627
    0x220204140906070e030a05150717012d0312081b04060903020f0102011418150c071a0c09011d2206080a0201050d0e0f07090b09102105010603080a 64
    0x4295101d56400070480c4e41010303941d20342ca01c80107110b42c0100940c030450390918050580c1190441c240040010082c0e041c650204509030301000600c81036154501d4456610f00000c007098100340301c5040807070b017140c0750070f9400310780c00c0c0c100c008204c41200003030703900c03001c1a107544085841001c0b119561a540c0c03030002e082c00d55a000c01c0e40700b00d4900050000540c014440e01270598400d0b030001e00590744140b81e9800c1c81e105401000b8050041070f05600e14250610400c030311038001425507a84801190510015152000a15aa41c28429002c5c480c03d042c807803043c0d9a9000b006d1030252412001003504446018003100b17210380100c1c02580301c0300e200302040001c1e5104141c60307004011141c1d03034207511640c1e83c03a89070f0060b020400400612600c072005400040420051104465016901d00f5845290144d0f9600844055555803d000a00c0c5000e02095810800b0050001c0506080441c0030308800e00c00400c03400c408201ca40c107d41004401e421420065400c1301a1580755112103001030300c0c0207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 368048111 1250 368046861 368046871
    0x7030e01111f06170a080703050f040905180624040f02070f0312020f040608070201020c0a030509031b0a2912010e090102070f02040509071a0c070e220204140906 71
    0x1410b041000c00c404c1c000c103651241c00c0180400030041d0050070b0702c601d001d80d07200324030560030007a0402c8100e181416220041c030041120342800034079450036500d408107091910030f001c1e240e60003040c284805a444044410000205002d001d00010788010000e802486200c15611030b142c0003080c54403e0080d00c582a4810314026214944418540881c2c3c2c4120310504030781c1c81070020706200c103002d8903201daa5415440b440600006140100b6070b841c641c50608201e10031000200d001544020b981001c0c00004c154101001c0714441034641003002941e203207943d00a0000c0700d03030480c0140042e0740000842004e61100924500e0740c80941c512865182682401040ca0108071403003c03d00e031030014800c0701e102580111041a507500c0030b600f0013003d4940078101d03c00e244182034003c40c20107007116070500708201c40b001069036000c407003640d03500342032280d44800f8a21031079a08020b07a80b1202c9002c0c0d0400506904468a451082d01c0098000c01d09805507801410382d50b0200301403441d001038105c1c015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 368049361 1250 368048111 368048173
    0x2405040c05010915090303030203130b0901270209010b0d02120906010f0b160f14150a0c0f090e0c040905130201110106050a0b18030a0b0121020607030e0111 69
    0x20f56240c2580d40034444240c070450001802c03155040012a11139800703180c00040e0403440d516004655211541001400d81d807018640e551071440c484d01da20404596421a501101d60300c4920b000350b0001681101c0510880c4008000028505101c1a09a046a40c03d03031101c0e080b25000c5c00d02c0180c180e6250801d010f25800c00080302d801040c4040360005403482c02c1070b017540e00702011119075960b01c030b24140342008644ac04403141c0300c4039400d4014040c2142c3c04500d00b92018940c9002c000c3c004c180c641c1c50040f0010b01042500142049620419074000e032900031907000d03180d407582444181d046c45294410244103180200f0707c08cd074045500381280300f9000b40d0b034080c0d01c0c0a80521003402c85d02d103407207420360040000c20204969442e17030020340740040d20000130b4107086c180500428140300760300d0710841344000030b000103000c0c02e0341c0ca100d00103461080c10403e4a001d03c1550100d251446502c4004c0d00303100140c0700c0d402c03580e0b01c81d0b21900c480d686501c090b583c5020f000040ca90101007481044a00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 368050611 1250 368049361 368049377
    0x227010e12030a0302160b1f050406180c0e030d05091e090412170c09031c08130201050f0a0e120d0c060b0d050a06051e0615030c0403080309030d11070b042405040c0501 74
    0x4270341340ca4041d80045e070783c1042044004411708250035004100880702101404009014140030b90b806200b02c1c001c00c000c07619081d9443d2a01c0301003001192181000c0b03400e180c0324110080c4203441e259003669015a00140510f620110810181e5a01c400c18403085946080c4000300141e08400380b0250504501c05d800f1a1804400304150404900300c011280e80040c05000010701040868100d1040050041c1042c0d403820307482c0c0c0c0b19040c899000503a0440480c01c50001d0354403508194030280500300044000d03100c000780c0214010404800710002070709081c0c03510040c00203560b030003030b594010320780c403038100c8001446921340400a40b004481021128060490303007105540948010351042e10024a800103109080d940350302c2d0381e00701402030007050109000100008800c14011030007010079078010754a030900d030a20b103000e4401e072504680350707180c0502c412030015080f03102d400d4200740e0041c44184003101256084100d001d525003608107190402041c0820312000030a07071016100281c0e583c401c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 368051861 1250 368050611 368050619
    0x60f0201050f0415020c010e030301061412011e090c020a1b0302010903020909031209030403020a090908030f04050c03010f090203010e030901120f0227010e12030a0302160b1f 77
    0x20807a40102c80340103460590000160000300d40000840340189044001030618104008050840300150100815640008010320805e90414945a640341c468000c843c0380c00e089861094803d4010f209a10780125910784056800202000400151040302820000020510b800940d19585080d05644110000175031804100c50041e0321300560b0b8060b1211071070b40707103140e00f070003680c42006002c41c070140411b1104000c40900c440c4007600030300d001070007141c44034103600400041c0038859104030740880c40e0081c0d500001c0da00f541901c1d4040c10b07690745060280e03100c1c18182c0c01c00c1400f0000c958107501e426401c81d00400303194891b00080e40294000c00c4800860720020387d0b43c0c46a08030050101d0360162002241841360f4225240d0300396421809410011100d14170f04034840e50f4035060342d0384902590b110202c0d5a1191589030410011030302d4a020b00f6100c00050380780c0c4950b040020425400003203d25010181c040c000072010360001034003245150a41210143c1d002a08641e612910044030001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 368053111 1250 368051861 368051863
    0x210150b160308062725020303160e0a090c091503021809040506061309080706051f032001020c09040b06182511010509010c1b0b010909080c0304080304060f02 70
    0x1200c9446481d02c04000a0075500325810001c8010144c00c0815181218000c240c1d4201c1c03201071b03190915400840c1c0302e0405250710140c00c1e2103020410308004021005810990382c0b403e48170129499040000b4041803100c9048400030601d40150124003440b400006130680d0550040480c5c1c00d827180c0c5144140d2004040150b21001520b02401540c016000314155250a0074200d000302c03103c41d000900344c2807541c5d8840c89070b00008402e6401c1c40d60760f1700300720704441d0340c40d07903440f000000e8880020002d00b540e5462403001404001c040d003201040d411402d182e402040801064040140b80d00715914041c034003071042c0304d011a405030162055a992443d118a802e100300c2c003903180240032400c108400c14891810100f041c510703000b00048846c500f84550300030703c41d040c0542c83340e100203c1c01c5d8200032400351880708402d45006c0c2c0783e40810b41c03440114206031030f2141580c4907404082080384050500110f140200a4461001c2c0000100042c200900200a00c1212034644800c0007412500303a040e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 368054361 1250 368053111 368053129
    0x180b010816050310090c031506020a05120c030f1303061103010f0e060d020d030f030b0a030206040e150a0807030302060112081803190606050f100210150b16030806 72
    0x1c050014500720300084480c0902d0145030b1140c0e80040c140c64481d51800120705881c03000c0002c0004c26910340400011078080c03280324010300b56600007030210701119600d05941d003419403024981c038040411141d540c04030520071910b0140a604e00261502441c107401e40d02e01030703148001c07074919140510000a0001c500c03303032070407502c1d030340700300d498076031604c141c0d41c0304040f00928860384100302c3c010010040e90b030742c00d800c150540203503a510088400d000f0f0140403240e5507541c0301e204140f509800c00040e40c400080790f058443c0650500070a4543c02c1400f0b10716075040c0c03010743d0301030b601000110718461300285440849009500310751440c0d036a05501c0c100082c487c0300c040c02246042001d2012011030746585090004064100d400706018601d206041010708442215503c0d1180030070022840e24811001d0220012520302010315002e0101a5852541c0c62641a00c41d07143c07a0102102000381c00054018003904182d542c2d5960940380c0d41c014240011401c40100700a031001c00d4540c04c1c0380300c071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 368055611 1250 368054361 368054371
    0x804051201140a090312140402100201021602010c0606030503030c1905040f210209011d0906060117180105070f0810080606130222060206070216030b130b01180b0108 73
    0x9402541c0c4034240800f0160554007019070a02c0004035614900c004540702d010304003640c0307000314605400d15104010020380da115529045a005000da05200300380d1041004080750309091400c0c0e040594580f21018001740e500103003082c00040200000c03496100c0003451500000c1c1000c00d400c10888100340d0341c40c001c038007a40c0e0101901c1d5900780501c4519060124401d01d01c850044251030316540081c58800098100e2000c800c82c80a1078201703007411420081e08400300d04050100e52602c100000d20905011694050360400540851034030740c0c1c03865100d003000202500a00c0f5030b20701104050100800c0c10b181d00300051200000803102d41d5010b900340b007a185000060240d41d204c040802c0309003914440d18126690b400c101d00d800c0e04c10581411110b400c400076403540494074001003c4d04001d40105100299000100030416030349001e80034800703495110107500120b07292190580e803900c040c07100050903800510008a55000d1031100e907402029513081c00e0002c0c02500c2c004580d8040d0a4903 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 368056861 1250 368055611 368055641
    0x30f11011806020f1e04060e0109121118040305030103021c05071e0503070305010501210c03030c031b0b16170c0d0b0901090b09011202031b0f0d0804051201 69
    0x220301c00060040d4004100382c1303905003022401c1980c40e001080c488044600d00c07034001070000504104164200010185010003424004082e510b842000414003169500041c04050014100841942c482041e4208036240d1003c4d80032500e400e1070043d0481e802030000303074031502086203041d808500580c070303418269030f101e8003900c0035614061001080c001d84110885c442c0b80c000f00041060f032001c102190081d40031344008078003075141c40c0a600c044180004800c510351248044e00c000324102d031a004048903810318040700c0d0702106007000c64240c821540070001e21003e500603403003413004911400d8007800f251014010030b4144e02c04185d8403020190035001c2d400c000580064103110b601006072480c00e42d10180030030340161803000201d1a00c0b00340c2001c032069955513001860f50421444190141c0211500c4111044007030700040e0b0340700c02900c04004003603c17840d041c3c02640c40380d642c8030008201c00340c07070025691890b1410b803c85420500410380190364091152030401014041c031554900c07409 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 368058111 1250 368056861 368056901
    0xa0f0c09110a2c10090f05040c021203060609060d0507030e0102160201080402030c0a080303010f0f12060203071205090109051002031005060304032d1205010602060a09050a0f030f1101 81
    0x164600080d145012201c0e4410f041e829044003243c8900d42007413400460307580c0c0e400c10542040c0c1c1c0810340c40140c1e0080741c0520314005911082d2500002d151050f0b8000e0402c1030348903564403002511901c80c080d1110381004011800c0c11214413240c220f035000b004552428850703401c2100b070407402c078061032110000c000c0b156002200554095080b07242c1041c0050199051102042c01180c008091540a0041a4400401013110242d90080e440282162201101403249029200c2030b0296081002030f01a95002021450803030068140c900384801410060060f071806a0542e40241081c12041e00e96026002d03115583c0401c92007101e124404900c030315440030b8144003c0c4511030300b00400807010b010005010421f220107098241011407082d032580201d0a02c00c280c02010111002c500b4040b5030b003814014011544c001c116564040081000000d6102c0c041c00c1040c0b40060003070014202d0401401c000d000d142d445111300e545d9a0b00f68460315028425580c641d404c889600000000240c140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 368059361 1250 368058111 368058137
    0x1506040f0b04050708070906091805090a231203040b04061e0905011b02010c20010b090f0411271003020306090d0f0e1309050a0f0c09110a 61
    0x5603010000c9200c01400000c0c02a426202180442d6003e40790360b0080b034005410012034a9009040c5000780c0354500e001030000d03291842100407200c1d00f14070030480a8403100020203182e020801c00418540101100e01c5010b611f030110499299540980d038040e015400b0001459004001101c3c01540d1008504450b41d03229202e510041910042141d07010840107030382038807450740b0b018404c41c090050303000151070f00c488000449035040360612202564140f00381c1d60103154005801400c0700200b000302d0f4415581c00d00f10b20780144811074030998000820818094034828001503280300784d214400801d01c0d034070703d0fa0410003400c103605040a04100101c0003082800101903100d60030582040c001c1d01040c4e00c95000905120085605416961004c64104e000c00d5104605040e1003040741042c0301380814400c0402c07110384500d0f51001b01291180d40030400c0007020843c2c0b40b8819040310b4401c004640c1403918150f001c0d003600c20542903074200350740c08001c2803140c812a8a40e9a85464407003400c508 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 368060611 1250 368059361 368059369
    0x31e160813090605060418090c03020d060e06130510050408040f03080408010b1807050f1c02071505060a05060306180907030507060e0901090f0f021b1c0e01052d09040506031506 78
    0x8e2444100d030350200540c4000f0040e00d078042c003a580b10b40704880106000d450220024600b080051006081d0b8810403600c2e80811408501101003052480b808611961282030008aa218075401000c101c203001c00008107101440002d0070541760304500038001703144048100081c1c418003803503410f2165510740100d00d425002d0030041c5242d641500103181440041e141407403106030701800340e50710030b0303000a00c500810041d000b0040b1a00d40340041088641040300200e510510a8000c03d40601800008141c25550300f1800202d03030f103281848011649800f22100703881d000399100444191244002c0443c10314000c04842e80ca9000142900d20356a18040c290005085402d100180b240d6440503001001c803264001409130410381c0c107283c0915400b80f0301c55441c00c0d4100e4010442d0b2203c50919050450703100342c0c5141200402d01c1c1c074a4845050040f1241d4004d412540c924040c100c0b14401d11011420b640a000480e0080b6010815030350791f03000f4540ca5481090088803070540030000a101f82c60 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 368061861 1250 368060611 368060621
    0x629030106082b0c081902013b030c0d091703071716050a0308060a080304050a030b18060f01050a0e3718020f03031e160813090605060418 61
    0x514002d800304d609500c510065600c030f0003000c28503483d507888a984103034090080c000000d80401840ba091501c181c140e001100041c900e40c0080c0e02c2e203c998081592003002503e1070000110241c400c4894045401341ca50116842240c000400c2d509031580814400b10a0320303810f50f040300c5484502120107060040d035a002107032440000c4640203103000030500401c040a500380c880d8403032850908141017089030044941d0b1100716164000c201c140800c2e20364280da4803c0301e034404282405920780010804440325403c6c6e120740720384109010030003032051200b42c050403540c080d01d05582407600d840248414400854690820500d5826440c0070940002100c11081c809a8451000740e007844c101a015950b0400c10355400d0030310620082c1c1585400c240200001000b24001d40c54032601102d481e250043c40c4000c03501c40a80880c074122502c104626080348a070707004402640e00d01038a11141082c040c10b0140380150b62030308001180c0750801004407000c1d180804100100f40c080040041c0c0501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 368063111 1250 368061861 368061943
    0x50d0c02120607020f060a090c1406091815010c0209070807090803040b0414090603120f072901090c140708092101110313020d062903010608 62
    0x3241c0c0d000c803802881801d214280c020310596002d09210b1303207111301083c0703884005800218864601080c010000e80d024031400f0441c0c080d0817985101140100c0003861a0041d0a030b09078204091030031900d90500b521000380e00c10100e4190301c009049800d030045444010030711000390030141700340100b42420b019400045d4081d5592802156840d114032606003186c102d0382c4083c119000210f42030011884003030749840d183d101519180702c0c1d46000d000181d600d881800815041410004001c28800508030803129016001900d0991612a905420301e205040c400c00300740404d8204000300e83c030903150051103240b02d0980c0d40c290740d02e01c4c00b60030b0303200d154414841101e000404101004594540c5007800031000c04140070000000d00c0c0740d51050a48140c1c40110b640d200007041081100107246000030034040e0159828040140c8074542074009019680c00100c0c0340c558455030161080c8100d4005042c09400c3c0d00910039240d441482a694000c10611403519002d00a104066543e16405d40c0c5600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 368064361 1250 368063111 368063119
    0x180504080d24080109050f01050906060607031e090e0a0e06010501031e0908070302061605030c0c0a0b01030b0105120708030a030504030c0f030302070b1609030303020f0f0310061b050d0c02 83
    0x142c02601440401c4042d40c0e10180301030351184a13102c140300c8248499001c401f0118024050b6203031001003240c070b8400041c04503100d6800400d428051620a0596529440404a20300c00301100180082d02c0c503483c83c440e451410700c0c4280007461030b001a01580280640b002c0c01064543d0a0000550182841003160301071284080520003451a01e1301443c034005001d200708681d14141806c0003803d0500040504060304540040346840a511104407540203402040b011784408280320524107180d01c0d10400780c03182c6c01e454008414008505000c6040341c2040754059034107258081c0e0561501c0840c41407845c6604203001a00c1514042c0d0082c40e4004c0c480d240c03c030350466183d640d911004e0512101038000139404178101040110b6104000c0d040713640090900c0d000c000c4401c00401d154103500004041540100f910105107030320364240c4050785030840071243c8030314021980d41422009480b810b00000d600a4500c12000d8071264003101103a0000081e090616519805540c1d06070780a20407600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 368065611 1250 368064361 368064401
    0x705100e060f0301061b050c010807030e0d02100b04060807031506030b07080a20091002010f06140f0a061e0504090c03020a080907060c11060903030a09180504080d 72
    0x4540c0c1e20001005108500705405440c1e504180005141403001880072980860100d02031004c588000340f203029203002440c190b44241d84128003100505426035503942184600d0261a11254002c02d20154249000c4001c11000a10b0b40410080d6085072103000017070303013048005001007105c2c1d501d07585555080400101d40959640e0721100034200403140c440025030040188204086a8001c0c0380040c0364007903400301410320144080310a80315104000f071088108841607191039000f90843c0c0140c00010380200012030365225a80e00128640304128030a086501c801c03031329441c01c1e12451042d00d400750b13a04000d0355070441c44500a8600d240c449810f00c80c0034440065206240e008449076a100c59401580300e901d101000340150101501140154001303103010701036140d0021455190580010fa03c810222801c000325500f4452440202c2d090b020004901c0b0300160440395000466141001c44100a4103142500703040b45c0080d0740c001d11564007080711401da42003c0d0800020a5418400c0c4c800c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 368066861 1250 368065611 368065637
    0x14040b0d0c0303020d110105012601090b090c04110c0715050906031819030e010c0618051501090603050c01121805010f0606030504050706030e03120106021b0105070203070510 77
    0x10107240e580210010703444407402601955000c08208400e5941d81e000b070090794140a45958100c40150030300240002940c2e03140c0450200350420300c40d09030010003101043c00c02001c91a203400c2c04481705801142460440600040070400b12088521000b024012150900c0c20301240e4101c3c850700e140401005001d030f44181e9541c0002075016040c0b825080c1c8900c808070f200c075030a1400070000004174000110307034040801d07000388480d2502c090900e440014000e051030000002c000c001c0142d444240044103410800c24000b850052aa2244c02c8404190ba40d860508040c1c9085000040c038640203291201059400354050b02001d0412280c0800d400700c8040424114580c1ca60f030079180c3e41c2d180c4090039011a120b04c0384030f0280040785000e00807403400d80c6440f9501c0b4078070320500e820035039651809008070405000351000d02040606900e56940c2d50100250344c0c02843e40c0c0030b60043c0c69001000001c0d8050000c8482043c2c3c060081d00f4482c0c40c2108108400028404150602c903426500c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 368068111 1250 368066861 368066873
    0x1503261908180307022218080306180103050304030803070e03100903030e011a090907180b0a0609061d03070801020a0327021e060f0a0c1104020414040b0d 68
    0x102614aa690741c0004510300070640180d16880d100c840388850b00304004000261315005864445080408010110314044003e808020040050340c130039006101840c1101f0000c8010046024840c226024500c00d4043c20a40784d00c02400c2c030000300550300801c81000002d0b2202c01a6a0115840c145030210a07070b0100403904120b15042800300b01503554460208041d0180725110b01520400700070040300c400c3c50700c0ca075440404410340c180319040c02304c001441c1c1c140400049000c0d10074600c0b8545085064001440540000c20304680300b849040800f00d00a841f450901c411a0019561403510000c000d00ba00907450b800c00e0703141c1c1c040c01034403c00b00e00250b090000b050310070401d1307400040102003003110b20100240070094004484583c1d4421007d60b0315841c03004d45000c400c440c0c2806001500740090001d21498402c91080c03880840d80f0042c0c01d801c558080111030068030b450040c81217141c01c1004a11442c00749542040b850301c81c61411341019445945d41c1c1d4009001030030a284180c95203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 368069361 1250 368068111 368068147
    0x7050901060c0507090510050d020f060a18050d121b1e060b0306100308132c0a0b09070309050a06050103140d0f020a0605060f090c03010504150326 65
    0x5600419540102c039410441c0401c9813900400780e0714420056400c00c0c041c00c034104280d510034103102d0820b40c4c80820540d0350b41e0700f8940300385500800c842d6a80b0b49808000d403000646071640c0421501140e0006500d08040101501642d40300b23541d02c1200300e80d00c90940303007501d8511461592040c1c0314503c8000543c1d400305c41c84c01442444480b4071580b1a4a001c0060b50040c00b0300314065045401400001584c0100c20400e42e03911003020742c0c45d5044281210f041d82060360068a4654231040000c1c51a40c00303c0302221070303001c20b5860b01040c6c2d883c21020805e50f04242106908083c50600188410f44281d028124182c0701c2c101780c1354890b0300c58544400b501c3c03007a0400c0e5a03c0550300071145551204200541c43c014190905050030101248060746490300701c00040c0c002074035540092003d68031106400b00c07006004007041c1a504100281c0c9940741c1003406054025480d04002c8804110100d2031041145d80c00003c1043c0010020882150000e18014164000b00c051108440e010300030100c1e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 368070611 1250 368069361 368069369
    0xf171303030e21190e0f04091401022a0a030c0b06040b04090b0f010f081c09030602070302060603010605222c0a0b070504030812040201050c0f0115050603070801061107050901 77
    0x1407181c4074403c3c4541e840c0181c81041c013150030f11403000c11207456520f91442c0a0003050085500180d80c201b1418000060010007004201c65440040c1e070003160744002c0c24640741212242c0062070186455018a075882d13000300350190214102d003180c0400907500803442a032051024001003a03a4001c01c01180c1501d03500201202c94850150800c5180300d80008480d0040030103540b0308400313510f4900400d4840e078895078692601c0160882041615006148500c000c5501901c1155141c58034200207454040580341e041c0f01c0d500341700340050985801e48012019480c03110500e12007048084600000f8250301808082c0d012524605244842003030a50303411702c0041401404501e0001d00d4900c00d2080024490010700405000510100361107001740d440048480e075049245480b24001a54240900c2d1400c0c0094450144424850349040d0080364400103266007107000d0355182c0e410085c050004aa405000499410041061031321039042905805554020f0354100c90319030020402008090b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 368071861 1250 368070611 368070673
    0x40f020c0706050c1b0904060207020d020603010810060503010605010e0609040b0406080a1109071205090705090106170604020a08060105180901140906010309030f230a0f171303030e 80
    0xc4c1102a00b41d050088000d00c022071440280c0100d0340e040050b03c0c005015001410050b400301d151404c40d00c8020381c01c0940d54000708015140e61391140c4640d036800d0f0130388010407090304240d0f00081d44d0405009100542d84142c44200030748843c841440403640001200035030041c0c40741000d15a03038aa62080401a040010261001d100d107410240c506500e41e4130624000e802c0e4a00308403d00c0ea10480c10980d220041d0f2000ca016254044001e2503e01140c01c09503010780810b0000900e5030b0800c858034180591252503200d10390b55081000b00305d000305000440403500100c00180c20350b10a40c001c141c21500190080300e1a40154003050500b40300740c001482c542d03130346a5001c0325880d2040e64154422002d1906000103600741d50000c19045442c40c400c801d0100d40006c041003905084281c01c01c00101c1110740b901e0308141e550040060510b282e1000c041030b07074203424900c0c041c3c03202c0c02d2511926088042c0740c800e0b1541d41c2c0c100d00400b18a0f0382c0300c0050145900700340300d40000c0d0207095966501d010f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 368073111 1250 368071861 368071867
    0x703091a0a1e05040513020c12040815090a0605060102120a090e150307031202190c0e01080f060f0402010e031501030606140d0f080903070f0f06050306010e040f020c070605 76
    0x1400c0600038840031408100b41d48103040e81040c40d141d0107802c48099410944000315901c0d5005030001c081d0280100034800d074051140c4030401c410541000d0800c40b003010b01100d1180b4503584200345112401c3e103405c10140c0000300e00501150389600035581106041c0304a50040c1d27150b5004c59266000041ca801c0000c007004030801540500100158100705800b40f0020382d0341c0c02c840000d5840c10300340700080c14114600b0290724124020701440c9500c050100b65650840740920740140705002500036000d004d4108000805c1051002500314400b103041802810b668450f144a4880d44500404c00c90410260300d15564103514248100124924400b01c10140d55046142ca241035510035003001031440f9901030849403d51300e07070300e03140d0050380c02410fa02510381c1c59060404441c450804e865070948140c1c180000d00f40c680009482c01c550050400101c8181c4502e01118540f00c10703100680092141c0382c214496180540c01207510000d402c100501d80641408102d04185440d401040811004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 368074361 1250 368073111 368073127
    0x612030a0518010e010c03181d100b030c040e0907090903020c0a08010218010503130203010e0f10060608060f040617010207031e140706090807080d29060703091a 71
    0x810b184a1a035007400d00c01500b10000f4002407603d01c080f0000350420100d0101c5403101040000c4440c040c00a404034000d01c459002c03070811840d51300361642c0740703030f01460b5a00040c0400d1840c1920700404580910f9850301c1d1401c14410311521001e45540d6860282c0400050042c0c0c4603c00e0000e50f521903009040d440703402a0800007803075481da114481d664010001d0061051205841400281e82400c0480d146c0c1c80349a00300c02144840c5100a4056182000481005000080c010b03030003003002c2c003100c91030004900750708203483c3d4911880000c28946800300c0e03450b140c8001101306040001c0c00000d8a581d84032101c544090000800d401141d40c005180010b055000d002c40303050055207409003540c44858000141421210a5104c60040001c1018810030401307410034152a070704008425115586070900007600d90100d4201c0321b440b840c2c40d00300014060702401c2691110020007601c010f4560607014400283d0100c0e504071304010112601180e14080b584001240d044170040d40b5440c0d17061 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 368075611 1250 368074361 368074387
    0x4110405070906121109030d031b0e0d020418020301060306060623030105011b051006090f051302040506060d05040804050411030c0409090606030b0a0e010c05041202090612030a05 79
    0x900014100a41002d06101d80c1e50400c01c0700c031501c2070798000015079180e202503201c41c6010f5280303180e605010f94814007000a51580042c5140140a014a41c5420040e0b4094070480f1014080c00c0d00008085030210241c54264018611036200c0445203050100d0340d400203003118525082101d4859880d80e0610950341c0c400c8007141c01072403040c0340107985c554060146040c2c2c00140308883c10048804485100c21000841c0c00704500c1d402412250140d012406c0c0c400136104600601051501d4406400310f0310706140649805000765424020500c42c050302400041d082c028030491b085002001503198414280c42200c0c0700324003030b26840352542d04040c2000700b45c407120040c3c4800b2103001d200b84603507405218111400c0b50150310001846040b40c2c50f1107000342c80954006000c8980d020208400e8400e680c2003040e0b2644144000c00414251f40c00640e80d41c007440c0659a2002d641803001001400c29180d0650842001001107207100c02c0c50840741d01e581d10201d036000020798003240242c078046d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 368076861 1250 368075611 368075621
    0x30f0103050c150909090304030804092a0c150b032b11070611070e1306060906140f03010b040c0c0c1a0d0911120a0b16090513060905041104 62
    0x21240c40c070b880c0c40300c850080c2150062444c502d10034492040403409001c000c1044400950340520b1840d111965190004010210010520341440528560550a68841d2244140800c6946030020810074644030a2a0b40003034960b1100119035503030300305003240d07000c01651904c145904400366185140206a5940608104550051214944040800c44c102044210948070380d0b1401b00080c40300c0b0f60105150200e16400148030344800001d0026806071425180140b90140801380b021a984070480421603866115512150230170b0700c02d0f50070a00d0104802d500e103000060010070002c03401030001c0e08545500c40c1b0710000c90104003c7d80100104100500e00421080c042565403246c083d480d0200741c421802e1102c140ca40d0361100c0f1080102c0d01d41d51801d141400303888205000c0009503c5644c0e01e41050080c0c81101c0d88800084034000d05d0018000f9114207990703030603895481d05092181a003402841c03412016160040401c0040d1030b0f00c5024440d0303000e16540c0521b06002814881155 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 368078111 1250 368076861 368076883
    0xf080d0e040204030b010b031905100302030c120d1b050106060e090c030f01050906060c0109033603020105070c08030f0d1b020606060a030b03060a0606020d05180103150308030f010305 81
    0x42d00522081011540028580d41100c241d440b285030340e0790b24803410b1380b071010a41c0e00350030721f00d4600700c10721060640c24415602664801d50846a40d4401c110801440e4543c8000080d519400210a005d202d44501d000040400758050203080041040d03030b031b643c20350b8855001600001c4100d24408564603001c0d01d1075070401c82d143c01c03042c0b46040003401e503622020140242d45c0134020f038030b003c2455a1104030444903c250420000c010700280ca2070700910b580c9031a40b07010504030b500c2c825101300003805980f00c4803850000021072103961459005454541000105a800001c01c600c0004d130a1001d10041803006400c010302c50342c448542c4100021586000002c100300322203c00694020354000400c540c00480c00c59034142c03a11142c1c48218003070054004215010b001c1c11301405030410064002005440701902650306c0c41c64054021503450240c54000d14020708030100019640d4081d87c80184c410b401c554102c02056200d4890004070361051f40e0500d11803010310010401e1140034800881d1039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 368079361 1250 368078111 368078119
    0x2406030601051c030806120607030504050d181205160b090a15120b03030f0c0318030c1003020c01290102010507140f030c0702090906040615030b040b100f080d0e 71
    0x5800c0d800f99481ca10030b240c2500070240007000c0f0108001c0d80c1c1c1c0102140b851440401110340300e00c0c180303400802074034068804460703d2140b00d4418440e54052240085c0e0041200408402c1500e070510b070340500c1c80c9000d070035101d130701601144400510010710300101900f00a5030b0540c1da49400024400303030340b096a02c001d0404021640705000c0c564042d6070100810300c2e410012960000860029045105000c580c1e1385410700010a5481d01c2008005400350354800084e8100d0b02c3c102000349a00c1c1d4041c8031203e50f01c2002c03400501345042c086c2c0c1c060020f4040700000003490300030800340d101001c4200811444040490358409140d036a090043d25400391652030100348185101842c143c003130081c1000380190303c00200c0080d60040d00401519550b64000b080d0802c3c90500144860300ca01040c0d0b0141c502c0e6003000101b0341c1c00c00604c0851400c49030b00c02c0e04c1c081c1541d241e483e80d0740d00000181107220382c4004c1480c0010362000c10100d2501810415015142900e202d034009081d044684144a000d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 368080611 1250 368079361 368079379
    0x7030507170303040b060409060b100e01030f0b0d0b04030504050a120209150f0d060b040c03140915040201030f1814010e010608100903050706060801020904050a0209031c02240603060105 82
    0x45d1014882c40d402210640d4081422340440c50510060180b181d4616003115110710040310075a4040107000711000203880030003007280420803031019280c928800c01d820050322540b8000040b840041968460b0003490314a0501ea01c0d00d00144015680754080c08100541541c9c40e410340c549141700d10742203003040c00c032070b040c400540001c0f40d90015250003452049600c01c20620511500d03030480028100014070401c40440402805030007484c400c0d040040c07800d0100002440030900044e072602194488200d40d0155440358011400340040c21164105541c8416900452003410720303000703022030711480c4298034484404140c0c608441114070010400c2e8140001040101800701300b00d000e0758640300012584207458201516180302d10341004100343e1620314006903044041d8003411000034225401c1c40319884010800090703016260076154180c00c583e50a070721048101504060202c824011354076801620303502030032120064100300486801950800a562806100040c05800c0490796014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 368081861 1250 368080611 368080613
    0x705040b01081612020403060f0e0c030a030e040519020d1a0d03050301030602220f082122090905070e0c030915072c032125050703050717030304 64
    0x1d4a2883d0940c840c28030a4052400750409250740480d0003450304500140412021806048001c000c0e0701000256401180d030908100e14001c90420852a01a038504648640c12010440204070107880d0700c00343c98401d0301c1400040b0300350025101650030030200103940508a229500c400707000d000d025208006010450002a030070a0582c0d05403500a100182c450000c103140600c40c1d4602400796460382e540f010001101000444a0019183c210003620074103452181c92080034a0880541c813400f440c244000910760307140b01c1ca501c2d000c4288080b00d51070556190001030849004503400e80c0c5903000101e0070302c015411403401e5500100074200302490b500d0512a440e80b00c0c045182c40407805050740000c6400306200341c1d4684482031040f8290f42200c40001080700540b0065005280240503640c030f1240050050030851022815a40c0030f1860b103016022141908245481c04d051103d14100300c01010490803c020005544268010040e8506001314107600904121049003260b0003041044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 368083111 1250 368081861 368081881
    0x62a11130209130b04060806040c032901150c0602030705120108070312110708030d0903020d0804110123030a02030405070e0705090d020d140304140411090105070c03060e0705040b0108 81
    0x1150301c0f00701000500c3c040941d0000d0042c20503603008079480d00c83d180900050010111130403003101d12400c88003130195079202c1640700b01014010455010b1003050010062950300400c60f40d200c0005141c0f001d131080c61550ac03d0704a070070548810001a0011503240c0076102e4038010385014082e00401042914515a1002c8543d00b80500710010030078845c418034410b5108010010140080c202981d0311201c200581000804007003100740c00511a6001d05000c0e035000d0000f041c0900c0d008513111044503200401500d600e140300e010000a01600c2d2900104110841c0c0614080c07801020050380e2814141407a503c0c010b400d4000c0b00700400c030303401880781071900641120040711055624094089450001500044048601030900305a030001c1c00d034104008001482a03c1480c0c0751042a850b0765014402194512010b440d0240401c10886980b580694040d20907a4450303000c0d1400d6603100d03620442516030590508016600c0104244640c0c5030500036000020003c1c40d1031040d40ca0035000007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 368084361 1250 368083111 368083129
    0x50d03020306010e031f0b060c0102070f06060e06090105060a02030c0a0f030306151e03020705010e010c1107030213110f0f03040c05040e190618141006030c062a11130209 75
    0x1401b903a0f4948000b5020b48992040e60340601c4090000c54840080f4140182c00c06a1841d00f1100185000c20200325421207040d1540200d0000c3c2c950351507a0b08000500c00c7e1907211010b0ba82c1036102c20b00c4000c400100c100941e460349031080e68000f00d894001e00e030160070384a1a0300b020b0600002c080700b04402c91ba000e610190719071808650000000100c00d0143c000f48900700015020b9424690700c03039014141500800c2e1640030660381d05a185501200f41c13603d904070350000075440603050070805403c0300d658020510486003010050318000703001d0440c60b203980c4491050540800040100010f0001801084c2e000b400103540c180001840a080103481d0402c6401650b060621413200d181844000d0348220307172505402005060003102e5003812100102060b801a40d81e12820b1000312000809005030422660b211808100720383c1802001d41da200d507040d164003282d071000001241900e804010320184d09024603a105141c0c001c240a200f0902c03019964101c85a0041045400719100c030814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 368085611 1250 368084361 368084413
    0x507021c03020a0e0a030614070801061b0c050d0f050c0a0f09021606020f070b150306040f050a050a03090905100f09020a0302040518091603030c021309050d03020306010e03 76
    0x1c016581c85aa4509941e41c0030320b48411504810913110220400046a020240184588500c0310481c1d481400c2100d4000007402a18001030b01c0600c54105541c5062044003202d10600c2e094208648440210741c1c42c040590042e1811650741c0d24220034041c041c01940e030304003419540750000f18201011101180400d104080440b030b40000ca01d44920b010002d14a020750f8440415942c83c0b00d03810b036030585030308840015103007006c81b0b102064105840701940380010384090b01914413541c585e2a144000f0005c4202076034107000358246107002410920055a090b842030b1140544281403540d82401c59800030320041c0f4400b1141d10601a05c0c42c1074090008035180507001594030066060200c000e1b0007141e1005800100707140c0c00c1074400b100d041d03480384910a000202c07a10b0b04200d00803000b07003158611000e004a07200030307654400350510303211050809a41c1c000c0400d111a095844516204952300600c0000341d000c41845000e60f4006440c50502d1022402031003020320380c0a00d441d600540e02f003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 368086861 1250 368085611 368085617
    0xc0224070b041a04110a06031e0e0a0807030201231315020903071401020d0816120b0d050f070f3503030106030b0a05060304030c02040b030304050a06120507021c 71
    0x40000c0c03c0107540418032518142032541001541014641360f41182c031142c00c0381d482140c191602082c810320074420074810900c407106031103089020b0411a001410b40d10501e000d94041d9040c0d500100301c00000528010b0300c20303400004c50011001d07410441c0142203200161800403501403100d1740035a8501c4080320b580151148041e805c400d4480d80003440740d0316465401d0b018070180000c211402507850142c022080c0c080e00c00c2925200030440e150b401c210b945240b04080106c40e2801180319810030494200314090000c0c0b486074140003e50100e001000407105544085a06442d0300030a00070840102a44110040d43c0d03400c2905140441d540d04004080315a03500c900865071440030842e404190b2811800d6a54030b5840c4c0324000c01a0284907981805079039042c2000070305081c1402224072440d01643e807014602c078030b07038204405829507602080e850320081c800400c1d96038415440000400098580e100343c102d5808001040c2c1d40020000004d541044c41c4ea00d20861202006282100d1503207 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 368088111 1250 368086861 368086883
    0x501080307120207080a05060a050702030307020a08030601051b1606050a05160515010b19020a08090d11090a090312060303080c0c0102040906060305040317060105180a05030604030c022407 83
    0x181c0c0072440d007003865021030701c681b2400208006005000c100c440c001d80f0741c16014426031b9141c0c0e4099940f07200580c0d0040060380004600303030100c0d5014014580044051500b203140c504840c94842e1080182811a6074035003003081080700c000c103100c001000421050030b146050021200c0007410354010000b81324142c41500d10342004000c0203200025050b0303000c0181d0003103075840710260003158004030040704e24410b0560400c09958000900c49007110751000c80d29181403004802d001c901342a0020403200e4000d12100000030780d50301c40010f4071500600000140011050500a10310040006030301e100354078046051000c0395101420590102e2040301d402d50b55260106200d0080c810b80d031141000a180141c0442c0c81036040d00242e00840c0690f0b10314800900605c14003c10302420340e0150702045d402c21081301030218100d2550107003000200300307000c160350340c0e0046418058201c4e4103c0000d03800075480000c502c0c00e070707070011004400c1d40300013907070460513040218172403195050141c40c0e8001e05c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 368089361 1250 368088111 368088143
    0x41d06090a02090f120616050f07120e12210408060109180609050a020906060a201e2503050c0607060b03010911040c050a0504091802061c0f0501080307 67
    0x15541c560504c038009403044c1c0d50940101c4100342c441505071003110030070b603004880507490b520510640b0010702448507620328000355030750388078250f660f20210f1605000521a0a0049513101440c444c00000741c10b015001111101120f00070814518030aa07002840030b010911240100103112410b440251000240daa00d440b060f1050b80b418444d4000c0c0994140700c5903074100b100120340280030318400d43e20801d4a880300703c2040340c1d40c0100f14000001404001546103d00c110301e00701d159049060b02039071201c1d692803802050000f1000021522030b403241d140c1c201c1031071110409414515512012043c1603046030703074083e2961400c1c0303540303442048041072243c00d000480c1d0001c03a2180009000b0041800207107004a0002510368074140f01e0b171300e80800c441120340154102e4500750042d0b55860320f4582407034807040040c04c03922050908540510703800401030300c428004029018560618102601c0c0d11426081034924200801140070f04041c010000d1040001c1507804d41640010035500380100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 368090611 1250 368089361 368089369
    0x905040e0c06130f05040b030a060504080405130218030106180203040c0f0311010225030f0602250501063218151c03020c060a1202030c041d06090a0209 67
    0x24422081e40d02c4940010074225110310350b070081c070440740c2c10101501031360307541c40400007110941d0b81281e4044d005034144500040c01075100710361043c07040810700c0c1825200c40100c3c012200504a509003594006044401c404a02410a16440084000340719144c00e28400709111a1314040701c5104a80110100701008032003007001000c3c0c0404940c4203005985d07030800c800c440700a0103116015001d01c0c540301031105004040c1c80400f1301c903419842e41303081ca56074880c1d14100300401d0076162168203010205544408000c620401090000d11010300d17001c81c20000d0031900a80c0c0115402d00304919030004120204801a8001e0b2440d05c401e004800030714082a10502440c2c0792b001c48107222004c00c01c0c9800e01c0110f0540310b01051301c90034094001c0302003420360400d1440001d00580d00c040c1c400c40d2146030100c02420071621501e00811500d80d1554036205a030010341d0130200010001c50103000409042c00381c1c48610b1100d0070704928038100000402c82d550400341c00b418903a600004d442c0a075443d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 368091861 1250 368090611 368090623
    0x1503100e10120b070807090f0b07030210240f03030e060901050d0f0203150a030c050909031e1e03150609060705193e1512040606060c030905040e 64
    0x24000e01461140b16003403602220401e41121801c01140348440881c00c1d891082540100755148600001c2680381800610440794002030000c80861181c46030000d4491042c0c061246051030100072109402c6400402107170080807600801101c0240c0354080021940c0700e0040021034030241c44040c2e6404408004880f14410a50000d1007039007044080c0b81c418106600a5100746040c0003030a1011000000300f0405108900c00906a003600c020305201c0f92420207180f0b50072814840442c0e24107401d01d580f401404c1249000d5014012020a00c6203802d41c801000d031010700391b0100c0c1c141c50f51802c500c0c03c010350368500c004107010700d4002ca0703203a2070394640340220b40c4140d821204864459580b44286218080b06d03100442c1c1e008588402ca10418214049407008200002d61071098080b00f50584e152034a80000e10396070245401c0c2003000042c000710000c00804485900080030340c503150900d0350640395158822001c00800720b0546000c2a44141d00d2400d40340129004291440e144180f20710b000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 368093111 1250 368091861 368091869
    0x801090c0c0203150609100b0d050a0207050f0f0d05311a03011802040e0406020f0708040303080a0501140a030b09120415021b06090d03111009021503100e10 69
    0x1210f00d2000300d444d03a03809440c0c0780c03042078101c81d820496611b1941d602c2c82000544039a0042020a019214904490b5003125034001c0041c1001410150a41c0f2903d1402c142084d07049a1500151482002c1d04c00500c080d0390b60041904000c3c2c1303012940e44940210748110000c60b40c142055988040c0c1255030b0059800040815008400c0301e15404100d0141582c4280700355010301142541e0021918124002d86040710740350200b06240340d4460302c1d030402079840f81d030500800034010456000011408030107040618040e82e5176123048c4c5400b0340164111201a00401850070140c20319006070398800b0403050980b9441109046641c461450b210300c2d0070600c0c41c5052003540046008160740c4010b81e00b0341250413180d422102034110050380444c2c42d4002407041d6400c010200001c07030050800c0300c841540c540c800d2901400d458070b0076040740c1c00d10036034050140d04552100511010742c0341c40ca103069410800394102078514240100c01d13030b00410151050460f010b0020000881325000c1c3d4144070010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 368094361 1250 368093111 368093113
    0x702010507060908040f14120d081312030b0906030a050712080c070308070210051911031309230f060f0114070c09050f04020d1b050a0311120d0801090c0c0203 70
    0x81c0e501c2c4c1c6c0503102c02400d0b90107149464810f9483c2c0c0d0142d80340084041c50302e0f2880c58080d2180400d401000c0340c080e00001c0090505260048401340010304402054071080b815550000b40304c03845508000e010303400031b030210340710380c0c000d901820100794040784980403600001507819802c901403a1010303140c01040c0f00c0e046107000307080000080c450100f0060010318401c44400325500003440055070140900000d4484500c448900f0964041c02101c1e42c61490105508a80c144140c10a00c401e082080d0b42200c010140c6551544501480340180c80c4105804002440c0192810104c1a12100d40003070441e4411aa60002d0702039990041d08014408512508031582e61f00090401c1c840201b4280325880c2102d1030000010811041c0940b02d6009643c006c040d072805c0341650321400700103158914242000341c00c078040060aa55445840343c0194030030704440da08440d03020302b04a15108094991141a0021150b040031168090165070564a10700c60001c0c401448440855041c0c1d40324070f0080d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 368095611 1250 368094361 368094367
    0x130b060706050a0506100e19150e041b0804020f04090f0302030a080f040201080604090c0807030302010902030d0c0233030408091023030903160b010e0114060702010507060908 77
    0x510080e034100303d2103040003140a10498807550203000c9100d011582c3c520020741e0740d0800c00d000d0b180011002d52851030041d0742c203280d5610303004000c94a140104d02140450402c401e0204035044c18052288082800341001e402c1c4c02c09e000000c1c1000d90011b1009116000740c08401e1f08581c0e66a200e030300313001e0b00206003247c8240d0a181c042e640c1d43c4404448404a024040020b50031482454680d20440c1d040c1c0d981c01d010b4030340b20240405031000b520125029020300f000420248820040007005500039400801c806195006050800240040700d80030445c40c951010007584440c01300071003280d200c11014080000d401c3c0798110310380a48403201904ca90001c1400140103145020340580c00041380c0290442200c80b0050f81c040004201e070020440c168a50b00d1155007009010395485092102500e2a009907030032131440400d56800100c0307160b0f50031030060051000c203034201c03409440e2155000305035828141c001074060088520084c10804001966400c020781500143c007596400034121791 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 368096861 1250 368095611 368095613
    0x501022107111b060703030b10020d080f061c0804051819090308070c020315010308040317070c0306020c010f0e060105030d17012603030c04180c0e130b0607 69
    0x110308000d940e0303180001c2c101d9452520405020501205218000b440402c12940b00401c0c0912600030482c150249030359510f04031110f403520800d0510f00c3c213141c0d014210b42912100701034040c4c2c02c00740c440311070103155508205650311400103407180d4103440c02601c01c41480c1c070303c0c0032a1144030ba50400ad0f081000c074100288036420039030a8a010b108040d4410320742c803e800b001b0f0310803114028006000600354034086401d80c0d00801060310060b00150a80348900301010038803071141d03400e030300c12212064001010400d00c01200e0000742211004101039140c01102d4980072012600360201411317903940010400b10001003540403603403582c6404410300510060152150710766900f446064000d00034942594103103031050790114810516810226041d03402c00900d0700101d8800c2034040045000d000210b0000c01040010314810200c447c2c56995440c00d103280c2001050019801c1002c5034103002201003010340200c0182d13003075501628010380c500b482c401303d40b026000c0918038a42140d40020008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 368098111 1250 368096861 368096917
    0x90414070f090b0114070506010b182106180d030525030c110c0a03060e0a1e200919231515070b041104022b0501080316050102 56
    0x81e503c0000340c841340b0f4003001e1821030350794034031450600034403942285005018480c4008042c180204004151250042a44001c600e59074203007140e840c9015030b034a4011110242c104040340e8400c41c02c03c41c6c03040b03901c04003040d107668403886841c907418542c4410008042410000c0685a0002c1504d02d0b07401c40c1c03140c224058014031290007030304000b940b01611511030500029000c03e0400019220300d0900e0300d507450360b100912064003c0c8015018070900343e000300304100001507180600d08100d0880301d50b40e1401c03000416000c6541c00403010001002c4060b07559481e280740d88201c411800300003442622160760001c0404507900c149580c20800800c00307948102010500c916070780c00740701504407001020002380340040d04c0701040c0c8490800c1b41c41c000813140f81005412601c0355581141940c14000040d06a0f00070b104294840c01194035140311400d039131100c0440251015008115035414a800c0940324401d410041030300305c01d40d000c00c0701044001d504070345d080840c0c0311900020a5081e1054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 368099361 1250 368098111 368098121
    0x605010b0a09060201050105010f030f020405030102030408030906060a030206070807060e0717070b092d04050a0902130e0303011208090d05070503100e0c090705070c08060717010302090414070f09 86
    0x1580000700328282c040b075050300522860b81a104141c543d286511451401140589503080591401039000d002c0050f0580302400910b0146101c0c6805036280d10707000300e01516200e80204042d1103566038490400141c2c84010803900307003d03000b12890f96900e04904046d405030004c070040e688180700f121800680100f0031422885c60080c0c035816191358541d51891f10a046c0a02c82c2490340c4140201e4042d00045a507800c9101255004080d150000d98807d0005040354030844904200d683ca90140710210300d88040180c1ca00f40240c00c041001c403d10044196890205000c1c01c1d41d280c1600f4084024400c09905541450400800c02e0101c10107a1410503100c4031248078a038040c0c892445010142000f5009040102d41414000c041c80048101003106812001d060722040c48000c221320008900030240b940302a04100c402002c0a04040c2c100130200b9403407080c0c030a04003c0355401400140c0d600d40c81241c100b03400100e040e080e0305540064600b00384003548030700b1070b00548213070025281e40c2ea5004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 368100611 1250 368099361 368099377
    0x402040e0715030b040b0a15120f021b03030f0a2d091b06120f0204080a0317010918170c1b01020d080c12191526060109180605010b 58
    0x20500103e13418009200680c2c0005006079800040d014080c0400c0001c2240c01900004030b261a040ca064107600c003004403000c0808000320950006610b00031000c0100e80d030807003850030078000d6185203021b4000720183c1801410780c0c4501c42e00e60700002c5103260780c55500840c86000400d940000d564080840c002024607a40440e004000000104100400312001c181110b00645480c04d0712505110320030700405003480072000c455400e1202068011082107400002031180c0c850840c225504c42c411003400905074403240109080c0411718a6070300780b6a9445030000c0c1d01603003082d01102e0713034024001180211164880313140b25100d4111031450b09003a00c005148020380aa504461140108a61040040f20410b459003000c0001c1d00d18802d88159a0354840c14051032074a007486141206019100301010750a150130200409005010720492060080001c01000410321000c03104501d40b90b804c148941501d40741d9075406d224002200280070802e003503200d0010070003583c40e01d008120366004054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 368101861 1250 368100611 368100617
    0x1401050901090203041212110712030b060301180b04020403020919060608060916020703050f0c010e180105100908030f07050d090f1406120906012c0f0402040e0715 72
    0x100000d5041c1c2c1a1003281d00968004943c8191342a40c2003080c0d0714003641da041995000d940302d004182c08010200030304825841980c2c02c10f0038000038000142501d500b44525842440308000400103951014014201d4030600c80c008101e01c1d02c8072000400a00039a40007a40101a0004118483c00c0303180080f110740000302c20400074552203c03022581881304403030654000b150200420400c900c4600717030310644030302441150320300c41d00e0341c2c1e8881c14404080307603100c85a4400b120020003507800440300c01e501c1400791400c80d495811f001503030f10401e02c10302c0307004c0c010008601406a500e109946c058044c000d850100c03561030250380c00e0603140740c0c08803200f0745460182d1948100300500c184c0e400021603135812455651603040160522600701c1c0419003d600000030089016140074200040d403140e0036400180040f50302d44091a104801d0301c421280003619440701c0d1003600350301443d070250450100040d801d8656140e2002c40c00815142c050b0180900c525400020802805041100401c3c00e642d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 368103111 1250 368101861 368101879
    0x131a0a060305100b010504091107050a060b0a080604021305060319051b010c11010302030a2306030d0504030506010b210a0b0111120f0901180303020307020a060906021e10140105 78
    0xc0806011104404c000b940000c400304002c02816072140c2003100359411054455140040e5540c0e03041c986120502c0480d03640d511035040c0300c85440c21054480007810213101030402031400758002000f55444c0e9001a141983da2030100b2215101000270700401c141c2000c0c400307a0071000703003040f42e5908050007148050f8160509031804552003011340344016a81706c4480c6003040d001c500150040d4000501c104003580d545d064a101c1e40c0c1250b00f9a00b0b80120444035244035090410905040044e107032011000e0080800c41000003030000141581111b442e60781141d2102548404d05d943e407108914826414503480092202402d0a0303804a05003000980b1419007440184c4441c03600c2e20181c640c01480094207120f414a2008284000c000320384051420907200e01103880200310000740303034100f0b0313005920104818085041400c1f003d00680882e06005a00f0707444c00600a41d11400d0824144d444008101c4580b100a402c1002920b100c4049070184568181022011214082403040c10b01c101419 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 368104361 1250 368103111 368103133
    0x702190b01090f0b031903140d0515061617040e0106080a0b01020c01021f020705010603030f03050f1308070f0c140103060f0308090922121214131a0a060305 69
    0x243c42101e07010400a4040c2081002d0045180c00310707201b003e819800c3c00212040e030b4a02d0516100203000d0b40040d8000040e160805441406007a40c4060401340111020044405500c40b0b00020030b511036440039000c5080d240311803c0081d14040c66004112a003820070010800036040248103209070002c070307130070408100c030440126640e244d40d070002070258100000941940d1010341001c10882048080989817808680e201c508440c2039900590000701c0380710100c10352983c10300405411070038850341c000c00e50600d034510060356180c2040081800a002a80504214201074078192440d00500c10001e0b02d030340c9403494602c1107801c10980740000d02d0311700c012a070030845480348415260480c002d2401e0201e01e10034442584409803d4011820b0f0702105070f0000b1140030300c0d400c1c1203440fa068a00000c3c90301600036040e201d6000c08030b01200c2c2070040340030f004c83c4003a0526502c980c510b421004082c41c40d0a01d003000a250204a010038030b003941c200092181e05030405000c0b04d10400c11180ca41d004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 368105611 1250 368104361 368104391
    0x2011404021302131703070302070e010503060a0902041508010b0a05060f0d02070320010204060e1e0919050c04080f03031306090303061503140c09030a08030702190b0109 75
    0x31503009500c84078120707109842240301e078003802098030410f160002d4191610042c10030741d41010f21905940c2d00000b660f00c01c0690500c2a840240902203c3c50115418000003a4551000030010484143d40e4140c41096544a4000000125400401301605503e402c0c035140601061151607000e407070300070400201c03410310360100d80a07140351105103030500c40c2c105c450101a41c00014141c0070060601c500c8206030111082a01d4401146800160348034a4800c000d802105c500c3c0280d48205400c540b0700620711030100d4840c010131702c03c8590780c980b95a840b02007801d882c510103003041d1403881c0c002013141c1c6001c82d1009005840c0320008448580000d05220740c0d4920080b04c100d0300103141896540005509900b01c045024420700f400709415131115240340702004404070040c0000d8a0706161001d0089200010350804486c6120500c0c0c45e00e010b0100303507541a40f15000703020f2000040001c81d07c520901c2905511001043c10b807041d50f0707607400c0140540c803007802844411441c00d07100b1598416 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 368106861 1250 368105611 368105651
    0x1020d0212090f031f0b010305010f0e06090718060c02091023150c0109020420070209090304030c0b0c0f1902010f021005091005150d0b0c12040c060201 67
    0x1460700400d28144500d8180024140160210343d0540705680007a184000e600d2903244220594030000590080104001410b480d0181d00c44c0d403000202c107105210742c102458496070b100320240c9180b021030300c41e40030807203801c4100d03540c450381e9415201001c6001d40e80040d50042043c000c6411240300d0b119140403402c0b9821300e00c20b0403804034006c02c81100750446164960b01d0410000c1a401c3c1c4442c1d0003140f9845940701c0c40801025940d103080c07400440c6402d200308505c21107050740300f01940c0b101c81680c0b0740d14811007801900c2540c0e6240000c0c5403031002c02c101c1c1d02456226081003000381e81e51859003107541101e41940840d000303841c00d98071140c034000390f080b10101d1408410b00208005800549180c09420750340380440c019034070401c0c3e2502a90181d60700844220300100040341c0c90101250483d42c0180042000c1c6082051882140e83e4003804400a5600704141c0c20707103a1130304143c926071441100d01d000121180c9030300300070600c013000d004581120b8080e0028801044801c5d44e07040001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 368108111 1250 368106861 368106883
    0x903011103061c0302010b030a1110080f07051602030d0c031b051b0111010504080c1219030c111203040b01080604030c12020f03040f0f0f1503020328060501020d02 72
    0x8056000100401c5035501c43d1054024041d000004400c48020701003400d1210084040c3e5441d040400c00d01d006040500714440100c0c100d2628001504000242c410804c0000d40004100130b00403c61151000d80d0701007858145500604445480ca240003000d0040e050100098011848020100314030450300e009070301616034800051710781905400345441e070007002203150904000714004030307900c1494248600c60107280503649907601d404c071192410f4034101ca00d8181405514060081060751260000b80414120f075505010400d0140c00c8021103c51507050baa141e0244203002c0300080c5502041c1c000c602035801140000c00c44e07a2600c010741c3d51404180d5004000582920901000c14110704000400e8226403040e00e061031314248616107150003039040344001c829040d40800c4000c403c0c12070751000701000c030b37102c1014901d4007c1c0b0003210010140c0803410300d031300000002e683c2d041e0504c55615001c00b003915070091180c1012000002c2102d806594050f116281c4415502400042c1c0c0340710750 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 368109361 1250 368108111 368108119
    0x1c05010f0e01030615260c040204050102070b030702012003070e180402011202270a0503010b030604060905070b0a1206080106210c0801020a080405010b09040209150a0504060902090301110306 84
    0x1d80d1a50b590b950007407903002d9818140602c2d441011078242d192070500e0903100d4180c4143c2c800c00c40031070a0b00d402c00900b081d030f0034490351041108005c240d801148800c00c6600c036208841e00d90792080d90030f13070162000301d0355613a100e418056070082d9405c8801c00b45004510b250354401e00074403200240200d444141041803180c0800600103070045d84102c100c450902c0b800320000d07040c81500d0540e0030326100b21004043e00408007031001c142a0502c0e00c0404000c2070100c00901c00214000d0110391038940280018291517200e0030050103104042111100030001c14a8271560340002e220001d010900b060799489101d0708180700061500e405005803810341d80b04501c1c501c001000002d9200207020754078411220302d900340314009035500342031000d49010300391a1100da090780340500d0241d00f114803480c00984240c11190a10002d602d4407000746502103401e1680f00224911440040c400801c2940428bd110f401c01a0200b00c21480d44c000d800c41640a80003440703100c48180301c0342003502003201d0403508 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 368110611 1250 368109361 368109389
    0xf010605030f010b03071e0203090405060301090f032607050901031a090604150e0f160201110703081f06050d060e04050309040b011412010501080a0c08011403121c05010f 75
    0x60b0320540e00195000342c071b5400d0103030080b90040c041a40406002110ba005a00040746101003802d260007059840343c0210000c1050302da250740d40150000550101a04015180c6100c081ca070070b81d40050071058a04250304802b501c0c0c06030004001e070b880048a40c1c0002d003429020b14684030049203880c0070080060401007240d4070002800024600944403094090b10b8503000500c0d25124009640a174001d83c144e40070510f0b0144034503126003c2d90101c82d04580c506910318005030040c4007036031941603041c68500200e4841c500030f00341100c100209004040c0c150900050314a800c00c00a109415058000b440309580d60b420035500c1c00030807134000d001c07604204181407451401d58440e14003040141072800814966400907180360700140f8207150319500040c01440191707001550564024645101070040c00e0160708028881c3c401803280d01e00300c20440c40100541e030b4062204c100e503114070301e50f030b0380c6c9840030ac0728201d0141103201040c003a11880c0200104045070992240f00541d005134440102c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 368111861 1250 368110611 368110619
    0x201030b030a2019080a0204110a02030a0309020402071406160f0801050d032d0e0405012706150305160c031403060409060e030705070506250807020303040305060f010605030f01 78
    0x3210794103080202c2d44070850140803850341344c4251807840a4000c18004262002861060208031503007500d441904210600c02c01800e40d07800000c4510910b00c9290100d078100c01440407034040d028004005160034003440320140046400641c15220741c0a162442000070018002900e0342c040d1415464001002c1c2d0300140703c00d0800ca0001c000041c0300740307001b284800001c01c160014003500545000e0014003160783d880351f240d101c100c0301045601210100003951402d001200403140285c4840035003110303101082c00903441c0b0351142d00100b8030f4900740110021029801802030804035001b241400300b203401040c425100e0382201c8402d0350305468100150307101c1c3d1001ca0b40c42d000241090752207034076001040c0000da207a016429900c2400001107803075501c0382c03400c5802c1200ba50440350041e0002d000c042000c80c07154030343ca031094044011400d51b011b154100070005200e2060085d406100014001003002000182c1031f2040f451365100309500d90700d410046856210a617050740d03a0007040c90041c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 368113111 1250 368111861 368111903
    0x302130b09060403080c0c1f141c0903030e0613060f02070b19061509080c01081b0c0c04062402060903030a1a09090f010b03030408100b210a0201030b030a 68
    0x40300610340022100310712540300c005101642d40d400d9503031000c23003004021202c403500840a1500303015480811410859403041400c05980e0400300040110348801031002450300a901040c1e4401d8a1400e507041441c140402000c510303c1810304480c507901e000c8010820710340030710a540001e948056403904070307216201580754102c1061007c100c591f41e12800080e910440b0b130707010600d028558442ca5455498611a0380c1441c040394842e505000c40c0d03504001c08030354030540c0c02c030303072010044005a180d0b2440f1207854540003c2180c03090300a03182000115a90b20490188400000d9594000700e0641d40c5210032611000d05445c9480c280d40b0a2001c1480014640c0100180000b425200740c10059104001403650800f500c84143d02e822416070000c24510a00a03000c450f54160002d506d4207161083d010707130340d1003555a104d140310755424a160565070b0701d120315810142450b1180010300311305a03509495440d516000c0b030100e4501038039007049040200780421816000481d450320500030303110704 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 368114361 1250 368113111 368113117
    0x30606090b0702060f07170a0c03030506011d0909070e041401055208010e1503070911040b181e030a03120209030f0601140d0c15020705040203070302130b0906040308 73
    0x454081901c1c7e0b04c4001c0440b5043e000d00124281507540d170381c04943c0e608010b0100c50024056a04000e4a05a0795a200f4000765032030042c12030680e00e800b0142c0d500b0584608100740340d0021903280c02c404040c80140a440c03200034051070802d20003040940c0b1000410307881c040b01c2c00460145000e07401d880011400181300851185480840040f6a04504510350074100e4001642500804c4a100040c80218105100395078040699108000d12020020000c1d542c1c1d542ea1269111007900e9196010351038a80e64103580003004002c0c01d0644031691704100300f4a4001c0070b40954060380c018490780300d030f00040d182c00c801460750280142011203e83d40b012030305102d5071001c4282c90303a001c00002200382c60400010700c5517035104015000a50510480300c5901c0440502d052041040c94817440c0800c0701c00451404549010980480c1103d64290680c1004020341c055030b4014408070421100c240c060700205100f03002820108020382e1105080300f070364098111101e411002c01d00091000802101c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 368115611 1250 368114361 368114363
    0x4060e1b16060902030703151506020f120702120d0c060c020102030c0d050717130506010e150d0c08060a0b090601090b1602040e07080a020907020a12050703051306030606090b0702060f07 82
    0x21b85004035101c5e201c4060710014030121003034860395032440c24181001b4a80c041c010f80b0240c030140803003040c6411856542ca50000b4400041c81c2c00041c45000c6554a54681c44400403481c16200c0070400050041d2041301100306c182c6000b81062190142c452062003203070f01c6a0101c0b056142401400400d040090000520480c2889900050050b000c189030310b50606c210f8180045003080390091610b5030070328030182e2090101d10b2002e02444000e103191000200c0803d8103070f403a07035601c210074181800915a41c2c3d21400c1c0754045d003418011203621640142180e81426100c291183d02c900c001100c08442c14810307207100c403000388240024040351130007050285000920100f44080c8241003241020f006520240740c50b40442c1e6014114141180f89560080710780c0041e0180d074106448103d1440441d091080c01c1040000e61001010300070b600303507241e84e14000e045030141034440c0350260043c0707002c1c0070702e00c040740d4030f9400000d01102a4044442990340504131500300b0095031180e60302da410400c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 368116861 1250 368115611 368115613
    0x12030f02101515030b06030c0a1407030201050708130506010b0307030204081203091e190f060203090f061014043201030201081b03040f02060904060e1b1606090203 72
    0x780d028a01c40c01001200b00801030910040e80c039006440c1011840c2e45280003c2c1800c0c200510700950721041540d030304c00c5500280c03955514495008480c038624030303102d0059408000c1050414160b0542c807052160b4180d0702c6109158a4110f101c56201e01c80640050481c0d100310010702184590f0720146411000a09000d800c2548801a03942070440125040314841d00210410500c01010860010302c2e21103800001e0002000002c2c00d80c6a02d2100c0078000c040c01c0c10981340d01082104504481c0c0290000404c540b00d08141c00d106860309200b03a90b02c1201e214220110306041c1003500d0744011131f03d4001000001990b68001e010107000310391011002c0103e036440c0c8502d20b2203040305400000100300e424401d150b0462001404511025005082d40d80c8d00400c400311a80282007125041600141900c3c0c10082c1840061038520580f0303100c507081b44c104113000a050301d540c11150301a01d440ca80000b01250050030401460103a50780382c00400110f80c8110001c502564490941513002030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 368118111 1250 368116861 368116873
    0xa1503210e060d0203100905070f050a0210061d011e051e030601030b0a27030503060f0a060302070501110a080103080a090806072606090604150305060a0213060912030f02 75
    0x8070015070140c00140101c080240c00004003c05003150341c0c1d07404040c204244007085541081c43c4010010000c804803030013032100019455482034004c00c800d9004207031158003401402d0b21041c050109982800d59005400500c400104080c00107502c0f449104a251007808065450301c010000c003c00226503880c081c105248150f182505c052040c507004c0d5014041c0c0c000b050400c450758004984c0b05c1d140310140b0566a140000390128400d402d000c81c05d405280c0b407501d85d110300c80056204d0070a02c04440e8421250a4001405a0507801130145180510300030080c03c514140264182e100b0745000000140074400180001400700000c3d0070b03079030010701e490004c2984440e01a481d060081d21070701d0105e1081030013000300702890000444034084036030003202076003061404034120010148c961840b40d51511210b00301070901d1550207000b0b40e00b01086404504042d4100002903010100502041303842450100d0903500650440d4200d61a003031550704607107480c0e1401c60716180c0b43d9400c00e0841c0115 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 368119361 1250 368118111 368118137
    0x90602120708070f0f09090b0102030c01090c08121801140c0304031109280e160906050109080f0a151407090e01170a020609190e0a150321 61
    0x58150903200e800180c0380c0b902103042c507020181000c000c150901040101041240c40581d0b4050b0404049404401010800d060040c00503421406542d5164030030350710b0949031405000998500008072911003043d60006034080026010710300c81e071540342203004113080c00d000c2d00354455400051251040c1219504241c0b1b500c4c1d506040d503110390b006a60703101c5050044003041c80e110300100d82110316868541c1d0071a0503602518050060303c803d12000d603a0303031018400850300601400301e440215880c0448002d8a500d449002420540034080c002004440d01042d10100003c4c40880440b040d001816032010350b6540901d1070200084080c2c22640310180070072400c0190b400c0d6401107150b6190715140c181030288003544d04405910103848074841daa50500307100404180c02070010f40659031a0b0350385a800740858201006140025039944011600250702d80d031071a0385134040c2041e400180011454104600d1480700c640c00081c01c81c01c002c00a103822041c029204001400f11402c0000c2c0e40301003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 368120611 1250 368119361 368119387
    0x8090d3f090e1003082106011715010905030a030908120a0801030f1104020714060a05100302131506090312020c0f091003020301020f07051515090a020405040f0204030b0a0b13090602 80
    0x16580441200b40000304502c006c40144003034940c07101007864040400410700005031001300020300600c0480c01d100100701413591080062001522000d030440d100c044492400529407085c03031007480c0480c05145807881051800c4d02c100c030410701035503441040c1c5900359119050703a280c01e0f56088508905802e0032030502d840d1800a408254019400000960141c4824030b050400041840c41d6285c504410400c0705009a820740060340d40507030705206410340c10034440e4020000c01d030340702665002c9600005402c035800035258050364802c0d1900c0c00040c04078202680c1d94504812005da000b141c070518800242010300d030312540701f25555004000d0700c2da02c1e0042400c9a0080c0300c215880b140002e000400d00000f048034011605841c0441305551038000c2c2c03031461405c100d0f02b0042c443d04548012840c0d01109406840c040e1400a1041040c0c907020740740b820007980300c0d1004071b4042964000040459000d40b003004805400034090041c0fa1000f40091801030803004021070b4a10f80c2880002d070940c01c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 368121861 1250 368120611 368120617
    0x70503220918020f010c15020a1b0b060117071b26030a0b0d120806030f060702030301090c0e1003020904201216020a08090d3f090e100308 61
    0x12400c00103201e24100c0c0c014070054130345250804e814070400324040000120f8440c40520b484030b41b44401031301c580000800301ca01c11600038000c03050300e15003ca20b80034081c072041590b0254101b6280d0509800d064100034858640c122003850104440c14007841141d46546c122902c5544224001301c40000f80c00c0100c0b00c5c05100085a143c0940007104000075980c0500c2140e285100c00c541c0e20b91008025030714007a0300c003102c01c1e030402001010804036032151002c1000304003014401c401e4130b4413841c04800c000d40c4d0b50030074410b940f00b04d400e20141d80a118001c9002c0400810080c0c440c3e0104803059070140c010b5445007035800d8126580b80d0404924095245418040c9468000901d0742c0711310000100e030b0800f4010f03103c20340c00b03c420b8a43e502c9940c6c002031419101603201a4003900c6040300070028040707145241018000500c00f8051200d20764000001c50b59000101406180341a800400c0f0780d080303585d0800820101d013410800788a5480740360000c0d070340030441703014020540307880350394842c10740e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 368123111 1250 368121861 368121881
    0xa0513060e0d0f0c0203030405300a110402040e041719080a0b01020105010b1608070206030103030309060f060503030f0d060f1205190b0606030a0f15030302010e030705032209 77
    0x90030a4142041c02580701805503d04041071401400c034000d40c1c2c0002c0d45078801e51141e548114055400c3e5503503400c00440504030761b68602c80355448502034a80c0e21b51100c04040302101c2401080d807207d80a440c140c0f00343c0c1c0a50310150040d003101d6403990781e04801d40149003d95030400c041480010100d4000c068001c0c480216541c1c0e90f8a14140900350308180c3d0071943c0e01605590500b001841600d07070f407105039240100134161003906200a4206403032036205840c0041d410400006c008030905405400440c000381c4100020098803d040300448111141760041d264140c000f001a9295007030340d0300147c19140800e650004040c0d658445010965600c1ea0003108400b80b103c030680c007801024002110150600040c2c039541c00c45607900d0b204104001081c2c5441a80084003080106015502c0b490703d00d80300c038000300424000d0482d580b456403080c0c48114010743c01d10030f0b0440e8211010041d01c250030751013002181000712080802c032035614107055401841d00144c0c40001c99040a0080c59820 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 368124361 1250 368123111 368123113
    0x2160e070e040f181a0103261e07020f0a060905060c161d180c1e0d081911060c160803100918030f081504140603060105090f0a0513060e 60
    0x4d40180380c01c51012034800d42c8040102c41040c0100080b074003c0d2064084441641001041c514036601d0701d914034002c2c030503055000040c0c1680c420b103100c0d00d0001884001c1c0205c41c800c091361030b07910400068210f58052607000035070001040050b0b0500e0400b03002d000031418240d9002d04061070f078020742100654407059041c07078441d0001c01790340d81070400c541e00030000f85014103840d02103038042c690350590b032040c00d070107407440741ca40c0c90024030002c00400303d10130000c00074103030780d40300c0c2c20b00d20300741c0e040003500e181220b11600b201441c1501a4007200a0f0042c448082c000a60700e4440711055500100e540000e115440303840440083d031a00021445007030100240c607600303801e000c1c040c01210b00040190300c1042c5100007034000300350481e03a6013140481d10300d000c0002e650307031664410310490464441500a42003404030500f500c00300c40c620380703d00400c0d01200e4241c3e036200104208410f050703580540388d66000d808203c2a0101d80c200380d81c01660f40c0c1d0488080c5580340d031172000f203901041404100b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 368125611 1250 368124361 368124401
    0x150c01090f030f0815010f050c0303101403030a0c080708070c180f0506060d15080d12050a05010303120c201b0f0a0e090a0f0305030702160e070e040f 66
    0x1c05400250143c003181c4a0703d081c10161600c10307140e0500000c18560f075410700c0001860011075a100d542190304c1020020140c0c0d071030342800040d40d01080e5182c001c1103200303a1044014400c50900000350f0b0800d02407a40d4003400c0c280c181e210900310b60f05c0380300c2c1030706c6003030342000b4142c0840c120003040802801110140031320449111440000c48002e03614005249040400380009a0b5420060f507403985108000000c0c00e4450705020058200d180d40252440d005d04044d03502a150000014207850350459414000c41e601c900c50307242201d07424000140402c0703030001400c00700d0400d980803031141580781c1020308030355a0b4414102100c6a100f8071801040c1c0c1f12003180030000c0b000e00d414120210054400305208000f40000407a1019140108050b1004100026030100350030000051080e13001445080303000d00505005040e54400c440000240c030600340c210990341c0182e28494110340d1410038500d101d444291007283c201c240711000c141c1c800d440306601125030486209004c1640c2070b480c04400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 368126861 1250 368125611 368125613
    0x40f06020706080906151c05070b1c0b03120a02010b0310050412031e0c0306030b0c03040515090a0204050c0d06091d010e0a03180b180a08010902030a02150c01090f 72
    0x88410001040d80304c1c02d800c10000d1042c0099107075050b0340b0000c02100c000030f41540c10a0042151a402c20014240b4428a58002642b400d110014402e2824256400c00700142d0900c440c004d03603822071f801c90340590049070326120000d5210007038401841e041c4000b103020300c003400001c1c0c070f0a000c078042095a40d5a410520003000001c0030f41c070040000f42d040c01d205042d2030700d9080b8180e086444052400130385680c0b9508400d8466408000510340c0101c40b0b0890782040e0110710070b507401c215422503441c400d0401b6401754945074a0f5062003044080024417500d00c10340d00303000180c000904043c0103110280190104034600d401035201038480c0e49400110410001c0442460420001340494039034500403542c000d00d0000f10b030030b100781609814094040003400b55807000c036251580c002c0030f07103800224514003184050900d05003000d008a60303107080581c03200101401c80340d403120001d515031712040508005040c0641c104144854110000d8108599507038210700b501c50f42da80488495070149104c1c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 368128111 1250 368126861 368126867
    0x1519050a05150301090308010501050c12041401090614030412140c0a021e01200304030f1a0c0a17060f0a030303050f1b0412020d140c12030a05090d08040f06020706 72
    0x70002d05012402404524042c1e24050070222040c09032a040080010700c17008511000c01c0882040d007407034400c0550740c40d5144507140700c080d682c8076801d001031038500700001c91a10440704010302d1200750789140d1640c0c81e9580c0d0381c1520283e22412206100d10100b0110003158000c029208a090400140410300428410070241a070408000502041e03524902c0d249664400719005500d50000450360408205408062960046510007043c1c105001c1d42072080106080c1004604101c40c92000d480d82c80e95107040109020314441c10700010440c1c011703240c0c0011141201c81d04180050900060001940003084079140d07a5041070340401d07200d10038440340002c451080707988940c5000304102000440c1c601250540318074810000d011100760080d00666440c007030329181543d07228030a400a0140d00d2556616140c0800b04540304034050381500c042400040304981c0010319036910302d880c108514041022403c032420007aa0f52450500020a845d00c14519035005001260002c042d41c91030041c0003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 368129361 1250 368128111 368128141
    0x2307032a0f020303090a020f12010504030504090f05071e0e061306020615030a0201050a022407080609060a05100e0604090209030d0513090c0509130b031e1519050a05 73
    0x380300b10b500030020801a02d10102c1c0d070f0110b080d81212080e0501c417100000503001c0c0c02900c0400c56075443c010030300007003513040001841100c41500d020301409048115103412988111042004580c41403101144890344000c00d0705501024204913040481c1c00c0b0201c3c0713035600800c00ca080018601c14003070040036010401c0766030280814010744c00348440100802d4460303410983c002d051140114090302181e0007445002041070381c4440d03210a40c1c0103a1945211140c068038541d011581c0c1c0800b0400074241000414803811016001c0c0c00e1043c54103043c00091031906081d601001000241040295610750050008005801016803a011802c00309400e02d0420100744080c02400c1082c0a1406070b010250800c441b040c07900001c20481404090b6014446c5000c0940d1200584684c1103a8901561101e00070942c280c04442d00da007082480880c42501d20946284243e000d0103004040e424079031811584540401c20303081c1131120481005099400c20740e0000552900c407401c01030400203503030003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 368130611 1250 368129361 368129387
    0xf0f0b030c0a170f0a1b0801230a0207060f020711030a1716060c0c030305010b2a0307050f0601030b070c151d0a0c030b0603012307032a 60
    0xa0700c0078401100c00507062510912592500128400280d900c4280c1480144d0211403940c040d1401e4159070700d030403019051000e4001103110082d910228007040305128164060741117000c2c1c151218103000c121600c4581c02081010100d400300f1403d000915a4040c642818080003070141c0c80c0c44480c6402c50190f24011561340c000e50040810b0004201010080c18002241010059864412400345441c1c41c0d00e0800180002c2c0c00c02c074007c00c040358422103680c4258042c3d6820092070b43c0b101c440d40d0162203081c500b15604841840303400c1c3e090107030a840c40400d140810440b4500040ea5440e81e04080340f06454005541005004200303014900c1081d982c0311081c1c0c41c00100c107072010394a0324a10010300b562486482d039183d0003074054002d000c801c03040343e500807404c03a80e50040514040307031b42d00b4040c0002c840d011480d002003010307800c0500683c0f009040055040b0100c1a140781004d1503007000600c000c04040e103403d41d64600026101c002c11043c3c12000501d247c003075028030058950300d03400e40c0e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 368131861 1250 368130611 368130613
    0x20303151215090c0f01020a030302072907030c0e0a0e0a1410080c0102010b010f08070207090501080f011802100518060a08090d020606090711100608030a0f05090a180e010f0f0b03 79
    0x5c441909030381d01140e4040641d40c14100140c8560b62824452202c1840c0345840083c030900c0c1c1c1100451071240480795100382d04a0780e090145181038017049901c0c030b200c142000d4208100a605010042404ca10554452080e03480080c9040d400703080321502d0b4406564210b000002c90300140320005080c000c5008456080c0002d04c41d511364000002c01042a051312001000304000100710344074420302100e8000d0005003014001175844104058507030480080034040da610340b048403010351a4071a40070400301d40003044c890954030007603000c0e03469620600205058491a0b603902006a907050090114040190b03030310150b43c500b42c080c3d01c2c64134280c100d604003598480020840150784040e5855441202480e0201080819420440c5002c4064103000c01c4e540c01c010b40403401407000406000800f10941c2ca21025118032201515030303202d010280c6030005e074003800900604100303440b901c40b9103100d1000058122441c2114500b1202200c2c0b0f983c0d203140d108c8010140c0840640601000700c98214 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 368133111 1250 368131861 368131879
    0xc020a151403180a14010c0804050303070305060d05070308120c0304112202040e060a0608070905040504020607021f12060501051206011e0c051c020303151215090c 72
    0x14101520540030318210850070080000040c085644050744000307900c1c01401292032240c428580700c405130200401007010b9600e0003941c0310400d4807038005640a590008040c0d1700d5601d8000713088029110040c0103d4002c0303164245030000480c04c01c03644008500642142d0b8580d00b0741c11503020244805428000703156002d00501000c2400070010039001002113400e90020b03d504114940240390340840003001c0c920202e030014490b048110142c1c07141c80201c4882180d01d440d03490640b002e90b015200c080008074090420b001e20b05281c0c0c0040d802900042149041c2001540043c451059081111140c032482028aa209542000040784a1a40c1d1003050111a05010009180703005021039440c14403400720108000f64028940c4034491024142450402407803040040c00d211400c0300200c4191003202c12854810001c02c100342c0461040d94042c0d45581c031145065039030501840e0203036600c6001b400b40c45e4080c030f004001075100401c11000640c0c0c60325101c3d100e01c1c1001a10500140a00c46078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 368134361 1250 368133111 368133149
    0x3140c03090d0309180510060c03020322090204031b0611120919080601030b060429030f010c020109110406211707080d0e120a0c0602190c020a 63
    0x8000d458814506445507400b0392103600b002c50b549040c1d640842090944500ca40d4500320064211034451071a160358a001c040d40c4080071541d0028215000c1d005030006d004500064070b03084070b0304024002601300a1440d80d1524080002c80e0700650080311002951109030000043c0a01c2e85001004981051f04400c1181c008060b01d42010701054002c02c200003641110707603613842a21100000d1810341c00100c030364855284903501c020a000032b4a5070845400041c650b850503000e04088020200310070104020700540d49103035800c00f01d540d564180260100c00340f420b0b00900c144400020554004141d5150711304058001e60b440410240c01681001c00500000c52010010389010100f1031003503210501a09011104150f800c0300f0070200003000403901c1c14030500c0c102030001c000b424070080000303440721011660303641c0c100382900002e000184500d05200e40102c0b0714040445c022a805854414440c42c480360719843d050044c00850910b02c00c070130950400385102e60250800c070682c52030701c5001d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 368135611 1250 368134361 368134363
    0xa0c050f0f071a0706060f05011202040503030405040b0609130c09080102280c0c0f0e1e06060c0106051c05012d0c03020f0304030e1201140408070c031e03140c 70
    0x1d02d00402036007018203004080c0d020b030303008122205281c005e0b50812002c1d403902d80c00d808041c03807403080f02e002503ca42c1d680d1141620504c02c41d802c88000900a51a061400081c0000352194100240e40610280803001301a204c071803050301041d08549002498114030000a00100800e07084603a00b03a2040c0321411001000d00d00102000d400c902000d41d409150450031a40d1030a01c0c0c2e401842510714504c005031140d1b002ca41d00f82030315801c250410326030380c5012400000003031800f107230b0300c0c42a46400800c4042c00e0000c01005001020400850340c03548030300100700781a280d4000d01c0070300c10050080d074040c004203214070188001d00c01403d1007900038a41c00b0140e040440c0f20781b18902503807105080c2440b40694102c1c1c0c2411014841d140e240d243c1401d000d8601c00f00200118025086c040010741c1165043c4580010b00c0403a0502100c0c0c1d482c3e9440d1800140c2250364225840e000100000c0040f580004044031200c0d4004038000d082180c62070010b040307800b4410511060340e030502505c00b603100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 368136861 1250 368135611 368135623
    0x60a0609090c03110a0b04060509030d0527040219080105040c05070b16050d1a03010e16060522260601030b070c0501140a0b270c031801020a0c050f0f 66
    0x10300840c101050540340e2000131000a4170b43d100841318200005d0005569030018050700c8408400c0f01a1184010b0f104026200340c85402d02506100381c60060102809083c807806200c04207000e0700050403ca010803408903501d043c3c0e2410741c0810712203401000103180c18000d101f802d212600c1c040b41868079690f60500150303000340c49504a10b40e684a5298218480c0050b200744c4100c9210911610800126180b182a01c104010b4007950a0800040d0301010001c2e10390018070320b44c0c80049080c1d203803074811206508280d2120a0254a0801040c01112080d64100c003920040d16007554403240e140441c0d215034603035544050650402001000814124002d81c2d40c041d0060804c420340c1c00681c50158010301852981c19600c3c0481014440012150303840041d4002d8140c0d801509103201d1802c4c48004844650440307409400f020010340359a01d0b120196811042d000241500d208820032003500f6600880c905000241412840e03070300707200c02000416050118080580300e60b800e00d00240ea1958 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 368138111 1250 368136861 368136863
    0x30305100902041d15060f0d0908040303030515010903051906060b0703210608030a03050a1b0905031b061e0409060b070c0b19052b06060201060501110c01080402130905060a0609090c03 81
    0x601d01043e0741c4907010302380d04201c0140d070b07028150540c1c1c0c903203074a000380042400381c5415808a13030b011000322065000e03043d40810340346c00c0f80c010003010980c03640d80600e2500400e000c848031a1500d100055030000140600000f0303200b6290050070007060444000501019058190300500703110b410040d00d0000f00489142040918011074a60b079040c5030000502a5413040c42c84a0310300084000c0384c030360f00c00007020598208030142c515030708024411150004040407510351100c0204600010307402a00445610300c081c0100481c00d282d50789001900310b480c1c0d9032006009006c00601803003000100349000b005070243c650402d04001e64007401441c410101d44c0184280700700022034040c00707511002c1e106100c6c08007000c000007120180342c07a60090641071203903802541c20f00704007241070340c0a00110b118509203c001003840441c03010044034121400b50040c1c0c2c00a002c101030034046961030141c00441c0d40100000c0c021414030050b40d4080701d0b401e0707000c4085a450142c0200024900101c284103d0f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 368139361 1250 368138111 368138137
    0x90105030a0209121c031401050603101a03011d01031e08040909140c0d02010507060f020d020c03070b10140904051507120b011b030305100902041d1506 67
    0x80d035a900c0d03660000d103c1c0511150348480006000d0b10401c000199501260015402400c2d079165035030401e03002e4801410810316180241d0300140310a051075009142d01440740c0f45000882076072024481910b441e03182300d003051820000014000300c0002c01c81c040031119800036007500342d0701d10b4031811343c0c60f0810400318480303000a90503401802901400e513800f510812100708280c6e10585844a500f03190038004a0490040803407680381d03460f0210700e1082158040e15a1440c181c0c01da80d800c2d005085458080c01100d82c2130182079000c00407480076092000045000b15580c1d070103420000b100c40d0001344800040b00c0780300801c2c480d6680c200c401c4494804182c034920010b031138134a001c50070300c02040c44602c0701071402000c0100c0190700a05841303150b00403d80410010a1500c01140d0241c0a80e07400344088003140000300000e8883ea000300d43c00011580c0c1c440d0300b9502e8003031f00410703a0301603403002e2106e200e00c0c100c02c80110044281250040900000036030083d4054011840b81d0158010322188 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 368140611 1250 368139361 368139367
    0x13120c0617010e0a0e10021803010b0d030c0606030c06120516090909080c0303040f02090c43030f14030907060e270406180201170c0d0f0204060e0312090105 69
    0x415070140c0c2080c1d018400d0174054031401c208840504000b5044400044141d080c011104420b504040c81448800750024001c2031307854049880035149556000802c0f074a042d0384000000100350001e55602c064810f030755940d0510942007141c14140e07040a8202030485c51040c840002403504100e503901113590307610006c41c1205140c148183c0900030310750031820b18040013042004202300410907004d11791080352021050f8507030200510f0703140501000f80301c418084c42d10010b440d05000c804880d496007001d00400c4041c00101801c0c100c0001d8460840204103400d880002840c1c010710303c0c09105040702c01075829450640841540c8403502e04c40c0009005110000d140192144500d912034014000b03044060282c54642413501800704840c140c94903031130564681d0b2300302c95040c100b00c0d150381c05079116000a034405460702003c5c030000e440504190b0040281071811040784c000c20a41c40c4c400840181c0356460300c400070306032114a00c40319110380c0001a88a4001c188003095444444080c030300346071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 368141861 1250 368140611 368140621
    0x151215130803010801020405030f0601060504030308190e010b040b010e03030d150816080d0e091b040801090f050c06030132040f0213060801080d050f13120c0617010e 73
    0x165002000340076000c10310020022415450540050040750421780448490b500318120782521135900f8001c40c40015401c000810109110f500d40c01d40007407020550003404902410751104448540e001010280d4550f00c0b220038900e49841518017612013030900e04410b130214000603441e80300311250420322650315100050800d6441a4400140203100125601c0c2c80d5401105001661a0b102c0c41303d01d403003a110600403051041800b0307840c0c4c1c0d20162055540e6140d0901c8a40c03512442d09a4008550b018040000d4410b403d020324a0103a000d18102a01c3d00d045080150400380c0c00c0d104a40180400c00041050050300c1404a030450762489902d094460803000b001e10745070240c2e907600e074458200902c01f0040390903a4000c00c20010104007115015545030b81c280c440725400d100d0b450158000b0044400081d001d0f100510100302c00407011850500000005240c500c0f05811211400c030f0303140462000c2010b8900002c01030f1030f07203041c100d000f20007102e4807070090081401100303545496100070076 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 368143111 1250 368141861 368141881
    0x903030c06020c07080a0b01080102040e04080d0b100c061401030317070e0306010e1801050108030406050d0b1903021e030607030e0f0f1b1f1b06050a0203151215 71
    0x43c905036500c0103a9000e190342c0c1c2d050590300c102042064501441c10400050280014400c44080380e8209618401d40e6550b80c03110082ca4101400014a640e100d5007865180e54a08075402400041c0d81c80c1c01d0208866810032404640c3c0c010554422201440d0040c0b0200e9000001c1e20055070000c4a14001c50761500f808440440c400c0c100203800d441140b0000c100c105081036014803a8000090358013000051302c3c801420303104203114501c000e4204101c144411b40c0315000800c4040740d00003020800314450b201065a545000b0700c944c00041505400740110315111064000d180c0f42c1c1500300141034400b40000f900c40e0710260070b180625584002c0c003081410144400c0b10300e416010242c0703441591582d141c0f5242d101d6040c0b2100365003190082c401103403401822500c180b001160324a0f44440c0c000e0001d841d0001c54001042003d450300c103002000071f4003030003500c1c030500c215000541c481c20003d032400c844402c0e10340c2c4140b0941039080800310504c4001401e8508da486114041100c0d200c0f51914 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 368144361 1250 368143111 368143117
    0x5030712080f09010b01081b0c060a020406030b091b070c240e060f070605060109050a0915060e0f01030506010e031504172a1509010f05090303070903030c0602 70
    0x2004540e0241018810980180003203125524008092030340755140b0380224201c3d10b101d400b041c0880c08103404500c1d000c07107544c0d16000b94010390510b80c2c40c09410181040c0380c114111742c0d80c89001d4001a090050517818040c4d00e0008100340c41700d16482c10a01c0200305240c2550703108000b403031400700e07211303040c0889446014010116a00c5c000300207022001346000e25801d03a02c1c140c002c01c01007035000036036060080450300480d1076400c503175040c1205542e540001d040e003c1c002c0c42c104541082d02003040e1741c2d41c004e21402030100c608001074034104181c441ea0b0601e4554004c0f402e1000840d01110f1070f032184ea0a0035071610003443e00007a15605d035401a6905102c4d550000d406118680d44600d0050a0b680d0841c0181d024980d407036650403214070015151700c0380c410010464250068199104004881151094003034403083e2021100a1702e6026813510048840354000ea442d500d024030f02d080c4074800c1030703088141c0c1e04c003540c40e5107020390024112401c103120081c100120403800c100bc6c403000b5030603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 368145611 1250 368144361 368144363
    0xa2a082802060d1a1e01030b0a0506190914010504050105070542071b03120507120f091e0c12050703030807020303040308150102031e19030621050307 66
    0x81c0075192040303c91031000034000002c400c0140711035110500914640350550901300039018003150401900c00740110b0240915100b00c54000031040c0c2e01040c640e0310000945481c90030100043c00c000c4200c10000d10701a420780c00144150b220844410403642d11004460a560f800e0030000e43d1031125181180c0f5200102c03010700c003611070b00300c0c0e840760206d22650800c1086450380d0055200047d0040540010b900c15150b62000c2031034880c0e100401689804224800303806810a51014543c203400d103c02d5420845a40d00000c04030b030034100200400d480b48080c40990180b00300400c104c40c4d40c42c1f0700000c0140011003200e1091042e0501044441c141e00406070141c2e141e05284003065141540d030f5001d4070302045003c1036050000561151000040d02e01c030700c1d050364400005490f04d041d011118159401220f0450008100f0821004601002c81c0307100100200d0032562103100f10744003200c2c02900c0c46d02508140c104070042026a0401da5070241c030300203948201003000001c0c0751841c40d40c460214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 368146861 1250 368145611 368145619
    0x8060a0b0c0c040c0e030c0105030f0a0b011115040b2203120213120512070507050d0305121312020d1d03010917090a09140f060102010e0a2a082802 65
    0x510103485680a6601170510748140c0031604141c00003001540c01c0d00045482a01114a11300010380207841d68124401c501c906040620031628205035942c2000025038040004240f1201403004201900d030b08540d200082c071780d240b0f000303110700540c0e4282e10b02d1100010742040140450310b102c26506904030b910004880303400f074900a644020510340307421645c80551315401540d1800050354515070445603102d03405800b500e1903030f090000300300900794441000c0d0200034040c00802c030380455104549004110303440351809500040d2a01803c0240c2c120700c2603085422181c007a0b045039800400920080344070b02e500c0d40b10501c1780000300303004080c9000040c1818400486130720314107d2200007401a010180c400010282d00c2c0c44001080c0d40020104c10502c54411000503007000d106c45005801c144140700202c0c90503103900d8414680200ea1500790f840d0740584d104011140504044005290800c135110a011444e0541c0c080d00d8010010111070303416200c15035410a246801c8000042c654010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 368148111 1250 368146861 368146871
    0x8030313030e0a08010603060e03030603030418060b12270304061d150307080a09081615020d06080c0414010608101d07020f01050c03060f03150c070302070608060a0b0c0c04 76
    0x4c080034042c08007484103840e071900d41446c0c80c17a8030002200b1240b080c003000d402186041e140003c0f0120540701403c9014020390303620400304905080c200201814840d201c00c5210900b8140c1d1418102420000d5000461142c0540e008050350080b06403000c4590320704148801c00c240304e00650344031048200a9078400708a02c0c28800940c9050080c3d4054070b61540c600c00d440ea11441e0036012641c9103e4040c00200b02448003154a194040602a03075906c609400c0a0700900c40382e91109980290100e810801e031155420702c0075010070804005141800c072004d1154480b45c04076515900c2d03060243c5401c101589000907540ba120592100c000c00c1d000790080346020001c040f64044000540e8007400502480c2d50350780d1a8001400b40501460b128201036240d86c032100d0400c0140c80509800b141c02d40507900480903282840c81895100f0403a21480703594440042c50020b007003c85581101003071040500038002580c480a800b00151582e25100d640d890703008000c01132a00c070311446ea05901600b00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 368149361 1250 368148111 368148119
    0x140d020408031909062c01051b011b081302010305041a0a051015080c03090a060e1509030f0403020910090e2a011218080301030c030c090608030313030e0a 68
    0x1290f40308140044a9884202e07554884104440844000b2910110041850701305000c20307010005485032400d05040503417810103003140b880300502041c05951190303551030b420103940c0240f4103201c000d206800d1a0030a02450207a214200c2c500d13500b40068101640c0710002400c0207000540c0c849845101c10720b8110518001c411100580300440345108640e00000000417004e8845402680044560f100e00e281903840311f042c051241c00091959801d031103100b00d5900031603510b00c00c030000710006902904103c040100034a034944409170240201e540108424981800030b00150781c1a26812a07800d0055114100107a20403406030b080b00c5070f00d40c603003000c0e1881d844002410741002100b6040244030101c9103041200001255031001703020842c0b41d00e007008030040360390282d20804c04403580006030302615280d01449030400d030011a40b19500340020f0091003c26200780c1c00034161010188455030410b00d1850320307400301600a013220143c002e409400c15000d407620303d0941001408403c0c410395a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 368150611 1250 368149361 368149387
    0x3090b01030b011a090609090903130810050c0c0714042a0e091302010c05010f0e030a121a090603071a0711030c060909091002030114010f03060303140d02040803 71
    0xb0038071600d10039244103843c1140e642003007002d5402152000304594104255142405405100103100c00e40902040100010404080d40c40001510709070008240240120012808454001e44900f00400341442000229000000c0d460103540031040342d00e6407111a140402e0203020b20b48203e00344000c43c04017640c00c21a41440c2500780d002181e0350030090006500501038203c8060311103125011110f641132002d94080d4181c4c07072403144240b000044102120341b1003011a81003210398201a04001a601e0203540c0c4001409401e040c81c1008000c6050f18000c2c1a21144c803007501c8ae8010700c10340d40020026a4241310701001400280303245100078030350f820044450f0344414011180800c07400c0d001905401c000450000c0b03840003500061074507214504021160000400c0d01c1a14402c242a5440c2442c890004d10f0007020030102402141c00320030005420780c94583c60f001c08041c035041c004c00200354001421900c0c108048901999005443d41800c043d10440e00312503620b01c80010145c0340804 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 368151861 1250 368150611 368150633
    0x3020903071401030f0504171b01060305060610140315030c0a080102130f0308030601110a0611030f090309091909082709130312090f03030c030b2209020103090b0103 73
    0x81d09a13001c01504c2085c11781d500071142c0580b4050000411040c0060b04a2080b000402200e02074902614032540325080607806d44825410840e2640c200000744085810000f1445040c0d9249041010303035210510b41d440540c1c007009102403074144080096200945044c844c611400c4805094070304183c2d00e0304c1d0194081c0d03210104107003100c00c030201d00081c0c0ca4911351010080d2036110200618584900b001146c1c15000501c070b02c40c4138004c83d592100065a02d221b600c07400a04021a1912890500f0301d14688920042900c80c0c2c0b9001000310750b171543c0d10121141e81c441c40d00d0320700c6074030880e00c004141c00070300007088018607294001807020716140d81d13402940c50102d0303103211501c0d083c00303903d0034400d008005a4007a1000e00c035400070040060700030264040303080c98000303002924003141c0c1c9441c9413001136880103601003541d803213410707038410761602400b00302c1d80041e201d403116107800304101415020b008180315903983e03448001900310b82c8241c12a0480a81140e100003003544c4030300381258030075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 368153111 1250 368151861 368151899
    0x140706021315090e06060d1b080105011206080c0904140d020c0310060609032d03080711060601021218150c07060f08160903060c02011a0603250302090307 68
    0x7028460b89814051050809405071102d52000940c41e03100d6000384903407504a2180b4034040c540b0f031505a10440f00c494a81083c80301c1c0707552400b07440e51405001600c00c0c03d000c0e0800e03400605200e0140000c10b8000f81e400e092480075140307030701c0035619400d000b2261404078520340c031503011310210500d5a603800a600c1d02101000c0302a50700d448c2030440900200ca00300d100d01b1020070030401e01080410900d86001c14480c40c0d68400520140002852419002e81d01d9011008601941c040c0108154040e080b18a0000e0700c80040007035007041d00c000b0f03654040075508103445480000725550303151381404c1441c044d00e401a00c40a20307817500398021041d0360445d0300d001c503040c800c01e070001030b486c7d11850034100a01c9641d121070070706848454010600e1080d0726a03410610440f2800000001e402d84242482c5804503030000943c00011142c102d0701401a02015106840501c140b04400350301c1c0034600d02c803014100451042e0500944181c0180c011010480d0781401240d10010b000d0180e00b0b1150442 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 368154361 1250 368153111 368153129
    0x90a0608070801090b06150c0d0521011811040e04081210120f02030f060c040503070906031502090a03080a09060f1806080606120108150601110307031407060213 71
    0x680e8540044070f0894900d0741001d0101c0c002900802c202d414090980c3c3c00e0409006142c9152032807041540e45441d111807030940000e440020015405a000020380c1c00c46030030961041c2040d45410a90003204a040a2401c0202d41e00c07210001c40b030110130125030040c040c141d5105103a180c1400c0c02c0c8406d0b00810348500e0080c0c10080000c01c1640601d40d0f50003a038500712a8164030010a88030200b40510b0301c842203800d882449210320b0f4028003000811701c0b43d452071403c00d0307440e4284028182410490707030000d0200e0b41045000c2c400070720b02101e07090901d0f42c009001616194880d00140240c0d180d80d1014201502c006080014143e01018031010756105803180d90049901c003004441071240c95003481401081d440f020700071a132040704c140b50401001811141408005502001070350820b900685459106902c60100d1140c120080c0344e11040909201c115189003c11316500d900c600c0d10020b01300411018004801e9103520240c540850b04103104545811008a181ca41c00030207000704445 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 368155611 1250 368154361 368154373
    0x40e1015080616030204080105090a0204060801020a0203031b040f030b150a05060901120617070f0806010f090b0604120501141b04290a0c03090b030c03010312030b090a0608 76
    0x102909942803044410040091150b0f5441580c02207807003181200101c1010340811000407100401d0007114029a1010041d200d544180c2c4104021208141d122402c96401480207244c81034000c01a280d0004452075410f0482d82c0c1d680300419588a96041060081c081400110500415401c40351103500d103070400081c0c4d11540c40411040301c885101d02984480c04012400d100d500c00d02021600078a21200070a800c1c3c0c076090712414944044055980c103510880b000c0250042e8900c3d018000c0407800090241541418202c4995410901400345e107183c6030120348015480b8181100c00800840340114020301c034925000d0b01030105d000100c142e002d0b240010940450001c4030b0340d2550200c4905044c43e11389050703818a400303d10301c0a00c1100c000c20000d03200118030b00a0080c200440b0b59610015240c81500e40501b07003607625082282002024010003100c171102d2003c490546c1d13000030a41940c6c0c101d00004502030310ba000f207804d40000c000300070b000b181a059080501a00c0f590415280 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 368156861 1250 368155611 368155631
    0x5090d140601181e0902130c0c0203240117032a0606041e0f09050703030c0b01060509010c03030b0f0a090c0914030a0f0c0807260c010c060c0c02040e10 67
    0x100b51465010303d00341c4c00480443d24503010340c841d80112120740c4003900c03100f1a10001c1008034201c0c1c501b45294404202d0251894045180c01d2040485070010680030740c01000c0c01c4200001d40200500880803103205422110070750b00e6041082d50411000c103110811910b2000349001c0100c007088000d114540704407000300da068500b6010b401402141c100c20000ca1501104c8003034090140009081036003582c4801840110b2810300101000d14000d445010460300c2ca450a81d03aa0781c8164401007c001042c40300d15400d81e840450500d02c40c0c0c0510f40401c56800d2880040c454009210a1710342c0030707014140004030b10050b0b0304180b81114440e2120040c0656686064184180c1c0d81c202e654550806000100002c0c0703450385002036180103c00030700c0c00726141c0030f68900e071480c15040704107402c080301e140c0344242d00515403116184026402400c2d071141203a00191015000c20f0340281a983c50700c0da1034000c60712940301c2d111420b400400a11146003e003400c00d0701c0b00894410f54441d170742044000d107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 368158111 1250 368156861 368156909
    0x90b010206090d1215140906030a0c0302060d061e0f06020a03120f0b06030a050a0b270a020d0212101d0f0403020102090a0e07020708010c02030a05090d140601 70
    0x1e00c030707100c080b02511001c076604004581180211200310302c6240d0356410911a401a840c03290b02400040480c20026032050080101d000001051540310ba4003000d103d0f00040d402c00c4120301140ea05594480d2102e41a0354000050003071070f0000d107164000030455460000c150400b8004681d07210307007060411a116013041f40c543c0d041c0100a004540007016202c2c4502080d8815218030181110000c0d8020180c00021104e03402650419500758450b8240301801c0100c1c0301e2b000d0110b804481e813800c640032403901c1c0402842000d140d4001c0c0f1900500040721042590111118540f142401319500e0768840340000d592441950459419009141d001c91900e0900031480789488903d040880d65582c3c065207a034019000070030443c2155001c1c80241110b0321401070100186c10408c0411156140c0410b0091078075006600801d521703810200046a5150084100c0b8885111480c01c213980741d0050380402c40030bc80881d00113044044021800c0b900c0c41000c80d901d416558007080c0b110a818642c1d04d40c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 368159361 1250 368158111 368158123
    0x21e09010812180a090903050d0b0307050f010305090109080c030705070801020901020c270a0902040c140306040902060f0c16080304050604050907110a030816020318060304050a060c09090b0102 85
    0xc2500c0801c01000340c0301d0780900c070b00340c894010003013800410548412004084d14a0210f0841c041000031900c040703041c00500900e9601441a07008050301407030100094420b140e00d00c07030b480c1810b0755440411285c4030203402060b5500c0c1c02010300f81d540c0d840300039810346d00e030700940041c0c42038041c80001050705001070084030a0000142e0007040d80501d00410008079000d010510f00c1c107000c112409110f80100010003a10400000c003000540c5600d50040c08195401e09030400200700203c080004030030b40d004180d076080b050075100041c02c5503103032020808600c50001003110364036000c1000e83d0402000590440d0000f00110300e00f407180c0d9100f0303401d5501e0090b405855070008003031206100500300306080c1580507034140b8000d041c900c08101064244511070105800140100081040c03040d104d19000c0e129111910085140110000350940c1c01c0c000d95511500c16100000481e091000070428142015081041000400212400035180440d41c0c81100b607000d08222102c08158000300300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 368160611 1250 368159361 368159383
    0xc030603051e0f01060303030212221103010f050c0403110105070b01090b0604170a11190b0a021507110606010807020318041d03040906093303021e090108 68
    0x281042c0d407400074606102209003440b24501e21900c25000181e40007405014000c40c06a140107980703907210940a2800c010041011500c0c10024080e044090400d0103c103039480e420001941c41d5a0007900000d0140202c004162441401c0000303001c1300380700001c018000c6034450034040f01a06640001500d060043c144081d00e100440e5004001a42090704840404600140801d25040e1500b0304010118081c00c1c2800213130b40105080402c04c41c400741800c0d03e9002c21542225018424075100c000440d44d400f400404a101280130039125000300194081a0103400c98981549403030000106281102800200c443c40354601240307095004801082c020000c0b540518605820905a80035034400c08032a15001580c03020060011a80900c420944080c4040950303900c0e840c00360303080f0503103140c0d07000054003600e400120138001d9800f25101e9902440c40030805011440c80c2420340b944107a542c0003a400034880300282101d02000d0103a0f00d0b102c402140e03000d0707032a601c5054040c0d8070500403030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 368161861 1250 368160611 368160613
    0x2070344040501060f080109050f070f06030b0303090a080f0114060a171606030e070503070506190e04060e011508220f05033f0a0b030f01140a0c03060305 68
    0x39500300c0100240391640c454007500010a4580d621911a103071170896501014159640d104010208201804074440b100710600007818400d00f0118170140b071400c030384180710034503554441190860b141442a51994240240a0038945558020f1a512a1210318116146520708103104003860303660220340c0d00940005d40640c40341810314a4155804c2801082c4108611901c1c041d110007000c0387c40c252014008980d0041240001c040a041c40c0a0440e0013140c4030350400302e0140115194507042c0c500199880d00000c50072101c0d65001d035215a504502180c10a0625001044a0700c1c03440c0c1e21412036408168030b050001441c601212500810388040c09030801e5007602190045141034038018150052040401d6074841c0c0e07a45516542c401100c68080d656043c11aa00b01107030001d00ca01c502e0000c02500071388108103002d00c40700ca00300504c0840d005950316000b0300030351020000b010080c00094020844417812080e095103e41c03048503803000c0a401d01613103105240c030a00904040b070364004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 368163111 1250 368161861 368161967
    0xe0a060804030c1e0221070806011a031305030403050a02011202031e2d07080117100216080304060b120a0b0a09030c0203060c040e15100e0f04020703 66
    0xc0d0ba8920208401c025904c02040a0b04560000d40e4409076a142c0584400110410039500300ba211070800286600c90fa950785c005038010001c007402d4022082007280403910465903651444000790094502c004054005e01c0003250203c10440300040305c1141c54000d0301e46285401507540001d0a0740b000f20340d030440d01300040301024201e81080d020b660704000c5110070317804050b6403441a90b84081494840002105a02080c00201500407451601601180721101c030ba41c00a41d40315903450a00c0045004540c0d8001800d0200c04010702114212030380c441d00b081e98174101030401b0000f030b220050260f4070a08403200600d000c1032000030f012000740da0201116116a5030307540004000e15801310705030309005440c010040140d6060000d148a4080c54038503c1d2520f0800340c000300380000003000240e10714a100b030301c0304465a4032078100000500c01d02c3e105086404010201c2d25282c2c0003945542c0044c00424800308040c0c1140e5250040c0c50b1860442c100000c58040c01807440c03180c044441c161075620 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 368164361 1250 368163111 368163113
    0x711040903051c0212011517150909010c020c0604150e04020409050103140f1603020f0a030506012d030c0b0315090f040b0a0e031603090f03030e0a060804030c 70
    0x16084400001c0c02420715a0070315202d04280d41d5a4403440300303031040140d40041c02d980360040c0080fa680c05071035010106141303603690050207007103494071140d4080c151401c080094150741160f01d84000004024140100c01e040442c491400381c0020920b40025004044526141d130601006640c1290440c016000410400c2034040c2c400d90750034040079800c182c0820000c200c6201d113002c2c03240210b2003104140c1c1036030185080c890034464101000d0500c2d8020400032001c4808030003140080c0d079011503820790880703e0311000502c403240304c1e40014600c1c040c24000080003001a550716071402149003c07941c3e4040b09400a1a8a002c075000c000c0c4000740c802e50500c05d03941c0803409558090900c0005035200c0150400003200c4c44011565040380382944000c010400281d0300c0e07003e4010b2540081400060440011350b520385c082c0c040040d61101d0308444103001d0500c40c0540200805401c880144155101d0400400450504448a0150307120f0000040c819109003083c92160f0342640d00d041c20a825 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 368165467 1106 368164361 368164369
    0xb0111030c0a0215120c0901123e0f0a0216090b0103060b190503090c1f081614090111010c17090708060f18030d06090f020711 56
    0x803d004882408038004241c5403c400000f040390780307c4148400407100090800c00c941d810605001e074820600d002c22030311402c034480c0d130980168860441a2000050f00c02043c219540840400c0300e0200408100007500810f5554030580300010701c0180b4402c143c49441d0040d01000e643e90318a46c10540c0c1600c80d48005000e8221002c2c00c3c17007070b0385145d00c0706c80c943c008098091060000001d413514038144100c096105008016401f600e10107900342407441c00e15054000030070440e001207a1030410341d41d10071001440b0356445a8005542d04201511074000015040c14403121700b10010198034280510801d1212590300c88210155100d210036044002030b0011820790401801842840004601951b05c907100304075114554488000303081c0c42420301010780c0400c0c0404102c40925441d01c0d04180200c44008809005c07503900c50801d40b089200d036030070003848846c0107144045a810 = true := by decide +kernel

theorem cover : BRFrame.Cov 367985611 368165467 := by
  have h0 := BRFrame.cov_init 367985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 367985611 ≤ n) (h2 : n < 368165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
