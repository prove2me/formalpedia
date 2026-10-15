-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4753
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:37:17.167961+00:00
-- url     : https://prove2.me/submissions/9aeabe41-0d85-43f2-be34-e7b1627f790a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 854676258 ≤ n < 854856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 854677508 1250 854676258 854676269
    0x71407030f0b04110f0d0f17030711060a0614061305040204030b0f2a070602130608011a03040221030c0d020d0207050a0b031602190c240c06020310050904060c0801 72
    0x203200300601c4240c0c0351b07450b51514154220300b64800d003001a00384100728404440d0304404010f0000100f280c2030ba004440d224175040990102d4a5503654010302004442c40c1e8002e81900c440d40d4600f18080389012406050011070b190b10f181c0300f082d0788500141c1287d10540c021119240004208009c0c0400da40d515980160082882034a84aa00d4500c1d51408036034600d2014148021a4034010b100199060b00c1d29006d20030b0301c121086031036604c05401d00d8000d00c42d03030400d00d6080001e40501c081031000d590103a503005c2c1401011f40e40954034240e00070114070b207001483c4818481800c0300d1100300300402280c0b02c0e41d00036140c6680400c20003400c0400e103400542c00340f04c0d0350070100440000e0b64200ca911401c1824038032000c58145008904200980d0340c10301011416421100c14003039400c2001045818181c406401d40c83d40c40220110980540807190200340c2d10a42c030b03c04070b5029001158040b0880c0c9585140c13540303400000b0100c24007900d090711960365424402d44071680021000e8050315 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 854678758 1250 854677508 854677519
    0xd060315050421032309060610170a0f02032701020906040b0901050702210105150637050c1b1302090f06071b0501080c071407030f0b0411 61
    0x41c0c2900c41035074030300f100711401003040d460001d980307950782c82680031030714108001607000b600c641c1c034000580780700d10142c50280140c0907003004540c042c03170104400b00d11100b194407085a01180c00e050243c940400810010816840300303407401842e841c038401184078696003843c0041003040c0a001c5200b10407491031580c0c282e84100000c0115541783d109640031103c86454242d943c0100c80c0040340e8038010700100940241c10200400140005202c0200c20b01e99868002c103c0d40c2e481103402a0398845d40803445800030010425040304040f40c030402848131400f0f0011000d090944005000b003007a04c01401c00c00124042854040e100007840202c003c6842210a150f508180c540040c201100c10021044c0b95517000400c003032203895a128495020b03500402e119241c40271810042022002e0720039182c06041a170b80c0c08981c0358040c5005901030b42c1071030852810143c990740c45520010314000ca40655114580c000000110403024102000b40301d2001d88105090a00d00000d80c2606440101e10a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 854680008 1250 854678758 854678761
    0x3040e0c0c0606030313050f0a0302100c030e04180206030703060b03010f1e03020f21010f1a010c03021009060e03071208010603020a050f0307030b0306070302090a080f1209060f0d06031505 83
    0x400c41940346d4070554004540e44c3c00740034940300008601d40c003140e20007900604151a01c45040b07412503103413440d041c0a40c440742402500300c82000212814000c02121088000383c045001d070a050016640c003c4c058140000d0640d11105100380c0fa0700240e200209008000703809003c110902c00020151100803000c02406a00356070006421005442d42c6034025045207100c0d401e691401201c11044d896030b00001c010a010b05071014010740544580e14a505000040104544d407141802681580c1c01d03074003601015070320020010180984100a684058071010300c08816641070008022091068080019038003071000042c2c49180168054400c2c10320600011580c0380c0c0010444d44510109042103a5aa654031811f4006080000003a6007522440d41007002e00c0e50142d005080581c000c887c5400c0035543c41a400d552002c20303100c0035440c0d0300038490b5040c10741003031000b50040c0301004040c2810608031002c2c85103a80c000003d21041203455007030800900049140c4501340180c010400d101a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 854681258 1250 854680008 854680027
    0x7061401033909050c1902060a050f0412050d02040e010b07020111030412030e12011d0118021e12030310030605010504090809010f0e040608061b0c0a0b06010203040e0c0c06060303 79
    0x10302c14640f0480c806036850310006613003513a10350100c40d07030300781d0004c0107100d809903009000b50365990403079148004a1420001c964841c0c0d03141c10551151350700050190003444840c6003110680c100c0000c040074076070203020104960300364418080c060022511140c1d101d0b20140001041500c1e800441d9031990010041800403000740c444c061142e07509401c010480f424001e02041000d5003640c4810095440c0440c03402131486203440c1c12010501000c000d104128030401540d0000340005070080d4440802458644d030b9021844000b40400b40040c448880d04085054179800c0d03501c1190302c5803c031239105009004003c420301c030725800740006480400100d07100e07035102903852042c00d20cd103041c080c88080f980c3d0204c0c41000183c0c90280040c20901c03070283e54040b16603172000140d980e0200c0c4044404038400001c084000d5403c1e101c180c10052410400035183d16010342d4003d40a0380c11408100030204012545400351400b589100001b160381d048035032080da0070040d014101c140301c3d41041081c03012 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 854682508 1250 854681258 854681363
    0xa0e0a050705041a130308030a0506030c03010203010807051201021308100515060d020c0c0a0b04140603041e060b0411210907170106031205120c030613020706140103 73
    0x2021410b0350b408998a1700c1000036000341410a52000b03000a000004114000040d60411401104164115000c0d007074031104243c00d074002409243c1076540b240b1020803040c03910807003c0c40070340200d0000520700254080d034802d030304109400840007a40480511001c484040c481c10391b110f88203c0c10724681d03158881c0092403620170355805c007610f9030b0040f502029914003070091502103480104800d42c01d5950700c4005403150041e1082918000a04c48071b1901c40c20040226842903500440c0c0c41c00f213040550341004c5e4140c0c221019940c4035604c0100e00070640302c0e4443c60380b000c2204002140c452404c10000c100c0030281203005000c2022010600112100000d0088181d407610800c01141074140e0356028010102940090042600307181d0201150f03402c40000c1c203500010302d681c41020350304ca000604d4648401c3e170305243c000c1e240700b0018048140550142c0907aa02c00c0c400490042c2c42031031040d021600070781003907a034449002c000d0035208101440818013402a150b9443c2030300c100100400c2c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 854683758 1250 854682508 854682539
    0x21f0f1103030f010302100215070e030d020105010f05060f070804030609020a14010f080a090c090501170a0f02010503070905061803060a1a09090c0303030c13060e1f0e0a0e0a05070504 81
    0xe0141f042045514141c074005d100c01d0055808180700183d8174a440309004041c01c80c0a06542d029020300520a01d525106000e0a416107199403c0301d4259840c20060019941c8130801004003000c09200e01d40004d030142d00284019801560081452409401008601001e5510011100840041d580401d90700480ca08044280d1802c05001a640e908525400f4047d2000010701441e03810001080c0183c82d0b40c829030680d6104c100e2186410421aa0166204480c0d1400fa005203c200c00220056100c0c0008540c411054030b4080c07813040e6540c0c0406d00c5138004420241c59604001020034090404001003540081040c0007800342c1003000f014044000e81e030342001030290300d642001480400d07007000b01040c0b8003400b81c101c82e03480c0350204140115070490751039031b4a80c12152800084041c8070b006002100c0d4802008424654184403c060203080e0381035145041c0101c0006812969460b0801140100021f09450405240c2164080d040b9100200b0301414442e0501040c040b000546802a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 854685008 1250 854683758 854683763
    0xc0d050c091504090f1a0c0301120309210201032004092a1205010e060a060807030e1606021905071503020c010f0b0913031b021f0f1103030f0103 64
    0x4151910b5101149002081c058181c940090074580041d0411082104000b0428054040b6440c035220421083c101480255600d00520780c0c2480103100c0165071130280306c0302920a040864071203640fa5098001c00e030a082c2040d41000f1100c4404056507058002c80c2801035000211a010401040f03105185e40a917001c3c2003403d90355407240a4942810340c521407001e400c6040000580501000c008080d0a50040c4410301303d42028000103c80c2107242802d40900f100402e40204176091907000c032400c1c1c4004003450205900c0d00c1882c0c0c005070060241109221000340207021050810001030310305850b0a40030003202078078078807507000b240000c20004150f072000401d00900a154080c00c40207401688160102c80d460200c20344600601c035030201007103400554012607d13a980201d81030503071445200103404034104a43c010381d500c0800d01c200034000d10040c00d02c43c4110a88a806031040113a80c0380c400030801c10803240401980103240039002c10700c82c100842c5103260820b05103003000780c1840700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 854686258 1250 854685008 854685019
    0x70e030a0c0806090c2818054002010c0c0305061b03060a0b070c03200103141302040b0a0b0f03010504050121060207060603121e0309210917010b030c0d050c 69
    0x595842903518100803001f405004519000c0500c607064210003810181c1c0c0b07080f460120b24007088041050104104001c11405582c104081c2507910350713010418450b442241040040008000043d0358494072602460149000340003518105a0ad40844003507803100031501007040c420420907644000005007500c0e60000c2d06520760f021803a0018501a450304014206c1a0015004101441040005000c148240d0303040c440a80500000f0811060a854031035504000c5c0c034252026051035000204c01c10b9000d003a00b00465550000c41000d90043c04440c03e48400003c0108041d151034043d40e405054030700c2c1e11100c1103504255080707030b404050310010032031600880e024003403082940c4208001c40c1c001805030311000d80094018858024820070105a5501c581a2100141719201c4d10900d40d1780a4908015030740d00003604104070140c084060100300c1811408a04111072202003002d107207000001042d443e581d9010182000b200b45103040c0115010302d0a540401c0c07000070701030003480c8107890 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 854687508 1250 854686258 854686309
    0x90f030807171314030111030106120e0f010c02070306050601170a1a0d0b06091008100f020c0f06160804110d0501060b030910050109020c0303070503070e030a0c0806090c 75
    0x104003143c0510a807248440c0c1c000b010001d080e001c004142c00580404500030070000c143c0c64071400e9580020301819001545240801004030090b6100c030004030700840444081d6911148000c0c00d59107076018080050b00321500400401c91140900c2c1e0704000e09003000c0240d044200480c03810050020301d0310400f603840d08560506a41e01d1694080040806802240d82d4481402d1140c48141c0980d0300c1402960503400180c1881002c4d030280040c4e030b1111001c2d00f410180c048109000d040c0c0d003d04c14140359420420030208000070401c100d03201c02c051000d000c640c0f8080815010300b8a032500403170240030f150b078200000201f0100031140c000300215801a8980c500e410120b005200a03000080018400020300909820000c1c00d0003101d6600c92080c0216a05c1e00080d03000d9009811282c1c03565801403001c6400c3d98010005103034899000d140656041300c412000138948140d0001c20784419804080c03d0140c40000d0220342c3c1d2045e2507000811000c0102030228003a4001070b0110b5558454100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 854688758 1250 854687508 854687543
    0x102040303080420030a12110f030d0209030c040f0905120a0206270619061703030c1b07090204031e0321020c010f0b030106080d0806091806040b07090f030807 70
    0x20620513200098200c03000140980780c44a0120304111165001c00e1340760250320010f1a002498000d2821800042d504162203c9494400780d00f290640a905005004220f0b5290300c0328491080c00115440010420001c0350501d40e08118284218502003901041070343c02c0340d0740009503260000c05910702e5000b42000071a4500d83c5241c015071440b883d0203070300180311141d600156503e00d04d1500d40d004008980d583c1555000010303c20b801c2140750381040c4002910000010003828152070703072800070b0719800c100383ca0395420301c109034118042951303010030140300f4400c0386044a0b00240c1205880c2415020b283c5000d8404210b181d201800e840100030000884005501950198000100240316800031603140c50054240603805c0781c080e6181c41c1000455080000e0b200c01055004c2d16140c0c825101d1200b4400784180c0201103014400e101501e0740d8004204216103481a4007452428066040c02030006201c04410fa014021007641c4840c28004100c0c600c080381c1141c0da100760359074117111400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 854690008 1250 854688758 854688803
    0xf02040207140106060801080a020a030803070306120308090706030501080303132d02030c01090312080702150712050a0501181d011401090c0302160201030b030c1c0b060301020403030804 82
    0x1104000e090a030b0021a005002c034054104000707440c80380e1120741c0c0580e02c0c0e11700341e0b0f81c80a000c0d0010f03520070349901041012410980055400030b04030710b0003240845e1600300941155000100c01c41c0041d40c0c510400c042d0204c28003046000e81030615081c4001d526101c000340c0e90b03000141c5403074444101c03201724004000598078551410401e80380180e1400056042480c18414000401d84c002e000c0d11580103050b611450034a1f05496004903580a082c5400c001219060b800410020a6105038458114030140140410348149101da640d801e22a501041507000c1e02e030040c0c1402d0700182000018050303403051103088400c034a03030b0300000158015182400400c16040b5040302c1419441c0c40114407080841190090580d00096010700802107865401c408078401c82c00b417407040c510840d240710015032003504101c00071035004044905a900300300004030404401c4200494442103103a0f61010003000b141e146a02c030f80120000c50900307140d41c5001d88880b4005000a000c845030300719148000c46d08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 854691258 1250 854690008 854690017
    0x60f0f0501080309120a020918121b0d1d040c0e0406120b09060105090627010602030c0706020109050c0114070506040506040209011502070303300929040f020402 71
    0x184806204559403011820345942c0714440a5000f608400200c1000810000e0120100c5501411030525a07a8050b0280807605229007100594060100d8080b00d02c007024021b44041e8400c00e000020035004054102e00c0c0001d180703186028020100324075800e5100303414000d0440881a01c1c04a84090314100403580b0500d50818554481d140043c081510720f500c0755202e031890b11503503462181d6203487c5506036440d1001d101f202e500030076100c00076600381400014a420480c0442c00b42800c1c0c0401e901c0d0141c262001d810031801030b40301050088040c01e040001600901e101d0000300315002098a416490ba62001429814051a200655440d00c005003c0f1360400b03400c007068604609041c80d08584034013084d0b5003641714600c5800046a01070a908070440181c640341c00424190349540d070b0a0760421616010a256001022540041c0d580b505241d80081d110f010300005060740f061401103010403000352201c240303041e40c1070050840c500c00c42003250029008919800c0c0c0800c0e600c0001c0c0079114 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 854692508 1250 854691258 854691281
    0x80c33011e0b120901200a0c0f02030604030c0c1a19180b040e1e071d0a08100606030209011b020a15050711091b0d060510050a021203040f060f 63
    0x80020341c045a10340320440e090003844c560b0000c3c498500c0e140314003407050440384805d5070850410007a104c0c50307900138200ea60740325214000b03620701e0104a40020707041800848050300441c400324500c3c2c0070042d9200c4244050b1034111031b10001101003200300780303c0703020b060300c01c0104041a06c0d03200f8505003d001140041c800035071000c0c61103611185003d5490300700d4030406c10301139160f102080302d09003490a4001c0c0a80c0d010343c105151f590b070f000111507aa05690705070310900c600d072100032850703181c06a200c40030303000e6440208445141180c0d10011140c8680c08003082610501000010b6a070040140d5400c4003103900741c0303a50359140d000083d000000da50003c18455a8051204c81198100019280450081443d03420708820380c000e025660300103c600c1b900e0302c0126080000341c00c9001001d0b00910f2684c81c0c00042094490b404030301c0d5208007600f40700220f6804a481c5c81d1090b41008803100744044084000c0c258140f44c0d40d2202002100e1200410180d180c41680c031301501c503030b031040d00440c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 854693758 1250 854692508 854692529
    0x30a02031512032502060f0d0f270f02060307020d120c02120319051501031b050d09060b150c0f0718020f0d05041101020c0405131e080c33011e 63
    0x1410b451780d0504d15441809230710070242c18802551011400c51286499215144280d030002c1c52100b080407480c00301000f01101d184011028820150303d41202035440381484e80c005140b001d041d440c0117800b42f405080e00c09040ca013058102582c3d158045800c1f10421440350030a9201c3c0c1340e4080480e0041158101d0354902e07444c0c002008111400d00011040c0e840c000e0320700300190b0a044100311198544400c0240c0410030401040344c19100703903070001680c1800b440001070204840340004036040480c2c20a002c6030207010035100d10181050210349030b401c0c62030005184840c903011444450081120150484c00da010a4485510040b0011100c03214460301e02002203141a141c150102401500003c1c014426401c0c10a61400e2031302c1064060446440458030900240e5070741002040c4025487e013500655891000005a4410252140401c0f4002401e00304010501485a00e00747d410300b2003483c2c0c03103070088001c403901004040741501c0040782ca640702e8100c11803110074070500c50b80c001034182 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 854695008 1250 854693758 854693767
    0x30304050411120703092f091504020c0d08061c03050a05090d030810080d140a050408120306030c060313060b271506040b0a081308030a0203151203250206 68
    0x7258503a115030b06c0319202d41d070300310300d031100001d05001d5a5020020a288051420101800ca4502a08059880f0420072807401740c44074584003180c180c1c1c01071040e64a5075400b015400c000c4941000032207511910036101c081084096000e48004460880f01c080c052220000d100c0d0400c80c8548111112400e001d00205d00360701017864000c08050b001c07200d286a100c8115400300d4040030129010700705c0840f90317a869040c00c80d0240351903a5607209502d103106007c81007000141c0003805004050040841c06590782d00e03071a003441030604100c0450030692048100300200070126940c007120584c00c0da00204c00007003025003500030a01441d500720241c0072035004440401c864031400c11016200c0c0302c4480c0049034000d02e030024000d490043d80200d0b00d6840060100c0156148240344ca254010745c4002c024070f4101841c0c5840d002a401500d404241c40e40010811080c2c180c1130ba0700c596540d100b618040340c40e226640040d9143d001c0ca01c85451224031041c0c000422464400310b80c050160001c003402e945 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 854696258 1250 854695008 854695021
    0x1c05040f031505090d021b030304031407090c0905090a0b0409150c12060518040303020409050406060302030d02060705032202060307090501020f0f070312110a08031b040503030405041112 82
    0x4940b4501a260060401001403c29400031030102c6101d089600180000c4c141b1400a19070107481089113034140c0300a20002008c40d511002c012804828a4064400f441c249900503040e2680061800140100c1c0301d02001075844200c8501c0c2c1c810076000b40026441d601c000006c020301007814010f821000440000100c1080650101e6500440780c4c50381000c8000c4a1041e200303441c110301c01e49a100f17a40b90b414088010011400c2d5030b01510a1900500e05a2514040c5040301c0701960301740c2d1100d03542d007000c0c001c5050800501010b0b1141b40014201c900e00154020414800141010710301c54860100f542c22400034060380c550950300800b0103490385460100100202d1051103014018441c0382056079000000ac521400300f003071000e020302119401d43d110130780000c1c1040980010800d0502a601c0f02a00600580e2a0b80744180394403a52820310f8500c40c010650409150050740e04104030406c199640002150121034040c3d80c007040008128141480034080d42209d4007401011034100940f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 854697508 1250 854696258 854696273
    0x307110109050c0a0909050d081909050307060507051204021203090604031104062937090501050a120b0d020a0b07150b0303030a0914120909011202031c05040f03 71
    0x2c90b00d044c4c0d8038800c0a0b54502c041001e840419202034034903040282032074401881203c00c6a800344207100c02048201701e40700c800d82100c2d0000c00c1035404d178001245c3c071800c00c21580500ca07000b041d28540103042c02c16104180300750303c002600c0203101d080f0440041000003028801e60f1203020006080c95140c81d92410042003680100d010700d4030444c0350038808102904500300412103140c9810349241680494034003a81503078005021400c000042e210083d00c1054480b89280004042c8102c406440c4404040a0400c0c502d9030007060601605100840b040d03030340270724224031b501d941840c04152080c078800030030329407241024065003101000001050040229008101d41e501c55191080c400b10211540811208581621a4103420800205150300420340140e02145d01641d40c1c18040504006410703d0803002d0180303400070780c401050b1507059103450b100da94010266006200041900c650000780c94445c0040303020541e202c201c03003c18070b0f14800e800343c1f005080821061607030341d40c0320304000d031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 854698758 1250 854697508 854697523
    0x1d1c021c11191703220303090203060702061501120b040204030c18230a06080f070e1e01060f020309030a060207121409010c0512030703050711010c0206070302030711010905 76
    0x110382c0b1031001c5010302081501c070303903aa0070798020b028161800488842114154806021804000c948843d02d0400b07030707021421100c2c81c52080d1400152000140f05140c10038600a08c490155042a0f0030005080898400159283c0b02440c01c000e030f00002c80459001481c0040300d03684c0082c0302060110030020083c036544240c03984440310b09a4000c29603070240c1500d0301c080b041c240c002078008443d202d0940000310180c00100e001d034013082d0f01c2c0d2105e0304030f490030491a54a1003240d20848041258600c40c182c00f503008159007103c803289141000c0780050b020010b02c00d441c2000502e07508501c890313101380150b0783c04540040640740b80c584c260401d1000394001c1c60045d50343c8010341088e101114050780c50581038009003400325042891580041d2103c490800c001d0342d86001e02d107601e681d00e0001c8001103200300c2594400181c0e074101b10200074540020540e2106032a071600c1004280181c0010322a58018031614001da0760b40c0d5441000c07200700103203143d1040290300f008400c500300303c401700e03904 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 854700008 1250 854698758 854698787
    0x1f050f0a2f06090706051903140a0b04060819030c1a091e0d12110f070c03030201180804120312091128031b0e090a05011d1c021c 57
    0x360203e8880700022038888142d4802c8902040c810040c0c3c06e2081d505101d8800f501d00c40d401c0004590b0503030300031002480780845612132950b6949110304201d1910303108800103008900010511603202d542601291510315030080c0c14032030b41101d030f4020000b00d1030741d2284104400d1081001c60820300e0a480d03030b9601e6114422203200d01510310b14806000001c90015802160356120803414141080000404000c5a1001c40c1c0400b0002034480b10f84039070007820f440d48101c0c010004d081c03031070800a0031606800105110030381c8031a9030f0030101d0441c9054400303450750782205011f01241454141e900540042e1410038050501c15060140003940f034400e103101005940104406240c40d0038040340071404201682c424501090500120301038802010780c521602a60700c10b0360f500c42036070484c0010308942004050b07000c0260300b410804280034030700607101620001e0a0384001c4d0103a480e1110211031070350940000d00c1c90702c411120f1013044000704001191070101211644054010403c2c00e800c42079 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 854701258 1250 854700008 854700013
    0x703030501170c09180304140f03071805070c020d080310060e03030d0203062707030f0209060403080a02120a0e01021c05040b03040c0f06080103021f050f0a2f 70
    0x524041554031114840800400707002502d03c40400c210b84000081d1900e110b50b1030f604115644031204000410107001d08140c139170840780c140d804120300801819802c038040d41182804000c0b03c014411166000c845c280f0003c1040e41d555981141c041141d0a0040d50000e60788244809000380d00000b11700418205900c3d4405a4440405640c002c6001c03c4103501544100400c2003208810307400ba6800ca40000c1a10041c074542c03c20003207020002d45d400c0c80561070710b0350501c100345415206220344541c40307150560404e80c2080014103d07004601c03015040200008144200c81c0c4284890440286841312207511000c04820050020000841c003030b0240c0324100b8400390681000100d8001902c4a0361075524240c02c0903240102908003800c200e403064405c1c0d0300464590442003054020b04030310360340c5603020740c558010007001301c121100c000313048800d21003c0b410195000044072890050041081d81c0c56904180c106c1d500d20303c03014031a0070799460448900b0420402070f040664141101d04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 854702508 1250 854701258 854701261
    0x2070c180b030d05030c160c03060203011806030c090c0e0d120f02151b070f2f010e010302030705390d02070311130f0f0f0b061b0307080a0507030305 66
    0x141907a800580c04402d004c80e205000113424001e1140003400104010645402d814209176103034210007015400484089070084014429045140e400e0350507119030b4401032000ba855a21002d00c80003a074020105555290b0041d03175802030094424012045001c3e0807900180f2050400c1950321410041d890001004048041d07040b9100160300c002c41c646100d5144c0d5161200300c0005c07052000484250b00902c0284104004125000b188c0340d8494080c10394403041c030b2050320042c12075411300c4114440b9031204440484440e64065030742c4441c0b00081c03c00503520b841e4803005440d940510b180108207181d03c0003507040180d01203c0000012448540d03031549041c60341d41c06503126400d5500610050b80300715801c001182d01941401428840503001840386c4007510a03d40035100c42c80307070320101103880e0001100301d406d040c401c030965410070540c104070a0340e010b4006249803280503100f0b501042c5001203154212402c0c0101c0d1078040d40104007582d15100a00d02400c0d640000c64290042840c020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 854703758 1250 854702508 854702531
    0x1b0a030f0903080904050411030a0317070804030c032007080a111203031506071401150f080705091b12150a0b0306040f140106020c04050108070e04031202070c18 71
    0x94504082e240d001c1c120508041c40403080c00f005080040044d1455680c0c000214101e403020305c641d00c0b605009540e40c04410500c00e440a8004074054652001c0001190810005c00d9125040c101c00303684c0f43c03818141141220300124500303540450807002030701951600003400807001813503954a80c07150301550f8000b40160108198075010000100c5150070400c0010000100040d8006038440010245828000039455003401500c0c0b4039610a903a0303640d010207008240701c90100d03c00030108540001c0200b130a0100254035200c0741c2c81110300071401d40010688640d51401c00701740d6a14040354154440e01d0901408144100c10b55055030007071803d0f50101c0c514200042010280c8050030305e01c62850300c0e084103020003003001e0844240b11035a100c0d040301601c4c0c10318001c24005d03e050f5000f054003130806020002124410783c0b01e800c540e4009401045081d40c1006940c0d4003d40500302900309071426161040030f40714001c0001d203c85080c00002c105075800d844201e01c01c030f40c1c0786803c1080e540c004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 854705008 1250 854703758 854703767
    0x209150334141201150f032010180801110301061b030503070c060e060a0e121204020904030504030b07050324010c0b180a0b0612121e1b0a030f 63
    0x240250000182c1100c5000100c1c2003201900c038240648100015400c201d01c039402d0200d0031160090303625113250180c2001406000b4070311001c0c0da12228602102401c1e44000600703580031078001c24040c00001d140c1e404103203408142c45801000600c0c0240121001045000078907803090040501042d80300d0008503081d90740200808040c5c4d41a22414950345408000341c614552030035048401a44900d50300b01d4000082c000b40c1c1c0211100c0e480420400c00c11101d090506444900366211008140a9040320032440056181c00c15010384182e03000381c58a08084400c1e115a4002030500203c03c0c0c140106079a1003401140302d4400a07030600240c000f080c401042c088048000c290002e100301041201240c190450b280e04000040118004002000641c0381403048007082944c180c0101010080a414111880400501c210002d4400d850070310142402c00d0040824881000c950a400101c4d207441c48c00032a210416100c030b2402e201d442440390030399901100e400c02c400240d0a80851054913006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 854706258 1250 854705008 854705113
    0x90c031b23040e030c06072010020703180f033e0301060504060303020703021206060a090b01170c030415020306130e0712140601120f02091503 63
    0x1e480029800002495100d404411900c400303501c150743e0702c074490301994100010708002080c07202134a814502140007600002d2400c0c04100000142e084985e6006408124162140440303c001030b1140c40d03606045801428903020038030115258a00800c244620100e6001164840c82c2002c500070b54064403900911480d0105d80c080340038040100580b11154003403041018005000018103980d20707000241542c035a6070060b40580c00c014014420750a289403105555000e40c00100201c1c1041404110008240c1c454003604650721003440d095030b131080501024003d00c071400010641016803c000301c640c8103030b03411241b202c607690194280f9140d5009503842440c00814500107110386001c0782004d080070605441a90241c01001b08035101410b5004003100c1c022507602c040b4440c0051814540801078001f00700502100002c1c00008522046031070203d641501c00c4007a40e140c0004069042d202442e04583c54012422040310402280b241c1c0d12100e00c5001051014401802d8203a0503101c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 854707508 1250 854706258 854706269
    0x1e040f051b090105040518010f02041e03080307210603031e030603050c2808030403030f0203090603070311070215030a06090b13050709090e07031109150f0a030501090c031b 76
    0x702c50041020340f80542c042940444c6c90356207500588900310801c0d003100e025603104540c00f0390100d418000d4445000d0540300c60420845480b0340641562210740721400001e082d101081164100706003030981c01014000116581107003440940e4880c5000b0f020350100d1a41c41640c03914003106250030702d01c68040c03a002c894201000e8600149140240401148400ea00b0070811340c41d410080811803900d8402c000411042c0042c640b900e040d441d0081080b100d441074402154001d001a030815550f003400c69421030305a0800003060b1100840d441e07034500510780069480041c08101d2088005580300441c482c00c0ca41004000d12610b94404070103d9500c2194a81c1042901d0030b0003481100c903134010350f040141d0b41001504141c1d2542080e007650205d0301750b00ca5640007150208104001c07119020354a030400c0b6103580d00344c9094040350402d541070159141c415181e050040c40c0d2503d81000c010702440d0458000d1105014605200050305180e101c201c40c95124206024809008011032900390307030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 854708758 1250 854707508 854707519
    0x60903210513080c0c030610050102060c0f0f0706110a02010504060b040c1e05070f03020c0916020a030c02010921050c010905010f0302090a050a03050607090605030606121e040f051b 80
    0xc410f072226126600a1550140c86205030303d80c0400c1940c3c2045240d11809140450030480780c184400207060000141c1240c08410050244100c1031f0039901c01e450265001c1d00d110754441c10316041c070b000604100601d0f8040443c0010700100d00d1031341034005a21960280406002e019052014030086501013401040004e0703035000b01030341c41e102d440c1c000101c8010341d1804500f040226220075410035140c3d1812400342e801790046d042c4d5414044038017648003c611102d280c0100b181203000c0d46030809104024100f100d038100050443e80601d10303080180104160110400012011009039040004000c1d6114400d0480624180d84501017100c166913041e903820705c609104600030b038041d40240c3d00c041e601041010b008582c3d512055007480040d80600021310450400c000301030100034050700404108a0304004000d090340740c03802100c038540c100205e1007074903581d107014001cbc0c54148111324007003801c0ca80d07007803000340f158201501082d680240e0644145508102081c8101c289400000342c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 854710008 1250 854708758 854708791
    0xe010518160902030c0d020f12060f0d0b091608010608070812040302190905040308160f02031b0f072c0103032001020705010c03020c0f07030f0602160609032105 71
    0x15116030f0040c54208568484070340c2400280f10135003084c0d0b00036482c40b5415050200702d4101c00081d801202e40c000c90156841ba074000c6803400400c0140034541c3d009040740140e1001300700046010008402e1840a18480b001400d40b40c844c070314082c0440b4443d450702d51064500c041035000700401d014841c0ca40c00c120881c40d0618690912128035103048a1101003000700c64005241d010354041c941c800e034803d030f80c4c0348118034004060b8041d91440e07005200c00c11025a1002807060b40000c1103624410080781c2806000584074040c6140c421590b40108150140075000180b0b00c1061070340041005d075001c2010030740c0403410422492000c3c02d11003d00014440441800a00782c08a0f10421000c64400050b10308241c68890030f0a607000400544006036000400c81100901400001c0f400300407803000e0301d081c5203117403030f20140760031640030141565600144101a0000b040355520300107921100c00c0c00440e025003005080d200c150040c090207030880000c040c08000302840742c540701d603254548042c02e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 854711258 1250 854710008 854710019
    0xb0d0f052112010e131403071a06012307021207030c06020303090c190b120115230a02150a02071211032b1401080c0303030408040608060a05040e01051816 68
    0x80c0400500151104245c04050602207035603001d44080e03084804000310340e20012444c00005620004e80320101c001710366420b001250703a000516607494612004120f2442c140301c48180141d10820300000c1d4000440000c1d8800c040300484c0c03c90032a80585c0401c2100d03540ea440c01d9899100071101c040340c0f5040507074990840c0c0380250400d04006002040c00c1a141d440d62543c8907564440c02d14440e400000344010080001042d60701d0340020403928180d041c2c80d4003460135050417890740c107040484a02c04503040310010f1081260001030b00317007500801003506010070410000e60041704182c4aa0b02c0e550a24a201400703259410083c400c004000e624000c0900780b280c00b04034441884070580b00308040025200c480030b010b11a008041c403c4058a01c1d4500002145801030500300300780070740c00031f01c200404141181c080ea41225214106015550741d4000007039024511798004a512900d084003441148505600c09445080c5803030400b84991801134540da030701ca4002d00518495000b00500380701 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 854712508 1250 854711258 854711279
    0x140d09031703012423030a0b03011503020105071a0f0f070206010e0106030e070b04082505010905150403050d0309030e031609020a020c030f030702100c0f02040b0d0f05211201 77
    0x14075891481d00862602c255a0301145078450040e944001217004001d2210a0001c2d120301c041e40c1404074020461506d04ac400a585802da511010f0305000303000c0b80e9002400003107640d0035079540600d01c0580091801c584410340e43d13041a10714403507200200300001c00081c00000e40505a0b464000b4042603a0318280b011005000da101041340b050007411000100165418042d1000d4900c42d0701034210000744c16400c1c000a4094400000c20911100d000c21140c1d80240790002500c409645007800340c4c014402518076031141d0760008000d40b003a01c28003107525034103501840d540e81c0300f43c0d0b0764007000303912100309a40c944090141c04103c404050003044401ca42e6030080406640070b00540383e48501c004006800d10714ac00000100c3c54000040c0d050451419010b0703d5024152401d0030000080a41c464415910300000002d001d50782da034410740c40582c3c5141e540c4004c145d021140d01d10229603481d090707844298981405001392480100c070140944090306070b90135408000c60030081680380021248 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 854713758 1250 854712508 854712569
    0xd05010e2409030423060d1d0d02150406020705070803030c1903050910200313060b2413050d11040b030a030e0405060f030a03030c0207060504061b140d0903170301 72
    0x61b4030403010060740f40385c450b05004060369101d80a113400714148018010343e0a00702d020708298110b4010009252038054002a900d8215400040041e20351a06103030007841c00c566071b08000f00500c404400c001e0466141802040c4403648042d0100c8514040d090940c00d40d20700f92030f121104c1e08510485080d00019a20500a0f1380c00245081c8150344841079600041c1c1c025600000c10044c1c0d98115000d01109009801c06241f06131842c1340c5201001782200b4400d01601000d00b00103030001014142c10800c440814040c240040100910f00405e1030314150305111644124000c9040000c01c2000d45800f245a60071340b50543c032848000c010b203d0821000b4030b0020016948815099018003458404200802a45101c2e40300000d148515100103450710680d80e11840411008000900841d9030100c8040c2600c1080303928500d10301d40f9032400104001c1c081c1c00c0c0442d81d100e1000125121a0310100c1041101d0040c01c1010140c03150308100882440309003c0d40c0d10325034545190f00e080b40040160b01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 854715008 1250 854713758 854713829
    0x3050c130216030527030733020a0210020d0509060d09060203070503090f0715050a020a021207262805060a0501050f0108010f050d05010e24090304 65
    0x501d8010342991030034400000000c20f50009101042500306038841491070142c5214070303400160401296000070740d94a0715170240c0d180141c030140b424241e603207840c030600199421294601d41c0303d01c041c440c0250398072601d010a0f4880d0090140ba6000280007081e081200381066440c14a4030708014203005540d030008040c09500c41e41c03070800740702040c007901c00380d409618250345190703030381c1001032004d0f1074482c15060381d4800390842c40040040c101c001c2c40b20881c54943c0d081c4140c9801210354160305100c1070900294200441048060141c5004101c540555045e0516a07810070f5076070b1209000810060101200c0e0fa008440104080390010080c02a1000c001000c56130155140c1e1814100341c0203480d00441c0320b440d10014445460055085c4030380b81c000786000c00b9698903054003015122524815540109210007124003404404e4115403655010380f4202c030003000f0794030507403174800800440c80c0524502142c040703200c40358080125011a05052440e0400c0c250541c800f181c1a4400030b00c1c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 854716258 1250 854715008 854715011
    0x614070c211d0105091509120303070e0f120f0d090f03080a03150f080c010e041401060305100302040204030c05030c0a1203080a09060c1d03010c020a1401020c03040902071b03050c13 80
    0x845c0815590f080007402d041c00041841030305c0d680d04906224030b58031000ca0f02080c0390400e20401c001d150307018880c003030801000c0f1030410030f0018540c0400e0100c2541d800142d81409000005803a210000031041985001685c50102440e0381d104103600d460040d00000701081d0081000d0f85803d846904140000d50500000c0303001241d60f4500d900020415510802003600f10440248282d0781141c544802c0840c01d0f1418095140303080840c21a00505020300000d0503624004241001c41400c00080079560240c4110b607203940704d0800c00c100c019180310302886803007001c5500e40c2504010201200315102c15501e005060465a0705650300d00c0000c2c240c99961b03985018a02c08903040703009400e88200e8a0f2a10741d02d8003560540c1000c00f100c00140540680c1c1030509051180d41e000860804150304440c15600510200300114007910408507a403880e48000708001c100b001c0300c1c1d4001c08a661140389405511460078103540406e44103484050041e403c0f0814484090820303110400406030390000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 854717508 1250 854716258 854716267
    0x610030b3d030f050f0f040209101508010305070501170a0c020a240605271e0106090602060a051611070f0f050127030f0614070c211d0105 61
    0x48040d41c010100e001c14001980381c0052426418040c82001c3e08009080241910b601c0c04183d64448400003a20086c0035030b01d550b001036840c044407010040508514601740c2002c10001400801610080c00144d840d1b01800d0b00c0000c2660054201d0043c8100c104000242039803640503000040940f107400d40300750300031100d5140004510003680c05690200c032004901c5035504101000448465403c290b000c0c81e103128100111510807100d44c42d01280303c244101544c0e80341c000c201141101c00d40803210300345410f40081903050b0002141825640d00354225801d40c0e613184184425078a054403401e0070449182e008030211445014014070074059202150503050340d400314100b1000307042d032102c0040120418240419a885410b40d00c4100702401d00803095080000301c000000301e11b200080c004468059484100100d64010517170000c0402003182562800200141c44909464401c0780c025400055480000000d11403006000b035055488a48070740c00040b10588507001c4e084050306100c020b00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 854718758 1250 854717508 854717599
    0xf070902040e0f1b280504030b150127090e0607080c03040c05010e1c0602090301060f0f05190b1602040b06071205030903310e0412080a0608030c060610030b 69
    0x8050801c070181c1c3c3d075070981d11f610b1403c03c4100480080d02c50101016041c00e00c0c0c0e41682c1c001c0901a20000c4404400d549800c2d1740c40350501c6101c1c1d60b0001c01c4c00340c200b05202d2070380000498542c0c0718000c3d540765120f445e03440b84001a43c074032049400600180300c009052102c1d511560801400b6080581300101044040181000640b4000340480303806800140711849420280a054000d01c0c03010301e8100c0d2a82010400504501180a20b50203040d608203030400341d881e1119400c0c01030849032500d503aa006212243d20300c5184400c0c050380030300e0400003014850708151046810003600701000d04041325030400300700c40e20f034000b8003101d00c0b6200503c541d80c806400c10102c110800f2551810881c0400450f0304c04120320459403141d880d41c52400d04201c00320340560104581c1c1c043d2480c1020f038540c1d0784041203000342180d8104280511020402070070b1040d0026032240510001c41c1c07980b54903a5034074002c03400c0c2c5811108d0f081d007205030840002c00b20814000051440c0c82c3c5040441c1c1d0700c0f08410b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 854720008 1250 854718758 854718817
    0x110601030305041a0c010f0518031e0d0b0a08060604050c070b06090903090402040905010311010c170c1608010c142b02091903062004030201050c0f070902040e0f1b 72
    0x50102000c55982c400a2060402002d284c4002c440304d004003035070a00c414140c8581e00be0021540c40f03104040e002480c0f6021032480d9000340d1a06c0c800600101c01c1070b484a070402c1e6601d001320741c1207009514203030200710000c4074502034404440d400240040b0303640d0b881e03040c08522000685410030718881840102e40c10350742c0d07001520140183d464001007a40c51401e0000d0355480110f515414030511403034420208005520b440006025411200d40d5802c4442c2c5d40c5280514030b10a0081c80085010086500071040d0020780b070701d4291761356107240c2d034904107409a1a4840e04c49542d811108143c0e40340450344030010780700d1400c5801d40005040c0480305000c48e50191440e616202501c51101c000d10811200e0700c80c0b040f15012005420b181071101d0143d101c02d5100b5408041d0610001140c00d42054804014185605440205560090380daa1380f000c8041e411a0180341005046000082e5004030340030041c070b00c5907160502607218644840d070240c003a540520304611841070a150b0fa00b0b0340c100403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 854721258 1250 854720008 854720021
    0x4020418021323011407020f0d03020a05010606030228020601051909090803160203040e0103080304022215050f03031b150f061f09051003020c011803110601030305041a0c01 76
    0x14564030303c02e1400144010b10591000e034450300141314030009602c401d05070001d66a000d584003582d106082c1800c0e45400174101c1c0080c0258280071000c80c4079a0315802074001300300c84244d80b201c2d041801300b0402c866003501e26140c1c016407004d00104514540300c40d40c074030360401c028418840141c981c4008c4d003d4514244040d2584030000052200790800c1ca040ea0b03524003614400b642c2041d003010b50140c5091410301c0054400034010001c0303803c2d580c0b05940b507800c4034410740b2002c14250b014040c00000e440d501c428030300450050080041c460400d203038101c00300d11009000d17502d0000140512440768400b025650800c0c0702c0c414103034100e0706684607920b01a1000d8201d110443c0b4000c020004510b511000894450800081078101c1a40240401c0c09403401151402c3d10003602010860090052910b040d10560134082e10300c00350031813030115110706406a50380340c40c00c00707821080e560344440038400103001400401042040039001c050f130380324040082e80e001d03140c001040d4215080d15413 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 854722508 1250 854721258 854721299
    0x31b02180a0906090f030f080f040f022106090628050c04050a030321090305180112110d0e0304060c080a0c0204320c1605010603020303070b0405010605040204180213 73
    0x81c49005d20516811a80e8040c40e04082d20b007040c442d20f8921801e40000300040e100400140d181b1002c0400c556801008500040040501039004444101e2a039914007007500e14406502500b004a109009000d1149003a820031044803040400ea1b05c05480003000024205016010144000705440d500c0c4040c01000790300a81d03c131984c500708641d9400000140d11702d82a07500b4580600303a40025001000d80b42c928000a03006500c03101a0001a5090030507044401c8040d031038414034640c4000b040d07001c1c20802101c40d008010b800d203010071103a40d83c41a0f00490340070491030751407600022004001001100c043d80760030541c0750103503070100713054898018003080d14400411380c13949803610a41c05201c42803005040d010381420000d41c40041c1e0310810060307501c03503142f904406090090035000703880115400740480b0394901540c00d180381801c1e000e0724100c41a5080c0200020f480c0340ca40251015100c0714900840200c035030406201c020b602601640c00c2482e61590002500f240e554241409200c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 854723758 1250 854722508 854722523
    0x70807030311070503030a09090209040f020301062003030622090c140415060504050d080702060c0102030f0f0c12180f011b0c0b0c13090e0307031b02180a090609 71
    0x403441100c0c3c2c01e040094126601983c003d200799000d41d54449a2030045564a000040c0d5072019a004074001e4210f11020740c045c540000000514541c0c0441070000e201e02440c162000209425412900d1744000e03107402d0382c090010801e46000703405100360000c00720021036001403800e80301e40e910140c480542c1d00960450704600a01c2078942058049d035107525802c0040c988481d400c00300050514080d9000355805108000d17480c0041000000403200032580044c8000c1c1c5032020110a140030354421201e01081404000c042450740700c2c04500346000380c2102001030b003803900364281407070141c5000b0580100c0c2c1c4011988028400d0051040c8181c4c14004800824000026035850503044541006001007051080c1154007298494500b5500700c02c0402c0c0555071400fa549010000b6604c1e90402810140743c42c0402100030f00c00001801c089110340c8905100040803c08080c08035800c020194020709070518002c0002142c10307100398400f810b0000040c5d4000302d40c462004907200e03a00102ea494 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 854725008 1250 854723758 854723777
    0x60a051219110a0503030c21040803070b151002030403080a0e1c0b0907080316060b0907030605040501061103030f0a1d01230105030a0803040f0f06140a0b030d0806030708070303 78
    0x500b82407403401c1c013a140a500440c40e04110030f0403143d5450810702c00d00c0a00c1c0310f280000354440c0b0010100c4000700030f1441260f440300c12905023856412070507a10b20410f0301c0e080e000a00b840c203001060b0105079aaa0b0003850078103143d5110102103510005d1540b041003048100c070a040c0d075440030b10a940110005403c0b40b040b90030320700701c03804d01d0000d01103172410b9004550410198100100312540350742c42000444920031185089406024210391282d881a400800c0103095581581700200312a0b04840501c00c50350e8420090360030410041221020b50020000140461542c4040303c0c1c100c8140c4a000444000514000303900089409801e041030f5180c0c0030b2401070300721a00c030b80340300342c840004a94015490240001e03030351b0f812840002d00010000c00050240010000401441a005201d00103040c80610f000002003216203001886800d004002c41c003c10030500c03a000c1201000344c01014090107541080d1201e4800400c40c96061060b03001c00b103007807402400b40740e0085101ea26481e42c04d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 854726258 1250 854725008 854725043
    0x902030108210304080f0f1b1b15160b01060c050d0c17070c0e07110c09010b0a2607050405040e06010e0612011d030702150913182f0603060a051219 65
    0x20b10754020101d540345070846802100a03501c018242c226000d40c404503564a112038039404bc0010501440902641008000007582e980c00c900500340340b0b0f1143c001d954586130214070558640c900c2a40c060b001035909402c1c080c005c1d0303144006002d505d000b0043c01800c82d0362440e0742d18110004481d85030024000c401d0b0b890032180d0800090105c0003088402c50716960400d54a60b1040c0102c0e40c1010403c003240e05111042e5103404c00e0ba00050b902c07250b20490780c0c034002401600c680d001d841128021b078905108000c8020020400906a400f80c441c00c507410f480c0c0404002c07800000848a0009540c2c4400c000700c08608000002c400c3c201d110003540c1c8400040c010400010b00d003041101c0720400800a6a005907160703490710035004070410000480d12028540c4016080c0c071404002d100402c15032010320410302482004084485414600b00b0405060080c040140802c0e1109500034840440502c01c518101510724103214800c030444035a074080c11140c034100290000d00352040d00303c0c580f500d0f59 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 854727508 1250 854726258 854726263
    0x30703061a1203090105030606040e010b0a090915030201030e03251a040b040303090303090f0f0b090109240915050a05010e07050a0f050d060902030108210304080f0f1b 74
    0x650034070440d051080981540e0b20281c40703200302a0524104000000011100d45d00c207010b64004d4000540411815a10340c2d4410794664400320100340030808100002800b0b1001d802500c641101203d41b10050038559030054028200400c040a450b0000f40411a00d40b42c41012012030200504041450360006040030440c40d506141d2422291070359208001c085030030241c003607804c254146000201c0b4402400d080b00205040c1d54010510f040c8a00c102c0c0a02c0514800c0c0f0490741d006c0c1c6180d400c00c1d1121081142250011000200302000d203607401074244440f4048070a035950364901c00b06803a000c070303a40c2c204084082c04091041542d00c0080c09103009031403150602600b100004120039081400001c0c11030b01400c090f1038100807a403803100210ba442081504c0300c0f03075a03a0780c0600401d6240e2380c600003e500240500d5485200f50403a400d491452490ba1100c13192a050b99036243d0340b5682c41d0900b05a00041c040c65100800f0042510400c504e240103000c00d00c00c8000403100c1881f5407540c0350 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 854728758 1250 854727508 854727551
    0x315150f13090f02131a0d0212090c1c03030f0e0609030a03050901020a090b1b060c21012702210f13020306060105070f1e021002070609150e03070306 66
    0x40f691441032164101d000c0384545868250b408680d49a0f0031400c0100c50107240e031040d41c42c40c0803034a00201e40e1000d6003d1305400b07580949001e0041c0c0c3c5c1031b6010103090102400b0016010001e0b26800405131001c0b84c00f0342e00200f0320380901400802c80d85005400c00b4a0000c0c25100b1707403003c0d480055010380032540751050310b8100d189480250700e44144880024100d0001d8001e0341d40210002400b26510001c44110391141d004040940c0c540340380030010341807140c006000b044847c01481c3c2d4901d24803c0d02c0700655050311000f140b00d1958042e21000100b20703010581d166901164200319015440542d00400c2c100300c038003919003505a1614801900d0101c2024100f0040400225071050061390003107502c0c1e600400a180643e1540518280716203034078070703206015218001030024102c000300d8106002c0b14050003681c007284400700d600401c9075240390a204036800100008403d10040080b250040c6001201e8a0400880190280080e040c90081c4d44121905641d455a00752030000180342d05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 854730008 1250 854728758 854728781
    0x40b0a0f03032007181806110409060506121609030b01090207140115050103020a0225030c06110706030b060d0e0d030f06031709042a12020315150f1309 67
    0x340180d82c540380c06050b404a14150351700490b0344a07440d50308158041c1100502c0150030510600600680001c03248040e881030240f6038000b400d1000110301402c02004944480300b21342d10840031030307442085190180c030380c0080f80c10400c50ac0a800101041074000c0b4a80030b442680c00041ea0380c031071494440e161001e20030300f43c2d84c2641080c81c15103045400c8606041180c0003800c000d81e40e000c080100324206944440025403010b41aa403501c1085600781407081924815481c28072041c0c4c40301400d90341c89901c14140441640110000d1107628030a8201c40044407000d001c4c0780c2802644103500065480c2c0f520251074a6004807414443d07298180181e00442e0948401040340d5821600d4000712084011140d201c95180000c2d414062b841e2030317010b200000000c4400210341d00c080103048010f00041e8550130001022601c2080500c00350b0310803207014412082c20052515508030a20640c0b4503540740d0802c0821003071044000340e112803001042d650b0f2040400b501d500c0d040003c43c0d022110109500c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 854731258 1250 854730008 854730013
    0x5090403020d0807030c17041704030c1503020f07060e120307030c03050c04350312043806010e0901080c1216300308010e1b0405040b0a0f030320 64
    0x10b00001c1f034010286481c6407042c1d0725030700ba83d99118181810089010b006004e100200080d002081c408500d20440644000008a21580480e41003c8040e4055030150140c1400c003040402c000802552014074000c030f00801381c40d11079810440700401c40d0003c5076010080380e100c161a9102c940d25204ac1640101c050b0721203410903050291400c000d6407411f021801a15146078440440740c0d4410164540d204054222555000c1048581004802c240c40880c0c0b14511001400100100704550511140c8040081481c4036507502044007001d402400c0b09042c0180c50070503c80646803c80d05030701070301222004000c0101141c040c414241c100c400443d070160000b03200c400207049540148030448200260303681d04241011214034074007c0c0f240b4240207030443d01c1c581c0001c1542000c0300358129100d0a03032051300d99865150003007a210f000800f218000e5820403051249260591091482c00005040344060a84030b8a11800785501c5810940214020a00c00d42400c000c9030740780441010302e10b02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 854732508 1250 854731258 854731271
    0xa1406030106080616030608060403020304080d02010b0f0904060f0501080c01020d140315130e0d0e0d050705010516061d0f0a0b0f07032307020f0c03071e05090403020d080703 77
    0x100d03ea110400500044525803464100c000003c0c400d0b0050707000b40a600f810780300581441e1078065601c2c1c1c854401c2021900801d050110782078010720580c294600058040707021281d1250401c121100c008004441d40c5d9601e8a0841036450684503950103010000000c02c00010b03000000b9152807500b080070010004030740641d121048541050b80c0c1c100b82ca210324004c005d0303146400204180001c07056501000c1c9056001d501c2054005174034040140c15440705a01c511088040c007404402525010b4451740c0005001c02c110b5115a004041803100f441104580d20126924a019141c5c0305920000c012920280c03c000024280468440700d851a001048480c4040c0d641c4034500400501d000c850b80c2c103000c0000e020300c1c00394010003906049905000b144034051100c514200400381c5074600144500d03824160b82540001b00c680d9080d4009006001c03081c541800e0450540c00c4020341003029045042c0042e4644840002a02552094003c0d00a00c5030881000300388600c01440081058207120703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 854733758 1250 854732508 854732519
    0xb0313170a021b031b040506060412060504060b061204030e210c0405010909020307140312070f03080105010201150b090d171e04060f081005031212100b030c0a09030b0a1406030106 79
    0x6052a4652034141c402040d40d5543c0340c0002d1701406554444141080f0b9560340c441040101d50140f40701c1c1e80701e000b040201c181e0000a200080c0904030301c266224b40090301180110b8011411704040003c001e207854011103004044101c61a441a406007079640207000601c80d51401e8040c00e03000d041e8001041054006640010388e441d02680f05104042825035a0b909803904c06000d444280601610116640d000500c0c00302110200e520003500010350000002c90103610600900c0a61046040f00d401c01d1814044005100c0d40080005580104540f01c00c81c0080d03005d2a8001c04041691045510f43c2d0b00101214481c0c03d0440d032403141501d08010902c821904030240514003d03451612043c01d0fa40c10381c42d440d10480c9a040190715106189000c04050079680041560100c444080907094440d00000e480b07040d800d0003007500c000c7d030500000e00094400300140162119901c0d28448003940e949a03150200c00c107a5050200c1c0b911100d240002c0b1413040170036034001d00c05500030400c2c5807420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 854735008 1250 854733758 854733793
    0xc0b1b070803040302011103010f0608150901090c020708070e010f120b0406050402010e1306060f0903120809160608310212030702120109030e0a0b0313170a021b03 72
    0x40040c107031034011000c80c06151003540450031415001c03a03032603070320b50310340c04070101c14542840388500107005100010084480e90842d1050340c640a0244641c42e400c00e601100605201400503045201d0f10000040c0442d041004100616800114000550610101e00c0300d9102582000c4241300d100d000400000e003401e802254040c0c5c11440010780d41d211440100c1d803910071800460b90040020442004181d10340d401401140c00c55198905044903400c02039469616070302c40a0b00c0300c03a1184110340d800b4000c1160aa01040314004d4030102c0c0c00800310500114001e8200900103030400d0208600703520718080d011111b140b489003440d2400b800060541206000c03807002801040e20541c001c03805001001600e840c281e00400480120b2200c240150081c9003105c0240d0000741d0901f142d0031b10b8100492800c0641d0314a40f0302c1855076a0b90905580000703100a003c9620750110403400f0b0140200360b000e002d844207a039001d07150700032140c0110f10014042c080254400d820202c03403082121004d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 854736258 1250 854735008 854735017
    0x109170a11040e01020705060a0c09050a0909020f18091e1c02010f1a150715020a0219050d09090b030304030f020307030501020406120c050307051c1b0c0b1b 69
    0x700120095505111001c10081c1c51100c038042019800441c04c8001c00c1804100d80b4070691101904024811420344101d410b601603109043d0800c00c880b5040c094170405070000c00005002403c1c00e515070402402144219400c100f0b07684030b004d01e05007881840300703003403010316052000315606d101c000729203039100e03900e039524115000565400c2405421105000307410020040c07000c16010000e0a280060603240446883c100031322942030045100c90006150094840c0143c04c010080c5419099000c164025809015402c0c154465210034600e200b402801070300c6881d2140c070240c0440403030050060080d560300e422445211742840341c100e0803510300000396022030b5009040d0f2907412a13540080b0741400403941024200d03500010380070038a2904045009072454140c0400c219215240c0b1046503103000a0300c43c3c100083e001c104100100c941c01c0c0d090f03860390508000010b40c4000a004c2c4070f4005504070103072008240b0300c94204080c0001245065884100c8001402d0b80321144021041039104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 854737508 1250 854736258 854736263
    0x5010e0115060e0a0503120409050109020f0304020d1505040804080105090a021e0604090608010e07140108010315020d090b06120c030d1110021305040506100c02060f0903060c03060109170a 83
    0x100083c0f00300040d13440d100018000c240103019601901c800801e00c0303540341d00074003c2806843c20a07000041d807203c1d2703208540141d07a00032036850450726103500b003004241c4101e41c00c0e03469040201e0b121070082e80600c80e9a015501c00d400e010b5480e40707050022803c1d200c0041100440303801c95940c410168842c00008200662401e00380044040e2010004205005942012017000d10349000801e41c401c0540c81100703040400412160301c0b80c2d40d0015071410185048d881400a5002c20040001400b403440c40351118109040160506946540640841d10214800d4501000703000603c0340e18144591a00c40c0325040c1c102500451001e940440c3d507865042840b1030401c66001c0802111a8090020009100c0008819541d88081c3c19941c1032444260007428401c03803614000c5405403800800002414070240ca130b0fa4241c900d82e1f000c100d1541c000d0f0001c44842001003200c1d5049a8090191034440c005845001da12420030100041c040580398101042d280c0e05c3e0004050199000a000c610b2241d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 854738758 1250 854737508 854737517
    0x11a21060117160806091e04020d020d060606092903040f0f03020a1a090a200d030c0b0a06210507050907031b0801050a0b03060f1203030405010e011506 67
    0x2190140120740e82d01c040c01c082038101495030207002040102d084030700081e400e981d0707030b0210640f203110800801030390079281c41c103100d801c10b0010440d000041621541c41400100301002003445600400c00da44030307840c4c003182c030584e4546043c8845500000b28070003074645205199148050520700c00d48a41180548260700c40c40400040c08000b074036071815080c20340c40b83d8034215000340e528000e56103245d003100455512090013442164501c110150a10a00e980001000c00101940b1403640c3c2521502c83c82c036038100004006442c9443c0c0f804404801486959409180829406c011600040141c00d080ca80b41c1401c9040040300302c4e03444042603000b651315007180c18065903d042031a081e4a6445243c000c440131082040540d01a401010303400528001d0340107000e40c2c03080455038130b1030900031180d001c0c1e10701c1000d00500d85c4242c040c580c015005044a01403050202c000f0f5001e010444011421b9400001000100b080038000d010791411020004c1c04901090360612103030030b009006000411 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 854740008 1250 854738758 854738761
    0x702010c020409050a0507090c050711010507021f021e39040501092703120207080c0a110117010e0a091505040503030114010806060a051e040905011a21 67
    0x150345a40c0103e00141e030101c1150842805442c1094541e0070328400c440b4194500802040c26601600c2102d43d0b42d9401740001050900b141d0054806400048003a80c01c26480da8500d00a680f5a02a440100440b90014200f0708801800e40b0b480342110140140260040240c8884282c07960701104101c03e15030118ac3c100b00c2061800440c40c0300741540180d4820b042400000b1b004850f54002c426020740c42c0d40502c40245540040a80055040801000510702c880920704c0446981c0c06844228410042c0c11301d0030354940074681c5802e103a42002d9070404140d241d440419a00003880080c14010352a20203013961502a844051740070003424991740c19140e00e095005c200c00700d80c50109469404c1d200b04001d0501d410840e5581d0003d0240d4100c0c2800201804450f42c02900d03003d21540c8010580c40c903040750b07608215110740102c150030401c031480310144022140c1c10b001501c007410300c940002415603d40390803501c0190019002249000040140c410040240342e215000d4004164410415 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 854741258 1250 854740008 854740013
    0x1b110d0302030903160b04020f04050601120f0b121e0d120b0a030209070e1009030f06150b0708120a2a020304180501080705040e0307120504031502030a1b050702010c 73
    0x441c854031140b424002e204034209410000020840c87c040c1e0300a441482c0030859500c1032100b2a81c0564880e404070b0406044038a103010f69401010b8040d84010021500303c51600c0890080e003001c44103103c040c2c11145007a645620601803800211325004000d07c08c0e8210600060881032880040c62625926001c24800319154444141d00940d40905a45c01d0703407900b0b00e0f0050003020003020740b502c112107407282800e5141c800d4036080c1c162a0042460100104d02c0d40d6448001d1410801110390703480030100004881c000000501354050240c80f01590314550303024129603110008020b00051407400c40d12518484c051a04038112441164400520041e84181a45903000d0740e80985203504004058021b100c96581100303040341e8903007084480664860080206072400c031248028564014440800812881003c030011624203040c0240b401d5100d849003844081c44d04258040341d80c001080c011a44064480d1722568140070b0b044051242c0700d903000400030701c03400ca0080d040243c010f001805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 854742508 1250 854741258 854741263
    0x1205070f080406020a03140a0914150f2232090907090b0609010c170405030d110d08040309090c182702090d02060d0b030609011b110d03020309 63
    0xc107401c450516240c641d291070007942d901071103408400040051300d00c2c072504100e1000ba80e4680503da12040c3c040c50410000e5480c00c036005500795407100342e543d0701c0300d1001003040c0184402d010300c00680e95a05514803000070840e101c211041c1040056210030002e140c01074225075048068003005051012078040000d8004914442165014054405100f4540300004000c3c1c11500c2c1503000f4071022000004110b40d600824030140d02180480c49100d001903000a0b2218401c80a00482030400f82c58501080c41c5c07060200310000030401c8e0394076000c96000c040100c0600520745140c080010b00e02960010030600041c4603d800c41c0b511101404002070042c603000e02540007400103118119a01c982c51500e80c0c1e00c00850f20714000c1c902c1c1402505640b240210343c4458006084050301085990a100c2e0542c003071030602150742e0b99020007200700d543c140886402084000000714803d040c92404450400301d00d41443e09100842407200980d10001c211111101100e060050300da076140e0f0b80450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 854743758 1250 854742508 854742533
    0xb0105120a020915240f0703020709051f150e011b0f08120708042001031e0902040605010f0806100c050d0801090b01050708090907051b0a02040e0a120507 68
    0xd43c44141242000001c44600c412903240d440c0071030f170046030f20f481c420316102000b0002ea07078525144010040c0c01d041c0300d005801815018840c0c8110350038a07980f103901408461095980d42c4208076103440d02020100075041c0f80c0b010703180489041d00144001c203c050b100c0748800200c00c0c1031042c08079009249054801c44540116080b1a203908050564500758010781d0100410301c00c803030203150100d80024032070014071380300e55401154201c12140c9035241c00b54220202480714100b40e00e440707400b0031280801d0507c8a411203201310110380110540704200903500f180e040f00e0704000c2901902c000e1540e1101c0416004001600e101141c250502c6c0200e80c01d2200700000fa0880c4200d80d07280d440d0070351022040d8100d51803264100300618894004446502c01c10743d01420080c0240301211840c501150a240c22822a0038100c2c9444010b000a004030007000030703111240e402040c1078a0650a103802801c900720841c6d005464081281d80c0d50b08422243c0d500b07800100440030840c101000190030111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 854745008 1250 854743758 854743763
    0x80c0d110d0c02010e1605011407080d0f140906061305040f0204020a020303010915030b01061107090e011a060c0607051c0612021929040339030b0105120a 68
    0x520a01c03429500c064041c2881c004417400b01c0c494284031041e0000300221035001c2e41c5050b07481405280458407080c0303541c0c221400c10780300400d007000a2072000c041c0344110383c040603c03c640406d041c0400305d5600201d110041c02e6507003a8010f00c0c20800396030780f028032480c48290b00040020f51034aa42c1041c950f14040ea680003074100344006040c68800e50000080d50498042d0789084c4140542400d410405207683c0c070004200207a6000103000c624002c58030306c0320800007842142c1c2c281e0f03504d552000544400081c0c03050a65521103036510801c81d142003103d5003100995205142540040a0301d948850082001c070411070080750a000000141011898a05404809008054071100211035426504100701c1c4101041d44042c100c0c40c08130304a40007140c00908082c40d44108805c0011f03041e04460b000c1c010103240411000c0000f522031200c250005000400c8054403400c890203541e0a44201c0150115800700c0400402c0010810740c9003605517401518004030803070413504a51300d01900071800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 854746258 1250 854745008 854745011
    0x31603050702041802150c0c1c0b1611030304020a090e0a06050408030a05010e041110141c0e12032406070302010b010e011d06092b12080c0d110d 64
    0x3919410b0344c0312100c0c41c0b40a4000c8072041c1d01c400c100800c0142e58402d90009403055000000d03228090320307010050306a0304400c003000040340d008544e01c03002001d4084500c1480485498540700e22b182e48460b240d40d0101c1214021451030406800146014859100c2d8181e61604c030b840441d5001410310910591710380c007003030500c481d0806280c6845107400c21290012128a090f00001e9829211541c09000303030303081244040103c003444144001c010020441605002a102d640c05869441c0401800480089549031551001c3d071255141034a020030b031002a560b1206040d6455030071101c0031603070043c410711900130402072504480c18004100f414100d0788454045810b50034142c041d005044805000d0361102c40b20300100c8015118001c00b4046092118105da800e00743c0303410404005c0103110402000700c41003000085624204420b84100c201c038220310340e500b080401040751080e6400382204c3c2071402d41858110401c0d14039000f010440c0c1c540e0383e2100015102414244100d600e20310b14074030b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 854747508 1250 854746258 854746271
    0x901050a18081308030f0406020c0906092a0a050702100e100806010e04060602151b090d1106030403020f0d030203010e1513052e0b0a080c12010f030204050f0903160305070204 77
    0x21081b40381c2e0400d1103490054000c40c0380040f103d1904074480c511800c0028100c800e01d0303c030705451603490035050100100240343c2c2c070b003ca1400c1000d1405001031000310380c1c0d040e941e0441c910500203803690840c450700901900030500c201c0d580d5000d442c803102d22a185021710290f501c01004039502c0612413003030341d0824500000420f02590100b41c103002e0f0300012110542c80c1d150034071981c01a01403908a801d0700e03c010312403d24a46810358511507181e005100a0104501034030004d003d9500958040300582d0040091501c02202841610b000b45a241021130556240c1391164015841c020600d4580d043e8040b2550116966003410702a00900441304011500d410340c510300710000c51540030041320500a4055030390700124000c80007551910b420079810107d0b601e009449559020306440044081842500c0314040103040742d5000300110030f00300490915500500040301d801516421508807008100451085d00000301c2d8a420003164180f5003060140c00e040701c40d0f008088000f0f40c010305200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 854748758 1250 854747508 854747527
    0xa030309060f0f0504091505090f060a1202030627010903030c0306080307080409090c030f051c0302070b0610020307051f110c250306140901050a1808130803 69
    0x11020309a4415458034211101114400c0c0c032610100c004100005604100501601034250840882140b60090181e90240c560000030443c2c90121000c1281200d14804c01c001c40c50f1412015009107540e0100910350304887d008243c440300002c0c400d00348068100b000d0102416051080400448900000c0013280c1d000c0ca002800b90181d5000039001a04100c004680761001100319101076a000a00d03d1400e8902107284010340300458040d240b05913140d000002240e00040b008010742e00c90300103000c1c55840d420704182503024800d890000c240c4103121907000074800700714023a00030400f00c5106241209800f01240f0f540f0074048010098080c09218030301c80321041004140003883c07a40144211405500c0800e00341c080c0c04003400c460f50142039102090164400005c201030401e10441d01c440d5184e4503000700b40d400c0213020049400011042040c01c850038469940c205181900070b0115201d190b90440d80d4662850000d0711400740019621311000d0b820056400400c0e040e4180c03522215181c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 854750008 1250 854748758 854748767
    0x2160b040c0303020f0c01051206041d0d1404050f1210150305070902030f070806010c060c0c020a050f030c04050c07050f1c021f02090301091b18050601200c0a0303 72
    0x5102c118094850404007490203480400d0b040c40449041e0f4601d0b0400305051a81c2c20941e402038850780e000f658880c100071f8850f101c003288604180c0110010f220307040714050010202e981141498404800c14402800503a070703a010410400c450868035071542e0781c09607003103a042414800646407028908800790200c1078400036210b007103074084c1e0f098a46480d03950a41070103034030088a00310103880b9243c00207200280550001c075040038040c03408103060483e03035a1700012588a22403140100f8045d000c240e0451901c08280d2020300b40541d00094041481404246d0300d40142c0c0e0000e200d1034441e4001060804103500380e80d100c0c4d4100d012544200c146004a90312080ea071444509080500210003004a00004480704101030103c000e580c00040d2100c4040250404042240d0554960241901003501060038009100d0140192201c0c2480c00004403003032004d060300d80c1c105504041c00c20045130381061010b0032056581245d5641d40124103c8142800032483d5010342c030012040c804420706900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 854751258 1250 854750008 854750033
    0x50a06030b060f010c0b0711010510140d03020d03090843120503040312050a0b0a0806090a02010e150c0d0801061b1518060e070b04140402160b04 64
    0xc0c1d000311409446410074480300d440c4222115001c5800340e0001000150083e00459104100703151205c0822164140113094a40a4078505103082d084002848002d8004403c3d140102044803550704007006654081e4032000b07645000801c0c180d4900e10b02c01840303501d1084903061245414443e132186101e01c404a180016091606815018265002c0b81d00c00d01102c0410216000603110384140c007020011202e03039200500440400c041e160000e400800c05000d07590251255070b501240e139003084401e00070002d00d650300011059000405001c250b21000c02c46c6882580c0a2810340c0c00c0c4495140407891003650360401c1c00c41c0c2480051000303030f03010012545100746c103145d90703510501d0f90f0f0b00c2d801180c800d5015101e41c20500001140e00e00016682c000000c64403040010214695241c00700a01d43d821301e0043c04c2d50036648070440f443c02c003442800004040e0030001c007000d06180c2050300500503500510344040c00303140d00151101c4000c42e10064110762683c0a90100c10914080c41c0100b440c0d0706 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 854752508 1250 854751258 854751263
    0x60a050307151b0b01090c11011401141009050405060f18040201030524010c14010905030408010e030406230915070506070525210207030b0603030406091e09050a0603 73
    0x541c03c2c00e0f5103007450284881c450706500104c01e02c581c1d908050041c0000c26040ca03600c070621100c7c0d4941c211450080c083c50808454640e5061002c1d0b140c0303104110002078107440345210f00c0203c2c40320b60603150441c0802c801e8403015a4001020358a00000c620440345202005900c424919100c25940e1045102544601d10030798040c001c41d140d0b440c038203034044989101d242d00400e203107400035029441910001600350045080241310903e05d020f8070300310b170481d04003a1a95040010144845107090250459002182c0c0085141c11314008000701402006900082c5d107000036001e0301c0b0342c242014151081040b0003040c840040304a81d0547c48a5801110116068056400040d000307a008005540d404400000f078540581003100c1d01d025032a0b0ba00d5401c9455888a001c121f19112010400c50109802ca40041c01d106041d800c240c804c555000340001c2c441e600c200030030b0007072a078000800b000f224601c01c4007403014810003c030510403461a40003021128544010443c10810541042044031b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 854753758 1250 854752508 854752517
    0x90b0114010c020105162604031b082d030d1e0902060a0e06071e14070503070905040503190203040501090605031510051e070210110703030305060a05030715 69
    0x35880041d281c01c1111180680450002c0c443ca510305000d0022400d00580304140b51401008500700809a030949803009100d6601d010600380104880d000f10b1303600b80008500080d0139503141014060340c0b652025841011041e0b14182402d8128440d40c2c0061501c0441d401c0d01d46070680182c0420040034212820034070355110301002007825110b841600d94454000d402d052401d4480c06059508515041d4640d070421801c000032000f084003c0e0200b40d4a826220aa030550801c80c1406507840f07040f2019080f00d604800000c001035540010203c045030f007811408503440d92241082811030060707119480401900001900c1e10640c00300082003a24004d0b20b0740440d858843c4c4044415000840d0442c0b0a00e105041c502181d103054002d1404021103868201e00d0107e0041591034490000400c0001c0d0810100d1410214580031413100189000ca280849400003091001a07803030720644405020715554070042041c0b5200c417178010018040190071a0b40762903490310304015a4007222066800034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 854755008 1250 854753758 854753789
    0xf041e15050423071703040b0403050114100e06090a02071e0b09070b030c07170a090f0b0f090d0302010b151e0903070312092102090c0322020a0504090b01 68
    0x520f200d988400b402541c140c01090000d050140d1a50303044155514030780035100c28440040c24003140740003030004d144500000f0550600800d031140d004d02c4c019003012582c05680301c00703021030f158040303020381c1c0500b08598900301e585a541034440203200d01031000d42004d81d1503c1042070040000d41c0d122250340705410400705035079203855a5846051600071030301180003c0000c52044130400c800f9203000c901034a040e12110303000710141c01e4a07a1003079110001142c500c0300700300501e040c0e030318251008200c00d8040b58545007051044000603c1103d41c4076204550040e10b00c02814800d500c0340340e45004c0501240a5000404070616494002c43c07400254520030004000b40302902c00b0603144407250140041c403a00d411680d40c0c444006112941008001c00c403000051180c002c10300e01580030455814025202020740107016136a100100981d031205020014418009000d142859590278086c00500e042e1480c0d1000400300b00c101d60001e47d015003050ba02a041c8190440c03413030304a600210004045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 854756258 1250 854755008 854755043
    0x3020c030102030636070908010c080709030201031802040501180609110417100f020702040e1b060a020c0907050301081506060f281e080f041e150504 66
    0x280e21049911315000030194140021040041102c682c90f80300c0e151020f072849072134284a20340c0100032600000012080c050410482d03400303102c1d5806035812071a002e0094900341c00041c0401000f803100a040540c0c0700c0851541a03101d03480020074503401003007401310756900c00c4d4140440c1814107900200500e800400120040701d8441c003c2c01c82d40d11708601d07040904e420700042009281e5000000507000d01103060721030422610510a950151500068644c2d05600500c422100c04040752440343e44041c3e14120700402c4450b4041413144120b5003641d4640741c602089052207181c041c0340c0d0b048903903002444503441d0458080d6059030038000c215041c01c0000320000e030028001317403a6190044800c00804d81609050801013860f5601500030300020038801c040d65001c5440711000030001102c03842c0c2050900d924000d03848410603503103004812420600c00e008400c1801801c0145517260198955400c01020410501c0c0603400215401284401172310740c0d809007100b103400710b507084800f0720718181 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 854757508 1250 854756258 854756261
    0x10816050a050f0d15090506010303090e09100c0306090204030b09060603070614090a1d0f0a09031b0c180e100c0c0f031b050705040f0b1e0a05090405010903020c0301 73
    0x440d50002d00c0c0800303041e00b407018800a00585042555400121075200002561901618030587e03c03820003001c00d036145040060140c220b0380c2001180c0303d40c80301480745600c00020421880f40f102400080c2c0e08010340c10507001050300e07921101c040c07800458000700b0301c000d11410380e02c1040315000f070314200d585000c105900c0796590b004a4011890388150141c4900265001d082624806041c0800080d12802031080b00300e451f4451400c14001c00301004548005040080e400503641a0306110183d040d0390042c0ca00308022280300e00c450300d6400f1020501c0b0301c020148009002c240035000084140c07c6154024201180100440303104564034601440d00c1d44c41001803024580e503628901e0407582d9a83d81c20960b0240050741000320241c02c10711500d2840094125070781c4140024103039103140c80148401d0f502800c0d50400c50b04e2030131114140c10b480318001c2006449064111201000546c07001403542d0340c00703412003a00540108100810494154025501c3d54029001c491540c42440205070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 854758758 1250 854757508 854757529
    0x20405031504120302071b090203060f010806030a020405041104110408071a0f0c0f0f01061409090706080709090c090305060f0121060209090f0f0106021c0509040b03010501081605 79
    0x3d001e0b0b003403103181e888160310940c090100c403031013000e1b0110005070051440403012450b410110034554004140030309880d15603035003116400282015041490f142000a4a8036840a80a409140c8403c002802c00c8910211074000c0038000703004204081d906c4801e485503801038019071805100d9810085180c0a04601c542d400c558000c843c50f240114032080e020041c0c009805008180c41a92a2480755003824005452010b100d4000003c04514101c2401000b00c8010720980c0103040c4101441001c00010500000f650441c4c00c11107155140c0e10002c45101c0f003103034428030f9418903204c03010521513405404402182d0042d030440d06191104003025068010a01c20726030180404400d00700500b180c50080301e00c540c021100141400010780c041a1440702c12600000148c0240041008480c14420700902405a510041c691640b00d041c0c5042104e2024034250140400840e8425065403540c1000607a0340c409070080c801542d4174894656075455200103009103a9400302e001c01c1c203052008418 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 854760008 1250 854758758 854758763
    0x20301051e0d02041d070f05090a0209010207150c06060803090d06051f030f120c050d031a130b09010512070306110c0303070503010303120203060918030418020405031504 75
    0xc0c1c6155800c0e14100103035200340c5409820210702010803001d80d40c0c0e40301d24035841c1c5501c01030030f00c034000704210b036400c29400f6000522001410303a42446a902c6040e62a988145103039001651800d0b00700042c5c1c40d04009500140e58101c0398100549039a60140200001d24840c1d40140314080e11111040e4603400b4000700c0e990891901500e80c000700b840342d004284c00000b01706040c0e5450b140b4004968100c4c41d19001139405521403008141000010001160160030910b40b1306540f2103103076a11511100c1e5400004201901c1c0c4132006100100040380014a000007458178009480c12005440500f044d0b2400501c2035031054000212810080030704800f80d941c1030090309181d411540d4034002401600c5100c110b140c070a200c40c0c05201d40410003180221010385415450b5859841c1c020300104c06404211451070041c802c1c0f01c013503220301039001e421001440c1d52110180c0c01c0c03401c03240f850141c2d602c20102024090700044014515600502c00c3ea10180d0641e4080020045049071300a002d9500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 854761258 1250 854760008 854760019
    0x5010e1b0414150922080c060a0c050708031b0712090806061315080322270504050c190509100335030c120612073b06010906020102030105 61
    0x343c41107450002c80c4a54000303600d003403510100c0316148003030312291082182140c044800054050111408002171503003c013038140c0610041f10f048100508500500100500c21880403001c0340b80d8440004181d449041a24103843d1201c085042c010304102d482581c26020403025940403403118001b0420501c00c802c0a49245480b0b030070458000d000f06543c0754040078008481d840802c00e0003003070005000407e0300c0103a02c80200780b481c0c4201522021544078035443c1440308000300c680c24220000611504c0300610014055449003040c03400d000580e000d0301d91282107458281c40048039180d842c030955001765140c0155643d19002540082d4142c0000b801c01502d4910300204c4190b600b1040700a00c05004400d90002c20311040c40c85290004d8070200c4e441c10000c1089061120641c500700e504c0001101c1104075038044000c0151903156038000c41710f040c041031010301c3d100d8213941d054041941020003010101b04001d89200c0032490140c4000b40060b50860b0b001907010320500030760b410386800405 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 854762508 1250 854761258 854761291
    0xf121505090f0c2d0a08010303090e0124020c040e1b030c0604030209060612010305101118060904110d02071b14060304150c09030c05010306080709050405010e1b0414 73
    0x1080502141c000703246200c101180c0c401944201c0383c2d84c00b6000411040e100c40341c8035411807501800600e8650030024902c88880010065130801c0084031400c003540c294074841e5003a003084224100000d1b6411582c1080c20240c2d8854502400248850902c03076070301410404281d090308043e00c40d0f0240e0750b01948180140014400b62821140003500200010f00c1076240408107034505111074026030068601c0e4001065403000c683c2d403402999000440b110340c00d46009225195424100d9080c0400c5020700408281800541c8450388000c0078402030304c0005132500e4907000c024019511031101140c04d091178000010b0010581d04418058520140407420842207440c140502504001e105555182d5410f036840caa01125128221102006595048051f8103600303240450910342c1d44141e04141c40c04500704100c403404078010050300c58080f0b02042e20b0b196424064098610100c140860b405003000810302001403d07419017a00800761313018810241c0b5035441d920040012580c3c04000c503072004c1c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 854763758 1250 854762508 854762527
    0x3060b04052119060b062d0405040905010e070b0903070303052116111c030b06190f08060303030411090717070509011d030a030f121505090f0c 63
    0x1021150100c10003070480c03002c001d00109203841e2219640c11480c052041150000a2110354020b83e0002c182c2070b82c02e98078040b803241034000d8000c0f094940c1c1c03ca00d5a0440340c12810708801c0c080710000e09000b04180400d010b5030820a0090070492100036052055540c0014108119020b071980e0701002000f42c00302c3d41c0340d510700342c0b003c1d031051503184822250340140c11600705001134014000c0010006003d040a942c01016103501070708402d90708664061900045e0007011980310443c24030350740c030b8013080304425030380451381d980a00c0e1142d0303445401840c50302032030ba54817108112a86030581e0f6206101e4030380c2800c2c10303101c2c030040d00c0241c0340d0791400f91072640c2400c0c100c0303e05400c820245800001301b6400174410001c100b0681d02000003410009001b0007a42c0d000d0b2500546420300450b40301c0042c03000c1d00195680011540080501076508400344039107006200180c1c1c8003041c050103100b865082400c10501c0c500334050341c0e10030302d034030703c08207242651042429104103081d48076285080500d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 854765008 1250 854763758 854763769
    0xb0a030807030905040f0509010c1d010e0f04050403080601020d09120b0c0c010f0b010e030705102304060513060c03170a0e1902040e06070206010303051c0e0703060c03060b0405 78
    0xca4042d8140002040005219110340c401c02441002c903160010369424043c9015007034401c400b0080017040a03141255a50801000070207914090034200a41040980400301d000c1c5410004099485841c000402060507000b0040c00d2140c082642540d403038a01c040010b07a41c00345180103510002055114850002c0c0446c06c01c99000480300310741c00d09180d00d05800c00d003902c98141c4443c4981d51584140c10301540c00c4100750f604071508402034141c0c81d0410300405c4141c5100880c0f00200300c0000d1b08541728030703240420509030619030362460396030341c1d183e41c4081c066034004016592420400240000c06903c20b80407100619859030302d084070700404849002615201801c14282a9a500000301f5075086c20020704030030045902e45c04001003981d00400c4125451440305602640102c4100220642e01044040c1940d5041c03c000c0e48031914141c006807010708801701081010314010403440a02400103403002101e12038601407286640c801401c909641040c890310426500500c018051841d04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 854766258 1250 854765008 854765017
    0x1f0e04140103060c1b11010309120306091107021e01030902100e1309050c101b0605150d0c0603020f0706060803090a0b0c1e010e0d05120f010e040b06010c1b0e01090b0a0308 76
    0x14900861041d80a032103618045220f42b00c60008a50307691410400000035004046001000c806414100905500801c02319003007000d500c0c104a00d03074610001c440c1c1c02544140310881d0044c0188940818814000d800d061800300414802d107804d00741c00d242024640503180c48198400041d051010f6030f8001c0c04042c1e460100c4807400c0c0070805040c220494107402e00034036020f0003803030082205e050081050442c1d10710350b607116000d40d10744825400810300310078160382100c05d0b914006940d84080c46d031504d854082d20800038003050402c0e20028003000000007030a211401101d5010f40300ea90b528a4000612824000b102e442d0003211800300e00c1c5c01481c010440500c017260020441411030307061582031052000714007000c24004158a0840d0419120003a8400e6103440194210350400e440c01c0d00303021006200824004600340014481d911a000c500c1c081d6038401100320312840180f040c9429400c06019104100001324000200a1040c0c042c1d0b00c0d1102c3e019010805050441c0c8410b10950b00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 854767508 1250 854766258 854766293
    0x504140d14160504020c1f020f0d0c110106050f010c0201051c060314010b090c0c0f0d20150112050f07060e0f010c021f0e04140103060c1b 61
    0xa40c4208000c03501c81040480340350202000b400005003100d251144881250b0082405148180001240d5030000503007510001e40e4454100d101038600154103029100e0500412682800406c182525090079004030043d02241d4440140c540e410010560885000d4411503a001c2c14001d038600a5502034441b0210060061401d549080380e404054000b42280c401041c41066450400700180260702c030040700805c50950092041c0c107076000020b107140740c001d032440700310b4940042d0000d04035100700f0114991600c1c03803003601c114586483d40940f4203114400da1503045540848480c0d02c0a4000c40c4010600e001c1c1e21102c1c4443e400e16407110900c010b54001158035204442d03401c3e949a00412899000382103039518071405100c054140810804050407460610002d07035140300042c0d4400341e1744051040c0c410400007007160841001c07500e26030855203d541252a103010b20882c03248001c0c8403410703240036030410302c20540c100b64100c0d00c9101103c0043c82d844195000320b00050154901c0240b120b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 854768758 1250 854767508 854767519
    0xf11070513021201140f01080c040b0a0c06050a240e19141f0b0a0203180418031e09030b1801140f07090f0b090d0f1e1406040201050414 60
    0x81590303d10a06008085e013011300344c0302044000c2025407401001d500442c080a02c0d10701001e042c0000d18095a0050f0302070342401103004200c2200c0c585c410594a03040c0364000c54203002d81e0404040d440002e00d0303884034940d84044e0000a41c490b480e8a03200c05001c44d524034249071165a039412000501ca502d40c0100c02135641c40710544000c00c20f0702448140120f50300c0c1c0d013084200b03019210107520401360b0790001200820900000317005c19004001d5800742d80c2260480c156840002e0b0003c0d0043c0010718a658152100d50b900d541410380c84000c00c001110350340400e2a044980b108241c03441c240d540b0004020144110000303032803102d164400300e4032048003000807681041444507425003220442d00c4940f240008410440740503403041d20403004080c0c0400801c12a07042c5440c41c649486880500ba0091074800301c000c00b00500304a2000c1095000010a0151135044680016021180c142980c884c940501d0003403002c5c50104005004aa05031111840c1510305605003013132101800840ea80003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 854770008 1250 854768758 854768767
    0x30f150a020d021306170105010903080c0a150608010e0309060304020d05100c0309150c050d02071a07030e1006050a2c19060b12010306151707060f1107051302 70
    0xc195001504801e00b211803013200c12800c1c600010001300001c03620021001c0e00100400c801d9030003031a40b105494112400b43da4031900030714403900d48025a00300070410706c2188507400c8010f1155010000341e80c454002400045803140c9402d0f5a401140c01056101004002040062600c3d1030820000b52003003040e24100755a031165001102c01c07400e501000b10b030721213240e101044128004208504180c100801600c03891010052050160450382e003000e541c0010b1110600103840f8020351001007242d41d10402c1c0c034003c68000e0140a03550315a00052098001c2200c40070b45c1402110700b0355501400c2c0342060707498198882004500542030b000701502c4500600080000c58480d5445141c0c49003203002c4100240780e0910440d03d0542c00800061400c0c0148413104400c6212181160b801c0207001c10250440b5881702040040d030380c00040080030401100b26004004218a800c403401d0741c82d00090548641c03029184004403802e100320327540002009000c14a8a440ca503100341d844007a005082 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 854771258 1250 854770008 854770027
    0x2208030301140f04020316030e0a05070b0d27030c030e09070905090a0603170705011104170105070f020a121407060e0105060d05070611160b090906030f150a02 70
    0x1503500c2038025004400c141a0340a803282005601071000c900262004c5156150800038888450303005502c0b0340402d0f440e400302c02c0078618104428101d1640000035240283e07511a0500b0f11507000f11814100181010f0040340d10222241c82c10324030b43e100a0001c403c0e5589682d04450b85070690b0070403414800e03080207440f550303210428101d21650b1b0a8461060705410300003082441400140b62500c42800c0802c20300008111022030301c0354184e4000e4207078442d043c0e860040c0c094002a020b0030004d034404100016900c20300d1078500c145940b001c008000301c0d01c41c00d01c116425100c50b84441c2c09680822020030000e0101c10300b89200801ea4909114150a200c9800e010f82c2d01024081e511a85c48541040441b0030038800c03d03420003c115084095006550b40741500c0740480e21802052142d10020121280d80078840c5404a01c904410607510b2510384c582503000790826551580034040310000941c003418000303108482c07041c03108000c0000861041030030304140802000801c11079024003000a9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 854772508 1250 854771258 854771263
    0x1807090608060403020f0d0522080102030c120105012a150501081501290a0201091e060b0d0305390303090d2a050a051b011b082208 58
    0x180c01c040014080c1c03414141002407034200c0f0400300c0034258218400c0c4480d9207820904450020361000752000008401e100e0f03d01c020300e0150302034125075000008000034554040c004050b0700364003000000c104d90f254801141d80c001600b60f1110745188008485000c401c880d2101d2030781d80e100f480b0204154240482c0710090b0756082e80f008050740d000c0c48000000301c030606045409007041c03042a01031901d00741c60080901141c44a4101e81140009900440c030b4401e40102a0700c581100d07042e08101640c0d41071004000080000340c841c80c0c81c101e41c0054134541800c6c46030209800da540c550500084040e01d4212040b0525a269441c1c2108150000c6801030b03184241404041005162a032806000042c04d002111992a04201106100d0b408440044400c0080149042d0800762043d8203850014940414120050040c2c400c8441c0c80308014140445940000c00a03a1903c0b00c10f954410f00c0400780000070801041d41c8014807901030310400211401c1110b120346030380c1a5000d590740304800e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 854773758 1250 854772508 854772521
    0x901021804052a0a1106060d020d080408160f06170403050901031d0601210c181d070f080d020c091f0801020406080c07020f0f0a0911040302040c05070b180709 70
    0x10340340f44082030149100d03410181c400b20301411280078181a03d0000006905011340c42c4001744204415075003801400305200c00d03900500064011268012400c00030002649540d204004185001c004042060ae2203500c00d403544041105030b00c840341e121980c1c15591030b000300d040c0030304169540c0c51100c000c030305c40720001201444a10141001c4d50620940c203085103221415004107500002681000900c070360000003c903049030146c1d0060032091995036001d0a20201c0c241150240380c1ca101105a1002c81c020049942e201031030225182c1e0303480d50944441178290041c015800030000b8540a0801d00301d2290304c6104d0001542d186130104542001082054000c800700b0b80d404201032140a800c0fa02003600200007207002c0d8285043c5a0004e4500c451840d641802500340b03400000d5a034441041280c054004803909000035956070039105850f400a2105900c42c07420703c1204030000707004808903600d507a004440d1401690355181c50800160100c2580007e51207008000101c2182c0ca00c03450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 854775008 1250 854773758 854773831
    0x51c020c0c240a05090a1208190201021204051f06050a030f02180f0a0b010806060d0f06180e010506190b030c0d0c0c142e020f03041109090102180405 66
    0x4c0d901c9024480034000c0e005202c1c0c01c10b1880c00501ca0025000c188800e09640300002c00e12401d00101c0c040001c1240603002c1c104401080920301c02c1400300b00301c0040703a2140070701c260899481d0004034100400e400c4d10700714070485420419080050012620150fa0820058005040c030b4295400f0a20f010b48070050450350384828820390800e11120145901030003040c0700c2c007480c0403811410a04002445440b400340300c2c0d55030702d1b61414580c403245200c2d0006001006c0066900d1826290022038502904d40e4808100955223040f00003a07142c54a00009103201c185c0d0281000500d091032041603440e400034000d1050340c0300602100031240702c0f5004070740c241c1c0019502c44001c4401c0c0e1401c5810500c0c2d0405000b8950011120755442c410880782142c0440c03611482850b04590710030600c002481000c41d54139101800000700002c1c4032110700c0d100040c810565484045903501340d14517080b0701848000c02840d052500d440b0040345041d4014a400070044462901c1e081080e00c8582544440700b04031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 854776258 1250 854775008 854775017
    0xc072f010e061306030501050a0909030f0f030e07060203040f29071505010306090b0105060a081f0305060a0506100903030c02190e070c02030f030c0712080403050706051c020c0c240a 80
    0x148207034240103007044000c0800340ad0034880d1815541d07010b4544086c41e81550708100c200c41c0003040b00340c4613401008012402c101030352022a00c0e840700a490358414011480aa00207040c00140040c001002401c0007444034813410b0030000c0c5400403405640030f8141030304e84030f04206280c40d9007032040c8940f500861251038001201741d4145014008404160302081c17003000305100d14008590840030b040d600c2000d01000c1c00d40c1303030720603000382884401d1a00302800301d10503902040703d883c0c42c5602c041d00502080b284900d480c21440800c032511a8070f40001000035210314910070041c00e001c6210303000143d40c1c004c0d0b80d0015480c0c0314103840c030040403109500020b1020304040d080d81030911a903c55000d2080c050740c44d081c10b03505090b5403000380b4818038040110f2041c01c407080c00a103d007070314065940201601c0e8001e0f6131302d00007015500720381e440749141c4c003841d03680707100c5501244200d03549480444058031514580c10104540518515803400075242e00000314a20350f01c0d4040100390328540350b1607 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 854777508 1250 854776258 854776261
    0x70e0a09200313021201110d0213290d0f11030a0623060c10020c0610090c1b030e040c0309030915092106050c072f010e0613060305 58
    0x11904030440c0701c803400501440e000c0083c071501510910402034003c2d010303201041c0c0e0000c0d40c40b0481c01030201c003880f003019200100d401031050006400a1000c010301450508507a504ca49421000c0300c41818803414144400b18152008018040601010081c024001950210114a0700251112490022041c800010030485540441d10401e030180c105c00c08800550300154002c84c50310701d008540e091052001040e90000f1890402000c04080b2622405540f55402c1c006600e6503a2802e65440700003000623000400c1c2c2c041c40d03100d04c0c5d40440e55540d5812034251181c420070b120326030309502a8200070b020013202040f501c3e94054110061a1503400041ca54142d081c010121420398000c0526035a222041c201107960000c0e0003000d0f1030a0071420a0100110340c00e0740740c0f007204560300420380c40c140002c00c8041544800504030050085203081881c0001c90070b100100740700d4114110a91090800340506035109905101500c10090419807a002180e01001c00396003c036400080001d44840 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 854778758 1250 854777508 854777531
    0x209100b07150e0105041e0c03320a08180303090d0b0105101701032301111c090c060e0a0306050f071407050307020f040612030c050601080d17070e0a09 67
    0x1003825045940340008200909207603444401e160047c503000d6403180e1151398224144079501141500540e448030405440758080c1c080104c024000e038080415084c03000c03090b802002800b2440403022507000d54001c1c6800140c1c205020b140f45645c40c0340b509840300b4840c1c070b58251180001c2d680c90074015040c040c00c9600d000b0400c9280394030102c1000800400390038200d070f458189402141900e5000c2281d1400801020103d900990a4088440e1541c20407607490000071107240108401c908007844102c401c05a00820f606483c0040c1d001409044119010886c1c24402c41c135a09126000030324414046540e920750300e05580003603c81500401c000810300c10801c1d0070048552004194480440c03d040154980c1c80d140d000c0e904d0041d0040c40c641148131100d0340c1c0d0340e10070380107400080d000411500c230b50705000300094041c05003152f0a2081c000040f900100005244110f1491903480180c0400c8440765040c00d964007510107000c2c4040c03850f000c03429648608881e006492140800075000d010030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 854780008 1250 854778758 854778761
    0x1008060907020706140f130b030114040b0f090601030e070801140a050705030c070201031b3b120f06180d0806010c030f0c020306010b1803010606020a0209100b0715 72
    0xd44080e00b5035110180c10404070360480002c922060386142500d881d030440c204801d9940c840c60a68000c0382050300740c0403804041c142c020303506030791220754107174540042d140600c001c0ba941d00f901250b10044a406008140c81d04214131940000d06141c003180c081c1c0c24124240c503090b11034000d03090a13519501194520320450400300c1d40a681c1c00424041ca0070710381405002888080d1200c0c5142c040000c0c42d100750390181c0c01002e48007a50384400d5041225000c00200710b000201440c40d00202d441c0c81d540030300135146050b00074106416401d07041840c04042007140b4a406800040200e000300c85821071120828000e0754450036040b800424541301f12030307a40e410205526110824012810207200f00c0b644e0003083c00201a0b0f040c100000416410241074840301c84401000354144607200002c2000c08904020f410200303c000c0b03650846508002c105400e03901d076030107440c0050744810300c51000b41ca003201301140c0000c12208007100d03d03500c60400442c5076021041c280d404a03d0045000040c40c5107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 854781258 1250 854780008 854780011
    0x204180e01060905161214130c03080703080114030109111011070303030606020d0503070c020906042009040b010801080d1413091a03010b010f030e0106080f010902030601120b040215040510080609 86
    0x21b4400c03c2000c07400600100306e080d4406440040c43e00040d14a10003000340780890310300a9902f08100940302d0003603140042052209010320161814441c00d89a00c60505000e003846a50307110360040d038aa01030206014481001500007000c100301c480350400244070070300503000030b10b00941c0e010030340300d00705003010345010030346003100b420404100200b240c1300340d00041000d24a54125140c180c10741310000000c0c060401418070000d0707501e0341030401d80c4011108004010b0781c41c050b5401d00215481d03000545400000340306a00641d04040d0200c242c141c40780a00150b0504a8001c0364244034400d0684100c1e814a9000554165903130b042504100385100d82042e00b41d14110000e00a0b034102e400001d00e4640500c24642c141030719890032041c800804e400040145c20404110352145500115031400380281e114242d01a0044c0000800c181541000320301070660003140625084c1c4442d420f01800000c0181a1203103000c0030b00012415644152240c06d40c00390390b03687c0741d1450a24404001e00480c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 854782508 1250 854781258 854781287
    0x1060512060f0a021207030504021908030f0a020a140c091312030c030b04090f1b0b0301140105070618060501080609100b040e060c0d060503010204180e0106090516 72
    0x4094958004101001075016400040c402c0c25000d180c82d040f100303902034050f00c036002c001a200d02c010045640d505a00007845075000f120318010b24580b148040c2c42d441218090b4091580081201200d1200380c0c40080442171447d20444500c00840c1c1c4812500c2c18a41d0140c031016005404071016600e050300742c00750881c01179200745405004990f10760b0380480541030308500341516403801d4a0154043d512402c030a04019005000c4e40c1001d00d065413001c3c0d041d18085034400307400d10554202881c84040507041e00c100a640354656402d140700701c07080100040e0030382d042100411004000541c580541134140c00300d65410700c0004001d181a00c1035480581203421903511500c00c110b01c1450001d11480130700800480016140c80310300100c0c0142c00d442c0300b468001e2040310f003440b902d261004010f00b021903000c1c0040044030b03100d1040509071306c102e10032100e242c540b080c0094603007038066008142000d806000010b4207a52000d120b42681e40c01c0b10b20141c0d008446100b50050758100c0703000c880c0c400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 854783758 1250 854782508 854782519
    0x142506110106180504030e0a1202011202041214030403150b030c041109040b030708031908090607020307032007180f0902091b0f0f0d0e0c0d03080901091e05010605 72
    0x5003001c04035030541d011808040c2d0304513100d0f40400c041c14010400d4500100d005400031b503003103889050035241209010022800140e09104031004617030a4400d6405407480f02d111403400112684983c07030128000d051000e11030008100000000e21101e03500400050607890106044002da0304040c00c24014031215030040e402d100f0b041d01c00311140380403121030781001c80b4000b0788440c0c450003003491300c000f0360000e070410300c000100c120300385904110130104840256203a20095842c0c0c040f80c1d803121016191440964428895440001d00a02e01013603119180200e80106816640b8030300e01e8002a030344445611030030013a0a501c07030394450040e107003d13031682d00c000c1c0040200782e4081901114014003518805226000208210303219000b100d259116155400d030f100c1280c00800c01459110400342e9103903034a003604c0e41a0901000c280300d0526000184a02040d9007261001d60340c03114003e01200f1301d5583c91507988001106205003100d10702c001003420501070310a280a40c04c40700d4a8100e81c1c880c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 854785008 1250 854783758 854783771
    0x403020f15061002061b030901020c0723030d12020306011b0f06050a1416090f030803060f0d0312150503120c151006140d02040803070302011b0c1425061101 69
    0x64080c803199503e208006d840080e583ea54180c401d0b80240656498000c080c000c4400000300000217607103105240e801c0341d4900c3c03e030041d40000c255898030103900280104880381c1024100003003a60186500007018102048102142161684802000c40b0f040300e0500443c4e0028050000600c10b9a41c03010b00382d241081244154a900d4a0030840105080101d0340d181d151818150f00c03c191020042c03036140c2442050940301d24003444036400454089002e01c1081a60070480d142c180015081240c154903a89181d0501003883c0c0e01605100b1104032000e07007560000503c90700d040080039041c10804400035103980c0d148100d83e00740743e55131040115081d5200144058100d040c49a002150154280522020f01b8410300000b0ba024080303044071081c2c80800d0003e4205400300c000c0034404c0c400e9000b0400f41803815918442d801c1c4043c11130001507909000e243c0012100c1d8041c44402180d0f80403114104038003440c500c030b40140e154008200c0096070307100300b00c4a600925035200b20b581c5036000b80b000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 854786258 1250 854785008 854785021
    0x12020a2313030b060d0803180c010903080d051819050c1512040c21260f0711040e071d010b0d02181518010809030306090403020f1506100206 62
    0x45060a0001900064003003011400c00c5e90340c064480f10850340000115103e191402c9069004207030110038a20070300036000b0000b0341d0b622654001040c0ca900c40140703418076240c0e24004000b020006d04a0402e010700c210004032480080012020701c1c851075180d45440b001505e4802c0c146100c01807401d000c0c54412280e04c01c0003041c00f040d620754040c080c903925440e0f5242d040152244000384d0041c000e510307400e5405050041032801c034000d034a0089001a5004c00c10b00304010607c03a01841800d440e4005200d850f80c8400341c5401007680301e000b00c1e00d042c0e041342c660001038100e903083c00300e80880f40d000320380400404d415049407090134140285003038a07a42c50301705e0800c03551188608465200e540041d903410a0314290724454101380b400780003420350402100088003594401c0c0421043c10001400301c100c2c3d90b1087c00b215108002d504003850858075960305001345808003030412000d40c000c10703217459000c401c20403001e0101c403a502d0720142d2a040038000c1c800c1c00ca0b000c155540445d0411400c2140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 854787508 1250 854786258 854786287
    0x3060109150b0906030103080702190305060f0c0a090630060512060c0901030902040908190e0609010905090a020708193504050708030c01150f030b0406050712020a23 73
    0x11030742c218451950310307278152002074445400c1c03410607801c003510140c012050110006442c0e1045610940c540120b448526210605000740d030034120025122500034003000d03104900e1303001e04444401403c110342c0103100f04107180e200d440c000308410b2507582100300243d140080038070070703029a1480035003030328100041800d22502c90510ba09050548901480c002c40d11a40e00c0350250360340107148140c8600f1000100c0d556469480c040ca400a41a108407101711700c0c002045031800c040585034800401d1504091200c00c641c01824100308550900402c0d021480c1c1e0703030040458440b400b1041c2078000c5070080181c005200710b80c0c6d0881d0820181c0d07100f489408804200154040b4400460459a4441c0b522a2415480c1d0b04a445240004a003a4060407815003000200034400d6400d58500c985440c1a182076601c076200142c14041d524000c40d0108805500c03998004c01d10f40f404450104690b4440ca099034003a10013400002d191030a4408401d103403a5000c1c1454070300e251030600d4082c0d41e002182 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 854788758 1250 854787508 854787511
    0x30c110a2a061e21090507091406040606181208040504060b340f1103191e0206040303120209030a0309060f0804120e010e2116031a04060b03060109150b090603 70
    0x1469a078001d045c0510004210301710003825400c00c24410180444102e0582c401d064940c1c1e8041c1e070400c440403802c1401161940d603441800d04014038050f1038a1240c01c98415004015102c0c90030420021039652101d0107000c01400074694050b9032100107581d00e1909080c00c00003010280810009030811000c0c1e444403020290b0480b2041d0701025050403c0c10070041c1c82c4018642c1072044e000f00d0203504000c0d003800c103515400346107504207410306840d9112400481401c02548120100421b0001030700810034500916681c0000504145103500881e2401130380c1d082c01e401045070036004008030b541c4180d000801002e1450300c0411403c0030b0b51a504140c80c0b40580e08140241c003800503507103034410406014200b600905100d0340003403440900d8180c010500f00d143c8280500e1949a84030810b803403101d0203c982c80040300c502c03400c0040c590803807600c024000b00c500070345516910700141c1d8100041406004400c10009800d204142011010000c50380301070b071000400e206030301c00342d070387c0c80700b0b99 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 854790008 1250 854788758 854788817
    0xa020705060d1803030f0c020303010506090d0507180203100602191106090409120e0603450d0810030203060604020304080c060108030a030c110a2a061e 67
    0x880d2241d02c1c41c00100040d00d8104102429800d0108080080c140d060304240d000e00c40400040204484c0309408036280c2c0b00900800e0b811400405c010700ca203003020b1005e440a01e0145c004d070b46115072511007030f4100c1c004007002007211a0300802481250183c01101000521050004050003281403c29261300034000501420303803006040e008030203441340005c5500c04480104204441d40042c45d1007803100290b0a441d20001d4140701c4050000d090a0040b00d0085003c2c0803000c140c1c001002d0410005039544100000c00c0804085010031904c081c004207100b011510041c013017003039030b96070000c0800500520110550301c480c2c5040000d61000b0460f150000c905440c003680d03da5540c20b000d0f5080c840c64042600c1c0b842a07500002d01c480022014060b440290381d000d0015000104040b40c0441c02c02d44d40d03050036005400d0b03000c005039030384540d4180c913a0000081112001c012510201410a035404100032442c0800b859880220040c0040c0004419003007000d20103051140d901650030340100030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 854791258 1250 854790008 854790019
    0x1106180a050d0f231f0e0105041e022b02040e060717130f050d080703050c030a0f14161b0b0601111216021f02060c0a09031e170a020705 60
    0xb000b1300180d8203596400c00c4404040b6412407400c50f02d03101c1c0500442c0300c0d0480e01c0f45801880941403006010ba203008580000c200205030000c010b20840580d42c0107001c07644603554400c40603038040200ea582074944020800c3c0611006907005100035150307012843d40168000c181086649504014240050600c3c01f101007080e41c2d801008103140083d21001400c0410540c180e0020000001090502e095603541c0b407126039100c0e103109606540040e00d0b80d50710144103000107124214950b0004180c1e080700c400110305409200d1180c0000f400039604401204a2100c100807002d41204009420030280c80c40e0321110000c0d5142c110308080050040c60401c001e02d0941c4800e001c0401c0154010342010200942e07840200da0000d0410440060881c0035841c19080c8400981d010418403194918039005803c6a40c0d641e60417100d542c1c004103891060101d064004000318444585508030000019400300c04410710f030904c8603002d00308141c07081c0000c100300010700c402e550202e50031703003101d200b07564 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 854792508 1250 854791258 854791283
    0x311180c0f090102120d021b010912210510050f1c0204182001140a0801030b060d080c0d020f0d0e0105092e0e01020a0c0b071106180a050d0f 62
    0x105c0c1403c00e0003580440d40e6a01003801140c0c004198010325009800d9031040c203c0c80d410042a500381c0340c003074802618040d5079000001d0070b00d0142006010032980540806d4102c00c007028180103c40007915001300140301e8210a0020b030030814420340c5007803411240e00d2801103c090203c00c400c40c110f14000d010b01c1d216002e000195604e41c10104020f60301400d0a11540081c0c0450751800022909050010b20038003003010002c24100c0031520f6922051356181050782c01d548849240401c090181d50704244002e2003800800c03c3d1001070140c0034050009003141014010000385804942c501080d8650880c55154460366040048925000300a092854440d800100042d0450070030820070030181810704000c0641200c802130f02020b0f4079681c1c03150000d00c1040c900481e1758501c0040c2c000d1140505000503c010b45000020308a0300384104020f440b003562040200c1c4481d04000310380e11004068503103481d41403500c50150320107804d0544411200c10105e490f5410755120071040a80b4030303841c0b182d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 854793758 1250 854792508 854792527
    0x10f02121603050f07050105040b0f040201051e16050f1501050604060f0c06021603020d032d020c03070302070315090308180106030212030405010306080f0607050f07020a0311180c0f 80
    0x80549034660002040b141c0c861199046c5940604801c98007210140d00c110001919921840368050040350180d4586090066008041c0c80c0c9008d6200d80c54203050041c8280070201c017100d2030389104030380b0500241140007502d101207413400c150040d6595152140b680140410784420081d1802c440503451b0250051a030400240c40c10305a80c003002d07001c60700020f00802c001c40c0c82076902a186200f542100d860b901402404c4085501d0175010b00c841c02a21448040b041d0030980340b1420001800000525003004103401618550107003600314003580020104000f8070103400b9503520003644280090246500d2503400070b100b10710090241d49000d483c0c11942c01598001d50041c07015550251200c000c00c0003000c8070540e0303a005841440e0003c2d00304400841c0c00d010208584104002e07050013400603485102d0246c1d4103402000446680c0340d020300c40b00f4056a9035000f02d00003140690a01d6407600c040c0028050f83c0c013000c607038600d4101c0d4600e05111884880c07500300c8980c04038858038251500e0445 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 854795008 1250 854793758 854793767
    0x170703110f120711100e0c0316060206091b060d0b032e06080d1b0c0b0306100f02061b070821070c08040e0703060e090a02010f02121603 60
    0x4851840034810118284620400e0310000381042c0c594440012041c0c1e840100c11914058003003107520240e00324004039400760301c2c20b07041003072400510340c1550b003960b6a4a0110345012405000840181c848074401c210140d010b000d81d40d0484020406040004020210303540311610303180080340074060005411350311451300d520802c0008802400d0b90305100300140d0420003003c2d01013250307040c00000700780c070301d100070052190300111031030200a0000d1210031a41601c0c2410982c43e280d5a80340c0c541e011130009409200d004001d003c450b24916240e04200091101820b501001c0b1014030140700300641c8403070380004145901246e9100082c07003500001e440500b882c0140310004103019404143c0c83c14100c02d802c0341d40707669402800154180d0703844c500c080715801c03034004025184a404000034001a5005803071103601413040e0801041055444c00800500c05040341c0d03989a07600400d112004660780181d400e80000d10601c003c0589080807035070104148035820341c02c082e042481101000700b6008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 854796258 1250 854795008 854795021
    0x15090c0e03060412090b040b0723030c0d0801090e0604060b060c070f060f03020403030e2101020708030f09150a050903070b01060e1302090a06050d0b091008190308040311011401060c0c050d03170703 87
    0x441041d030f03440d80445d10406644908050703400f00414031034000401d0d04401032040548800b0380c20028100e58a40d9100d1500a0000b020b4540e0845010040d50207545810000f00004260030b071140d40101e490b044000b001200000100000c15004002c00c0002c00d03440347c0c03000303401c1008484502c10301d00b00e082b546000350f0010302d2144441d4004074061062107074560255109411310110858195180c420154035524a61102034809031541c010825500d51640516406504802100e241c0b42007905c41070034075007007684400e00003140c40810b81c0d440d090812071200c844000900545c03c10100703d0000b26442807038080d110030000003059a4030f42e65a10b40102c29100e101030b010300000c0c103000c000c40751145041d00030380c407481c403803030003c00e00e400688040d0690240d016500e400260b1600d80e411902d45100701d0040f15199220003148080d0341d81d441c0360900034210394554103c0e2503601d1070564003419441d40051310030381d02c0714610b00c086604000c81966000c0340e200000e1580e80c4015043c0e0041c9070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 854797508 1250 854796258 854796323
    0xe031603030e180a021321030804030c1a04060b044a070824010b090f040608031305011b240c05071515090c0e03060412090b040b07 58
    0x10000107008138010b40394002c054070709492101d48803240e155070f0f41c1041003506041495010303048002c3c00000c00d04c00e400064016200307180150f800460741c1c03a20000c1c840303440b0081c0315104104061004202051041e11203a41c1d0641d424050801503071001d11410242d4070510490741e60100081c00d0032455a280104d0300000344400d080080340c0303500300582e84c00040c01109001d10a600d1114000000c1c10170440c07461f40b110426142c0360f030800c0515001600000f08581e004000f200401c0205e5989002d00806401c40100440d2546030040b0031403203c8481e640018180310407080c0c10703081e80207035240b402c1c5007581280200042c2503000101d072640c56581418000300d00c3c507060350f50300301c0d91303102e002030404074040d800d003002e040c1035000b40c2400c61301e10282d800021031421204002d0403901c2d4010030403004140c10160038110341c0d01c000c6400c29a0844c0c045556030101611990825044014032018162070700041d4102824014050410303c290040034010401c8100d00d00040c00f0b240e4451800501d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 854798758 1250 854797508 854797549
    0x31a06030f07020607090f0b090a21020a0f081902061e070302010501230d0302120d0b040c1b0b101d160513030602070816050d0e031603030e 62
    0x10307021002003034220040d00c4600c014021880458541d5200345080c0055035000e05641110b50314048201c03a03e1b0344159441034000100c0e03d0b001440010740f00800c032040303000c01805054601e0a00c10030801c11502c1d08030340e9003407110034024005801b00040c100e0440500080c02d4a014403140005010f034011184044461071045030422032808003540503054091280d0000c0c005030740c840c940319120b643c0152252412820010701c9007881d2070910210426280030b4015200e0404022030728002c0790348110041048592144003041c81c41c01c0510a0b401032000c11301c1c0c02030280c018123800c80c120050b003010240c50a000d0101180c1c1d184ca0022400d001040500311401409020060895254030112110206480281c0201c01e10314094001c0365161001e0074103403c800d80c190b035181c8009401ca110182c800030f0703061040c035646030b0b960a015015a8003d1004000701441590000d198500032400ca50298000310f43c0c0515048070320b400d501c00d5a40c1400d2080ad00d09107040811040c022002642c40d105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 854800008 1250 854798758 854798761
    0x9090311010c020c090f1803030c040317040b0f3a050f1015030b03060403050912210702030a0f0309140a080d3f0b0f030c01031a0603 59
    0x16041040160005458002031001c4100c100050380c40d101900d510b13580018010002405111441c1070b007662005526480f4000b41545001e07691440e00112852810114005410310a100002841c9003256101454591030f00e410404032090038009d010340c0029408001c101c941d401c801313151440b01c440052490450814942090700c1c04da0084142103428820728100100e500c0c98070701e4000c944104543d800440300c051030700c20814000310010600d1010540c1da80704015155509201e464013481c0a5590300d61244280000c000d2011a01c010001242d0b1040071104007040c0091680c0c01c603c80e44101c2c1d127440e501c0c0c500204e810020119401010740051114410800d030300001c403442030341c040400404800c20b9a80901602c02c4040c06010b03442e9018010561000303200b021706421071180009001c00c9815038468140d45c00700c6a0900301036001c0910522981c546207072280104061040703c541503000d41500c04a500c4030709024034181010303168071088010142880750748224600c00750201d0340c0e9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 854801258 1250 854800008 854800013
    0x405100b03160801090924020c0114041b0807031b0909320a0b060102010608100219050406051206010e061c11030601300207030509280b130909 63
    0x44000c2c0500600100b80840000319400c0103910030380382d1450348282c100b10106200f15151642c40301101c030005046408004100d0401e60071b01800c080c0c1e50394102c080b0f160781000d140400c0d920b41c078100034510035402134608004280000a00d103045980148550303148080d04000c0511080d002d4000007a5079080a011001b0000350b43c00da1091451001c0c02103502c1401184d20030740c814004001042c05034480600c07180450600c0600a0b0000d505000024a0940d02c0003040e0605d040c2402c0910025170100700340c202d1880c1d41c0030758900141c03030345070540c605030500034090014096032000005130b424003c00242c440e4054402410360b00750041c2115221002c0315222003910580c4141401e1407428120b0a1320402c004c0003c2d80d0080c82e0584801075402c400440c0c8407400c08e0340703100842d0364090807004590300900c58401419a68000c1d0b0340c0e81c2da906030b80300174001c440f820000c1300500d031031044d0344100501125283c0705081d07601c42c00303d0603130758480050750009084042e00b000000c41d180c100389004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 854802508 1250 854801258 854801281
    0x30305090a172a010e0111010f0513110409080406120b0a090b0a0b070320010b09181605011e1214010312090b0f03070c0f0b0615040b04050405100b03 66
    0xd010050140c1d10741d00e0324180c00b2000a81008034403c9004c9031521030f001c106980141580084010100e0001808011012840098a0040d589044039508400054061180c01561005002c106440520400509544408a9205502c141070070400f0600c0314420410580d0071a60210400405e0004195140d5031410000e10700c10230b02e540b240f101114000740c142e004000b40d6449030b07010780758407581c1c00d003490032048000d22444680d8425581c0790000701c0c3c50394030703410b289002d201159924441d4007600c1d41c03080d140200b032004c1041d0358044008100701581e40000c0d50035611242440c0800c40c4611035800b903800c181d03503902202100303003040085400351440b01d03081030403280101022003a010b0401c0003a103001e0420b01900d07003c084100524800100a0b1000b11341000ca14034140c4035440340c5456058040c400014101c5003541800244174551505a9401d40c0c0180c43e106143d10b040d14042c280003484c402e9102e02c13070085403168005003034501c00d4070144004003080100700d5540e02e0314802804 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 854803758 1250 854802508 854802523
    0xa0b13060b27060901030221010308031503210c0106030b010308031609060c02192402010506061201051219030909061a0319060b2d0c07030305090a17 66
    0x519242c0300220401c810709585901021880015003290300e4400c1e0000110040c0d40030740e040301d1946018441c0c041510951503180350003103000f01c0c011074032410704407100c40c2e402e8515090301e0301c41d5100d150421301d008008107500403c03c040740c196a07602c204801601e80501150390026090b42c0e0880000402e000341203008500ca0980801413000c40648a00309665000280c080c0500280708803000a0041c24a888041c0c9564485418100c0b8a80d60300c90008581c00ca2500710f5034036407141c8450410f07258090150700d070010000c640303181c00c0015107140c9441d001c0d014446c903072107403a41038008403540030103002d25481c80700c807107a03e00180340090070040c0ca0f640842c40354048040c0381007000151031a01e01c0303c84650445080b0694510744540f005030303c1084018a031a140c0c1c95507510002032101203038000307040c3c000001188030400d1199101c0c028119682d403c01d0b20030840e08203c4d03c5c00004000c9814170940303038903041450b1269881c0c004501c0507038042d0402d0084180340e04040d04031039030005242 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 854805008 1250 854803758 854803777
    0x809040b0102010908120a02040b0d0f05010b09150904092108091f05060a080f07030b0c040506161403030f090d18120f33050601080a0b13060b 63
    0x14440c0c5500000124201c0c0e0844801030b091640512103410480003e101c11a006100e501c4058186502e91a1543c12540540344218a035941c0352a810026a61809414010281c8603000b500300100b0380d001c82d20782e0108130f00703420721080300040300ac1c129910b035404118403a822401685a001541c4440034200300700544a00108601d030002a440c140300281c01e15441c001d440f00340a902c44044818806404050051640b080da03841000c6590a4100403012440c41d80c40020600300d40f660070402e01b00c90001d0044a1f000d642004140480e03100e038001c030b130031386e60100b80602801e0708103060283e5042010178004086000010900a02c11214200c850144480c0310030364002166006042d24450311500e40001d0b11512000d04000700b0780071541000300b0a000c1d1402004038040c550300c04109a140b400c0c502140038840d054008250f113124000c0112021a01c0c0c20411070401c0c40003e45069001020640740c1c4d510740400300c0b400d4554110140541540c43c81c1401416202d0220703030510781005008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 854806258 1250 854805008 854805011
    0xa0b101121090306181f0e0d081902090a050f150d14090a03321216090303090b030402010e04050f01031b051804050109081201030c050904051b130603080904 69
    0x1c40d00402405170081c9024600400500d401d12a1102200d40e0700d012120306c81555a5815075003d0280d818002254440f42c40d13584c00e205843c0c00e000e02d9444450750700c14002034510511901d582c076200e0414074810344100f118170702d00420410000402c003c00c100c0c00d0402c1e100003c50030081407100c1e0f0b0060300c8000c051444408403652491fa9142e5501c2d02082c0c05070002d041c513016200b60841c1c0d040b407046001084805001e46400b640c1184425034030080f4a4102c4805000420040c070030b014090741000e11040c5030a02c0740a00d140c900910110319400741e4100c00d08008082000c6a004540102d4441c00103041404070740f030302c00880103d4100034482a6003008080003000c001220140400c01500c100074000104c451800161540281000b4000c0f101903682d5190b10010a46c100050314103500880030141d500d42c15407502e03051928003a481640551050400d1000069011070b03000c0c2c0080400065818442001e0009910358038400c8601c415189001004000c1c001d15000800b00721005640 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 854807508 1250 854806258 854806261
    0x10b013906090312050c0316050918100b0f0318010b0d03320a0305040218040b15030a0b0a020c0a020a060302120606030c12070c0204140f0a0b101121090306 69
    0x129001a45c10803038032071144880410008880340c035030303501c001420709040c900301e41080020b0707000c03a0b00c0d090903d1002110071644410031004404003c5903c0191140c11011402c16540d0300400980380405028401c0c0515a00040c900b030303140c00d6110010601004002200c0702c002c13410702500041c140200000e40004e85006251580200d080301100351504030301051420041a40c124018007015204031780c0403055001c0314000f4090341d1200b83c0120b0040034804114102046040082d10050580a0003508000c40d1100450140701003560b0103500380c00056512402d0145d8941840ba400c1c0e4029441162000b020540d90b83c1503000e032410850b4403e01c41095100e0404026060008640307600e85203008000140794500300c03124460f0006000d0a01101c0c05941d580040c05459802c2e0b5400002ca800d2010400e880c0c804800640d0481c0c3d100508010301008403010075906141201040140702c074607050391280307640401540f0450075100341d280080542c03110b0b0b001040c1d8030607a200c034800d00c070340710 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 854808758 1250 854807508 854807537
    0x5010810060807120c091a010206070806010503070e19090606090b12040206090105040b0d05271c11070e1015170606070506040b1602010b0139060903 66
    0xc01d5900399070400004009861502e0311480751006084c408131444808000c002510305200c0c0a010808003807021545952200500024901107004080c9410002c12400b440340c903036000f6007183e03000300f0307030b481c051045440340030200307042c21804880400c95100d583ca000401d640300c0d80c00802542c04684c0c400c0109a541d281e02d842c4c901407a48060903810191010400510304200100b0f005c000c181401d90070700d66105102041c641100b0050014142ca48081010b04006220713004081c10400f0300e20102402c110700e49a598501c01d80210040d40c0510050388409405650035a002031a908101d80e030064859411000b5a40d09407a09040f8110a8001042c3c07401702c21020b00349110203640c0c0500c0030300d2195001039409800303422290011420002000030442c1401024070881c0034420180b040c1c1003245521401401c4000d005d002c59140c5003208019a031b102c080f045008040b4030a4101c80c0101301140f894102d8542060a800c0703003000444010084580c000c41c0d84280a41c50307881040e606403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 854810008 1250 854808758 854808761
    0xf0317070c0204060b2106030a021e0906060301210219030615080d050a050d0212070c14011104061206052211250611160b0105040216140f0703030305010810 69
    0x40700000c0c14a06401d01b1040c010030f201145a4400310003000c84019003082c0e000324502e940540e010409141806103041d0f01400e140e4185a0001406d40c1e0300d81c03070f43d80341c00028101503552000201058a03400382d900250743e1000c950328400c204a6804c00c0c41d043e0f90349030210040c6170001d01158111040200001c1940c40410540d130724203480d8844c180741203840041211903620500d156503a441d42840103141c030200e2461000e1080d04d15464009a0150b1424503601d5511030340c1c0042010b03814070000c1c1c0c0c2c6d081c550740b05480440d06142840303d0140c041c03240d0309014040c0c54000c00d80000303425405410074800c1c681e0518402c009201c00b000703e081d0341910a445449800301e02c0c190810350000c0326284050708070618801600030000051003080c0c050322141b04c0d602c191020510f4905140c002c6042c84080920140100380c221821840c1c10b80d42d02000c16841000f280c040c1400d48443d0040c4032000060002914212030b01d02076900761510b9103000750003814280190340d014840c580e4118400d40701ca = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 854811258 1250 854810008 854810017
    0x602210a05040803060904150f0209040b0f0a090f1d0303040210021c05030408130b03090f07120b06031e0604030e100206061005041e0923040f0317070c0204060b 71
    0x420502440d50341c5d0341050041000380500126621008180ba006109542d8824030803103c21803940507907200c50b11030820040d02c080401113445881800d50325501a50350414001c01c0f10111031001c91080c4003954924001c06500c00c6010380e4880100b50038060000210040d4452442220341d191074042c2e40608981e0b458408400034280c11100d0b801c407528a0040018680c41440340307103181d1a200c0c035403801e00300d141440d41c0301e000c8501004c02400b448500c14810f514010900500411400340381910b00b0b2815410084060800d10901c004207050f500c0521404150782c0d402e08500d0244558400201e584d8241150182c0000366150b030340b41030038541012452900301c4580d000703280390389a0408001000f29280c0740582070040030000010310800c18800040074101280100070610700c2c241a1000b912502084e807007440200110741250000c166890f150881c0d002551007031442c11307501d000e4075281821542c0f65a1400f840c8108101541d1054000072214400c0d5002c3c051240c1e0344540000a000c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 854812508 1250 854811258 854811263
    0x150705220e1f090908070204021909080a050601051e0a080a060f0b061c021e0c0f0313290706021801260604060e0c03040c05060405010c030305060a030602210a0504 72
    0xb900d6003041801c219800141000740104083c510304605513000500726030249250401c5071084a4242420307075003204000c002020941c5c00391a07a401166240b0f0748070541409007074452240c141c201d01c0351102150311503000c510b0242140031040d440304242503070740803600421039031141002c00700a1018402c1c0031b04561090040c102c00d007803114064181800c04218090503211503403c0c410042c003024a0241c41c408181d003051400d6882100f003664500700342d05449480c1e0399030700402800030b40c0c01582040004685050000c1d114a902d0350031050550364a60f26172006036132004c90b00c8420300c2290b50007000c001c485611402810703200a801074800028045121030303031070348802d00070310b41a100a000d070342d100000810004040d61a881d080340d0560083d90710320011171000c000c100801c4608214903001d0101142e50fa418a450640020210720954030000c0c02c15840743c010a03250384400c0f9500c005150b11403007e5480307061105c0c0a40c8440280d00f0107030340c00340c9440003082c054a403c0c80b540d03000b00e8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 854813758 1250 854812508 854812561
    0x303310305090409030c05030f04170c0a0b0a0201060e01140f0a05011202070501091505061008040f0f030215070e100e060909090f01090605010510020609150705220e 73
    0x10300e460030400100301142c0c0582c28801100c6d03400b400600240024102c1134103a075686911181440d8290f0340c0c4880007008a20030780d00802000700d075030340c80c0078000044992950042d0380d00d0b1204030040340904020340c01140f081403040d0001c115001d8024982400c450182c1d0110909001d881c00c00002c61014490305002c200e1003070040e020010541c00500310b070303402a400400d0302e01442c0d5414010b120020741c1c40010680e0f032001d1102a04e411582d0a4842d1150318216501e070400fa01d52407508110404000c252498000c03141c0101402448503a80c1d07910034160034409441d00210281401301c4107000c1500c2080f00d05080e129117070141040141005014010905240c14942440110301e0046e14404051007070111b061010003090050a03400e5200701d4004c00c1e00d5141c8010701c240ca5081c40300d4801550008000c104002d4000140031403d40800b0080f42415183c481d0b054030b0b68400c5400b0b8001010b06200000c0c100300c00a21132008071100988240c0140d560441075010b0b42ca001c220803212003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 854815008 1250 854813758 854813767
    0x2071104110705070305030d0509030a0212131205060a050106052803060f061101060501080903033c150a0b16020102010b06120a0506010807020c04110c0303310305 72
    0x2030405a0040c1046066481c040d4689001522000d1802c04654021501e0703170b10000d8903500310709241c02115040020440198248008050081d441e0603001c05a8031400702c01160801044007180d4111008101015000b0001034541c00c00c2602c07000100c4038004814104000016030521030021230b40b131406035070245030791020304400d40f00c01c2444941038034040584410020a80c907045411100040480d81c580c40480304c0c58903c005d0035100140c1c40141405440c0e8104030000e900481180e5004054070100c000509030300c201f0340b5424500d00c41800c20004038109110004a901c6646405440342d4107000e400050400e0400c040b514240c01006a8030f4003e02c815a88019a04082002584140000b00b002c040e08800314200b5000b44281030700d0122040305000b0440002d00c120741d086a021329020351146408030b400396485015540080c080c0e41d58400351080e618181080c2e0344000302c1e131820307030703680381040070348402140041c143c0c44071819040c1d043c0b480c640350030040392104264540c9a840c02c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 854816258 1250 854815008 854815043
    0x9060603030a0c110315010b030403031413020f120d050921031e120a06051207140f030307020d0b07090f03020109030803060409120807020706030b0604050405040510050a140a0207 79
    0x50130012010160180304882d1650346940c00002443c1c060a40220401d031603140074100241524802911228841189418413032110340b43d602a050745c64050300c1c80180404550041800d0509101c400a25030003404070b240c1c101a8010000c0440745030840307038540001d0311440314a081414504108036103920402c21040c880007240135000c40b444407045a1814032800050f0744407014021a02041040e0713650505011a01e031010080c141e040208005155450800d80c4030400c0314400901e035446001c1818810380c0960b0b0420491740740743d07405000d442c60700416180100030340e0010340f22100400d510020219001103611412000c49405943d8100150320b1516003104550001c2c04850300103848401640204210030401081c00c0250b030341d103a2651520b102c00a0504029400070002c0606000c003007501c40ea2684151420354404071400a003e880c1d901e4242d1500014000800c40c0c3c07802d02c4100664210306d640180c180d041c1d80604807070039543c0d050f800c0080b449041c200600b10140e000a120340c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 854817508 1250 854816258 854816273
    0x7060e06090307060c14060106020601060f020d0806120c042306120c040f09050d0906020106050418060f02160b10090c020a0f031202120a06091e0902240309060603030a0c 75
    0x5d05400382c41a040420b903408000350920030260400307000b40c2d0210b40100b0020380d10101840c040a4030780301500900310380c00002054054040e24040c4500544003203000011014007120780c030030b44014001c1280503555181d4410081d100141c0003400c1c4452000106141401038005084428000203852070440410400c4003c158007111240c50076a20b000440c00508104007903450200300d51100481240b401a009081d20403076003010340210b0402d0300c0c0c440180d01e01f8000c079a00c503501007804910082c80d0081000280103032104c0e00680480c8900c1002481802c0c0c101d28004c4c1d201124280c040380c2c40714400419540211180c5006070300180141003c600184141e60710140300f4a04032110769007006c0c042c400d81e007050075070031103501035101408850040740c42541d0084c00a28014802c2201703250311031303828808980c010000c580d190b04900b011035540106100041103400071070304800780a00c100c442190401c03248850340b071240c400860b00e28580002603d440c40350303d070b130745032106200d85e0380781c44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 854818758 1250 854817508 854817527
    0x1116030c06032f040e070201020702030706140d110906030117010c09030809060304020307031205090a0e0903031603061e090f060312050d09020301020a020c13020705060f1504050907060e0609030706 87
    0x18101c248804030701d06010405c9140a5815540056224130382ca00425042803902d0b0700000c280906104440541d500020a440d10400800307000a1710982c80003000c0c6661054010543c2d200304008000704801398a0510744a060420030020051800d100800340c5018445020140081d0011f102160302c1c0d10b0a0710056520501c0a07065a207807980d83c0d42c85018006071845001d02165011a030400780d4145842100000c0c40319400040150415010789510380c4006492802741c031860554030000d0781c1c048d0300540000c2c022049815100a49042484010a214020041c4071418050360b10aa4003c81c040c81e0162600725406106204951382f040d00c16900c6040c200d401c240d210032410f005a1340c284040d00c401400b940141400640e00070800c04210315042503040c0185c414890030300801c0000500c240e11181c4200786813565160041e45988004048102c55481400c160401501210110b4420308680c09038a810303a0455151003040030b64000c1a1501e500760b80441d00802400c0d20940096 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 854820008 1250 854818758 854818841
    0x30c09090b0f030a0606080f1f0203090f030c0a15090c05060903160b09091b030103020103051003051e1006181505060301080d0f09080d08071116030c0603 68
    0x8900b140301004241003203540380307040c4c0d0001e035500b10800103243e0600c501d500b0740440741d0103058402c0100c540601d95803410011280300d20f6011001500b04c00d0300300000c038102c0c80d84008498880c400c1e4100d441e554000036508440301082c0e050043c0364901c0b41e019040601c2c1d4025000a4003a00f0302091220980010122035814450301c3d900a400c40782400a01001c1c03c455540c89a035103c4002c2805440d803005054100c002c00303007918141c4000712107000d580c1520b0f0709280200b15601c95a664a4150300c640e00064200d000b000c079100c40030511001c2540104030a01c00b90f451565072402d46204844240c8079001d04400d21030b824035101c0c0c405600a65a01e00b5520800501503101c3c00032803007940090304030f480e460b4000020190039540240040da030024007441c00c4a031050038103400c16141c41071701c800a024031500801103014103018101d8070007286c07840c0b4100d6030410485855170200d400c0503c029210320f420000040f41051080c01061800b80300301340b80882d43e400d80c100d408001907040d58070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 854821258 1250 854820008 854820019
    0x215041509050a200109033f02010c021603110a08030f031b090d0f03020f01050a0903080603120307080c12190e010b090604150e040b070f030c09090b 66
    0x10214148400d01c28044501e000c0d90042002030f542d0b00d850078418051414800204026112001d0385a0340003001005803548441c0034940161811004040b0021604c3c403a105242002903952219030750701d001c1c22a00c0e00d50f42c000d00484905072410b9803652441580c11a50b282407100600114400c2200c58001c24005041244002d640e00b04c910f003150004402c0c29150400003040c404103100107031100c194510001c4440d85804644e00005041042a10005127490100c3e2040010300d8000d01c540f6903144818002480240b5000300d0900040001803003c0340850f4000c000315219040004440e4589c03160100131500c0e45d20b0b61482581d100d00020f00518810008002c40006251050b8500e0b014160300c05d880c40c0041001120310703055a0292400707800c241c0c98020600b07034543d02c81080b550040d10540c1c000480301c14032034641e901c12032a030300300c2070492220380180710030083c0d07004c0d446200302407560b50031914074000d080032820303111840c0c900390024480340e50900a221080d803181c401e41c0e000405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 854822508 1250 854821258 854821283
    0x2d03020d0b0d0210230f0406120b132304060b03010c0305090307030c0213020c03120a0207020d0b0a060503010e0c09130b06060f0403120c03030b0f030303010b1b03040b0c0c0103050601021504 84
    0x51005035000c00101b4402160210701003240640003031a180b00202447c500b800030040320030128001075550707418011355544410030901d50042e0030851116001c2e00c0511884186401e00f4402e01801c00030100c00d000750f10f80050041160720038403581e8096507105003d0b609e81500781d1021188280e6407a0107a901c011080145261400584002c0c011407007400c001d0341d1110300c40b084a100d00f070320041030b900100d0b0040183d000103036100000c4080302c0ea40f014074070495444e2000900d0003080141c00550701980380c8001c41e0400c4100290070540010308407030241495450004070440c1401c4144028a02001440490740c80e15100d0b0161100c480444212403c0135a241c8990707280d180d200e0400740c00310380440200c2c001c1c56490b000b0075152410554400744501c5081010071707502d200510510029000100d80b80d00c0c940700c011240c2c0444101001200c0c0c4854403043d0000d440e0f80021421041f921404041600039402400b8091107680e051700503040d1904003038440c08940c41c0c0140225100d03005c820 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 854823758 1250 854822508 854822567
    0x3040803060111031909120320030405030708060a150317070f0b0a0b010210050c040611010609060b0d0e0703120c02011815140f03072d03020d0b0d0210 67
    0x203000314011724120700e0030080ea90302010388900e4158001c8082e28400304042c40c0441c2e0002280c8202c402002c0c0620312181c40a01410b040d80210781110380c0c1030140020006040030001111809a036040c0d408201c0300341d071400c2c001c800400c2844010f0660070801c2d03000c031080c21b80740c01422003140100f10b600001442a683c141d5107450840d44046580d076903240c0304010307590400c001c28001140510400c003070300b4a030194161600451140e18208808494821002c800a402880081c10031010520840340c0307030039401109412111403a180146407260036108580e00248400c21681c000042400005e0a00000c4801d080900e4007a41844108041010301d440300e84010401400b840d036009880544059000300f5140010009540141003400340c180c41080e40d000300e9070040403e003803141c140e0b07541407055a00e190303980448420400200400e500c2942d01500140703010302151030100403840c0154200302000305240c7d4041c0d045491200400349142c000e414062403071101c110030000c0e421030350 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 854825008 1250 854823758 854823763
    0x1e0121020301030807110103050c03060d020307033203040501090603020702040905060106120e07080712140d030f0f050f01051509040e01140603121204210f0f031103040803060111 79
    0x381e00413614644006212814012000c1c41400340d50002d10781031245003000c0845a00d68000a01598070500380c24022404540e000c0100100665012030f0352080850080800c0001c01541a0440c122800d5130f121001003840c044200e03801c0d51016141c0b08100c50070004220025040084201d030000d41d10002d0401060040169a000302040d988082d140d12008140d04241c852034641100d042d40b0460307090110f1100032810a0a81d03041c040341d142c0c2c0d490281003240003010500080d00250094825040c820f0fa407580003402a03011140003031028010890a003000c41c1e00850340141d0041c468401030140e071500001800481807590340d404d05101070000041c0880e100e06c491121140c0d501c0d01c91410b40a444402698040c1e401c401610000c070721080030200c2c1d442407242001076014000d0005081040106801d4903240304419119143c204c4400081c1840e03c0514107600441e030a0020b05840c00d101e401a031116181d40d081ca98299140d95a8902083c2c0024007403078103100e044030b19050446002c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 854826258 1250 854825008 854825011
    0x13020d120212070506060f04110d051609061211221d01150809160b0d0e030306011b06060b0f0d06061d0904060b030303241e01210203 59
    0x1440aa901021010006454400c02e0350070303a007500e0741c00d00034000071520101e6601d60190081d55181c0803400d8510000f0b00400310a400f04c000441c0114005200440035800184502c3c4640d5a4680d00040054140d89003c00d0b03104a100294940300c01c40d42c448600c1c0c2164519440740c41c199410440004d846080c000b080380014003850301c02c04020001259603e080c0300800288244081c10755040c0f60b8082d0180c11025403400a221086000c508940020801211500c0119503100311080d20752026168952100f07144440c402d08100425001600200440e806058140c40304508039008132000c51824114990a075a00c5c0d40e40c03040013510600361b10040100b002e034200c0c042d559103851280d94045031625003001c0204003415a014001c1030814980ca040d11070b088860300050b41d00c1d480c0c0301d4080c107140c0c407100790903000c003205010011030340031407d00610505904100c12034002c001030106401e40030340d444010040031030b151310603940180107188105a1100e03491a49115105824080c0c3c2e10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 854827508 1250 854826258 854826263
    0x5340210110105011409070807050c0106060509030c010e0a0501120f1104030c0b0c060609090a06060311180f01150912030c0b0f1306110904140a140403080a020313020d 74
    0x1d8107003000c2054a030030f11a09024107142d003c07001d02154200c0100d9000784005104205110781d800c0841d0009000300300751403001001c0e4009110494403003800074002d4010039510350003071140720015000303907006070b00582503004041c0a810b83c172031034680111524200800100c03101e540c0e80300480d0030000170380030300c205000c0c28a801c0380ea80e038510710f05009420b505900c072001900b82440f09061920000c00e0b4690822001c541101c0503032150032605043c1141c4850051819162031000010070802c00320311954240110ba920061442c6c041d003c0088030822284008100098001800104840c0d6082d6032805400d107001d0b05540e480d518803030551300780103c00f600850840070a01d801c0148141385541d100000142c0d801d000d0038000031512416039100c2000703182030384814078422000840810f031000e01c10010030900c00a403020703003088600d05055036011182800d04000361b40c01d440788900d690181d030749581c8440d01542c4282d8100001d4102928200b00014001c4a82015940320380844070480e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 854828758 1250 854827508 854827517
    0x5010506010e01081b0f040509070c02040b060403021503040827150f090d140115031401050603030703081509090303190b03100213032a0605340210 65
    0x10a48000340c071821001c0b112504001407041004452051401d401c965440110a2152503000341c402d0b44d0002d01803500310a401c203180e0020091090380c84070403940b15500036902000201418001d03c006441540800303034010501001d48481c23907107020002d561141c01815400d04025880900250700c11050111303000d0203094a05e1542c4a24203550751240b40f401f8090005d00c0c020640345050907500450341c101d4842c030170754410b020510262400074268a5070240003002211701380388144005c00e0307070350209480002d142030728000c05210510400d401000020011030400071a96021100040c3c01040510350b414014070320256900d5400d40103000d103034400c0155440345000018118898a00700d2030341b5501d4249548200e85803408121410021102500569100452004512165515400280f407400c0038200e0407044507100302c503501d405402d1517580d2030840c3c4d580e1080721540201001c2032a0a051041c492540740d800c0c01d240400060800d42410f00000c960300080d054490007041a0b0224 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 854830008 1250 854828758 854828761
    0xa09050403081b03060f0108091c030903030b060f040302060d090501140403110c0f010c06020405060c01090c090203010b041206090605040b010911040b0406110f0f0d12140a050601030f09050105 85
    0x103055540f4000b0302c1c0e81d6104240c2145044e000194250810084031410b0100c0a000700e42d00e44428046240034120345014400121607642d00200200b0014a09a000034600383c801040c900c1c210040b0303940c20719249007840c18a8255000c00c641070340450703040c080b1140c0d036030a21400540c081c0115507a40c8913850500030a46400d08018004081400d41e154254104446040056940c0c085001c042802841c200303950750402d2502000030b11031508065401b0030003140c829142c00d015004007000301c1c840c007000b1000680d030f09040c20680c0820b014805071140240414400f20400020304201940141004900400a501d455084610a840c140e0781030340048018007886005000301c079102d800340c86050789014500210649180214003410080210b4000804a4000100300d640d40d8000c3c0382013502c0d030715003110306d40950312480803000c3c00118504044100900c00c1c43e01c200c0e03032441e4201ca003009544d80c2e12040c00c001028020700035814180c1e1403d014151031124403550072a00e00c641e0000809 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 854831258 1250 854830008 854830021
    0xb0406060509010b090102060414032203060615050d1802270603030a1e1e0201090606050a051e0303130807140d020607170415020d0809010c0f08060a0905040308 71
    0x2011050700003049500c8100618036081c2d03030005081349c4c05500030466206000c01101c04904512400c0303001441d03504001c500c01003000301a486141168801c034402c02089a80707080c00e04144e02c060f605a004940c06008040d044e0b4501d4004110541e540c9800341e031146810f40c0007601c0c041c440d08004251a400d0015080721580d541049030f00490114011424031500020044c0a4036000c00740c0c2140c42e400c40b03041d1040c0c03070090781d22407058250481d2951710000c002d28000e000300f00c110001c1d0f407820b003014030000705030034140c25110584001920550041003035008403412030400c2c110550701480b0801c50300c4104100d425014020b0205480070b0720603149001c1d04031151818800110f0310483c064240100140d54100c102c074604ca50000301e00c001a000d10400800c0d50051b039018828070074070800c4603991a9030105400c080001183c451410988400a4003802c952410800c0d0f40032034030b6480320543c49405002803550100780204054816500c0c0c120040980301c05441c100c0124074603400f400007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 854832508 1250 854831258 854831269
    0x203150a08120f070605010b0d061401080105011d060406170105031b100309050303150103180c1e08010e070f09090b070c0201052809050612010e130b04060605 70
    0x2100222100d10036503007003665030740d1150b090030004001c0307072000207441c415600f10f4025a2642c5030043c0082103150b94544440c0f550b940040c42034101e01c0d1030302d200811042c2c91f105034407800c0316044e5a0b03e00716a007030000641c1c0311088a02041c02a809207408500d09a880a0003400a45055552441351940459901243c5441a000144245c0000038030b20501c94403081001c00a520031292203062030305800c4158010821808050300701e000020800c00c0741021208019002c1070280d90030800070540b140c24140318010366800a1403c07009c0e40c2c04000341d0070b8007103d6000d03411040c800350500c10740ea020800d0840c2c180c12064805900030f1001007002880886c00d0300000c140c1d01d1b07424411800c0940c0c900c882408010a40018082d42c0c1782c4040559125506440d403160301e4902c0d1403040c801601485400c0c8d420441800e0015a1044c400301e4039051000a40d00c1c459056485004503901784011816204002029044030313000d00d001d980701003108010760f00e015034022000043d4450404043c0203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 854833758 1250 854832508 854832541
    0x40b0607120e010311030c0d09021c08030f071d01080912040e070f0f020705061608070b0f0a090b0604050403050705030703080f070905030303062e0801170c010215060310020d0203 79
    0x610240300b402081240703087c020032902e02144062000883c1d2107248000781c01d0380c111014031075510304003c982c04204605100114000d07800c008080d1925a43c640044862100003c0320201070b6540d4140449954054044541c00c100400c0a07034996002150803048103410039882a0300704010941840416500940d08054402030303880c000c3e08040b249100a90380348207a1081600074000040c002540e4161640c1d40651190700144440c1d80f460141022074507000e00799412400e040c24400420142c0026101c0d031004544c5c0000010041d9652108001c01820020815002c0c40010000380000420901c01000383c140310340c4584580b82440d039503620b1910001400d18040c00b491000a110541d40003003502d071b129004840c403100c0c200701c040c00c03c24500c414080c1100c1958819280100d41c5422003041410380300d04068a540c140d44c0148031554448001040c18050703000141c0541d001000130204682c440c2d0080c0071a41e5014003001e070f0004913408152080e10442e03000c004d12102d0701710071211a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 854835008 1250 854833758 854833781
    0x20d05150306070809011d0c090105010f0c081e031305010e1f18050718052a0d180309080d2a030c0209041a1311040b0607120e0103 58
    0x214031080c030880401d69803880a0b200c40180842180000d182d10000d400c4842c00c85103a43c10a99250407a2134640c0da61300b40445045c0c03003200d04c0000030039079501c21011100d00c64810b94a10b070807a0705548031111568070000940c0740b9454002000c0c0ba0b00d0300008019030082e02d0801c4207161000c080e08100d800c5410343e092a0441b0342092800060ac00307083c0500c11441703c903007000000c013508103060b007004551540314020040d0049441c0000c110382d0703180301c03005685075645091100c1d5460300408054041c032200010030500110b08020710380e88162018204881c03a095001480101c8941400f1a480c0304480840020340328035000e001c103042c140f00030244080e050402c0b003201508034041002a0411804142e990f100303540301c480c203051041a5500a5070307005820150350341428280f14aa210120360089241e1099102140c00811150068480c0c26000200e040030007029404010281030540704d541e600c001c2c240851404281c0c4490341205101c520b032a4044015122400074090300d0848030f20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 854836258 1250 854835008 854835031
    0x1519091103250e07080c0a0315180605040b061204020604090f02072307170c0924032e02040302041b110109170a031409030703020c0604030f140c060a0201020d05 71
    0x1e04c8545504506025040482d038081d45071180c1651b0011001041669488038008c21400c50000d400b845404140c501c00103030354000d009642e240e200340b109445c004400507030840810441604010521500203401610017030035189050755605100c0103480000e800200c80c20b40c00540a0200800408a0305961484d007190941164041402940740c03040e03032003280b229451400000e00f8132007052005045140700203211100500b40464003440407052014444201400c1c0303442c0403161702d0300240e00940080d083c0034440c0c20181c41c2058440404103014103c03511a002d000100c0103a4941c001c0c0000e0303400e0f14501041c455080c2c00010b003c1d5440164010b4030b41d151012010124404031203640d00c5100a0080079500d4040c120120000c16007807801c05200b1320860280600d0410200050079010f00984c22680001d481e0310070408030380700e44e00c00200030841c0600254009000e190990200c440550b0a80c0c0e50421071002140c0b40345e1040b4010070041c3d5001404130402001d42c4207198001050060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 854837508 1250 854836258 854836261
    0x200d0b0d08030412120c11070501111b0f1002061b03090703030302092808070609060e0f0d080c030405190e0105150c0d050c1519091103250e 62
    0x203840308588000380024050713030385030700c1d40402e014050030400010004c040b030200846200c90301c1c0180f0710705610714a00081d014080c800030b290b40c468100d003010030b55031802600011900400d1a50843e40c107240ca81d8120401c0c01034000f650f0345080f0704c134142000940140030b003860900b42803a03089211046981a40800307205200b150354001034880e0a40342c3c1803c0c010303601d01c040d1001a06104104420b420702c80080a842c1014816540340310003121440401c03110900c0d00d448054a05550500500c00010342245200c03034a031400258041c4000303005401c03030150070b0301501c404d50030760721a513600e250700d0303000260410086c14803041c000300b00c20103890347c0d800e210304002e030801000e80c06100d0f0501c1005d0b20900f00c40e00350303941c2e41120981ea131417004844005a0100b0098100d03000481c01c26070502030488014455001907003180d100d41c4403015100391800780400904010b1203d52000e84540c629503403540780b151410460400094114842c046c404074038414408800c442c250800d000c555550300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 854838758 1250 854837508 854837513
    0xa0b010b0307030f1a040f090f0c0501080702062a070c0f0602070602010605132004140f04150e0a020f030f09010e0304080714060f030a09020102011b17040501200d0b0d 74
    0x1005d203840c00411180440c140c0f80d01e8400d90081c03c425400609650307050201e4608001e01c3d0742d01c0c80100e035002c1e2142e4403141d0325001f0980c2c41d800d0445220308454018100c60b1a0a03441e070b0100749010362900c0c0e99030b042060586605501d04184d80100c0d150601c145005c1c00314a0301044a1070080004c1d01c000c0c01102c0c10000803032041d0410803181710f1003d84810020803084520344102c07258900d02224144c036035558502d151680002c841000d401100b180c10081c00c282414040c0c07500400f50f00c580008043e1401e078039090036901c004c0c00c64404c03e43c01e104036403000ca08a0003c42c0500228800101d0700d0405080c050700315a13003400c01070660307442000100001c07a0301044410448800760a59082d00b1080b901103a1188140c0d001400c2c207500000030403a11201c15442441628004e038002c01402240f0344070142da0308421390003c40420304030b6468a00000c40300c2401a8001d00c81c60010540007161208151407440381a100c0c54a0540864428000d2086200d0031054241c121029810a485038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 854840008 1250 854838758 854838791
    0xd0302070e1512061b0306030a0b190e011505030f06010b031005040608062a160f0f0326060d110307030b1009140c1603020a0b010b0307030f 62
    0x24880d8a0122101500140118018008400102401600800440e4000c58280d40c45030001c40c0d01c1500b05d1a0180c01803848420032050300d103e0007001e001002440307404c0d00c800984140c01030210302030240d044410a1440018042c0c0b000f17002595001284050008511554440306074002c00e001c1d40c010041d0320700488000810390704444140c41c080b540c0b030301c42c03c000c8084d0081c56001960030a0802000255582000859030311401c269800102d580d05103480324400c040300c880c259003400400303100840352603001646030400b01e4883c82102443c6803503a07454210b65110000260081100000103a07011210260200d080300d02c0d0380484409450480000750144481b2030029007900f808221100080d2001c00c405006503820003012001490000071030b490510140c003c82514034204200d000a4500c51000c1501840d90410fa007410324010300e1b10140d80020307003030060b001c40c4100b02e04040071650b07546620b03028240918103150303a0f01d050304024054820420b22101c0c2145404c1d901000240305 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 854841258 1250 854840008 854840023
    0x5011103090a020d030c0b1501030506041e020901030603050d02030307120203100b0a05220503120304170f1306050702010305070e0907030e030f0f0912070303140f1603030905010b0d0302 82
    0x45034210200f0545007801c442d12114890001c0a514001040c00b410341c3d401190064204c0b2301b43e130706004a541d0390046c0000c0d20140c1102c0f1a01085003200d0011501c0c3c190040c0030074800625002903a503a99880b414034001d440c1090300c001d0b0300004180402075522541d80402010190415803035401d000c06036180e030604038401c40301f43e21408150342c4103582c0316404950300ea02510300070b150280c240c200c2ca0407103540e15101d0135109100c0d1442820802026500341c0344100d800117115110349964006540442e4003840c071078210803900300100581e00000d004060080c01c5181e490795158805803002404407000901300101740081c812090780d03580d95040803140d018040b4035001c9024407801c0707807040c550b02811410024a0202051066045440c00c1c050040306804440f260802800200030703a0300d0325480d01002d00040c02c1e20244950141151780207040000f0b1403801107190072980888411501d05008003200029211400d010522009001c0d0b5004440300b2112442c00101943d406580c2e10300c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 854842508 1250 854841258 854841263
    0x605010608011217070f120f08010923091218040b04020403051902010509031209040c051e09190603140c0c1510031b03060606050f041215020d0905011103090a 70
    0x50000800c01200c0d00f1820b05a0b0211100070440d903004809043d03003c040608c03400080800d400043e17500034074045d036904903140034042e18900540c841c40401209004012680500c40d20702030322004140440180408a13200011030743c2a0042c00401c02500c0e250360086100d94014802800818004500c0403203c000e81c410301da000b500103100503950f0340103004055905020710307603e4482212542005040310001128100301031400c1040507900b80c01032080c106900111041d01030f8120a490004200641d80207020350b43c469200e01c405040aaa55040b6100190302e40807066a9280811605c41c2c00035141000d0320f0920407032034047c941c0c40002c2c0100400840d0290041580592103400345000b550b0400422040d201c1c0300c603501d034040c3c143d0b444200d8059241240c0020924801c000780c4013282003c07030080b480d25103000c40c02e10148001032426607441000525410f142c05980c4000c241d01c000e20079000c0f44902c45810b00500311203402d40640c803104010030030840c250202107500003880383e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 854843758 1250 854842508 854842553
    0x816120506010905040216051608154b040b2706070203070203060106110705040207060b0a06030c1103071e080d1503110111120f090a0306050106080112 67
    0xd4600300121014043d603403005411501c0001c505d90b84200c0804c03204603160103002201c01760360f043d064280e80a8017501c40c622141d0841c8040c5100051000380b03c54000d600c0c1075a52556001280001055020303400c00d04107010012410384590340c1c2c0c45845c40411071070503040b00c2e143d40b401d0348411119880080c41d040c1c0d050ad10790f00c2c40301100c0c440758075000c0b0300303464104903a03d9181c89600070f5500e9100c880181c1c800d100720000000c11500c10050044021194005850590700d007038180000794014802c21901192038602c0911980c07264022403005000560b4041012640d542025015504810b00e003c21600104202e4000c5102030500001c0d450031109601c2d0140d03090b048c42d1180c1d00403250450400ca05014501c2d4807880401200000d60303009103000c1d01482c04000042d00e8508513002400115040078410030b90403400310000d04888080d0524103032400703040c4800605000c03415081241d50f156920b00503c00281d1005c0c5c1140942080f02d158140e8a28945511050100016407002c508 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 854845008 1250 854843758 854843761
    0xf06010f111b0a08030304080a0e1c020405150324150f1002160e1009021207300e1b0607080904020927090d0509190b040303050a08161205 61
    0x26250150840000d084c00e40c1505e441c0d0600d8580508140e000c004614002441c0425076034031031502d40b4000a1020070000050b49011080d424003018100041100b845582101d030f0002140d1400d00c404c60680e4609288900308002580c00c50346401c0c009808030702d00d54450b42d440091031715840945860024121100305807022400001c034030f040c02e281d00d40440d006110070f0000781d02d1a0b0300300050103041002e0258420079200e0702d0110803801624448407035203049a0101c2e80036401104609401c1e02d41c011410880700e20f140c048030180b44004440d410142e503480e100e1080a9043c8001001a441c4070498108076804000003003d030b014912000d007050000040419582e41c80364115110404040d005243c14008400000d442c00302c000c4400c441c04c00315400244844501041d555a0f04007541c81d410b003031039407803030910802c00c03d038200c0d0b85c1c1100f059000120704040c401e0080d100540c4203a0b210381e0b4520090400500442002d05800d41034240c0d802c451051302d0b0403840c200d903d080e0040c000240ba = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 854846258 1250 854845008 854845063
    0x7020a080f1b060115021203040201050c011b120b0a0b070b0c0904090303060608090601050603010902130801020c03041a0c0d11010213090c140306090609070c0b0f06010f11 76
    0x542c811100d1030030b0800c1c0c0324080780151010201e03009040b95910820702e6001840e00e0002e83e11100d1106a0702442e5000b00002801503001d400600130300c25400c800001c0f509144802040010726440e50303e40800c812044040d95860a4001c0c100c1442003501c807070b507000785000300840840c0a5000020324025008000404010803001940d49034240200f0500000105040190040c112801a01c00003040c210004001c1d100010b241812994080d090074a168a414201402500002d14050b5a511a02d0001841c0c1c4000d001030843d103c2c6c14006960358516114110b00b914008000b84d81d20704100303004000e034050001ca03e51a4003503d03820400c20351204140803600a10401010401c0d4108070a80403501d10001c7d40b0030302c5105c1c52034076600d641d40d405401c00d911a010440d62581d0200802d00060614100b11810503040700032824440c00c1342410355101071b07062a0440b01081d1013419801008459a0b005142181611300c42c01c00183c4680ba0600c590340310343e02d40e0b140d4041d043c102c41c1319984 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 854847508 1250 854846258 854846287
    0x9060a110f0105010b03070f17060103020901050708071a010f08031611030609100f060b040312021f0207030305011a07062a0e0f1918020403080406111507020a08 71
    0x100c0003181e20007000a0b40e11a0004806a003041d01c000c00002d40342c10100000500030030314401c1d510401400c0315443c2e078071400114043c1d40903d202a04200003844030030009011003007e44001845810980340304100c4615001d414041640140c000300d0701d0000402c0010f401004885215400d21000e511024450501004420b03600d96080c0c0c141c42090100008280c01040520800983e88024444489c0e00700040c4203031940d44c040d49200180401c0100005941c01c103411102464030700503a822a10001844060140c1c58030403618003036000900c100c1010707814071949000d032540307808142c43d040340d0720651071460003500e100070061582c4410005117480c039014403404002100c21100f034005915000109030343e000d15801402503800c01206001071511180710441000903051401c007a92504014503140c1000a0201001650801c004000f04003490300030400344c101501e48202811030041030524140c1c10b10000d070130f4551107900340941300351301298881140340c00c04900d035124a05400d00d0b52 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 854848758 1250 854847508 854847523
    0x50106050a2303010b0f061b01020a1d090103030c0602030601021515030c0d03210209031c17150f12010603050c030f03030115080405010902040501080714030309060a11 74
    0x36400034101c0000140c001144070801107608491074010182c000820a26080c1c4076600c03009580a000540307406218141b4001800048140880c00101c450f15843c4003401c82e4031001407000084c07010041880d0328062104100b10542e02540da1080941c035648000303003101f510a100922068000011401e80d078401c000c0b80c20580c4079600d10011038241f03501031608001900025078068020000c401c0c0080c0781c80341e03880307003065056250044c1e191514400760b11000203951000c18072590a0140310b000e620200300c200200c0b660b550198800002c460301c05000002c007038888030140c04800d410007200e03242e0840d60001c401c9c010364102d0820241400000c09154503044c0481c030710b6280c643c000003442030000714606c90120035801e0b40d144017103003840b4035200d2009000c0c1505140c0c1e411003417500039105685040d8008c1c010400020200c01c039500050030707a142a84007000980c03051005008100780c0310320025049000700d00031480c0801e03400220f903542c0500c2d0202ca0034014551110403003000144800b1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 854850008 1250 854848758 854848769
    0xa02031b0f0d09080d0206040f03110727050604090302120a090b030906040606170d08100b0c01060906050103150b0702040b130903030b0405132604082109010516050106 74
    0xc0e10414002c0c840206200014800c0600a11882e041c10302d60f80e0001c58810700a6801c14948804441641c9040e284601c061302100100c7c82036010000f04040980910361200c20000c2d0010301c40a50100c540040d42c101800c424895441c040d00140041c0d000180354110003100c43e06d050700c42d4180c040c1030b1420126a03102c548809000400c108001c0030106a1a105502c552800c1004c01c0e01e881e84810714661b4403c0c2d5000303c0d03010100808406010780042c070fa07c04d446003040b561080d00c3e4807418500342c00c2040360707000c40d03034540800384000407d6000b01c2c0c01418080c40d0806c0320b03000881c1c102d0301501040c4280f41611400149034019515280c04c400b00c41240900904c02c0d4090700203800d0000d2018103802e80000c0c1c980b1540400f14a014018240a4803003c3c0b41341e2000e40d41600c0b20104151850a00d1074000c10700c80381c4848080a81010700004d120f1680a088642c440303c5000017022403182000c00d0b5100104440301550b130700030003558107407591360600040e0814603141030cd00419454000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 854851258 1250 854850008 854850013
    0x4050912040b0c070f032a03140a030e09061003110c010c080a14041110020c030717102a020f0105010b0711030109020105091504050a12030f02030a02031b0f 69
    0x71480d0202d1030010030390502228100d03401a69912485410889580802840403000c2c1c01820044954080707401301580081d9414801103580341d542051500400324810582d03040f600d0104107043c1c01000503103052006403040805441d18100080314103484e110042c00781903440e483d84e442c1c01d0101c000ea400c0154501e0007040304800c1e11030054030801d400c442c4000c0650904412075100504ca40c05903005692160400703403803114040c01c001c9242d4201c00500304600c9016281100c1d40e03010000c0c03600400903a03040b0107034011801e0100d804d00d0b51a004070005241031087c1328140800c0703103040c0007a03801070587c50359092084507001ca0810418131960f134181c1d82840004506008290002e20440c2e118661041d0f4190320201494280e4107200300107404190b0907c00040c0604120110b041c007050f5108003149029201c1000952810554110fa8040040300c8100d0003015080070300701c41c0c41c0002d40001c40c202003020400a580380700f0120b40181d480100d4003403500b524002c220090598482006 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 854852508 1250 854851258 854851267
    0x50703020a0e0423070b03130f080307030e0a1203090203031201060302030a0e1c0302031801091104050906010e0606090604033003090c0b0c0325050105101404050912 73
    0x900d8060300405440a075550808110644c60940c9082400d00006840d000a0f0130b0b1185014a91003c41c2c000610f402030b1400b4481c04640082d440c1012111810700c140344d01030b1a4280110014110750403075501540a901104018001c2428688100c403c1d64040c60003103510f4089102017800c6014030896645240c0c01c000000c40c001b0f8040d00610711480c10140100500000c059803940d8070309400381001d81006800f030905410500c070350001e640c00451104c204600050700c1c030020f401c481640d00d00303507101c0341092074a0349585064002c01d40c2140c619001852107505100d0100039540016180f580300e500001811183d945519007070354001c41c0c20403a4420f410180b4280381c075450b0200700c09502000c01d0303100350301000350091040015441e04400e40d220102c3c20480070b45e80716403110101d05043c2c802031103200b0516456120aa4480d0701008450440d829103181503400d642c1c000d08030b00c7c60000d2404007401440d07200060941c11120480d03001c41d09491b0400500c5c00d001d00d0180c04036400341d0028 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 854853758 1250 854852508 854852519
    0x60605070b0703110a2309060a030c030615120b0126041a130309080d02030901030f0902101701051509012105100f08150103022814040c110613050703020a 68
    0x481c21440502e401b0f601d04002820203441e041c2d611a1880c02507110100740508440e01c1d00c07030361103011511803d00f000078080b625607621b24007030b54101c0306040c001084800161440c00c0c0d240111003140f002800c068020341d2202d40d42804203940304504170501c1c000c0c03c0005080c0000d03003155140309460f40e0008403a50900c25011480c1c0030b40140e064011800400c4001000000090903052080f00e5a02441c03d0050381001180500804405d81c88070540b15a01c59000d6515901c0c1c5401c00d0000c1d403140c0420703420807140d1308a0450140e2140b072085240b20000368003402004201c0f40841e000f443c04044042c942140c1c0c400002c031403a41140c00710328040822021641400815056640e102e503903840b215076601d0590340d150000e40100c0d16182641c4010030060412940341010040c50f808403041002a00101600320070381548264010190384a55070080c1c1813031b1141883d4103000d071502006ca802c4511010b643c03040041c00c0410b0030040311003003400344542480030102940d03006100f094005d5644 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 854855008 1250 854853758 854853767
    0x309171b0a12300209040b221109041103011e12171303111e0a0b0a050408101517150606090d2306040506161713050105010603060605070b0703110a 65
    0x41758400e000b103141c0090b1144514000c00101035084803000e494400300e041401c1140a080035401d01c8100c1481130080c40f0866940d80141038001500d004444d03229850441a01c039090309040d840560200e44020520070f00880b031001004003504404440384040803540c10954610440301c080700c0485000d000801082103140002409400803243d035140380448000094882010a503030962100c1084c5040011001000151006140d2410950b090030b40c0c82d12104c4c1011021602c1c0f074003040d03407080c0c6441406000801c25010342140c000f40e0b8448150202d01a0391509002949910084802c000503410b80d9100222824207201601411141005280400c080e9142c003030403c40340b482c0c0340c001c04240329000468920880e0803000420440d21802c0038080d007032043c1c07903624042006140080c18500d401080080c01405a11484022114282402c40c2101c1041c1c201100301030a043c1c1c204610350740402603031515500202054520f88820905400130720880744414034041000c9080f50007035820 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 854856115 1107 854855008 854855017
    0x806150d2d050c010f080403020c0120150402121207060f0b120a0b15010e01030e150720030a1205070309171b0a123002 53
    0x25004620103070588034001d85607a40302440d020740f59680000803440f4420315113000c50841c04d2a82e0000d40f90358034400c540d810848810794400800b140909070350042c8a0036004c450301c4d03065407403004e103170400110b50581c4101083d030800300740e500c4003088004c05807904060700391030400140c0e80c11004000c2001d1115400e40d50b5031030520580c0301e030b2102428403040c900050040740303801c1c43c10030200e4100408400c01c00480d481d03040c201d070760460441e0003880e0007401d010414100c08451586860b07000747c00110480046414440700d5034100710350507400012030711000c0000e00d10010640c1d1342c1c8a0750b0903d9001902c6960a403509031005d50001d40c00001601c3e000c00d020402d52503003000d004e62030415010748180052046003a0316849001c1c0d500550b004041c2c403600c0d883c1e44441a90310480040c020074401d910003c04e00d0014580070410300c0c541481c850b41980f151040303054009402 = true := by decide +kernel

theorem cover : BRFrame.Cov 854676258 854856115 := by
  have h0 := BRFrame.cov_init 854676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 854676258 ≤ n) (h2 : n < 854856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
