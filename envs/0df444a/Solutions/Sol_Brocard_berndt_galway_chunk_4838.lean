-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4838
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:54:17.683418+00:00
-- url     : https://prove2.me/submissions/52c80041-828a-47c6-87ec-5b8d12e908b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 869964028 ≤ n < 870143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 869965278 1250 869964028 869964041
    0x1512201902161d0a0f060f210c0314011b12150b07020d060209030a060e0c0409080919090609090b220609081204060608190503070803100320040b04 65
    0xc03107001c40c07008400d880d00b1000d20305600c003440303400102d031940c11705000d40161034081d0442c9000c3c029545040c4001d28200551a041505181c05031045114507140e010401485000c060720040240d200b40c10480c0b0250401c0b0b1800301200020700350030300d41d4900180400e54040749152400d0604505190480c00c0002030300a80b10418642c40c0f038020b00d58200150222039082c1203c2c002d80034080d5411569080c09000781041c05001c0120b120740d041060ba5040c8004d20201703d100d02d21f05030410000c5072401c42901d0340c3c280c0680e40e48002c9400d91941c02c10340c500c41d0340b001c1d21403030401001290340c40d00340d0030a1011502c104030900440c1c031001d41107131000103000c003044801402e040c0100e01184081e0040218107000f8004145020a480c4a00c170b424041160b06860458481c1d40c03c020101d03042240401c0041140c074500324140c2c16079121910b0b44035210003c1e151007004000b00d6007410b84000c0c1c0400840e44655000c1585034003031026402d50000a05061203a80b0340302e144007050501e8010103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 869966528 1250 869965278 869965289
    0x102070906030b0708180102120103300f02161d010b0a0503070e01051909050307140d020f03070b030a05040c05060a050904050a0b0a1806151220190216 67
    0x52884c4d1390b1000869210000a182c10304603441c205140311604020b100500c68401c1d0a00500d0096045040a20418440c1040c00e10f41040b444140c0e0154040c0b1111560401110f203080680700d00a87d00c202d241100c2c1d201c0070404400b1610f80042d0307075111800d6074054603804403101c05550f1b0340c41050000c540110300c042408544100005480c2034030404112440002c1410302500301024103584203100340001c091580800c1d8041d00a109602e0700b00012001000917021191070812504003003101000c902000900982c0c846d1001000c95500340316038405045510007060300d0b40380980e1514080c0c04141c07400d0ba410303c0d0000d000b0801d8180310048270003008658070354901c3c1141e04130034000140b0006081c004400c0e903610950615944164140c03000746109808010800741c103a402804491f0142d0140001d05500001c13400d1098210250703081c007290222002840c0300030030200031141c05121204035084e99000071001d080c140c80100c20024132403658201c4400000036400000da40c10302c2d001d00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 869967778 1250 869966528 869966543
    0x51603020c15100e3310081b0a050a030c0215180f1213090614090415110d0e06190e07030c0308030106020d030501050a060503092406010207090603 65
    0x65051280b18007068a40181d55810002025561240505040d540035030314440803100b5503000d84001d800b0944241c3c00d03408080581001d200c003850000780c01401c0401c14505004980c1c0002e21001d1031820801546441245130035070f105c505130300007016980801000710100e45820000303100c143c030000c0c0158129200002001040d12001414440c0300e000703041c000554030815101041d6003d06001442250002d4500941c440789580c0041c03280310020782280001d41c3c40d00e131040003070000242402400e04001d894040c15034895007001803e8a00a0086196050501114401c1096241c00404050f103001408200280200c101e05480f00c4040d59940c21400e0440032042e07031032446601c0303202c187c11264100c8074501d0380c0c0c2c1d84000e4100d480341d10507180e080d80440100149c6405000904450b2860301c0c040220350704040000384c10418a0084404010001c400901552010000c40389900756081d041500502e0707000401c13590b03290403108180140205400054012074a0150308281ca521607507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 869969028 1250 869967778 869967793
    0x22030206091c0c0308030709060e060703030c2606040e010209100509030c180708090a0302100903050d050a0506011b0b0105190b030108010e070b0a0c03080a1e051603020c 75
    0x400506103610428912014109404100014604985600114420450180c403491f01460280a03194103074000c0050101c1c1c2514848650b8400d01140e00150f41810b00107904d51000804840088600307400c0c4034000c18a41c42d4a8542d40840d41239407041c0f2007140c042c000c00c504250214240d008a0722440d8009409103200d01266010354060040b454000d0101d50804504e0f2000540344545196800c512401401c00d00500c1d81d4007080c00c95220030004000d0421070070b540d800943c0c404030799065001c8030365501081d00070144100308841030210030610a00890a150084100600d0140c130f81c940030030f00c41407400000c00401040507000c0d541140600c100307680f0700024003110f1141e210350301108001014010036410040c030082c601800c00c4500019440c3d00f06504107282168a41000d0f55007074003030111740000c65202940244450b410b152500341030701e861100c280500401084649501044221201311088560141d4400c80103c00380780c1000000040690891180140602581d0071011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 869970278 1250 869969028 869969047
    0xa02070611091c1506030605040b01090c090605250320010b011d0a09020309060108061b182215090501051f02120304060507020f010c2c0d030522030206 67
    0x140050400e00400965800c074222130710340310845002d90000c80701030b50780f9001e00042c040d01c1054140503090f1100304005103003050700003030000c03d102d100345001c0001c002801004440c0b034214038070b44402d40705962400348100b807401402900c2d05840070b82894200c0c041c40c01c88ca8005004150281406848130180d21901c40c400b0001c4002035145c0340d8110000300c100145405091008510407403880018102a504003401d181c2002400790260520200c402000307010300304024115250151702004203e000c900038004501c241c0025448140c001d825401036068140a5420007903841814105484940d52241c81c0c54044880a00440750401c0e503080030050140f10404c0317012000400fa00441d07084419501da040d131b49a104850895040f500c0e07505104c596034042000d00d0002004134024030581e091464001d02c1380700c005400061000c1c4003030140c802d540c62081100800800900070362500015810040c005910244000a05a099809516499004207541020340350700910280c40d105419 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 869971528 1250 869970278 869970319
    0x30106030911060409090203070b1903020d0b030a0b09010b01030203040c03082a0307020f011110050c070c03050f061006090308031503031206040c020a0c030b041a0a0207061109 78
    0x1400125640300c0e0760005201d442e50b07043c01602c01030041d000041040300f1144103040c01e00c81d4603840061290300500c501e00016800c4442104440264500140c07510307843d22551000d000c031180250342500800101c6004e0004480a140c40340702d0920081c01507041d201c0c0114201d20007103a025001904030790f82440001e0140005080c00034215002c0080d0f106d07480340042103902e08200d07a140c01e40c8001000310441c18520818203c0c02000d003005100701c1c0904141c0b648660036403418442c1c950b9240c0c0000c01440d0600107403032080e034000011030f11490702c0345401039644100c0000581940300340c0000a041e0625003000b04243e903510398039070944910303540c0c40614582018085600d660708241c5000c100d40c034100302401c440a00c3e00103050741414110705200403100034100da0b0013190003408544011502d40d4aa060480fa800001440c4940e42c0341010400d0381460702544003111651814002c02c41c9064002c0c000701800790100704041c1103070071340d49111849190491500018520001c04080c00b40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 869972778 1250 869971528 869971541
    0x10306020d020c06090a05010c031e0c0504090c05070605010515070311010b1f0906112107050624010216050f04140901061805040206070210020a020d0c031b0b03010603 74
    0x301c0250400c415500b0150801c20308550401d981ea2001035943c00b0b0050900500d03103159a1814200302c048a00448101810211100e00d0f02007078860b5070360342ca918400d204640081030a02c40800445c034454500a1440c0d000c61800d450303190519001041d54a00340036000e501d80c2d00250143d10f480100d5905aa0040100798403980c41d5603102c0381c6160a44907110030550b8003802014464100120300406800044503070407010402c8845c05d050b075040350000131031040c545142820007205c1c0c202031004000c9441500c038014464058081401500d02c01d41d880d2031080002511134814082e1040c00480e600c5101c00041510824029020012820070000114021074090004144a010f180c3c01460f1580d040e10b01d01d405a5480500f0400d03601c0e01d10310200380c0003680d0410710050425030002411070181140113031003032000491001d01540200044401103a02a001404500181c10080b000d104103110a803032094048a290f142000c04c80d08140c140c0e2118020349095908010086008108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 869974028 1250 869972778 869972797
    0x10515070b10180504260a03110403061107030219020f011b050601060e0a06090506041406040905040b06180603070e10090203161115070e040b27091501030602 70
    0x142440101da000d14030780440d48400070b012404071362814280b07010034101c0700b9414402404801c58043c1c4c0d40e6000c8000890789070381c3e107901d80450070503848003c46240740300f2540002c0210f4581403040c00c0a6610310081c001d8580a6000d4541240f11410412001c001a050003580039a40c0c10310014250300401c4000d081e0141d40207104c00e0b5001a50300c4500d031032000e0300103401140740d40341c801c0d4080c60800202c1e00134155615004803080e14040100c0c400c0e010740d00684080c0841d01038003c5032034440d240ad44008050094050001c3d050a040980c07080005031030b62070241012003603050700140600003260181d400a0000d2111600e404050240510003524400141310a180d00090030903081c000707140640c08000b000d088041b0f14000c0a0f03c1e41041050815040c1c20410a003031190003071101d00d0f03a1101090070203c100c1c500500002e8020200f03100984e510402000164448c9002c0034540351134405c00100704400d0780c550003002035489901c80010301101c0100030050002607810340103816801c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 869975278 1250 869974028 869974051
    0x80f060d0303060b03150f0f03032a0a15050c03040b15010e0a030b060f01030c1202030a0b060f0304031d1003020f090d03050309070e19200d14010515070b 68
    0x5886031980c0b6813030ba2080e00c20758000c0c0e582481116031847c121141148085c0100e902c5580d41843c640480c0c0c070b80c0207140c2001405503015840e002c59031841d92041c15040b00700307000e40c0c440c0007091619044071a0003060243c20349107088005401e02c0c101c0c004481c0101d400c00c0b5800f140c0d0741d6210000c9060103095800b64108218201c0080759511250102000307144102a5600701e440c01c4410702028280041000f81094207101d400c40740d40d0340149a64290300e0f4a0342016a407555500040409010b240c40066001540011140401c40c0c1c0500a1800b85102c0da94038451501000f1200b14142030016420350700c58420f40f0702d10b0000c0d01a030300030080b0090221a00d03042072400c030002080007803890300c1034011031000000c011600e1402e1007614054035080c03180b41205d08100054007066054514510015507aa0900000c4a031540c1002c2c41851450900305a561581d0034400002e040da811041100c40e450342c002003014940072080320850400105554184030041d11504003121014000070107a8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 869976528 1250 869975278 869975291
    0x60a02150c0c010e0c09062e0801140307080c130e06070903021f0c0b0703090b0108011b080c071721100e0402090a050a02090402130303030c080f060d0303 68
    0x1540c2203298511400309515010b8541c2a0410881d0039a070062000c0c1129400c0f64031120901c0d5074a18019030014800d03180420000c07140d03110341c042003419810302161100032a1800c10170a40c0007000905803510046001c0c0c89054810516030344030950300a0551a8024040004850a1141d4090300c42035413a00046600058552224100601070b50240c00044003c407080c41541003181041c41070b040151050160008916001171521100d05001401d83c0c0030900460b294600c01d030024200345030230050b0510603580d2102224004d1200c0d8117401201045c900e00d01030513030b0203980100d21400d80c032a0340e5841d0186507907518030106d2004400070032460b801e22030fa00884142035030300c070324041e40040d002a1600f4184814004c1c149150f1285200c035900300e0800005803a5282c409800048160010426440e0008500f000c1c0c0251504030f5009071012a01e001051a40404201124043e4504104207400c400c81151640802c07a2070301b82580303aa0010410b60f0901421407034180c1e00138503000074003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 869977778 1250 869976528 869976553
    0x70c1101090314010f060f0b0d0207030e041a1005120a0e0102160605070e060702102d0e10020c0904110310051e061e0405090111132d05060a02 63
    0x10300250f02000e07080c1e665200c100d0300f801e0581300f004041e025010a500b111b42c0ba1280c250524850070a0120020b40c01061740410107028140281c0e0384c000080052004440c0c1001d99030071142e001c0c10b0188101c07080c10080e00d006004100329000c1c0503103d4050340490f038031490a0303000340c02c030f289049001c1d48d0308008000142c8181d584000303c0e24030500f00818036084c0110024140862306801511030141040303070b007005a0340c0c3c4402c2501580030381826280b091450803252400c0e180181564039000707103d04007a0f103595000c40d0200b9034500465942c1202580100120383d5010101c10282d00044020003060125580d0806242c80010040444804d500c1c039850b0401501c00c2902d800810507807036600a8820b9140520181c0d101e4400c2d00c558800c1815450140d8000000807009409a903485010500104017034200d401844600f0090340d5803800e07022451941050144038004130034148419288102031242030042969415803407500c555405c01c020403006501c40a04207040d03108140101d0390 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 869979028 1250 869977778 869977793
    0xf12030a05030108070603060f1203030605040e030c012a14040b13060e0f10141603080f160e01120b1302090f011b2409060605120303070c11010903 65
    0x1030440103540c5054895143c00c852501c0c001c0076412040605040a506000010200d109031003250071060718444d11a000c2e04003030300100703144d40095070024107101402004440000080c151060464020825030b02c3c1080400034001640d1411515051050352f01d444161160321012041c07907640b40c0761452700e035948500b41029404000354603c107050281003000703040d40210f0b10310000113042d900c2551504009c0005440740d50001c0002c020302440541c0c80c0d8800422800ba946209240a0b00d0f03501000c803424090b205210032039050240b80c000b80002100304109000174070071030302c40362201ca42d85864940155481072001e80405040c40e5200030003420703540d80d02c001240d0001410b10040c1c1d41da01705000e102d94503440c000120706100407015500f41c000c1c1c10710380840c0c2041d0044005803070381d000e9500201c20000b0070040c0900f018100880102070101c0c950091003114000c8079503a0514000b102510740360f00040b0b444101080f000c0d1482004a0706096241c1e80f14201450010251350b180e50b103884 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 869980278 1250 869979028 869979037
    0x6101b0c060909020c070506031801020409091b08070306020d0b030a03080402040e0d1407031106251d190515030411190b070203070b030a02030910020a09050f1203 72
    0x45441980c6941000042e80150607407010349101001546880d640480c2d0560340d1040d8803c00303000341400000259500540e601101c0140071034002990380307603510b01d80603014042080042d10300c3d0024203c540c2c408412800c80e00308803200328001d006918074507280c4000a4002c040c1c1c0428480d1152402d401e65070b014401100d969100e500c4103c0340e400c150040c00111810380018403855070002c4440e0907815000f0040800f9841a028215564034240c84c0844039400604421003c91103a8000e001c0098800b01041005904042652020380000304049440c00c840301c00f10b45480034254a6010035040102c52007441121000702c1502c0390f130b0b0343d10104402111540004040441c0401031208200080c8085059194110741c10080e440d0b106040760315241080c0305003010030200050220454030705021741c01c02450081021034507450300a03044e1000c0c2d4000c035140c200ca030061010145041019109a139903240e040e41d0b4441e411410301052120117070100003d01d9011481000780c5040c2c400070030080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 869981528 1250 869980278 869980283
    0x705070206162004023a2909010308070602032703070203061302032a0a060c03180e19110a02011512050a061e14061801050906101b 58
    0x4259500750b142c0f61003903c0e120358035014421401008000c0440441c054040c0d5030b02080b420710110180703542c0130544002201008000c0c443d09080309112203003140341140141a40350303074441c400d40407941c08001c0f40f1102404010700a04050200c1c00208035a175003d0360744442c2c007110385000d01c20503620f42000502458800c84566100154000440c00c00f03000050300003d030801d8004900b0310035030000352590b042500c00c010300b100c0180d250410006018a03102103080203440e20600302e40707034080101400c81c0a0015000f08034903a09035644196046004000c840100192407040d85508006040f00e0000035002e00b061511805c26800c42c00c482c10040060020390f07000003400c1c0002059007064402a0350081c400b070134401040b2408651301095502d440ca0b4041400110403003000c43d002003d0040407131080754580b401380003418410f0242e14084c094031017200c59142d110a8010000b028280900809801815000c0465601d05080c4550451010a13040070250501c14010b00241c010380d1000c02e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 869982778 1250 869981528 869981543
    0x1e021201050702121c1e1505031c120c0903020a1e09021602210115060507030509220507020f030a120207030e091515090f0108060f12011d0a0209070507020616 70
    0x908444046d24818583c0d40300d464066241440e242c100080d40300c84403c510a5015041040700c801c56600c181e604104060800c2400c0020112003400282015820300080b030054000c07070408148440003114800d040c641081112042d141410301c1c036000fa400000c80140c40030240d12046d030060b41c0701c1d1000312042100f400c000b04882c420a00700c3e804c1d0754554102540f41e8411842c01c0c01502e500ca0101c900050301810070590b41c20030ac502040001d29412074080074031480d1589501c050354642c10107402030501c1d900303c171414054a0310040d180c4c803e480c04900481d4105c1c6030300d800d628054000c2c0c10b542d406410319840805400c0085211801d00300d4030140600c043c1400750041d45013049540c6181c10100c2c404a0605071050082070f140d102c6100d0b0076060000c0100000e0a65561b442d5581d01c961000e4001d0f143d401242c510203018003000c07090303c03204a15120084001d074030005010710f05180c005195407815115140b040c0c41d00e900108050740c001000b00844001ca408083c040c0c810903205240 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 869984028 1250 869982778 869982821
    0xf021504090e10090323040306060806061f020c120c0d0320060601050313150c1d030c032503050115051c0210030e03071e021201050702121c 62
    0x2801e0404440c101140e218600c0c1c060000d001c03c1d4002d00e080d20b1407031006c60200081c1e0101500c1c800601440e40300520b4036040c400c002c502040d020841070700404007a200c0800d02c6841100c94001c8668840c40c12006038012441407000d4580083c0c60b244102c01c00040d03800404c0340c807000c0b682c1c008008000750081078410b58426200401100d400da80d0464040c0544114141000002d006200142007418081480c4202c1000c4c4031406d0072640202c445800108500402c00c8009032140e03e000e0025824400c2c0a002c01c025410003080e203032250640100a841c08050341031900710b2012040882d00c60100101d440407000500c00d2060500d42d41c00011440c800c1460141041601c940d4150505507169084030400c00588440300c2c002d059800724140030849110f080422850360156880c05008200480c1009400842035006841500c1c000e44460117800384180320a801d840040e200d250050740454000b40b020001100540301c030505000e1001c806001034103040f01501c0039000350208601d003800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 869985278 1250 869984028 869984051
    0x80a030e1203030601081302060d05010306150b041d070c050d080f16020703020108070c0f060c080f0c0901081005090702060711010605031020030f0106020c0406120f02150409 77
    0xc0c94001d404070500290702d0351502c0d10000b84280c1c80901811110710001e00d44604558440095034021090001c017003000c3d40e50b03418040c000d00090507224a25520550340850a29555002c4801355200c2498900007416014909404607a00400080402c0b45d07003504503000890078807010500507a80d5669000b03600b8200c035000c0c1d00510251469460b41c0c1202101ca00e601d4012402c5c00c22690242042d02d0640e44440b01903035580c0c0d9201000f0105802400c010b0b0070070071036a100014030720342640d81c4001544c42123628980c1c501c094466075001e05042c4921002588200038503076100280706c1c148241c01d90f55402140000c80107444440140e000b407000c00880350350040403401d00c61001e0000b13002d075a18000109480d032030007801d0100c4a07a01c503114041944440c80f04c85001110040015941e4600464041160002030140c44014003a1030200d01c00b61820380039034401e4602002485080c0200b07661210360b0241920403c0340c0201c03010301c584080c1c00100340500003e00d142240424400c0702d80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 869986528 1250 869985278 869985289
    0x206090d05030d0c0806010c020102061305033a0605060315030304050402031302091f06080a0e0304080f01050f061509031e0a110d030807050c0307020a060f0e0405150f0109080a030e 80
    0x6c0545040000340d015000c0581c0e80041c1c1d040d0440505008180d4140720341c10454251320600100ca50158144103400304920745200882d0049504411800c80c0c0844c17412050042d1840d92042d194400c1c0300b440421141c0c000c0038800030004600508903464103075a000402c050340c0049a46c480349004007400c07081542448460143c2c4501244500e039070702e003440c400c0910328041a0107120700300210600001c88400469114088600c145000c42e52590f6032403100503135852000000420a50800303001c1440c2e210040c80c054014200186140308419144031510501e801c50b4490790fa041c8220500000b0003a242024892420389810103854110102c2c200b0780000c0d1100d00500b070160500104202c0401d0f07003c072105030003462a1804940e030b072070001203c40c514020210302a50000071894009400c41d0820308402d50301241e900e803084c00c40f01c56810001100c900300c607822070b6280304040380f403440c2c6002c00042800c448141804005140c80b040480e140940700003007100800ea1950315083c0e80e00d002c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 869987778 1250 869986528 869986531
    0xe0f061807021906090b0a0531110607020d05030408070e13030f11010203070305070e0d030903060c050d090828141b011b030b0105040509040206090d05030d0c08 71
    0x4195a0040c603050007180250703152020b84200380350400070b081c018100301042d001155003030340119031082c1d20305201c88504000c010a9444a842c0f4100402c2c0c60510080165a911645e50302e4100045c1070002e6211004000400405c05900c00001c210f50710041ea80c051010820f90f00810086860354240700034a45401d200c1d422004400b241841044800301444c294900ba00398103181c000d0445040080070b031a0009051007007040c5500210801010310b0307256020b1413180d80c041d960400454010030a10000710f0440c040600080c2c50100c040c404a059500300c0203c2000310314140d4a0301800c038801ea4200c5400d1902200c880c1d0340001d490400d1702e808000108114090a604400e514510fa030103040c8079021542811040c1010403840e030241030091504484102482c0203020002610f52a156110200241080442d241c03030404601c03948280309803003c1d183d01400709000c0d41c4a54003002036a4002a407a03903070141d41450704c1400100140003802c840400201e0106200b01c1c42400034000500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 869989028 1250 869987778 869987809
    0x8012f0f07060902060c0607050304170408100518030c0f1002090607170702040f090b010608150910030609050717010c05040b0c1c090512030c1f060e0f06 68
    0x1000c0c0308050060105000700c88980c0c1c0d0203140081d140800b0b2010070064000d85005102074000c0340108916136401c000110b204510030182c01180100b502100000c40c051030042c144942c2c400c1c03031900c49601c480d9025603001a0354041040185803801512445c66008004040035500100401460058104104010a9410700080d4249007408012683c140200c90015100c2442c450b41028488900d1045404080d004bd109000110703e9444c5000a480d07540c10466109180000005203d0b10581070b4074001c000401c2c03140d82400070442040440d403405040400070303a01701c400000c0002c80900c1010502c5118101a000640c82d0040c10038400e0705407074078003146034100484544030781c0d40718040f40c2c2911040d027806601c40d00601d102c54548030b0580700203000d4420706c1400107610342c1c00042d80350441da0125107500480c02803040c070585074041e14840784c02d00c0e441409402c860841104291050b200542e03070000f541643c5901020542c00e064460070784d10400001441030701e003861851009540c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 869990278 1250 869989028 869989121
    0x2011406010e1302090901150f02010b060412020a08010e070611010b0f01030f021b071401030209100503060111100b131509020d0608062401110a0f0c0801 68
    0x5480d4001800480b4201201c51107042d01802440c12004540e056581c0761002600300b9400d5a143d06003142140001c800220106291044e80740c02d95105002d29486414040c040504144c80c10b24101c10f242000b0404030303480503150740e0210704003d00744280d10007903000c5001004891315000014059821000031218664100340e14000c00762100038035a18168400c1ca40080c1c4480f08400d00310003070040c4010440d03500400c0318144100305000410000750754195000d105500b9100005408901c5a0043c45402c40c40d00c4a100e610340e800340025503070000040c10021045074034115814101070210003081f0f20070b40e0703940302800c55050102031010020240c64081000c50703285040c442d14510707503100c2c00c140a500001e2055001d40c05810400c0101955812115a03003402d85194103425540c040c0300e403c9006005611500b50311030a2442c0094290741c0c090030341181d5988850b200c00d400d00c80300792810041440e0008800100b4803e00c00c28a4002a2204621368210b2000c03c40049132212440c068 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 869991528 1250 869990278 869990281
    0x120c0d0609060b06190f111006030c05120703060c020c121c0807080a2a080f0c0306061902071203020f01140714180a0308040810090b0f0907081c020114 67
    0x54880303000590a03240303410003800001c6c0803031080355068081e80d07442407580500740d00c00011017110340101c01628441e02800310310315218002d1204000c00f0000c0e2080603803040e00d080011403001d610001d15101d151040d0b607260b0541c00003003144000c0300c0700021865803003810300442c0708419401c0900440c0651804500750f0070100402007000b040900914400c0341e80c2c440b80d28150700300710b5020041c0740c060020302404074040c8030060440d0104860900741800f40320000b6480c00c10600443c1e104000007012913091402244078000801c007a180d01206521030038802041c1c4400c2094464082c0d48680d00420384101010f40c11803c1d2100104c2c940f01c01000c10050109050700a04854800000c0c1e0456030740324550084407086503a00e0b07217106504240300c440c000c03050024120062007560b29140458001c10100ca04000454100c4003000e0581d4100c28003145101041e00c001e240c105d110582200d07140b90710303600ca2030b0402450802110760034942c60070100c1751903020b01660509260701c646e0054103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 869992778 1250 869991528 869991547
    0x603050a02132c180105010801020c03040e07030608011401050f010806090c070302160909050f060103080f0705101406100305010b0403060e03280e1e120c0d0609060b06 74
    0x4a0524002c2245001c0240142121a0340f241c05510076801c070303030601052500704003c9021681003103507035014103542802c002185640e0305000319448202e4100045242926100301115081400f03001702003019110301c400075540909001e040481003d245048410b945800100190203008404080c140034200c0d0030031446179100c04030039501ca00c0d00c035103007a40c80160380b80403820088640c00013041c01c21100400314903904a64484c00e0324078800c000712002c2036403450300e06942c0c0c4001d1100500041040084040c41d24012025084151081046410210546c003502d000c4e11100d420301c0a080c10354000300f00036442c01e801c0f504c042010760300303041107254104209150640701340d0101414980e00c03028410250201001161303183c20304420749509904c01ca0740f8910040699041c040009086840110183d2600c550142148407614a149100c00c03888010f0040c451103101010b10136015001c40480340340c51741a01c40442070721580d40050300d95401d10700002106c42d482e00f220300401060180f80c7c2c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 869994028 1250 869992778 869992807
    0x1270603050d03061202030601051e060310031403030108061b070212010507090f050306011a132c16030f0e19050d031b0804020a1512110f04030f0206090d05070603050a02 75
    0x1034ac0c109a03001810039203106056080300b05c03910440364001c18000100440624004145015203204104854140314110180c968a001c00e0090200c03e411810201c2c2d5000800d0310860a80d40d2154156820180c1c1d03500000c8a141081e15150340304e9446004000311554005214070141c020702240c7c40d203042c103084c082640e981c014061110740220027002c042c070302d5000300262080d00320318800f4114030350b44030002540e05422498000740c604030005e10340035101e01d801c00054800d140c800c0c0303481600101c254044014184516010301c2e681d0741d40c40380c900c03070440038483c0f0003044080d1058001c02003243e140003880c0045100c080e000301440e1a208007007001c0c50f80380541c410f000b030b4503080c038550321240000f0b401000d01c0d40c4086030052510100d507828070b0304251410a0506540c0c0200868010440b11000790301c540d0314146c25401007080103000182c0324004101f89140080c203002d0030580c450002c20080b50641030180c1c1d8662082c40100001c030b5050089030340c40303240320f081923040c00c00c240b2080d02d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 869995278 1250 869994028 869994031
    0xb03010c1b0b0a09060207030210050c181908060c1305030601030201020726101e0b01020607180f06200703170711040c08070e150301270603050d030612020306 70
    0xd01102240300824043c20581d045030900e2600400d0840d9520039030b24002c2d65611560391820000d134200000641101d04803000e44100390314070000c20807011480c10030801d45840070402d40300d07003c800d07000201d0141420000c2740d120f10a030585040d690741030200d090050082c5030b8009407081d0302c410010b00060b42d02059110840d0644100300c400c01d421041e041d84149803c41c403506035440380c40000d0187c00c1d0550405a00000a0003000080204002c524025140d101e140715025030f1164000c1902d141c4500203c0c1a0a42408180309040e900d0f00c1c94070080b82641d0340403400040500300d6040180107040c144116404000000b0b0400b80d00d5079039004100000301280c5540b002c804590902444520401c03c010030b04020420880070560f80c0c009003000501781d034418001071689800104904180060712074019200b42c0041c01e503880e100c1c1542203017117800c600030405010141e001000d040d07a4003940010b940b184001e0b0402c80e1108000904071303141d0b907018007041540030352000090f03240854600d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 869996528 1250 869995278 869995283
    0x5070512032d04080d0f030608010c17090106120809031606090501050a050d090f0c080d0c0b07172d04080a0c0501060b280212040e04051c030b03010c1b 67
    0x1000041c24811800419000fa984107440a0040310885600c066015010561a0006442c10071209407034144030750032103440801910206401c20000341405000f031580941c40024200040b4010352a014000a04103944900311360000000c25505081e103402d20040e1001d010081103540010b1508000804848a40c851b0b079051042c001080446140f08000b01c43e0070000703001007480501d001e850002c01a600b81041520282800c400100724035001280d803448070030280d9141c6540c036002e07072940c82034110041d0000c018003a580c0f034a1280c039040c440105202c0c9980c15400707111000b028010646070b2000000c0000054482400c1000003004c0340103070799070300c0018a001c40614000d0703c0c01c60b00400044c1c010040344080416442310014a510b81c414190fa00228940042c07140103505070307910405051210301078402808141700285d640c900b2503600c1402002202c12900600c048010000010030482000a40394407400d40107050034010140441c200d40b42c1110700c2103500d0100780c401d49108000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 869997778 1250 869996528 869996587
    0x5031b060702121303080f090f0f060a08250206040302010b100f0507030e090c071407030308010b211815070807110a051204030c0b030105090c03220507051203 70
    0x50301d0715130050102c041c40d40a400341d5600c80703c0403001640394021190045c41402031286404282c1022600d1700002200030707054604180038044c1c19900c45200502d003291051030301000da5400816070080002500d0b0b950040c3c10b450404e0b0400a0a450070444650b00900b12601c0c4034a1865208190000e03101c664605192500d40502e004c0701e483c80b5034284a58802904c03c14401100c1d00f41008140c00f81c17013070402410541c0281c030728540301c1d82248000350104207004010015141054000c103232114440b041c610b0000c1949a40d030310700b14000e0314061036002c1c00d200400c03080c400030007102440c1000e142400d50301340f401036402060920000c09050800652003000d0b0031940f000c100400c1d015074490309481051211450510340c98211307220a40e289030384a240014204408000c0728142c5601500a180b03e80d40c0783c2c46545140d1001d05400782440c07000540071540190b180325458990701c03801c081c00d240d0749088100403001144403203a0350243c004102507400b100b01d840c10803020b04d050564 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 869999028 1250 869997778 869997787
    0x5010f051b0c01231e040306060905060f0616060213030b01120302070f0807090b1c05010b0310020c0a0f08040f0f081e15060a0b040305031b06070212 66
    0x1114580100000491686904410004414400b08904064034420398a03902c000814000250918900920020104504000d4400c00c0307074161025410040d041482a0301c0c03d42d0340c1da920000c0310000c0d40600c840c0e650b40c509100043c5000c1c044061503000c06c81e07003079003400a08407041124a8000d8801480ca030350004040d1030742c08045404100468002c9003400c05982c1d00d070a00310000e00b03a9403084006004542c1c020034070f04000c2d007101080e510680e00a0065030300341564000180800d49025a00001d40d0003800e01d0300316500080403925201e10700204210344d0f02c0003450b18002d01079200b4a81d440c01404000c014910000d0507a00d0a500440c0c880004003542c2400c604034842e5070850300b2b20500005001c5481e04035082617a0491b10b4101c04c41d07105545503070920707015040e408038600441e000181c1d2503a4011040310403942044004011402103581c038401c0f0020b550190b80708503281d4001044651168000c9030001d20208032a0b4007030310b071034540090b0081d150301d18210800c02403100400e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 870000278 1250 869999028 869999057
    0xa150809100c0203090301050a0606170903091c020a0b0a170c12070c17091e041113030308061e2101050f0108101a04020702010210020d0c090f0b03010501 68
    0x11503207224440000080002e01e1040348025101d602000c8624007a60030070003c01c440d4a210302c02c0d00126505965040840b030b02d95003080508007809046105144000e11104000f681d40e840b0521112800140d00c840484840c41480740745007040d0b20001035648148850002c06411076030084550b040460b9010083ea100700207075449010f050541e8080d64640010020026000491006214000d1810901c51202c0300c801804900c10100c0c00fa40201c042054200c0705a6201c0d0714207185030700100040750010012440c1e80540e000b907480c03585510010f40b02001410b402141d41c5030841421b45021100384603010101c143c040e20400d000e4041c2440a403d406242e01d00740300b0801c0503003404c00a0045051080912001031028000c5e0005402640d540324810f0aa520451190b4000b00b02c9040720541600304010003900300b44400c0c0d040d40126007051880a6491000348403001403a140001e072803e8214004110020b140c2040e1404a018001071084c407000000303aa045070024030744204040640d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 870001528 1250 870000278 870000283
    0x53303070e041a10050f040902040b101e031b0c05031b0a0303050702030a1205090a082a070308090d11121b01091d100305030307020a03020c0a150809 66
    0x5030312004041c0d841c40c0600040001c42410380c507205008902e2124076448031040c034042d070036440c40381c16440700360303019030740c440382042d81255810a0004200088100c003160104001c042140c05480c006500040d11001c24503071074803603486501091804100e2000c0300d4506030140c4e0045005c003c03c0c0040e9207003076410044104104c403c80c1c40e02c0b040c14440b0700d20344100385903103000c140c0084001c00e0130720780041c1455200006584002d50181d851066181c28001501c005290182c109401c030b008680d061004180000e00034071034405204184030400300d031126454120340c4000d00382100c54010384020030114125009503410200704071036800f00310f41d440c503080c0c403510003100943e60000410f4080780b00740c140120304421074007040e601160148202d0744c0110380d14130b12402003401818504507030459205020044603807141d018486408213580b2a19903515680080b9284c00041c0e008401c52010554103000324120680d01b5900141c241d0304140b5501d41e400c008040035002c00c000040005c0601c0380c00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 870002778 1250 870001528 870001543
    0x1e160912020904140f1608010f05040f241107021e0117130f03050c0606060405060711060c07030f030f030507120f0b060a0c02040510030302030708030c0c01140109053303 75
    0x10f217089038025003801c100c0d00c1c0c2e81c00c5548078800a55180040c0040001c949004075407060398000102c0009101c265035464603911031105403105544080d6606514003003d00c0750b90710080c044441d0303a8031101340d481000040b460076000910b02100302e41d560703091641c00c1581d0301c04c50300540c0c3c03042c0c0d140d68030b0200a5200340c03a1000702a1400b03448114030003c4c507820000a02103000202d007516841d590b21018060a48514460140c002c1d0081000728085240c0040c00201c8000003000580303000b8054010070300d040c0054200348c406081e1000190f0401d504000c0e806440c1d800c3e42418001031402803030180103859080c10981ca07582d01d604011800131b115522418030010000c080c9a100c0c580c003080140031000c8810103c3c0110b20300070100340011054042c490460f0b03410f50003145001c01d00c0c0d4414195070005440b18100391810300c10110f50360000c2c0a0008068160380b4800d109600d012003580a840014204403e01d1161500041110400080d00700070310340c0c0750940082400b03004000c80d150118 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 870004028 1250 870002778 870002803
    0x60904030c08120103060c020601080c06250c0e0a0e0303011a13061e050f0409090f0816110108073018020a1e05091e16091202090414 59
    0x81c000741c40080040e19030861130680f4022a030030000382c201d503601a60b1300c800038000c03180e840c1d01065084400346000f05c020001c540464a0b1402030076094050441512080441100d8800d0901c0c0180074414107140050341c00300c26000107010a0400440480d1270303100602424003a6001403100461602c040c004075421000c8614180050a965800003000141c004181c0c000004500c403031300100502c40c0080d0307051482c02c844124506407030324422100030402e9000c00c0b601380000c90906008542104090480c9540803c01d03845010210b02d09100328a446000711414041c0f20f00c02d00030002d40c04440c81c0c124418a005e20345200d0100b01a50010701c01c654030310a0a907041010031966419089010b102c014402c1e500d6403003068403030941c84004034401e04801c5003515081010042ca2526200e80ca401c9118682c44180b0192a141c80c205161011107980040c0005000501041035010001c403009103038040c820540b80800760300207010048094005400e02e21050030309600c0c10010b11030360500c0319 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 870005278 1250 870004028 870004043
    0x80d0906020c0a05010b091302151602060d0902190b0316050c031615020406170a060b03090606090a0203160e1816030e010b0f0d03090b030c180a06020303060904030c 73
    0xd490724046010b41403030711400b030040000e0004032304d4400302c1c141142c2c507583c0d008040b2500c03010303107480d0b18401360451589910040c0d458074000c3c02603110741c8010580b50800d90b0f8086024452401400200002c000445401c10200d280c200b05480c034480540b50403001c40d048103a04803203500000c44050060380142030203800300003011012820403080e190070103407184003464403e04640020350f04038000c074445c403804107240181890030101d03200c1da602c7d0702038152000000c0e641c1e15010340d015550022642a1100c0d40602e00303208061400d545810b6002d16419025450761503c103001d00f08030801182c0103002d014020f00382c030f141a03854018a521414040d45210b1603860310420000903811110a0030b00032034980341103142030b03d0041c0509c5101c00c002821a10075040c000c0c0a200340500c2c445000c0d410454909801315800624000850280030261392842d05c3c1c1c05101c00414580c001a1b00d00c03071084001440030460f40790040240d946c044d00032030b4008260fa0340c078101a6110140c6440c01444e04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 870006528 1250 870005278 870005293
    0x40b0f13020d06080a0812071e2001090c05100e04090b0618040507181d07060908150f09030d0501150905040b09161101060801020c06070804080d0906020c 68
    0x1412a81c041d201d881e003a60018040160354814050b04c41c00007480150203010100b010031580010302030805e401a0a5181c16402d5600e11440c0046544141c602407000800100341e00000103c0581440090940c910003000181402d0341c8030602440d0912819003d01c00c6042009030007401848c5020715107001400501c0040403910b0240050101101d1261054000d2510030320403804000c3d80c6440740d40c0c044010500716042456020a030612402010400c82d190041100340080c00040505e620705a94000c02003142001c5000c0c4c1903601d10381185402c2c4e4040c03101503841462001045e6003002490210394840d840d5451200e08511502e031399a8200750914000080b0030340718400b80c400c0000b40d41c1e20004c042d41c03240200015508262442ea6010b00200f012484040030756080c100100280e0622895483d0f84824003425104a6031000c40070b030b54042050380c80b44000340103c07540181c07070345440302440c0b81c42e81d2031403014040c08000079500f5949842c52810000c55074116002c1c80441c20441d54130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 870007778 1250 870006528 870006559
    0xe0118090c0f0503090a02040902301212010e0709080304081b040e030703031505180906010e1308090d0803190b03010c0c0b06190e180307030e040b0f 66
    0x161065038590800200b4180d0540402031051080c0c074020b050f1a005045036440715000c11000c1d011a000690f0720002d0030400c500019204d0201001800442c244003c205006034111420001d0403108c01d45018420049120aa80e5200009043d291013010113402c3d03880c0c45504031000d103c030340c015113504d1000080c04035000d42c2c000390034003440fa41c101d0010210403002c4140070a0380c03840b00b46052941e07c00d0003400c0010b40250003080d49685104001c00c4260f0340c4400140501c400c0c00700314813070a0426070512024040030300c000e9000d0004240484000d00300701400d0b103201c0c0d0b0244000390001a011511280b503603541d140100c05150019211902c9042840600c1c5160301c15048601501e4908440c00c0da042c1018022140d0039200c5031100503c6802c82d480f05c5da80c1e854010551544090211403240781c0005038982d20010300041c2c031410619241081c50100441540007612800f5071051081308002513005e0242c0c0f984450981d40802d039040000040369030800c9082d612540b010302000703071188 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 870009028 1250 870007778 870007781
    0xf08040806180c010906080601440a092a03120815010c050304050d17030f04050f0106150f030209041d010f060b16020102150f1b0a0f0e011809 63
    0xa000902c0002c0e5000c0901c28001980e6101680c400c20f408140e4401c00100b15600a182c055040fa260958550000d4410713440c100340f20186021000d404290ba05520382034207003a0301002c0e44403200380f400700f240d002c56440b0840c031803205c401c1002441c8030b0030344200000116180c1e407000460740181650101031600303202504c1d110f422504046a2540c8130011140c0e5845140b0b901c0b0b1185d0040c014514140c245030078000300304409501500c144281100c0c0e8165090322100075885250f4608074000603040070302d001030400d640e100060420382c0c1425014003a203240c024441a0742c12080c03d2140e00701808000c1a0040d000e2007803010f62040c60404100c550700d0101469440151205008005000040304030204036141401030804048003030081d00480c0c609081003a01607401401111008410807a40310052541114400d14440780328091162007003688060100480d5503e010070304141010710000d02009000140900308001d880551180d40d0040d201c500591000880c14035580ea118a040030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 870010278 1250 870009028 870009061
    0x1140a021b090403090512010b03070308040509090312061c1a16030c091202030304080703060e0c040207020906010e0a15031a010513060807020313030f020109060e0109030f08040806 80
    0x8100c85410a040c1856140c80c0305072030f100e41d51545843c040c0c1070902e001d01640803080484002130399640c5c00e0000607a901000310800940c030801249640350304150501950a4019003001d04540c0140040d011815a5120f1558003142c01d407400030040c0700800581c10340c1907c3c2c42018150f03103010749101a100d91103001d041e11a0000c020161404d0f100d00c58101c00b110741158020000030315160b4107018254003045a0001e240c00101224105525240d80501b48050f6500440d42641d58910080040c0c000b03006100900008071011801c020740d5030042150210000e0426040255100d0410308a55031005440e02902c214400c0c0300307100e401c009025005110014403850001e100c031401000942c4108126554422000100c4900526040c2c041e51401c03000b0704001c0960200384000f0645000070420503008600941540d811701920b8000904002c080350410310400c80040746070724090342c1050f000c2303045903405011404226a281842401e60040341c0102d550343c002c000070302c0041e078043e80454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 870011528 1250 870010278 870010303
    0x5131703180601080a0f02180108030d1a092205010e0a020a05150405060f040b03040c03021e091911071a010e1006030e19032a170901140a02 62
    0x1140411808440542e0341030244140c40d0030340d010340841c00001c6c00750f00422800300d1019160b0744080c03080d11403554414500740c11400390b07648045180910007a1500611000032920346043c41300000c0c031404030f424001c008240e100880c00441402040b828503560070814940c1040080140c0701c00c01d2000c940b200502141070740301d00a000030108091400303400440c21607550340c0189291515000c03e00003540c0100c0c0c4d80c410b9040c400c1c00002104800340e8029841213206070454010241544104040c140c0600f255140c80c05004c0b29100c900e4882c2c04506400c40b05807041c41d110040d8540c0300303401401030151034010b030341c00109014082108005000c04d01a01c0d41d401c5d460f040e81c0f24403040b01c003027800710780c0c81c0c0b03050445500801c481802507000012000303400080e16800440c040d2500026400e0040850005d82402503c0700b040003001550340140c41c43c841c507a502c816031516041040240c80046503940f00000420b101316a0040000c0b0301107070300e12680310b915040b174200c000e07485200c201840d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 870012778 1250 870011528 870011551
    0x18030c06090e0105030d14040e07050301050405150a1701020c071805012c132a05030115031104022502100c0206190203091e030c030114070305131703 66
    0x2c200481000c400c1d03030607114082c004000d04649444100e4640c02c44030f412003a240707001c10000c00e03182c5070680160b00c03480c1c2c00d45805980f540341405103c01c880c0c000b804c41088000700e81c000e054a40d80d00c500306044483c409003060340b02820650060092044c21600503040c801c405000400c244624201400462508010805a80e85610000c0a440f000003014018003a8008500004042c400c503550448044001041d580030320340d9030381030a4070703d06106900f00d00d0a0b80440d5030344045c09414102402d002e500a0003044407401f0100018034203400000c21110009001182544440d81940c04000200e405c000503240c000d20300b8010010140026401030000300c0c1d100581c40d0060f8488140d00e68040d041c41c2c81e00c0030041c541c8400303406c0d81c610842180020072000c106540c5500305440d02081310210008022100300c101032170440b0040205000b030341869a0f008114480001040d8070100038200030455039100c43c0380c82c120b044003079402052848484100c4581c6d45082c0055403007200700800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 870014028 1250 870012778 870012797
    0x19050c03010902010219110a06020f011a0a030b0405120304080a02010b0a050609040507020a12030e0106081c05130513020301060e0109030206030703200d09030f03151518030c06 78
    0x149070030b80d00c40d101c000e40035030311a81d07100081e10500d20050040c01e0150b50070b992140107c0300040c4070034256038031a00c016403040c07245440652080c8141081820441d0741134540ba1100c0300840c403105034911000d804540940005024000280022a0410114034415039240fa0502d408142c5404c916a505c00661034400004130b41d040080d41e280641e440140034908100c540380800c0060440103001200b103020340c0305140c0020320145441320850001c0c1c0c40c0421802c0d0032040107400c40d0466445181190b101503521800c840e510010885c80c00e0b61881e01c5a40c070a101114100c0b403030b04592086822052a85010ba0b4100d0503a0196060300c8140c0d45040710065030500444402d6203500020798001810004121140d000390302c030905840071410300411440d0b103a001000306c0d4008003440c0c000140c903031503101c0806600124015040c9080e0600b0440300c034180603410a90300d6580500001d14415090320a4110b0040301d85040e0a041d60446180c10b6890b40750210002c5000d210b0f690201c1d02d23800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 870015278 1250 870014028 870014053
    0x312030204180b040b030a0804140f130209210307110306061e03250807230409031e0905090a1107060203100f120b0a0504020d231905 59
    0x2110102d42c2e07507508248041c2042c0c81c8020041c00c60725035059105035102d8a02c0502d4905002007514140540c40e521b07191881c00e41d1a140001a1a503000e1069081c1180200d0a50301c00625001441a6403801602d81e06d01901269820294048824101545d04260600701e18000002d00480b44904000301c400f030307442402d05503110001e44582e64401c020309943c403695142507031055260000202180d001046000444c0400c068080c4c0c1c012500c0d110300002d00924100f002003400030003000c02070b05032100103c5400c10406c0010080988a551180000c00038944504d000703000151858a2840c03603c01808405030003c1d040b44180d40c00f54807108000f41111055204140c2071149851140385090540c1d40c0f100000d5000a2520f111020810004035042038546000d401030000103c10031602c1500d03003003d1000d440c00515110100d8200410080140c0740c0210350f051056004c42007050003200081c0802102410f0551b500c540d1140e2090300328907881d0580c4802035140944191440031001c02e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 870016528 1250 870015278 870015281
    0x30d020705121819031101111c03061e060507150209131b08010b040303052508040e010905100b0307030e010203090d12050403080615040902030703021b0a030e060d02041e031203 78
    0x5e100241962540c2d03114181c0355401803a0b80240805030740165410844001c0203150590a040488000a60f171403a003407024032444d109525044006140c0381d11403604d00b0074010a24070601303200401c118002d240c2d006201c0c0031070301542e5035401c0052205618001401901d0000c0000c1100440d0401980d030040c1c10f52170151103818143d172144c245407480d190840c0c406507007030b038421003d40d162566007110b844d060b05c10182c0084105441003440940d60743c17401054044000341a0480e04a030744c604400d0101c1210300d0400c0c1c0b01120b80c805049901c0b41c0e954032080c4d008101d02c044680055000104020f0500004142100010710b2521f841d00300c00d10310445181101e004450003400f0400c0071012500307510742118203880301c500300080d041c9016102c0031000d0036070b001500c4200109401144002080d80154410741014004c00005d09911019450040c1030b03082c1c40c51803500a00000844040c001a43d4044401500d034030300f1440c4011140000d0100074140300d1000392010f020210b0140e01c454440e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 870017778 1250 870016528 870016579
    0x14010f09020306071803020303030c04060906030b0a0504091b0821090901061103070804080c0901150c021c17091c0b1b0d15090f0e030d0207051218 65
    0x60000c083c03da40301c14058408540d13081d00351440040400c0e0000040e5400c100030f51251003030341c1c013640e141c0346080d401034900503c640203d428503041c404090f110344c4950a4000494404440204001d4164100551281c1030302000f400101600e05020541140020301007807000480c6000b00e80240d010580744420340030304005281d020210000400c107052245901100c04107803242564078000180e569040389610981c42400701d031300592055a400d141117802540181080000e030849080c025200411a02082a00078480e81031055002043c554408440c1000703a8050100c80f81c003035054500030226003000350440d126032245001681314140040300c40c40c0941e402240c81d8220348070010f081e00002141d03001d400800f0300a012030a8905000c0c01952030400d0380100001d040c1e0f081540e034a007600c0340010f084000c141044400c2518080c00401c99014042e44900180c0741e000d40d180090500e00389094200501901107018144012580c0804017040700c01ca075013007040c01101c0e041d105550350 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 870019028 1250 870017778 870017783
    0x2030414100b010e2202070302031612030b0f01050706050711100b27150f130e07060504210c030f05030d2f090109051f020f28030c0b0414010f09 64
    0x5c07072104d04c064001c0c0e281c020b4103655100b07005690801003805680c00c042230001da0140e4281c004400d4840e1126018441c1d105248001d0340c0648081d074034200060110b2181d0400100125900c000251200c0e00c82c0d81d02c2c56141c0600015a40b00307c410156003c00b400b2004406c9100d4404040d00001581d00f850750401034000d0020360750902c0cad40d1940281168501e91540d103070003c540c0c12404045580d980800000642c24030000290070000c00d00301413a1004030380190302880300800060088100030142c403000001007000280c1c4c040c06d1403810b9480c410003588010810f4203540c00b00c5040141c08406020466036120040040c01a0342400440d060181d119410b401c0d00060802c0d583c104074503000300032840c81030414580e02540c580108407900440d0220410501d0802c2c86141141d0b4184290a859101e920051980a03480a81c0a0030f4002007202c0c3c50180503564031500030527010752000003049420409440341c520701414010220808000b011005520380181e28001c400c15104003902c0701d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 870020278 1250 870019028 870019069
    0x2101020a171608100e01092c061b0408030a11060a181e0507030b0a0c05070b01050d02010221031e0f011e0e01080a03090509090307020402030414100b010e 68
    0x100c140c88151070307400b03025184004411551301c0c0401c080184405141c02003100c084000350417240d0210404944000303807400402d162890304640128400042c5241c0c002602004640d407504125080282500c5164080051340c0004203210302d01d140c00c600c0044802c0d080c031094841039520001300745d003241c0000e18061646040b101900020900d8280a110381c000c0408210351144501c0c3c40d031901c2c0501c6907104840d1000b00604009005085002e0030b00e000c2034a061941c01c1c02c00325583c800e13401c00140105801000e01c0807100c41903a01c02c2116980004042d40c1a4291580a1401f0300c2103900444110002c4101d0810b40703000b52100c903946512030300400300c0c40301d2607900745000040440c0068800d090310a003030110110b20042d180b80824000c02d800c10041009000500d0302038448285940301c20300c030303031021300400c0b10300140030046922a540c110f0300140c0c1e9a98504c0c22900000e2400084502031243c0700400070600500d5210746403e400980345c00140413605400c1041145441d00800d00b900c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 870021528 1250 870020278 870020311
    0x609010209030f0d1e0302070f0f0606051e100c0213060f060507031709070506040609051c0312090203150108060a0e0c010f0c0c050d0804030b060901232101020a17 72
    0x4d117107040207540f50f40346440c02600d0111252540100c0e0012039009039260700c0d0082060b410081c00344a0301700113003026900360711a29090013008002a282010150289250003580184248500e06504242d40c0c0203110001c440301000860004048034000c1c0c03680030030001c0021840c0f0b4003075001e4450705549aa030300541e156020340044048400900325460a10901d003003c40d041e0b032070101401c0a81a20f9844640003072070b050400c00011029030060101c400381c040c07110082075101d041c0c029201e40300c3c00d0200c1c1295013480401d10308031080e044040d103c04102c00110320004d0214040c3c3c0642c00c940c0d0140140c2d128404c16540326000c81000a012854450424013028061406003c40d68007400341c00442c143d4500100705010110315086401c100c00140602c20054a500d01c41c0c0c10501c01cad500586150b040a409001c0c4502030940c1d80c10001380b8041040e070640d1030400001580c000903401075000c00848030702d039002c0e400c25100f4002180950015850340c6003c24043c81c030032000d03c0320000b0b40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 870022778 1250 870021528 870021557
    0x3120f060f0f010e060a030e1b010e060307120903090e0604051614071505180a0b04030c02041d061e161404080d09060f020c210106080609010209030f0d 67
    0x4506091850606100f13000c699440703290b135171001402e881c91440c4c40c00300303d04201c444a41d0030018005900764506011001d0004541d901c16520780000d103050700e8559807510384c95000d40c0c01c40344003214142e50304e0401324007408142c1d01980443c11258201134824198895004200a0320412102088030000d040d4100c2c1e8100d00c59020040303011004840310b844c241017a2541c0743c61358a904804021107465070140300301ca004540f40d140e800b0301000c4c080c20030b80442c2d59134400f6909028002030100030200e5006000e40d51154050342c0c2c00c003481080800e03446418000c940d01d5042c200c072403000d202624140b01543c003c214112602ca641503c0028040b0032036004203070b5203c10708103034141e07220300305000108140380300700406042403442e13403a403004507440c0590041c14255a11008421034101d040080c41c161181c003c103140c0f0703000007000d41c0d00291f0300407843c03401890303a40d0100303040744101c41c24031442082c19801080c0e07044003030301070300c1020340c1640c0300d140e580400c100e2000c0018800880d6450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 870024028 1250 870022778 870022789
    0x615051f0f0c0c1409090601030503041e0902070c030b100503030306130615080f100521030d140105031e030f0c070e0a020d14010f210c0803120f060f 66
    0x2032214500b010300454a20b621412a0801c50382c014100e115081062040c1c28908241266405458a401000300b0740c15940c500e52617000b1072191900001100c006031812000f00000203014001c042c1085489450a0030708513483c81d914401500c0e40c0e40d80c2c01c085aa142d00054840c1e083d00c1c1d001c0c000b940303903454410500c41c09030803004550403856614403011505030460503e48040000c1507a445e1040d092440281c20604400b41c900000062444810810b41c2c40c3c0181691400c0a42d0f844000660000c2d16400d05511401522059030b41c6040c0751200c1d03141e00004014180c44058080342e40202c4601004030044004c1d005641c00c9510500003a8140c02d91706c0001d003802044d08059424195035004040110002542e034100602d40200790610090343c3c921a00d000264010381d0143e030340d4903007a540d064038455402000c1c2d8031030180315a10f171141c140c0c40c11010000e07480b1802143c1c06568120060300d0f40c12000c540c1203580500030201d4042c51180340e6650150398010452011440400304101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 870025278 1250 870024028 870024047
    0x90f02130603110702130e07120308100f120204140108010e0709020f03010e0a150b07330c0203090a09020c06010608060a0b030a1e02030105010e091b03071b0615051f 73
    0x1003950b12021b088668120070b1260800800d41303040709002700b40d8540740142c00c2d4040286000000c141c0c0402c1002100400c0486c4000c407103600740b800c0240c0a007400428050314803100d890382d01410071000003c0825056210000f0707841c149081d01d0402e512081404242d00c54211142d602c00e07420f00040c81180806c062407034114004c644001640d505d83c44a50000b40c401da07008045815010491000340001070185c0c03c0030f1140305007807070410764000045413140010903001c010b00a617070f1081c5001040c0200211044503500400c001072555481104070082d500600030142d07980540c0c80001141800741081a0103054014183c4d203180342040e038501107e800050403183c82c2c6407035040c0744a490711040031050b02100d101c0c01c05692581000c00160400d96000d90349802481440d040001510800d10101d486011903040580e030794656480c1182c0f508101c407550401401214440c13007c100c200d5021100c41180f800203150099074501c20092161202c0c640c4594a1080c2c2c000030700040d01c201c030880d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 870026528 1250 870025278 870025309
    0x15022a09060102241b03040203060406110c01060803070c1706060409210c0506090c01080a0b0f0303030901140106050315040f0f060e040b01080a030504060e0a090f02130603110702 79
    0x4588482803140300000c0c6054403140724a03080b040b00f06000d201c407245041d145645d006045403d255051039400300381c0d5141c0003070001d03040780e40e11091022901440c00840b02d111032504024440c031915040b46548992152404540780d803004a00040c0f5101c1c810004503401c203000c0d01038159a9504014000503095508088031059016901c800c034480c0410078510322160359548180c805041803402034078001c006015102030350b1241c40340e80b0081e0790000200d030b8014030102c400308002660f600481c090030500940c040d410300010042105501d41548100303054220040c040c9042d90765000161450320003910940070504090981501900781908080c81130004124005a07429003240c951040f12000e070401d00d455200e00d020b00c000d00401318a824050003940340642101d6205940c090500d101d544500300902c6014146d21900c0d40d10840100001c15042d0400d1110008011035003000758055030820042c8410f841d804144070b4270034460314044104001c07145151200725020031115201c000d241 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 870027778 1250 870026528 870026533
    0x1d060a0b1c14090f06130204020f090d051018030917160602011d01022110080d0302030717060907030213031b0807090b0603010905091615022a09060102 67
    0x4119040519215400c0c8900240b400a00d460905800190502c00358250302030190384840e084c0710303aa202d819021702100ea4120b4006030784913161070440086005000c401c0d0340c0705196160780c0c01070000100e07c0e40d0300c401c004c0c1c40400240140e5130220b508040c040001800040d034501081c04607216180915a050b0b402e40e045820300a001c00040040002d40e40003180140d4480c0c04008042c0c00e000b44e4690a103079040d0007982880001001005441451030200d00004112404a1601d20138414005c1c003a0642c01c00742c6801814200d0040c000e980140c030008000303242d081110300750706c6414103c076000341e10007010002251952402200a904801c3e2040b1041d44992000000900d103080c3c1011105006060700031030038038241c0942d080542da80e00c16030f14035040000e0b945031a030754101101c3c15070f0180f110000d160740b1055116031a08100801c1050168a00f0740041030141400c1503071017540c00e250f800c0784c6c4451290405120082d24400e40c0b07407035004070f44000aa091800040d80390b0b1007031040c0304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 870029028 1250 870027778 870027817
    0x80d0e030d05040326091009021201050109090b06040209152b06090608120703081506120f01050301090f14150109020901140406021903030e030a0503011d060a0b 71
    0x1203045034420745040f03002c44c0c0c20444041e00111700f450544443d45c40c0c0c200ca20801e00d045000980c8840c591003049a0040c0c0d00c1c1440c400b1540c82000c003403c03803204907000704000e6071510122002080c040409840c90000d10340080c0c65442d1500071150100743c040c0403402814600d88030030003641c1043c1804507114400301030312020902652101c03070100070380b0400824414034002030300e070440d501a003280f00349800034600c1030030903420036044460451741450020707490b0360b95410403054031540c030303103410f41c0700e40000350004100d58000c4940c0d008211030044480079903a036030304060803201d0007c80109103000280102d404664658012010004804199401d01c00407a28800c1c1c0084242c100c881d9544d0701160580c0c1e256440b035074103d6101d8858140914003820300d0b2029684d9007600007440f400300400342c0c03200101071003a0490301d44074000b2000c032500c0b003004000141440e0002d0140500940c2c82181c1c2e0042015408446406494050b2600c2100d07030400f5022065503100000c8103040c070f44c2c0c514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 870030278 1250 870029028 870029047
    0x3050405030f0c0606130501050102030403140c040516030501080115050607060b04090f060606052107140c0c042f1b06040605070f03060b04060c020325031a0103080d0e03 75
    0xb0001c20360b911180020b0007541c0340c044100020104107611142d49103180800501469030008215807e984e0001c1002050500c6652258a8a403c4040c0c480c1c102d41001c4c01c0c0100f50007282011440640a600c062115a0300c49401328221451202200300e1a207001c1c10800c00b40c21b040004000c40d50040c1d90200d0b24140600216040c1c0341a00e10454881224203215820f1100c00c0c499070f80941030034a04945070074210070794100c2c001e135542d01030300d40e04140f0000f2552450080da4407080c4260b4800c44a511080070700c4505403a4100034000c6030040b814042c05110440d03001610301071602c482c09440d005032072b44070020700700e40d042842c4803046800d44110441c42e0181c1045058800c038030400c0c001c00c1902c0c141e00700601001c0700414440a050409074284103514100080e1011303243d0a1074216440022800041d2601807030196034003220f072580721b020020001e43c40800c0142c0c4d000341c050140c41c01825040d00600c180910018003041c4003480454100d850139000504d0310000c0c0411281001100c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 870031528 1250 870030278 870030307
    0x1060f050f160519080708090102010e070f0609050303040b340b04030f03050f010905060d0803090304090b12060406020a0504171509070f140307080d11010f0603030507030305040503 80
    0x2006020301c105050b14000b04118003080580480c81001d0b0745591102030b00d5071081c0c07440c01031031001407100102003500d04c030a074407d502c0151081928001c40b40c8051f5100e0928240c8607aa00585000070f1300400c1c0403a03035040010440d011210a01d0700301d40b43c05a0003002e800d86160070746918600d10550b41e000401c4110701516540c01c940901c0044140d400d081c50080e042440301a15601814100006c000582c3c4050040d107046640c841c0d001f01d4075559040000d008581d810758000c11a600220a10400039400005002982c4890504022503103403a0700b00700c0721110048140485502460020b0700181d0307a07402500d55103c5904101d801c190312071442e074024000c0b0300c12481c0d0a43c03000b841d1601880e24202d010f500020010090301c3e0150610891603111642d5014079400000c0c11002d24810380c030108000001482c0a006a0b6145104040001c2c03242c6140a40311a0a608000300f240e080440c40c4030707400460b541921043d19203c200e0b43e042d8041c04c4024004c1ea038a000030f0101c0ca540e082071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 870032778 1250 870031528 870031537
    0x60109110f0d14060409031b030201020c2d030408120d020904020a120f06080307030e0607120f08010b0a0f0e04090203010c05070204110412170d1e0507110601060f050f 74
    0x960000b0640a40f0034503801c2d00320000030406807007142009a1440071070340007402e08480720031642c003000501005082c1680603104405a40302140704c1e42110301d06003500c991150b040a061101c01c280401040c068184d40c138040d5004004007600107440300208022618020a03100401c4d4102604110707000000a0403600807c040ca004624002d094000820303540c412010a90f0154108201040c100588913999000b0140300038280001800c24182c00c0da6030714103540c410366124000035a0501c1118008225580341c1c028800403c1c0e5000c0041040b01c40c41d800d803034034480f90740d035100d0030003560f01403c0750034440c1c1416003604590740741000000346e2001c2c0610300150003507840d40707503603420f0f0f5106020848416100014441c0c005000522080710315520000c03140f03801c16082906900400d01d02c04492040400ca03c035014a000d90301100050440580c00700145006801c0146a0b1110340684001701040d2a144690700044014441c03d4013134003001c00501180e151441c2004500080b204041c3d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 870034028 1250 870032778 870032797
    0x703030b0607030521042103090c0801061505030f060904020112060b03150a0806151305010329041101050d060e0f040c050a03051002090402270f0a050102060109110f 73
    0x17a000c885032845501c038000d007500c801d0300000349103090b443d9a4680304000305060070043e4498201c103019840b1f0f401050540707400c00c0d410707007400b0b1b0756150480c000c2c1070a1041c0c102c4420342c10803c00405024000f524440c00b86404031180303d69812013000511240244100c0c1841495000e11075010f03818484d0002604021070302c241d80b400d280e000c1125031050000128031409840e031051211800205840340c10140d4a4041241a001540002c1c015160309010120441c0b62800000602409201074a80d090244600ca900d0107100b008644180b2001c48000c0d000c12244a82400306501c07481c0208984500510001003041e20303234800f61600e1905030752503170719195000180014401c1403400000240001c55082154a03e55980c8948844c01103443c01c038070700c5d07011031071504031303126070301140c848200d41ca0103090039624802d90001820030524445028040d801c00b8419076080030140d074010741d0816001020a0380c42d011140001d040c0341407548908203000e00c04103c0d03030b0f824203000e07002281 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 870035278 1250 870034028 870034037
    0x601090b18040b030c03100c030e150a0b061602150d1401051f021504030e131d070f0308210c120c09060a031503150b1309050c060703030b060703 64
    0x541e010200000e07142d20180c1a80300c1d400c4150740100360741d400500c105181e401c0b0480407031481d00188098008208400c20900540160038511280c000e00c00782d481d00c5901801c1c403c010101900052251901400b10103429041089400030050300d800f00002800101c410b8005203081910131103101030340c0011824900d42003010b4010f01061030196140200030645c1c0c0300001c80c19801c0c240c000c0d07440300c448011b5840030355441d000c94103051190381c1c80b900c0014085c080e04c00700c0c03e2202c0800f0040c00b03500035031031546005080010b810300012a01c00c0448460750040500c2e541140ca03046600d40c0559001c003a034071003a07000301100c10300b51001507100c0c0040c83c55003502d4510138000c1c18800440184011042c9604000303d6400b82e8072441a03d529404610340000d034400004440311800ca00c1da00060005141101341840041c4035810480181106031100e144d00700302c100307000c82030301c0000000800a4000c1d1403502150300b070800190141602034035000c10818900c0b004503400b03034031055042c0c0014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 870036528 1250 870035278 870035317
    0x1b080904022b060906090b0904021c0210120b042a030f05071106070c0f03080c0d0f0e0c04231015020c100e010c0201030e030c071d0903130e0601090b 66
    0x44284e44241780041803100c4c4284000000e103c00956110320013007000b03204d0b180468046007007041c00740a503040e2035805050450100c10012002c1e008508403022071a01d9401c0100c0342c0c1c4582868015165030b010301c10160000c0750716441e90b6090000703001381b020007015501e83e011812034110b030180d980204030341e0721082c00c0c50803441c061a0138820010154000c0c00750000f0310b100000d4170801c1806a040d0175103018480e64495a495900d148500c00c984519103041c40c04035240c41c1919445041d00b00c44060480b081c1804507818041500d1440e01388248a943c01c01d2218200b210300f044041c0d00c1030414400c0a0707616141c58240c50100c40385060100141c1c00401403c40c17038180444010386082c0a4104280760450f100002000400c1050b0024101512211403890120003001600c0850296000380c59016071118518076084e1a101e10406010610350041000c0e160040200ca0b001c0a440300001c00c0d86052000050700c041010b020181001388440000885c120310002420407650f00c6090000709 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 870037778 1250 870036528 870036539
    0xb090a09020f0c160815040b0403030506013510060e09060418060b191212020c0a032405010803160224090a080601050120011d030a1b080904022b06 65
    0x40046d4034902528a00004003404003040200d0011075000364945008038040d070350800101ca015141422003c00002841102d84408450105000d4a0221580308182a1380c0c2c1e44003610030205030b4072030080410701000c0da9400c3da040c882c500b81d03481040a00b0220725a248480006042400c4400c02ea40f082e03aa00c01c02020391030300d05072188040da40c207811000598244880180100d01d0101e00518242c810140c54a9040c0280540805824010401c13607a00b582c07400e10a0b41560020060f01c20190a044a040400c81038804c680c10780c0c41400c0158101517030707112038844280c03d250701641d208441382d2001040f481581c00c01c1541030720301c4a0507529000c1c1d09052004981c10f50700a4111504040018800c60f41d004101c1094840d010800c81400c0601c0c1c0c405500400040304550010380f01012890b40150b0000300900e8481c2c0d4030f40e01c00020840d140c00d03c0e0234a645041c40204820402c1000079440d10f8079030040d2100188920511307030000c2803400070102841e501070107828902c1c0c0700d2408126 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 870039028 1250 870037778 870037783
    0x705040e1f0509040312060b1e13030f060f1d010e1c0e0a150c020901090507021002031510020d0314010b04030204090507150201150b090a09020f0c1608 67
    0x10807103180080c5074060407070350401104008150080300d010b800200b001805240c45a9040941c9090720f14041099540780d00b800140355215010100385130141c1d0307848422032412081202d02e556140f0b0241c413402411941c40c00150166400192000c40d207503203540d2494a041c1c070404125002d445118421800188401c07030079034401d4540069650000283d41c50038850000148010482ca40307002d00030391800c94000750301408540c00440035003400300101c818003600f02040e581034500854020400b60798400180e405e07500b08990740f00c010f17000a40000e103e8107498010710742281140307268a4050045030080f50395080c4000d68500140d000415400010f80c05110307030741c010304c10b0710012625581801000006846144070090103135543c0c81a402c14410107010040c05050142c4c1d019900c0c015107103000707010780000364070040c40c2032104e800011003400800494051a10252900c8200b5141001083c000c0d0004800c0c0001108108940b5240c1c400078480c0c0c031a080280402d05648a040c503a00f5403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 870040278 1250 870039028 870039031
    0x14031908070201090506070f031e0203070806030f0a030e04060e091c0f200a05150a0b010503060f0d0c050604080312090313030611041226160f020d08030705040e 71
    0x1c1c10359150130b4500f00400c1010824690140040c1400b400c1e1144240c4214003c102050100b00081039007a0312451983c070340d07002140210410f40c0c8043d02901c880b030405460f41003114403500c255001034035443c00680121260740d11400c0c000e00000740c1da07a403205a8000100211528456038000d00d00c10341404041c3c4c482480110010329100b10300100c1900301034070318028111310f50400d9011941119041500300106405140e0100540300c80800429029070040000d807807030707425641010083c143d154490710640f44201030040060203146141d8051000100c00080140c483e840d6107000495184caa00300100000d10b1300500a55403031a480001c0004020068280c0e1075076001041460810701c84040c452080d2504100000740600380c07110300c0c031950312032a48200074040e8660781d0003050100440b000810b45c1d40700d080200549011445d082000c0c07084a40110b1020622000303c0081449243c1c0c0390b40c0e0b075101034132202c0c0f1b2145545a121042d0030458080e000268000b03414000c5100020741c56 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 870041528 1250 870040278 870040291
    0x807061d01020a170c04090c1d03150a0b0d050105070c02030601050907050720030601091b0c0201091401030b040e030304120e030703060f0b0a030b070e0108012114031908 75
    0x850400e10008402050084d05002c8400c4140803103004c0781c001803454007154010000d00070200038060380d104000c0c0c15400c800400310b0030300700303aa4840261414049007443d0048070604444819130ba0708800c3c40300820441003139a41003c903100300b900014009108090241c0c029407144c8603045041c0c41058030b002016080030b40101624000d01c6410b540000646170100da20000700c4400c114050042072146106903500d5515210706400090418107582c4200d1120a01049810360103400070410794002d042081c009000030502c0c0c60401a1401e4008149168201451b01089181003100003c0981c2d05040300c0c40010742000091008000d0204404606480c007410400c001640c00c4c03001a80351007031440040c10654075228848002112070b070040c1c0c08584001c01242d4001c0d00d90901a240c01001c540100104030313540b0360b4507243c0d80121203d6040314081c0701e111044005540f41950b642204c0501100d01d01c110403076200e0250010b001401090143c14010324586c05040c400901071a000b5104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 870042778 1250 870041528 870041531
    0x12306040e0f030904020c190b0105010306060f0c0809030106080a0b010e071106040f020117070305071805150706021e0a02010f020304050a0f021f02010b12030c030313020a030807061d01 82
    0x428480c2d20000c0207031180c08004440c0141c84e50785180b81c0074180855005c0c1104014030359440c041c20040c0d2010514145c034402c2ea0100082c0342c071242d042c2d40c01000d85d42ca601c00b0542e4001303008005030f0650001c080e2600050004102c4c0c1d50794142a900e000507140003113554040040060112801c8907206c1503120801c0d00d00018a040c0c081c022a0b110391016001070300c0c1c1000d000402055900a076013141454446c0d80c0c1040f441e2904c1031008001b8003017614480000b078103a01c1458001d03440f00c000c44058910050450015004071a428034850388092021581c858090081c000750400039000c03c01c4c080403e50010395241ca003000001d08442c413400105204ca0f20500602011074000a980b00f03080d41d1103820100d200c00703107000064041d0228044118140300a02000059542c190002440d8040580c0c80040003100e042c60380c3d0f207d010300d40300c1090300c0c0d00900000c3d03d20030510410300045800a0030044c00c164894543e44040d5204c1c07002950b609880e600e10307020000e0340108272000010031000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 870044028 1250 870042778 870042793
    0x3060b10050412050102040b120a06050108011d0a110c07060f08070e1309050303090a03090b0a021f060302100801030203160e0a021b0d02160f0602030a030e012306040e 74
    0x4001d0810b000d503024990f141e603c000c0030081000003d504403009400e60800064540a902c0a2001c2191040301c01041035400c0c03c200095035401129554140c031103002515800403c440c69404540f880100044509a19000956201217403003000b0320000d9240009402050f0801ca009401d1219884e403280420641c3c1c82042403103a4800d17510b480072030382210316240d02030707404410002400400d140030b481804000144015404000343c05895144a5268a0386450742d4a0001c0580c1c0100c807024000b50300140c5842c0c8003880480350480a9903500300000030038a03102d80104e40b4151081c0b010b98007184600e00140300750310f0100311410f68690130807180b1400c5401d089032003041c8134016083c1080705401040702510390519965001000101e041251035207125404000e42d60040d1120510a603a05454049115082c4160344400d881c481d800442c40d0003100503013100140f200102006180d581e0351806038811071103a006c240031300340506140304107052203401c02040391001200c40c046a886002c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 870045278 1250 870044028 870044059
    0x15010c06091208102913060810080c0d0b0612160f081606030c05270a23010f0e06120a110c12180604090203070e09010e0f07120e0703060b 61
    0x17403c103860310072013104035442d035a907140001034000d806052490241004010030304c250301078641031003000860041511107540e5400642c4031502c4100245d0041f0021080030045040c084000741c20880c0038000c04011029580c04500f071003440001c810310000505ca00300103914552828501408580014040760090402d5a04a0351158424607041c903807228140591036000e0801da9011b10404180495206445c007015881d0000c1d11900c0d41c800d15071120b0102e440c101b45021000c2c41200c10f40d0001400e02c4040c0159880032885c0488000c0141e01c0420030700b00d8440303602034088075440a400c2c9038103007410311a0009a07010a09102c0328200e050007902c016000c0003880903608141d03000803c1c0d03540150b20703024004000b80e16a40750096000030780040c440c041c0782d00071440303900382d03913112030908000f032080108000c428440c42403800740d01400315000304006c4960f01d421580e40d08209060002442c619025540c40c03203580545034102c2c40040050101da80902107182100301d070702c0307407600d560b51 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 870046528 1250 870045278 870045299
    0x20d0c03020d2901150c05161d0714030a02031005150306120c010c080d0204210309050105031014040b0a06020a0201121401060c15021207030e0a03020615010c0609120810 75
    0x4d020030006c0301410305050000a10501c420604681a080590fa883e12110701c441801a10180c2d84102c074000000c0b04103200341101d02241e150703030103141e02e5602c800d259100a50400740098403c0c0c00c0041d0001a581c1d9082100d03009425403000a5490745004401c02c000e543c45100d0b2500c1c183c101010003a05a039210880744d500030b0340300c0c0301303141c13503800b5a00160024095a04200c1214029880040072840b643c0f20f0305640714481ea5998090a440b80c004448901041c2c0d0240d150b81807242e01481503094400344c2c2c10080c200034000040d41007410000503460700d80359000f100560030910344003080d0750380441c640c1010143e840081c0b00920103051601420305d41403282c00304101c0001c03181170400080e4408862501e400b89030554079914582c0c0307041c510340d105031441c402192602d492109a4400480d91525050300340c0c018100eaa03a50050010100c2802c02185040002c0340110380002a00c6100720303204640500d940c20ba200c4000c0c00c01400a69000c0c3c0350b100c1410a0100802c0340340e040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 870047778 1250 870046528 870046559
    0x280e06040515060d0c0c02181803071101080702030d1b300b0a080f010f0e0f0604061e0e060a05060d0f1b0308030f0601020c0d0f020d0c03020d2901 65
    0x84c9900140103064608201d625a0002c00300039484418a901820f5041c08a40180d00684180e0040080c01c40c44800c40f90b5a8460402c006240741402010314500f98003d40c45a90700506a0041e2480d001c0103070304250841e989552541e4204000920004410fa403280c444803e400140d4040601403610300300c0b65a0a100303200304d000c1038a40703856100110361120802c42c402000d4107001c517a070050010500364040c1880c0b04150b803003d89410400c480740030000618050010404010b004a40c1703581d00e0348000f41503040300c0074140c9212100107081030700c81d902c9403a40301e14940b4003402d5903040c620810000d03103001400c100d21501e20f0200450115565600b5a9921540014645240c40c10840640070801142d80080c002d0080030003049488101c0d03500a0744100800d07401d441070384920004012803d5000f500103441104001d42130301c01410403007254080e050080e10190741407940d0b9400907601e0108124110b4158031400c203104540743c9403503802c02241c424480b5002181d0305110f41ca0466158 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 870049028 1250 870047778 870047797
    0x40c0c03080109060f09051005090403020304140f06030403110c0d050c041a130c141810020f030417030d0213031a040b0402060310031b0f09061202280e0604051506 72
    0x143e9601217942300099044c00c10050802411080c000d00e82424040e4882c1c1092080c031100c900606501503443c0307424010120702d00b0000b0011030842d11551401c90741c00805094056003031048000c154826501d440b102e8411605c80e10003400c111140310103006c180c424000060328400d245000703d80b1784c3c7e6100f0b01c0c140010100214001698090503008076181a0500e004002004000902500e141c01d190241a070150090312080b9011139034034030490340da1036130303940481e00354100703000038000c20050030054907034a00243e00f141d0038541410741e940c080364002860301450425112040003005012149940d00d466000d00080040c03605440d48a40030328001d1000740b19020000000302e0010171107284a000c1c540003054031402c0c020044524401094900030303849640e503403000010b00030b6414091082034400c105086150484c0e170ba828040002c01c0c107042050810014108101c109400c84202401440848052200f90500f101400f048910207044441041d03c00440c142994685204031240c980 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 870050278 1250 870049028 870049031
    0x327060e0a1a0c0a15060303170613110c100b0321030a110d050a020a021509070509073b03032a0309090a15051f030c0e040c0c03080109060f09 63
    0x4281003c06424000301000090545400c0351604d41010050740c042410351384a5120200d50014001c011224000c1c1102c58541c4514210f141c1c1a1600702c81c1c0251030900d2440c1980d0307091070700300715070360b82000808004c022031b003650b0b692004040c1c602009500c60616903a201181040c2d072100d02240300b8880100241c0000761562030610b4140743c03d4048800c59400d025013007145081c9012008082c2d4090b465020052280500b0f4581550824090345d014149050080501e50700d00021f0014900d0300514000a00c0501194020344190002c40c100c620300710301c00b82860004a10904c0d0f9840030304000d4540c029401442503651010042d407416421507a0520720541030300c04484660320b98496402c10940001c00c1405002d06040179070815034018100302034040200d5120024403000d5042a04c0c0481c0c0400c4045401b28801c0c041c1e4400c482c0c1000c9031810701da643c8058000b040540740ca0701c0c600310018058040d2035083c1030303205c2a29809132020800600c03503075241071a034809000c0640515440207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 870051528 1250 870050278 870050287
    0x303032a0f0708181c03020705120a02090601050f030f07021e1f24030b15010f0f090905010816290c0f1501081c1b0327060e0a1a 57
    0x100078818282074102c00105400021018070128000c020310030117003200581300c2c40c200071406141c18a40f82d074a000e200001410101c08640802c620303d440a080541841000c100000002e03509100461080c0b4206400380158186454001e01d80112642c850b00725001c0c5081442c6030050128481e0041200d50a411095040380d41203400200700000940d0415042150200804001c103281d1800320b9024500070000d82d036550419410108100d02141d00040c000c521035120180900b0480c2060041c3c2d2409140303849e290900d0310b080392800c0e00301018035030104080b009184c1600006401804d44021000f83e071025044a020601002403070f450403050003c030321500740c080304020700780c01c8039120070407254100c0071540c5080200d0b00070b004868050192003628011040e00020122070114039070307504a21850310344140710200018541c1103080203a1551484138020180581c0148125001c03c850301091802c50050900100540b11a0142000c01d00402410001c0c410003100d813445078010301d030368 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 870052778 1250 870051528 870051547
    0x91f120c0509071404180608010e071a0903100501170f12090315070c0309090c0507020f060712110c01090e0609070210020708070b010e040c090b0406050303032a0f0708 74
    0x2c0701e01c410912403850078003050004140f02060003881104a003c06c041120f0f9417201540b40c242d400301c01c0d2180490340880000c103c5041d48400090382065030503c014140260000024104940b104d4049043d945580051041000002e002403100c0c0440005008590101c14143d84821001c080d0a40900010520a0007501e040c440c0c041484c00c40341c0c15445500d00303008040d005c00e4100f01c0580004092520110725000c180c41024114401919543d003420391030f5080200745000c40c0700c007d402107000d018900018900e15842d0400a01c9512454180c07992040d00360301d0901ca002e0441e040103404207080102443d294452908140309440211060345c401c00203a2030010b0818240702064400184c800a0142c080007900e5010f01c506d00805050740e07241a640c460080a803001342100074028030400034101e0641c80803920003001781001c6299661580002d043d90411101e11080030170806019041c040d0003410040c0b00007002d43d095007000b0102e0303038449450181040041ca08100040c81c90f00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 870054028 1250 870052778 870052787
    0x5071b11150d0f090308130803010b1b0f0a02040509190f0206071b03060c030b1e01030f0f0f0f05070c0b040507050d03170907151d091f120c050907 65
    0x82400c03801d000d019400c043e80082c00100ba190030140c000030603820104032880e03081150107111076040070000d4116424112550199030141070070709803a0760760f000c911151400c148205202a0090005082007000c51700601050300c200500107030305900103c030040c22500408140710301b41e9800c01a0001001280c5c0301050480c483d10382c001d0b1a515200c07011540c140040400c46095901c02d160502030040003031000d40a0b10050407000340d03c45102c4403608002e0100320200d2507480014500403600c81606080c03003084405100f01015415140c500401101b04a8080c0540320510000200712925010070000c000022042c80100b0700c041d81300c0032a0502c5810466034001d000010308080b10464585006003210803480c040c512030001c0d490018520807004102202112542080c05036400c1c04410100c03001c003140030060025004001007100d10342ca4201210384600d002c49401020103000030342031404603807150700c8156400000351401c40000c00c0e00344451f04031401941d2912181d152000142d9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 870055278 1250 870054028 870054037
    0x6090b0f030c0c01020f0a020f060708070c05120c0309011412040b0408070b0705030a0c020601060909090501060801060303022116081c290a121403041805071b1115 72
    0x7800c4d40c0041440300701c04500b90002c0c1101507045d0200c0e403a0300b407008652901d1300000c4400001081410000401950051200c044250700c1007003035415a42002030200340f10703041108106002e80c00450000b0465030001140456a020345d42d407581824036a1480001900c030003403004120300c8804011030100401c56040d1028298008c00022451411b50401443c540003152a24105403c0210f0000c0706030010804038180d5802d581c40b001074a04099645000d00001482112991769400d03000500310340171322411018500c290301410348031450384910303a016111240c0e10345d03070001d04004100000356140a510001948189040c1d1501c80c28421056100c10400e180f0320240e0500c005204101c000048042900c800d942d61b107007050211000380000520755000c0c411518401c14212404140e003010040900004039041380d140c181c0318001d82c3c0e100000344440c40180c907200c0c0e040c00103158004a0f41c200040580c03202c0d11007220b454481c409908131080b0b0090207990902c99818040d4219402c03074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 870056528 1250 870055278 870055297
    0x60a0512120f130b030604060e0f0402100c021903050f07060f0e0f27070531033e011707031805070806060301090804091a0a03080c0706090b0f030c 65
    0x103040803956080002c1545c0c0c42201e0081c4100d14001001c1036407411044942d0080c01d0b05140340149907601d40c20301c4013034051215190140805200040016aa148121a0904500d0506001c240e2540c6003052800b454851a4281070f040b01c030003440b545622500510101000b4034007065660001d0340480c004e616107002c41c40d00b09004091090b465094034666071054910f41400002d1540c030200212540e0007074240c117280ea01401d0244007110301c0c443d6646c3c1e134001003002c1240c40d89552941ca0800c07858201c1c0c45034448130054204c040381b43e0904401c0700460a03948030741c0200680c00f000020505044540c103600600302d820045240544650b0000c84090303000150314818500c103040140d0343d20701c00c3c41003000c40c0c80f0b0140069120709042c000c00c428180d003c400c850030542040740d442c0180c41440b000801c0211907a984c1505691390750342d140001e5000360a516641d03c0c0316501241002d409400007800c2c03080001003040601c449904030f82c10705d0640c0c41c46076242c0c2c844081c201d20510641000c1d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 870057778 1250 870056528 870056557
    0x807030c080c0319080709090f02041d0702010b01021c05031905090a0b0a14040f1403030708240a14060d060906180603150e01020904050f060a0512120f 67
    0x409040e81000401856654015072a002c84c1010300d030f000319140303078044600c14001403100008203d10300481c1c010242e41c0060300c00150a1a4840c2c0c24900482c21040c02c5003001026030301406130507078080c401c803280c1715402e2000e0300707004405602108861070340781000c5007003000c00400901c084444c1f04042e041e41d401c15006000e071782040c07262a0707612031040c4001d84000403078501141c00100036106140310005640e04643c2c842c4d543c3d4480c0604030103c260240d548456801c00010700403020b100462240c80c585d04c550925003001c00301d104054081e10901c4492140c4044402099039500c1103100c00c558009030955600130441c0701184680c09002d5000d001c04d41008030108030741c5044d42104c0e09a0301c042825100a400d00c00da04015200340e4400a00554480b0340c000300d4800d0070303811038055403408030300140c9000484c1c000b05080720703411201140400200c00600509160a00340e000090008035101130002c80c80034080d6481b56211070401d000342c400010a00c21209040c001e82c2d542c50364904c0d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 870059028 1250 870057778 870057787
    0x3110102011b0207052b080c0307050a030822020102121b030f0c0c03031c1a090a060f0b400f0602190308150609030703050a06050f070c0807030c08 65
    0x200695241c0d000d0085c42c2c49512454280c41c0814000343d4a54455200d80c900c030a000200d40e260314125501503c110410f5010070407281c40410410001c0022045c80382d9204503151512081440e0300012203517030259408110482d40e07015030307400591011428503822500340d503108200360080c0000d00c1030b91509410302008c115510300481402c06800b0924800e4255501800c0c9007042640324400c0b50310041000b0f1018104400084c2c00d580064041c0c54044081c5600388041d20014103500e0013183c020004a85507641401045050804980100380000400b42018149010a2a030390302500d401c01c181d01d01024421801c00c61000c003e9140d0185528010015845180004c1500503030b0241384c6c09031085c01100707c42e900841e007058404075007550b640702d40c0e40c45034860000d03d6121680030310f80c000002c1c41086255a02402100c0081d4403172401410700781c1103440c14800362200207041d00e50740e10341e80d030403c43d01039000b108084010340c0c803081c3c44c4d99410340c500d4190b503c982400e0000d0300c1e1210206 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 870060278 1250 870059028 870059081
    0x103050907080f0610351204030f020411130b0913090b0f06030607050a0e0f0307061211030603030714030d021207110f120c070305010e07031406060303040311010201 73
    0xd40b40d8085c49003a410000e01035101d556050780100d0070100840308214601c04080804c400c1000341a090744103006450391000000c1c000341035500260001d445210500110204502e06489000354a00d10596018200018050903000b02900d621401d511030300300080c010701d5030743d0380400c105519898437410042c1a100707040170354590508450a5000c0301b900d02c0403886d9450005025071044d480d642d82c080c54511040303412640c010518800036003140f44044400d08681e0103000b50b901410031940c404054004191203001a1464045046a40d00040050021f10b4401004540c40d5903005400c8442142841107407074910710a240314413079800c0c8080b440501d82c607190108a03026070000c0ea034031100008030040e078588440382c10390040502d07031208130803001e466210009000303d00303049400da9030015541c0d1101400d41b1810851004150000c28090040100841c03145010350b40040040403103150007404a6a240308030302010b042130a40320b4144007903a200350040c082c90402407120011004000303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 870061528 1250 870060278 870060283
    0x190608070f0f060c080901050904090b0106030c030b1903110a0b0d05060907030212040201030b0f0d1101031b050a12091406041103030c1c14040b090411030c090103050907080f 77
    0x6020391410a000b0a00015050b4070030303d1042003064001c000d9501c1c249035040191a5607010804c981d0700310b40c4a10410300400c40203906207000b88600d8401082c2201d0210f0300a04031340c9000e00b1240700301044d006090b82030100f0f002810a40c0d6100501028020101c0d002a141c44581d17400138144250000d0081d110342c3c040e0300a0f501480c07054030450129101c880040e404d9000d04901c0b10790802c031780d0000070050362091b001590b411340081c0080655802d032801003032808180c50300540e120482c1000c02c10244d40c2c10320650340d0110100c00501b60810400c0f44c02003043c4909210401080020b20907080c1e0441541e00480c281d541c4011400c040b036180c0b914094075924129001c0c1c540350340c030505c406c100e801d02100311100304210001400f000713401c0da00c9060301d65284012800403c42c0c6040c121104640800040c005040d240c240c060300d03000c90078104010f807010b4075035945001d0410300501c88004901030640e0003005007420085460743c1c0d218202e40c81c1c0106540301d07085c03d02c039085005d030404001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 870062778 1250 870061528 870061559
    0x5030c06010f0e040b04170c0102040e060108090703080a090513200c03041217310e133014030c0a05031302040606050408060a0c0819060807 62
    0x50400e03903020780e985090080304800d10307206080400d003012000a000408184000d94010310940c03c1158031500c1c2d10b04542150411590661182c1d8002000e1102004402c0100e60040d0300340b1b05081035240101409485150707031b01c0000c0c180c0c100491598001070207008120040d240182c03910741b0000c03449000001078090001c0f00b10030000942100040c8402080850754407010181c02545040e203041e0200e10603805804090f61642d061114200c440100b0f000240780c00c0d1800c00351802800341e000401035000b240f050103880104a414010407003403c010300001d91101002002c203102d4507035407d0014803039103500c0000040400d403448490001c0e982105040000c9001c0d41ca1880d02140e5841c245494481540d882582003800c4c850311840b144504015036010780417000505002103958007040654070799400c5040815008542030242c9241000000d61000508a061051122026001c2c1c0a514068842282e443c1c0411030f0980d81c0f07030103401c080c00401084044800e088e43c2c9112012403c1007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 870064028 1250 870062778 870062797
    0x9070c03030c0306060906051c0e0f0d05071109060303070f0c0801151a03100906090911060307200a051603030e03061005040213030807060f0617030418060b070503 72
    0x240c510603905091003441890142d170003580b81c0045040c1030660650351504440480100880355039003d8606070400d0259481c02c1144d6001018882c820f001024101107141404404110083c0440f002054881d119115030b4203040d10484101e48030790003c01e04501c03500038041c25640a2181c084100802100310004440c00f00d802000300050b00980840c4003001d6100300c190520485061120368409003005581100d0404e1108c406261768103540806d40304207a100d80e041e02e5031607004d00d0074001100d00071203a9020440d50a0b07d54605900b0103800c80114600c0b03158024078600048a120504100406000360003c04852408286080c0490011400d001c202c000034803184400c191405c00003500d50140b0f40d803500c0d41d140a4100001d200c02904254072995400003440b0001001c1910500104210350040c000820705910084000c4240d0b28103a2081001c0c070303010f220050840d840030040d00c00f40e801c8412004a1015190802d1000d45802d40202030420000070f0403070101b020000007894401d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 870065278 1250 870064028 870064031
    0x80c0105042f01171f08010603020a060905030613020301240f050324060409080307030903110606030d180e100305071a0f0901030e0d0c0b060f1f0207030209070c0303 73
    0x1003a11042c0c1d104078000301c124602042d10011400428800504c1c066070024404202c0c041141c1d01242d0605041c516501110311a590380c00c3c10f00135410032040e00005441c150421410480c03811001c40e6407a48000d082511b8040058548021980c083d04412195480d40c142c4014014400340c4298031403010384500c40c0401c0c4524800102e600300030800180d40b5221064410881110968401c402440142810f40c040e5980b055400015034010245d8040c103c5550001450700481c075011b07001400301896072400341c0c060020050703035580003c0c40c0050890989011010000c0210f84041903950355084100030030b5002d0308204150740d4101c4448100c1c1d01440c2150840341d528100d51040381c1c50301003072103c56002009101c02d2880004020000c4281c10303d00016001c801000346810041d44041c004009940c2c91f010409000c0b82d1480c168000c5000c440c2c0302a400c060100080030301c00390400c0051202403488607612024020700001c00150b402801e002900d203810705c170051030003c1c80c08084001c607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 870066528 1250 870065278 870065333
    0x20301060924051f0f050d0c1d010c0b0c07020d02030d050309061021140d092603040e2d070305070c0b0a1d03040b04080d05180904080c010504 63
    0x20b1501c2802844d060907192400400403580c81011a549020944c03940300303200d01000b401c03000300744611600000c0d000350341e00e02d529516102802500b8403200713505581000045410000071a072687c03d01e41e080200400030076900c000341d00c00f00e4400d007460b40c1c0181d85405240c404036410390308030004502c030f4032060f0f040d80c2443c3d403644681c01040904ac000d0010111136219402d4140c089854070010050084800702e12014800c81224580790340003042c0700018a1485003006004098144400365803941d6030080c00702c0310322041c5160b89004034032650744980b070f2580114400001000745a2001c8158060054145034800b40184074000241c622030002450100054656803107608440c0c200d692040000c111900c80c80f603200081d052829000007428404541040b1903082000100014a9000c0d1440d4603036103003048090904c804031f0700f1101445810060006003003c0d098103600d6070300080300c184009032510b040011440c0645c0300780284642c41d15041c4424441568203040b40514440b1302d02450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 870067778 1250 870066528 870066539
    0x807020c0d060f1d100203060d0f0f0203060604022502040216080310170a03030504060f0603050601051503060121091203050a0b040c05070b340810120b04020301060924 74
    0xc0c0704d40300c644401d0340d410071021481c007034032a60011500030000034260070184102e5121002051406a01120902001d8201008600f0b0034010190300c003c00301ca0440c2400c3c603250340d52401c240d92202e0400841101d00031202150b4455050303400150702203540315444c070400e10301407011350700a66154001142441002400340d00c03444089074010040b20241a00d950b41e517074180d01400026000b1503580d500c400a07050b000c58603100b944025400b681c0102200e515040600c034a52400108200440000700f08120003a6001485981100304207090019041351880c40d800c02032103120001040e080001c0c48030641d450b071580100b402040041000c110b611a8001084102d83c04001040e011510900500000c82c50042c14190704c00340304d0001c2402c00702e1101c030050f507410342c1c0d0300401c1c40255003180d100c10480d030050360325034441205501e100350981825400c1c4028991010002c280303148640014046403802e401c5003001f85155170060088240d0100514034420420845080022a01d4000110f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 870069028 1250 870067778 870067811
    0x2403270c0f0607230706080c0403021804050124090c0206010608060613050a1220310509010608100612060e071802370807020c0d060f 59
    0x1921100412040d201c0304107509100054102110954031451400c60005200c800e990384601400002030241542c242845806450b0318000342200c00100e4040c042800181c4034600140400003030540c1d18105956a4502075025212002c24000032101d04010740040500b4130b00180c00340d803800314041c016102c4d1460200c0c4d03542d00910401c0d0004065101164540c10004020003034005001a000c080c0d40e22800420480e40c0c16511644500c40074260b60b0b8103210368001212000340e0009000c1c0081c4040d2000a1030207010072040c90409003104000c60400403030202a1003405003031031011720042c6001c651980c0242090310880c4802d00a44c18141a050543c0c441c2c00f09844003401602020001ca40f102c200a04501055445610a100000c00c1d845020b003102180e02030443e00240e034802c0084140d0a0f0300c2071a00021803040380b841c03c2402403039404003ca200c09034a40c82e252102e980c942c0c0d0201d01d004201c89032190000c008008400c00e201e500c0c3c102c0200001409428410754000000000c3d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 870070278 1250 870069028 870069043
    0x1f1805070b07150c170f0f01061b0b010b0d0b10050a050a1e080709080d05190309020d060506031204060804110f1201140c070812090114090604020907180302240327 72
    0x7d003010b0640e0060142e58010715190010040003440b05c1482405a41c50011801c4203030070000d1020f00c0032648001c0800c031400f85440041d4143c84000340400c0c2e44401400703e0040200c3e0005112000c1a0044814403d020f50803414489904000c90101c1d0300341d01400b1010140c8155000801d00d00c0041001e440c00501894221007a985607480c02c00400d20b114800155801007034100f5495203100d10143c3c1d100714031400da071800390000246d40d0524401301441c2c01c006000c2034603030701400d00c0100704060b00055655030081c0c02403a04840582280c00180c1244440303499140c3c4202055101c40c10b0300c0b015805190030011480704440513840d40c0070030b181c8a0040070710003050118100a40f084605140404a8216101301d001003406825200714102c40c6104403614001607100e00100320651801c1070280b034008250381004501400c0480002c5001204da0001a01070b5100b07036841d01038000004680703420541c03580300c66501c0c2d0611050310003034080c640d204014a00403600c0012084400485c180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 870071528 1250 870070278 870070291
    0x21070c050c040e12030a150807090b0108040f0b0603100f020a1107050d030507110907120c090f26010903020a030215010e271f1805070b07150c170f 65
    0xb4070242019200c0701203130380e00003040028000d07102e94114503540a41e207102000307401e4003000b4103141401d000ca400704442104001504106103803080c0000b1500501145411a42050840c40079580320030209262110450701d01810390302c1e00205000c0b08803541e02030712004510703541e40200c007900d00c0c4c07505a885480380140360740304d244c0c2c44c0f405000a0065004002061141010740d81246650700054180e81c0103d0b481004030b20f1103485c950240c40f441c41780d000d491034641840c2075100e04007901441002114054003107075a03a8a8941003008421240c5030750042e0707200c03000380000045454000e440b507101c410210090300c2440381d0414011ba100d0304040c140d031891000020303142c0c0c0f01e89400903210401d240c284419100e204049146000a22000d2800b42d01001400310070070035154020700302e0701c1c6882545c60785210301600b58000b4074042051411214645170303031030b218400e908200e0005050141e00030901e44c9801809a01107400c004800f086580b0341c217640125580d0664101510725044a15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 870072778 1250 870071528 870071533
    0xd030f11070c210c080304360c0c05031c050705030915040c0305061e070905010e1314091006060c030f230f0910020102040b040b21070c050c040e 64
    0x1403140c50044521000c0c0d001007040503c001c00020344405820314030070b400ca40c5450301700041c07d11500c6c02200413040e06120340c4460031403c15071141d00203ca0b2100494648400d81c0300c40781d00310411321840f24400d44907000010359a9800403521041c1d00c02d500c803800c1c000c2140c100400070b40300790702601c25603128021100180c5080120901c41400f83d010080c400c0310726540750000030000c40c6003007240c90302c21903080d00c0013400843c1e0090081c400e000010034020402c6850300003841540d0b801a01c40d85098130551705c2e06c10000c03080d004113029110b80004041000b074a50b04004a1060005480b06000c024100070010b15490f030008951b0741710b00150180115110020a5030180d00c1200f59034a212601041d5000750003243c0300364102a1300940810312401004541c030741d10740c80d220146140d4110640000c40c03904c0d181092080d403600440c17140c1d13803500e40007003a142d00c8402042c40d15121216207403004401032401001c05000d0846250090300da0384a1a004c0540d10b08051080305070000c0f88100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 870074028 1250 870072778 870072803
    0x20306130e0604080919060e040509011505130617030712020313030206090d14070609080c09011503021e0c0607090e1602010b0d0b19050708180a02030d030f1107 71
    0x250030b01664044490181c216001240c1700c246c0800211100c00a0845640e502005540820800058990240c00c9402a92504140d80100c9110800344c0044510544400d007500b00f11807a100010b111030b0f800150301000c01c07810504042070100040c030741c0610420480300081c4415100f00e81e40d004040004c010100d1400b028405403404501072310031040d00410700c000031071175030b0384850248540c051241c0035a03101002c00e105480e041031110300a455500700412421010200144401a040c480e6686040643c020040c0c924402d404450b2441100ca1448280c22a1045461007642c0320324004c0c0d51b01c1c0149004500b400303101c0c08005044030b0f042e0244442039100c070709001c11401c112420303060a541d40d0301e62a910545804081003d1103016a541100c10700d00b010190041400a0380d0402d00301d45490108429241c0095845412000d0104c15240c0b5500741c0e48803918100030680d02035410b12490401803541ca80c103401c8401980c82d4000306006042040c3c0890701030b4040d44100a080494084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 870075278 1250 870074028 870074033
    0x703090e06300a1b0905091b030f06040b010608010b0c07060f0203040f0e090706050f192715020d020a0204050a0b0a0f05030c10081b1309020306130e0604 68
    0xc10004031410b22001120750192800001d40341980e01c00c822940c6128030148003080fa2902203049004000b42c48090207941b5140c80d001e5240d9100390721607280c01c0322400781070729642c80400100b8007944005080741c070f0314201402c00c45000c0d0300074801e210020358100004034a480020080c1c50001e2000300080c01031904222099443c108034000030b0301184414040001c95201da100c03500c000340b4191500c03c1050802074241406d010307454020b28180300040000c034080030725542c1200c10741d54038901113181601e50140101c2c1d0b41402550a81e184098214020001c981000780f4001200c40b104510070300c7c0d50b0014002d07038451810b040c0d4000560010410171000d8240364010703036845224204001140350154000621100007500103551701c0c814410140541d0038204885a101d4030200e81c1004091000c0784000c0c0500c0b0005c1804190b68010415440c1140401081d140c0341c00c215035580ba141c603222a4024004c1d00103c8101d0711840c004203800e01010000d20410088920f4900079054940c3d594 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 870076528 1250 870075278 870075319
    0x613090f03120e120702100806090a050402242205032107170a090b28030f02030a1505120309061c0c090303080a0c020c040e030417030703090e06 64
    0x316001070925169081c603c0d60003c00e10495080c0f06114040545621080c0188000303440780a52030000d001200c414021303181e4548284a82c417035a400c0c40850142d48078400b1070203c0003081d05911300484124200400602d164000d02540840701a07095205420442d15070301c66801352007125003607002461012012001001d02d51850f0010270745242c82d0280d03645d24014850701a0030b00114103a404101406070960092042c2d0080c5442a83c0d01d0910040c03403004080741e0044d9248681902806070060450360180d00325010100c96464215105d1500c166068060b02282c028001440401280032450346801d0401c4002c1c5070545001350b0034518a0014031072103521103591a500131210b000c0d1181c03849154041c5c496a401145d4039100e485196180241c050308024000000203810300700c540c40392aa0024200c0a42402160b011807941c40c1c4069040c21846684c02494100360701e00c2c25620358080020042524900c69901c40090300d540705800340c2d1054041d00c03d10782c4548a00021601c00c01d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 870077778 1250 870076528 870076547
    0x90609050a091e03090b0a0306080607110c0d0510110c0c010c081e07060912110109120302090402070b0a020403020111070608040305030a060902221505030109200409050613090f03 79
    0x207410011080d40d1a80200146c1c1d07045280312000181c2c55403401d01002009028464010840e801d11071103800601551603140c031510340c050303802240400e0800742813100400480644a1410f18100300644010701304003155408540b00c21110300c96058914900e500c0358003520041500142e0503810556241584038500301501e01030103210b0170610002001c01c0c0e00d0302c18004100e100385481c2244040c10034028000032515102030325681d14241015010038030707844101c02040c0c6945030060f0303a00e010340e0000d0024081e0307280207815862984200200100e26600800a40c3d000740c0314101c503440c0440016036551801d01507d40064050b00105001a000310050354100008140104a039521352980e84100d80004900c4010f03000100f00605410b81000c101e68003a1080800084507603803403903405803240c4030611840050555500d040020351101f941e440c0300c90454080c8041e600c030313581c0138a08040c000c01c3d80c1e036a2184804179400d00050fa400d03c565074505600100c40c2d400d41d60310761020b4079031220 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 870079028 1250 870077778 870077783
    0x2a0a032003031206010305060607020916030612050f010501051203070f0501021b060f0603010c02191e0b2509170f1c02070b040f0b07031701090609050a091e 69
    0x96181408455070244043c142c2411403804121240c0380200c0010140d03075000d4150b5000f10001c004440241c0c0340c061110ba40103280700340381b5aa0000f400d50072030052010b98840700c03941c003200d11800308005000c40c0303c040310a1544000d000d40d07620303581002440c101460103e402c0d94020000040029280c02010100038007640005041800301d1001c1001103000104140440e0004401c1044044d010700015401004c01d40080000c030701010740103940e030413800349004a04500c9044100410000300303140c1c14000d1240d0792500c000301e405d05d032072055040180c4466051407290750f032005500c405080c2121030100b440d942c0c00841c1d490001c00112406840d4200310042c01782149441440d10100003400c000d0450b006140410002007500130b0400c1015001340f091200200030410003901007607081030a50319640759140c4e95241d41d26050310009424101034280590b03410001403860b03201d5200c842203502d5040c05110903692901c1c0074007220380400000340381c84105070140407204000700341d0458032803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 870080278 1250 870079028 870079073
    0x30405010c11041112070206162304150801090908070b2a190806150f0705010c02070303030e030705120d02040306091506080d0e04110d020a022a0a03 66
    0x12601008201600d68070442510140e100046080d0300171403050845501c07020f1807010300700768100400003411507014014030004010610b07c034042806c40900c40e03030001d071603031802c415a2107030341c0d86220601c0c2a00c0c000300340204030310b8000016424007500608600319805414117241c80101e43d520350078200041c105028281c0c4070310301400355011030703d402c0c0d400d603041504003a10740400340845070038401c400c8001c00400c29103109114407901e4083c20034100481915405440e60420903482401d40107206028000750300f801c100d803507015000300e4a6801e03680655030501079030100da80b5160b80c0303114560300103002ea48000a8600001c4071040a00804503424002524042d40c0352100c03010f494a00009443c1130642b411200504e48013442100000c0003c800500f0a44914041c0503000303070344002c3c003c2d0203640c0f503580e0f550f001661481115035010740400110348420b0b104d00000c6d0b54201c3c80800c042082003001b1598816441500c503229101c2004080002150460355844032000f0b820f80c428207090b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 870081528 1250 870080278 870080303
    0xa1e0303121107051b0604050603011206090f0f0201020d0807050909060105390a020303030a09050309040c0e041d030703030e10051f0501080609070507030e03030f0c0106050909030405010c 83
    0x92000b4018000e02e07004800401908202c600d4034444039501602c5248140b0003000201310f031b602d6440c1034904464801c1300c0c1c1c81c0101010704041002d451524001800e00303c1000300c0d90208095490150030680c004c1e8225140d84410b84403d503510355054404901180c410300021500b880c0445001c0d51091041c90032508240041c800c419040c80300c8007000b880d1349684484100f241544100196070100c40400601d40380c512038010070f40340c0c440509000a201c5d00c0ea400802401020000c44000302000b81041018401e82d00005050350341400010348182d0922118030600003172082d0042c08841000003a514068007568160024a46102c0f000c0240c061041c801000580511656200c0e4100a0041d10800c104414410300c02161f508803505018440c4240032454441d006007d80c0201c1c00c0c20425940d10250a068440b082141400c2e81e041c4400543c01d040e20441c00050800c6030040c80080c400c2607140c1081000308002101c14591651003440100219032142e44005070541c0a020b460b80394 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 870082778 1250 870081528 870081551
    0x1030b010516032706020c1504030f1416060e030a0b060d02030111042c07080a2301081f180201200109030c1104020702010e0f0a0506180a1e030312 65
    0xd482c1545503442c0341c0a0784c0004100054043c0417416201d04c0c00c0303604191f034003e4649498081d00441c0406001e99503030300031442c100221340b000010752150420444401810000c0b0003444035802d802048000703018603041d0600c0703042c000703a0802c00c00e45c01100f601442e61031100344101a40100c400366070641d254011200800c0d9581d008001602c3b6000251a203822030203060343c95041210201c0d00d45d4104c01c01000b510560100c0003a4200880200102d041c00c03000b43c0d1a88100c640740800006d959900740001200b040010b400c0d880d1411601004150300c94060411003290b14422401888904888801d001580b06030201d4000440c0c165062017441c1c0001045400c403040b1920840c0415070f58528002406803e00e494643c18030112425072800c6290740c0000e0130550044003581c02004461035400d41340c0e492482c5000600ba000d403640c1e031205902c0007071004081040e11041d0094400910110340000250346150002d001c444c0c18544c1a8035642d000ca40c5200c4030a4200b1001d940c1d401d80149 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 870084028 1250 870082778 870082817
    0xa02180a09150f0305030306150d020a020c09010f0b04170703120807200a1502040b07080403140706080c070c030210020604061b0c020603130602070b01031101030b01051603 76
    0x1030031902070001001c2c4109a40b0b202202980c0e041140c565407020400c00c000790001040b00d5010205941111060042c09070b010a503002c0e00c0208078000740042000481103038000740c0c0310405082101c403081a40d98541001d0780010315405140014a4200030070b104800c0703c1b1032091402140e00e0b0846403026600d4846498121345240c21400103403400c000c0c400307800d034040600660b40c0c01062480c002c0b04412030704c05907128030348034005146d00f4000c180c080c40d404103641030306d000349101c09000307640745d55601d041c0c8241e03441408201c0f000014003806100c0010f00040d06001c0c0da4180d2104000b0b521201d00500494000350800c4410403030740140800180c4585880b00786910b81c80e001000c16081034517220007aa61540f0124032141c40c0500c070000400c0d0700c4503801100b5601a41c030035980e610350404500301000784900c040d15060001800504003c0b07070a14141c101c9014420b03021301960004011800d50300c64010306400202d0502c41006507040554190408600c41d0a0403004075585003604c03003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 870085278 1250 870084028 870084049
    0x50114250b09010c0905090f0916080109020102070e040b010b0c070306020d0c020d0212190e1e360c12070305070e0d050615280f1403060a0218 63
    0x5910803501c40900400710707400d000e001994201030420082050078040464152030000301440c0010341c0d10004101c2e194001d00003042140d1440700c00c50380712500c0d400090f001e000315210407130061007401030005584403000c3c44a0700403913200b141c0900701c1e440e11011040302d401103031002900d8000c4040001c0003840602c024041c5640c445d20100703071822101c0c4040d0605452421620543d001080c00502070241c031022641c03141d0a0202e1081082103c4e84125800c9040407006074001d411100701100788108142283e1100804a95641e01d42d801000700000d14069a490400f2629051035120807030300c00080381c60352190403012001e040c1001d010f40001c0c6120240d40710700100303645005200340940d0150742c0c1c05218100b41d030560301201c4d142d13a5003544c8443c01031500c0304604010b00c110445698401d003400c0e0303464444044026010341845003100e10b40007132103881300460107075a001804150003111800c1c001001805850740b03582d8446003801a40c0900c070640c56040030149000f0b41a9140302902 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 870086528 1250 870085278 870085283
    0x52409062709130c1e03020301050c04030605010b0a05041202060c06100905062407051c02150f07020d080703181118090a0f020a030b150f0103020405011425 69
    0x1418422541031103070400b40504280c91891004028102040c81c40c40942c0443c1d545039111403a00c15035819410101c42d058000035815402c200500040c406e480000e8001e8038051b0b1820049a41d0301c103517842e6640709441c000303004100248000c00581c24022001041d0a00203820301e45411985070481d4102038088a00b100415122442070150700c04074464143e02100c01d0718030b469401959103090f00c10307003074201e44020030400c0042e44c4810810188140100700c0300c81003410400e0603a0040c080e4880e030005c8c070211048074003400051058a0061034441c05804140c02422040170018000c590694004003940706040c0c886000c0300c2c01c85111840a80d080340114550303003611034290308100000e11456801500d450803c024000301d0a4041441d17800d82c0d500c9940013021580c20300c040ac007041d02c070b6230002c0c10025000c1d04020041c050701707540c85140c1c40221703000b4901c8084c400044d0124040e034080d45000074800c240900310800600d00034115007000c4941c14814ada00409819050b03001c3c00c408 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 870087778 1250 870086528 870086587
    0x109080d1505010e0109210503030711190305030112061103010b0d0501080307022206120f1101181e05060a0c020312090907120e011d0705240906 64
    0x22028580d00d01c240100c0901002d00e0a10042103d5600090042030180901c2840e441050050100e054030740080b01c40309548801529103e01d0000d2029081400c0404050a03d0044515014038050b80c1e41c03c0400c59035040c0c80741030560b400c3c44c06050300c1c145081c8045400326502c032020000208408061802801c03495155956204000e0b850425200d06a0004e07640354001c3c841c800041e603421130303907901100f000350715000060070882d00c1101502503039110b1541c0b00080840d10317050040818492017a540940940a0f2070b0403404011941c1911400c00700c2400c0800e803006208600140c860520100e101d40c001002090722400060920307400080c4a10101e80d0b42015102141414800c0140c10010030881c00c0c181084040400d4030400b0050080301004400d0a507074031408810342c44040804000c400801c6504c48408100440501103101100340d032040030300024841c03602c1100c1280f036121102d4025014412840202c0c0203402c03048209602034002c3c4003842c0c03500e00750020b500035401080034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 870089028 1250 870087778 870087791
    0xc09010e091e0c0103150e040309030c06082701110d02120906040c03020d06060308070c06141809100e0a140a09120822030201050f0726090109080d 65
    0x34003a00c0d15070348519900c140e04020a0000c2c8a0001042c205600907080c00c01052200072428180d43d144180e4006499290103002800141a40050480f042da480f034010b2040d030356218041600d00740000c0361840c2c0d90704100090030407240d01003d150b651400200700080707808895000c1d443c07180c1c1c10240010040320b070f000c56482c00f00c0d4500d0002c1d903085030311240506014103141e120302030845400c0c0400fa008210410345003041108591001c4015a008810306840304401d00d8840700b156400e2103031000050509140c003d81414000807100d441c00c100c2c01d19507110009400f032006604002300ba02d41015030f01c0d072002a481d104c00c4003151003408030705800158aa241020847e20703400c054a81004540740007040b2001601022034061030a84505141146d40d440c1101c24808441001c80b10414501c202c03c0d000825405400c040d0265a40c000c0854960760380080c2256092003413190381e4a99580e82c04048000000d42610a8000900100205e02e2450b80e840b2222503900c4420901c0003141e8850 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 870090278 1250 870089028 870089041
    0x3080903010b0f030a030c080421060b0301020f0414040f021c06060e0901140a150201020d140c0a0809010f09201807050f120a051e0f0103030c050c09010e 68
    0x10070303000450b1049401034081e0350200c1c080313a40c5644a070380040901440503400414040302c2d0050710300514440110540c0005a1144400502e580b020211500360400c102d11035240b9060090711045080507850340e0070289091324410980702400e28454000e9901c10309600000c006000500c1c4140050b0302c000c004032944040707036044807001d52002d01007240d14003030034183d0b5541010850450303c1a11428510203c03160000791403054540c0320060300440d90340034001c540e0301034001e00458112440708102915002001552180003106c0d525a003200c10013019400078001c201c1c1c9904100c05100009000001d2400f4401316141c00341e05030766014003540494050a01002e1102440d0001d80e102c000545000112480b008005004e04003400408601d0008803902c20085d0b0303a0306e202c1c070112104c072820720710550801030105451010380c92040000604110b0750b80c00b82d441c00307a064203800c02d40030f03031035038404881316460050111750301c1c0100b401c521069543c0400b5240a4800000401031504004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 870091528 1250 870090278 870090281
    0x20d110307032a170a0e1c02070515071b0308032404140601081e04060c0225030206030712050f07080718030206070c030515090d09030210270308090301 67
    0x960f615080011500c01e0001254403003946090fa403510304030449143c59003807612001c3e04a899992580c0d200350742001c07500c905441c84490803401640c00b500e42054a62090005815a1442001a140f41006410000340b0310300800c2c82d0032100981600c010703d444c3c0c0e40d01c0d0b101e42d0040e5a419804902c8001c41c013030083d41d101d4002d00c103d004036020412603080460311070114100800546c14006c0340000500380c2022400c01011542c20004000c1a520b001c3c0380000060034180855001482011032246949285da400440d040044002704404149550b0800c1036952000b00700070100549010300c4452102c0e140202401220790308084240c92516100c0101000030003060241044401408201e4941c0c58511b00e50549405488203680e0f2a01410002a02401503000900c0b5114141c0c0c400300d010110503141d80500d4180c1c05580d40d00d41c40c894100e030640c1840c000658000104c49041d035000e030040030399015120789a00000b11a00320540c9c0c0c940e0300d0704039500503a46020005443c0d81c1c0c9180c00e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 870092778 1250 870091528 870091571
    0x906080f1f08070e1e061302191709030f04031b21030305061c02120a0524100b03060402070606051002030901032f1602030610030203100e030d020d11030703 69
    0x85c2e0700100c00c01443c0420f9811100c2e40904468080e8850410002d040c0c50341d40c0480d210320420f030101c0d5040754008079000f400303200d442000d080c00c1d00c508404246903040c04800c90302d8448040004d20300f058255102d0002036007120b40540c0d0101d07100bc200042d1401240481604a03603400c8110242890a00f0064103a402c01080548200d00158055008600314071000ea19580c0540c4c80500c84100d2640d01481c05e041084054814030811003d144d181e2000d031841189804003c4110409440d031032120a010a0a400350400110091001030440d04159000d0310381c2500442001c01c503147d640c40440ca40d0210002060b00582000810100c00c0d40c00d401a43c0944840000a11a0030030305032400304100c407100c2e2040c485500c0050303d901c0322024810405003640e00182900e12034184080a0110810140320407800f0780144640364209090300e20500042d00100c801079450400c10f0101c0c14002d47c404182011815500d150071158400c1e07520180d41b140302c040d14001011428012440d144454 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 870094028 1250 870092778 870092791
    0x20220f05040302190503040506040305030307140c0303073b12150a091407080303160e0108010e0a02120c0a1701031e060b0d030c020f010906080f1f08070e 68
    0x18601800006503000400e80140c44003900018104c0080b407514900714816540003070351007980803c000c0140700c0080002e40c007807002c9484001e00c4a2107070040c400c0500659040e2821034000380005016a4010007003000842c411609110300401c044800607042c0c21641071305001c2c402180b074001e0701424611000925640303084024049000500099840399100402c0f503180e45480b85002e004100a4410314010440782c00e046e02c075030b9508c503805240e9a40041f00c1041c0e940c10024401c1c0ca41901a041c0442021010b075280d00c010381c00c1c000380c0c0c00072903800307045070205960030800b00c100041040d00803802684003a00d041e0742c50504d428010041d4503203040e2984643c500c1d400400010f100504103401039003001000c0e5200f81c0e86c40c01c0600042500001080d041615504540c0c1010303409814190180e2003240c102103060504070044404180c0c07401000d020500100210b12418041c101710381c0c1c40004a41404c02107030701d40380921001c50b50f5501c80e09160b8000c1c4024000306c5520004541d1219 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 870095278 1250 870094028 870094031
    0x303080c0405031b040912020a05010b01030e100b1f030501030203061b04120501020409140f010b04080a02040e100e0303010810020306010804140c060a110c040504050a20220f 77
    0x2400c00001a4582c1003403500204c1c0c1c01081e0b204ea10781501c4507041b01c03e42c581c1109a46101e2800c0c9600030f510749a000001300d030170f54a0100540d40640c040d126130910100131701d005001c0c03070340031591481c010000c00740955030110030301c55644840344160251002c841c1c0d01d84d41c0810507502d184141860f008015000c205c00764412040f0105c1d03203080d03e080d80e0403120300c80f45d02c240d840c40c21b042c40b0f070080c425500700c464a541007904200e200c04402141c80c4c00751519000c610002e80e40da11041089019a0042845680009071201e004d8581a0044002c0e462284142e50300011103a032510111692551002e20790b401c0440100000c01c0203000500100c0fa8000040d45507261040000b00801d41c0108001d04408400703e40d40240101045031002c40c00001c0c103925a6001d80b41400380c6400d00054001003140700f106088a0307242098000c0c58041c0783c0c018018200c9003500d0f40d403000b5607220f4909501c80701d10b1140b44400310b607849501c0140d4a000c4954a600c00f110140840c0060307411403a00c2d0415603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 870096528 1250 870095278 870095287
    0x90b0c09040b10080f04110d0b0609090a0213110c0304150809062205153c040b18060103031706030c2202040f14030c0a141c14070303080c 61
    0x1260008083c1c1d501c00200d07200c80426075124074140101800312025550007200384188c039001c000095103038a015001c111440340f000d40d40d0701c62440e5035110521000b0f41100d00201c0ca002d00c0d51403034100d210100c3c40500388600b03011690b04002d1444d04141e011a0340d1000d40754268800a40005500380c20560b00c502521040c64920003440c011074502c04808408040f640c031884c28000c0510091003540351182410803941002c2080070a50350b0009001c0200114000300d40c042c0a04c0d4194040041048420108155403161150740810030003d1082000602148101070025020301030301d8060b52190300c40c90f4024503402c103181000c29006040c0c90090340141c1d04150f0954603800c440c20110307200c10418050088490a10b0701900565000401c45041144041181d03200e07200140e0300e070384043e003c135135070042c3c0b00d01040810145e80c403413039035100075000180080d41003c6450310070003461200c003450360000640e60312154024080c4042041d40101c9c01c18400c243c0c4c0a07540a400c8105004614200b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 870097778 1250 870096528 870096559
    0x170a240f32010b0a1101050708010510030e0709020a0504050616030e04020702031906062304050c0405010906050c03041d09060105060309030d090507120503070605060102191203090b0c09040b 84
    0x84400600035410110408100d00018a1207582031030040001170009001e01e00f00b45e9006082a031080c0030f030350b01c41c2c0e040c0c0409440300c80c03007413003087c812061040090401d9441c004140000354004016041040b00030000883c082c0c44990050441d0500a40c5210510501d420028400d2240c10b1496200c4c600401c10840940d400140300e404418407002e880b21600c2ca0b41c034044c070003040c041c0c0c06882c1c1c091000004102401203003003030440d40c40c005d640600030707aa85c400340c651462240e801624042801d01d042030010038801d00150600310285d200302c0740381c652a0394100344940c48905885c81d414141c8410800e8019040c00500d0042c5002d80703005007035007807844a0545900400101c1085250307181402018050704014020041c162010917440f10903490901c1c6490354081e001c269801760408000c00c625510000c0c103603129501640c400e800c0c085a5958485844440d440c083d410175880303403010380209043c81401d601411400b1009690303a082c0009200a9030b4840756418030604559049584 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 870099028 1250 870097778 870097871
    0x3060213090b04140f250c03020c180403180902040e061f05030105060d11043210050c030904060b04151404031101021f060e01170a240f 60
    0x2c05c59200040b030040b66aa1808a0348018543e00491184001c9a10040c0da015000403403c030906019a094404d001c140c1014400c034420500300e400c4036440c1c0c110014010910483c0c042910080400c25042c00c2642e5101580a903002070f00f100003510701034814009285801006c0180e040b01c81981b402080d8240c600c003030305500051207003074000e80c000501844090302035404000150b00c0c074110161155141c10303000064044e4400c0b0001285a114802400714500400e55801014024032805c0462542c032811103103504103160100c05884140414085607485006000c05001c2101203075840ea454400c0d9800744082010608040c0307d0201d81d600503040e980700480d029030381c01c05215140b440265004034584440c0031941c40e090310758101d0070707140024240c025030f08842c529030000186980320354446009580038000320035541e200444c02c00002d030404000220300e00040d5840c440c0600d00e0700c3d0340383c1504d0020200c00c0f40241c0d244030303524031814400c1d032203151150384000c48a040c0064120604 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 870100278 1250 870099028 870099031
    0x70801080f060a050709090519140c0f0a1b031106011d01051e031203040c05040b010e040b0103182d0c09020f0d0905010905011406010903060b0a03060213090b0414 72
    0x1c40b11511390000031005400b070080e9200600789490104010324080d5070098901459111a044450404502c00d0b034403490151064000c50402a002e032501840800030f00c09607000550f40f8050007030040c2007100014410002d0441907000303480d110503103441c0000325410007605800185071120481404184081c03000402c605582040d940042c45038550300030388494402941d000380c0c1c9031107070071034803002c42030100c0c0650f0185115100120a1030389038010042680c5084080900007041403500c00380d039140ca50003210350b01c0c070181400181102100c510840f00c1551500644024200b40403030721031584070310702d80e0b003450a4030320000c034080315241e80720701d01008284100c10302c0d1500401c4101c80c00d102d8100f02c0e2680350f054141009070703620601c0c0242c06013405407815078480d46408400e404080c0c030048101e00c01e800c160f6502032540c2c207507030f1010005c0c04401d080782d070006007002001c00010024401000d410800d29003241d141407511650303105488042c08418081c0d401c1c03980c000300341401a0441c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 870101528 1250 870100278 870100291
    0x1121091b0111070305120a18030305030c1b2509050403050307080408090447060c0102070b0405071a0a020d0f030e070609180522050f0a0308070801080f06 68
    0x50304003400e20b034109450b210035074002401c1402886080d524a030300c05001030034020800d480c4c00a205440720303c1e049581c09944030150100b042000011900c2103210000d044180c01601074101040140032400d03d001080301c14002501601100c040454200210080c020220f11400384403a05e403542d00100b00d4000a008070043c001c1040110f000c000075401078404410300038204014607900c039105c081d03054850718003000314040c4401000441590341032040c0000880719950310029214031023440b5140d8401603882c0465542802144009501544002d006600400080207600e080c00481c0880c42007680401d41c0b00f140402c00907080315008111141091206d0034100300c60800d0031002d8014103000d0b800ca5005024100e000b103803d0350404100c3c02a00c0000382e24200318604603807000121042a6a400d14002d0880c2c130f445000c6000301d804848040c400c206550550450225061a0255104040300800c9a0008120610780d126001c103004110702001011101d4541e0301d030030303150940603000c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 870102778 1250 870101528 870101537
    0x20a240b0a180209061605060a0507030c0c1202071a180102150c091810080105010503010608032d030901020a021005060607140717030405030d030b100e041121091b01 73
    0x1201266541c10f015036500384042c0f4071412040307006c1c0c40c1440d2140412070340c080d845850a4042440f0910038420392002420907100c0f51154070030398949219101044503030604610031450041038600c41581c045043d01803042000e900c4d64255264602104101750495045602c842ea44803452005020540e40011120001c076030340c0c0d4070100102d46044144031801c130006104038248418007100500403822641080020012a622a81090b081e121988680002c95000380100440301e17020510098040c00781c039007038168001d011211220107070000c4030303085556507011441862140d0140a080c0d442040758600300407a1400000040b424040d8403030150102111404e02120510100040780183c41c4030724a0030410b0304502c11241d5030390301500501c0d000c0c0c00740d00441c0c0040e5006e40100090154002c1080c0302c4a890340070101d0f40008800c16041e80035494014000f004030003a0020022007070741c040819030840002504c1421488081c10740c0801d540490010030b40d2030751041d048410038000f40f03030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 870104028 1250 870102778 870102787
    0xe0105160806180403050a20070b0d02121e07020c0a14030c091503120705030415050f0a08040303180507060f050f0a02010507022e020a020a240b0a1802 67
    0x1107601402d016860510f00b0588409210501d0740150107820300740342c00c0c0e80d10346010401c2c041c0080709040003401e10300281d100d018280510781c40d0402610360203070008001400c1542c1e81034080c0031648151980294000c0305c0d0300600140c40c020314003079031101580c0000c1802108500209201011078801c58401103021210209070750340c1845864540389008110501c01e0504542224000c2c2c502241c9512074414810b6822422a40005950070260404003950800b46818034180c0310b1000c9004100c100141080384540d003a041c040030340105440c55480349680e123024076001e0115400c101401a13000c04000c2e540000500028122094a0715440c000e4213a401d442410703241401400c11a0018600100303201d480c1ea5030540c0030b640314071429421104140038101003944081004c0307604000504c0342c681c40240b41c00403034005102c40b41c00c0c2c0c41200e541403460703101c03046581241c40e031100c00040010441491030f00d00f401400c0c4040c60458800001c946014182e640e66903800d104c5402e11500402d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 870105278 1250 870104028 870104041
    0x6060e0616120e1003050112020603040f0f0602120603061009021e030c0c1203041e110315070e1c0209180609030405010f0c1e02130f02030a0e01051608 67
    0xa181c00480e540980c0802a602294070082d040508488902c0d01450000c41c3c104040c902c240a518101c407000302c00b0040c14101502030085e035920045c020380b030b0040541d603980002522410100d01c1c480c09000c006231580c0c01c00c10030455480028003443d01c40c0c0c4c404014400c070404081c640004694025400680d501e980f40c0c041d400c101724170010511109804030401c110186000010b1883c4850740f81600c81410a4103501c11580c0019903018141d80d2089615446041003c0c140e04000b40c02039204011140c541c00000f07203030030301100e1104c6c210101c00003031003c21600000104060141190b040c4503110003480b071103218004070840603101e00244804940c6122287c00b86440c0810300710281c3c0da140c681062880e40c0e070390041c483d40740002c1100c012807042c0d40c49032004681141e40034a9202c2141e282800840d807043c4401c0701640d0080e485041001404494030078003151101d00500580caa1814411490444180e100c00400a034149010418001c0d22a03840c03282601c42070420703416640300c07071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 870106528 1250 870105278 870105307
    0x1506021c0e040e10060b0301180f090609110a050907020a230d02030c06152d0901260a030e13022101170d200123010302100306060e06 59
    0x59080c2c1192501019040c203400110344189079071001d09062000d2565486040401c2c44244a2854040e00f61107604604803001d40103682003d001c00b10100c0c0c07443c150b840311412201c284000b11640406402007060b1400e1660690004110407139400d0b840d890000806034889503c0100100b04003a000070a04803103481404019a803280c1c20201c0300203144000c2c01940e254010b900001c1c0902c1100e000503001d078550f8003100c00c4410f0160200141c8080c0340c50600b100031078003c90321445202207881c02da80d034a404030150300802c804107042012014450001340d20302c0d02415000103a410008148c0d0100750400d0503040c8035042035620990300120800f5610090251a02904550b4800009460000000303000d5a060321a4072145812410105401a40d6800300340c4d14040410354182c1000c8414500c1001c41d10004802c1c80041000c0404200c00c45000005000e0391400301c10350b0300140107508000d8081480410107007030402400e801d00d88060890355600c4d100c603206020004414150100c407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 870107778 1250 870106528 870106547
    0x15022b030e10022a030409050c1b0d1202030610180f0906140621100807080a051203150d020a0801050f0901270b0606040f0e0a1506021c 60
    0x24105807005640380740c0a0710b020354002420040800640d94140e44030000c5651101c0e0780004400066150900c0d01c100d00380500002810350400c282c051015078803d07a8503195103e1600131103405040d40c82880203000c2e2095074694000c0110714410700c10020030b51a4141c0143c412180341c1411001001442807a0b040f140481d0001c0b503008a145100152601860300f040059503e20446d04c0c5401c0300030000d100b0a801910a0001c1c2c4844111030010307280036411301036410203034281d02d80740c82a0321510200e103000e406510207542e541c801d2403d40248034040c80750184034100500341c0752450800d0101c00025000f0040e409205420101c190400c43d40d1300070705a4010103082009000625104d1811080800304452402c869424094910744250340d01c101c0b6403500c0700010036803500441c1c1e034880c003000e803c0040450380c004808010200381c00c079a41c2c0c00308008040d0142010560304c0c0c120042d400b80e035801041440b4001d400c8505210480d00881c0404e401c0a440c910030108100411084903041311 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 870109028 1250 870107778 870107801
    0x2109041802060a080114010e1305090c040207051f0e060f1f08010504150c0512130218010320060d05130c06090f0f0503030a0f2715022b03 61
    0x400107030075442c01e904130000d00d0403a014402c40c8811144001c0056508030b039240b0040b644000c40e016180030001e80c940c041c170f80094815045500c42403159000c10102e038095401035031654448504040c48042a1400c032040e140d014405001070845603d007255128006000403d00018000000d241202805603100450031460a0308030181d568402c914000c010a60301074500b007140e00800b1b10368503494040c5c5007580c031513030751240c1c03421342c40180b1422215406001614010318002000016035184144000360000c80c0a103030fa100d51442c5017440144170307444000190345100780f04843c0c2c15681d010a4880310440c45801203000c2c1e5911050740100e1380304440c001c2800c0f0010402042882d4004145400c0e21801060080455203c11010100101520aa9906601c10072111f00c500344124042800203d0030b062100240381a0b40111014071207a51041d030f40c01602207010440c2284001c038204446055001420030200c88d01d210306c032810703565a02d0441d087e504031201c0d8280c03840303944044040d24 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 870110278 1250 870109028 870109039
    0x411040609090506070e1c15050c0a090f030201080703021b0d0f20120a110111030613020a0f050c07050406081c0216270507020109052109041802 64
    0x40e100c41540c0000c00b02c01005031800c0c0b003800000f0300c5190007104006440d000003402207814111b00c14001d850079039050021074070600d943c2e902c40800c21242c050079010b407010014880e00c400e11420000d1088038554044103040310080b90070005030342c1103688503800c05030a05e00540e603521105440140b020b5810f115648034451030384810100d5a01041412003440183da0300f0b079103a409540c1550741c20718800a00b1a840e00b08107800c280002c1da81008280d1a101410002408031403c10b00c0d85c00c4500d50590702850380d200104001503490503500000050030801c1003141000340d81100200b42c20b40000b410301c140000001c2c5c0c100e29510402948000702401002480001c5d16201401c0e110181001c0d06080090359600310300040b07002141e4054054128840a9801458210f20000ea00022520700c00102510301002d0050b6406006607881541c1680010440007914900b00e8980202d66450b8070384400c0c1c010101640c002100c084030200882202d0200c1d0042408001000f404080d0000942c40b6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 870111528 1250 870110278 870110291
    0x2120f0d0b19060e010504031502070611130e070512060103050612030d020706060b0909070c030c02151207030e03070f0c08160806070c03120e160609080c03071508041104 75
    0x4020300392540080d116513541e07010070110040c0055a03680582e0000038803041c0711003a140058109a8042c080c4a40181404a0f0380f100c098000d003e651700c856020318106559410600840d2020040540c108505280862a000c81030343c0090b900318004d40098101600c0c0c2002c0384583c1d1f90a00d80c401d110b8036a40aa940c0c6031104110b5100a6020000848200e801c010f4006920210401a24600407000c1c02c022040d541e001c004550720004100700b102031244a04200001d80c6501c031010442d5051f01c1c403d540e4a07124040039103503c0c40f00414a50405040090840810002009441480d903000d04000b101d12031600c3e01c3c064a03001c1d50081035181c41032008084030384544a2401c0c0454202606451090311071300c0003250383e44100303040030300403030800c600d1a021800e096100c0b002001505c400e07517015200c041c14516803203040350b100c080003601c2d40d80140300104062210782c030720400880c01441040d24100407540594103400049042c07044010000707080c06148240e00c40390490080042104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 870112778 1250 870111528 870111559
    0xc130b0a030501050c09091503070e040f0f030305040b060a03050c120304031203051803160803040f020a0b1305010c0b0406050c130306060f0506030403080c030a02071b1502120f0d0b 80
    0x5d070007814402c1d10903118000803c09412351208000030b0f42101a02500b502d40c28110800610340001c1d04c1180d04101c0205080007140c0701450700d900b228401da074040303680c1c1442c2c00c0007003501401519030342c4102c21540c0108001607001400118201c0196882481080040341c51070442c0140e90001c1c00341506083c0f045149645607000704d00c20b0000407413140b502c01c043d604003a900e01510385851081258a040c2401207014400074540c014418500300c500c0b0701d0305a02250128000d9405402c000602054103640d20840c01c0c00e07040a00f20a1800d0703034082d10291101001c5079800b41010f000d0541c0c0314041900c400241c1d0031101d2100d550409807540a64a1a208c00104030701d11035400305070101540407a0515000080301d000710b405581d02d02940c2c480c01841c07449544003810343c80a00394200900000a440f5803034800004a06c80c81c407444c803518200103c03104244d03480c00071007150042860000f00a201c40252611500711954141c0c0342d06800391401c000340900d14a8546c0100300c9121900b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 870114028 1250 870112778 870112801
    0x309060d06050918030f1b01090303062102031506040e160501080f060607030e190e0103050c040608100504330c02010506060406050f1201080f0c030c130b0a03050105 73
    0x2c64000381c03014082542e0b00320102c0c8040c801c480004290760400c21118981d01500d0b006006520480641e1b1105442000d880e40d00f1101206001c0340401d8031071804001c848904030004d0042e1940045001d2445503990010f41c03601c202c00c90409c084260300006c100c5a4545a201d503203007111764401c44e4200c1c0220f00c1c0c1081205402d1007203c0c00100c061340018108403242d00c0050213000d000e0a4503060a41d00daa0658584031400f9209401c12541a00010354075040f0004000074059600c40c60015411030401030f06000400c8001d9000d01d0a09004000301d03d00040d01d00140c2c22514400581a2542d10b050103204a50000a071a18080005090300a501c003042d0684445100b50b0100005460340400343d00f6541c04071807042d440502800100801c9000b4070080495180c440c030220319000205085e400e040500ba08821181d5100c0b160b810801c07001084080316a103021801030155501c070740001018806091072a0403041d4548440800c1a00c0308202c0d00081c59000009000d03500d09042a0803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 870115278 1250 870114028 870114041
    0x10516080d0c080a11090d0b07140f09120d09030f06110a1e090807060c0528021207030b01090209011101110c07060806030615010225090b2706030309060d 68
    0x51300289400c003006104141c180480e4400742d409010400c9252868407010665040102690188203014107803091441c410310041c0b2210401c940c0a940368401d00080c00b9020b802d42c2a1a202075000150a583c6e042c1c20030720340000c482e44a40721340601945490203002525a8492100a245000c82d40025aa810046c207030704004602442094001c00002c1c111010f444912640354190082c0c00b003801300e28810401d5a003c50300030011070708640000d5198100b0384005c0c42041c010018078490800c21072800c0302425104483c1d24004104641c1540c494503040d03d8180b141122460b400544a526a4007a8090111480c900c0008010a800d4440c00c8109075000b4140c25255014840c004107280e406610001c0c0102400342c01800c865031204030300310b00100c003069000d0544c4a07240c1b8004c0a103102c9403c1ca1200c00950742e1003040d4525080e0800c094464020496106805160504101d009095000102ea40242c0108215625004040380c01d508c500e000d415008840000c0c4031066a40396080310 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 870116528 1250 870115278 870115291
    0x91c061503030815010c020103020a0921030f14031303030b1e03100e030d0c03060509011805070302073309050604140d050706110d020c0d0e030c010516080d0c08 71
    0x381680d56516180c084081104411602080151b280d200165200e42c0c0a410400c1e8242041c00f00ca43e16046442d03202000d02c0b44240c828051002e103041059404640c1003030040301c500301b040c5490541c1c070030030010780002031042c0c10700f0400c040e0000a241c80303a000040c8400010300244104510130b03510300001d14600d0111070091050380c601e010754001e54461030300b40303030302290166052030209070a1001501c1d1105e032004c20540c0f14138021446070303507841c40385009200f500380710031175000d040c1c11402c1610002400305041c184140f0400010a11544548170703201d102003001d501c00c4101c640410074001000340c44842c00d6141c501d048040040003c0e00703500a60060100d000c5400c10514201c0c1d840e11400815400220300744844070000702c090300025990380d07924080c0e600744600710281038200e800c042c0d910f02050303101074031004206802201604460070154041c0c112280312000290031441000c0c5c907000c404440036190002c2c828000c060f5a160400d24800307004200341208010001201034030351 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 870117778 1250 870116528 870116537
    0x90e1602120306011403150604063903030c09170a02030c0a0501200c030a0b0426030c0c030405030111070b10030b011418010f0611060903091c06150303 67
    0x101c40107429044103036881010140c0d44d1981803108682040f026400241007032500340380c03050069000b0754901c03024001a00681c2e8544411207440303094054440050241e0b0326084580211503684200c441e03a00401550305070030003281c94000c000c8201c4960605603c030040d50901a80c400055140124160001600071012540300e6140354040117440c600c0c070320420740419400c4000702d0030350020514032035240992034107a8a42121140220b070820180307032822182e15403004108802c120010486e512040c00d0a8815140e50700381480900e003074803020f0110580600003044459216400708101d07400f4100282c02844003e21044040b82e903600140c04c1100c10040c8130002031880c0202d17482c0c17641200e1b0048041d4105910703185800c010b0b80004602c0e03e4000a650b01301d9406103040b407040500910a030000071034180d01e42840140050401030f40d0940300e400000501180700f80000503034903a40001c81e080340003948101551445c55101003070050100e0300b0300508504040340308004004a9000b5260f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 870119028 1250 870117778 870117793
    0x602160801060f051011060c070b01060503360708281113020f1308060106030209010c021509130209040c0c05060a091104020f0405271303090e1602 65
    0x300358240c0c1d10368002c1c1c8205900301181003200d49013204100e44148414200301600e4081801c900f0304281c000c50300c3c5203503a8070015510f41040b07004020301e401844145006821400d01121aa14070140d40c015080740c04001084440d4010504c1038925440c800710080360314460742c03404800d403a02143c2c403100078060284600314004103d222914044a0f9010f0140c040b2402d9040800c1142000402e5551519500344481000042244000d00a0012065030b40580a2801d05402d2510605800c00820180140300310102d998020340054601c43d070443c0c00c0c50749803003002d0404255000b0041500d0b880074030000018910f001960081c01a01c0080e07078180702d00907201c00144ca03e921145001842a4030070000140580420703070041080038451160808106204000503081c6d800020003202d00341e00000e0200134920f442c4d900380d954140281c071002c001e29401c00214000e0072004200c00a50801480c0f50340406200d900c61002400408558030791074240300d00300240303d100403410040980310f21309 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 870120278 1250 870119028 870119039
    0x91807090e0c090c0304060509010f06090207020321180d0b0f040b0f07090b0d060b04141309020312030a0b030304030c06020f06160c02030a060c020303041e02030a0816020406060216 80
    0xf1a26201c1d02011440f689542c803550340d10802010003c05c0c1c203032555600e03500308a075227004d401000000c2c20750300009138131082c0381e0040500300700d0320485a000c00401c00482e0058000c0703080580b0325120305210701c0082e500c1c01c80003041c040c407409040182081d408030101f09010104100c0c05009a000b011902802d40d502e608201116034259003940100c2c25a0b0381c2007103080074020003049000840d1001080040d034603c00a00d01e900a90440740e4860009100d02e082c07030400380201d40f1411a400700034851407803190013203900d841b4805541004820004001590082a40c00041c0c84d000081d04032a07685070380c0c3c01c15510a614074000c41006000c1d4401c900000140002d40c3d1307010b02c007006042180c0b050b0b6601c0a9410707000d400e400700c0c1c26000b03c06084d40481d5687c80b80c2ca2440512b90003456070b07071901e40361041c1440d0320f003281110b17003031101802070300541c8000505d590866480409640e0311000a5448442c03400c0705500294014140070003c030746181d001c41c504007261195041c0c02061034445 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 870121528 1250 870120278 870120289
    0x30403111c0c110103090b04060501150c020a171f0902040b0f0109060f020c03060f1008070f050405310b06031b091308180f0105030114091807090e0c 66
    0x144600015440382c407254049a0400e8100b0449401410b0010b2403030103640d40c4101c21801140c0c16214180d603080100030320070a910f90a9204d0740c01d450f058442031441ea00182c012025030040e40109540e080784841ca40380c0c100640409a45200550140c02290785480d50103071040c51400c0b0302407410484413500c6400c05803000440741c3c405842d5030038494148602154030034128070300d00e8218402e144102405031801d1056502440c0900b003003220510f810784100c0b01b00000381c0c0c0440c030b80790f12003241045940c0140032580191201120080790581b506506110400022850341c012884a00101700b0241803180300a52a1403244107000c840fa91200101611860300004400f0604010320070f51030985007080c900c1d0745c071800000c108040c0b10b00c5511000c0e029045003007484845e10320020300140525044504180894003464198036641c1401000c180006082203440c1c0110007607404140c210244802d010103000c0c0310001c4444080d99050310001410356404050001c2c02041c0480c06141443c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 870122778 1250 870121528 870121573
    0x50405060f040b01051b070518010302061e04090e060a141308160b0f0f011a162301020d0e0106030b0601210903081e1506070f050303040311 62
    0x60a161200340014103102c050440106902e041140401c000b044071214000010742d90141ca41c014000300d410402880380307001c44c1030707403400104015800400050340d0f460111051014402d040c1904941040c01b89005405a034020310302490030405403206214001406a108036001e40003880780302403900410a0554081d03c0b807501034410511060081400f81d00101612400708030601c0e00940c0b162100700c0d85070016030300060348140c420240a1007415a4070b030140134081c02c0e06000102001b80c42915014400c0f0100480c0103102c00c2881e070107100c00c40c1d003000001e07410405641c0329110720740c40043c002c3d40b100107171071515031034282007110003a01449000d00703070f07030780b0010300c4941e600c415006460300d43d4001c08901103103101a100c0d010740d0340a03001302c41001d071003612822070f0b601788502c0c0c0000311959102d0780c0c000000c130f4404004103080c250009074001e54040d1400c0b039855440d81009110101d45050181080c400007050204055128007199070008140e000c0c0e901c14034215050f80001c914 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 870124028 1250 870122778 870122791
    0x31a0405151605090102070f080102040503060a020f0304240f02030a11040311091803040602060f0702010b0f0f03010f1503050d0513050103020d060513050a0f061d1b0309030c07050405 81
    0x511820b011060180000705110309050045800584e51114124000b00c110f400c0311070165004101040541400c1040396006086410b0035402e09011207a0403003103000090002d064a484500c4401c0380031004403000312248403402052040602c80c00d41c0d000a984241c48402c1424548030509203007200440c15102521360048030701c0c10750344102c0200111050068078900c1c15200c205a4506101c60030002032004181035005801603141444d03080c1c015010041c90346003075904011505e58035546680d106103400b00122064440395408001190040c00b400100d1a062850044141d071841424840e4408491241046500c9070940c03580485680c0070720b508c164462141144107200c00e40c000e402503c4a214514000180a03607201d00060030851001d5a2104030b907920345c14001014641d014041001408000500c08a85816035400043ca44a19000140c18a16001c20000c3c40c026140c4002400394292054481c1860031a068903980a09104040c030321071024000b42c40d08050060728450725 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 870125278 1250 870124028 870124051
    0x5031207020312090121090c090204180c0212211f06030e0a02131406090606090915030604030503070801080706120c170a060e01050a0e041407031a040515 68
    0x403440e03020741c005034120080c0075042c02052074401b601d00c1888100d030781400c03200510114038004541094251104280c108048141c0100000e011b00c260040c90103218003510f89001500050580b4105d040200e44056400e088000080c0443c0800c90340034031062020622402454a85a120000162a0b12402600086540d400c010041540203034000320300208000c054400101003640043c10b4401c3c500070b4403414550318140741c520214040403c582c42041994540700d60708140002a06134040c02070a140304100800024480c50320b0020300c0c0d02c10300c2c00074003215924142890050810f80044910f0000120b0840001034109000036a14007140d043d62104401d0903d10300c01d1601810780c0d82424028407650001c510340399a450741e1450302c10151094000703290782c01c080d051420ad41060707221130300c0743d10075410034040c4c2d0520350030054100341d105401c50b20903020107400504100f13481e0301c0600140411254000c6508020311a0f6100b14070810a03541024400d00c02402410310503102d40244a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 870126528 1250 870125278 870125293
    0xc0b1c020304050a1b0315020a0305070e0310020715050c07051002390d05040819080a200a0809121603021e040608010207030816080609071103030f01050312070203 72
    0xc00b41d88804141c80e45a50400411071b4481e2504010040340c00c80c1452030707543c0003e8103030300c1641c14810036030010007503d00010031040c91000240c0d0382c1982c5034140c0d00e65038005038480070851400c040c2000017444c403034140010b25089030141459000004160b400740110808040c511200744200e41402004480d9201881c0b01104841c90355403070700844003207440e80d1508070742c8000c0c0c04009100194006684196655040001d0542000c901c2071060000600101c0141d00040c0d0314001e0710107200c00d500d0568119810380c4c4041d8107602d81c3c16640c00f0700c0d01806001c842840200b00042055050559040301200514038601d5510b5100030742c6107190320711484003031005190014541003004a88415002c051802400140488281d6488202640e42c0050030030101500007a21950101c002c0118503054010f242000d00070341d000070f0115210340f06950001c0c924a00880f28041001a49412240c0300d00e00700c40320b812070880c02e00401d4070a1050007407140300000070004440c01c45a020703000e000f92 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 870127778 1250 870126528 870126533
    0x11412070c060e01022a032d120a0537090501060f120c06050f0304080f040f060c1506050d140a08030403020604170a0f08060109030c0b1c020304050a 66
    0x8a40342807a00b2506542c44070f80040e000c54090015040e44c5402d0209141c2007142a855240c0424901e213003017009030400d220314800d0788101c0c030031070061303d8042130201d4404d10501440003042c810107400301003400c400414081d40c000c0d0703a8040d5100e000403072070304c2c01c8542c03002c125080e81e0354903c2890310841c804080c1c047c1100c0c2e910742003140b032603200e0000400c2c510b071079105400c00c280244e0043c03003448440340204801d0040450301a4010074460610310720b00301c00300340030780c03910310000300301803c40d84000807582d0703910311390b82e04840091081c042543c0399903407a98001070014400701016544140d841c60801d880304954031442c41269001440746c00c0351034050b85c542d00035258410940c00c1d40d02078a0540e601089c00c00006620462183d07000c1c2005181500e400d500768544100240319104003440304007061500408236507001045400e004599a6070003004807603500090f00010250a5241800240129420b0142903203000c0058408072080401c0c4540c0c0c200d000458001d45070f54000a1907902 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 870129028 1250 870127778 870127787
    0x7060512070f12051e10050d2405130302100b0603070c0807050708160801140406020d0e0d030b03070504050c0f031023040513050a0b06040b0d0803010501141207 71
    0x30324544074104400744003081c2070242d01300d5604a81c880d00070b4030903148440440d140600500d81c01610031110040c0c01c0d0411000c01c0c4c2c1060803400041000c0300e540f404806000304900c0f031003194002030b03400703002610704400c1e500c9501060354800c5016119007441c4804100c401c1c00741e4001d8031030190115045540760300c8112400407040c08241d4040074200450000b088040c0b200d080a440d22074000d0900618022038081050030701da2103c9004d902d4036010005d41c1400e0f0001e01d81245e040350b00035884000c0c1c00c1d200c1009110402c100e044620401d49101c0c0d04170f0309504070282056040741511012a980d000380002e440d42120001c84603407040020001c1e10420501854100400541180d00f6a44a51500d110031091a800c080c03007900441480c9010b00c5c007130084691008416500109603a030581c0d845940ba0b80304100200007000ea440090916203580d40680d80e4039400801003041720501341815201d5920a020b0315000581c041c482c001103034495000c0b510103c41c26590800f0a60f6500d001300c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 870130278 1250 870129028 870129047
    0x70c14092523030c0318060c03010e15030a14010509160b07110a060507050c0d0209070c03231201080304030807140106050603010308030609090d0f142a0706051207 72
    0x480440c12101c0ba60448100e1402031482103010544982d96801c0400c1c4056402c034170791806280d164030540400030202864402c1d207044072140c80d0b883d25151200701404a09a0a07040d003d5003510031083d0301d1091080b580b05071107461200790020456a1210720455440d40c1c081e20014408080f10b8030200070702d0140c0300003008c102c0c2c098091303403001c8042400094141c0030580c2c0f10100095001c144c44051042c1403011080c010b4084510300030002403a0b010842c0940000e12020500900000d22814140210780e40283e1a503201603050180d02d0000005c182038000020000c0c008001e403001103000d0310004100c0301602e40042e0301070f003440c00d00ea99041e002c8002c281c00300450754031614001000d4655001440c040d600c103110303503504d918248050000c0048014904040d560160203c9009a03810030450780c03104050b840c00700b1038602051940b40f80c80c4102032034443d52041d582e0240c0c00b1190700142080802800340c094903985030399064202c03014003605c500280d001d041d404c00700c3c3c28140900b0740390 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 870131528 1250 870130278 870130307
    0x5030c0120030307090602011b08180109020307181409060103080304030203040503120a0e040510120c0e040c061b0818010c050706020c0a05040905100908070c140925 73
    0x45100610301002900b160010348101002c0303410300707509001141d020b014000c280340c0291407000090440107002081090042c010128900a00c1c1030895802c2082d046080307030a0f000b03002c0f40c00b440d03a688a100740d050004800c20f030311540351500d00400c4c1c4c000341c44040d000d00900ca0040440b0b03401e40d20755850552029000302c00b9840108000150b075202401856905030b000120f00742c840c240c41c84007600290364111258411803924007004880650078000b5000d590301d44c10840c1e80f0301154604094542446d4010358080742000c400c000400948240a40035514103035958184008804c4104141d03802c4288000d200140900140801500aa00100c0c40003414984204030310000d484840c1003206941242c00141c0280f4240442420104c103c030300288401d440402003a6001d8032029207552860b0b800d035000c01c0d00d4800200a0021040513600c0641e00041b1100007590b417504c00402074070003030302010b010f010a113000800c440c0b4009940d006102d904c0740210076030301c1c10000403201c8404c244000e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 870132778 1250 870131528 870131567
    0x3020609030f1914010507021011160b011505041809030314190b01020c1804020102010207080d05040b060d0201020a060e031603030209090a0207082706070b041b05030c01 75
    0x200000858104821a0240c8043c403c184403a001810030501012882858507241d82c100000e001055500140c5049040d003910b0000406441c645184a000d1207201e4040300f170b00016a081c0801e01c084103203d40d04950864010342140c101025080d82c075400b4500c80c4014400c04866410f404010319084410307424880d28000035103020400b0036040200c0280d40c04400d40c0303a02c80480e44114207078800c00c000802d090000700740d10072081c800618842035100c3c208803140c8444010808690007501916441548100b240f500d41008074800e5004103070485064030307060982c03c08034010741400000700c541381e03806a001d040300401584604001e40308050501025100070000300c2c180042050449800340d100c0da5015951780c0142c8104405e050340038003507008940c81000700705c0020324080115516202d2940c080c002441892002c0030385004030701a26074112400140140c01c0013144043c3c00d205900c521043c1041901d420040c00c1140b00c1406055010392080540604940c0500214400e40000251 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 870134028 1250 870132778 870132793
    0x60a0309080f03090c130b10110114190606180b0306210309041113180b06040f03150b03030a0302070602301605030f040206120906010f0e0f010302060903 68
    0x1a100307001d40c011189160240c11840031701c0d5040c075140e0000010307102605400d10078001c0d80c900080c0918500300140c000d00c001c0c03e171581420502034020302016500050f54000c00d01d401220181c0185000d00322200c0e41d803a05501250340ba02417003000c0d03007500d50040045207080c02c0c2210070486030b0015060507800900c2100c401000707480428508502d00030b01c4082e5455807048424030041e10f88041080d02400c00a001c2e00147c0641c1515000c1112000c01e08101c1c0040402d003600010164200c003141c200380c0000300400d00d071300010403203011244159040c8030344259280500e01220130101449500d41c004111202c0d8851194018102c8a80145001442e01d079400c4203440d00404001e400c2041d100d1000000074500d401c400043c1e83c0282e90b03040441c41c59003004c1c801003c80c0700c02400d4141c0e084c07116020900355102c5d90184da81014140030b440959040801c4982d5948034240321345000f01401d41400310300c003032040380e205000e0100300710344440070390030355003000342580099003040e8041c0314500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 870135278 1250 870134028 870134047
    0x30d0501030311010c110d0305130b0106211a040e100914010501051005030f18010e070905090a150f1503030e03060c04030f030806150406080105030d030902060a030908 74
    0x810640254442d403503203000714107040c000d50b0954151460b41401e0080741000d0307514203c0041010b1801400707502d00007400da0346160040001200c8001d02030034000c0c111001050140c0c00a030031003121036114540d03581d04003580318000300303447c0d003c06d50f04d44a0000b095010340e90700706a0000081050590161400d2100d681d244204440c01c035902540c00050794986410811000e10505002d490f06465004601480c01000f0700700307120103400b81041180110011b842c50303600060b801c4282c6100c0c0028070034140503070b110a0381d03441c0078050091603034909030110311003d800040c1e16011903448030300c021001c980700001c0801046c1b406c81c201015a181c9240c48140c10095060101861081d120403c0e80c0d101c9130281890300f0390060003010340400c00c01c410320210703410b458408a403540c14070b0302c03041d04c0c0d039580082809141c0741e02100203603850218011500a40040c5a00d050395415012200034150b911011000e44456440280d0405c10801104200d10b100380c2100940742d021781d05180c50250f852 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 870136528 1250 870135278 870135281
    0x23040911060f130f0f2102060f030411030606130f09051204031203050408090402091306080d171b0309010b0a23040c0504060e01021006120b090706050403020d05030d 73
    0x2400e40c42d0380000c1c428000c000c903403800c502030301c0301075680380302581050b05403c8640e0081c050400510000c1d070302e00c50b145003043c501080c402e038090007040d2501982d02c1c00d0010342d0820344003141c00c81c00341002c101032402c00045440c0b042c080103111a92010350b2290390002458200d820740440c0d525000108045002080000b18600c002005140c0d95403443c1029082c8a0140c109001014104001e11010400303031801d4882980040f540140d42d02030200000700c03440d201c558180000d904000300094895004100d1200056664a40380c20742c01000d1102c035404c000032141049912030b074150002c010904a0083d540c40b030300000001a6108014000401c10801c651041d00307145000e03652200c1ca40031300c50000301e03040010f580c24003001d02c0b90100a0510700aa001d20820445a0400580d05a108020601d40101a1141004000e44074035011010020064094031088454400315115420005000d402c54507150398082c100342c00c542c2040302c85c07400381c40207880390b200601021b034080318103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 870137778 1250 870136528 870136537
    0xe0402130f08060106110a05120f09040905100c0e13090305070b0a0c1e020d05030a060f03050d030506010c0b0c09011101020a020d1101020a05030609130b090d092304091106 76
    0x2c8030041105600d04000101010044031602000d50070016910740019000511000c540354072840450325500d0042a4001500454006a62160400d0880020303c880803807171100c15114404244441d20500c842968580c0c03501d5600c0d90041c64084045002d004158080001580300e4075056161244035150b503401c1f402e0680c2c2d0284d54aa8403030858600701c2c0c1280c12080424041950099019007485011352551031580e035050038043d000000030303c2e546031075100720043c10358094141e03c440d8036400e1203a52403508429400100b40b402c804141950f028030600d004043e4080515200e035a160600b6000301d0704110315103414016202252400c8900a00141000c0c011940c020820b4031203441d002082e1005030290316100703920420a6550807607020049a50000055861298a458001c3e23211a0768084040143c001c0c04100c007031103110800424030090859140d5102590346440303400b440c0015135801d41e10a40c0c00040c0084c0e603140d0510b41c00101106c1d000b020503030591211880483d080d07900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 870139028 1250 870137778 870137789
    0x80402040c0e0613060905010807301805060105010c020a1518120b010f1a03090c030a26210411030d050a120b0306180c0a03030c1e030e0402130f 64
    0x3c802011700020b5440140380000345024038001203181891030000e0203206042c0080c17104d0f020411100803030000005401c041c0300d22a40f0f010044000305c0c510030b0310601c03030400c01100d0501400000243c0c661240c2c0e2816821500100601c285520b00b140f0369900503003043d030001c14030003e8016a8034950440801400500d0325805280206080745482511607a058202000c06003c520f0103209040d0744540007100d5a513444d06259036902e55401d01032400c070310a120181d040c40307441201e20400c00c2e59030081142c62681c494091a002100d21030740e0352409800e024113100704142c51b00c80c405a850490007604603000d0511070154054800c0824200042c07810020003040000030780d62200740c1c1c004104801505915002c11201740703a00b0000707807a4400500300f1681a007080e07102420002c01841240062100100703821041e90b41c03840e000d4010b20f90200305450a000c05000c1c2944014010003071020280c1c1507650184022881003000001d410090022201920180d80898006c5007241310310007404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 870140278 1250 870139028 870139057
    0x3100503010c080c09010c0512030c040609060306081c0509042c0601030506010302101e0c060b01030513061104080709240602071505160f1103030703080402040c0e06 73
    0x5080105050946003422444410000c00d0420041ea20840c1000c0c0d60380003100746044c181e503a0340c1d420f02d6440c1544420301d1b4510702c0c00001c2444802440580100101e034583d17292040c11a235078a0040e02101c90301c0c890480a60040041c01c032071840c01848001c001404c50a01905112030f01d808101203e44100400c001440101d016103014149040c0075190307000410001c202960560b07440588400040c0305c028042c064001c00703c0c0c240d40c06440703086420042404405041c140c5060006c0908031410025a201ca160032075a90f03281d4424090184180846600503002050594420380207201664403260703913010031b00000c24003840512128004003a0540082030b118404002d421103907100103280b8041841000c010012190042440000c850305415100003032010520103444030b109500f5100074001820285104001020b0b000d120b11074051604466803455080c00d0540e60b00c41c10300c014010a054400040c0140780c580c04c41e15101c0b07454503054801c503c09002144860b0010045080c604 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 870141528 1250 870140278 870140311
    0xf0f0c0206071b0503190203071e0b060a1410030f0f0f110901080a020901030207020d03051903020a0c02130b030d210614270901060303030605030105040c171203 71
    0x10303030080f891600500e0901070281846030300c0e941c0310755070b115003107045005030360b0189000780c801d000b88140d445464029001d81000003030b44006058030302ca00382045803481141404941d450030102164004c0e901c010f00c5840c5550b545004001900343d141c00c0160400d074555103c003e07001101d004003180e0405451011a0b100d440f000d04105540031994076621562080c041c3c50300581e03008071b540390490080900140e88540010048020344074200e006508514100404000c040d4007400070210f0074000c030f0341201031580071601141680300708940480020620080c1101614213108500b05040c201d01c400100030300e0107000b00f0b0a01015070406400b20304c60401214407099006884c11203500c4007601082542d081c08407018450b2048082c0c103000d80312001795400d040c50071003840101001502148805440d1011017903002e00344500040300001c0c20140000703550b08050040034000c0d86c0c0500105445801c040b080368101c4415404250144034011603d05003e8200c3c00a50050740148280d1606 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 870142778 1250 870141528 870141541
    0x10180c020118050d0c1b06090312020a02010e0f0111010c051908070906030905240603100506061209070b0711040b06031b090a050415030b091504060f0f0c0206 70
    0x8482c024080c0e80340c61403800140600082c00881d09070500d4a950924900300d80c00d42c00c02e041c42c810542d028011841c0c030f10102048068001e0150300c100c0344600c103001d05000c2c0b02c01c0101d031200c41003070000b40492480c1030755070300758503040400100120061405e07100c05001254203e003526096600b0a000c60000aa5030a001c000c8148500f400d00d070a00f1324101d18101803200402c3c2e58540d124002c1095a112143e50406c0800d000d4106002e07504da4030b101e00c55844a0307038002d04c40d80a552852003803080c0001a61034444134080c55103d0840200480e0900340703640c810b151074800c0180400180d00400c1004284a03482c103014015031409004070f0f80d21000c0110074481254642000035204074018010841202c41c074406810050340940c18158807545181c02240490425800c90344d400ba09083d2090301140051100d5001c40e40241c06c0155507481d8482119202c3ca8800424050001e01078001030210720950030080c051032040d0000585107a00c820200212a018111000160800401e0042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 870143884 1106 870142778 870142781
    0x180a09111801090e010c0509060a0203070b01120b150d030f02030c0106090509190201020604030f1704030f08010e010f14031204170f0319030510180c0201 68
    0x21500d40410384074000e44240502c8000c079140c106070395070302d003014000d0a034480c4035074440c030b8a405800b105012159004030181d0017584000c0bc403160006040028a500900002c20040300030000d9141a10f840e030806050f1011503200404500ba0642e43e5840040c01c8030b0381030030401c020400110060b8218014041c1c00303032455182030b40c00280c01d140c0e03030031041c842c500104c2550301516000b41d01050340200e0990107030059020b4000280028080c500e4101c6141880c1048001c074082031803001800e00040301c049000601c085500a80c164202250b00d02500601000d00c00c00c0d810541204084080d03441103c001001d991201342d0a80c806003c0450840e02200009645903280c59680c0005007003c43d4a402c5442208140d009286011058507486101e4280b02d21464190700011009400d01034022601000303880d030005071900e0b604196200d500014600491000410b50001c0d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 869964028 870143884 := by
  have h0 := BRFrame.cov_init 869964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 869964028 ≤ n) (h2 : n < 870143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
